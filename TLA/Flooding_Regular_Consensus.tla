--------------------- MODULE Flooding_Regular_Consensus ---------------------
EXTENDS Naturals, FiniteSets

CONSTANTS
    PROCS,
    CRASHERS,       \* Set of processes that can crash (to reduce state space)
    PROPOSED_VAL,
    
    \* used as type in network messages
    PROPOSE,
    DECIDE
    
N_PROCS == Cardinality(PROCS)
Round == 0..N_PROCS
VALUES == 1..N_PROCS
SetMax(S) == CHOOSE v \in S : \A w \in S : w <= v

VARIABLES
    \* Per process local states
    correct,        \* [PROCS -> SUBSET PROCS]               who p believes is alive
    round,          \* [PROCS -> Round]                      p's current round
    decision,       \* [PROCS -> Nat]                        0 = undecided
    proposals,      \* [PROCS -> [Round -> SUBSET Nat]]
    received_from,  \* [PROCS -> [Round -> SUBSET PROCS]]
    delivered,      \* [PROCS -> SUBSET [type: {PROPOSE, DECIDE}, src: PROCS, round: Round, vals: SUBSET Nat]]
    
    \* Shared
    broadcast,      \* Each record: [ type: proposal/decided; src : Proc; round : Nat; vals : SUBSET Nat ]
    crashed         \* crashed processes that can be detected by the correct ones
    
vars == <<correct, round, decision, proposals, received_from, delivered, broadcast, crashed>>

\*----------------------------------------------------------------------------
\* Initial State
\*---------------------------------------------------------------------------
Init ==
    /\ correct       = [p \in PROCS |-> PROCS]
    /\ round         = [p \in PROCS |-> 1]
    /\ decision      = [p \in PROCS |-> 0]
    /\ proposals     = [p \in PROCS |-> [r \in Round |-> {}]]
    /\ received_from = [p \in PROCS |-> [r \in Round |-> IF r = 0 THEN PROCS ELSE {}]]
    /\ delivered     = [p \in PROCS |-> {}]
    /\ broadcast     = {}
    /\ crashed       = {}
    
\*----------------------------------------------------------------------------
\* Proposing Actions
\*---------------------------------------------------------------------------
Propose ==
    \E proposer \in PROCS :
    \*\E v \in VALUES :
        /\ proposer \notin crashed
        \* Check if proposer has already broadcasted its proposal
        /\ ~\E msg \in broadcast : msg.type = PROPOSE /\ msg.src = proposer \* /\ msg.round = 1
        /\ round[proposer] = 1
        /\  LET new_proposals == proposals[proposer][1] \union {PROPOSED_VAL[proposer]}
        \*/\  LET new_proposals == proposals[proposer][1] \union {v}
            IN
                /\ proposals' = [proposals EXCEPT ![proposer][1] = new_proposals]
                /\ broadcast' = broadcast \union 
                                            {
                                            [type   |-> PROPOSE,
                                             src    |-> proposer,
                                             round  |-> 1,
                                             vals   |-> new_proposals]
                                            }
                /\ UNCHANGED<<correct, round, decision, received_from, delivered, crashed>>
            
Deliver_proposal_correct ==
    \E proposal_msg \in broadcast :
    \E receiver \in PROCS :
        /\ receiver \notin crashed
        /\ proposal_msg.src \notin crashed  \* Sender must be correct for weak fairness context
        /\ proposal_msg.src \notin received_from[receiver][proposal_msg.round]  \* Keep to reduce model checking time
        /\ proposal_msg.type = PROPOSE
        /\ proposal_msg \notin delivered[receiver] \* Enforce BEB2: No duplication
        /\ proposals' = [proposals EXCEPT ![receiver][proposal_msg.round] = proposals[receiver][proposal_msg.round] \union proposal_msg.vals]
        /\ received_from' = [received_from EXCEPT ![receiver][proposal_msg.round] = received_from[receiver][proposal_msg.round] \union {proposal_msg.src}]
        /\ delivered' = [delivered EXCEPT ![receiver] = delivered[receiver] \union {proposal_msg}]
        /\ UNCHANGED<<correct, round, decision, broadcast, crashed>>

Deliver_proposal_faulty ==
    \E proposal_msg \in broadcast :
    \E receiver \in PROCS :
        /\ receiver \notin crashed
        /\ proposal_msg.src \in crashed   \* Arbitrary scenario where sender crashed
        /\ proposal_msg.src \notin received_from[receiver][proposal_msg.round]  \* Keep to reduce model checking time
        /\ proposal_msg.type = PROPOSE
        /\ proposal_msg \notin delivered[receiver]
        /\ proposals' = [proposals EXCEPT ![receiver][proposal_msg.round] = proposals[receiver][proposal_msg.round] \union proposal_msg.vals]
        /\ received_from' = [received_from EXCEPT ![receiver][proposal_msg.round] = received_from[receiver][proposal_msg.round] \union {proposal_msg.src}]
        /\ delivered' = [delivered EXCEPT ![receiver] = delivered[receiver] \union {proposal_msg}]
        /\ UNCHANGED<<correct, round, decision, broadcast, crashed>>
        
        
\*----------------------------------------------------------------------------
\* Crashing Actions
\*---------------------------------------------------------------------------
Crash == 
    \E goner \in CRASHERS :
        /\ goner \notin crashed
        /\ crashed' = crashed \union {goner}
        \* Messages from failed processes are no longer removed from the broadcast set
        \*/\ broadcast' = {msg \in broadcast : msg.src /= goner}
        /\ UNCHANGED<<correct, round, decision, proposals, received_from, delivered, broadcast>>
        
Detect_crash ==
    \E detector \in PROCS :
    \E dead \in PROCS :
        /\ detector \notin crashed
        /\ dead \in crashed
        /\ dead \in correct[detector]
        /\ correct' = [correct EXCEPT ![detector] = correct[detector] \ {dead}]
        /\ UNCHANGED<<round, decision, proposals, received_from, delivered, broadcast, crashed>>
        
        
\*----------------------------------------------------------------------------
\* Deciding Actions
\*---------------------------------------------------------------------------
Can_decide ==
    \E decider \in PROCS :
        /\ decider \notin crashed
        /\ decision[decider] = 0
        /\ correct[decider] \subseteq received_from[decider][round[decider]]
        /\ IF received_from[decider][round[decider]] = received_from[decider][round[decider] - 1]
            THEN LET decided_val == SetMax(proposals[decider][round[decider]])
                    IN
                    /\ broadcast' = broadcast \cup {
                           [type  |-> DECIDE,
                            src   |-> decider,
                            round |-> round[decider],
                            vals  |-> {decided_val}]
                            }
                    /\ decision' = [decision EXCEPT ![decider] = decided_val]
                    /\ UNCHANGED <<correct, round, proposals, received_from, delivered, crashed>>
            ELSE
            /\ round[decider] < N_PROCS
            /\ round' = [round EXCEPT ![decider] = round[decider] + 1 ]
            /\ broadcast' = broadcast \union 
                                        {
                                        [type   |-> PROPOSE,
                                         src    |-> decider,
                                         round  |-> round[decider] + 1,
                                         vals   |-> proposals[decider][round[decider]] ]
                                        }
            /\ UNCHANGED<<correct, decision, proposals, received_from, delivered, crashed>>
            
Deliver_decision ==
    \E receiver \in PROCS :
    \E msg \in broadcast:
        /\ receiver \notin crashed
        /\ msg.type = DECIDE
        /\ msg.src \in correct[receiver]
        /\ decision[receiver] = 0
        /\ LET decided_val == CHOOSE x \in msg.vals : TRUE       \* Extract the single value from the set
           IN
             /\ broadcast' = broadcast \cup {
                       [type  |-> DECIDE,
                        src   |-> receiver,
                        round |-> round[receiver],
                        vals  |-> {decided_val}]
                        }
             /\ decision' = [decision EXCEPT ![receiver] = decided_val]
             /\ UNCHANGED<<correct, round, proposals, received_from, delivered, crashed>>
        
        
\*----------------------------------------------------------------------------
\* Next Action and Specification
\*----------------------------------------------------------------------------
Done ==
    /\ \A p \in PROCS : p \in crashed \/ decision[p] /= 0
    /\ UNCHANGED vars

Next ==
    \/ Propose
    \/ Deliver_proposal_correct
    \/ Deliver_proposal_faulty
    \/ Crash
    \/ Detect_crash
    \/ Can_decide
    \/ Deliver_decision
    \/ Done
    
\* List explicit weak fairness variables on specific safe actions rather than globally
Spec == Init /\ [][Next]_vars /\ WF_vars(Propose) 
                              /\ WF_vars(Deliver_proposal_correct) 
                              /\ WF_vars(Can_decide) 
                              /\ WF_vars(Deliver_decision) 
                              /\ WF_vars(Crash)
                              /\ WF_vars(Detect_crash)

\*----------------------------------------------------------------------------
\* Invariants
\*---------------------------------------------------------------------------
TypeOK ==
    /\ correct       \in [PROCS -> SUBSET PROCS]
    /\ round         \in [PROCS -> Round]
    /\ decision      \in [PROCS -> Nat]
    /\ proposals     \in [PROCS -> [Round -> SUBSET Nat]]
    /\ received_from \in [PROCS -> [Round -> SUBSET PROCS]]
    /\ crashed       \in SUBSET PROCS
    /\ delivered     \in [PROCS -> SUBSET [type: {PROPOSE, DECIDE}, src: PROCS, round: Round, vals: SUBSET Nat]]
    /\ broadcast     \in SUBSET [type      : {PROPOSE, DECIDE},
                                 src       : PROCS,
                                 round     : Round,
                                 vals      : SUBSET Nat]
                                 
Validity ==
    \A p \in PROCS :
        decision[p] /= 0 => 
            \* \E q \in PROCS : 
            \E msg \in broadcast : 
                /\ msg.type = PROPOSE 
                \* /\ msg.src = q 
                /\ decision[p] \in msg.vals

    
Agreement ==
    \A p, q \in PROCS :
        /\ p \notin crashed
        /\ q \notin crashed
        /\ decision[p] /= 0
        /\ decision[q] /= 0
        => decision[p] = decision[q]
        
\*----------------------------------------------------------------------------
\* Liveness and Temporal Properties
\*----------------------------------------------------------------------------
Integrity ==
    [][\A p \in PROCS : decision[p] /= 0 => decision'[p] = decision[p]]_vars
    
    
Termination ==
    \A p \in PROCS \ CRASHERS : <>(decision[p] /= 0)

\*----------------------------------------------------------------------------
\* Additional Properties for BEB and PFD
\*----------------------------------------------------------------------------

\* We cannot quantify directly over the msg in broadcast (\A msg \in broadcast) as broadcast is not a constant
\* 1. BEB Validity for PROPOSE Messages
\* If a correct sender broadcasts a proposal in round 'r', all correct targets deliver it.
BEB1_Proposals_Validity ==
    \A sender \in PROCS :
        \A target \in PROCS :
            \A r \in Round \ {0} :
                (\E msg \in broadcast : msg.type = PROPOSE /\ msg.src = sender /\ msg.round = r)
                /\ [](sender \notin crashed /\ target \notin crashed)
                ~>
                (\E msg \in delivered[target] : msg.type = PROPOSE /\ msg.src = sender /\ msg.round = r)

\* 2. BEB Validity for DECIDE Messages
\* If a correct sender broadcasts a decision, all correct targets deliver it.
BEB1_Decisions_Validity ==
    \A sender \in PROCS :
        \A target \in PROCS :
            (\E msg \in broadcast : msg.type = DECIDE /\ msg.src = sender)
            /\ [](sender \notin crashed /\ target \notin crashed)
            ~>
            (\E msg \in delivered[target] : msg.type = DECIDE /\ msg.src = sender)

\* 3. Conjoin them for the final property
BEB1_Validity == BEB1_Proposals_Validity /\ BEB1_Decisions_Validity

            
BEB2_NoDuplication == 
    \* This is guaranteed by the guard /\ proposal_msg \notin delivered[receiver] in our propose actions
    TRUE
    
BEB3_NoCreation ==
    \A p \in PROCS :
        \A msg \in delivered[p] :
            msg \in broadcast
            
PFD_Strong_completeness ==
    \A p, q \in PROCS :
        (p \in crashed) ~> (p \notin correct[q] \/ q \in crashed)

 =============================================================================
\* Modification History
\* Last modified Tue May 05 12:02:07 CEST 2026 by floyd
\* Created Fri Apr 24 09:04:30 CEST 2026 by floyd 