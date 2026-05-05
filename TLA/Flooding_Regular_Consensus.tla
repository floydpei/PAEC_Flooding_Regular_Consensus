--------------------- MODULE Flooding_Regular_Consensus ---------------------
EXTENDS Naturals, FiniteSets

CONSTANTS
    PROCS,
    CRASHERS,       \* Set of processes that can crash (to reduce state space)
    PROPOSED_VAL,
    
    \* used as type in network messages
    PROPOSE,
    DECIDE,
    
    \* for explicit scenario
    p1,
    p2,
    p3,
    p4,
    p5
    
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
    crashed,         \* crashed processes that can be detected by the correct ones
    
    step_index
    
vars == <<correct, round, decision, proposals, received_from, delivered, broadcast, crashed, step_index>>

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
    /\ step_index    = 1
    
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
                /\ step_index' = step_index + 1
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
        /\ step_index' = step_index + 1
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
        /\ step_index' = step_index + 1
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
        /\ step_index' = step_index + 1
        /\ UNCHANGED<<correct, round, decision, proposals, received_from, delivered, broadcast>>
        
Detect_crash ==
    \E detector \in PROCS :
    \E dead \in PROCS :
        /\ detector \notin crashed
        /\ dead \in crashed
        /\ dead \in correct[detector]
        /\ correct' = [correct EXCEPT ![detector] = correct[detector] \ {dead}]
        /\ step_index' = step_index + 1
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
                    /\ step_index' = step_index + 1
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
            /\ step_index' = step_index + 1
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
             /\ step_index' = step_index + 1
             /\ UNCHANGED<<correct, round, proposals, received_from, delivered, crashed>>
        
\*----------------------------------------------------------------------------
\* Bug Scenario Description
\*----------------------------------------------------------------------------
\* Somehow needed to make TLC actually increment the step_index
KeepVars(Action) == 
    /\ Action
    /\ step_index' = step_index + 1
    
Exec ==
    /\  \/  \* --- PHASE 1: Initial Failures & Proposal Broadcast ---
            /\ step_index = 1
            /\ KeepVars(Crash)
            /\ p5 \in crashed'
          
        \/  /\ step_index = 2
            /\ KeepVars(Propose)
            /\ \E msg \in broadcast' : msg.type = PROPOSE /\ msg.src = p1
          
        \/  /\ step_index = 3
            /\ KeepVars(Propose)
            /\ \E msg \in broadcast' : msg.type = PROPOSE /\ msg.src = p2
          
        \/  /\ step_index = 4
            /\ KeepVars(Propose)
            /\ \E msg \in broadcast' : msg.type = PROPOSE /\ msg.src = p3
          
        \/  /\ step_index = 5
            /\ KeepVars(Propose)
            /\ \E msg \in broadcast' : msg.type = PROPOSE /\ msg.src = p4
          
        \/  \* --- PHASE 2: Local Deliveries (Self-Delivery of Round 1 Proposals) ---
            /\ step_index = 6
            /\ KeepVars(Deliver_proposal_correct)
            /\ p1 \in received_from'[p1][1]
          
        \/  /\ step_index = 7
            /\ KeepVars(Deliver_proposal_correct)
            /\ p2 \in received_from'[p2][1]
          
        \/  /\ step_index = 8
            /\ KeepVars(Deliver_proposal_correct)
            /\ p3 \in received_from'[p3][1]
          
        \/  /\ step_index = 9
            /\ KeepVars(Deliver_proposal_correct)
            /\ p4 \in received_from'[p4][1]
          
        \/  \* --- PHASE 3: Intermediate Crashes & Round 1 Message Deliveries ---
            /\ step_index = 10
            /\ KeepVars(Crash)
            /\ p4 \in crashed'
          
        \/  \* p1 delivers p2's proposal
            /\ step_index = 11
            /\ KeepVars(Deliver_proposal_correct)
            /\ p2 \in received_from'[p1][1]
            
        \/  \* p1 detects p5's crash
            /\ step_index = 12
            /\ KeepVars(Detect_crash)
            /\ p5 \notin correct'[p1]
          
        \/  \* p2 detects p5's crash
            /\ step_index = 13
            /\ KeepVars(Detect_crash)
            /\ p5 \notin correct'[p2]
          
        \/  \* p3 delivers p2's proposal
            /\ step_index = 14
            /\ KeepVars(Deliver_proposal_correct)
            /\ p2 \in received_from'[p3][1]
         
        \/  \* p2 delivers p3's proposal
            /\ step_index = 15
            /\ KeepVars(Deliver_proposal_correct)
            /\ p3 \in received_from'[p2][1]
          
        \/  \* p1 delivers p3's proposal
            /\ step_index = 16
            /\ KeepVars(Deliver_proposal_correct)
            /\ p3 \in received_from'[p1][1]
          
        \/  \* p1 delivers the proposal of now-crashed p4 (delivered as faulty)
            /\ step_index = 17
            /\ KeepVars(Deliver_proposal_faulty)
            /\ p4 \in received_from'[p1][1]
          
        \/  \* p2 delivers p1's proposal
            /\ step_index = 18
            /\ KeepVars(Deliver_proposal_correct)
            /\ p1 \in received_from'[p2][1]
          
        \/  \* p2 detects p4's crash
            /\ step_index = 19
            /\ KeepVars(Detect_crash)
            /\ p4 \notin correct'[p2]  
          
        \/  \* p3 detects p4's crash
            /\ step_index = 20
            /\ KeepVars(Detect_crash)
            /\ p4 \notin correct'[p3]
          
        \/  \* p3 detects p5's crash
            /\ step_index = 21
            /\ KeepVars(Detect_crash)
            /\ p5 \notin correct'[p3]
          
        \/  \* --- PHASE 4: Transition to Round 2 & Subsequent Crashes ---
            \* p1 realizes its active set is complete, transitions to round 2, and broadcasts
            /\ step_index = 22
            /\ KeepVars(Can_decide)
            /\ round'[p1] = 2 
          
        \/  \* p1 crashes immediately after launching round 2
            /\ step_index = 23
            /\ KeepVars(Crash)
            /\ p1 \in crashed'
          
        \/  \* p2 transitions to round 2
            /\ step_index = 24
            /\ KeepVars(Can_decide)
            /\ round'[p2] = 2
          
        \/  \* p2 self-delivers its own round 2 proposal
            /\ step_index = 25
            /\ KeepVars(Deliver_proposal_correct)
            /\ p2 \in received_from'[p2][2]
          
        \/  \* p2 delivers the round 2 proposal sent by the now-crashed p1 (faulty)
            /\ step_index = 26
            /\ KeepVars(Deliver_proposal_faulty)
            /\ p1 \in received_from'[p2][2]
            
        \/  \* p3 delivers p2's round 2 proposal (while p3 is still in round 1)
            /\ step_index = 27
            /\ KeepVars(Deliver_proposal_correct)
            /\ p2 \in received_from'[p3][2]
            
        \/  \* p3 detects p1's crash
            /\ step_index = 28
            /\ KeepVars(Detect_crash)
            /\ p1 \notin correct'[p3]
        
        \/  \* p3 transitions to round 2
            /\ step_index = 29
            /\ KeepVars(Can_decide)
            /\ round'[p3] = 2
          
        \/  \* p2 delivers p3's round 2 proposal
            /\ step_index = 30
            /\ KeepVars(Deliver_proposal_correct)
            /\ p3 \in received_from'[p2][2]
        
        \/  \* p3 self-delivers its own round 2 proposal
            /\ step_index = 31
            /\ KeepVars(Deliver_proposal_correct)
            /\ p3 \in received_from'[p3][2]
          
        \/  \* --- PHASE 5: Decisions ---
            \* p2 reaches decision based on round 2 values
            /\ step_index = 32
            /\ KeepVars(Can_decide)
            /\ decision'[p2] /= 0
          
        \/  \* p3 reaches decision based on round 2 values
            /\ step_index = 33
            /\ KeepVars(Can_decide)
            /\ decision'[p3] /= 0
          
        \/  \* Infinite stuttering state to prevent deadlocks after trace runs
            /\ step_index > 34
            /\ UNCHANGED vars



\*----------------------------------------------------------------------------
\* Next Action and Specification
\*----------------------------------------------------------------------------
Done ==
    /\ \A p \in PROCS : p \in crashed \/ decision[p] /= 0
    /\ UNCHANGED vars

Next_rules ==
    \/ Propose
    \/ Deliver_proposal_correct
    \/ Deliver_proposal_faulty
    \/ Crash
    \/ Detect_crash
    \/ Can_decide
    \/ Deliver_decision
    \*\/ Done
    
Next ==
    /\ Next_rules
    /\ Exec
    
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
\* Last modified Tue May 05 14:26:40 CEST 2026 by floyd
\* Created Fri Apr 24 09:04:30 CEST 2026 by floyd 