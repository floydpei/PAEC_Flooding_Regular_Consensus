--------------------- MODULE Flooding_Regular_Consensus ---------------------
EXTENDS Naturals, FiniteSets

CONSTANTS
    PROCS,
    PROPOSED_VAL,
    
    \* used as type in network messages
    PROPOSE,
    DECIDE
    
N_PROCS == Cardinality(PROCS)
Round == 0..N_PROCS
SetMax(S) == CHOOSE v \in S : \A w \in S : w <= v

VARIABLES
    \* Per process local states
    correct,        \* [PROCS -> SUBSET PROCS]               who p believes is alive
    round,          \* [PROCS -> Round]                      p's current round
    decision,       \* [PROCS -> Nat]                        0 = undecided
    proposals,      \* [PROCS -> [Round -> SUBSET Nat]]
    received_from,  \* [PROCS -> [Round -> SUBSET PROCS]]
    has_proposed,   \* [PROCS -> Boolean]                    to ensure a process can only propose once
    
    \* Shared
    network,        \* Each record: [ type: proposal/decided; src : Proc; round : Nat; vals : SUBSET Nat ]
    crashed        \* crashed processes that can be detected by the correct ones
    
vars == <<correct, round, decision, proposals, received_from, network, crashed, has_proposed>>

\*----------------------------------------------------------------------------
\* Initial State
\*---------------------------------------------------------------------------
Init ==
    /\ correct       = [p \in PROCS |-> PROCS]
    /\ round         = [p \in PROCS |-> 1]
    /\ decision      = [p \in PROCS |-> 0]
    /\ proposals     = [p \in PROCS |-> [r \in Round |-> {}]]
    /\ received_from = [p \in PROCS |-> [r \in Round |-> IF r = 0 THEN PROCS ELSE {}]]
    /\ network       = {}
    /\ crashed       = {}
    /\ has_proposed  = [p \in PROCS |-> FALSE]
    
\*----------------------------------------------------------------------------
\* Proposing Actions
\*---------------------------------------------------------------------------
Propose ==
    \E proposer \in PROCS :
        /\ proposer \notin crashed
        /\ ~has_proposed[proposer]
        /\ round[proposer] = 1
        /\ LET new_proposals == proposals[proposer][1] \union {PROPOSED_VAL[proposer]}
           IN
            /\ proposals' = [proposals EXCEPT ![proposer][1] = new_proposals]
            /\ network' = network \union 
                                        {
                                        [type   |-> PROPOSE,
                                         src    |-> proposer,
                                         round  |-> 1,
                                         vals   |-> new_proposals]
                                        }
            /\ received_from' = [received_from EXCEPT ![proposer][1] = received_from[proposer][1] \union {proposer}]
            /\ has_proposed' = [has_proposed EXCEPT ![proposer] = TRUE]
            /\ UNCHANGED<<correct, round, decision, crashed>>
            
Deliver_proposal ==
    \E proposal_msg \in network :
    \E receiver \in PROCS :
        /\ receiver \notin crashed
        /\ round[receiver] = proposal_msg.round
        /\ proposal_msg.src \notin received_from[receiver][proposal_msg.round]
        /\ proposal_msg.type = PROPOSE
        /\ proposals' = [proposals EXCEPT ![receiver][proposal_msg.round] = proposals[receiver][proposal_msg.round] \union proposal_msg.vals]
        /\ received_from' = [received_from EXCEPT ![receiver][proposal_msg.round] = received_from[receiver][proposal_msg.round] \union {proposal_msg.src}]
        /\ UNCHANGED<<correct, round, decision, network, crashed, has_proposed>>
        
        
\*----------------------------------------------------------------------------
\* Crashing Actions
\*---------------------------------------------------------------------------
Crash == 
    \E goner \in PROCS :
        /\ goner \notin crashed
        /\ crashed' = crashed \union {goner}
        /\ network' = {msg \in network : msg.src /= goner}
        /\ UNCHANGED<<correct, round, decision, proposals, received_from, has_proposed>>
        
Detect_crash ==
    \E detector \in PROCS :
    \E dead \in PROCS :
        /\ detector \notin crashed
        /\ dead \in crashed
        /\ dead \in correct[detector]
        /\ correct' = [correct EXCEPT ![detector] = correct[detector] \ {dead}]
        /\ UNCHANGED<<round, decision, proposals, received_from, network, crashed, has_proposed>>
        
        
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
                    /\ network' = network \cup {
                           [type  |-> DECIDE,
                            src   |-> decider,
                            round |-> round[decider],
                            vals  |-> {decided_val}]
                            }
                    /\ decision' = [decision EXCEPT ![decider] = decided_val]
                    /\ UNCHANGED <<correct, round, proposals, received_from, crashed, has_proposed>>
            ELSE
            /\ round[decider] < N_PROCS
            /\ round' = [round EXCEPT ![decider] = round[decider] + 1 ]
            /\ network' = network \union 
                                        {
                                        [type   |-> PROPOSE,
                                         src    |-> decider,
                                         round  |-> round[decider] + 1,
                                         vals   |-> proposals[decider][round[decider]] ]
                                        }
            /\ UNCHANGED<<correct, decision, proposals, received_from, crashed, has_proposed>>
            
Deliver_decision ==
    \E receiver \in PROCS :
    \E msg \in network:
        /\ receiver \notin crashed
        /\ msg.type = DECIDE
        /\ msg.src \in correct[receiver]
        /\ decision[receiver] = 0
        /\ LET decided_val == CHOOSE x \in msg.vals : TRUE       \* Extract the single value from the set
           IN
             /\ network' = network \cup {
                       [type  |-> DECIDE,
                        src   |-> receiver,
                        round |-> round[receiver],
                        vals  |-> {decided_val}]
                        }
             /\ decision' = [decision EXCEPT ![receiver] = decided_val]
             /\ UNCHANGED<<correct, round, proposals, received_from, crashed, has_proposed>>
        
        
\*----------------------------------------------------------------------------
\* Next Action and Specification
\*----------------------------------------------------------------------------
Next ==
    \/ Propose
    \/ Deliver_proposal
    \/ Crash
    \/ Detect_crash
    \/ Can_decide
    \/ Deliver_decision
    
Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

\*----------------------------------------------------------------------------
\* Invariants
\*----------------------------------------------------------------------------
TypeOK ==
    /\ correct       \in [PROCS -> SUBSET PROCS]
    /\ round         \in [PROCS -> Round]
    /\ decision      \in [PROCS -> Nat]
    /\ proposals     \in [PROCS -> [Round -> SUBSET Nat]]
    /\ received_from \in [PROCS -> [Round -> SUBSET PROCS]]
    /\ crashed       \in SUBSET PROCS
    /\ network       \in SUBSET [type      : {PROPOSE, DECIDE},
                                 src       : PROCS,
                                 round     : Round,
                                 vals      : SUBSET Nat]
    /\ has_proposed  \in [PROCS -> BOOLEAN]
                                 
Validity ==
    \A p \in PROCS :
        decision[p] /= 0 => \E q \in PROCS : decision[p] = PROPOSED_VAL[q]

    
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
    \A p \in PROCS :
        p \notin crashed ~> (decision[p] /= 0 \/ p \in crashed)


=============================================================================
\* Modification History
\* Last modified Fri Apr 24 11:22:51 CEST 2026 by floyd
\* Created Fri Apr 24 09:04:30 CEST 2026 by floyd
