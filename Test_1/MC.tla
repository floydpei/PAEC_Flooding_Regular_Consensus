---- MODULE MC ----
EXTENDS Flooding_Regular_Consensus, TLC

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
p1, p2, p3, p4
----

\* MV CONSTANT definitions PROCS
const_1777023808551269000 == 
{p1, p2, p3, p4}
----

\* SYMMETRY definition
symm_1777023808551270000 == 
Permutations(const_1777023808551269000)
----

\* CONSTANT definitions @modelParameterConstants:1PROPOSED_VAL
const_1777023808551271000 == 
[p \in PROCS |-> IF p = p1 THEN 1 ELSE IF p = p2 THEN 2 ELSE IF p = p3 THEN 3 ELSE 4]
----

=============================================================================
\* Modification History
\* Created Fri Apr 24 11:43:28 CEST 2026 by floyd
