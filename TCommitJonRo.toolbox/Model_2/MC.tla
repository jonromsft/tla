---- MODULE MC ----
EXTENDS TCommitJonRo, TLC

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
r1, r2, r3
----

\* MV CONSTANT definitions RM
const_1459881476745143000 == 
{r1, r2, r3}
----

\* SYMMETRY definition
symm_1459881476755144000 == 
Permutations(const_1459881476745143000)
----

\* INIT definition @modelBehaviorInit:0
init_1459881476765145000 ==
TCInit
----
\* NEXT definition @modelBehaviorNext:0
next_1459881476775146000 ==
TCNext
----
\* INVARIANT definition @modelCorrectnessInvariants:0
inv_1459881476786147000 ==
TCTypeOK
----
\* INVARIANT definition @modelCorrectnessInvariants:1
inv_1459881476796148000 ==
TCConsistent
----
=============================================================================
\* Modification History
\* Created Tue Apr 05 11:37:56 PDT 2016 by jonro
