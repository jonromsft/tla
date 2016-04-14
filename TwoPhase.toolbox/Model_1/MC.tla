---- MODULE MC ----
EXTENDS TwoPhase, TLC

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
r1, r2, r3, r4
----

\* MV CONSTANT definitions RM
const_1459894282261490000 == 
{r1, r2, r3, r4}
----

\* SYMMETRY definition
symm_1459894282271491000 == 
Permutations(const_1459894282261490000)
----

\* INIT definition @modelBehaviorInit:0
init_1459894282281492000 ==
TPInit
----
\* NEXT definition @modelBehaviorNext:0
next_1459894282292493000 ==
TPNext
----
\* INVARIANT definition @modelCorrectnessInvariants:0
inv_1459894282302494000 ==
TPTypeOK
----
\* INVARIANT definition @modelCorrectnessInvariants:1
inv_1459894282312495000 ==
TC!TCConsistent
----
\* PROPERTY definition @modelCorrectnessProperties:0
prop_1459894282323496000 ==
TC!TCSpec
----
=============================================================================
\* Modification History
\* Created Tue Apr 05 15:11:22 PDT 2016 by jonro
