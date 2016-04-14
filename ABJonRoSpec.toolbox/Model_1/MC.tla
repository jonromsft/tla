---- MODULE MC ----
EXTENDS ABJonRoSpec, TLC

\* CONSTANT definitions @modelParameterConstants:0Data
const_146016283021935000 == 
{2, 3, 4, 5}
----

\* CONSTRAINT definition @modelParameterContraint:0
constr_146016283023436000 ==
Len(AtoB) < 6 /\ Len(BtoA) < 6
----
\* INIT definition @modelBehaviorInit:0
init_146016283025037000 ==
Init
----
\* NEXT definition @modelBehaviorNext:0
next_146016283026638000 ==
Next
----
\* INVARIANT definition @modelCorrectnessInvariants:0
inv_146016283028139000 ==
TypeOK
----
=============================================================================
\* Modification History
\* Created Fri Apr 08 17:47:10 PDT 2016 by jonro
