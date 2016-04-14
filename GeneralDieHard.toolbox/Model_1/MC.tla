---- MODULE MC ----
EXTENDS GeneralDieHard, TLC

\* CONSTANT definitions @modelParameterConstants:0BigJug
const_145987738887976000 == 
5
----

\* CONSTANT definitions @modelParameterConstants:1SmallJug
const_145987738889077000 == 
3
----

\* CONSTANT definitions @modelParameterConstants:2Goal
const_145987738890178000 == 
4
----

\* INIT definition @modelBehaviorInit:0
init_145987738891179000 ==
Init
----
\* NEXT definition @modelBehaviorNext:0
next_145987738892280000 ==
Next
----
\* INVARIANT definition @modelCorrectnessInvariants:0
inv_145987738893381000 ==
big # Goal
----
\* INVARIANT definition @modelCorrectnessInvariants:1
inv_145987738894482000 ==
TypeOK
----
=============================================================================
\* Modification History
\* Created Tue Apr 05 10:29:48 PDT 2016 by jonro
