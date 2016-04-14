---- MODULE MC ----
EXTENDS TCommitJonRo, TLC

\* CONSTANT definitions @modelParameterConstants:0RM
const_1459881073416110000 == 
{"r1", "r2", "r3"}
----

\* INIT definition @modelBehaviorInit:0
init_1459881073427111000 ==
TCInit
----
\* NEXT definition @modelBehaviorNext:0
next_1459881073437112000 ==
TCNext
----
\* INVARIANT definition @modelCorrectnessInvariants:0
inv_1459881073447113000 ==
TCTypeOK
----
\* INVARIANT definition @modelCorrectnessInvariants:1
inv_1459881073458114000 ==
TCConsistent
----
=============================================================================
\* Modification History
\* Created Tue Apr 05 11:31:13 PDT 2016 by jonro
