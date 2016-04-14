---- MODULE MC ----
EXTENDS SeqJonRo, TLC

\* Constant expression definition @modelExpressionEval
const_expr_145996177340525000 == 
GetSeq(3)
----

\* Constant expression ASSUME statement @modelExpressionEval
ASSUME PrintT(<<"$!@$!@$!@$!@$!",const_expr_145996177340525000>>)
----

=============================================================================
\* Modification History
\* Created Wed Apr 06 09:56:13 PDT 2016 by jonro
