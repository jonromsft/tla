------------------------------ MODULE SeqJonRo ------------------------------
EXTENDS Integers, Sequences

Remove(j, seq) == [i \in 1..(Len(seq)-1) |-> IF i < j THEN seq[i]
                                             ELSE seq[i+1]]   

GetSeq(j) == [i \in 1..j |-> i]
=============================================================================
\* Modification History
\* Last modified Wed Apr 06 09:56:10 PDT 2016 by jonro
\* Created Wed Apr 06 09:26:47 PDT 2016 by jonro
