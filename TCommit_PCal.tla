---------------------------- MODULE TCommit_PCal ----------------------------
CONSTANT RM

(***************************************************************************
--algorithm tcommit 
   { variable rmState  = [r \in RM |-> "working"];
     define 
       { canCommit == \A r \in RM : rmState[r] \in {"prepared", "committed"}
         notCommitted == \A r \in RM : rmState[r] # "committed" 
       }
     process (r \in RM) 
      { a: while (TRUE)
             { either { await rmState[self] = "working" ;
                        rmState[self] := "prepared"                        }
                   or { await (rmState[self] = "prepared") /\ canCommit ;
                        rmState[self] :="committed"                        }
                   or { await /\ rmState[self] \in {"working", "prepared"} 
                              /\ notCommitted ;
                        rmState[self] := "aborted"                         }
              }
      }
   }
 ***************************************************************************)

-----------------------------------------------------------------------------
==========
TCTypeOK == 
  rmState \in [RM -> {"working", "prepared", "committed", "aborted"}]

TCConsistent ==  
  \A r1, r2 \in RM : ~ /\ rmState[r1] = "aborted"
                       /\ rmState[r2] = "committed"
=============================================================================
\* Modification History
\* Last modified Thu Mar 24 18:13:46 PDT 2016 by lamport
\* Created Thu Mar 24 15:21:53 PDT 2016 by lamport
