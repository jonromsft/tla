---------------------------- MODULE TCommitJonRo ----------------------------
CONSTANT RM       \* The set of participating resource managers

VARIABLE rmState  \* rmState[rm] is the state of resource manager r.
-----------------------------------------------------------------------------
TCTypeOK == 
  (*************************************************************************)
  (* The type-correctness invariant                                        *)
  (*************************************************************************)
  rmState \in [RM -> {"working", "prepared", "committed", "aborted"}]

TCInit ==   rmState = [r \in RM |-> "working"]
  (*************************************************************************)
  (* The initial predicate.                                                *)
  (*************************************************************************)

canCommit == \A r \in RM : rmState[r] \in {"prepared", "committed"}
  (*************************************************************************)
  (* Can commit iff all RMs are in the "prepared" or "committed" state.    *)
  (*************************************************************************)

canAbort == \A r \in RM : rmState[r] # "committed" 
  (*************************************************************************)
  (* Can abort iff no RM has decided to commit.                            *)
  (*************************************************************************)
-----------------------------------------------------------------------------
(***************************************************************************)
(* We now define the actions that may be performed by the RMs, and then    *)
(* define the complete next-state action of the specification to be the    *)
(* disjunction of the possible RM actions.                                 *)
(***************************************************************************)
Prepare(r) == /\ rmState[r] = "working"
              \* Any RM in the working state can go to the prepared state
              /\ rmState' = [rmState EXCEPT ![r] = "prepared"]

Commit(r)  == /\ rmState[r] = "prepared"
              /\ canCommit \* Only allowed to commit from prepared if we can commit
              /\ rmState' = [rmState EXCEPT ![r] = "committed"]

Abort(r)   == /\ rmState[r] \in {"working", "prepared"}
              /\ canAbort \* Only allowed to abort from working or prepared if we can abort
              /\ rmState' = [rmState EXCEPT ![r] = "aborted"]

TCNext == \E r \in RM : Prepare(r) \/ Commit(r) \/ Abort(r)
  (*************************************************************************)
  (* The next-state action.                                                *)
  (*************************************************************************)
-----------------------------------------------------------------------------
TCSpec == TCInit /\ [][TCNext]_rmState
  (*************************************************************************)
  (* The complete specification of the protocol.                           *)
  (*************************************************************************)
-----------------------------------------------------------------------------
(***************************************************************************)
(* We now assert invariance properties of the specification.               *)
(***************************************************************************)
TCConsistent ==  
  (*************************************************************************)
  (* A state predicate asserting that two RMs have not arrived at          *)
  (* conflicting decisions.                                                *)
  (*************************************************************************)
  \A r1, r2 \in RM : ~ /\ rmState[r1] = "aborted"
                       /\ rmState[r2] = "committed"

THEOREM TCSpec => [](TCTypeOK /\ TCConsistent)
  (*************************************************************************)
  (* Asserts that TCTypeOK and TCInvariant are invariants of the protocol. *)
  (*************************************************************************)

=============================================================================
