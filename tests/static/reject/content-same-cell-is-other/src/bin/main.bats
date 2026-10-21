#include "share/atspre_staload.hats"
#use array as A


(* Setting cell 0 does not leave cell 0 as it was: the lemma about the
   other cells needs another cell. *)
implement main0 () = let
  val (len | a) = $A.barr_alloc(4)
  val (before | v) = $A.barr_get(a, 0)
  val (set | a) = $A.barr_set(a, 0, 65)
  prval still = $A.setc_nth_other(set, before)
  val () = $A.barr_free(a)
in () end
