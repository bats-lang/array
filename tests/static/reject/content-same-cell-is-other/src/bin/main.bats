#include "share/atspre_staload.hats"
#use array as A
staload C = "array/src/content.sats"

(* Setting cell 0 does not leave cell 0 as it was: the lemma about the
   other cells needs another cell. *)
implement main0 () = let
  val (len | a) = $C.barr_alloc(4)
  val (before | a) = $C.barr_get(a, 0)
  val (set | a) = $C.barr_set(a, 0, 65)
  prval still = $C.setc_nth_other(set, before)
  val () = $C.barr_free(a)
in () end
