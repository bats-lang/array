#include "share/atspre_staload.hats"
#use array as A


(* The cell set to 65 is not 66. *)
implement main0 () = let
  val (len | a) = $A.barr_alloc(4)
  val (first | a) = $A.barr_set(a, 0, 65)
  val (read | v) = $A.barr_get(a, 0)
  prval () = $A.nth_functional(read, $A.setc_nth_same(first))
  val wrong: int(66) = v
  val () = $A.barr_free(a)
in () end
