#include "share/atspre_staload.hats"
#use array as A

(* The cell set to 65 is not 66. *)
implement main0 () = let
  val (len, zeros | a) = $A.iarr_alloc(4)
  val (first | a) = $A.iarr_set(a, 0, 65)
  val (read | v) = $A.iarr_get(a, 0)
  prval () = $A.nth_functional(read, $A.setc_nth_same(first))
  val wrong: int(66) = v
  val () = $A.iarr_free(a)
in () end
