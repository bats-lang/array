#include "share/atspre_staload.hats"
#use array as A


(* Cells 0 and 1 were set to 65 and 66: the second byte of the word is 66, not 67. *)
implement main0 () = let
  val (len | a) = $A.barr_alloc(4)
  val (first | a) = $A.barr_set_inline(a, 0, 65)
  val (second | a) = $A.barr_set_inline(a, 1, 66)
  val (p0, p1, p2, p3 | @(x0, x1, x2, x3)) = $A.barr_get_be32_inline(a, 0)
  prval () = $A.nth_functional(p0, $A.setc_nth_other(second, $A.setc_nth_same(first)))
  prval () = $A.nth_functional(p1, $A.setc_nth_same(second))
  val wrong: int(67) = x1
  val () = $A.barr_free(a)
in () end
