#include "share/atspre_staload.hats"
#use array as A


(* The second cell read is cell 2, and the cell set to 65 is cell 1. *)
implement main0 () = let
  val (len | a) = $A.barr_alloc(5)
  val (first | a) = $A.barr_set(a, 1, 65)
  val (p0, p1, p2, p3 | @(x0, x1, x2, x3)) = $A.barr_get_be32(a, 1)
  prval () = $A.nth_functional(p1, $A.setc_nth_same(first))
  val () = $A.barr_free(a)
in () end
