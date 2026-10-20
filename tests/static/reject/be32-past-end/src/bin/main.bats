#include "share/atspre_staload.hats"
#use array as A


(* Cells 1 to 4 of 4 cells (cell 4 is past the end). *)
implement main0 () = let
  val (len | a) = $A.barr_alloc(4)
  val (p0, p1, p2, p3 | @(x0, x1, x2, x3)) = $A.barr_get_be32(a, 1)
  val () = $A.barr_free(a)
in () end
