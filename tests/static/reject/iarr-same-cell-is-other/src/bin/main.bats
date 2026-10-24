#include "share/atspre_staload.hats"
#use array as A

(* setc_nth_other is for another cell: used for the cell that was set, its
   index condition i != j is false. *)
implement main0 () = let
  val (len, zeros | a) = $A.iarr_alloc(4)
  val (first | a) = $A.iarr_set(a, 0, 65)
  val (second | a) = $A.iarr_set(a, 0, 66)
  prval wrong = $A.setc_nth_other(second, $A.setc_nth_same(first))
  val () = $A.iarr_free(a)
in () end
