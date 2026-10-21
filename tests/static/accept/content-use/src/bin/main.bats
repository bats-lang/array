#include "share/atspre_staload.hats"
#use array as A


(* Two cells set, the first read back: the types know it is what was set,
   though the second was set after it. *)
implement main0 () = let
  val (len | a) = $A.barr_alloc(4)
  val (first | a) = $A.barr_set(a, 0, 65)
  val (second | a) = $A.barr_set(a, 1, 66)
  prval kept = $A.setc_nth_other(second, $A.setc_nth_same(first))
  val (read | v) = $A.barr_get(a, 0)
  prval () = $A.nth_functional(read, kept)
  val sixty_five: int(65) = v
  val () = $A.barr_free(a)
in () end
