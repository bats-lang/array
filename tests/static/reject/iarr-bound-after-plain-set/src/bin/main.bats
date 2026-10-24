#include "share/atspre_staload.hats"
#use array as A

(* iarr_set gives other cells (cs2): the bound proof of the old cells does
   not say the new ones are within it. *)
implement main0 () = let
  val (len, zeros | a) = $A.iarr_alloc(4)
  prval within = $A.allin_zeros{..}{0, 1000}(zeros)
  val (set | a) = $A.iarr_set(a, 1, 5000)
  val x = $A.iarr_get_in(within | a, 1)
  val () = $A.iarr_free(a)
in () end
