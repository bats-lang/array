#include "share/atspre_staload.hats"
#use array as A

(* 1001 is not within [0, 1000]. *)
implement main0 () = let
  val (len, zeros | a) = $A.iarr_alloc(4)
  prval within = $A.allin_zeros{..}{0, 1000}(zeros)
  val (within | a) = $A.iarr_set_in(within | a, 1, 1001)
  val () = $A.iarr_free(a)
in () end
