#include "share/atspre_staload.hats"
#use array as A

(* A bound is widened, never narrowed: [0, 1000] does not give [0, 999]. *)
implement main0 () = let
  val (len, zeros | a) = $A.iarr_alloc(4)
  prval within = $A.allin_zeros{..}{0, 1000}(zeros)
  prval narrow = $A.allin_widen{..}{0, 1000, 0, 999}(within, len)
  val () = $A.iarr_free(a)
in () end
