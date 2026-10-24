#include "share/atspre_staload.hats"
#use array as A

(* A cell of cells within [0, 1000] is not claimed to be at most 999. *)
implement main0 () = let
  val (len, zeros | a) = $A.iarr_alloc(4)
  prval within = $A.allin_zeros{..}{0, 1000}(zeros)
  val x = $A.iarr_get_in(within | a, 1)
  val wrong: [v:int | v <= 999] int v = x
  val () = $A.iarr_free(a)
in () end
