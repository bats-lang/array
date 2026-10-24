#include "share/atspre_staload.hats"
#use array as A

(* An int array as a caller reads it: a cell reads back what was set, the
   others as they were, a fresh array reads as zeros, and a read of cells
   all within [0, 1000] is indexed by the bound, so it is a position
   within 1000 without a clamp. *)
fn position {p:nat | p <= 1000} (p: int p): int p = p

implement main0 () = let
  val (len, zeros | a) = $A.iarr_alloc(4)
  val (fresh | v) = $A.iarr_get(a, 3)
  prval () = $A.zeros_nth(zeros, fresh)
  val zero: int(0) = v
  val (first | a) = $A.iarr_set(a, 0, 65)
  val (second | a) = $A.iarr_set(a, 1, ~7)
  prval kept = $A.setc_nth_other(second, $A.setc_nth_same(first))
  val (read | w) = $A.iarr_get(a, 0)
  prval () = $A.nth_functional(read, kept)
  val sixty_five: int(65) = w
  val () = $A.iarr_free(a)
  val (len2, zeros2 | b) = $A.iarr_alloc(4)
  prval within = $A.allin_zeros{..}{0, 1000}(zeros2)
  prval wide = $A.allin_widen{..}{0, 1000, ~5, 2000}(within, len2)
  val (within | b) = $A.iarr_set_in(within | b, 2, 999)
  val x = $A.iarr_get_in(within | b, 2)
  val spot = position(x)
  val () = $A.iarr_free(b)
in () end
