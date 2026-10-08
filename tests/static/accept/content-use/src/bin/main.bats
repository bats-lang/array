#include "share/atspre_staload.hats"
#use array as A
staload C = "array/src/content.sats"

(* Two cells set, the first read back: the types know it is what was set,
   though the second was set after it. *)
implement main0 () = let
  val (len | a) = $C.barr_alloc(4)
  val (first | a) = $C.barr_set(a, 0, 65)
  val (second | a) = $C.barr_set(a, 1, 66)
  prval kept = $C.setc_nth_other(second, $C.setc_nth_same(first))
  val (read | v) = $C.barr_get(a, 0)
  prval () = $C.nth_functional(read, kept)
  val sixty_five: int(65) = v
  val () = $C.barr_free(a)
in () end
