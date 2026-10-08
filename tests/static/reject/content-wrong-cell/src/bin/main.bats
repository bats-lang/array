#include "share/atspre_staload.hats"
#use array as A
staload C = "array/src/content.sats"

(* The cell set to 65 is not 66. *)
implement main0 () = let
  val (len | a) = $C.barr_alloc(4)
  val (first | a) = $C.barr_set(a, 0, 65)
  val (read | v) = $C.barr_get(a, 0)
  prval () = $C.nth_functional(read, $C.setc_nth_same(first))
  val wrong: int(66) = v
  val () = $C.barr_free(a)
in () end
