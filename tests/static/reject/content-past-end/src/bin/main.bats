#include "share/atspre_staload.hats"
#use array as A
staload C = "array/src/content.sats"

(* Cell 4 of 4 cells. *)
implement main0 () = let
  val (len | a) = $C.barr_alloc(4)
  val (read | v) = $C.barr_get(a, 4)
  val () = $C.barr_free(a)
in () end
