#include "share/atspre_staload.hats"
#use array as A

(* Cell 4 of 4 cells is past the end. *)
implement main0 () = let
  val (len, zeros | a) = $A.iarr_alloc(4)
  val (read | v) = $A.iarr_get(a, 4)
  val () = $A.iarr_free(a)
in () end
