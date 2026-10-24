#include "share/atspre_staload.hats"
#use array as A

(* iarr_set consumes the array: the old one is not read after it. *)
implement main0 () = let
  val (len, zeros | a) = $A.iarr_alloc(4)
  val (set | b) = $A.iarr_set(a, 1, 5)
  val (read | v) = $A.iarr_get(a, 1)
  val () = $A.iarr_free(b)
in () end
