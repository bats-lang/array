#include "share/atspre_staload.hats"
#use array as A

(* A fresh array reads as zeros, not as 1. *)
implement main0 () = let
  val (len, zeros | a) = $A.iarr_alloc(4)
  val (read | v) = $A.iarr_get(a, 1)
  prval () = $A.zeros_nth(zeros, read)
  val wrong: int(1) = v
  val () = $A.iarr_free(a)
in () end
