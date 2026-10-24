#include "share/atspre_staload.hats"
#use array as A

(* An array is freed once. *)
implement main0 () = let
  val (len, zeros | a) = $A.iarr_alloc(4)
  val () = $A.iarr_free(a)
  val () = $A.iarr_free(a)
in () end
