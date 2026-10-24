#include "share/atspre_staload.hats"
#use array as A

(* The same bound as alloc: at most 1048576 elements. *)
implement main0 () = let
  val (len, zeros | a) = $A.iarr_alloc(1048577)
  val () = $A.iarr_free(a)
in () end
