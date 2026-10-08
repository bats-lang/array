#include "share/atspre_staload.hats"
#use array as A


(* Cell 4 of 4 cells. *)
implement main0 () = let
  val (len | a) = $A.barr_alloc(4)
  val (read | v) = $A.barr_get(a, 4)
  val () = $A.barr_free(a)
in () end
