#include "share/atspre_staload.hats"
#use array as A

(* An array is freed: a linear value is not dropped. *)
implement main0 () = let
  val (len, zeros | a) = $A.iarr_alloc(4)
in () end
