#include "share/atspre_staload.hats"
#use array as A

(* The result is not an array: it cannot be used or freed before it is matched. *)
implement main0 () = let
  val a = $A.alloc_checked<byte>(4)
  val () = $A.free<byte>(a)
in () end
