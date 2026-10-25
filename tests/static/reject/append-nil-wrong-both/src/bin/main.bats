#include "share/atspre_staload.hats"
#use array as A

(* Nothing followed by [1] is [1], not nothing. *)
implement main0 () = let
  prval wrong: $A.APPEND($A.cnil(), $A.ccons(1, $A.cnil()), $A.cnil()) = $A.APPEND_nil()
  prval _ = wrong
in () end
