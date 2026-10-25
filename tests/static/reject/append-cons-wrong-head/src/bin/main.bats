#include "share/atspre_staload.hats"
#use array as A

(* [1] then nothing is [1], not [2]. *)
implement main0 () = let
  prval wrong: $A.APPEND($A.ccons(1, $A.cnil()), $A.cnil(), $A.ccons(2, $A.cnil())) = $A.APPEND_cons{1}($A.APPEND_nil())
  prval _ = wrong
in () end
