#include "share/atspre_staload.hats"
#use array as A

(* [1] then [2] is [1, 2]; [2] then [1] is not. *)
implement main0 () = let
  prval ab: $A.APPEND($A.ccons(1, $A.cnil()), $A.ccons(2, $A.cnil()), $A.ccons(1, $A.ccons(2, $A.cnil()))) =
    $A.APPEND_cons{1}($A.APPEND_nil{$A.ccons(2, $A.cnil())}())
  prval wrong: $A.APPEND($A.ccons(2, $A.cnil()), $A.ccons(1, $A.cnil()), $A.ccons(1, $A.ccons(2, $A.cnil()))) = ab
  prval _ = wrong
in () end
