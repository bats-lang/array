#include "share/atspre_staload.hats"
#use array as A

(* The buffer [1, 2] begins with [1], not with [2]. *)
implement main0 () = let
  prval wrong: $A.HOLDS($A.ccons(1, $A.ccons(2, $A.cnil())), $A.ccons(2, $A.cnil())) =
    $A.HOLDS_mk($A.APPEND_cons{1}($A.APPEND_nil{$A.ccons(2, $A.cnil())}()))
  prval _ = wrong
in () end
