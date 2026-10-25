#include "share/atspre_staload.hats"
#use array as A

(* The buffer [1] does not begin with the chunk [1, 2]. *)
implement main0 () = let
  prval wrong: $A.HOLDS($A.ccons(1, $A.cnil()), $A.ccons(1, $A.ccons(2, $A.cnil()))) =
    $A.HOLDS_mk($A.APPEND_cons{1}($A.APPEND_cons{2}($A.APPEND_nil{$A.cnil()}())))
  prval _ = wrong
in () end
