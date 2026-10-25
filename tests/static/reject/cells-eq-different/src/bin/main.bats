#include "share/atspre_staload.hats"
#use array as A

(* [1] and [2] are not the same cells. *)
implement main0 () = let
  prval wrong: $A.CELLS_EQ($A.ccons(1, $A.cnil()), $A.ccons(2, $A.cnil())) = $A.CELLS_EQ_refl()
  prval _ = wrong
in () end
