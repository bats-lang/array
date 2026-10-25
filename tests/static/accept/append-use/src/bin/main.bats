#include "share/atspre_staload.hats"
#use array as A

(* [65] then [66, 67] is [65, 66, 67], built from the two constructors; a second
   proof of the same append has the same cells; the buffer [65, 66, 0] holds
   the chunk [65, 66]. *)
implement main0 () = let
  prval whole = $A.APPEND_cons{65}($A.APPEND_nil{$A.ccons(66, $A.ccons(67, $A.cnil()))}())
  prval other = $A.APPEND_cons{65}($A.APPEND_nil{$A.ccons(66, $A.ccons(67, $A.cnil()))}())
  prval $A.CELLS_EQ_refl() = $A.append_functional(whole, other)
  prval held: $A.HOLDS($A.ccons(65, $A.ccons(66, $A.ccons(0, $A.cnil()))), $A.ccons(65, $A.ccons(66, $A.cnil()))) =
    $A.HOLDS_mk($A.APPEND_cons{65}($A.APPEND_cons{66}($A.APPEND_nil{$A.ccons(0, $A.cnil())}())))
  prval _ = held
in () end
