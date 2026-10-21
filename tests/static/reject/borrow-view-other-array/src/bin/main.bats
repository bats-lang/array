#include "share/atspre_staload.hats"
#use array as A


(* A view of one array is given back to another array's count. Each
   array's count is left as the function's type says (the first one
   more, the second one fewer), so the arrays differing is the only
   mistake. *)
fn view_to_other {l1,l2:agz}{cs1,cs2:$A.cells}{k1,k2:pos}
  (f1: !$A.cfrozen(l1, 4, k1, cs1) >> $A.cfrozen(l1, 4, k1+1, cs1),
   b1: !$A.cborrow(l1, 4, cs1),
   f2: !$A.cfrozen(l2, 4, k2, cs2) >> $A.cfrozen(l2, 4, k2-1, cs2)): void = let
  val view = $A.cborrow_view(f1, b1)
in $A.cborrow_view_drop(f2, view) end

implement main0 () = ()
