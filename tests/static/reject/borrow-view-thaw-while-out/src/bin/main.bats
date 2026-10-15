#include "share/atspre_staload.hats"
#use array as A

(* The borrow is dropped but the view is still out: one borrow is out
   (the view), so the array cannot be thawed (and so set). *)
fn thaw_view_out {l:agz}{cs:$A.cells}
  (f: $A.cfrozen(l, 4, 1, cs), b: $A.cborrow(l, 4, cs)): @($A.barr(l, 4, cs), $A.borrow(byte, l, 4)) = let
  var f = f
  val view = $A.cborrow_view(f, b)
  val () = $A.cborrow_drop(f, b)
  val a = $A.barr_thaw(f)
in @(a, view) end

implement main0 () = ()
