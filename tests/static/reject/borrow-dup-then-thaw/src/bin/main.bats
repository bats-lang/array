#include "share/atspre_staload.hats"
#use array as A


(* As the accept fixture borrow-read, but the borrow is duplicated and only
   the original dropped: the copy is still out (one borrow, duplicated to
   two, dropped to one), so the array cannot be thawed (and so set). *)
fn thaw_with_copy_out {l:agz}{cs:$A.cells}
  (f: $A.cfrozen(l, 4, 1, cs), b: $A.cborrow(l, 4, cs)): @($A.barr(l, 4, cs), $A.cborrow(l, 4, cs)) = let
  var f = f
  val copy = $A.cborrow_dup(f, b)
  val () = $A.cborrow_drop(f, b)
  val a = $A.barr_thaw(f)
in @(a, copy) end

implement main0 () = ()
