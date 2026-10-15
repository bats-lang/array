#include "share/atspre_staload.hats"
#use array as A

(* A view taken, read through, given back, the borrow dropped, then thawed. *)
implement main0 () = let
  val (len | a) = $A.barr_alloc(4)
  val (f, b) = $A.barr_freeze(a)
  val view = $A.cborrow_view(f, b)
  val x = $A.read(view, 0)
  val () = $A.cborrow_view_drop(f, view)
  val () = $A.cborrow_drop(f, b)
  val a = $A.barr_thaw(f)
  val () = $A.barr_free(a)
in () end
