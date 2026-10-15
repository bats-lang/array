#include "share/atspre_staload.hats"
#use array as A

(* The view is read after it was given back: giving it back consumed it. *)
implement main0 () = let
  val (len | a) = $A.barr_alloc(4)
  val (f, b) = $A.barr_freeze(a)
  val view = $A.cborrow_view(f, b)
  val () = $A.cborrow_view_drop(f, view)
  val () = $A.cborrow_drop(f, b)
  val a = $A.barr_thaw(f)
  val x = $A.read(view, 0)
  val () = $A.barr_free(a)
in () end
