#include "share/atspre_staload.hats"
#use array as A


(* The array cannot be thawed (and so set) while a borrow of it is out. *)
implement main0 () = let
  val (len | a) = $A.barr_alloc(4)
  val (f, b) = $A.barr_freeze(a)
  val a = $A.barr_thaw(f)
  val () = $A.barr_free(a)
  val () = $A.cborrow_drop(f, b)
in () end
