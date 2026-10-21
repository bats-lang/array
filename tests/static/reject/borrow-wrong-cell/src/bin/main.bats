#include "share/atspre_staload.hats"
#use array as A


(* The cell set to 65 is not 66, read through a borrow as well. *)
implement main0 () = let
  val (len | a) = $A.barr_alloc(4)
  val (first | a) = $A.barr_set(a, 0, 65)
  val (f, b) = $A.barr_freeze(a)
  val (read | v) = $A.cborrow_get(b, 0)
  prval () = $A.nth_functional(read, $A.setc_nth_same(first))
  val wrong: int(66) = v
  val () = $A.cborrow_drop(f, b)
  val a = $A.barr_thaw(f)
  val () = $A.barr_free(a)
in () end
