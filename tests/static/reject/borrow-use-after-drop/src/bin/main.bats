#include "share/atspre_staload.hats"
#use array as A


(* As the accept fixture borrow-read, but the borrow is read after it was
   dropped: dropping consumed it. *)
implement main0 () = let
  val (len | a) = $A.barr_alloc(4)
  val (f, b) = $A.barr_freeze(a)
  val () = $A.cborrow_drop(f, b)
  val (read | v) = $A.cborrow_get(b, 0)
  val a = $A.barr_thaw(f)
  val () = $A.barr_free(a)
in () end
