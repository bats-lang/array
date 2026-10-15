#include "share/atspre_staload.hats"
#use array as A

(* A cell set, the array frozen, a view taken: the plain borrow and the
   content-indexed borrow are held together and read the same bytes, the
   plain one by read (any byte), the other with the cell's proof. The view
   is given back, the borrow dropped and the array thawed. *)
implement main0 () = let
  val (len | a) = $A.barr_alloc(4)
  val (s0 | a) = $A.barr_set(a, 0, 65)
  val (s1 | a) = $A.barr_set(a, 1, 255)
  val (f, b) = $A.barr_freeze(a)
  val view = $A.cborrow_view(f, b)
  val p0 = $A.read(view, 0)
  val p1 = $A.read(view, 1)
  val p2 = $A.read(view, 2)
  val (r0 | v0) = $A.cborrow_get(b, 0)
  val (r1 | v1) = $A.cborrow_get(b, 1)
  prval () = $A.nth_functional(r0, $A.setc_nth_other(s1, $A.setc_nth_same(s0)))
  prval () = $A.nth_functional(r1, $A.setc_nth_same(s1))
  val sixty_five: int(65) = v0
  val two_fifty_five: int(255) = v1
  val same = (byte2int0(p0) = v0) && (byte2int0(p1) = v1) && (byte2int0(p2) = 0)
  val () = println! (v0, " ", v1, " ", byte2int0(p2), " ", same)
  val () = $A.cborrow_view_drop(f, view)
  val () = $A.cborrow_drop(f, b)
  val a = $A.barr_thaw(f)
  val (s2 | a) = $A.barr_set(a, 2, 7)
  val () = $A.barr_free(a)
in () end
