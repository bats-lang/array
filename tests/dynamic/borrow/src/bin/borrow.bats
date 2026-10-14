#include "share/atspre_staload.hats"
#use array as A


(* Two cells set, the array frozen, two borrows of it read: each read is
   the cell that was set. The cells come back at thaw, and a read after a
   third cell is set and the array frozen again is the earlier cell. *)
implement main0 () = let
  val (len | a) = $A.barr_alloc(4)
  val (s0 | a) = $A.barr_set(a, 0, 65)
  val (s1 | a) = $A.barr_set(a, 1, 255)
  val (f, b) = $A.barr_freeze(a)
  val b2 = $A.cborrow_dup(f, b)
  val (r0 | v0) = $A.cborrow_get(b, 0)
  val (r1 | v1) = $A.cborrow_get(b2, 1)
  val (r2 | v2) = $A.cborrow_get(b2, 2)
  prval () = $A.nth_functional(r0, $A.setc_nth_other(s1, $A.setc_nth_same(s0)))
  prval () = $A.nth_functional(r1, $A.setc_nth_same(s1))
  val sixty_five: int(65) = v0
  val two_fifty_five: int(255) = v1
  val () = println! (v0, " ", v1, " ", v2)
  val () = $A.cborrow_drop(f, b2)
  val () = $A.cborrow_drop(f, b)
  val a = $A.barr_thaw(f)
  val (s2 | a) = $A.barr_set(a, 2, 7)
  val (g, c) = $A.barr_freeze(a)
  val (r3 | v3) = $A.cborrow_get(c, 2)
  val (r4 | v4) = $A.cborrow_get(c, 0)
  prval () = $A.nth_functional(r3, $A.setc_nth_same(s2))
  prval () = $A.nth_functional(r4, $A.setc_nth_other(s2, $A.setc_nth_other(s1, $A.setc_nth_same(s0))))
  val seven: int(7) = v3
  val sixty_five_again: int(65) = v4
  val () = println! (v3, " ", v4)
  val () = $A.cborrow_drop(g, c)
  val a = $A.barr_thaw(g)
  val () = $A.barr_free(a)
in () end
