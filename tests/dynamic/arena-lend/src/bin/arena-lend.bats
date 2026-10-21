#include "share/atspre_staload.hats"
#use array as A

(* A piece of an arena lent as a barr and given back: a cell set, the barr
   frozen, read through a cborrow (the cell that was set, with the proof),
   thawed, and returned to its arena, which is then destroyed. The piece
   is past the 1 MiB alloc bound, and what was written through the barr is
   read through the piece after it is given back. *)
implement main0 () =
  case+ $A.arena_create_class<byte>($A.Arena4MiB() | 4194304) of
  | ~$A.arena_some(ar) => let
      val p = $A.arena_alloc<byte>(ar, 1048577)
      val () = $A.set<byte>(p, 5, $A.int2byte(9))
      val (len, lent | b) = $A.barr_of_arrx(p)
      val (s0 | b) = $A.barr_set(b, 1048576, 200)
      val (fz, bv) = $A.barr_freeze(b)
      val (r0 | v0) = $A.cborrow_get(bv, 1048576)
      prval () = $A.nth_functional(r0, $A.setc_nth_same(s0))
      val two_hundred: int(200) = v0
      val () = println! (v0)
      val () = $A.cborrow_drop(fz, bv)
      val b = $A.barr_thaw(fz)
      val p = $A.barr_to_arrx(lent | b)
      val c5 = $A.get<byte>(p, 5)
      val c_last = $A.get<byte>(p, 1048576)
      val () = println! (byte2int0(c5), " ", byte2int0(c_last))
      val () = $A.arena_return<byte>(ar, p)
    in $A.arena_destroy<byte>(ar) end
  | ~$A.arena_none() => ()
