#include "share/atspre_staload.hats"
#use array as A

(* An arena hands out more than one alloc may (three 1 MiB pieces of a
   3 MiB arena); pieces start as zero bytes, keep what is written to
   them, do not overlap, and all go back before the arena is destroyed. *)
implement main0 () = let
  val () = (case+ $A.arena_create<byte>(3145728) of
    | ~$A.arena_some(ar) => let
        val p = $A.arena_alloc<byte>(ar, 1048576)
        val q = $A.arena_alloc<byte>(ar, 1048576)
        val r = $A.arena_alloc<byte>(ar, 1048576)
        val z = byte2int0($A.get<byte>(q, 524288))
        val () = $A.set<byte>(p, 1048575, $A.int2byte(1))
        val () = $A.set<byte>(q, 0, $A.int2byte(2))
        val () = $A.set<byte>(q, 1048575, $A.int2byte(3))
        val () = $A.set<byte>(r, 0, $A.int2byte(4))
        val () = println! ("zero ", z, ", edges ",
          byte2int0($A.get<byte>(p, 1048575)), " ",
          byte2int0($A.get<byte>(q, 0)), " ",
          byte2int0($A.get<byte>(q, 1048575)), " ",
          byte2int0($A.get<byte>(r, 0)))
        val () = $A.arena_return<byte>(ar, p)
        val () = $A.arena_return<byte>(ar, q)
        val () = $A.arena_return<byte>(ar, r)
      in $A.arena_destroy<byte>(ar) end
    | ~$A.arena_none() => println! ("FAIL: no arena"))
  val () = (case+ $A.arena_create<int>(1000) of
    | ~$A.arena_some(ar) => let
        val p = $A.arena_alloc<int>(ar, 600)
        val q = $A.arena_alloc<int>(ar, 400)
        val () = $A.set<int>(p, 599, ~5)
        val () = $A.set<int>(q, 0, 6)
        val () = println! ("ints ", $A.get<int>(p, 599), " ", $A.get<int>(q, 0), " ", $A.get<int>(q, 399))
        val () = $A.arena_return<int>(ar, q)
        val () = $A.arena_return<int>(ar, p)
      in $A.arena_destroy<int>(ar) end
    | ~$A.arena_none() => println! ("FAIL: no arena"))
in () end
