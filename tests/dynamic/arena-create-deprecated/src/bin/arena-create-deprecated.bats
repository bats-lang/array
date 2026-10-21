#include "share/atspre_staload.hats"
#use array as A

(* The deprecated arena_create (arena class, array#67) keeps working for each
   element type it had, with a size that is no class; an edit cannot drop it
   without this test failing (as process's tests/dynamic/oldspawn). *)
implement main0 () = let
  val () = (case+ $A.arena_create<byte>(5000) of
    | ~$A.arena_some(ar) => let
        val p = $A.arena_alloc<byte>(ar, 3000)
        val q = $A.arena_alloc<byte>(ar, 2000)
        val () = $A.set<byte>(p, 2999, $A.int2byte(7))
        val () = $A.set<byte>(q, 0, $A.int2byte(8))
        val () = println! ("byte ", byte2int0($A.get<byte>(p, 2999)), " ", byte2int0($A.get<byte>(q, 0)), " ", byte2int0($A.get<byte>(q, 1999)))
        val () = $A.arena_return<byte>(ar, p)
        val () = $A.arena_return<byte>(ar, q)
      in $A.arena_destroy<byte>(ar) end
    | ~$A.arena_none() => println! ("FAIL: no byte arena"))
  val () = (case+ $A.arena_create<char>(100) of
    | ~$A.arena_some(ar) => $A.arena_destroy<char>(ar)
    | ~$A.arena_none() => println! ("FAIL: no char arena"))
  val () = (case+ $A.arena_create<bool>(100) of
    | ~$A.arena_some(ar) => $A.arena_destroy<bool>(ar)
    | ~$A.arena_none() => println! ("FAIL: no bool arena"))
  val () = (case+ $A.arena_create<int>(1000) of
    | ~$A.arena_some(ar) => let
        val p = $A.arena_alloc<int>(ar, 1000)
        val () = $A.set<int>(p, 999, ~5)
        val () = println! ("int ", $A.get<int>(p, 999), " ", $A.get<int>(p, 0))
        val () = $A.arena_return<int>(ar, p)
      in $A.arena_destroy<int>(ar) end
    | ~$A.arena_none() => println! ("FAIL: no int arena"))
  val () = (case+ $A.arena_create<uint>(100) of
    | ~$A.arena_some(ar) => $A.arena_destroy<uint>(ar)
    | ~$A.arena_none() => println! ("FAIL: no uint arena"))
  val () = (case+ $A.arena_create<Int>(100) of
    | ~$A.arena_some(ar) => $A.arena_destroy<Int>(ar)
    | ~$A.arena_none() => println! ("FAIL: no Int arena"))
in () end
