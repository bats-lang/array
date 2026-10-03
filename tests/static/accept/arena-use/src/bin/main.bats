#include "share/atspre_staload.hats"
#use array as A

(* Two pieces of 1 MiB each from a 4 MiB arena: read, write, freeze,
   return, destroy. *)
implement main0 () =
  case+ $A.arena_create<byte>($A.Arena4MiB() | 4194304) of
  | ~$A.arena_some(ar) => let
      val p = $A.arena_alloc<byte>(ar, 1048576)
      val q = $A.arena_alloc<byte>(ar, 1048576)
      val () = $A.set<byte>(p, 1048575, $A.int2byte(7))
      val b = $A.get<byte>(p, 1048575)
      val @(fz, bv) = $A.freeze<byte>(q)
      val c = $A.read<byte>(bv, 0)
      val () = $A.drop<byte>(fz, bv)
      val q = $A.thaw<byte>(fz)
      val () = $A.arena_return<byte>(ar, p)
      val () = $A.arena_return<byte>(ar, q)
    in $A.arena_destroy<byte>(ar) end
  | ~$A.arena_none() => ()
