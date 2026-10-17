#include "share/atspre_staload.hats"
#use array as A

(* A piece belongs to its arena: free does not take it. *)
implement main0 () =
  case+ $A.arena_create<byte>($A.Arena64KiB() | 65536) of
  | ~$A.arena_some(ar) => let
      val p = $A.arena_alloc<byte>(ar, 10)
      val () = $A.free<byte>(p)
    in $A.arena_destroy<byte>(ar) end
  | ~$A.arena_none() => ()
