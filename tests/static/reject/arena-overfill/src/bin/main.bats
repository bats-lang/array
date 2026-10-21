#include "share/atspre_staload.hats"
#use array as A

(* 40000 + 40000 elements do not fit in an arena of 65536. *)
implement main0 () =
  case+ $A.arena_create<byte>($A.Arena64KiB() | 65536) of
  | ~$A.arena_some(ar) => let
      val p = $A.arena_alloc<byte>(ar, 40000)
      val q = $A.arena_alloc<byte>(ar, 40000)
      val () = $A.arena_return<byte>(ar, p)
      val () = $A.arena_return<byte>(ar, q)
    in $A.arena_destroy<byte>(ar) end
  | ~$A.arena_none() => ()
