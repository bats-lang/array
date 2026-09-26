#include "share/atspre_staload.hats"
#use array as A

(* 10 + 10 elements do not fit in an arena of 16. *)
implement main0 () =
  case+ $A.arena_create<byte>(16) of
  | ~$A.arena_some(ar) => let
      val p = $A.arena_alloc<byte>(ar, 10)
      val q = $A.arena_alloc<byte>(ar, 10)
      val () = $A.arena_return<byte>(ar, p)
      val () = $A.arena_return<byte>(ar, q)
    in $A.arena_destroy<byte>(ar) end
  | ~$A.arena_none() => ()
