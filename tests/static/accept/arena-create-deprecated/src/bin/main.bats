#include "share/atspre_staload.hats"
#use array as A

(* The deprecated arena_create (arena class, array#67) still takes any size
   up to 268435456, a class or not, and gives the same arena type. *)
implement main0 () =
  case+ $A.arena_create<byte>(5000) of
  | ~$A.arena_some(ar) => let
      val p = $A.arena_alloc<byte>(ar, 5000)
      val () = $A.arena_return<byte>(ar, p)
    in $A.arena_destroy<byte>(ar) end
  | ~$A.arena_none() => ()
