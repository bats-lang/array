#include "share/atspre_staload.hats"
#use array as A

(* A size with no class's proof is not taken. *)
implement main0 () =
  case+ $A.arena_create<byte>(65536) of
  | ~$A.arena_some(ar) => $A.arena_destroy<byte>(ar)
  | ~$A.arena_none() => ()
