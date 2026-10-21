#include "share/atspre_staload.hats"
#use array as A

(* 2 MiB is not a class: no constructor of ARENA_CLASS is indexed by
   it, so the 4 MiB one does not prove it. *)
implement main0 () =
  case+ $A.arena_create<byte>($A.Arena4MiB() | 2097152) of
  | ~$A.arena_some(ar) => $A.arena_destroy<byte>(ar)
  | ~$A.arena_none() => ()
