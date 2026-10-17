#include "share/atspre_staload.hats"
#use array as A

(* Zero bytes are a null string: there is no arena_create<string>. *)
implement main0 () =
  case+ $A.arena_create<string>($A.Arena64KiB() | 65536) of
  | ~$A.arena_some(ar) => $A.arena_destroy<string>(ar)
  | ~$A.arena_none() => ()
