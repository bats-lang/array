#include "share/atspre_staload.hats"
#use array as A

(* A size computed at run time is not a class, whatever proof is given
   with it. *)
fn make {n:pos | n <= 65536} (n: int n): void =
  case+ $A.arena_create<byte>($A.Arena64KiB() | n) of
  | ~$A.arena_some(ar) => $A.arena_destroy<byte>(ar)
  | ~$A.arena_none() => ()

implement main0 () = make(1000)
