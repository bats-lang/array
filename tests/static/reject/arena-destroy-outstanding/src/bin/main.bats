#include "share/atspre_staload.hats"
#use array as A

(* An arena with a piece outstanding (k = 1) cannot be destroyed. *)
fn destroy_early {l:agz} (ar: $A.arena(byte, l, 65536, 10, 1)): void =
  $A.arena_destroy<byte>(ar)

implement main0 () = ()
