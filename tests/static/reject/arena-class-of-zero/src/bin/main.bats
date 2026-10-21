#include "share/atspre_staload.hats"
#use array as A

(* A size of 0 has no class: arena_class_of takes a positive size. *)
fn hold (): void =
  case+ $A.arena_class_of(0) of
  | ~$A.arena_fits(class | max) =>
    (case+ $A.arena_create<byte>(class | max) of
     | ~$A.arena_some(ar) => $A.arena_destroy<byte>(ar)
     | ~$A.arena_none() => ())
  | ~$A.arena_too_large() => ()

implement main0 () = hold()
