#include "share/atspre_staload.hats"
#use array as A

(* A negative size has no class: arena_class_of takes a positive size. *)
fn hold (): void =
  case+ $A.arena_class_of(~1) of
  | ~$A.arena_fits(class | max) =>
    (case+ $A.arena_create_class<byte>(class | max) of
     | ~$A.arena_some(ar) => $A.arena_destroy<byte>(ar)
     | ~$A.arena_none() => ())
  | ~$A.arena_too_large() => ()

implement main0 () = hold()
