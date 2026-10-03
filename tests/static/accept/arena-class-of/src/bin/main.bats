#include "share/atspre_staload.hats"
#use array as A

(* A size known only at run time takes the smallest class that holds
   it (arena_class_of), and a piece of that size fits there. *)
fn hold {n:pos} (n: int n): void =
  case+ $A.arena_class_of(n) of
  | ~$A.arena_fits(class | max) =>
    (case+ $A.arena_create<byte>(class | max) of
     | ~$A.arena_some(ar) => let
         val p = $A.arena_alloc<byte>(ar, n)
         val () = $A.arena_return<byte>(ar, p)
       in $A.arena_destroy<byte>(ar) end
     | ~$A.arena_none() => ())
  | ~$A.arena_too_large() => ()

implement main0 () = hold(300000)
