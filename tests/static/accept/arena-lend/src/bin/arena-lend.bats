#include "share/atspre_staload.hats"
#use array as A

(* A piece lent as a barr, set, read and given back to the arena it came
   from. *)
implement main0 () =
  case+ $A.arena_create<byte>(16) of
  | ~$A.arena_some(ar) => let
      val p = $A.arena_alloc<byte>(ar, 10)
      val (len, lent | b) = $A.barr_of_arrx(p)
      val (s0 | b) = $A.barr_set(b, 3, 7)
      val p = $A.barr_to_arrx(lent | b)
      val () = $A.arena_return<byte>(ar, p)
    in $A.arena_destroy<byte>(ar) end
  | ~$A.arena_none() => ()
