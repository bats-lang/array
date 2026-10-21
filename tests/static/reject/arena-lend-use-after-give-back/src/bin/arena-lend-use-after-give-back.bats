#include "share/atspre_staload.hats"
#use array as A

(* Giving the piece back consumes the barr: reading it afterwards does not
   type-check. *)
implement main0 () =
  case+ $A.arena_create_class<byte>($A.Arena64KiB() | 65536) of
  | ~$A.arena_some(ar) => let
      val p = $A.arena_alloc<byte>(ar, 10)
      val (len, lent | b) = $A.barr_of_arrx(p)
      val p = $A.barr_to_arrx(lent | b)
      val (r | v) = $A.barr_get(b, 3)
      val () = $A.arena_return<byte>(ar, p)
    in $A.arena_destroy<byte>(ar) end
  | ~$A.arena_none() => ()
