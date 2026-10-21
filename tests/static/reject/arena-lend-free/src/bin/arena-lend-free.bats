#include "share/atspre_staload.hats"
#use array as A

(* A lent piece cannot be freed as a barr: the lend is not given back, so
   the proof is left unconsumed. *)
implement main0 () =
  case+ $A.arena_create<byte>($A.Arena64KiB() | 65536) of
  | ~$A.arena_some(ar) => let
      val p = $A.arena_alloc<byte>(ar, 10)
      val (len, lent | b) = $A.barr_of_arrx(p)
      val () = $A.barr_free(b)
    in $A.arena_destroy<byte>(ar) end
  | ~$A.arena_none() => ()
