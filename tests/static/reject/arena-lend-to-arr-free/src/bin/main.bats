#include "share/atspre_staload.hats"
#use array as A

(* barr_to_arr forgets the owner, so the lent piece becomes an arr that
   free takes. The lend is still out (barr_to_arr does not consume it) and
   no barr at that address is left to give it back with: the proof is left
   unconsumed. *)
implement main0 () =
  case+ $A.arena_create<byte>($A.Arena64KiB() | 65536) of
  | ~$A.arena_some(ar) => let
      val p = $A.arena_alloc<byte>(ar, 10)
      val (len, lent | b) = $A.barr_of_arrx(p)
      val a = $A.barr_to_arr(b)
      val () = $A.free<byte>(a)
    in $A.arena_destroy<byte>(ar) end
  | ~$A.arena_none() => ()
