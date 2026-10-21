#include "share/atspre_staload.hats"
#use array as A

(* A piece lent as a barr comes back as a piece of its own arena: returning
   it to another arena does not type-check. *)
implement main0 () =
  case+ $A.arena_create<byte>($A.Arena64KiB() | 65536) of
  | ~$A.arena_some(a1) => (case+ $A.arena_create<byte>($A.Arena64KiB() | 65536) of
    | ~$A.arena_some(a2) => let
        val p = $A.arena_alloc<byte>(a1, 10)
        val q = $A.arena_alloc<byte>(a2, 10)
        val (len, lent | b) = $A.barr_of_arrx(p)
        val p = $A.barr_to_arrx(lent | b)
        val () = $A.arena_return<byte>(a2, p)
        val () = $A.arena_return<byte>(a1, q)
        val () = $A.arena_destroy<byte>(a1)
      in $A.arena_destroy<byte>(a2) end
    | ~$A.arena_none() => $A.arena_destroy<byte>(a1))
  | ~$A.arena_none() => ()
