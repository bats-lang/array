#include "share/atspre_staload.hats"
#use array as A

(* The arena has a piece out (k = 1) and that piece is lent as a barr, still
   held here: destroying the arena does not type-check. *)
fn destroy_while_lent {la:agz}{l:agz}{cs:$A.cells}
  (ar: $A.arena(byte, la, 16, 10, 1), lent: $A.arrx_lent(l, 10, la) | b: $A.barr(l, 10, cs))
  : ($A.arrx_lent(l, 10, la) | $A.barr(l, 10, cs)) = let
  val () = $A.arena_destroy<byte>(ar)
in (lent | b) end

implement main0 () = ()
