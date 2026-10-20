#include "share/atspre_staload.hats"
#use array as A


(* The proof of barr_set_inline says cell 0 holds 65 after the set; it is
   claimed to hold 66, which the proof of the set does not give. *)
prfn set_claimed_66 {cs,cs2:$A.cells} (s: $A.SETC(cs, 0, 66, cs2)): void = ()

implement main0 () = let
  val (len | a) = $A.barr_alloc(4)
  val (first | a) = $A.barr_set_inline(a, 0, 65)
  prval () = set_claimed_66(first)
  val () = $A.barr_free(a)
in () end
