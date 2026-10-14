#include "share/atspre_staload.hats"
#use array as A


(* The array cannot be thawed (and so set) while a borrow of it is out:
   one borrow is out of this frozen array. *)
fn thaw_one_out {l:agz}{cs:$A.cells} (f: $A.cfrozen(l, 4, 1, cs)): $A.barr(l, 4, cs) =
  $A.barr_thaw(f)

implement main0 () = ()
