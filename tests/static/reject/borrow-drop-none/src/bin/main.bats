#include "share/atspre_staload.hats"
#use array as A


(* The accept fixture borrow-read drops a borrow of a frozen array with one
   out; here none is out (k = 0), so there is nothing to drop. *)
fn drop_none {l:agz}{cs:$A.cells}
  (f: !$A.cfrozen(l, 4, 0, cs), b: $A.cborrow(l, 4, cs)): void =
  $A.cborrow_drop(f, b)

implement main0 () = ()
