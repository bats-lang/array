#include "share/atspre_staload.hats"
#use array as A

(* A cell is a 32-bit int: 2147483648 is not one. *)
implement main0 () = let
  val (len, zeros | a) = $A.iarr_alloc(4)
  val (set | a) = $A.iarr_set{..}{..}{..}{..}{2147483648}(a, 1, $UNSAFE.cast{int(2147483648)}(0))
  val () = $A.iarr_free(a)
in () end
