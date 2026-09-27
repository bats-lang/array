#include "share/atspre_staload.hats"
#use array as A

(* A string literal's text reads back its bytes, and writes them into an
   array as write_text does for any text *)
implement main0 () = let
  val t = $A.text_lit("qpgi")
  val () = println! ("bytes ",
    byte2int0($A.text_get(t, 0)), " ", byte2int0($A.text_get(t, 1)), " ",
    byte2int0($A.text_get(t, 2)), " ", byte2int0($A.text_get(t, 3)))
  val a = $A.alloc<byte>(6)
  val () = $A.write_text(a, 1, $A.text_lit("abcd"), 4)
  val () = println! ("written ", byte2int0($A.get<byte>(a, 0)), " ",
    byte2int0($A.get<byte>(a, 1)), " ", byte2int0($A.get<byte>(a, 4)), " ",
    byte2int0($A.get<byte>(a, 5)))
in $A.free<byte>(a) end
