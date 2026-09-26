#use array as A

(* Zero bytes are a valid byte, char, bool, int, uint and Int. *)
implement main0 () = let
  val b = $A.alloc<byte>(2)
  val c = $A.alloc<char>(2)
  val t = $A.alloc<bool>(2)
  val i = $A.alloc<int>(2)
  val u = $A.alloc<uint>(2)
  val g = $A.alloc<Int>(2)
  val () = $A.free<byte>(b)
  val () = $A.free<char>(c)
  val () = $A.free<bool>(t)
  val () = $A.free<int>(i)
  val () = $A.free<uint>(u)
  val () = $A.free<Int>(g)
in () end
