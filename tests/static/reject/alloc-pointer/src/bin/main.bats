#use array as A

(* Zero bytes are a null string: there is no alloc<string>. *)
implement main0 () = let
  val s = $A.alloc<string>(2)
in $A.free<string>(s) end
