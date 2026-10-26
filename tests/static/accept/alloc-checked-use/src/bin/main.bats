#include "share/atspre_staload.hats"
#use array as A

(* alloc_checked: both constructors matched, an array had is used and freed. *)
implement main0 () =
  case+ $A.alloc_checked<byte>(4) of
  | ~$A.alloc_some(a) => let
      val () = $A.set<byte>(a, 3, $A.int2byte(1))
    in $A.free<byte>(a) end
  | ~$A.alloc_none() => ()
