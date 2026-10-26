#include "share/atspre_staload.hats"
#use array as A

(* The size bound of alloc (1048576 elements) holds for alloc_checked. *)
implement main0 () =
  case+ $A.alloc_checked<byte>(1048577) of
  | ~$A.alloc_some(a) => $A.free<byte>(a)
  | ~$A.alloc_none() => ()
