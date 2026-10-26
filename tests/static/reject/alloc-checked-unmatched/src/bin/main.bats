#include "share/atspre_staload.hats"
#use array as A

(* The failure constructor is not matched: the result must be handled. *)
implement main0 () =
  case+ $A.alloc_checked<byte>(4) of
  | ~$A.alloc_some(a) => $A.free<byte>(a)
