#include "share/atspre_staload.hats"
#use array as A

(* alloc_checked (array allocation-failure). With no argument it runs with the
   address space the machine gives: every instance answers alloc_some, and the
   old alloc is called too, so an edit cannot drop it. With an argument (the
   file `ulimit-v` makes run.sh set `ulimit -v`) the address space is too small
   for 8 MiB: a small array is had, the big one is alloc_none and the program
   goes on instead of writing through a NULL array. *)
fn small () : void =
  case+ $A.alloc_checked<byte>(16) of
  | ~$A.alloc_some(a) => let
      val () = $A.set<byte>(a, 15, $A.int2byte(7))
      val () = println! ("small ", byte2int0($A.get<byte>(a, 15)))
    in $A.free<byte>(a) end
  | ~$A.alloc_none() => println! ("small none")

fn big () : void =
  case+ $A.alloc_checked<Int>(1048576) of
  | ~$A.alloc_some(a) => let
      val () = $A.set<Int>(a, 1048575, 9)
      val () = println! ("big ", $A.get<Int>(a, 1048575))
    in $A.free<Int>(a) end
  | ~$A.alloc_none() => println! ("big none")

fn kinds () : void = let
  val () = (case+ $A.alloc_checked<char>(2) of
    | ~$A.alloc_some(a) => $A.free<char>(a) | ~$A.alloc_none() => println! ("char none"))
  val () = (case+ $A.alloc_checked<bool>(2) of
    | ~$A.alloc_some(a) => $A.free<bool>(a) | ~$A.alloc_none() => println! ("bool none"))
  val () = (case+ $A.alloc_checked<int>(2) of
    | ~$A.alloc_some(a) => $A.free<int>(a) | ~$A.alloc_none() => println! ("int none"))
  val () = (case+ $A.alloc_checked<uint>(2) of
    | ~$A.alloc_some(a) => $A.free<uint>(a) | ~$A.alloc_none() => println! ("uint none"))
in () end

fn old_alloc () : void = let
  val a = $A.alloc<byte>(4)
  val () = $A.set<byte>(a, 3, $A.int2byte(5))
  val () = println! ("old ", byte2int0($A.get<byte>(a, 3)))
in $A.free<byte>(a) end

implement main0 () = let
  val () = small ()
  val () = big ()
  val () = kinds ()
in old_alloc () end
