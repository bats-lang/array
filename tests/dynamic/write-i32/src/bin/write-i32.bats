(* write_i32 stores little-endian two's complement bytes at any offset,
   including one that is not a multiple of 4. *)

#include "share/atspre_staload.hats"

#use array as A

fun show {l:agz}{n,i:nat | i <= n} .<n - i>.
  (a: !$A.arr(byte, l, n), i: int i, n: int n): void =
  if i < n then let
    val () = print_int(byte2int0($A.get<byte>(a, i)))
    val () = print_string(if i + 1 < n then " " else "\n")
  in show(a, i + 1, n) end

implement main0 () = let
  val a = $A.alloc<byte>(9)
  val () = $A.write_i32(a, 1, 16909060)
  val () = $A.write_i32(a, 5, ~2)
  val () = show(a, 0, 9)
in $A.free<byte>(a) end
