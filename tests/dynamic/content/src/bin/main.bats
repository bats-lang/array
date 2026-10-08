#include "share/atspre_staload.hats"
#use array as A
staload C = "array/src/content.sats"

implement main0 () = let
  val (len | a) = $C.barr_alloc(4)
  val (s0 | a) = $C.barr_set(a, 0, 65)
  val (s1 | a) = $C.barr_set(a, 1, 255)
  val (s2 | a) = $C.barr_set(a, 3, 0)
  val b = $C.barr_copy(a, 4)
  val (r0 | v0) = $C.barr_get(b, 0)
  val (r1 | v1) = $C.barr_get(b, 1)
  val (r2 | v2) = $C.barr_get(b, 2)
  val (r3 | v3) = $C.barr_get(b, 3)
  val () = println! (v0, " ", v1, " ", v2, " ", v3)
  val raw = $C.barr_to_arr(a)
  val () = $A.set<byte>(raw, 2, $A.int2byte(7))
  val (len2 | back) = $C.barr_of_arr(raw)
  val (r4 | v4) = $C.barr_get(back, 2)
  val () = println! (v4)
  val () = $C.barr_free(back)
  val () = $C.barr_free(b)
in () end
