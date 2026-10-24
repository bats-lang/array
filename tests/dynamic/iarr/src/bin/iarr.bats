#include "share/atspre_staload.hats"
#use array as A

(* The trusted primitives of the int arrays (keyword: iarr width): a fresh
   array reads as zeros, a cell reads back what was set, a set leaves the
   other cells, the ends of the 32-bit range survive, and a run of 3000
   pseudo-random sets (a fixed seed) agrees with a plain array at every
   cell. The bounded reads give the same numbers. *)

(* a pseudo-random generator, a linear congruence on 16 bits of the state
   (kept small so that no step overflows an int) *)
fn next (s: int): int = nmod(s * 75 + 74, 65537)

fun model_run {l:agz}{n:pos}{cs:$A.cells}{lm:agz}{steps:nat} .<steps>.
  (a: $A.iarr(l, n, cs), n: int n, model: !$A.arr(int, lm, n), seed: int, steps: int steps)
  : [cs2:$A.cells] $A.iarr(l, n, cs2) =
  if steps <= 0 then a
  else let
    val s1 = next(seed)
    val i = nmod(s1, n)
    val s2 = next(s1)
    val v = s2 - 30000
    val (set_proof | a2) = $A.iarr_set(a, i, v)
    val () = $A.set<int>(model, i, v)
  in model_run(a2, n, model, s2, steps - 1) end

fun compare {l:agz}{n:pos}{cs:$A.cells}{lm:agz}{i:nat | i <= n} .<n - i>.
  (a: !$A.iarr(l, n, cs), n: int n, model: !$A.arr(int, lm, n), i: int i, differences: int): int =
  if i >= n then differences
  else let
    val (read | v) = $A.iarr_get(a, i)
    val w = $A.get<int>(model, i)
  in compare(a, n, model, i + 1, (if v = w then differences else differences + 1)) end

implement main0 () = let
  val (len, zeros | a) = $A.iarr_alloc(6)
  val (z0 | v0) = $A.iarr_get(a, 0)
  val (z5 | v5) = $A.iarr_get(a, 5)
  val () = println! (v0, " ", v5)
  val (s0 | a) = $A.iarr_set(a, 0, 65)
  val (s1 | a) = $A.iarr_set(a, 1, ~1)
  val (s2 | a) = $A.iarr_set(a, 2, 2147483647)
  val (s3 | a) = $A.iarr_set(a, 3, ~2147483648)
  val (s4 | a) = $A.iarr_set(a, 0, 66)
  val (r0 | w0) = $A.iarr_get(a, 0)
  val (r1 | w1) = $A.iarr_get(a, 1)
  val (r2 | w2) = $A.iarr_get(a, 2)
  val (r3 | w3) = $A.iarr_get(a, 3)
  val (r4 | w4) = $A.iarr_get(a, 4)
  val () = println! (w0, " ", w1, " ", w2, " ", w3, " ", w4)
  val () = $A.iarr_free(a)
  (* the bounded forms: every cell in [0, 1000] *)
  val (len2, zeros2 | b) = $A.iarr_alloc(8)
  prval inb = $A.allin_zeros{..}{0, 1000}(zeros2)
  val (inb | b) = $A.iarr_set_in(inb | b, 3, 1000)
  val (inb | b) = $A.iarr_set_in(inb | b, 4, 7)
  val x3 = $A.iarr_get_in(inb | b, 3)
  val x4 = $A.iarr_get_in(inb | b, 4)
  val x7 = $A.iarr_get_in(inb | b, 7)
  val () = println! (x3, " ", x4, " ", x7)
  val () = $A.iarr_free(b)
  (* a run against a plain array *)
  val (len3, zeros3 | c) = $A.iarr_alloc(64)
  val model = $A.alloc<int>(64)
  val c = model_run(c, 64, model, 12345, 3000)
  val differences = compare(c, 64, model, 0, 0)
  val () = println! ("differences ", differences)
  val () = $A.free<int>(model)
  val () = $A.iarr_free(c)
in () end
