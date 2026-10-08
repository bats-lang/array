(* content -- byte arrays whose contents are in their types *)
(* An array of bytes that knows what it holds: `barr(l, n, cs)` holds the
   cells cs, a list in the types. Reading a cell gives the proof that it is
   that cell of cs; writing one gives the proof of the cells it leaves.
   What a program proves about the bytes it reads and writes is then checked
   by the compiler, not tested. *)

#include "share/atspre_staload.hats"

staload "./lib.bats"

(* ============================================================
   What an array holds
   ============================================================ *)

(* The cells of an array, first to last *)
#pub datasort cells =
  | cnil of ()
  | ccons of (int, cells)

(* CLEN(cs, n): cs has n cells *)
#pub dataprop CLEN(cells, int) =
  | CLEN_nil(cnil(), 0)
  | {c:int}{cs:cells}{n:nat} CLEN_cons(ccons(c, cs), n + 1) of CLEN(cs, n)

(* NTH(cs, i, v): cell i of cs is v *)
#pub dataprop NTH(cells, int, int) =
  | {c:int}{cs:cells} NTH_here(ccons(c, cs), 0, c)
  | {c,v:int}{cs:cells}{i:nat} NTH_there(ccons(c, cs), i + 1, v) of NTH(cs, i, v)

(* SETC(cs, i, v, cs2): cs2 is cs with its cell i set to v *)
#pub dataprop SETC(cells, int, int, cells) =
  | {c,v:int}{cs:cells} SETC_here(ccons(c, cs), 0, v, ccons(v, cs))
  | {c,v:int}{cs,cs2:cells}{i:nat} SETC_there(ccons(c, cs), i + 1, v, ccons(c, cs2)) of SETC(cs, i, v, cs2)

(* ============================================================
   What the cells of an array are, proved
   ============================================================ *)

(* Setting a cell leaves the number of cells *)
#pub prfun setc_len {cs,cs2:cells}{i:nat}{v:int}{n:nat} (SETC(cs, i, v, cs2), CLEN(cs, n)): CLEN(cs2, n)

prfun _setc_len {cs,cs2:cells}{i:nat}{v:int}{n:nat} .<n>. (s: SETC(cs, i, v, cs2), l: CLEN(cs, n)): CLEN(cs2, n) =
  case+ s of
  | SETC_here() => (case+ l of CLEN_cons(l1) => CLEN_cons(l1))
  | SETC_there(s1) => (case+ l of CLEN_cons(l1) => CLEN_cons(_setc_len(s1, l1)))

primplement setc_len {cs,cs2}{i}{v}{n} (s, l) = _setc_len(s, l)

(* The cell that was set is the value *)
#pub prfun setc_nth_same {cs,cs2:cells}{i:nat}{v:int} (SETC(cs, i, v, cs2)): NTH(cs2, i, v)

prfun _setc_nth_same {cs,cs2:cells}{i:nat}{v:int} .<i>. (s: SETC(cs, i, v, cs2)): NTH(cs2, i, v) =
  case+ s of
  | SETC_here() => NTH_here()
  | SETC_there(s1) => NTH_there(_setc_nth_same(s1))

primplement setc_nth_same {cs,cs2}{i}{v} (s) = _setc_nth_same(s)

(* The others are as they were *)
#pub prfun setc_nth_other {cs,cs2:cells}{i,j:nat | i != j}{v,w:int} (SETC(cs, i, v, cs2), NTH(cs, j, w)): NTH(cs2, j, w)

prfun _setc_nth_other {cs,cs2:cells}{i,j:nat | i != j}{v,w:int} .<i>. (s: SETC(cs, i, v, cs2), p: NTH(cs, j, w)): NTH(cs2, j, w) =
  case+ s of
  | SETC_here() => (case+ p of NTH_there(p1) => NTH_there(p1))
  | SETC_there(s1) =>
    (case+ p of
     | NTH_here() => NTH_here()
     | NTH_there(p1) => NTH_there(_setc_nth_other(s1, p1)))

primplement setc_nth_other {cs,cs2}{i,j}{v,w} (s, p) = _setc_nth_other(s, p)

(* A cell is within the cells *)
#pub prfun nth_in_len {cs:cells}{i:nat}{v:int}{n:nat} (NTH(cs, i, v), CLEN(cs, n)): [i < n] void

prfun _nth_in_len {cs:cells}{i:nat}{v:int}{n:nat} .<i>. (p: NTH(cs, i, v), l: CLEN(cs, n)): [i < n] void =
  case+ p of
  | NTH_here() => (case+ l of CLEN_cons(_) => ())
  | NTH_there(p1) => (case+ l of CLEN_cons(l1) => _nth_in_len(p1, l1))

primplement nth_in_len {cs}{i}{v}{n} (p, l) = _nth_in_len(p, l)

(* A cell has one value *)
#pub prfun nth_functional {cs:cells}{i:nat}{v,w:int} (NTH(cs, i, v), NTH(cs, i, w)): [v == w] void

prfun _nth_functional {cs:cells}{i:nat}{v,w:int} .<i>. (p: NTH(cs, i, v), q: NTH(cs, i, w)): [v == w] void =
  case+ p of
  | NTH_here() => (case+ q of NTH_here() => ())
  | NTH_there(p1) => (case+ q of NTH_there(q1) => _nth_functional(p1, q1))

primplement nth_functional {cs}{i}{v,w} (p, q) = _nth_functional(p, q)

(* ============================================================
   The array
   ============================================================ *)

(* n bytes at l holding the cells cs *)
#pub absvtype barr(l:addr, n:int, cs:cells) = ptr


(* n bytes, all zero, which the types know nothing more of *)
#pub fun barr_alloc {n:pos | n <= 1048576} (n: int n): [l:agz][cs:cells] (CLEN(cs, n) | barr(l, n, cs))

#pub fun barr_free {l:agz}{n:nat}{cs:cells} (a: barr(l, n, cs)): void

(* Cell i, with the proof that it is cell i of the cells *)
#pub fun barr_get {l:agz}{n,i:nat | i < n}{cs:cells} (a: !barr(l, n, cs), i: int i)
  : [v:int | 0 <= v; v < 256] (NTH(cs, i, v) | int v)

(* Cell i set to v: the cells that are left, with the proof that they are *)
#pub fun barr_set {l:agz}{n,i:nat | i < n}{cs:cells}{v:int | 0 <= v; v < 256} (a: barr(l, n, cs), i: int i, v: int v)
  : [cs2:cells] (SETC(cs, i, v, cs2) | barr(l, n, cs2))

(* The array that alloc gives, taken to hold cells nothing is known of; it
   is not an array of alloc any more *)
#pub fun barr_of_arr {l:agz}{n:nat} (a: arr(byte, l, n)): [cs:cells] (CLEN(cs, n) | barr(l, n, cs))

(* The array without its cells, to be written by what knows nothing of them *)
#pub fun barr_to_arr {l:agz}{n:nat}{cs:cells} (a: barr(l, n, cs)): arr(byte, l, n)

(* Another array holding the same cells *)
#pub fun barr_copy {l:agz}{n:pos}{cs:cells} (a: !barr(l, n, cs), n: int n): [m:agz] barr(m, n, cs)

(* ============================================================
   Implementation -- an array of bytes is its address (trusted core)
   ============================================================ *)

local

$UNSAFE begin
  assume barr(l, n, cs) = ptr l
  assume arrx(a, l, n, o) = ptr l
end

in

$UNSAFE begin extern fun _calloc_bytes (n: int, size: size_t): [l:agz] ptr l = "mac#calloc" end

implement barr_alloc {n} (n) =
  $UNSAFE begin
    $UNSAFE.castvwtp0{[l:agz][cs:cells] (CLEN(cs, n) | barr(l, n, cs))}(_calloc_bytes(n, sizeof<byte>))
  end

implement barr_free {l}{n}{cs} (a) =
  $UNSAFE begin $extfcall(void, "free", a) end

implement barr_get {l}{n,i}{cs} (a, i) =
  $UNSAFE begin
    $UNSAFE.cast{[v:int | 0 <= v; v < 256] (NTH(cs, i, v) | int v)}(byte2int0($UNSAFE.ptr0_get<byte>(ptr_add<byte>(a, i))))
  end

implement barr_set {l}{n,i}{cs}{v} (a, i, v) = let
  val () = $UNSAFE begin $UNSAFE.ptr0_set<byte>(ptr_add<byte>(a, i), $UNSAFE.cast{byte}(v)) end
in
  $UNSAFE begin $UNSAFE.castvwtp0{[cs2:cells] (SETC(cs, i, v, cs2) | barr(l, n, cs2))}(a) end
end

implement barr_of_arr {l}{n} (a) =
  $UNSAFE begin $UNSAFE.castvwtp0{[cs:cells] (CLEN(cs, n) | barr(l, n, cs))}(a) end

implement barr_to_arr {l}{n}{cs} (a) =
  $UNSAFE begin $UNSAFE.castvwtp0{arr(byte, l, n)}(a) end

implement barr_copy {l}{n}{cs} (a, n) = let
  val copy = $UNSAFE begin _calloc_bytes(n, sizeof<byte>) end
  fun go {i:nat | i <= n} .<n - i>. (i: int i): void =
    if i >= n then ()
    else let
      val () = $UNSAFE begin
        $UNSAFE.ptr0_set<byte>(ptr_add<byte>(copy, i), $UNSAFE.ptr0_get<byte>(ptr_add<byte>(a, i)))
      end
    in go(i + 1) end
  val () = go(0)
in
  $UNSAFE begin $UNSAFE.castvwtp0{[m:agz] barr(m, n, cs)}(copy) end
end

end
