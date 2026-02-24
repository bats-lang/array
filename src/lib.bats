(* array -- linear memory safety library for bats *)
(* Typed arrays with linear ownership -- no raw pointers. *)
(* Typed arrays with linear ownership. *)

#include "share/atspre_staload.hats"

(* ============================================================
   Types
   ============================================================ *)

#pub absvtype arr(a:t@ype, l:addr, n:int)

#pub absvtype frozen(a:t@ype, l:addr, n:int, k:int)

#pub absvtype borrow(a:t@ype, l:addr, n:int)

(* ============================================================
   Allocate / free
   ============================================================ *)

#pub fun{a:t@ype}
alloc
  {n:pos | n <= 1048576}
  (n: int n)
  : [l:agz] arr(a, l, n)

#pub fun{a:t@ype}
free
  {l:agz}{n:nat}
  (arr: arr(a, l, n))
  : void

(* ============================================================
   Element access (bounds-checked)
   ============================================================ *)

#pub fun{a:t@ype}
get
  {l:agz}{n,i:nat | i < n}
  (arr: !arr(a, l, n), i: int i)
  : a

#pub fun{a:t@ype}
set
  {l:agz}{n,i:nat | i < n}
  (arr: !arr(a, l, n), i: int i, v: a)
  : void

(* ============================================================
   Split / join (sub-array with size tracking)
   ============================================================ *)

#pub fun{a:t@ype}
split
  {l:agz}{n,m:nat | m <= n}
  (arr: arr(a, l, n), m: int m)
  : @(arr(a, l, m), arr(a, l+m, n-m))

#pub fun{a:t@ype}
join
  {l:agz}{n,m:nat}
  (left: arr(a, l, n), right: arr(a, l+n, m))
  : arr(a, l, n+m)

(* ============================================================
   Freeze / thaw borrow protocol
   ============================================================ *)

#pub fun{a:t@ype}
freeze
  {l:agz}{n:nat}
  (arr: arr(a, l, n))
  : @(frozen(a, l, n, 1), borrow(a, l, n))

#pub fun{a:t@ype}
thaw
  {l:agz}{n:nat}
  (f: frozen(a, l, n, 0))
  : arr(a, l, n)

#pub fun{a:t@ype}
dup
  {l:agz}{n:nat}{k:pos}
  (f: !frozen(a, l, n, k) >> frozen(a, l, n, k+1),
   b: !borrow(a, l, n))
  : borrow(a, l, n)

#pub fun{a:t@ype}
drop
  {l:agz}{n:nat}{k:pos}
  (f: !frozen(a, l, n, k) >> frozen(a, l, n, k-1),
   b: borrow(a, l, n))
  : void

(* ============================================================
   Read from borrow (bounds-checked)
   ============================================================ *)

#pub fun{a:t@ype}
read
  {l:agz}{n,i:nat | i < n}
  (b: !borrow(a, l, n), i: int i)
  : a

(* ============================================================
   Borrow split / join
   ============================================================ *)

#pub fun{a:t@ype}
borrow_split
  {l:agz}{n,m:nat | m <= n}{k:pos}
  (f: !frozen(a, l, n, k) >> frozen(a, l, n, k+1),
   b: borrow(a, l, n), m: int m)
  : @(borrow(a, l, m), borrow(a, l+m, n-m))

#pub fun{a:t@ype}
borrow_join
  {l:agz}{n,m:nat}{k:int | k > 1}
  (f: !frozen(a, l, n+m, k) >> frozen(a, l, n+m, k-1),
   left: borrow(a, l, n), right: borrow(a, l+n, m))
  : borrow(a, l, n+m)

(* ============================================================
   Borrow single element
   ============================================================ *)

#pub fun{a:t@ype}
borrow_at
  {l:agz}{n:pos}{i:nat | i < n}{k:pos}
  (f: !frozen(a, l, n, k) >> frozen(a, l, n, k+1),
   b: !borrow(a, l, n), i: int i)
  : borrow(a, l+i, 1)

#pub fun{a:t@ype}
drop_borrow_at
  {l:agz}{n:pos}{i:nat | i < n}{k:int | k > 1}
  (f: !frozen(a, l, n, k) >> frozen(a, l, n, k-1),
   b: borrow(a, l+i, 1))
  : void

(* ============================================================
   Safe text -- compile-time character verification
   ============================================================ *)

#pub stadef SAFE_CHAR (c:int) =
  (c >= 97 && c <= 122)
  || (c >= 65 && c <= 90)
  || (c >= 48 && c <= 57)
  || c == 45

#pub abstype text (n:int) = ptr

#pub absvtype text_builder (n:int, filled:int)

#pub fun text_build
  {n:pos}
  (n: int n)
  : text_builder(n, 0)

#pub fun text_putc
  {c:int | SAFE_CHAR(c)} {n:pos} {i:nat | i < n}
  (b: text_builder(n, i), i: int i, c: int c)
  : text_builder(n, i+1)

#pub fun text_done
  {n:pos}
  (b: text_builder(n, n))
  : text(n)

#pub fun text_get
  {n,i:nat | i < n}
  (t: text(n), i: int i)
  : byte

#pub fun text_of_chars
  {n:pos}
  (n: int n, chars: &(@[char][n])): text(n)

(* ============================================================
   Text from bytes -- runtime SAFE_CHAR validation
   ============================================================ *)

#pub datavtype text_result(n:int) =
  | {n:int} text_ok(n) of (text(n))
  | {n:int} text_fail(n) of ()

#pub fun text_from_bytes
  {lb:agz}{n:pos}
  (src: !borrow(byte, lb, n), len: int n): text_result(n)

(* ============================================================
   Utility -- int to byte conversion
   ============================================================ *)

#pub fun int2byte{i:nat | i < 256}(i: int i): byte

(* ============================================================
   Write operations (byte-level)
   ============================================================ *)

#pub fun write_byte
  {l:agz}{n:nat}{i:nat | i < n}{v:nat | v < 256}
  (arr: !arr(byte, l, n), i: int i, v: int v): void

#pub fun write_u16le
  {l:agz}{n:nat}{i:nat | i + 2 <= n}{v:nat | v < 65536}
  (arr: !arr(byte, l, n), i: int i, v: int v): void

#pub fun write_i32
  {l:agz}{n:nat}{i:nat | i + 4 <= n}
  (arr: !arr(byte, l, n), i: int i, v: int): void

#pub fun write_borrow
  {ld:agz}{ls:agz}{m:nat}{n:nat}{off:nat | off + n <= m}
  (dst: !arr(byte, ld, m), off: int off,
   src: !borrow(byte, ls, n), len: int n): void

#pub fun write_text
  {l:agz}{m:nat}{n:nat}{off:nat | off + n <= m}
  (dst: !arr(byte, l, m), off: int off,
   src: text(n), len: int n): void

(* ============================================================
   Content text -- wider character set for attribute values
   ============================================================ *)

#pub stadef SAFE_CONTENT_CHAR(c:int) =
  (c >= 32 && c <= 126)
  && c != 34
  && c != 38
  && c != 60
  && c != 62

#pub absvtype content_text(l:addr, n:int)

#pub absvtype content_text_builder(l:addr, n:int, filled:int)

#pub fun content_text_build
  {n:pos | n <= 1048576}
  (n: int n)
  : [l:agz] content_text_builder(l, n, 0)

#pub fun content_text_putc
  {c:int | SAFE_CONTENT_CHAR(c)} {l:agz} {n:pos} {i:nat | i < n}
  (b: content_text_builder(l, n, i), i: int i, c: int c)
  : content_text_builder(l, n, i+1)

#pub fun content_text_done
  {l:agz} {n:pos}
  (b: content_text_builder(l, n, n))
  : content_text(l, n)

#pub fun content_text_get
  {l:agz} {n,i:nat | i < n}
  (t: !content_text(l, n), i: int i)
  : byte

#pub fun content_text_free
  {l:agz} {n:nat}
  (t: content_text(l, n))
  : void

#pub fun text_to_content
  {n:pos | n <= 1048576}
  (t: text(n), len: int n)
  : [l:agz] content_text(l, n)

#pub fun write_content_text
  {ld:agz}{ls:agz}{m:nat}{n:nat}{off:nat | off + n <= m}
  (dst: !arr(byte, ld, m), off: int off,
   src: !content_text(ls, n), len: int n): void

(* ============================================================
   Arena -- bulk allocation with token-tracked lifecycle
   ============================================================ *)

#pub absvtype arena(l:addr, max:int, k:int)

#pub absvtype arena_token(la:addr, l:addr, n:int)

#pub fun arena_create
  {max:pos | max <= 268435456}
  (max_size: int max)
  : [l:agz] arena(l, max, 0)

#pub fun{a:t@ype}
arena_alloc
  {la:agz}{max:pos}{k:nat}{n:pos}
  (ar: !arena(la, max, k) >> arena(la, max, k+1),
   n: int n)
  : [l:agz] @(arena_token(la, l, n), arr(a, l, n))

#pub fun{a:t@ype}
arena_return
  {la:agz}{max:pos}{k:pos}{l:agz}{n:pos}
  (ar: !arena(la, max, k) >> arena(la, max, k-1),
   token: arena_token(la, l, n),
   v: arr(a, l, n))
  : void

#pub fun arena_destroy
  {l:agz}{max:nat}
  (ar: arena(l, max, 0))
  : void

(* ============================================================
   C runtime helpers
   ============================================================ *)

$UNSAFE begin
%{#
#ifndef _ARR_RUNTIME_DEFINED
#define _ARR_RUNTIME_DEFINED
static inline void
_arr_set_byte(void *p, int off, int v) {
  ((unsigned char *)p)[off] = (unsigned char)v;
}
static inline void
_arr_set_i32(void *p, int off, int v) {
  *(int *)(((char *)p) + off) = v;
}
static inline void
_arr_copy_at(void *dst, int off, void *src, int len) {
  unsigned char *d = ((unsigned char *)dst) + off;
  unsigned char *s = (unsigned char *)src;
  int i;
  for (i = 0; i < len; i++) d[i] = s[i];
}

typedef struct { char *base; int used; int max_sz; } _arr_arena_t;

static inline void *
_arr_arena_create(int max_sz) {
  _arr_arena_t *a;
  a = (void *)malloc(sizeof(_arr_arena_t));
  a->base = (char *)malloc(max_sz);
  a->used = 0;
  a->max_sz = max_sz;
  memset(a->base, 0, max_sz);
  return (void *)a;
}
static inline void *
_arr_arena_alloc(void *arena, int sz) {
  _arr_arena_t *a = (_arr_arena_t *)arena;
  void *p = (void *)(a->base + a->used);
  a->used += sz;
  return p;
}
static inline void
_arr_arena_destroy(void *arena) {
  _arr_arena_t *a = (_arr_arena_t *)arena;
  free(a->base);
  free((void *)a);
}
#endif /* _ARR_RUNTIME_DEFINED */
%}
end

(* ============================================================
   Implementation -- main local block (trusted unsafe core)
   ============================================================ *)

local

  assume arr(a, l, n) = ptr l
  assume frozen(a, l, n, k) = ptr l
  assume borrow(a, l, n) = ptr l
  assume text(n) = ptr
  assume text_builder(n, i) = ptr
  assume arena(l, max, k) = ptr l
  assume arena_token(la, l, n) = ptr l

in

fn _proven_int2byte{i:nat | i < 256}(i: int i): byte =
  $UNSAFE begin $UNSAFE.cast{byte}(i) end

extern fun _malloc_bytes (n: int): [l:agz] ptr l = "mac#malloc"

(* -- Allocate / free -- *)

implement{a}
alloc{n}(n) = let
  val nbytes = n * sz2i(sizeof<a>)
  val p = _malloc_bytes(nbytes)
  val () = $extfcall(void, "memset", p, 0, nbytes)
in
  p
end

implement{a}
free{l}{n}(arr) =
  $extfcall(void, "free", arr)

(* -- Element access -- *)

implement{a}
get{l}{n,i}(arr, i) =
  $UNSAFE begin $UNSAFE.ptr0_get<a>(ptr_add<a>(arr, i)) end

implement{a}
set{l}{n,i}(arr, i, v) =
  $UNSAFE begin $UNSAFE.ptr0_set<a>(ptr_add<a>(arr, i), v) end

(* -- Split / join -- *)

implement{a}
split{l}{n,m}(arr, m) = let
  val tail = $UNSAFE begin $UNSAFE.cast{ptr(l+m)}(ptr_add<a>(arr, m)) end
in
  @(arr, tail)
end

implement{a}
join{l}{n,m}(left, right) = left

(* -- Freeze / thaw -- *)

implement{a}
freeze{l}{n}(arr) = @(arr, arr)

implement{a}
thaw{l}{n}(f) = f

implement{a}
dup{l}{n}{k}(f, b) = b

implement{a}
drop{l}{n}{k}(f, b) = ()

(* -- Read from borrow -- *)

implement{a}
read{l}{n,i}(b, i) =
  $UNSAFE begin $UNSAFE.ptr0_get<a>(ptr_add<a>(b, i)) end

(* -- Borrow split / join -- *)

implement{a}
borrow_split{l}{n,m}{k}(f, b, m) = let
  val tail = $UNSAFE begin $UNSAFE.cast{ptr(l+m)}(ptr_add<a>(b, m)) end
in
  @(b, tail)
end

implement{a}
borrow_join{l}{n,m}{k}(f, left, right) = left

(* -- Borrow at -- *)

implement{a}
borrow_at{l}{n}{i}{k}(f, b, i) =
  $UNSAFE begin $UNSAFE.cast{ptr(l+i)}(ptr_add<a>(b, i)) end

implement{a}
drop_borrow_at{l}{n}{i}{k}(f, b) = ()

(* -- Text -- *)

implement
text_build{n}(n) = _malloc_bytes(n)

implement
text_putc{c}{n}{i}(b, i, c) = let
  val () = $UNSAFE begin $UNSAFE.ptr0_set<byte>(ptr_add<byte>(b, i), _proven_int2byte(c)) end
in b end

implement
text_done{n}(b) = b

implement
text_get{n,i}(t, i) =
  $UNSAFE begin $UNSAFE.ptr0_get<byte>(ptr_add<byte>(t, i)) end

implement
text_of_chars{n}(n, chars) = let
  val p = _malloc_bytes(n)
  fun loop {i:nat | i <= n} .<n - i>.
    (p: ptr, i: int i, n: int n, cp: ptr): void =
    if i >= n then ()
    else let
      val c = $UNSAFE begin $UNSAFE.ptr0_get_at<char>(cp, i) end
      val () = $UNSAFE begin $UNSAFE.ptr0_set_at<byte>(p, i,
        $UNSAFE.cast{byte}(char2int0(c))) end
    in loop(p, i + 1, n, cp) end
  val cp = $UNSAFE begin $UNSAFE.cast{ptr}(addr@chars) end
  val () = loop(p, 0, n, cp)
in $UNSAFE begin $UNSAFE.castvwtp0{text(n)}(p) end end

implement
text_from_bytes{lb}{n}(src, len) = let
  fun loop {i:nat | i <= n}
    (src: ptr, i: int i, len: int n): bool =
    if i >= len then true
    else let
      val b = byte2int0($UNSAFE begin $UNSAFE.ptr0_get<byte>(ptr_add<byte>(src, i)) end)
    in
      if (b >= 97 andalso b <= 122)
         orelse (b >= 65 andalso b <= 90)
         orelse (b >= 48 andalso b <= 57)
         orelse b = 45
      then loop(src, i + 1, len)
      else false
    end
  val all_safe = loop(src, 0, len)
in
  if all_safe then let
    val p = _malloc_bytes(len)
    val () = $extfcall(void, "memcpy", p, src, len)
    val t = $UNSAFE begin $UNSAFE.cast{text(n)}(p) end
  in text_ok(t) end
  else text_fail()
end

implement
int2byte{i}(i) = _proven_int2byte(i)

(* -- Write operations -- *)

implement
write_byte{l}{n}{i}{v}(arr, i, v) =
  $extfcall(void, "_arr_set_byte", arr, i, v)

implement
write_i32{l}{n}{i}(arr, i, v) =
  $extfcall(void, "_arr_set_i32", arr, i, v)

implement
write_borrow{ld}{ls}{m}{n}{off}(dst, off_val, src, len) =
  $extfcall(void, "_arr_copy_at", dst, off_val, src, len)

implement
write_text{l}{m}{n}{off}(dst, off_val, src, len) =
  $extfcall(void, "_arr_copy_at", dst, off_val, src, len)

implement
write_u16le{l}{n}{i}{v}(arr, i, v) = let
  val v0 : int = v
  val () = $extfcall(void, "_arr_set_byte", arr, i, v0)
  val () = $extfcall(void, "_arr_set_byte", arr, i + 1, v0 / 256)
in () end

(* -- Arena -- *)

extern fun _arena_create_impl
  (max: int): [l:agz] ptr l = "mac#_arr_arena_create"

extern fun _arena_alloc_impl
  (arena: ptr, size: int): [l:agz] ptr l = "mac#_arr_arena_alloc"

extern fun _arena_destroy_impl
  (arena: ptr): void = "mac#_arr_arena_destroy"

implement
arena_create{max}(max_size) = _arena_create_impl(max_size)

implement{a}
arena_alloc{la}{max}{k}{n}(ar, n) = let
  val nbytes = n * sz2i(sizeof<a>)
  val p = _arena_alloc_impl(
    $UNSAFE begin $UNSAFE.castvwtp1{ptr}(ar) end, nbytes)
in @(p, p) end

implement{a}
arena_return{la}{max}{k}{l}{n}(ar, token, v) = ()

implement
arena_destroy{l}{max}(ar) = _arena_destroy_impl(ar)

end (* local -- main implementation block *)

(* ============================================================
   Content text -- separate local block
   ============================================================ *)

local

  assume content_text(l, n) = arr(byte, l, n)
  assume content_text_builder(l, n, i) = arr(byte, l, n)

in

implement
content_text_build{n}(n) = alloc<byte>(n)

implement
content_text_putc{c}{l}{n}{i}(b, i, c) = let
  val () = set<byte>(b, i, int2byte(c))
in b end

implement
content_text_done{l}{n}(b) = b

implement
content_text_get{l}{n,i}(t, i) =
  get<byte>(t, i)

implement
content_text_free{l}{n}(t) =
  free<byte>(t)

implement
text_to_content{n}(t, len) = let
  val ar = alloc<byte>(len)
  val () = write_text(ar, 0, t, len)
in ar end

implement
write_content_text{ld}{ls}{m}{n}{off}(dst, off_val, src, len) = let
  fun loop{i:nat | i <= n}
    (dst: !arr(byte, ld, m), src: !content_text(ls, n),
     off_val: int off, i: int i, len: int n): void =
    if i < len then let
      val b = content_text_get(src, i)
      val () = set<byte>(dst, off_val + i, b)
    in loop(dst, src, off_val, i + 1, len) end
in loop(dst, src, off_val, 0, len) end

end (* local -- content text *)
