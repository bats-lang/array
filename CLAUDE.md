# array

## Comments name their area by keyword

A comment states its reason in one line and names the area by keyword; the detail lives in this file: search it for the keyword before changing the code.

## Allocation size is bounded on purpose

`alloc` takes at most 1048576 elements (`{n:pos | n <= 1048576}`). This is a
design constraint, not an oversight: capping arbitrary allocations limits
heap fragmentation. Do not raise it, and do not work around it with a
bigger raw allocation somewhere else.

Code that needs more memory than one bounded allocation (a large file, a
large output) uses a pool: one region reserved up front, handed out in
pieces whose sizes the types account for, and released as a whole.

## Allocation failure is in the type (array#80, keyword: array allocation-failure)

`alloc` has the type `[l:agz] arr(a, l, n)`, so a NULL from calloc at a tight
address-space limit (`ulimit -v`) is not representable and was written
through (bats#288: the builder's `put_byte`). `alloc_checked<a>(n)` is beside
it, with the same size bound (`n <= 1048576`) and the same instances (byte,
char, bool, int, uint, Int), and answers `alloc_made(a, n)`: `alloc_some(arr)`
or `alloc_none()`, the style of `arena_made`. The result is a linear
datavtype, so a caller must match `alloc_none` before it has an array.
Nothing is deprecated: `alloc` is unchanged, and the ticket (array#80) says
no removal ticket is filed. Moving a dependent (builder, so bats's
`record-commit`) to the new function is a ticket in that repository.

`tests/dynamic/alloc-checked` calls `alloc_checked` for each instance and the
old `alloc`, with the address space the machine gives; `alloc-checked-tight`
is the same program run under `ulimit -v 5000` (its `ulimit-v` file, which
`tests/dynamic/run.sh` applies): the program starts and has a 16-byte array
(`small`), a 4 MiB one (1048576 `Int`) is `alloc_none`, and the program goes
on (measured, PR #87: at 2000 and 2500 KiB the program does not load, at 3000,
5000 and 6500 it prints `big none`, at 7000 it prints `big 9`, so 5000 is
inside the window with room on both sides).

The limit is set by `sh`'s `ulimit -v` in `tests/dynamic/run.sh`, the one shell
line of this change. Avenue exhausted: a test written in bats cannot lower
RLIMIT_AS, because the process package has no setrlimit (bats's `.claude/rules/patsopt-caps.md`
says so) and the array package has no such call and may not gain C for a test; the
mechanism bats itself uses for the same limit is `sh -c 'ulimit -v ...'`
(`patsopt_only` in bats's `src/helpers.bats`; `tests/patsopt-cap` and
`tests/full-disk` there use `ulimit -v` and `ulimit -f` the same way), and no
sibling package's tests/dynamic sets a resource limit (searched: process, file,
builder, bridge, zip, bats's tests for `ulimit`, `setrlimit`, `RLIMIT`). `tests/static/accept/alloc-checked-use` matches both
constructors; `reject/alloc-checked-unmatched` (the failure constructor left
out), `alloc-checked-some-as-null` (the result freed as an array) and
`alloc-checked-too-large` (1048577 elements) each fail for the one line they guard.

## The arena is the pool

`arena_create_class<a>(class | max)` reserves one zeroed region of `max`
elements, `max` one of the size classes (next section); `arena_alloc` hands out pieces of it, `arena_return` takes them
back, and `arena_destroy` releases the region. It is sound by type, with
no runtime checks:

* The arena's type tracks the elements handed out (`used`), so a piece
  that does not fit (`used + n > max`) does not type-check.
* A piece is `arrx(a, l, n, la)`, owned by its arena's address `la`.
  `free` takes only `arr(a, l, n)` (= `arrx(a, l, n, null)`, what
  `alloc` returns), so a piece cannot be freed; `arena_return` takes only
  the pieces of that arena. Everything that reads or writes an array
  (get, set, freeze, write_*) works for any owner.
* The arena counts outstanding pieces (`k`); `arena_destroy` needs
  `k = 0`.
* Pieces are never reused, so they are zero bytes; as with `alloc`,
  `arena_create_class` has instances only for element types where zero bytes
  are a valid value.
* When the region cannot be had, `arena_create_class` returns `arena_none`,
  never a null arena.

## One way to make an arena (array#29, array#67)

`arena_create_class<a>(class | max)` is the only way: its size is one of the
classes (next section). The bare-size `arena_create<a>(max)` that array#29 first
replaced in place, and that was then kept beside it (an in-place replacement
fails every dependent and the package repository's `verify`, the same lesson as
process's "Spawn keeps its old signatures", process#62 restored by process#64;
the owner's ruling, 2026-10-21: "Just....keep supporting both, have a p1 ticket
to remove the deprecated version."), was removed by array#67 once the newest
archive of no package named it (checked in repository-prototype, listed in the
pull request). Its two tests, `tests/static/accept/arena-create-deprecated` and
`tests/dynamic/arena-create-deprecated`, went with it. No static reject named it.

## An arena's size is a class

An arena made by `arena_create_class` is one of five sizes fixed at
compile time (`ARENA_CLASS`). The class sizes are counted in elements of its type, not bytes: 65536, 262144, 1048576,
4194304 and 16777216 elements, powers of 4. For a byte arena those are
64 KiB, 256 KiB, 1 MiB, 4 MiB and 16 MiB. For an arena of any other
element type the class is an element count and the byte size is that
count times the element's size (16777216 `int` elements are 64 MiB), so
the byte figures hold for byte arenas only. Every arena quire has is a
byte arena.

A freed region of a class arena is then the size of the next one asked for
(every arena is a class), so an
allocator can keep one free list per class and reuse a region whole. The
allocator's free list of large blocks (bats-lang/bats#241, open) reuses a
block only for a request between half its size and its full size, so
odd-sized arenas pile up there today. Which classes #241 uses is decided
there; nothing in this package depends on it.

`arena_create_class` takes a proof `ARENA_CLASS(max)`, whose constructors are
each indexed by a literal, so a size computed at run time, or a constant
that is not a class, does not type-check. `arena_class_of(n)` gives the
smallest class that holds `n` elements, or `arena_too_large` over
`ARENA_MOST` (16777216 elements).

The byte figures are quire's, in its source: a page's arena is
`PAGE_BYTES`, 4 MiB (`src/pages.bats`); a clip table is `CLIP_MAX` (32768)
times 32 bytes, 1 MiB (`src/overlay.bats`); the largest file a reader
holds whole is its sync file, `SYNC_MAX_BYTES`, 16 MiB (`src/sync.bats`).
The sizes of the EPUB parts they hold are measured on a seeded sample in
bats-lang/array#29. Do not add a class for a size one caller computes;
take the smallest class that holds it.

The first arena (removed in #21 and restored here) had none of these:
`arena_alloc` never compared its offset to the size, its arrays could be
freed, and it handed out zero bytes as any type. Fix such problems; do
not delete the facility.

`tests/static` rejects each misuse (a size that is not a class given to
`arena_create_class`, a size computed at run time, a size of 0 or a negative one given to
`arena_class_of`, overfill, freeing a piece, returning
it to another arena, destroying with a piece out, a pointer element
type); a piece lent as a `barr` and given back is below, under byte
arrays; `tests/dynamic/arena` exercises pieces past the 1 MiB `alloc`
bound.

## Byte arrays know their contents

`barr(l, n, cs)` is an array of n bytes at l that holds the cells `cs`
(`cnil`, `ccons`), so a program can prove what it reads and writes:

* `barr_get` gives the cell with the proof `NTH(cs, i, v)`; `barr_set`
  consumes the array and gives it back with `SETC(cs, i, v, cs2)`;
  `barr_alloc` and `barr_of_arr` give cells nothing is known of (and
  `CLEN(cs, n)`: their number), `barr_to_arr` takes the cells away so that
  what knows nothing of them (a platform call that fills the array) may
  write it, and `barr_copy` gives another array of the same cells.
* `barr_get_be32(a, i)` (sha256#40) gives cells i to i + 3 as the four bytes
  of a big-endian word with the four proofs `NTH(cs, i + k, b_k)`, in one
  call. It is an ordinary function over four `barr_get` (explicit static
  arguments, no `$UNSAFE`), not in the trusted block: the trusted block holds
  only what cannot be written from `barr_get`. It exists so a caller in
  another module makes one cross-module call instead of four. In a release
  build the C compiler turns the four reads into four loads, shifts and ors,
  with no call (seen in a release build of the wrapper). Measured (callgrind,
  release, sha256's `proved_hash` of 1 MiB, total instructions, #58): four
  `barr_get` for each word 491,338,782 (468.6 a byte); `barr_get_be32` as the
  untrusted wrapper 430,074,613 (410.2 a byte); as the trusted primitive first
  tried 430,075,276 (410.2 a byte). A matching write is not added: `barr_set`
  is 5.5% of the instructions (26 a byte), too little to show it is the cost,
  so per #57 there is no `barr_set_be32`.
* The lemmas are proved here, by the compiler, with no `praxi` and no
  `assume`: `setc_len`, `setc_nth_same`, `setc_nth_other` (the other cells
  are as they were; needs `i != j`), `nth_in_len` and `nth_functional`.
* The trusted core is the primitives in the implementation block of
  `lib.bats`: each does what its type says to the memory (reads or writes
  one byte, copies, allocates) and fabricates the proof its type gives.
  Nothing else in the package or in a package using it makes a proof of
  an array's contents. `tests/dynamic/content` runs them; `tests/static`
  rejects a cell claimed to hold another value, a cell past the end, and
  the lemma about other cells used for the same cell.
* A `barr` is borrowed with its cells in the type (`barr_freeze` gives a
  `cfrozen(l, n, 1, cs)` and a `cborrow(l, n, cs)`; `cborrow_dup`,
  `cborrow_drop` and `barr_thaw` count the borrows as `freeze` and `thaw`
  do for `arr`, so no cell is set while one is out). `cborrow_get` gives
  the cell with `NTH(cs, i, v)`, exactly as `barr_get` does, so a loop
  that reads a borrowed array (a table, an input) can state what the bytes
  it read are. These five are identities on the pointer or one byte read,
  in the same trusted block, tested by `tests/dynamic/borrow` and
  rejected when misused by `tests/static/reject/borrow-*`. The plain
  `borrow` of `arr` is unchanged and knows nothing of its cells.
* A piece of an arena is lent as a `barr` by `barr_of_arrx`, which takes
  any `arrx(byte, l, n, o)` and gives the `barr` with the cells nothing is
  known of (as `barr_of_arr` does) and a proof `arrx_lent(l, n, o)`, a
  linear view (erased at run time, `unit_v` in the trusted block) made
  only there. `barr_to_arrx` takes the `barr` and that proof and gives the
  `arrx(byte, l, n, o)` back, so the owner is kept by type: the arena's
  count of outstanding pieces does not change while a piece is lent (so
  `arena_destroy`, which needs `k = 0`, does not type-check), the piece
  comes back only as the same `l`, `n` and `o` (so only to its own arena),
  and a lent piece cannot be freed (`barr_free` leaves the proof
  unconsumed) or the `barr` used after it is given back. Both are casts of
  the pointer in the trusted block, like `barr_of_arr` and `barr_to_arr`,
  and add no `praxi`, `assume` outside that block or `$UNSAFE`. What they
  assume: that `barr` and `arrx(byte, ...)` are both the pointer to the
  n bytes (as `barr_of_arr` and `barr_to_arr` already do), and that
  `arrx_lent` is `unit_v`, a view with no run-time content. `barr_to_arr`
  on a lent barr gives an `arr` that `free` takes, but the lend is then
  still unconsumed and no barr at that address is left to consume it, so
  the program does not type-check
  (`tests/static/reject/arena-lend-to-arr-free`). A barr may
  be frozen, read through `cborrow_get` and thawed between the two, which
  is how a loop proves what it read from an arena piece
  (`tests/dynamic/arena-lend`; `tests/static/reject/arena-lend-*`).
* `cborrow_view(f, b)` gives the plain `borrow(byte, l, n)` of the same
  array while `b` is still held (quire#568: a reader that takes a plain
  borrow, like `read` or `write_borrow`, and a proof of the cells through
  `cborrow_get`, at once). It is one more borrow out, counted exactly as
  `cborrow_dup` counts one (`cfrozen(l, n, k, cs)` to `k+1`), and
  `cborrow_view_drop(f, view)` takes it back (`k` to `k-1`); `barr_thaw`
  needs `k = 0`, so no cell is set while the view is out. Both are
  identities on the pointer, in the same trusted block as `cborrow_dup`
  and `cborrow_drop`, and assume only that the plain `borrow` is a
  read-only handle: every operation on a plain `borrow` here reads (`read`,
  `write_borrow` reads its source, `borrow_split`, `borrow_join` and
  `borrow_at` need a `frozenx` of an `arr`, which a `barr` never is, so a
  view cannot be split or joined, and `drop` needs a `frozenx` too, so the
  view goes back only through `cborrow_view_drop`). The view is indexed by
  `l` and `n` only: what is read through it is not known (the proof is
  `cborrow_get`'s on `b`), and `cborrow_view_drop` takes the `cfrozen` of
  the same `l`, so the view of one array cannot be given back to another's
  count. `tests/dynamic/borrow-view` reads both ways and compares;
  `tests/static/accept/borrow-view` and `reject/borrow-view-*` (thaw with
  the view out, view used after it was given back, given back twice, given
  back to another array) pin the types.
* A proof about a `barr` holds only while the program holds it: `barr_to_arr`
  and `barr_to_arrx` forget the cells, and `barr_of_arr` and `barr_of_arrx`
  start again from cells nothing is known of.

## Int arrays know their contents (bats-lang/array#49)

`iarr(l, n, cs)` is n C ints at l holding the cells `cs`, the `barr` pattern for
ints (keyword: iarr), so a value read back from a table has the index the
program proved when it wrote it, and a dependent needs no runtime clamp:

* `iarr_alloc` (at most 1048576 elements, as `alloc`) gives `CLEN(cs, n)` and
  `ZEROS(cs, n)` (calloc leaves every cell 0); `iarr_get` gives the cell with
  `NTH(cs, i, v)`; `iarr_set` consumes the array and gives it back with
  `SETC(cs, i, v, cs2)`; `iarr_free`. The cell lemmas are `barr`'s (`setc_nth_same`,
  `setc_nth_other`, `nth_functional`, `nth_in_len`), on the same `cells`.
* **Element width: 32 bits** (keyword: iarr width). The dependents' values are
  positions of a file, entry numbers and chain links (bats's with-env table:
  positions under 65537, entries under 1025), which fit with room to spare. A
  value is within [-2147483648, 2147483647] in the types of `iarr_get` and
  `iarr_set`. A 64-bit element waits for a dependent that needs one. F*'s
  Low* buffers (`LowStar.Buffer`: `index` and `upd` stated with `as_seq`), Dafny
  arrays (a quantified invariant over `a[i]`) and HACL*'s buffers state the
  contents in the logic the same way, at the width of the element they hold.
* **A uniform bound**: `ALLIN(cs, lo, hi)` says every cell is within [lo, hi].
  `allin_nth` (a cell of such cells is within it), `allin_setc` (setting a cell to
  a value within it keeps it), `allin_zeros` (a zeroed array is within any
  bound that holds 0, so `iarr_alloc`'s `ZEROS` starts it), `allin_widen`,
  `zeros_nth` and `zeros_len` are proved here, with no `praxi` and no `assume`.
  `iarr_get_in` and `iarr_set_in` are `iarr_get`/`iarr_set` with that proof: the
  read is `[v:int | lo <= v; v <= hi]`. Not trusted (ordinary functions over the
  trusted two).
* A bound that is not uniform (a column of positions, another of links, a
  value after its name) is the dependent's own dataprop over `cells`, kept by
  `setc_nth_other` and `setc_nth_same`: it needs nothing more from this package.
* **Trusted**: `iarr_alloc`, `iarr_free`, `iarr_get` and `iarr_set`, in the
  implementation block of `lib.bats`, each a pointer cast or one int read or
  written. Assumed: `iarr` and `arr(int, ...)` are both the pointer to the n
  ints, a C int is 32 bits, calloc's memory is all zero bits (the int 0).
  `tests/dynamic/iarr` runs them (a fresh array is zeros, the 32-bit ends, a set
  leaves the other cells, 3000 pseudo-random sets against a plain array); seven
  one-line mutants of the four were each caught by it under valgrind (a wrong
  stride, the next cell, a value plus one, the wrong cell, one byte per
  element, no zeroing, no free). `tests/static/reject/iarr-*` rejects a wrong
  cell, a cell past the end, the lemma about other cells used for the same
  cell, a fresh cell claimed not 0, a value out of the bound, a bound
  tighter than the proof, a bound proof kept over a plain `iarr_set`, a
  narrower widening, a value over 32 bits, an array used after `iarr_set`,
  freed twice, not freed, and over 1048576 elements.
* The lemmas are checked by the gmp solver, and quire's `mutation_check.py`
  over `src/lib.bats` rejects every false variant of them but two that are true
  statements: `allin_widen` and `allin_zeros` with `hi + 1` (a wider bound is
  implied by the narrower).

## Appended cells: APPEND, CELLS_EQ, HOLDS (bats-lang/array#82)

The one relation the file writer and reader (file#76) and zip's INFLATES (zip#64) share, on
`cells` (keyword: append). Additive: no existing form changes.

* `APPEND(first, second, both)`: both is the cells first and then the cells second. Made by
  `APPEND_nil() : APPEND(cnil, second, second)` and `APPEND_cons(p) : APPEND(ccons(x, first), second,
  ccons(x, both))` from `p : APPEND(first, second, both)`. These two are proof functions, not
  constructors of a dataprop: a recursive proof function needs a termination metric, an index-free
  relation gives none, and the length of first is not at hand where the lemma is stated. So `APPEND` has the one
  constructor `APPEND_made` over `APPEND_SIZED(first, second, both, n)`, which holds the length n of
  first; `APPEND_nil` and `APPEND_cons` build it (a recursive proof function with no metric is refused by patsopt: "a termination metric is missing"). A proof is built with the two
  functions; it is taken apart with `APPEND_made`, and `APPEND_SIZED_nil` / `APPEND_SIZED_cons` below it.
* `CELLS_EQ(first, second)`: the same cells; its one constructor `CELLS_EQ_refl` is the only way to have
  it. `append_functional : (APPEND(first, second, both), APPEND(first, second, other)) -> CELLS_EQ(both,
  other)`, proved here by recursion on the size (no `praxi`, no `assume`).
* `HOLDS(buffer, chunk)`: the buffer's cells begin with the chunk (`HOLDS_mk` of `APPEND(chunk, rest,
  buffer)`, the rest being whatever follows), for a borrowed buffer that holds more than the chunk read into it.
* Nothing here is trusted: all proof, no new primitive, so there is no dynamic test; the types are pinned by
  `tests/static/accept/append-use` and the rejects `append-nil-wrong-both`, `append-cons-wrong-head`,
  `append-swapped`, `append-functional-other-first`, `cells-eq-different`, `holds-other-chunk` and
  `holds-chunk-longer-than-buffer`, each with its exact `expect`. quire's `mutation_check.py --root` over
  `src/lib.bats` makes false variants of `APPEND_nil`, `APPEND_cons` and `append_functional` and the compiler
  rejects every one.

## The accessors as templates (bats-lang/sha256#59)

`barr_get`, `barr_get_be32` and `barr_set` are external symbols: a dependent
calls them and the C compiler, which compiles each module alone, cannot inline
them (in the proved SHA-256: `barr_get_be32` 44, `barr_set` 26 of 394
instructions a byte, callgrind, release, 1 MiB). A template with no template
arguments is instantiated by the dependent, in its own translation unit (a
dependent loads this package's `lib.dats`), so the three are also
`barr_get_inline`, `barr_get_be32_inline` and `barr_set_inline` (`#pub fun{}`),
with the very types of the three, called as `barr_get_inline(a, i)`. Their bodies
are the trusted primitives' (`barr_get`'s and `barr_set`'s casts, in the
implementation block) and `barr_get_be32`'s four reads; `barr_get`, `barr_get_be32`
and `barr_set` are now one call of the template, so each body is written once,
and the old names stay (additive API). Nothing new is trusted.
`tests/dynamic/content_inline` is `content` on the template names, and
`tests/static/reject/*-inline-*` repeat the rejects of the accessors (a cell past
the end, a cell claimed to hold another value, the lemma about other cells used
for the same cell, and the four cells of `barr_get_be32` past the end, of the
wrong cell and of the wrong value) with `accept/content-inline-use`.

**Override exposure (the review of array#63, sha256#59).** A template body is
compiled into each translation unit that instantiates it, so a package in the
dependency graph that implements the same template (`implement{} $A.barr_get_inline
...` in a dependent) replaces it at its own call sites, silently. The external
names are protected by the linker (a second `barr_get` is a link error); the
templates are not. A safe package that depends on an unsafe one carrying such an
override gets its body too. Writing such a body needs an unsafe package, since it
casts. The templates are not new trusted primitives (the owner's ruling). The
exposure is tracked by bats-lang/bats#421, which rejects an `implement` of a
template or function that another package declares.

## CI is pinned

Every input to CI is pinned in the source (bats-lang/repository-prototype#269),
so a commit that passes keeps passing:

* The package has no dependencies, so its `bats.lock` is the empty one `bats lock --repository <dir>` writes ("wrote bats.lock (no dependencies)"); the shared package-check.yml requires a lock, so `bats check` also refuses a `#use` the lock does not name.
* The compiler is the commit in `.github/bats-version`, read by every
  workflow that builds bats (and by the publish workflow).
* The package repository is fetched at the commit in
  `.github/repository-version`, so what the test packages under `tests/`
  lock (`bats lock --dev`) is pinned too.
* `publish.yml` and `relock-pins.yml` in bats-lang/repository-prototype are
  called by commit, never `@main`.

Pins move only through a reviewed pull request that runs the same CI. The
daily `relock.yml` (the shared `relock-pins.yml`) relocks against the
newest, moves the compiler and repository pins, pushes `relock/<date>`,
opens a pull request listing the old and new versions and dispatches
`check.yml` on it, so a breaking publish shows as a red relock pull
request and main stays green. GITHUB_TOKEN cannot change workflow files,
so without a `RELOCK_TOKEN` secret that pull request lists a workflow pin
that would move instead of moving it: move it in a pull request of its
own. A pull request that needs newer packages runs `bats lock
--repository <dir>` and commits `bats.lock` (and
`.github/repository-version`) with the change.
