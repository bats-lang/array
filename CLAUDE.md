# array

## Allocation size is bounded on purpose

`alloc` takes at most 1048576 elements (`{n:pos | n <= 1048576}`). This is a
design constraint, not an oversight: capping arbitrary allocations limits
heap fragmentation. Do not raise it, and do not work around it with a
bigger raw allocation somewhere else.

Code that needs more memory than one bounded allocation (a large file, a
large output) uses a pool: one region reserved up front, handed out in
pieces whose sizes the types account for, and released as a whole.

## The arena is the pool

`arena_create<a>(max)` reserves one zeroed region of `max` elements (up to
268435456); `arena_alloc` hands out pieces of it, `arena_return` takes them
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
  `arena_create` has instances only for element types where zero bytes
  are a valid value.
* When the region cannot be had, `arena_create` returns `arena_none`,
  never a null arena.

The first arena (removed in #21 and restored here) had none of these:
`arena_alloc` never compared its offset to the size, its arrays could be
freed, and it handed out zero bytes as any type. Fix such problems; do
not delete the facility.

`tests/static` rejects each misuse (overfill, freeing a piece, returning
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

* The package has no dependencies, so it has no `bats.lock`.
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
