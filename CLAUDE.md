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
type); `tests/dynamic/arena` exercises pieces past the 1 MiB `alloc`
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
* The lemmas are proved here, by the compiler, with no `praxi` and no
  `assume`: `setc_len`, `setc_nth_same`, `setc_nth_other` (the other cells
  are as they were; needs `i != j`), `nth_in_len` and `nth_functional`.
* The trusted core is the six primitives in the implementation block of
  `lib.bats`: each does what its type says to the memory (reads or writes
  one byte, copies, allocates) and fabricates the proof its type gives.
  Nothing else in the package or in a package using it makes a proof of
  an array's contents. `tests/dynamic/content` runs them; `tests/static`
  rejects a cell claimed to hold another value, a cell past the end, and
  the lemma about other cells used for the same cell.
* A proof about a `barr` holds only while the program holds it: `barr_to_arr`
  forgets the cells, and `barr_of_arr` starts again from cells nothing is
  known of.

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
