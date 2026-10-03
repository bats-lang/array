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

`arena_create<a>(class | max)` reserves one zeroed region of `max`
elements, `max` one of the size classes; `arena_alloc` hands out pieces of it, `arena_return` takes them
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

## An arena's size is a class

An arena is one of a few sizes fixed at compile time (`ARENA_CLASS`:
64 KiB, 256 KiB, 1 MiB, 4 MiB and 16 MiB elements, powers of 4), so a
freed region is the size of the next one asked for: the allocator can
reuse it whole (bats-lang/bats#241) instead of piling up regions of odd
sizes. `arena_create` takes a proof `ARENA_CLASS(max)`, whose
constructors are each indexed by a literal, so a size computed at run
time, or a constant that is not a class, does not type-check.
`arena_class_of(n)` gives the smallest class that holds `n` elements,
or `arena_too_large` over `ARENA_MOST` (16 MiB). The classes were chosen
by measuring EPUBs (bats-lang/quire#251): a page's arena is 4 MiB, and
the largest file a reader holds whole (its sync file) is 16 MiB. Do not
add a class for a size one caller computes; take the smallest class that
holds it.

The first arena (removed in #21 and restored here) had none of these:
`arena_alloc` never compared its offset to the size, its arrays could be
freed, and it handed out zero bytes as any type. Fix such problems; do
not delete the facility.

`tests/static` rejects each misuse (a size that is not a class, a size
computed at run time, overfill, freeing a piece, returning
it to another arena, destroying with a piece out, a pointer element
type); `tests/dynamic/arena` exercises pieces past the 1 MiB `alloc`
bound.

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
