# array

## Allocation size is bounded on purpose

`alloc` takes at most 1048576 elements (`{n:pos | n <= 1048576}`). This is a
design constraint, not an oversight: capping arbitrary allocations limits
heap fragmentation. Do not raise it, and do not work around it with a
bigger raw allocation somewhere else.

Code that needs more memory than one bounded allocation (a large file, a
large output) uses a pool: one region reserved up front, handed out in
pieces whose sizes the types account for, and released as a whole.

## Pools must be sound

A pool's arrays are not ordinary `alloc` arrays:

* The pool's type tracks the space left, so a piece that does not fit
  does not type-check (no runtime capacity check).
* A piece cannot be passed to `free`; only destroying the pool releases
  memory.
* Pieces are zero bytes only for element types where zero bytes are a
  valid value, as with `alloc`.

The first arena (deleted in #21) had none of these: `arena_alloc` never
compared its offset to the size, its arrays could be freed, and it handed
out zero bytes as any type.
