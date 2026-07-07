/-
C0 probe — the region/view arena bounds-check + total byte-scan primitive,
as a self-contained Lean 4 model (core only, no Mathlib).

This is the ADR-7 `region`/`view` shape reduced to its smallest honest core:
a flat immutable byte arena, plus a typed view `(off, len)`. The primitive
`boundScan` is the *read of the view*: it succeeds (returns a rolling
checksum of the viewed bytes) exactly when the view lies in-bounds of the
arena — the `Store.Wf` obligation of drorb's `Arena/Basic.lean` `Store.resolve`
specialized to one arena — and returns `none` (out of bounds) otherwise.

`boundScan` is the SPEC. The Pancake program `pnk/boundscan.pnk` is the
IMPLEMENTATION. The preservation obligation (C0-REPORT §4) is that the
machine code cake emits for the .pnk refines this function.

The rolling checksum `acc := (acc*31 + b) mod 2^24` is deliberately the same
fold R05's H1 kernel used: it defeats dead-code elimination and doubles as a
cross-kernel correctness witness (a wrong byte, wrong order, or wrong bound
changes the digest).
-/

namespace C0

/-- One checksum step. All arithmetic is in `UInt32`; the `&&& 0xFFFFFF`
mask keeps `acc < 2^24`, so `acc*31 + b < 2^24*31 + 255 < 2^32` and the
`UInt32` wrap never fires — the model computes over the mathematical integers
within range, exactly as the Pancake `& 16777215` does. -/
@[inline] def step (acc : UInt32) (b : UInt8) : UInt32 :=
  (acc * 31 + b.toUInt32) &&& 0xFFFFFF

/-- Fold `step` over the `len` bytes starting at `off`. Structural on a fuel
argument so the model is total by construction (no `partial`, no termination
obligation). Out-of-range indices read `0`, but the only caller
(`boundScan`) invokes this solely on in-bounds ranges, so that branch is
never taken on the specified domain. -/
def scanFrom (a : Array UInt8) (off : Nat) : Nat → UInt32 → UInt32
  | 0,        acc => acc
  | (n+1), acc => scanFrom a (off+1) n (step acc ((a[off]?).getD 0))

/-- The primitive. A view `(off, len)` into arena `a`:
    * in-bounds (`off + len ≤ a.size`) ⟹ `some digest`;
    * out-of-bounds                      ⟹ `none`.
This is `Store.resolve`'s bounds discipline (drorb `Arena/Basic.lean`) with a
concrete total fold standing in for "return the resolved slice". -/
def boundScan (a : Array UInt8) (off len : Nat) : Option UInt32 :=
  if off + len ≤ a.size then some (scanFrom a off len 0) else none

/-- The single-word encoding used to compare against the compiled machine:
`none` (out of bounds) ↦ the sentinel `0xFFFFFFFF`; `some k` ↦ `k`. Sound as
an injection on the reachable range because every in-bounds digest is masked
to 24 bits (`< 2^24 < 0xFFFFFFFF`), so the sentinel is unreachable as a
success value. This is exactly what the Pancake program writes to its result
word (§3). -/
def encode : Option UInt32 → UInt32
  | none   => 0xFFFFFFFF
  | some k => k

/-! ### Reference vectors

The arena is the 16-byte ASCII vector `GET / HTTP/1.1\r\n` (a wire fragment,
so the digest is over recognizable bytes). Views chosen adversarially:
in-bounds interior, the exact-boundary view (`off+len = size`, must succeed),
a one-past-the-end view (`off+len = size+1`, must fail), and an off-beyond-
end view. These are the vectors run in all three kernels (Lean here, HOL4
`EVAL`, and the compiled Pancake binary) in C0-REPORT §5. -/

/-- `GET / HTTP/1.1\r\n` — 16 bytes. -/
def arena : Array UInt8 :=
  #[0x47,0x45,0x54,0x20,0x2f,0x20,0x48,0x54,0x54,0x50,0x2f,0x31,0x2e,0x31,0x0d,0x0a]

/-- The vector suite: `(off, len)` pairs. -/
def vectors : List (Nat × Nat) :=
  [ (0, 16),   -- whole arena, exact fit
    (0, 3),    -- "GET"
    (4, 10),   -- "/ HTTP/1.1"
    (14, 2),   -- "\r\n", boundary view (off+len = size)
    (0, 17),   -- one past the end -> none
    (16, 1),   -- off at end, len 1 -> none
    (10, 8),   -- straddles the end -> none
    (16, 0) ]  -- empty view exactly at end -> some (empty digest = 0)

def main : IO Unit := do
  IO.println s!"arena.size = {arena.size}"
  for (off, len) in vectors do
    let r := boundScan arena off len
    IO.println s!"boundScan off={off} len={len}  =>  {repr r}   encoded={encode r}"
