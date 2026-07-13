import Mathlib.Data.List.Nodup

/-
# RotatedLayout — the verified column allocator (Phase 1 of the verified-snarky foundation)

THE DISEASE (paid for in the revoked-root 178 migration, 2026-07): the rotated-block column layout is
a pile of hand-carried integers spread across ~14 emit files + two byte-identical Rust producers, and
the invariant that makes a layout *legal* — no two things write the same column — is an UNCHECKED
comment (the only `Nodup` in the emit today is `memAddrsNodup`, which is about memory addresses, not
columns). So a flag-day is a 14-file act of faith that plonky3 audits *after* a VK regen instead of the
type system at construction.

THE CURE: make the layout a first-class object whose CONSTRUCTOR carries the invariants. A flag-day
becomes a new `def` + a `Legal` proof discharged by `native_decide`, not a re-grind; an ill-aligned /
overlapping layout becomes UNCONSTRUCTABLE.

`rotated178` below is the current geometry, read from the authoritative occupied-column set in
`cell/src/commitment.rs::compute_rotated_pre_limbs` (HEAD). Wiring the emit (`EffectVmEmitRotationV3`)
to DERIVE its `*GroupCol` positions from a `RotatedLayout` — so producer + circuit + emit share ONE
source, killing the drift class — is Phase 2.
-/

namespace Dregg2.Circuit.Emit.RotatedLayout

/-- One faithful-8-felt group: lane 0 (the scalar limb the root historically rode) plus the seven
    completion columns (which may be non-contiguous — e.g. `fields_root` reuses headroom limbs). -/
structure Group where
  lane0      : Nat
  completion : List Nat   -- length 7
deriving DecidableEq, Repr

/-- The abstract rotated pre-iroot column layout: every occupied column, as data. -/
structure RotatedLayout where
  numPreLimbs     : Nat
  singles         : List Nat    -- scalars with no completion group (+ every group lane-0 is in its Group)
  groups          : List Group  -- the faithful-8-felt roots
  octets          : List Nat    -- octet BASES (each occupies base .. base+8)
  fieldsOctet     : List Nat    -- the 56 fields[0..7] completion lanes
  cellsCompletion : List Nat    -- circuit-only, producer-zero (still OCCUPIED in the circuit)
  pads            : List Nat
deriving Repr

/-- Every column an instance occupies, flattened — the domain of the disjointness obligation. -/
def RotatedLayout.occupied (L : RotatedLayout) : List Nat :=
  L.singles
    ++ L.groups.flatMap (fun g => g.lane0 :: g.completion)
    ++ L.octets.flatMap (fun b => (List.range 8).map (· + b))
    ++ L.fieldsOctet
    ++ L.cellsCompletion
    ++ L.pads

/-- **THE THREE LEGALITY OBLIGATIONS** — all decidable, so a concrete layout discharges them by
    `native_decide`, and an illegal layout cannot be constructed. -/
structure Legal (L : RotatedLayout) : Prop where
  /-- Disjointness: no two things write the same column. THE invariant that was a comment. -/
  disjoint    : L.occupied.Nodup
  /-- Bounds: every occupied column is a real pre-iroot limb. -/
  inBounds    : ∀ c ∈ L.occupied, c < L.numPreLimbs
  /-- The multiple-of-3 body discipline: the wire-commit chain folds the body (limbs `4 ..
      numPreLimbs-1`) in arity-3 groups after the arity-4 head; a leftover chunk is the arity-2/arity-9
      refuse the chip rejects — the exact 170-leftover fork we hit. -/
  bodyAligned : (L.numPreLimbs - 4) % 3 = 0

/-- The CURRENT deployed rotated geometry (178 pre-iroot limbs), grounded lane-for-lane in
    `compute_rotated_pre_limbs`. This enumeration is a complete tiling of `0..177` (every column once). -/
def rotated178 : RotatedLayout where
  numPreLimbs := 178
  singles := [0, 1, 2, 3,                    -- cells_root, r0/r1/r2 = bal_lo/nonce/bal_hi
              4, 5, 6, 7, 8, 9, 10, 11,      -- r3..r10 = fields[0..7] lane-0 (welded)
              29, 30, 31, 32, 35]            -- lifecycle, epoch, committed_height, disc, mode
  groups := [
    ⟨24, [12, 13, 14, 15, 16, 17, 18]⟩,      -- authority_digest
    ⟨25, [52, 53, 54, 55, 56, 57, 58]⟩,      -- cap_root
    ⟨26, [68, 69, 70, 71, 72, 73, 74]⟩,      -- nullifier_root
    ⟨27, [75, 76, 77, 78, 79, 80, 81]⟩,      -- commitments_root
    ⟨28, [59, 60, 61, 62, 63, 64, 65]⟩,      -- heap_root
    ⟨33, [38, 39, 40, 41, 42, 43, 44]⟩,      -- perms_digest
    ⟨34, [45, 46, 47, 48, 49, 50, 51]⟩,      -- vk_digest
    ⟨36, [66, 67, 19, 20, 21, 22, 23]⟩,      -- fields_root (non-contiguous: reuses headroom 19..23)
    ⟨37, [82, 83, 84, 85, 86, 87, 88]⟩]      -- revoked_root
  octets := [89, 97, 105]                    -- child_vk, contract_hash, pubkey octet bases
  fieldsOctet := (List.range 56).map (· + 113)   -- 113..168
  cellsCompletion := [169, 170, 171, 172, 173, 174, 175]  -- circuit-only, producer-zero
  pads := [176, 177]

/-- The current layout is LEGAL — disjoint, in-bounds, body-aligned. The disjointness invariant that
    lived as a stale hand-comment is now a machine-checked theorem. A future flag-day re-runs exactly
    this: a new `def` + `by native_decide`. -/
theorem rotated178_legal : Legal rotated178 where
  disjoint    := by native_decide
  inBounds    := by native_decide
  bodyAligned := by native_decide

end Dregg2.Circuit.Emit.RotatedLayout
