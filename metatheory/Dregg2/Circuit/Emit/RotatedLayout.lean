import Mathlib.Data.List.Nodup

/-
# RotatedLayout — the verified column allocator (Phase 1–2 of the verified-snarky foundation)

THE DISEASE (paid for in the revoked-root 178 migration, 2026-07): the rotated-block column layout was
a pile of hand-carried integers spread across ~14 emit files + two byte-identical Rust producers, and
the invariant that makes a layout *legal* — no two things write the same column — was an UNCHECKED
comment. So a flag-day was a 14-file act of faith that plonky3 audited *after* a VK regen instead of the
type system at construction.

THE CURE: make the layout a first-class object with an explicit machine-checked legality witness, whose
`groupCol` projection is the SINGLE SOURCE the emit reads its positions from. A flag-day becomes a new
`def` + `native_decide`; an ill-aligned / overlapping layout becomes UNCONSTRUCTABLE.

`rotated184` is the current geometry (178 until the 2026-07-31 ninth-lane flag day). `EffectVmEmitRotationV3` projects its group columns from this
object; `EmitLayoutManifest.lean` emits its `groupTable` to Rust; and both Rust producers plus the
circuit trace generator consume that generated table. The concrete integers therefore live here once.
-/

namespace Dregg2.Circuit.Emit

/-- The named faithful-8-felt roots the rotated block commits. -/
inductive GroupName
  | authority | cap | nullifier | commitments | heap | perms | vk | fields | revoked | cells
deriving DecidableEq, Repr

/-- One faithful-8-felt group: lane 0 (the scalar limb the root historically rode) plus the seven
    completion columns (which may be non-contiguous — e.g. `fields` reuses headroom limbs 19..23). -/
structure LayoutGroup where
  lane0      : Nat
  completion : List Nat   -- length 7
deriving DecidableEq, Repr

/-- The abstract rotated pre-iroot column layout: every occupied column, as data. -/
structure RotatedLayout where
  numPreLimbs     : Nat
  singles         : List Nat                    -- scalars with no completion group
  groups          : List (GroupName × LayoutGroup)  -- the faithful-8-felt roots, name-tagged
  octets          : List Nat                    -- octet BASES (each occupies base .. base+8)
  fieldsOctet     : List Nat                    -- the 64 fields[0..7] completion lanes (8 slots x lanes 1..8)
  cellsCompletion : List Nat                    -- legacy slot, now empty (cells is a named group)
  pads            : List Nat
deriving Repr

/-- Every column an instance occupies, flattened — the domain of the disjointness obligation. -/
def RotatedLayout.occupied (L : RotatedLayout) : List Nat :=
  L.singles
    ++ L.groups.flatMap (fun p => p.2.lane0 :: p.2.completion)
    ++ L.octets.flatMap (fun b => (List.range 8).map (· + b))
    ++ L.fieldsOctet
    ++ L.cellsCompletion
    ++ L.pads

/-- **THE PROJECTION** — the single source the emit reads a group's within-block column from. Lane 0 is
    the scalar limb; lanes 1..7 index the completion list. `none` = the group/lane is absent. -/
def RotatedLayout.groupCol (L : RotatedLayout) (name : GroupName) (i : Fin 8) : Option Nat :=
  match L.groups.find? (fun p => p.1 = name) with
  | some p => if (i : Nat) = 0 then some p.2.lane0 else p.2.completion[(i : Nat) - 1]?
  | none   => none

/-- **THE LEGALITY OBLIGATIONS** — all decidable, so a concrete layout discharges them by
    `native_decide`, and an illegal layout cannot be constructed. -/
structure Legal (L : RotatedLayout) : Prop where
  /-- Every named digest really is faithful-8: lane 0 plus exactly seven completion lanes. -/
  groupWidth  : ∀ p ∈ L.groups, p.2.completion.length = 7
  /-- Names are keys, not labels: `groupCol` must never silently select the first duplicate. -/
  groupNames  : (L.groups.map Prod.fst).Nodup
  /-- Every semantic group exists, so a consumer projection can never fall through `Option.getD`. -/
  groupCoverage : ∀ name : GroupName, name ∈ L.groups.map Prod.fst
  /-- Disjointness: no two things write the same column. THE invariant that was a comment. -/
  disjoint    : L.occupied.Nodup
  /-- Bounds: every occupied column is a real pre-iroot limb. -/
  inBounds    : ∀ c ∈ L.occupied, c < L.numPreLimbs
  /-- The multiple-of-3 body discipline: the wire-commit chain folds the body (limbs `4 ..
      numPreLimbs-1`) in arity-3 groups after the arity-4 head; a leftover chunk is the arity-2/arity-9
      refuse the chip rejects — the exact 170-leftover fork we hit. -/
  bodyAligned : (L.numPreLimbs - 4) % 3 = 0

/-- The current pre-iroot extent. Keeping this scalar beside the instance avoids unfolding the full
layout through descriptor reduction while leaving a count flag-day in this one verified source file.

⚑ **FLAG DAY 2026-07-31: 178 → 184.** The fields octet became a fields NONET. `p = 2013265921`, so
`log₂ p = 30.907` and eight lanes carry 247.26 bits against a 32-byte field's 256 — **no 8-lane
encoding of 32 bytes is injective under any chunking**, pigeonhole, whatever the lanes contain. The
`fields[0..7]` lanes are the only binding those fields have (they are excluded from the byte-exact
authority residue, `cell/src/commitment.rs` — "bound by their own limbs"), so the deficit reached
`TurnReceipt::{pre,post}_state_hash`. `Dregg2.Circuit.FieldLanes9.fieldToLanes9_injective` is the
nine-lane encoder that closes it, and each field's NINTH lane needs a column.

The six extra columns come out of the two free pads (176, 177) plus 178..183, and **NOTHING SHIFTS**:
every column that had a meaning at 178 keeps it. `(184 - 4) % 3 = 0`, so `bodyAligned` survives — 186
would have been ILLEGAL and 187 costs four columns for nothing. Downstream: `B_SPAN` 239 → 247,
`APPENDIX_SPAN` 521 → 537, the chained absorption 58 → 60 carriers. -/
def rotatedNumPreLimbs : Nat := 184

/-- The CURRENT deployed rotated geometry (184 pre-iroot limbs). This enumeration is a complete
tiling of `0..183` (every column once, no pads). -/
def rotated184 : RotatedLayout where
  numPreLimbs := rotatedNumPreLimbs
  singles := [1, 2, 3,                       -- r0/r1/r2 = bal_lo/nonce/bal_hi (cells lane-0 is a group)
              4, 5, 6, 7, 8, 9, 10, 11,      -- r3..r10 = fields[0..7] lane-0 (welded)
              29, 30, 31, 32, 35]            -- lifecycle, epoch, committed_height, disc, mode
  groups := [
    (.authority,   ⟨24, [12, 13, 14, 15, 16, 17, 18]⟩),
    (.cap,         ⟨25, [52, 53, 54, 55, 56, 57, 58]⟩),
    (.nullifier,   ⟨26, [68, 69, 70, 71, 72, 73, 74]⟩),
    (.commitments, ⟨27, [75, 76, 77, 78, 79, 80, 81]⟩),
    (.heap,        ⟨28, [59, 60, 61, 62, 63, 64, 65]⟩),
    (.perms,       ⟨33, [38, 39, 40, 41, 42, 43, 44]⟩),
    (.vk,          ⟨34, [45, 46, 47, 48, 49, 50, 51]⟩),
    (.fields,      ⟨36, [66, 67, 19, 20, 21, 22, 23]⟩),  -- non-contiguous: reuses headroom 19..23
    (.revoked,     ⟨37, [82, 83, 84, 85, 86, 87, 88]⟩),
    -- WOUND #23 (`docs/WOUND-felt-width-boundaries-2026-07-19.md`): this completion group used to be
    -- documented "circuit-only, producer-zero" — and it WAS zero in both Rust producers, which made
    -- the committed `cells_root` a ~31-bit COMPONENT inside the faithful 8-felt consensus anchor.
    -- Both producers (`rotation_witness::produce`, `commitment::compute_rotated_pre_limbs`) now fill
    -- all eight lanes on EVERY turn from the native `CanonicalHeapTree8` root; the
    -- createCell/factory/spawn trace generator still OVERWRITES the group with its own in-circuit
    -- accounts tree (the grow-gate's object). A layout slot is not a binding — read the WRITER.
    (.cells,       ⟨0, [169, 170, 171, 172, 173, 174, 175]⟩)]
  octets := [89, 97, 105]                    -- child_vk, contract_hash, pubkey octet bases
  -- ⚑ 56 → 64. Lanes 1..7 of each `fields[slot]` keep their historical window `113 + 7·slot .. +6`
  -- (113..168, UNMOVED); the NINTH lane of slot `j` is the new column `176 + j` (176..183). The
  -- first two of those were the layout's only free pads; the remaining six are the extent bump.
  fieldsOctet := (List.range 56).map (· + 113) ++ (List.range 8).map (· + 176)
  cellsCompletion := []                      -- (cells is now a group; kept for structural symmetry)
  pads := []                                 -- consumed by the ninth fields lane; nothing spare left

/-- **THE NINTH-LANE PROJECTION** — the single source a consumer reads a `fields[slot]` lane column
from. Lane 0 is the welded v1 face limb `4 + slot` (`gFieldWriteP1` / `param1` / `field_to_u64`);
lanes 1..7 are the historical completion window; lane 8 is the flag-day column `176 + slot`.

Consumers must read THIS, never `113 + 8·slot` — the nonet is deliberately NON-CONTIGUOUS so the
flag day shifts no existing column, exactly like the `fields` root group already reuses headroom
19..23. -/
def fieldLaneCol (slot : Fin 8) (lane : Fin 9) : Nat :=
  if lane.1 = 0 then 4 + slot.1
  else if lane.1 = 8 then 176 + slot.1
  else 113 + 7 * slot.1 + (lane.1 - 1)

/-- The current layout is LEGAL — every semantic group exists exactly once at width eight, and the
    complete tiling is disjoint, in-bounds, and body-aligned. -/
theorem rotated184_legal : Legal rotated184 where
  groupWidth  := by native_decide
  groupNames  := by native_decide
  groupCoverage := by intro name; cases name <;> native_decide
  disjoint    := by native_decide
  inBounds    := by native_decide
  bodyAligned := by native_decide

/-- STRONGER than `Nodup`: the layout occupies EXACTLY 184 columns. With `disjoint` + `inBounds` this
    forces a complete tiling of `0..183` — no gaps, no reuse, no wasted column, and (unlike 178) no
    pads left over. -/
theorem rotated184_complete : rotated184.occupied.length = 184 := by native_decide

/-- **THE FLAG DAY SHIFTED NOTHING.** Every column the 178-geometry occupied still means the same
thing: the 178 old columns are exactly `occupied \ {178,…,183}`, and the two old pads plus the six
new columns are exactly the eight ninth lanes. Stated as the two set facts a reader can check. -/
theorem rotated184_ninth_lanes :
    (List.range 8).map (fun j => fieldLaneCol ⟨j % 8, by omega⟩ 8) = [176, 177, 178, 179, 180, 181, 182, 183] := by
  native_decide

theorem rotated184_ninth_lanes_are_new :
    ∀ c ∈ (List.range 8).map (fun j => fieldLaneCol ⟨j % 8, by omega⟩ 8), 176 ≤ c := by
  native_decide

/-- Every lane column the nonet projection names really is an occupied column of the layout, and the
72 of them (8 slots × 9 lanes) are pairwise distinct — the invariant that was a comment. -/
theorem fieldLaneCol_occupied :
    ∀ p ∈ (List.range 8).flatMap (fun j => (List.range 9).map (fun l =>
      fieldLaneCol ⟨j % 8, by omega⟩ ⟨l % 9, by omega⟩)), p ∈ rotated184.occupied := by
  native_decide

theorem fieldLaneCol_nodup :
    ((List.range 8).flatMap (fun j => (List.range 9).map (fun l =>
      fieldLaneCol ⟨j % 8, by omega⟩ ⟨l % 9, by omega⟩))).Nodup := by
  native_decide

/-- Sanity: the projection agrees with the raw group data (nullifier lane 0 = limb 26, lane 1 = 68). A
    Phase-2 bridge theorem will pin each emit `*GroupCol` to exactly `rotated184.groupCol`. -/
example : rotated184.groupCol .nullifier 0 = some 26 := by native_decide
example : rotated184.groupCol .nullifier 1 = some 68 := by native_decide
example : rotated184.groupCol .fields 1 = some 66 := by native_decide  -- the non-contiguous case

/-- **EMIT-READY group table** — each group as `[lane0, completion_1 .. completion_7]`, in exactly the
    shape the Rust `[[usize; 8]; N]` layout wants. `EmitLayoutManifest.lean` exports this value into
    `layout_generated.rs`; Rust names are projections of the emitted table, never another data copy. -/
def RotatedLayout.groupTable (L : RotatedLayout) : List (List Nat) :=
  L.groups.map (fun p => p.2.lane0 :: p.2.completion)

/-- The emit-ready table for the current geometry, with its length pinned (10 faithful-8-felt groups). -/
theorem rotated184_groupTable_len : rotated184.groupTable.length = 10 := by native_decide

/-- Every emitted row has the Rust type's exact width. This is a `Legal` obligation, not an emitter
    convention that could fail only after generation. -/
theorem rotated184_groupTable_row_width :
    ∀ row ∈ rotated184.groupTable, row.length = 8 := by native_decide

/-- Ten faithful-8 groups contribute exactly 80 occupied columns. -/
theorem rotated184_groupTable_flatten_len : rotated184.groupTable.flatten.length = 80 := by native_decide

end Dregg2.Circuit.Emit
