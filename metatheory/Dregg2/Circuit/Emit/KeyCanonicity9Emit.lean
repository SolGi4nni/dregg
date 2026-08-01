/-
# Dregg2.Circuit.Emit.KeyCanonicity9Emit — `CanonicalKey9`, EMITTED.

## SUBSTRATE, SAID OUT LOUD

Lean-authored AIR. The constraints below are emitted from Lean; Rust re-reads the descriptor and
never hand-writes a gate, a lookup or an `air_accepts`.

## ⚑ READ `Dregg2.Circuit.KeyLanes9` FIRST — THIS FILE DOES NOT WRAP THE DEPLOYED ENCODER

The obvious task was "apply `FieldsCanonicity9Emit` to the owner-key octet". `KeyLanes9`
REFUTES that, with an exhibit: `eight_lane_canonicity_is_not_a_repair` produces two DISTINCT 32-byte
keys whose deployed octets are equal AND fully canonical (`canonical_32_to_felts_8` packs
`8+8+8+6 = 30` bits and drops bits 6-7 of every fourth byte). `keyCanonical8_iff_in_image` proves
`[0,2^30)^8` is EXACTLY that packer's image, so there is no missing leg to find and no stronger
eight-lane wrap to write. **A canonicity envelope on the deployed octet would force the columns into
the image of a map that is not injective on its domain** — a containment shipped while the real fix
is named as a later phase, which is the substitution this repo's own doctrine forbids.

So this file emits the envelope of the REPLACEMENT nine-lane encoder (`KeyLanes9.keyToLanes9`,
injective by a machine-checked left inverse), not of the deployed eight-lane one.

## The gadget — and there is no gadget

Per rotated block, NINE lookups and NOTHING ELSE:

```text
  lanes 0..7  < 2^29        -- eight lookups on the LANE table
  lane  8     < 2^24        -- ONE lookup, on a NARROWER table
```

Zero gates. Zero aux columns. Zero new hash sites. `KeyLanes9.canonicalKey9_iff_in_image` proves
those two legs are EXACTLY the image, so the wrap admits every honest key's nonet and no other
vector. The fields wrap needed seven aux columns, a cube gate and a doubled selector because its
lanes 0/1 were a `mod p` REDUCTION welded to the v1 face and therefore unmovable; the key octet is
welded to nothing (measured 2026-07-31: zero `colEq`, zero gate bodies, zero `pi_binding`s, zero
range lookups across all 117 rotated members), so the encoding was replaced wholesale and the
reduction — and with it `NoWrap`, the cube gate and the aux region — disappeared.

Two consequences worth stating because the fields wrap could not claim either:

  * **`keyCanon9_forces_canonical` needs no non-last-row hypothesis.** A `gate` is exempt on the last
    row until `hardenLastRow` lifts it; a `lookup` is not. Every leg here is a lookup.
  * **It needs no canonical-column envelope hypothesis either.** The fields forcing had to assume
    `0 ≤ col < p` for lanes 0/1 and the aux columns, because no lookup covered them. Here all NINE
    lanes are covered, so both bounds come from the emitted constraints themselves.

## ⚑ THE EXHIBIT, AND WHY LEG 2 IS NOT DECORATION

`forgedKeyNonet = [0,…,0,2^24]`. Every lane is below `2^29`, so the NAIVE wrap — nine lookups all at
the lane width, which is what "range-check the lanes" means to a reader who has not done the
arithmetic — accepts it. Its recomposed value is `2^24 · (2^29)^8 = 2^256` exactly: one full wrap of
the byte window, so the total decoder reads all thirty-two base-256 digits as zero and it decodes to
the ALL-ZERO key, byte for byte, while being a different committed vector.
`the_forged_nonet_passes_the_naive_wrap_and_is_unsat_here` bundles all three facts, and
`keyCanon9_rejects_the_forged_nonet` lifts the refusal to `¬ Satisfied2` over the emitted
constraints. The UNSAT is total: no assignment of anything else can rescue it, because the narrow
table simply does not contain the row.

## ⚑ WHAT RUNG THIS REACHES — say it exactly

**AUTHORED AND PROVED. NOT EMITTED INTO ANY MEMBER, AND NOT CONSUMED BY ANY VERIFIER.**

⚑ **CORRECTED 2026-08-01 — the forcing and the capstone used to quantify over an arbitrary
`col : KeyColMap`.** Only lane 8's column is unknown; the other eight are `B_PUBKEY_OCTET` at stride
`B_SPAN`, which `deployedKeyCols` already recorded and four `#guard`s already knew. A theorem named
"determines the owner key" that quantifies over the column map determines whatever nine columns it
is handed — strictly weaker on the column axis than this file's own template
(`FieldsCanonicity9Emit.canon9_forces_canonical` takes a face width and reads the concrete
`laneColAt`), while the write-up presented the abstraction as scrupulousness. Now only `lane8Off` is
a parameter, `§1.1` ties lanes 0..7 to the ABSORBED pre-limbs `wireCommitR` folds
(`deployedKeyCols_octet_is_absorbed`), and the capstone states the ℤ-equalities at those limbs. The
old shape was not merely unproved on that axis but REFUTABLE: with the block span free, `span := 0`
put both blocks' lanes on the BEFORE octet.

The ninth lane's column still DOES NOT EXIST in the deployed layout and is still not invented here
— `lane8_is_absorbed_iff` is that blocker as a theorem rather than as prose:

  * an appendix column (where the fields aux region lives) is not in `preLimbsAt`, so it never enters
    the `wireCommitR` absorption chain — a ninth lane there is a free felt and `state_commit` would
    still bind only 232 bits of the key. **The ninth lane must be an absorbed PRE-LIMB.**
  * the pre-limb region is 184/184 full (`ROTATED_PADS = []`), so `rotatedNumPreLimbs` must grow, and
    it must grow to **187, not 185**: `B_SPAN := n + 3 + (n − 4) / 3` is floor division while the
    real carrier chain is `chunk31`'s `chunkCount`, which steps every three limbs — at 185 the block
    is silently under-allocated by one carrier column. The unwritten invariant is
    `rotatedNumPreLimbs ≡ 1 (mod 3)`, and 187 buys exactly the three ninth lanes the counting demands
    (`public_key`, `child_vk`, `contract_hash`).
  * that moves every `state_commit`: **a re-genesis**, `CANONICAL_STATE_SCHEMA_EPOCH` 15 → 16.

Those files (`RotatedLayout.lean`, `EffectVmEmitRotationV3.lean`) were owned by a concurrent lane and
are not edited here. What is left to do is exactly that geometry move plus a Rust `key_limbs9`
producer; everything upstream of it is discharged below.

## Axiom hygiene
`#assert_axioms` ⊆ {propext, Classical.choice, Quot.sound}. No `sorry`, no `native_decide`.
-/
import Dregg2.Circuit.Emit.EffectVmEmitRotationV3
import Dregg2.Circuit.KeyLanes9

namespace Dregg2.Circuit.Emit.KeyCanonicity9Emit

open Dregg2.Exec.CircuitEmit (EmittedExpr)
open Dregg2.Circuit (Assignment)
open Dregg2.Circuit.DescriptorIR2
open Dregg2.Circuit.Emit (rotatedNumPreLimbs)
open Dregg2.Circuit.Emit.EffectVmEmit
open Dregg2.Circuit.Emit.EffectVmEmitV2 (rangeTidW)
open Dregg2.Circuit.Emit.EffectVmEmitRotationV3 (B_SPAN B_PUBKEY_OCTET preLimbsAt)
open Dregg2.Circuit.FieldLanes9 (Bytes32)
open Dregg2.Circuit.KeyLanes9 (K KTOP Nonet CanonicalKey9 LanesRanged TopLaneRanged UniformRanged
  keyToLanes9 keyLanes9ToBytes keyToLanes9_injective canonicalKey9_iff_in_image forgedKeyNonet
  zeroKey keyLanes9ToBytes_keyToLanes9)

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxRecDepth 8000

/-! ## §0 — the two range widths this emit introduces. -/

/-- The nonet's lane width: `2^29 < p`, so a lane NEVER reduces. Eight lookups ride this. -/
def KEY_LANE_BITS : Nat := 29

/-- ⚑ **THE NARROW LEG.** `2^256 / (2^29)^8 = 2^24`, so the top lane's weight leaves exactly this
much room. A lane-width lookup on lane 8 would leave `2^5` whole wraps of the byte window
available — `forgedKeyNonet` is the first of them. -/
def KEY_TOP_BITS : Nat := 24

theorem widths_are_the_exact_fit : 2 ^ (8 * KEY_LANE_BITS + KEY_TOP_BITS) = 2 ^ 256 := by
  norm_num [KEY_LANE_BITS, KEY_TOP_BITS]

theorem lane_width_is_K : (2 : Nat) ^ KEY_LANE_BITS = K := by
  norm_num [KEY_LANE_BITS, Dregg2.Circuit.KeyLanes9.K]

theorem top_width_is_KTOP : (2 : Nat) ^ KEY_TOP_BITS = KTOP := by
  norm_num [KEY_TOP_BITS, Dregg2.Circuit.KeyLanes9.KTOP]

/-! ## §1 — the emitted columns. ⚑ `lane8Off` IS THE ONLY PARAMETER.

**This file used to quantify over an arbitrary `col : KeyColMap` everywhere, including in the
capstone, and that was strictly weaker than its own template.** `FieldsCanonicity9Emit` takes a face
width and reads the concrete `laneColAt`; here EIGHT of the nine columns are equally fixed and known
— `B_PUBKEY_OCTET` at stride `B_SPAN` — and a theorem named "determines the owner key" that
quantifies over the column map determines whatever nine columns it is handed. The abstraction was
justified by "lane 8's column does not exist", which is true of lane 8 and of nothing else.

So: `w` is the face width (exactly as the fields template takes it), `lane8Off` is the one genuinely
unallocated offset, and everything that claims anything about the OWNER KEY is stated at
`deployedKeyCols w lane8Off`. `KeyColMap` survives as the type of the column-agnostic PLUMBING in §2
and §3 (`blk_mem`, `lookup_forces`, the peel) — those name no key and claim none. -/

/-- The nine committed columns of each rotated block's owner-key nonet. -/
abbrev KeyColMap := Fin 2 → Fin 9 → Nat

/-- **THE DEPLOYED COLUMNS.** Lanes 0..7 at `B_PUBKEY_OCTET .. +8` of block `blk` at the verified
stride `B_SPAN` — both read from `EffectVmEmitRotationV3`, never re-spelled here — and lane 8 at a
caller-supplied in-block offset that the geometry move must allocate as an absorbed PRE-LIMB (not an
appendix column: see the header, and `lane8_is_absorbed_iff` below for that as a theorem). -/
def deployedKeyCols (w lane8Off : Nat) : KeyColMap := fun blk lane =>
  if lane.1 < 8 then w + blk.1 * B_SPAN + B_PUBKEY_OCTET + lane.1
  else w + blk.1 * B_SPAN + lane8Off

/-- Lane `l < 8` sits at the octet's `l`-th offset inside its block. -/
theorem deployedKeyCols_octet_col (w lane8Off : Nat) (blk : Fin 2) {l : Fin 9} (hl : l.1 < 8) :
    deployedKeyCols w lane8Off blk l = w + blk.1 * B_SPAN + (B_PUBKEY_OCTET + l.1) := by
  simp only [deployedKeyCols]
  rw [if_pos hl]
  omega

/-- …and lane 8 sits at the offset the geometry move has yet to allocate. -/
theorem deployedKeyCols_lane8_col (w lane8Off : Nat) (blk : Fin 2) :
    deployedKeyCols w lane8Off blk 8 = w + blk.1 * B_SPAN + lane8Off := by
  simp [deployedKeyCols]

-- The eight offsets that ARE already fixed, against the committed layout constant (the Rust twin is
-- `trace_rotated::B_PUBKEY_OCTET = 105`, generated from `EmitLayoutManifest`). Re-typed by hand
-- against a committed artifact: the literals ARE the review. At today's `188`-wide bare v1 face and
-- `B_SPAN = 247` the BEFORE block's octet is `293..300` and the AFTER block's is `540..547`.
#guard B_PUBKEY_OCTET == 105
#guard (List.finRange 8).map (fun l => deployedKeyCols 188 184 0 ⟨l.1, by omega⟩)
  == [293, 294, 295, 296, 297, 298, 299, 300]
#guard (List.finRange 8).map (fun l => deployedKeyCols 188 184 1 ⟨l.1, by omega⟩)
  == [540, 541, 542, 543, 544, 545, 546, 547]
-- ⚠ The `184` above is NOT a proposed allocation — it is an ILLUSTRATIVE ninth-lane offset used
-- only to exercise the shape, and today's in-block offset 184 is occupied by the carrier band. The
-- real one comes from the `rotatedNumPreLimbs 184 → 187` move (header §"WHAT RUNG"), which this file
-- does not land. What the guard below actually checks is the shape claim that survives that move:
-- for a ninth-lane offset inside the span and off the octet, the two blocks' nonets are disjoint.
#guard ((List.finRange 9).map (deployedKeyCols 188 184 0)
   ++ (List.finRange 9).map (deployedKeyCols 188 184 1)).Nodup

/-! ### ⚑ §1.1 — THE COLUMNS ARE THE ABSORBED OWNER-KEY LIMBS, from two sources that are not each
other.

Pinning the eight is not tidiness. `preLimbsAt` is the list `wireCommitR` folds into `state_commit`;
a column outside it is a free felt the anchor never sees, which is the whole reason the ninth lane
cannot ride the appendix. So "this wrap constrains the owner key" is exactly the claim that its
columns ARE entries of THAT list at the octet's position — a statement relating `deployedKeyCols`
here to `EffectVmEmitRotationV3.preLimbsAt` there, not a constant checked against its own def.

Before this section existed, no THEOREM in the file mentioned `B_PUBKEY_OCTET` — only the `def` and
four `#guard`s did — and the octet tie was not merely unproved but REFUTABLE: with the block span a
free parameter, taking `span := 0` collapses both blocks' lanes 0..7 onto the BEFORE octet. -/

/-- The absorbed pre-limb COLUMNS of the block at `base`, positionally — `preLimbsAt` read as
addresses rather than values. -/
def preLimbColsAt (base : Nat) : List Nat := (List.range rotatedNumPreLimbs).map (base + ·)

theorem preLimbsAt_eq_rangeMap (base : Nat) (a : Assignment) :
    preLimbsAt base a = (List.range rotatedNumPreLimbs).map (fun k => a (base + k)) := rfl

theorem preLimbsAt_getD (base k : Nat) (a : Assignment) (hk : k < rotatedNumPreLimbs) :
    (preLimbsAt base a).getD k 0 = a (base + k) := by
  rw [preLimbsAt_eq_rangeMap, List.getD_eq_getElem _ _ (by simpa using hk)]
  simp

/-- **THE TIE.** Lane `l < 8` of the wrapped nonet reads pre-limb `B_PUBKEY_OCTET + l` of the very
list the rotated absorption chain folds — so the eight lookups land on the owner-key limbs
`state_commit` binds, and not on eight columns of this file's own choosing. -/
theorem deployedKeyCols_octet_is_absorbed (w lane8Off : Nat) (a : Assignment) (blk : Fin 2)
    {l : Fin 9} (hl : l.1 < 8) :
    a (deployedKeyCols w lane8Off blk l)
      = (preLimbsAt (w + blk.1 * B_SPAN) a).getD (B_PUBKEY_OCTET + l.1) 0 := by
  rw [deployedKeyCols_octet_col w lane8Off blk hl,
    preLimbsAt_getD _ _ _ (by have := l.isLt; simp only [B_PUBKEY_OCTET, rotatedNumPreLimbs]; omega)]

/-- The same fact as membership: every one of the eight is an absorbed column. -/
theorem octet_cols_are_absorbed (w lane8Off : Nat) (blk : Fin 2) {l : Fin 9} (hl : l.1 < 8) :
    deployedKeyCols w lane8Off blk l ∈ preLimbColsAt (w + blk.1 * B_SPAN) := by
  rw [deployedKeyCols_octet_col w lane8Off blk hl]
  simp only [preLimbColsAt, List.mem_map, List.mem_range]
  refine ⟨B_PUBKEY_OCTET + l.1, ?_, rfl⟩
  have := l.isLt
  simp only [B_PUBKEY_OCTET, rotatedNumPreLimbs]
  omega

/-- ⚑ **AND THE NINTH LANE STILL HAS NOWHERE TO GO — the header's blocker, as a theorem.** The
ninth-lane column is absorbed exactly when `lane8Off < rotatedNumPreLimbs`; the pre-limb region is
184/184 occupied (`rotated184.pads = []`, the `#guard` below), so today every choice is either an
ALIAS of a committed limb or a free felt outside `wireCommitR` — and in the second case
`state_commit` still binds only 232 bits of the key, which is the wound this wrap exists to close.
No `lane8Off` is admissible until `rotatedNumPreLimbs` grows. -/
theorem lane8_is_absorbed_iff (w lane8Off : Nat) (blk : Fin 2) :
    deployedKeyCols w lane8Off blk 8 ∈ preLimbColsAt (w + blk.1 * B_SPAN)
      ↔ lane8Off < rotatedNumPreLimbs := by
  rw [deployedKeyCols_lane8_col]
  simp only [preLimbColsAt, List.mem_map, List.mem_range]
  constructor
  · rintro ⟨k, hk, hEq⟩; omega
  · intro h; exact ⟨lane8Off, h, rfl⟩

#guard rotatedNumPreLimbs == 184
#guard Dregg2.Circuit.Emit.rotated184.pads == []
#guard (preLimbColsAt 188).length == 184
-- The octet window really is inside the absorbed region, at both blocks.
#guard ((List.finRange 8).map (fun l => deployedKeyCols 188 184 0 ⟨l.1, by omega⟩)).all
  (fun c => (preLimbColsAt 188).contains c)
#guard ((List.finRange 8).map (fun l => deployedKeyCols 188 184 1 ⟨l.1, by omega⟩)).all
  (fun c => (preLimbColsAt (188 + B_SPAN)).contains c)

#assert_axioms deployedKeyCols_octet_is_absorbed
#assert_axioms octet_cols_are_absorbed
#assert_axioms lane8_is_absorbed_iff

/-! ## §2 — the emitted constraints. -/

/-- A width-tagged range lookup (`EffectVmEmitV2.rangeLookupW`'s shape, at an explicit column). -/
def rangeLk (bits col : Nat) : VmConstraint2 := .lookup ⟨rangeTidW bits, [.var col]⟩

/-- One block's nine lookups: eight at the lane width, one at the narrow width. -/
def keyLookupsAt (col : KeyColMap) (blk : Fin 2) : List VmConstraint2 :=
  ((List.finRange 8).map (fun j => rangeLk KEY_LANE_BITS (col blk ⟨j.1, by have := j.isLt; omega⟩)))
    ++ [rangeLk KEY_TOP_BITS (col blk 8)]

/-- **THE EMIT** — `CanonicalKey9` over both rotated blocks' owner-key nonets. -/
def keyCanon9ConstraintsAt (col : KeyColMap) : List VmConstraint2 :=
  (List.finRange 2).flatMap fun blk => keyLookupsAt col blk

-- 2 × 9 = 18 lookups, ZERO gates.
#guard (keyCanon9ConstraintsAt (deployedKeyCols 188 184)).length == 18
#guard ((keyCanon9ConstraintsAt (deployedKeyCols 188 184)).filter (fun c => match c with
  | .lookup _ => true | _ => false)).length == 18
#guard ((keyCanon9ConstraintsAt (deployedKeyCols 188 184)).filter (fun c => match c with
  | .base (.gate _) => true | _ => false)).length == 0

/-- **THE WRAP.** `traceWidth`-, `piCount`-, table-, site- and range-INVARIANT. -/
def keyCanonical9At (col : KeyColMap) (d : EffectVmDescriptor2) : EffectVmDescriptor2 :=
  { d with constraints := d.constraints ++ keyCanon9ConstraintsAt col }

/-! ### The shape, machine-checked. -/

theorem keyCanonical9At_traceWidth (col : KeyColMap) (d : EffectVmDescriptor2) :
    (keyCanonical9At col d).traceWidth = d.traceWidth := rfl

theorem keyCanonical9At_piCount (col : KeyColMap) (d : EffectVmDescriptor2) :
    (keyCanonical9At col d).piCount = d.piCount := rfl

theorem keyCanonical9At_tables (col : KeyColMap) (d : EffectVmDescriptor2) :
    (keyCanonical9At col d).tables = d.tables := rfl

theorem keyCanonical9At_hashSites (col : KeyColMap) (d : EffectVmDescriptor2) :
    (keyCanonical9At col d).hashSites = d.hashSites := rfl

theorem keyCanonical9At_ranges (col : KeyColMap) (d : EffectVmDescriptor2) :
    (keyCanonical9At col d).ranges = d.ranges := rfl

theorem keyCanonical9At_constraints (col : KeyColMap) (d : EffectVmDescriptor2) :
    (keyCanonical9At col d).constraints = d.constraints ++ keyCanon9ConstraintsAt col := rfl

/-- Every emitted constraint is a `lookup` — no gate, so no last-row exemption anywhere in this
wrap, and no log moves. -/
theorem keyCanon9_all_lookups (col : KeyColMap) :
    ∀ c ∈ keyCanon9ConstraintsAt col, ∃ l, c = .lookup l := by
  intro c hc
  simp only [keyCanon9ConstraintsAt, List.mem_flatMap] at hc
  obtain ⟨blk, -, hc⟩ := hc
  rcases List.mem_append.mp hc with h | h
  · obtain ⟨x, -, rfl⟩ := List.mem_map.mp h
    exact ⟨_, rfl⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    subst h
    exact ⟨_, rfl⟩

private theorem memFilter_nil (l : List VmConstraint2) (hl : ∀ c ∈ l, ∃ x, c = .lookup x) :
    l.filterMap (fun c => match c with | .memOp m => some m | _ => none) = [] := by
  induction l with
  | nil => rfl
  | cons c cs ih =>
    obtain ⟨x, rfl⟩ := hl c (by simp)
    simpa using ih (fun y hy => hl y (List.mem_cons_of_mem _ hy))

private theorem mapFilter_nil (l : List VmConstraint2) (hl : ∀ c ∈ l, ∃ x, c = .lookup x) :
    l.filterMap (fun c => match c with | .mapOp m => some m | _ => none) = [] := by
  induction l with
  | nil => rfl
  | cons c cs ih =>
    obtain ⟨x, rfl⟩ := hl c (by simp)
    simpa using ih (fun y hy => hl y (List.mem_cons_of_mem _ hy))

theorem memOpsOf_keyCanonical9At (col : KeyColMap) (d : EffectVmDescriptor2) :
    memOpsOf (keyCanonical9At col d) = memOpsOf d := by
  show (d.constraints ++ keyCanon9ConstraintsAt col).filterMap
      (fun c => match c with | .memOp m => some m | _ => none)
    = d.constraints.filterMap (fun c => match c with | .memOp m => some m | _ => none)
  rw [List.filterMap_append, memFilter_nil _ (keyCanon9_all_lookups col), List.append_nil]

theorem mapOpsOf_keyCanonical9At (col : KeyColMap) (d : EffectVmDescriptor2) :
    mapOpsOf (keyCanonical9At col d) = mapOpsOf d := by
  show (d.constraints ++ keyCanon9ConstraintsAt col).filterMap
      (fun c => match c with | .mapOp m => some m | _ => none)
    = d.constraints.filterMap (fun c => match c with | .mapOp m => some m | _ => none)
  rw [List.filterMap_append, mapFilter_nil _ (keyCanon9_all_lookups col), List.append_nil]

/-- **THE PEEL** — `Satisfied2 (keyCanonical9At col d) ⟹ Satisfied2 d`. The wrap only APPENDS
constraints and leaves every log alone, so every existing per-effect keystone lifts. -/
theorem satisfied2_of_keyCanonical9At (hash : List ℤ → ℤ) (col : KeyColMap)
    (d : EffectVmDescriptor2)
    {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
    (h : Satisfied2 hash (keyCanonical9At col d) minit mfin maddrs t) :
    Satisfied2 hash d minit mfin maddrs t := by
  have hmem : memLog (keyCanonical9At col d) t = memLog d t := by
    simp [memLog, memOpsOf_keyCanonical9At]
  have hmap : mapLog (keyCanonical9At col d) t = mapLog d t := by
    simp [mapLog, mapOpsOf_keyCanonical9At]
  exact
    { rowConstraints := fun i hi c hc => h.rowConstraints i hi c (by
        rw [keyCanonical9At_constraints]; exact List.mem_append_left _ hc)
    , rowHashes := h.rowHashes
    , rowRanges := h.rowRanges
    , memAddrsNodup := h.memAddrsNodup
    , memClosed := fun op hop => h.memClosed op (by rw [hmem]; exact hop)
    , memDisciplined := by rw [← hmem]; exact h.memDisciplined
    , memBalanced := by rw [← hmem]; exact h.memBalanced
    , memTableFaithful := by rw [← hmem]; exact h.memTableFaithful
    , mapTableFaithful := by rw [← hmap]; exact h.mapTableFaithful }

/-! ## §3 — THE FORCING: from `Satisfied2` to `CanonicalKey9`. -/

/-- Every emitted lookup of block `blk` is a constraint of the wrapped member. -/
theorem blk_mem (col : KeyColMap) (d : EffectVmDescriptor2) (blk : Fin 2)
    {c : VmConstraint2} (hc : c ∈ keyLookupsAt col blk) :
    c ∈ (keyCanonical9At col d).constraints :=
  List.mem_append_right _ (List.mem_flatMap.mpr ⟨blk, List.mem_finRange _, hc⟩)

/-- A range lookup of the emit BINDS: its column lies in `[0, 2^bits)` on EVERY row. No non-last-row
side condition — that exemption belongs to gates, and this wrap emits none. -/
theorem lookup_forces {hash : List ℤ → ℤ} {col : KeyColMap} {d : EffectVmDescriptor2}
    {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
    (hsat : Satisfied2 hash (keyCanonical9At col d) minit mfin maddrs t)
    {bits c : Nat} (hrt : t.tf (rangeTidW bits) = rangeRows bits)
    {i : Nat} (hi : i < t.rows.length) {blk : Fin 2}
    (hc : rangeLk bits c ∈ keyLookupsAt col blk) :
    0 ≤ (envAt t i).loc c ∧ (envAt t i).loc c < (2 : ℤ) ^ bits := by
  have h := hsat.rowConstraints i hi _ (blk_mem col d blk hc)
  have h' : [(envAt t i).loc c] ∈ t.tf (rangeTidW bits) := by
    simpa [VmConstraint2.holdsAt, Dregg2.Circuit.DescriptorIR2.Lookup.holdsAt, rangeLk,
      EmittedExpr.eval] using h
  rw [hrt] at h'
  exact (range_row_mem_iff _ bits).mp h'

/-- Both bounds on all nine columns of an ARBITRARY column map.

⚑ **THIS SAYS NOTHING ABOUT THE OWNER KEY, AND ITS NAME MUST NOT.** It is the column-agnostic core:
hand it any nine columns and it forces those nine. Everything that names the owner key is the
instance at `deployedKeyCols` below. The `0 ≤` half is not decoration — the `.toNat` in the
`CanonicalKey9` half reads a negative column as `0`, so without it the forcing would be satisfiable
by a column carrying a negative value. -/
theorem lane_bounds_atCols {hash : List ℤ → ℤ} {col : KeyColMap} {d : EffectVmDescriptor2}
    {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
    (hsat : Satisfied2 hash (keyCanonical9At col d) minit mfin maddrs t)
    (h29 : t.tf (rangeTidW KEY_LANE_BITS) = rangeRows KEY_LANE_BITS)
    (h24 : t.tf (rangeTidW KEY_TOP_BITS) = rangeRows KEY_TOP_BITS)
    {i : Nat} (hi : i < t.rows.length) (blk : Fin 2) :
    (∀ l : Fin 9, 0 ≤ (envAt t i).loc (col blk l))
      ∧ CanonicalKey9 (fun l => ((envAt t i).loc (col blk l)).toNat) := by
  have hlane : ∀ l : Fin 9, l.1 < 8 →
      0 ≤ (envAt t i).loc (col blk l) ∧ (envAt t i).loc (col blk l) < (2 : ℤ) ^ 29 := by
    intro l hl
    refine lookup_forces hsat h29 hi (blk := blk) ?_
    exact List.mem_append_left _
      (List.mem_map_of_mem (a := (⟨l.1, hl⟩ : Fin 8)) (List.mem_finRange _))
  have htop : 0 ≤ (envAt t i).loc (col blk 8)
      ∧ (envAt t i).loc (col blk 8) < (2 : ℤ) ^ 24 :=
    lookup_forces hsat h24 hi (blk := blk) (List.mem_append_right _ (by simp))
  have hsplit : ∀ l : Fin 9, l.1 < 8 ∨ l = 8 := by
    intro l
    rcases Nat.lt_or_ge l.1 8 with h | h
    · exact Or.inl h
    · exact Or.inr (by apply Fin.ext; have := l.isLt; omega)
  refine ⟨fun l => ?_, ?_, ?_⟩
  · rcases hsplit l with h | h
    · exact (hlane l h).1
    · subst h; exact htop.1
  · intro l hl
    have hj := hlane l hl
    simp only [Dregg2.Circuit.KeyLanes9.K]
    omega
  · simp only [Dregg2.Circuit.KeyLanes9.TopLaneRanged, Dregg2.Circuit.KeyLanes9.KTOP]
    have := htop
    norm_num at this
    omega

/-- **THE FORCING, AT THE DEPLOYED COLUMNS.** On ANY row of a `Satisfied2` witness of the
key-canonicity-welded member, against the two faithful width-tagged range tables, the nonet
committed at `B_PUBKEY_OCTET` of EVERY rotated block satisfies `KeyLanes9.CanonicalKey9` — which
`canonicalKey9_iff_in_image` proves is EXACTLY the nine-lane encoder's image. So the OWNER-KEY
columns are the lanes of SOME 32-byte key.

⚑ Note the two hypotheses that are ABSENT and were present in the fields analogue: no
non-last-row condition (no gate is emitted) and no canonical-column envelope (all nine lanes are
covered by a lookup, so both bounds are constraint-derived). -/
theorem keyCanon9_forces_canonical {hash : List ℤ → ℤ} {w lane8Off : Nat}
    {d : EffectVmDescriptor2}
    {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
    (hsat : Satisfied2 hash (keyCanonical9At (deployedKeyCols w lane8Off) d) minit mfin maddrs t)
    (h29 : t.tf (rangeTidW KEY_LANE_BITS) = rangeRows KEY_LANE_BITS)
    (h24 : t.tf (rangeTidW KEY_TOP_BITS) = rangeRows KEY_TOP_BITS)
    {i : Nat} (hi : i < t.rows.length) (blk : Fin 2) :
    CanonicalKey9 (fun l => ((envAt t i).loc (deployedKeyCols w lane8Off blk l)).toNat) :=
  (lane_bounds_atCols hsat h29 h24 hi blk).2

/-- The capstone's predicate, said the two equivalent ways: as nine ℤ-equalities at the columns the
wrap constrains, and as "the eight absorbed owner-key pre-limbs plus the ninth lane". The proof of
the capstone runs through the first; the STATEMENT is the second, which is the one that mentions
`B_PUBKEY_OCTET` and `preLimbsAt`. -/
private theorem keySpec_iff (w lane8Off : Nat) (a : Assignment) (blk : Fin 2) (c : Bytes32) :
    ((∀ l : Fin 9, l.1 < 8 → ((keyToLanes9 c l : Nat) : ℤ)
        = (preLimbsAt (w + blk.1 * B_SPAN) a).getD (B_PUBKEY_OCTET + l.1) 0)
      ∧ ((keyToLanes9 c 8 : Nat) : ℤ) = a (w + blk.1 * B_SPAN + lane8Off))
    ↔ (∀ l : Fin 9, ((keyToLanes9 c l : Nat) : ℤ) = a (deployedKeyCols w lane8Off blk l)) := by
  constructor
  · rintro ⟨h8, htop⟩ l
    rcases Nat.lt_or_ge l.1 8 with hl | hl
    · rw [h8 l hl, deployedKeyCols_octet_is_absorbed w lane8Off a blk hl]
    · have hl8 : l = 8 := by apply Fin.ext; have := l.isLt; omega
      subst hl8
      rw [htop, deployedKeyCols_lane8_col]
  · intro h
    refine ⟨fun l hl => ?_, ?_⟩
    · rw [h l, deployedKeyCols_octet_is_absorbed w lane8Off a blk hl]
    · rw [h 8, deployedKeyCols_lane8_col]

/-- **THE CAPSTONE.** Under the emitted envelope, the eight ABSORBED owner-key pre-limbs
`B_PUBKEY_OCTET .. +8` of block `blk` — the ones `wireCommitR` folds into `state_commit` — together
with the ninth lane are the nine-lane encoding of EXACTLY ONE 32-byte key. That is the sentence
`keyToLanes9_injective` alone could not reach (it quantifies over VALUES; a prover writes COLUMNS)
and the sentence the deployed eight-lane octet cannot reach at all
(`KeyLanes9.eight_lane_canonicity_is_not_a_repair`).

⚑ Two things this statement does that its predecessor did not. It names the columns instead of
quantifying over them, so it is a claim about the owner key rather than about whatever nine columns
a caller supplies. And it equates ℤ to ℤ rather than through `.toNat`, so a negative committed value
cannot satisfy it by collapsing to `0`. -/
theorem keyCanon9_determines_the_owner_key {hash : List ℤ → ℤ} {w lane8Off : Nat}
    {d : EffectVmDescriptor2}
    {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
    (hsat : Satisfied2 hash (keyCanonical9At (deployedKeyCols w lane8Off) d) minit mfin maddrs t)
    (h29 : t.tf (rangeTidW KEY_LANE_BITS) = rangeRows KEY_LANE_BITS)
    (h24 : t.tf (rangeTidW KEY_TOP_BITS) = rangeRows KEY_TOP_BITS)
    {i : Nat} (hi : i < t.rows.length) (blk : Fin 2) :
    ∃! b : Bytes32,
      (∀ l : Fin 9, l.1 < 8 → ((keyToLanes9 b l : Nat) : ℤ)
          = (preLimbsAt (w + blk.1 * B_SPAN) (envAt t i).loc).getD (B_PUBKEY_OCTET + l.1) 0)
      ∧ ((keyToLanes9 b 8 : Nat) : ℤ) = (envAt t i).loc (w + blk.1 * B_SPAN + lane8Off) := by
  obtain ⟨hnn, hcanon⟩ := lane_bounds_atCols hsat h29 h24 hi blk
  obtain ⟨b, hb⟩ := (canonicalKey9_iff_in_image _).mp hcanon
  have hlane : ∀ l : Fin 9,
      ((keyToLanes9 b l : Nat) : ℤ) = (envAt t i).loc (deployedKeyCols w lane8Off blk l) := by
    intro l
    rw [show keyToLanes9 b l = ((envAt t i).loc (deployedKeyCols w lane8Off blk l)).toNat from
      congrFun hb l]
    exact Int.toNat_of_nonneg (hnn l)
  refine ⟨b, (keySpec_iff w lane8Off _ blk b).mpr hlane, ?_⟩
  intro b' hb'
  apply keyToLanes9_injective
  funext l
  have hz : ((keyToLanes9 b' l : Nat) : ℤ) = ((keyToLanes9 b l : Nat) : ℤ) := by
    rw [(keySpec_iff w lane8Off _ blk b').mp hb' l, hlane l]
  exact_mod_cast hz

/-! ## §4 — ⚑ THE EXHIBIT, UNSAT ON THE EMITTED MEMBER. -/

/-- **THE NAIVE WRAP ACCEPTS IT AND THE DECODE IS A FORGERY.** Three facts about one vector:
(a) every lane is below the LANE width, so nine uniform `< 2^29` lookups — the reading of
"range-check the lanes" that does not do the arithmetic — admit it; (b) it decodes byte-for-byte to
the all-zero key, which is what the honest all-zero nonet decodes to, so it is a genuine
misdecode and not merely an odd vector; (c) the emitted NARROW leg refuses it. Leg 2 is the whole
difference between (a) and (c). -/
theorem the_forged_nonet_passes_the_naive_wrap_and_is_unsat_here :
    (∀ l : Fin 9, forgedKeyNonet l < 2 ^ KEY_LANE_BITS)
    ∧ keyLanes9ToBytes forgedKeyNonet = zeroKey
    ∧ ¬ (forgedKeyNonet 8 < 2 ^ KEY_TOP_BITS)
    ∧ ¬ CanonicalKey9 forgedKeyNonet := by
  refine ⟨?_, Dregg2.Circuit.KeyLanes9.the_forged_nonet_wraps_exactly_once.2.2, ?_, by decide⟩
  · intro l; simp only [KEY_LANE_BITS]; revert l; decide
  · simp only [KEY_TOP_BITS]; decide

/-- **⚑ UNSAT ON THE EMITTED MEMBER.** A witness whose owner-key lane 8 carries `2^24` — the vector
that passes a uniform nine-lane `< 2^29` check and still decodes to a different key's bytes — does
NOT satisfy the key-canonicity-welded member on ANY row. Not "is caught by a later check": the
narrow range table does not contain the row, so no assignment of anything else rescues it.

⚑ Note what this does NOT assume: nothing about lanes 0..7, no producer honesty, no row position.
Lane 8 alone. -/
theorem keyCanon9_rejects_the_forged_nonet {hash : List ℤ → ℤ} {w lane8Off : Nat}
    {d : EffectVmDescriptor2}
    {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
    (h24 : t.tf (rangeTidW KEY_TOP_BITS) = rangeRows KEY_TOP_BITS)
    {i : Nat} (hi : i < t.rows.length) (blk : Fin 2)
    (hforged : (envAt t i).loc (w + blk.1 * B_SPAN + lane8Off) = 16777216) :
    ¬ Satisfied2 hash (keyCanonical9At (deployedKeyCols w lane8Off) d) minit mfin maddrs t := by
  intro hsat
  have htop : 0 ≤ (envAt t i).loc (deployedKeyCols w lane8Off blk 8)
      ∧ (envAt t i).loc (deployedKeyCols w lane8Off blk 8) < (2 : ℤ) ^ KEY_TOP_BITS :=
    lookup_forces hsat h24 hi (blk := blk) (List.mem_append_right _ (by simp))
  rw [deployedKeyCols_lane8_col, hforged] at htop
  simp only [KEY_TOP_BITS] at htop
  norm_num at htop

/-- The exhibit's lane 8 really is the top-lane ceiling, one above the largest admissible value. -/
theorem forged_lane8_is_the_ceiling :
    forgedKeyNonet 8 = 16777216 ∧ (16777216 : Nat) = 2 ^ KEY_TOP_BITS := by
  refine ⟨rfl, by norm_num [KEY_TOP_BITS]⟩

#assert_axioms keyCanon9_all_lookups
#assert_axioms satisfied2_of_keyCanonical9At
#assert_axioms blk_mem
#assert_axioms lookup_forces
#assert_axioms lane_bounds_atCols
#assert_axioms keyCanon9_forces_canonical
#assert_axioms keyCanon9_determines_the_owner_key
#assert_axioms the_forged_nonet_passes_the_naive_wrap_and_is_unsat_here
#assert_axioms keyCanon9_rejects_the_forged_nonet
#assert_axioms forged_lane8_is_the_ceiling

end Dregg2.Circuit.Emit.KeyCanonicity9Emit
