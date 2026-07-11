/-
# Dregg2.Deos.InAirAuthorityDigestGadget — the GENTIAN KEYSTONE, hypotheses DISCHARGED.

The first GENTIAN rung (`InAirAuthorityDigestSelector.lean`) proved `gentian_selector_forced`:
the capacity selector is forced ON for a committed declaration requiring the escrow tag — but GIVEN
two named-MODELED hypotheses standing for the recompute/decode GADGET faithfulness:

  * `hrecompute : witDigestCol = authDigest witnessed`  (the in-AIR `hash_bytes` recompute output),
  * `hdecode    : floorCol = escrowBit (requiredTags witnessed)`  (the in-AIR required-tag decode).

This module REALIZES the recommended Option B (`IN-AIR-AUTHORITY-DIGEST-GADGET.md` §4) and DISCHARGES
both as PROVEN gates, so the selector-forcing holds under NO off-band assumption — only the two
irreducible CR floors (the felt-domain hash collision-resistance + the chip-table faithfulness, the
SAME shape as the deployed `Poseidon2WideCR`/`ChipTableSound` floors — never an axiom, never a
verifier-discipline `hverifier`).

## Option B realized

The committed `B_AUTHORITY_DIGEST` limb (`gentianAuthDigestCol`, wide-bound by
`gentian_auth_digest_absorbed`) is read, under Option B, as the FELT-DOMAIN digest of the cell's
required-tag floor: `hash committedFloor` (`hash_many` over the decoded required-tag felts — the way
`perms_digest`/`vk_digest` already ride rotated limbs). The gadget adds, over a fixed-arity (here 2,
≤ `CHIP_RATE`) witnessed floor `[F0, F1]`:

  * **recompute (4a) — DISCHARGED to a chip lookup.** `gentianRecomputeLookup` is a poseidon2 chip
    `Lookup` whose digest column is `GENTIAN_WIT_DIGEST_COL` and whose inputs are the witnessed floor
    columns. Against the SOUND chip table (`ChipTableSound`, the deployed chip faithfulness), the
    existing lever `DescriptorIR2.chip_lookup_sound` forces `witDigestCol = hash [F0, F1]` — exactly
    `hrecompute`, now a proven consequence of a real `VmConstraint`, not an assumption.
  * **decode (4b) — DISCHARGED to arithmetic gates.** The per-slot is-zero gadget (`b_k = isZero(F_k − 17)`,
    forced by a defining gate `b_k + (F_k − 17)·inv_k − 1 == 0` and a forcing gate `(F_k − 17)·b_k == 0`,
    sound over the integral domain ℤ) plus the OR-fold `floorCol = b0 + b1 − b0·b1` forces
    `floorCol = escrowBit [F0, F1]` — exactly `hdecode`, now proven arithmetic, NO crypto floor.

Composed (`gentian_selector_forced_discharged`): the recompute-bind gate ties the chip output to the
committed limb (`hash [F0, F1] = hash committedFloor`); the felt-domain CR floor `FloorDigestBinds`
(equal digests ⟹ equal floors — the analog of `ConstraintBinding.DeclCommitBinds`) forces
`[F0, F1] = committedFloor`; so the committed declaration's escrow requirement transfers to the
witnessed floor, the decode lights `floorCol = 1`, and the selector-force gate forces `sel = 1` — with
NO `hrecompute`/`hdecode`/`hverifier`. The four sealed-escrow conjuncts then bite
(`gentian_settle_forced_discharged`).

## STAGED — built BESIDE the deployed, NOT flipped

The gadget adds a chip lookup + arithmetic gates to the WIDE welded descriptor; it is a flag-day VK
bump (a new digest interpretation of the committed limb + new columns) — STAGED, NOT emitted into a
committed VK, NOT routed. The deployed descriptors / VK are byte-identical; the drift gate is green.
Rust shadow: `circuit/src/effect_vm/authority_digest_weld.rs` (the decode/recompute gates + producer).

## Tag-agnostic reuse

`isZero_from_gates` + the decode/OR-fold are parametric in the matched tag, and
`gentian_selector_forced_discharged` is parametric in the committed floor; tags 18 (discharge) / 19
(vault) / Custom / temporal reuse the coverage→selector half verbatim once their satisfaction gates
land (`IN-AIR-AUTHORITY-DIGEST-GADGET.md` §7).

## Axiom hygiene

`#assert_all_clean` at the close. The named hypotheses are the two CR floors (`ChipTableSound`,
`FloorDigestBinds`) and the wide-commit binding `hcommitLimb` — never an axiom; no core edit. The
forcing reduces through the STABLE `Satisfied2.rowConstraints` interface and the deployed
`chip_lookup_sound` lever.
-/
import Dregg2.Deos.InAirAuthorityDigestSelector

namespace Dregg2.Deos.InAirAuthorityDigestGadget

open Dregg2.Circuit.DescriptorIR2
open Dregg2.Circuit.Emit.EffectVmEmit
open Dregg2.Exec.CircuitEmit (EmittedExpr)
open Dregg2.Deos.SealedEscrow (stEmpty stDeposited stConsumed)
open Dregg2.Deos.ConstraintBinding (Tag tagSettleEscrow)
open Dregg2.Deos.SettleEscrowSatDescriptor
  (ESCROW_SEL_COL beforeFieldCol afterFieldCol settleEscrowSatGate settleEscrowSatGates)
open Dregg2.Deos.SettleEscrowSatWideDescriptor (settleGateWide_mem)
open Dregg2.Deos.InAirAuthorityDigestSelector
  (GENTIAN_WIT_DIGEST_COL GENTIAN_FLOOR_ESCROW_COL gentianAuthDigestCol gentianGates
   gentianSelectorDescriptor gentianRecomputeBindGate gentianSelectorForceGate
   weldedGate_mem_gentian)
open Dregg2.Circuit.Emit.EffectVmEmitTransfer (pPrimeInt gate_modEq_iff)

set_option autoImplicit false

/-- Field-faithful lift: two CANONICAL (`0 ≤ · < p`) integers congruent mod `p` are EQUAL. -/
private theorem canonEq {a b : ℤ} (h : a ≡ b [ZMOD 2013265921])
    (ha0 : 0 ≤ a) (hap : a < 2013265921) (hb0 : 0 ≤ b) (hbp : b < 2013265921) : a = b := by
  unfold Int.ModEq at h
  rwa [Int.emod_eq_of_lt ha0 hap, Int.emod_eq_of_lt hb0 hbp] at h

/-! ## §1 — the OPTION-B floor representation columns (fixed-arity = 2 ≤ CHIP_RATE).

The witnessed required-tag floor rides two free PARAM columns; the per-slot is-zero gadget rides a
boolean column + an inverse-witness column; the chip lookup squeezes 7 lane columns. (Arity 2 is the
representative fixed arity; the chip lookup is fixed-arity ≤ `CHIP_RATE = 16`, so generalizing the
slot count is the same gadget repeated — the per-slot `isZero_from_gates` is reused verbatim.) -/

/-- Witnessed floor slot 0 (`prmCol 5`). -/
def FLOOR0_COL : Nat := prmCol 5
/-- Witnessed floor slot 1 (`prmCol 6`). -/
def FLOOR1_COL : Nat := prmCol 6
/-- is-zero boolean for slot 0 (`prmCol 7`). -/
def B0_COL : Nat := prmCol 7
/-- is-zero boolean for slot 1 (`prmCol 8`). -/
def B1_COL : Nat := prmCol 8
/-- inverse witness for slot 0 (`prmCol 9`). -/
def INV0_COL : Nat := prmCol 9
/-- inverse witness for slot 1 (`prmCol 10`). -/
def INV1_COL : Nat := prmCol 10

/-- The witnessed floor input columns (the chip-lookup inputs). -/
def floorCols : List Nat := [FLOOR0_COL, FLOOR1_COL]

/-- The 7 exposed permutation lane columns (`CHIP_OUT_LANES - 1`), `prmCol 11 .. prmCol 17`. -/
def laneCols : List Nat := (List.range 7).map (fun j => prmCol (11 + j))

/-- The escrow tag, as a felt. -/
def tagEscrowZ : ℤ := (tagSettleEscrow : ℤ)

/-- The felt-domain escrow decode of a floor (the ℤ analog of `escrowBit`). -/
def escrowBitZ (floor : List ℤ) : ℤ := if tagEscrowZ ∈ floor then 1 else 0

/-! ## §2 — the CR floor (Option B's irreducible carrier). -/

/-- **The felt-domain floor-digest binding floor.** Equal floor digests ⟹ equal floors — the
collision-resistance of the `hash_many` Option-B floor digest. The felt-level analog of
`ConstraintBinding.DeclCommitBinds` / `Poseidon2WideCR`; stated as a named hypothesis, never an
axiom. -/
def FloorDigestBinds (hash : List ℤ → ℤ) : Prop :=
  ∀ l l' : List ℤ, hash l = hash l' → l = l'

/-! ## §3 — the DECODE gates (the in-AIR required-tag decode, discharging `hdecode`). -/

/-- (def_k) **is-zero defining gate**: `b_k + (F_k − 17)·inv_k − 1 == 0`, i.e. `b_k = 1 − (F_k−17)·inv_k`. -/
def isZeroDefGate (floorCol boolCol invCol : Nat) : VmConstraint2 :=
  .base (.gate (.add (.add (.var boolCol)
    (.mul (.add (.var floorCol) (.const (-tagEscrowZ))) (.var invCol))) (.const (-1))))

/-- (force_k) **is-zero forcing gate**: `(F_k − 17)·b_k == 0`. Over ℤ this forces `b_k = 0` when
`F_k ≠ 17`; the defining gate forces `b_k = 1` when `F_k = 17`. -/
def isZeroForceGate (floorCol boolCol : Nat) : VmConstraint2 :=
  .base (.gate (.mul (.add (.var floorCol) (.const (-tagEscrowZ))) (.var boolCol)))

/-- (or) **OR-fold gate**: `floorCol − (b0 + b1 − b0·b1) == 0`. The boolean OR of the two slot bits. -/
def decodeOrGate : VmConstraint2 :=
  .base (.gate (.add (.var GENTIAN_FLOOR_ESCROW_COL)
    (.mul (.const (-1)) (.add (.add (.var B0_COL) (.var B1_COL))
      (.mul (.const (-1)) (.mul (.var B0_COL) (.var B1_COL)))))))

/-- The full decode-gadget gate block. -/
def decodeGates : List VmConstraint2 :=
  [ isZeroDefGate FLOOR0_COL B0_COL INV0_COL,
    isZeroForceGate FLOOR0_COL B0_COL,
    isZeroDefGate FLOOR1_COL B1_COL INV1_COL,
    isZeroForceGate FLOOR1_COL B1_COL,
    decodeOrGate ]

/-! ## §4 — the RECOMPUTE lookup (the felt-domain chip recompute, discharging `hrecompute`). -/

/-- **The recompute chip lookup.** A poseidon2 chip lookup whose digest column is
`GENTIAN_WIT_DIGEST_COL` and whose inputs are the witnessed floor columns; against `ChipTableSound`
the lever `chip_lookup_sound` forces `witDigestCol = hash [F0, F1]`. -/
def gentianRecomputeLookup : VmConstraint2 :=
  .lookup ⟨.poseidon2, chipLookupTuple (floorCols.map .var) GENTIAN_WIT_DIGEST_COL laneCols⟩

/-! ## §5 — THE GADGET DESCRIPTOR (the wide welded descriptor + the GENTIAN selector gates + the
realized recompute lookup + decode gates). -/

/-- **`gentianGadgetDescriptor`** — the staged GENTIAN selector descriptor
(`gentianSelectorDescriptor`, itself the WIDE welded descriptor + the three GENTIAN gates) PLUS the
realized recompute chip lookup PLUS the in-AIR decode gadget. This is the Option-B realization whose
satisfaction discharges `hrecompute`/`hdecode`. STAGED — nothing routes through it; the deployed VK is
byte-identical. -/
def gentianGadgetDescriptor (legA legB : Nat) : EffectVmDescriptor2 :=
  let base := gentianSelectorDescriptor legA legB
  { base with
    name        := "dregg-effectvm-settle-escrow-gentian-gadget-v1-rot24-v3-wide-staged"
    constraints := base.constraints ++ (gentianRecomputeLookup :: decodeGates) }

/-! ## §6 — gate membership in the gadget descriptor. -/

/-- A GENTIAN selector gate (recompute-bind / selector-force) is still a member. -/
theorem gentianGate_mem_gadget (legA legB : Nat) (g : VmConstraint2) (hg : g ∈ gentianGates) :
    g ∈ (gentianGadgetDescriptor legA legB).constraints := by
  unfold gentianGadgetDescriptor
  simp only [List.mem_append]
  exact Or.inl (Dregg2.Deos.InAirAuthorityDigestSelector.gentianGate_mem legA legB g hg)

/-- A WIDE welded satisfaction gate is still a member. -/
theorem weldedGate_mem_gadget (legA legB : Nat) (g : VmConstraint2)
    (hg : g ∈ settleEscrowSatGates ESCROW_SEL_COL legA legB) :
    g ∈ (gentianGadgetDescriptor legA legB).constraints := by
  unfold gentianGadgetDescriptor
  simp only [List.mem_append]
  exact Or.inl (weldedGate_mem_gentian legA legB g hg)

/-- A decode gate is a member. -/
theorem decodeGate_mem_gadget (legA legB : Nat) (g : VmConstraint2) (hg : g ∈ decodeGates) :
    g ∈ (gentianGadgetDescriptor legA legB).constraints := by
  unfold gentianGadgetDescriptor
  simp only [List.mem_append, List.mem_cons]
  exact Or.inr (Or.inr hg)

/-- The recompute lookup is a member. -/
theorem recomputeLookup_mem_gadget (legA legB : Nat) :
    gentianRecomputeLookup ∈ (gentianGadgetDescriptor legA legB).constraints := by
  unfold gentianGadgetDescriptor
  exact List.mem_append.mpr (Or.inr (List.mem_cons_self))

/-! ## §7 — the generic gate-forcing helper. -/

/-- A gadget-descriptor gate's body vanishes on a satisfying NON-LAST row. -/
theorem gadget_gate_holds (hash : List ℤ → ℤ) (legA legB : Nat)
    {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
    (hsat : Satisfied2 hash (gentianGadgetDescriptor legA legB) minit mfin maddrs t)
    (i : Nat) (hi : i < t.rows.length) (hnl : (i + 1 == t.rows.length) = false)
    (g : VmConstraint2) (hg : g ∈ (gentianGadgetDescriptor legA legB).constraints)
    (body : EmittedExpr) (hbody : g = .base (.gate body)) :
    body.eval (envAt t i).loc ≡ 0 [ZMOD 2013265921] := by
  have hrow := hsat.rowConstraints i hi g hg
  rw [hbody] at hrow
  simpa [VmConstraint2.holdsAt, VmConstraint.holdsVm, hnl] using hrow

/-! ## §8 — DISCHARGE of `hrecompute` (the chip-lookup recompute + recompute-bind). -/

/-- The recompute chip lookup holds on a satisfying row (its tuple is a row of the chip table). -/
theorem recompute_lookup_holds (hash : List ℤ → ℤ) (legA legB : Nat)
    {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
    (hsat : Satisfied2 hash (gentianGadgetDescriptor legA legB) minit mfin maddrs t)
    (i : Nat) (hi : i < t.rows.length) :
    (chipLookupTuple (floorCols.map .var) GENTIAN_WIT_DIGEST_COL laneCols).map
        (·.eval (envAt t i).loc) ∈ t.tf .poseidon2 := by
  have hrow := hsat.rowConstraints i hi gentianRecomputeLookup (recomputeLookup_mem_gadget legA legB)
  simpa [VmConstraint2.holdsAt, Lookup.holdsAt, gentianRecomputeLookup] using hrow

/-- **`hrecompute` DISCHARGED.** Against the SOUND chip table, the witnessed-digest column carries the
felt-domain digest of the witnessed floor columns: `witDigestCol = hash [F0, F1]`. A proven
consequence of the recompute lookup, NOT an assumption. -/
theorem recompute_discharged (hash : List ℤ → ℤ) (legA legB : Nat)
    {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
    (hsat : Satisfied2 hash (gentianGadgetDescriptor legA legB) minit mfin maddrs t)
    (hChip : ChipTableSound hash (t.tf .poseidon2))
    (i : Nat) (hi : i < t.rows.length) :
    (envAt t i).loc GENTIAN_WIT_DIGEST_COL
      = hash [(envAt t i).loc FLOOR0_COL, (envAt t i).loc FLOOR1_COL] := by
  have hmem := recompute_lookup_holds hash legA legB hsat i hi
  have hlen : (floorCols.map (EmittedExpr.var)).length ≤ CHIP_RATE := by
    simp only [floorCols, List.length_map, List.length_cons, List.length_nil, CHIP_RATE]; omega
  have h := chip_lookup_sound hash (t.tf .poseidon2) hChip (envAt t i).loc
    (floorCols.map .var) GENTIAN_WIT_DIGEST_COL laneCols hlen hmem
  simpa [floorCols, EmittedExpr.eval] using h

/-! ## §9 — DISCHARGE of `hdecode` (the in-AIR is-zero + OR-fold decode). -/

/-- **The per-slot is-zero gadget is sound** (over the integral domain ℤ): the defining gate +
forcing gate force `b = 1` iff the slot felt is the escrow tag. -/
theorem isZero_from_gates {d b inv : ℤ}
    (hdef : b + d * inv + (-1) ≡ 0 [ZMOD 2013265921])
    (hforce : d * b ≡ 0 [ZMOD 2013265921])
    (hbc : 0 ≤ b ∧ b < 2013265921)
    (hdlo : -2013265921 < d) (hdhi : d < 2013265921) :
    b = if d = 0 then 1 else 0 := by
  by_cases hd : d = 0
  · subst hd
    rw [if_pos rfl]
    -- `b + 0·inv − 1 ≡ 0 [ZMOD p]` collapses to `b ≡ 1`; `b` canonical ⟹ `b = 1`.
    simp only [zero_mul, add_zero] at hdef
    exact canonEq ((gate_modEq_iff (by ring)).mp hdef) hbc.1 hbc.2 (by norm_num) (by norm_num)
  · rw [if_neg hd]
    -- `d` is nonzero and bounded in `(−p, p)`, so `p ∤ d`; `p ∣ d·b` and `p` prime ⟹ `p ∣ b` ⟹
    -- `b ≡ 0`; `b` canonical ⟹ `b = 0`.
    have hdd : ¬ (2013265921 : ℤ) ∣ d := by rintro ⟨k, hk⟩; omega
    rw [Int.modEq_zero_iff_dvd] at hforce
    have hb0 : (2013265921 : ℤ) ∣ b := (pPrimeInt.dvd_mul.mp hforce).resolve_left hdd
    exact canonEq ((Int.modEq_zero_iff_dvd).mpr hb0) hbc.1 hbc.2 (by norm_num) (by norm_num)

/-- **`hdecode` DISCHARGED.** Under the decode gates, the floor column equals the felt-domain escrow
decode of the witnessed floor: `floorCol = escrowBitZ [F0, F1]`. Proven arithmetic — NO crypto floor. -/
theorem decode_discharged (hash : List ℤ → ℤ) (legA legB : Nat)
    {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
    (hsat : Satisfied2 hash (gentianGadgetDescriptor legA legB) minit mfin maddrs t)
    (i : Nat) (hi : i < t.rows.length) (hnl : (i + 1 == t.rows.length) = false)
    (hcanon : ∀ c, 0 ≤ (envAt t i).loc c ∧ (envAt t i).loc c < 2013265921) :
    (envAt t i).loc GENTIAN_FLOOR_ESCROW_COL
      = escrowBitZ [(envAt t i).loc FLOOR0_COL, (envAt t i).loc FLOOR1_COL] := by
  have hdef0 := gadget_gate_holds hash legA legB hsat i hi hnl
    (isZeroDefGate FLOOR0_COL B0_COL INV0_COL)
    (decodeGate_mem_gadget legA legB _ (by simp [decodeGates]))
    _ rfl
  have hforce0 := gadget_gate_holds hash legA legB hsat i hi hnl
    (isZeroForceGate FLOOR0_COL B0_COL)
    (decodeGate_mem_gadget legA legB _ (by simp [decodeGates]))
    _ rfl
  have hdef1 := gadget_gate_holds hash legA legB hsat i hi hnl
    (isZeroDefGate FLOOR1_COL B1_COL INV1_COL)
    (decodeGate_mem_gadget legA legB _ (by simp [decodeGates]))
    _ rfl
  have hforce1 := gadget_gate_holds hash legA legB hsat i hi hnl
    (isZeroForceGate FLOOR1_COL B1_COL)
    (decodeGate_mem_gadget legA legB _ (by simp [decodeGates]))
    _ rfl
  have hor := gadget_gate_holds hash legA legB hsat i hi hnl
    decodeOrGate (decodeGate_mem_gadget legA legB _ (by simp [decodeGates])) _ rfl
  simp only [isZeroDefGate, isZeroForceGate, decodeOrGate, EmittedExpr.eval]
    at hdef0 hforce0 hdef1 hforce1 hor
  -- the two slot bits (the is-zero gadget is sound over the prime field, under canonicality).
  have htagB : (0 : ℤ) ≤ tagEscrowZ ∧ tagEscrowZ < 2013265921 := by decide
  have hb0 := isZero_from_gates hdef0 hforce0 (hcanon B0_COL)
    (by have h := hcanon FLOOR0_COL; omega) (by have h := hcanon FLOOR0_COL; omega)
  have hb1 := isZero_from_gates hdef1 hforce1 (hcanon B1_COL)
    (by have h := hcanon FLOOR1_COL; omega) (by have h := hcanon FLOOR1_COL; omega)
  have hb0r : (envAt t i).loc B0_COL = 0 ∨ (envAt t i).loc B0_COL = 1 := by rw [hb0]; split <;> simp
  have hb1r : (envAt t i).loc B1_COL = 0 ∨ (envAt t i).loc B1_COL = 1 := by rw [hb1]; split <;> simp
  -- the OR-fold gate is `floor − (b0 + b1 − b0·b1) ≡ 0 [ZMOD p]`; both sides are canonical (the RHS
  -- is a boolean OR of two bits), so it lifts to the exact ℤ equality.
  have hore : (envAt t i).loc GENTIAN_FLOOR_ESCROW_COL
      = (envAt t i).loc B0_COL + (envAt t i).loc B1_COL
        - (envAt t i).loc B0_COL * (envAt t i).loc B1_COL := by
    have hrhs : 0 ≤ (envAt t i).loc B0_COL + (envAt t i).loc B1_COL
          - (envAt t i).loc B0_COL * (envAt t i).loc B1_COL
        ∧ (envAt t i).loc B0_COL + (envAt t i).loc B1_COL
          - (envAt t i).loc B0_COL * (envAt t i).loc B1_COL < 2013265921 := by
      rcases hb0r with h | h <;> rcases hb1r with h' | h' <;> rw [h, h'] <;> norm_num
    exact canonEq ((gate_modEq_iff (by ring)).mp hor) (hcanon _).1 (hcanon _).2 hrhs.1 hrhs.2
  -- decode the OR over the two slots.
  unfold escrowBitZ
  simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false]
  rw [hore, hb0, hb1]
  by_cases h0 : (envAt t i).loc FLOOR0_COL + (-tagEscrowZ) = 0
  · rw [if_pos h0,
        if_pos (show tagEscrowZ = (envAt t i).loc FLOOR0_COL
                    ∨ tagEscrowZ = (envAt t i).loc FLOOR1_COL by omega)]
    by_cases h1 : (envAt t i).loc FLOOR1_COL + (-tagEscrowZ) = 0
    · rw [if_pos h1]; ring
    · rw [if_neg h1]; ring
  · rw [if_neg h0]
    by_cases h1 : (envAt t i).loc FLOOR1_COL + (-tagEscrowZ) = 0
    · rw [if_pos h1,
          if_pos (show tagEscrowZ = (envAt t i).loc FLOOR0_COL
                      ∨ tagEscrowZ = (envAt t i).loc FLOOR1_COL by omega)]; ring
    · rw [if_neg h1,
          if_neg (show ¬(tagEscrowZ = (envAt t i).loc FLOOR0_COL
                        ∨ tagEscrowZ = (envAt t i).loc FLOOR1_COL) by omega)]; ring

/-! ## §10 — THE DISCHARGED SELECTOR-FORCING KEYSTONE.

Composed: under ONLY the two CR floors (`ChipTableSound`, `FloorDigestBinds`) and the wide-commit
binding `hcommitLimb` — NO `hrecompute`/`hdecode`/`hverifier` — a committed declaration whose
Option-B floor digest requires the escrow tag FORCES the selector ON. -/

/-- **THE GENTIAN SELECTOR-FORCING KEYSTONE, hypotheses DISCHARGED.** A satisfying gadget proof on a
cell whose committed authority-digest limb is the felt-domain digest of a floor REQUIRING the escrow
tag has its capacity selector forced `1` — for a PURE light client, under only the chip-table
faithfulness + the felt-hash collision-resistance. The forger can dodge NEITHER by an alternate
witnessed floor (the recompute lookup + recompute-bind + CR floor force it equal to the committed
floor) NOR by `sel = 0` (the selector-force gate). -/
theorem gentian_selector_forced_discharged (hash : List ℤ → ℤ) (legA legB : Nat)
    {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
    (hsat : Satisfied2 hash (gentianGadgetDescriptor legA legB) minit mfin maddrs t)
    (hChip : ChipTableSound hash (t.tf .poseidon2))
    (hCR : FloorDigestBinds hash)
    (committedFloor : List ℤ)
    (hreq : tagEscrowZ ∈ committedFloor)
    (i : Nat) (hi : i < t.rows.length) (hnl : (i + 1 == t.rows.length) = false)
    (hcanon : ∀ c, 0 ≤ (envAt t i).loc c ∧ (envAt t i).loc c < 2013265921)
    (hcommitLimb : (envAt t i).loc gentianAuthDigestCol = hash committedFloor) :
    (envAt t i).loc ESCROW_SEL_COL = 1 := by
  -- DISCHARGE hrecompute: the chip lookup forces the witnessed-digest column to the felt-floor digest.
  have hwit := recompute_discharged hash legA legB hsat hChip i hi
  -- the recompute-bind gate ties the witnessed digest to the committed limb (field-faithfully).
  have hbind : (envAt t i).loc GENTIAN_WIT_DIGEST_COL = (envAt t i).loc gentianAuthDigestCol := by
    have h := gadget_gate_holds hash legA legB hsat i hi hnl
      (gentianRecomputeBindGate GENTIAN_WIT_DIGEST_COL gentianAuthDigestCol)
      (gentianGate_mem_gadget legA legB _ (by simp [gentianGates]))
      _ rfl
    simp only [gentianRecomputeBindGate, EmittedExpr.eval] at h
    exact canonEq ((gate_modEq_iff (by ring)).mp h) (hcanon _).1 (hcanon _).2 (hcanon _).1 (hcanon _).2
  -- ⟹ the witnessed floor digest equals the committed floor digest.
  have hdig : hash [(envAt t i).loc FLOOR0_COL, (envAt t i).loc FLOOR1_COL] = hash committedFloor := by
    rw [← hwit, hbind, hcommitLimb]
  -- CR ⟹ the witnessed floor IS the committed floor.
  have hfloor : [(envAt t i).loc FLOOR0_COL, (envAt t i).loc FLOOR1_COL] = committedFloor :=
    hCR _ _ hdig
  -- the committed floor requires escrow ⟹ the witnessed floor does ⟹ the decode lights the bit.
  have hwitreq : tagEscrowZ ∈ [(envAt t i).loc FLOOR0_COL, (envAt t i).loc FLOOR1_COL] := by
    rw [hfloor]; exact hreq
  -- DISCHARGE hdecode: the decode gates force floorCol = escrowBitZ floor = 1.
  have hdec := decode_discharged hash legA legB hsat i hi hnl hcanon
  have hfloorOne : (envAt t i).loc GENTIAN_FLOOR_ESCROW_COL = 1 := by
    rw [hdec]; unfold escrowBitZ; rw [if_pos hwitreq]
  -- the selector-force gate forces sel = 1 (field-faithfully, under selector canonicality).
  have hsel := gadget_gate_holds hash legA legB hsat i hi hnl
    (gentianSelectorForceGate GENTIAN_FLOOR_ESCROW_COL ESCROW_SEL_COL)
    (gentianGate_mem_gadget legA legB _ (by simp [gentianGates]))
    _ rfl
  simp only [gentianSelectorForceGate, EmittedExpr.eval, hfloorOne, one_mul] at hsel
  exact canonEq ((gate_modEq_iff (by ring)).mp hsel) (hcanon _).1 (hcanon _).2 (by norm_num) (by norm_num)

/-! ## §11 — THE DISCHARGED SETTLE-FORCING + the teeth. -/

/-- **THE GENTIAN DISCHARGE (pure light client), hypotheses DISCHARGED.** The four sealed-escrow
conjuncts are forced over the committed wide-bound field columns — driven by the IN-AIR selector
forcing, with NO off-band verifier discipline and NO `hrecompute`/`hdecode`. -/
theorem gentian_settle_forced_discharged (hash : List ℤ → ℤ) (legA legB : Nat)
    {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
    (hsat : Satisfied2 hash (gentianGadgetDescriptor legA legB) minit mfin maddrs t)
    (hChip : ChipTableSound hash (t.tf .poseidon2))
    (hCR : FloorDigestBinds hash)
    (committedFloor : List ℤ)
    (hreq : tagEscrowZ ∈ committedFloor)
    (i : Nat) (hi : i < t.rows.length) (hnl : (i + 1 == t.rows.length) = false)
    (hcanon : ∀ c, 0 ≤ (envAt t i).loc c ∧ (envAt t i).loc c < 2013265921)
    (hcommitLimb : (envAt t i).loc gentianAuthDigestCol = hash committedFloor) :
    (envAt t i).loc (beforeFieldCol legA) ≡ stDeposited [ZMOD 2013265921] ∧
    (envAt t i).loc (beforeFieldCol legB) ≡ stDeposited [ZMOD 2013265921] ∧
    (envAt t i).loc (afterFieldCol legA)  ≡ stConsumed [ZMOD 2013265921] ∧
    (envAt t i).loc (afterFieldCol legB)  ≡ stConsumed [ZMOD 2013265921] := by
  have hsel := gentian_selector_forced_discharged hash legA legB hsat hChip hCR committedFloor hreq
    i hi hnl hcanon hcommitLimb
  have force : ∀ (col : Nat) (val : ℤ),
      settleEscrowSatGate ESCROW_SEL_COL col val ∈ settleEscrowSatGates ESCROW_SEL_COL legA legB →
      (envAt t i).loc col ≡ val [ZMOD 2013265921] := by
    intro col val hmem
    have h0 := gadget_gate_holds hash legA legB hsat i hi hnl
      (settleEscrowSatGate ESCROW_SEL_COL col val) (weldedGate_mem_gadget legA legB _ hmem)
      (.mul (.var ESCROW_SEL_COL) (.add (.var col) (.const (-val)))) rfl
    simp only [EmittedExpr.eval, hsel, one_mul] at h0
    exact (gate_modEq_iff (by ring)).mp h0
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact force (beforeFieldCol legA) stDeposited (by simp [settleEscrowSatGates])
  · exact force (beforeFieldCol legB) stDeposited (by simp [settleEscrowSatGates])
  · exact force (afterFieldCol legA) stConsumed (by simp [settleEscrowSatGates])
  · exact force (afterFieldCol legB) stConsumed (by simp [settleEscrowSatGates])

/-- **THE NO-PARTIAL TOOTH (discharged).** A partial settle on a declared-escrow cell cannot satisfy
the gadget descriptor — no `hrecompute`/`hdecode` needed. -/
theorem gentian_partial_unsat_discharged (hash : List ℤ → ℤ) (legA legB : Nat)
    {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
    (hsat : Satisfied2 hash (gentianGadgetDescriptor legA legB) minit mfin maddrs t)
    (hChip : ChipTableSound hash (t.tf .poseidon2)) (hCR : FloorDigestBinds hash)
    (committedFloor : List ℤ) (hreq : tagEscrowZ ∈ committedFloor)
    (i : Nat) (hi : i < t.rows.length) (hnl : (i + 1 == t.rows.length) = false)
    (hcanon : ∀ c, 0 ≤ (envAt t i).loc c ∧ (envAt t i).loc c < 2013265921)
    (hcommitLimb : (envAt t i).loc gentianAuthDigestCol = hash committedFloor)
    (hpartial : (envAt t i).loc (afterFieldCol legB) = stDeposited) :
    False := by
  have h := (gentian_settle_forced_discharged hash legA legB hsat hChip hCR committedFloor hreq
    i hi hnl hcanon hcommitLimb).2.2.2
  rw [hpartial] at h
  simp only [stDeposited, stConsumed] at h
  exact absurd h (by decide)

/-- **THE NO-PHANTOM TOOTH (discharged).** A phantom settle on a declared-escrow cell cannot satisfy
the gadget descriptor. -/
theorem gentian_phantom_unsat_discharged (hash : List ℤ → ℤ) (legA legB : Nat)
    {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
    (hsat : Satisfied2 hash (gentianGadgetDescriptor legA legB) minit mfin maddrs t)
    (hChip : ChipTableSound hash (t.tf .poseidon2)) (hCR : FloorDigestBinds hash)
    (committedFloor : List ℤ) (hreq : tagEscrowZ ∈ committedFloor)
    (i : Nat) (hi : i < t.rows.length) (hnl : (i + 1 == t.rows.length) = false)
    (hcanon : ∀ c, 0 ≤ (envAt t i).loc c ∧ (envAt t i).loc c < 2013265921)
    (hcommitLimb : (envAt t i).loc gentianAuthDigestCol = hash committedFloor)
    (hphantom : (envAt t i).loc (beforeFieldCol legA) = stEmpty) :
    False := by
  have h := (gentian_settle_forced_discharged hash legA legB hsat hChip hCR committedFloor hreq
    i hi hnl hcanon hcommitLimb).1
  rw [hphantom] at h
  simp only [stEmpty, stDeposited] at h
  exact absurd h (by decide)

/-! ## §12 — NON-VACUITY TEETH (`#guard`): the decode + the recompute lookup are real and BITE. -/

section Witnesses

-- escrowBitZ both polarities.
#guard escrowBitZ [tagEscrowZ] == 1
#guard escrowBitZ [] == 0
#guard escrowBitZ [6, 19] == 0
#guard escrowBitZ [18, tagEscrowZ] == 1

-- The gadget descriptor extends the selector descriptor (63 PIs, no new PI — the discharge is
-- in-AIR, not a pin) and appends the recompute lookup + the five decode gates.
#guard (gentianGadgetDescriptor 0 1).piCount == 63
#guard decodeGates.length == 5
#guard floorCols.length == 2
#guard laneCols.length == 7

-- The columns are distinct (no aliasing).
#guard [FLOOR0_COL, FLOOR1_COL, B0_COL, B1_COL, INV0_COL, INV1_COL,
        GENTIAN_WIT_DIGEST_COL, GENTIAN_FLOOR_ESCROW_COL].dedup.length == 8

-- A concrete decode evaluation: F0 = 17 (escrow), F1 = 6, b0 = 1, b1 = 0, OR = 1.
private def mkLoc (f0 f1 b0 b1 fe : ℤ) : Nat → ℤ := fun c =>
  if c == FLOOR0_COL then f0 else if c == FLOOR1_COL then f1
  else if c == B0_COL then b0 else if c == B1_COL then b1
  else if c == GENTIAN_FLOOR_ESCROW_COL then fe else 0

private def gateVal (g : VmConstraint2) (loc : Nat → ℤ) : ℤ :=
  match g with
  | .base (.gate body) => body.eval loc
  | _ => 999

-- is-zero DEF for slot 0: F0 = 17 ⟹ d = 0 ⟹ b0 must be 1 (inv free = 0): gate vanishes.
#guard gateVal (isZeroDefGate FLOOR0_COL B0_COL INV0_COL) (mkLoc 17 6 1 0 1) == 0
-- ...and b0 = 0 with F0 = 17 makes the DEF gate bite (b0 = 1 is forced).
#guard gateVal (isZeroDefGate FLOOR0_COL B0_COL INV0_COL) (mkLoc 17 6 0 0 1) != 0
-- is-zero FORCE for slot 0: F0 = 6 (≠ escrow), b0 = 1 ⟹ d·b0 = (6-17)·1 ≠ 0 — bites.
#guard gateVal (isZeroForceGate FLOOR0_COL B0_COL) (mkLoc 6 6 1 0 0) != 0
-- ...F0 = 6, b0 = 0 ⟹ vanishes.
#guard gateVal (isZeroForceGate FLOOR0_COL B0_COL) (mkLoc 6 6 0 0 0) == 0
-- OR-fold: b0 = 1, b1 = 0 ⟹ floor = 1 vanishes; floor = 0 bites.
#guard gateVal decodeOrGate (mkLoc 17 6 1 0 1) == 0
#guard gateVal decodeOrGate (mkLoc 17 6 1 0 0) != 0
-- OR-fold both off: b0 = b1 = 0 ⟹ floor = 0 vanishes.
#guard gateVal decodeOrGate (mkLoc 6 6 0 0 0) == 0

end Witnesses

/-! ## §13 — Axiom hygiene. -/

#assert_all_clean [
  gentianGate_mem_gadget,
  weldedGate_mem_gadget,
  decodeGate_mem_gadget,
  recomputeLookup_mem_gadget,
  gadget_gate_holds,
  recompute_lookup_holds,
  recompute_discharged,
  isZero_from_gates,
  decode_discharged,
  gentian_selector_forced_discharged,
  gentian_settle_forced_discharged,
  gentian_partial_unsat_discharged,
  gentian_phantom_unsat_discharged
]

end Dregg2.Deos.InAirAuthorityDigestGadget
