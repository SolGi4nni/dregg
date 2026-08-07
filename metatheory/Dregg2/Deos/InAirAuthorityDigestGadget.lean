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

⚑ **THE COMPOSED KEYSTONE IS GONE (2026-08-01).** The composition that ran recompute + CR floor +
decode into a forced selector — `gentian_selector_forced_discharged`, `gentian_settle_forced_discharged`
and the two unsat teeth — is DELETED, because its CR step went through `FloorDigestBinds`, which the
tree PROVES false at deployed parameters (`InAirAuthorityFloorRegrounded.floorDigestBinds_false_babyBear`).
All four were vacuously true. See the §10–§11 tombstone below for the replacements to consume; the
strongest is `Deos.CarrierBoundFloorGadget`, which keeps the Boolean impossibility AND kills the
`hcommitLimb` dodge. What SURVIVES here is the part that never needed the false floor: the two
discharges themselves — `recompute_discharged` (§8, on `ChipTableSound` alone) and `decode_discharged`
(§9, pure gate arithmetic, NO crypto floor) — plus the descriptor and its membership lemmas.

## STAGED — built BESIDE the deployed, NOT flipped

The gadget adds a chip lookup + arithmetic gates to the WIDE welded descriptor; it is a flag-day VK
bump (a new digest interpretation of the committed limb + new columns) — STAGED, NOT emitted into a
committed VK, NOT routed. The deployed descriptors / VK are byte-identical; the drift gate is green.
Rust shadow: `circuit/src/effect_vm/authority_digest_weld.rs` (the decode/recompute gates + producer).

## Tag-agnostic reuse

`isZero_from_gates` + the decode/OR-fold are parametric in the matched tag; tags 18 (discharge) / 19
(vault) / Custom / temporal reuse the decode half verbatim once their satisfaction gates land
(`IN-AIR-AUTHORITY-DIGEST-GADGET.md` §7). The selector half now belongs to
`Deos.CarrierBoundFloorGadget`.

## Axiom hygiene

`#assert_all_clean` at the close. The one remaining named hypothesis is the chip-table faithfulness
floor `ChipTableSound` (`recompute_discharged`); `decode_discharged` carries none. Never an axiom; no
core edit. Both reduce through the STABLE `Satisfied2.rowConstraints` interface and the deployed
`chip_lookup_sound` lever. `FloorDigestBinds` survives as a REFUTED def only — it is consumed by
nothing in this file.
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
axiom.

⚠ **BROKEN AS NAMED — FALSE at deployed parameters, so the CR leg of all four consumers below is
VACUOUSLY TRUE there** (`Deos.InAirAuthorityFloorRegrounded.floorDigestBinds_false_babyBear`;
`docs/deos/VACUITY-SWEEP.md` FINDING 2). It is injectivity on the INFINITE `List ℤ` while the Option-B
digest is ONE BabyBear felt — literally the `StateCommit.compressNInjective` shape, which
`HashFloorHonesty` had ALREADY proved false.

⚑ **AND THE FELT BOUND THAT REFUTES THIS FLOOR IS A HYPOTHESIS THE CONSUMERS THEMSELVES ASSUME, IN THE
SAME SIGNATURE, ABOUT THE VERY FELTS THEY DIGEST**: `hcanon : ∀ c, 0 ≤ (envAt t i).loc c ∧
(envAt t i).loc c < 2013265921`. The pigeon was always in the signature.

**The honest replacement is `Deos.InAirAuthorityFloorRegrounded`** —
`gentian_alternate_floor_advantage_bound`, from a REAL alternate-floor game whose win relation reads
the attacked value out of the REAL `VmTrace` (`(envAt …).loc gentianAuthDigestCol`, the deployed
column through the deployed `envAt`) and transports through the limb binding to a genuine collision,
carrying an explicit undischarged `Eff`. ⚑ SCOPE, NAMED: that repair re-grounds the **CR leg only** —
the chip-table faithfulness leg (`ChipTableSound`) and the wide-commit limb binding (`hcommitLimb`)
are SEPARATE hypotheses with their own repair paths, untouched. One of three legs. This def is KEPT so
the record and the teeth keep compiling. -/
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
  have hlen : Dregg2.Circuit.DescriptorIR2.ChipArityAdmitted
      (floorCols.map (EmittedExpr.var)).length := by
    simp only [floorCols, List.length_map, List.length_cons, List.length_nil]
    chip_arity_admitted
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

/-! ## §10–§11 — TOMBSTONE: the four `FloorDigestBinds` consumers, DELETED as VACUOUS (2026-08-01).

DELETED here: `gentian_selector_forced_discharged` (the selector-forcing keystone),
`gentian_settle_forced_discharged` (the four sealed-escrow conjuncts), and the two teeth
`gentian_partial_unsat_discharged` / `gentian_phantom_unsat_discharged`. Each claimed a Boolean
IMPOSSIBILITY — the capacity selector is FORCED `1` on a cell whose committed authority-digest limb is
the Option-B digest of an escrow-requiring floor; a partial or phantom settle CANNOT satisfy the gadget
descriptor — under `hCR : FloorDigestBinds hash`.

WHY THEY WENT. `FloorDigestBinds hash` is `Function.Injective hash` on the INFINITE `List ℤ` while the
Option-B floor digest is ONE BabyBear felt. The tree PROVES that hypothesis false:
`Deos.InAirAuthorityFloorRegrounded.floorDigestBinds_false_of_finite_range` (the counting core) and
`Deos.InAirAuthorityFloorRegrounded.floorDigestBinds_false_babyBear` (the deployed form). So all four
were VACUOUSLY TRUE at every deployed parameter — they constrained no real prover. ⚑ The refuting felt
bound stood IN THEIR OWN SIGNATURES: `hcanon : ∀ c, 0 ≤ (envAt t i).loc c ∧ (envAt t i).loc c <
2013265921`, asserted about the very felts they digest. `#assert_axioms` never saw it — it audits the
PROOF (kernel-clean, and these were) and never the HYPOTHESIS.

The def `FloorDigestBinds` (§2) is KEPT. The two falsity theorems name it, and `Verify/FloorRatchet`
fails closed on a sentinel floor with no visible in-tree refutation: the def is the tombstone WITH
TEETH, the accrual stop against a fresh vacuous floor of the same shape.

CONSUME INSTEAD — ⚑ THE ROM FORMS FIRST, and read why the ordering matters:

  * ⚑ `Deos.InAirAuthorityFloorRegrounded` — the `…_binds_rom` pair. These are the ONLY genuinely
    floor-free replacements: no injectivity carrier, no cost model, only query-boundedness and a
    PolyBounded query count concluding `Negl`. They are ABSENT from `Verify/FloorRatchetBaseline` —
    that absence IS the evidence they carry no floor. Prefer these.

  * `Deos.CarrierBoundFloorGadget` — `gentian_selector_forced_carrier`,
    `gentian_settle_forced_carrier`, `gentian_forged_floor_unsat_carrier`,
    `gentian_partial_unsat_carrier`, `gentian_phantom_unsat_carrier`. Boolean successors that KEEP the
    impossibility shape, with no `FloorDigestBinds`, no recompute chip lookup and no separate digest
    limb. They earn one real credit the deleted four never had: they discharge the
    unforced-`hcommitLimb` dodge, because the floor is the row's caveat-manifest tags pinned to the
    committed manifest by the EXISTING `caveatCommit_binds`, so a forged floor is REFUTED outright
    (`gentian_forged_floor_unsat_carrier`) rather than assumed away.

    ⚠ BUT THEY REST ON `Poseidon2SpongeCR`, WHICH THIS TREE ALSO REFUTES — by the same counting core
    at the same modulus (`Circuit/HashFloorHonesty.lean:129 poseidon2SpongeCR_false_babyBear`). All
    five are grandfathered floor carriers in `FloorRatchetBaseline`, sitting four lines from the
    names deleted here. So they are a BETTER-SHAPED Boolean, not a floor-free one: strictly stronger
    than what was deleted, and still vacuous at BabyBear. An earlier draft of this tombstone ranked
    them "strongest first" without saying so, which would have sent a reader off one refuted floor
    onto another.
  * `Deos.InAirAuthorityFloorRegrounded` — `gentian_alternate_floor_advantage_bound` /
    `gentian_settle_alternate_floor_advantage_bound`: the CR leg as an advantage bound off a real
    alternate-floor game whose win relation reads the attacked value out of the deployed `VmTrace`
    column, carrying an EXPLICIT undischarged `Eff`. Their DISCHARGED keyed-ROM successors
    `gentian_alternate_floor_binds_rom` / `gentian_settle_alternate_floor_binds_rom` carry NO floor
    hypothesis and no cost-model dodge — only a polynomial query budget and class membership,
    concluding `Negl`.

Both replacements re-ground the CR leg only; `ChipTableSound` (chip-table faithfulness) remains a
separate named hypothesis with its own repair path, and the carrier path is what removes `hcommitLimb`.

`Verify/FloorRatchetBaseline` still lists the four deleted names — a baseline name that is no longer a
carrier reports as SLACK, which is the intended reading. -/

/-! ## §12 — NON-VACUITY TEETH (`#guard`): the decode + the recompute lookup are real and BITE. -/

section Witnesses

-- escrowBitZ both polarities.
#guard escrowBitZ [tagEscrowZ] == 1
#guard escrowBitZ [] == 0
#guard escrowBitZ [6, 19] == 0
#guard escrowBitZ [18, tagEscrowZ] == 1

-- The gadget descriptor extends the selector descriptor (63 PIs, no new PI — the discharge is
-- in-AIR, not a pin) and appends the recompute lookup + the five decode gates.
#guard (gentianGadgetDescriptor 0 1).piCount == 56
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
  decode_discharged
]

end Dregg2.Deos.InAirAuthorityDigestGadget
