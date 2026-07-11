/-
# Dregg2.Deos.BareCohortFloorRefuseDeployed — the DEPLOYED-ALIGNED (column-parametric) bare-refuse.

`BareCohortFloorRefuse` proves the bare-descriptor dodge closed at the gadget's ABSTRACT columns
(`CarrierBoundFloorGadget.CARRIER_BASE = EFFECT_VM_WIDTH + 200`, a single decode/refuse block). But the
DEPLOYED flag-day emit must (a) read the REAL deployed caveat-manifest columns (`caveat_tag_col k`
= `CAVEAT_BASE + 1 + 7·k` = 643/650/657/664 at v13 geometry — the columns the deployed `caveatCommit`
hash-site actually commits to PI 45, so the `hbind` hypothesis is discharged by the LIVE caveat pin,
not a free assumption), and (b) carry THREE decode/refuse blocks (escrow 17 / discharge 18 / vault 19)
at DISJOINT aux columns on ONE bare member (`GRAD_ROT_WIDTH + b·REFUSE_STRIDE + …`, the Rust
`bare_floor_refuse_weld` deployed alignment).

This module lifts the `BareCohortFloorRefuse` §9 keystone to be **column-parametric**: the decode/refuse
soundness is proven for ANY entry-base / bit / inv / or / floor column layout and ANY descriptor whose
constraints CONTAIN the block (membership hypotheses), so it composes over the three-block deployed
member and instantiates at the deployed columns. The gate CONSTRUCTORS (`isZeroDefGateT`,
`isZeroForceGateT`, `orSeedGate`, `orFoldGate`, `floorZeroRefuseGate`) are already column-parametric in
`BareCohortFloorRefuse` / `CarrierBoundFloorGadget`; only the descriptor + the four decode theorems were
column-fixed. The landed abstract-column core is UNTOUCHED (kept green); this is additive.

## The anti-launder gate (preserved)

`declared_tag_unsat_at` proves: a satisfying witness of a descriptor `D` that CONTAINS the tag-`T`
decode+refuse block at the deployed caveat columns, on a cell whose COMMITTED manifest declares `T`, is
FALSE — under only `Poseidon2SpongeCR`, for a pure light client. The three deployed instances close the
escrow / discharge / vault dodges on the DEFAULT path. No new axiom; `#assert_all_clean` at the close.
Rust deployed-column twin: `circuit/src/effect_vm/bare_floor_refuse_weld.rs`.
-/
import Dregg2.Deos.BareCohortFloorRefuse

namespace Dregg2.Deos.BareCohortFloorRefuseDeployed

open Dregg2.Circuit.DescriptorIR2
open Dregg2.Circuit.Emit.EffectVmEmit
open Dregg2.Exec.CircuitEmit (EmittedExpr)
open Dregg2.Circuit.Poseidon2Binding (Poseidon2SpongeCR)
open Dregg2.Circuit.Emit.EffectVmEmitRotationCaveat
  (RotCaveatManifest caveatCommit caveatCommit_binds zeroEntry)
open Dregg2.Deos.InAirAuthorityDigestGadget (isZero_from_gates)
open Dregg2.Deos.CarrierBoundFloorGadget
  (manifestTags orSeedGate orFoldGate)
open Dregg2.Deos.BareCohortFloorRefuse
  (floorZeroRefuseGate tagBitZ isZeroDefGateT isZeroForceGateT orStepT)

open Dregg2.Deos.ConstraintBinding (tagSettleEscrow tagDischargeObligation tagVaultDeposit)

set_option autoImplicit false

open Dregg2.Circuit.Emit.EffectVmEmitTransfer (gate_modEq_iff)

/-- Field-faithful lift: two CANONICAL (`0 ≤ · < p`) integers congruent mod `p` are EQUAL. -/
private theorem canonEq {a b : ℤ} (h : a ≡ b [ZMOD 2013265921])
    (ha0 : 0 ≤ a) (hap : a < 2013265921) (hb0 : 0 ≤ b) (hbp : b < 2013265921) : a = b := by
  unfold Int.ModEq at h
  rwa [Int.emod_eq_of_lt ha0 hap, Int.emod_eq_of_lt hb0 hbp] at h

/-- The tag-parametric decode is a boolean value. -/
private theorem tagBitZ_mem (tag : ℤ) (l : List ℤ) : tagBitZ tag l = 0 ∨ tagBitZ tag l = 1 := by
  unfold tagBitZ; split <;> simp

/-- The OR-fold congruence lifts to the exact boolean-OR under canonicality and booleanity. -/
private theorem orFoldLift {oNext o b : ℤ}
    (hmod : oNext ≡ o + b - o * b [ZMOD 2013265921])
    (hoN : 0 ≤ oNext ∧ oNext < 2013265921)
    (ho : o = 0 ∨ o = 1) (hb : b = 0 ∨ b = 1) :
    oNext = o + b - o * b := by
  have hrhs : 0 ≤ o + b - o * b ∧ o + b - o * b < 2013265921 := by
    rcases ho with h | h <;> rcases hb with h' | h' <;> rw [h, h'] <;> norm_num
  exact canonEq hmod hoN.1 hoN.2 hrhs.1 hrhs.2

/-! ## §1 — the column-parametric decode/refuse block. -/

/-- Read a caveat manifest off a row at parametric columns: count at `cc`, the four 7-felt entries at
`eb 0 .. eb 3` (each entry's type tag is its first felt — the decode input). At the DEPLOYED layout
`cc = CAVEAT_BASE`, `eb i = CAVEAT_BASE + 1 + 7·i`, this is EXACTLY the manifest the deployed
`caveatCommit` hash-site commits to PI 45 (so `caveatCommit hash (manifestOf …) = the deployed PI-45
commit`, discharging `hbind`). Mirror of `CarrierBoundFloorGadget.gadgetManifest`, columns parametric. -/
def manifestOf (cc : Nat) (eb : Nat → Nat) (loc : Nat → ℤ) : RotCaveatManifest :=
  { count := loc cc
  , e0 := ⟨loc (eb 0), loc (eb 0 + 1), loc (eb 0 + 2),
           loc (eb 0 + 3), loc (eb 0 + 4), loc (eb 0 + 5), loc (eb 0 + 6)⟩
  , e1 := ⟨loc (eb 1), loc (eb 1 + 1), loc (eb 1 + 2),
           loc (eb 1 + 3), loc (eb 1 + 4), loc (eb 1 + 5), loc (eb 1 + 6)⟩
  , e2 := ⟨loc (eb 2), loc (eb 2 + 1), loc (eb 2 + 2),
           loc (eb 2 + 3), loc (eb 2 + 4), loc (eb 2 + 5), loc (eb 2 + 6)⟩
  , e3 := ⟨loc (eb 3), loc (eb 3 + 1), loc (eb 3 + 2),
           loc (eb 3 + 3), loc (eb 3 + 4), loc (eb 3 + 5), loc (eb 3 + 6)⟩ }

/-- The decode reads exactly the four parametric type-tag columns. -/
theorem manifestTags_of (cc : Nat) (eb : Nat → Nat) (loc : Nat → ℤ) :
    manifestTags (manifestOf cc eb loc)
      = [loc (eb 0), loc (eb 1), loc (eb 2), loc (eb 3)] := rfl

/-- The tag-`T` decode gates at parametric columns: four per-slot is-zero gadgets against `T` over the
entry-base type-tag columns `eb k`, plus the running-OR fold into the block floor column `fc`. Mirror of
`BareCohortFloorRefuse.decodeGatesT`, columns parametric. -/
def decodeGatesAt (tag : ℤ) (eb bc ic oc : Nat → Nat) (fc : Nat) : List VmConstraint2 :=
  [ isZeroDefGateT tag (eb 0) (bc 0) (ic 0), isZeroForceGateT tag (eb 0) (bc 0)
  , isZeroDefGateT tag (eb 1) (bc 1) (ic 1), isZeroForceGateT tag (eb 1) (bc 1)
  , isZeroDefGateT tag (eb 2) (bc 2) (ic 2), isZeroForceGateT tag (eb 2) (bc 2)
  , isZeroDefGateT tag (eb 3) (bc 3) (ic 3), isZeroForceGateT tag (eb 3) (bc 3)
  , orSeedGate (oc 0) (bc 0)
  , orFoldGate (oc 1) (oc 0) (bc 1)
  , orFoldGate (oc 2) (oc 1) (bc 2)
  , orFoldGate fc (oc 2) (bc 3) ]

/-- The tag-`T` refuse block at parametric columns: the decode + the `floorZeroRefuseGate fc`. -/
def refuseGatesAt (tag : ℤ) (eb bc ic oc : Nat → Nat) (fc : Nat) : List VmConstraint2 :=
  decodeGatesAt tag eb bc ic oc fc ++ [floorZeroRefuseGate fc]

/-! ## §2 — the generic gate-forcing helper over ANY descriptor CONTAINING the block. -/

/-- A gate that is a member of `D.constraints` has its body vanish on a satisfying non-last row. Generic
over `D` (the membership is a hypothesis) so the keystone composes over a multi-block deployed member. -/
theorem gate_holds_of_mem (hash : List ℤ → ℤ) (D : EffectVmDescriptor2)
    {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
    (hsat : Satisfied2 hash D minit mfin maddrs t)
    (i : Nat) (hi : i < t.rows.length) (hnl : (i + 1 == t.rows.length) = false)
    (g : VmConstraint2) (hg : g ∈ D.constraints)
    (body : EmittedExpr) (hbody : g = .base (.gate body)) :
    body.eval (envAt t i).loc ≡ 0 [ZMOD 2013265921] := by
  have hrow := hsat.rowConstraints i hi g hg
  rw [hbody] at hrow
  simpa [VmConstraint2.holdsAt, VmConstraint.holdsVm, hnl] using hrow

/-! ## §3 — per-slot decode + floor decode, column-parametric, over a containing descriptor. -/

/-- A per-slot is-zero gadget forces `bc k = tagBitZ T [tagColumn]` on a satisfying non-last row. -/
theorem bit_decodes_at (hash : List ℤ → ℤ) (tag : ℤ) (eb bc ic oc : Nat → Nat) (fc : Nat)
    (D : EffectVmDescriptor2)
    (hmem : ∀ g ∈ decodeGatesAt tag eb bc ic oc fc, g ∈ D.constraints)
    {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
    (hsat : Satisfied2 hash D minit mfin maddrs t)
    (i : Nat) (hi : i < t.rows.length) (hnl : (i + 1 == t.rows.length) = false)
    (k : Nat)
    (hcanon : ∀ r c, 0 ≤ (envAt t r).loc c ∧ (envAt t r).loc c < 2013265921)
    (htag : 0 ≤ tag ∧ tag < 2013265921)
    (hdefmem : isZeroDefGateT tag (eb k) (bc k) (ic k) ∈ decodeGatesAt tag eb bc ic oc fc)
    (hforcemem : isZeroForceGateT tag (eb k) (bc k) ∈ decodeGatesAt tag eb bc ic oc fc) :
    (envAt t i).loc (bc k) = tagBitZ tag [(envAt t i).loc (eb k)] := by
  have hdef := gate_holds_of_mem hash D hsat i hi hnl
    (isZeroDefGateT tag (eb k) (bc k) (ic k)) (hmem _ hdefmem) _ rfl
  have hforce := gate_holds_of_mem hash D hsat i hi hnl
    (isZeroForceGateT tag (eb k) (bc k)) (hmem _ hforcemem) _ rfl
  simp only [EmittedExpr.eval] at hdef hforce
  have hb := isZero_from_gates hdef hforce (hcanon i (bc k))
    (by have h := hcanon i (eb k); omega) (by have h := hcanon i (eb k); omega)
  rw [hb]
  unfold tagBitZ
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  by_cases h : (envAt t i).loc (eb k) + (-tag) = 0
  · rw [if_pos h, if_pos (by omega : tag = (envAt t i).loc (eb k))]
  · rw [if_neg h, if_neg (by omega : ¬ tag = (envAt t i).loc (eb k))]

/-- **THE COLUMN-PARAMETRIC DECODE.** On a satisfying non-last row, the block floor column `fc` is the
felt decode of the row's four caveat-manifest type tags against `T`. -/
theorem floor_decodes_at (hash : List ℤ → ℤ) (tag : ℤ) (eb bc ic oc : Nat → Nat) (fc : Nat)
    (D : EffectVmDescriptor2)
    (hmem : ∀ g ∈ decodeGatesAt tag eb bc ic oc fc, g ∈ D.constraints)
    {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
    (hsat : Satisfied2 hash D minit mfin maddrs t)
    (i : Nat) (hi : i < t.rows.length) (hnl : (i + 1 == t.rows.length) = false)
    (hcanon : ∀ r c, 0 ≤ (envAt t r).loc c ∧ (envAt t r).loc c < 2013265921)
    (htag : 0 ≤ tag ∧ tag < 2013265921) :
    (envAt t i).loc fc
      = tagBitZ tag (manifestTags (manifestOf 0 eb (envAt t i).loc)) := by
  have hb0 := bit_decodes_at hash tag eb bc ic oc fc D hmem hsat i hi hnl 0 hcanon htag
    (by simp [decodeGatesAt]) (by simp [decodeGatesAt])
  have hb1 := bit_decodes_at hash tag eb bc ic oc fc D hmem hsat i hi hnl 1 hcanon htag
    (by simp [decodeGatesAt]) (by simp [decodeGatesAt])
  have hb2 := bit_decodes_at hash tag eb bc ic oc fc D hmem hsat i hi hnl 2 hcanon htag
    (by simp [decodeGatesAt]) (by simp [decodeGatesAt])
  have hb3 := bit_decodes_at hash tag eb bc ic oc fc D hmem hsat i hi hnl 3 hcanon htag
    (by simp [decodeGatesAt]) (by simp [decodeGatesAt])
  have hseed := gate_holds_of_mem hash D hsat i hi hnl
    (orSeedGate (oc 0) (bc 0)) (hmem _ (by simp [decodeGatesAt])) _ rfl
  have hf1 := gate_holds_of_mem hash D hsat i hi hnl
    (orFoldGate (oc 1) (oc 0) (bc 1)) (hmem _ (by simp [decodeGatesAt])) _ rfl
  have hf2 := gate_holds_of_mem hash D hsat i hi hnl
    (orFoldGate (oc 2) (oc 1) (bc 2)) (hmem _ (by simp [decodeGatesAt])) _ rfl
  have hf3 := gate_holds_of_mem hash D hsat i hi hnl
    (orFoldGate fc (oc 2) (bc 3)) (hmem _ (by simp [decodeGatesAt])) _ rfl
  simp only [EmittedExpr.eval] at hseed hf1 hf2 hf3
  have ho0 : (envAt t i).loc (oc 0) = tagBitZ tag [(envAt t i).loc (eb 0)] := by
    rw [show (envAt t i).loc (oc 0) = (envAt t i).loc (bc 0) from
      canonEq ((gate_modEq_iff (by ring)).mp hseed) (hcanon i _).1 (hcanon i _).2
        (hcanon i _).1 (hcanon i _).2]
    exact hb0
  have hm1 : (envAt t i).loc (oc 1)
      ≡ (envAt t i).loc (oc 0) + (envAt t i).loc (bc 1)
        - (envAt t i).loc (oc 0) * (envAt t i).loc (bc 1) [ZMOD 2013265921] :=
    (gate_modEq_iff (by ring)).mp hf1
  have ho1 : (envAt t i).loc (oc 1)
      = tagBitZ tag ([(envAt t i).loc (eb 0)] ++ [(envAt t i).loc (eb 1)]) :=
    orStepT ho0 hb1 (orFoldLift hm1 (hcanon i _)
      (by rw [ho0]; exact tagBitZ_mem _ _) (by rw [hb1]; exact tagBitZ_mem _ _))
  have hm2 : (envAt t i).loc (oc 2)
      ≡ (envAt t i).loc (oc 1) + (envAt t i).loc (bc 2)
        - (envAt t i).loc (oc 1) * (envAt t i).loc (bc 2) [ZMOD 2013265921] :=
    (gate_modEq_iff (by ring)).mp hf2
  have ho2 : (envAt t i).loc (oc 2)
      = tagBitZ tag ([(envAt t i).loc (eb 0), (envAt t i).loc (eb 1)]
          ++ [(envAt t i).loc (eb 2)]) :=
    orStepT ho1 hb2 (orFoldLift hm2 (hcanon i _)
      (by rw [ho1]; exact tagBitZ_mem _ _) (by rw [hb2]; exact tagBitZ_mem _ _))
  have hm3 : (envAt t i).loc fc
      ≡ (envAt t i).loc (oc 2) + (envAt t i).loc (bc 3)
        - (envAt t i).loc (oc 2) * (envAt t i).loc (bc 3) [ZMOD 2013265921] :=
    (gate_modEq_iff (by ring)).mp hf3
  have ho3 : (envAt t i).loc fc
      = tagBitZ tag ([(envAt t i).loc (eb 0), (envAt t i).loc (eb 1),
          (envAt t i).loc (eb 2)] ++ [(envAt t i).loc (eb 3)]) :=
    orStepT ho2 hb3 (orFoldLift hm3 (hcanon i _)
      (by rw [ho2]; exact tagBitZ_mem _ _) (by rw [hb3]; exact tagBitZ_mem _ _))
  rw [ho3, manifestTags_of]
  simp only [List.cons_append, List.nil_append]

/-! ## §4 — THE DEPLOYED-ALIGNED REFUSE KEYSTONE (column-parametric, containing descriptor). -/

/-- **THE BARE-DESCRIPTOR DODGE CLOSED ON THE DEPLOYED DEFAULT (parametric).** For ANY capacity tag `T`,
ANY deployed caveat count/entry columns `cc/eb`, ANY disjoint decode-aux columns `bc/ic/oc/fc`, and ANY
descriptor `D` whose constraints CONTAIN the tag-`T` decode+refuse block, a satisfying witness of `D` on
a cell whose COMMITTED caveat manifest declares `T` is FALSE — under only `Poseidon2SpongeCR`. The
decode pins the block floor to the committed manifest (the tag columns `eb k` are the deployed caveat
columns the `caveatCommit` hash-site commits, so `hbind` is discharged by the LIVE PI-45 caveat pin);
the committed declaration lights `fc = 1`; the `floorZeroRefuseGate fc` demands `0`. There is no
satisfying assignment. Instantiated at the three deployed tags over a three-block bare cohort member,
this is the whole-cohort flag-day soundness. -/
theorem declared_tag_unsat_at (hash : List ℤ → ℤ) (hCR : Poseidon2SpongeCR hash)
    (tag : ℤ) (cc : Nat) (eb bc ic oc : Nat → Nat) (fc : Nat)
    (D : EffectVmDescriptor2)
    (hmemDecode : ∀ g ∈ decodeGatesAt tag eb bc ic oc fc, g ∈ D.constraints)
    (hmemRefuse : floorZeroRefuseGate fc ∈ D.constraints)
    {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
    (hsat : Satisfied2 hash D minit mfin maddrs t)
    (hi : 0 < t.rows.length) (hnl : (0 + 1 == t.rows.length) = false)
    (hcanon : ∀ r c, 0 ≤ (envAt t r).loc c ∧ (envAt t r).loc c < 2013265921)
    (htag : 0 ≤ tag ∧ tag < 2013265921)
    (committedManifest : RotCaveatManifest)
    (hbind : caveatCommit hash (manifestOf cc eb (envAt t 0).loc)
      = caveatCommit hash committedManifest)
    (hreq : tag ∈ manifestTags committedManifest) :
    False := by
  have hmeq : manifestOf cc eb (envAt t 0).loc = committedManifest := caveatCommit_binds hash hCR hbind
  have hrowreq : tag ∈ manifestTags (manifestOf cc eb (envAt t 0).loc) := by rw [hmeq]; exact hreq
  have hdec := floor_decodes_at hash tag eb bc ic oc fc D hmemDecode hsat 0 hi hnl hcanon htag
  -- `manifestTags` ignores `cc`; align the decode's `manifestOf 0` tags with the bound `manifestOf cc`.
  have htags : manifestTags (manifestOf 0 eb (envAt t 0).loc)
      = manifestTags (manifestOf cc eb (envAt t 0).loc) := by rw [manifestTags_of, manifestTags_of]
  have hfloor : (envAt t 0).loc fc = 1 := by
    rw [hdec, htags]; unfold tagBitZ; rw [if_pos hrowreq]
  have hrefuse := gate_holds_of_mem hash D hsat 0 hi hnl
    (floorZeroRefuseGate fc) hmemRefuse (.var fc) rfl
  simp only [EmittedExpr.eval] at hrefuse
  rw [hfloor] at hrefuse
  exact absurd hrefuse (by decide)

/-! ## §5 — THE DEPLOYED THREE-BLOCK BARE MEMBER + the three closed dodges.

The deployed flag-day welds THREE decode+refuse blocks (escrow 17 / discharge 18 / vault 19) at DISJOINT
aux columns onto every bare cohort member. The column layout mirrors the Rust `bare_floor_refuse_weld`
deployed alignment exactly: the caveat tag columns `ebDep` (shared, 643/650/657/664) and per-block
disjoint aux `bcDep/icDep/ocDep/fcDep b` at `GRAD_ROT_WIDTH + b·REFUSE_STRIDE + …`. -/

/-- REFUSE_STRIDE — the per-tag-block aux stride (Rust twin `bare_floor_refuse_weld::REFUSE_STRIDE`). -/
def REFUSE_STRIDE : Nat := 16
/-- GRAD_ROT_WIDTH at v13 geometry (Rust twin `trace_rotated::GRAD_ROT_WIDTH = 1581`). -/
def GRAD_ROT_WIDTH : Nat := 1581
/-- CAVEAT_BASE at v13 geometry (Rust twin `trace_rotated::CAVEAT_BASE = 642`). -/
def CAVEAT_BASE : Nat := 642

/-- The deployed caveat count column. -/
def ccDep : Nat := CAVEAT_BASE
/-- The deployed caveat entry-base / type-tag columns (643/650/657/664). Rust twin `caveat_tag_col`. -/
def ebDep (k : Nat) : Nat := CAVEAT_BASE + 1 + 7 * k
/-- The per-block disjoint decode-aux columns at a PER-MEMBER aux base (Rust twins
`bit_col`/`inv_col`/`or_col`/`floor_col`, recovered by `refuse_aux_base`). The aux base is the member's
OWN `traceWidth` (§HETEROGENEOUS GEOMETRY): a standard graduated member bases its refuse at
`GRAD_ROT_WIDTH = 1581` (its own width); a DISTINCT V1Face member — `setFieldDyn` / `custom`, four fewer
chip sites, width `1553` — bases its refuse at `1553`, so the block always rides the member's OWN free
headroom (never the fixed 1581 that would leave a 28-column dead gap on a 1553-wide member). -/
def bcDep (auxBase b k : Nat) : Nat := auxBase + b * REFUSE_STRIDE + k
def icDep (auxBase b k : Nat) : Nat := auxBase + b * REFUSE_STRIDE + 4 + k
def ocDep (auxBase b j : Nat) : Nat := auxBase + b * REFUSE_STRIDE + 8 + j
def fcDep (auxBase b : Nat) : Nat := auxBase + b * REFUSE_STRIDE + 12

/-- The block-`b` refuse block for its capacity tag (0 = escrow, 1 = discharge, 2 = vault) at aux base
`auxBase`. -/
def blockGates (auxBase : Nat) (tag : ℤ) (b : Nat) : List VmConstraint2 :=
  refuseGatesAt tag ebDep (bcDep auxBase b) (icDep auxBase b) (ocDep auxBase b) (fcDep auxBase b)

/-- The deployed three-block refuse weld at aux base `auxBase`: block 0 = escrow (17), block 1 =
discharge (18), block 2 = vault (19), each at its disjoint aux columns. This is the Lean source-of-truth
the flag-day emit maps over `v3RegistryBare`. -/
def deployedRefuseGates (auxBase : Nat) : List VmConstraint2 :=
  blockGates auxBase (tagSettleEscrow : ℤ) 0
    ++ blockGates auxBase (tagDischargeObligation : ℤ) 1
    ++ blockGates auxBase (tagVaultDeposit : ℤ) 2

/-- **`gentianDeployedBareRefuse d`** — an arbitrary deployed bare cohort member `d` welded with the
three-block deployed refuse over its OWN geometry AND widened to cover the aux block. The aux base is
`d.traceWidth`, so the blocks ride the free headroom ABOVE the member's own data — a standard `1581`
member widens to `1626` (byte-identical to the pre-heterogeneous weld), a distinct-geometry `1553`
member (`setFieldDyn` / `custom`) widens to `1598` over ITS 1553 base. The flag-day maps this over the
whole `v3RegistryBare` cohort. The soundness keystones below take the aux base parametrically, so the
per-member base is transparent to them (it only enlarges the AIR `main` arity to host the free aux
columns). -/
def gentianDeployedBareRefuse (d : EffectVmDescriptor2) : EffectVmDescriptor2 :=
  { d with
    name        := d.name ++ "-gentian-deployed-bare-refuse"
    traceWidth  := fcDep d.traceWidth 2 + 1
    constraints := d.constraints ++ deployedRefuseGates d.traceWidth }

/-- The block-`b`, tag-`T` decode gates are members of block `b`'s refuse block (at aux base `auxBase`). -/
theorem decode_mem_block (auxBase : Nat) (tag : ℤ) (b : Nat) (g : VmConstraint2)
    (hg : g ∈ decodeGatesAt tag ebDep (bcDep auxBase b) (icDep auxBase b)
      (ocDep auxBase b) (fcDep auxBase b)) :
    g ∈ blockGates auxBase tag b := by
  unfold blockGates refuseGatesAt; exact List.mem_append_left _ hg

/-- The block-`b` refuse gate is a member of block `b`'s refuse block (at aux base `auxBase`). -/
theorem refuse_mem_block (auxBase : Nat) (tag : ℤ) (b : Nat) :
    floorZeroRefuseGate (fcDep auxBase b) ∈ blockGates auxBase tag b := by
  unfold blockGates refuseGatesAt
  exact List.mem_append_right _ (List.mem_singleton.mpr rfl)

/-- A member of ANY of the three blocks is a member of the deployed welded member's constraints. -/
theorem block_mem_deployed (d : EffectVmDescriptor2) (g : VmConstraint2)
    (hg : g ∈ blockGates d.traceWidth (tagSettleEscrow : ℤ) 0
      ∨ g ∈ blockGates d.traceWidth (tagDischargeObligation : ℤ) 1
      ∨ g ∈ blockGates d.traceWidth (tagVaultDeposit : ℤ) 2) :
    g ∈ (gentianDeployedBareRefuse d).constraints := by
  unfold gentianDeployedBareRefuse deployedRefuseGates
  refine List.mem_append_right d.constraints ?_
  simp only [List.mem_append]
  tauto

/-- **THE THREE DEPLOYED DODGES, CLOSED (parametric keystone instantiated).** For a cell whose committed
manifest declares capacity tag `T` at deployed block `b` (escrow 0 / discharge 1 / vault 2), a
satisfying witness of the three-block deployed bare member is FALSE. -/
theorem declared_capacity_unsat_deployed (hash : List ℤ → ℤ) (hCR : Poseidon2SpongeCR hash)
    (tag : ℤ) (b : Nat) (d : EffectVmDescriptor2)
    (hblock : blockGates d.traceWidth tag b = blockGates d.traceWidth (tagSettleEscrow : ℤ) 0
      ∨ blockGates d.traceWidth tag b = blockGates d.traceWidth (tagDischargeObligation : ℤ) 1
      ∨ blockGates d.traceWidth tag b = blockGates d.traceWidth (tagVaultDeposit : ℤ) 2)
    {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
    (hsat : Satisfied2 hash (gentianDeployedBareRefuse d) minit mfin maddrs t)
    (hi : 0 < t.rows.length) (hnl : (0 + 1 == t.rows.length) = false)
    (hcanon : ∀ r c, 0 ≤ (envAt t r).loc c ∧ (envAt t r).loc c < 2013265921)
    (htag : 0 ≤ tag ∧ tag < 2013265921)
    (committedManifest : RotCaveatManifest)
    (hbind : caveatCommit hash (manifestOf ccDep ebDep (envAt t 0).loc)
      = caveatCommit hash committedManifest)
    (hreq : tag ∈ manifestTags committedManifest) :
    False := by
  refine declared_tag_unsat_at hash hCR tag ccDep ebDep (bcDep d.traceWidth b) (icDep d.traceWidth b)
    (ocDep d.traceWidth b) (fcDep d.traceWidth b)
    (gentianDeployedBareRefuse d) (fun g hg => block_mem_deployed d g ?_)
    (block_mem_deployed d _ ?_) hsat hi hnl hcanon htag committedManifest hbind hreq
  · -- decode gate membership: route into the matching block via `hblock`.
    rcases hblock with h | h | h
    · exact Or.inl (h ▸ decode_mem_block d.traceWidth tag b g hg)
    · exact Or.inr (Or.inl (h ▸ decode_mem_block d.traceWidth tag b g hg))
    · exact Or.inr (Or.inr (h ▸ decode_mem_block d.traceWidth tag b g hg))
  · -- refuse gate membership.
    rcases hblock with h | h | h
    · exact Or.inl (h ▸ refuse_mem_block d.traceWidth tag b)
    · exact Or.inr (Or.inl (h ▸ refuse_mem_block d.traceWidth tag b))
    · exact Or.inr (Or.inr (h ▸ refuse_mem_block d.traceWidth tag b))

/-- Escrow (block 0) is UNSAT under the deployed bare member when the committed manifest declares it. -/
theorem declared_escrow_unsat_deployed (hash : List ℤ → ℤ) (hCR : Poseidon2SpongeCR hash)
    (d : EffectVmDescriptor2)
    {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
    (hsat : Satisfied2 hash (gentianDeployedBareRefuse d) minit mfin maddrs t)
    (hi : 0 < t.rows.length) (hnl : (0 + 1 == t.rows.length) = false)
    (hcanon : ∀ r c, 0 ≤ (envAt t r).loc c ∧ (envAt t r).loc c < 2013265921)
    (committedManifest : RotCaveatManifest)
    (hbind : caveatCommit hash (manifestOf ccDep ebDep (envAt t 0).loc)
      = caveatCommit hash committedManifest)
    (hreq : (tagSettleEscrow : ℤ) ∈ manifestTags committedManifest) :
    False :=
  declared_capacity_unsat_deployed hash hCR _ 0 d (Or.inl rfl) hsat hi hnl hcanon (by decide)
    committedManifest hbind hreq

/-- Discharge (block 1) is UNSAT under the deployed bare member when the committed manifest declares it. -/
theorem declared_discharge_unsat_deployed (hash : List ℤ → ℤ) (hCR : Poseidon2SpongeCR hash)
    (d : EffectVmDescriptor2)
    {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
    (hsat : Satisfied2 hash (gentianDeployedBareRefuse d) minit mfin maddrs t)
    (hi : 0 < t.rows.length) (hnl : (0 + 1 == t.rows.length) = false)
    (hcanon : ∀ r c, 0 ≤ (envAt t r).loc c ∧ (envAt t r).loc c < 2013265921)
    (committedManifest : RotCaveatManifest)
    (hbind : caveatCommit hash (manifestOf ccDep ebDep (envAt t 0).loc)
      = caveatCommit hash committedManifest)
    (hreq : (tagDischargeObligation : ℤ) ∈ manifestTags committedManifest) :
    False :=
  declared_capacity_unsat_deployed hash hCR _ 1 d (Or.inr (Or.inl rfl)) hsat hi hnl hcanon (by decide)
    committedManifest hbind hreq

/-- Vault (block 2) is UNSAT under the deployed bare member when the committed manifest declares it. -/
theorem declared_vault_unsat_deployed (hash : List ℤ → ℤ) (hCR : Poseidon2SpongeCR hash)
    (d : EffectVmDescriptor2)
    {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
    (hsat : Satisfied2 hash (gentianDeployedBareRefuse d) minit mfin maddrs t)
    (hi : 0 < t.rows.length) (hnl : (0 + 1 == t.rows.length) = false)
    (hcanon : ∀ r c, 0 ≤ (envAt t r).loc c ∧ (envAt t r).loc c < 2013265921)
    (committedManifest : RotCaveatManifest)
    (hbind : caveatCommit hash (manifestOf ccDep ebDep (envAt t 0).loc)
      = caveatCommit hash committedManifest)
    (hreq : (tagVaultDeposit : ℤ) ∈ manifestTags committedManifest) :
    False :=
  declared_capacity_unsat_deployed hash hCR _ 2 d (Or.inr (Or.inr rfl)) hsat hi hnl hcanon (by decide)
    committedManifest hbind hreq

/-! ## §5b — THE PEEL: `Satisfied2 (gentianDeployedBareRefuse d) ⟹ Satisfied2 d`.

The flag-day re-keys the apex over the WELDED cohort (`v3RegistryRefused` — every bare member wrapped
`withDfaRcPins ∘ gentianDeployedBareRefuse`). The apex's per-effect soundness rungs are stated at the
BARE face (`Satisfied2 d ⟹ genuine kernel step`). Since the weld only APPENDS `.base (.gate …)`
constraints (`deployedRefuseGates`, 39 pure gates — no mem-op / map-op / range / hash-site) and WIDENS
`traceWidth` (transparent to `Satisfied2`, which never bounds by `traceWidth`), a satisfying witness of
the welded member is a fortiori a satisfying witness of the bare face: peel the appended gates and every
existing rung lifts (`List.mem_append_left`). The exact structural mirror of
`EffectVmEmitRotationV3.satisfied2_of_withDfaRcPins` (the rc-pin peel), so the two compose:
`Satisfied2 (withDfaRcPins (gentianDeployedBareRefuse d)) ⟹ Satisfied2 (gentianDeployedBareRefuse d)
⟹ Satisfied2 d`. -/

/-- The refuse gates are all `.base (.gate …)`, so they contribute NO mem-op (the mem log is unchanged). -/
theorem memOpsOf_gentianDeployedBareRefuse (d : EffectVmDescriptor2) :
    memOpsOf (gentianDeployedBareRefuse d) = memOpsOf d := by
  simp only [memOpsOf, gentianDeployedBareRefuse, List.filterMap_append,
    deployedRefuseGates, blockGates, refuseGatesAt, decodeGatesAt,
    floorZeroRefuseGate, isZeroDefGateT, isZeroForceGateT, orSeedGate, orFoldGate,
    List.filterMap_cons, List.filterMap_nil, List.append_nil, List.nil_append,
    List.cons_append]

/-- The refuse gates contribute NO map-op (the map log is unchanged). -/
theorem mapOpsOf_gentianDeployedBareRefuse (d : EffectVmDescriptor2) :
    mapOpsOf (gentianDeployedBareRefuse d) = mapOpsOf d := by
  simp only [mapOpsOf, gentianDeployedBareRefuse, List.filterMap_append,
    deployedRefuseGates, blockGates, refuseGatesAt, decodeGatesAt,
    floorZeroRefuseGate, isZeroDefGateT, isZeroForceGateT, orSeedGate, orFoldGate,
    List.filterMap_cons, List.filterMap_nil, List.append_nil, List.nil_append,
    List.cons_append]

/-- **THE REFUSE PEEL — `Satisfied2 (gentianDeployedBareRefuse d) ⟹ Satisfied2 d`.** The weld only
APPENDS pure `.gate` constraints (and widens `traceWidth`): the inner constraints stay members
(`List.mem_append_left`), sites / ranges / mem / map logs are unchanged, so every existing per-effect
soundness lemma lifts to the welded descriptor by peeling the weld first. Mirrors
`satisfied2_of_withDfaRcPins`. -/
theorem satisfied2_of_gentianDeployedBareRefuse (hash : List ℤ → ℤ) (d : EffectVmDescriptor2)
    {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
    (h : Satisfied2 hash (gentianDeployedBareRefuse d) minit mfin maddrs t) :
    Satisfied2 hash d minit mfin maddrs t := by
  have hmem : memLog (gentianDeployedBareRefuse d) t = memLog d t := by
    simp [memLog, memOpsOf_gentianDeployedBareRefuse]
  have hmap : mapLog (gentianDeployedBareRefuse d) t = mapLog d t := by
    simp [mapLog, mapOpsOf_gentianDeployedBareRefuse]
  exact
    { rowConstraints := fun i hi c hc => h.rowConstraints i hi c (by
        show c ∈ (gentianDeployedBareRefuse d).constraints
        unfold gentianDeployedBareRefuse
        exact List.mem_append_left _ hc)
    , rowHashes := h.rowHashes
    , rowRanges := h.rowRanges
    , memAddrsNodup := h.memAddrsNodup
    , memClosed := fun op hop => h.memClosed op (by rw [hmem]; exact hop)
    , memDisciplined := by rw [← hmem]; exact h.memDisciplined
    , memBalanced := by rw [← hmem]; exact h.memBalanced
    , memTableFaithful := by rw [← hmem]; exact h.memTableFaithful
    , mapTableFaithful := by rw [← hmap]; exact h.mapTableFaithful }

/-! ## §6 — NON-VACUITY TEETH: the deployed column layout + both decode poles BITE. -/

section Witnesses

-- The deployed caveat tag columns match the Rust `caveat_tag_col` v13 pins (643/650/657/664).
#guard ebDep 0 == 643
#guard ebDep 1 == 650
#guard ebDep 2 == 657
#guard ebDep 3 == 664
-- STANDARD geometry (auxBase = GRAD_ROT_WIDTH = 1581): the three aux blocks are DISJOINT (no
-- bit/inv/or/floor column aliases across blocks). Floor cols 1593/1609/1625, separated by REFUSE_STRIDE.
#guard fcDep GRAD_ROT_WIDTH 0 == 1593
#guard fcDep GRAD_ROT_WIDTH 1 == 1609
#guard fcDep GRAD_ROT_WIDTH 2 == 1625
#guard ([ bcDep GRAD_ROT_WIDTH 0 0, bcDep GRAD_ROT_WIDTH 0 1, bcDep GRAD_ROT_WIDTH 0 2,
          bcDep GRAD_ROT_WIDTH 0 3, icDep GRAD_ROT_WIDTH 0 0, icDep GRAD_ROT_WIDTH 0 1,
          icDep GRAD_ROT_WIDTH 0 2, icDep GRAD_ROT_WIDTH 0 3,
          ocDep GRAD_ROT_WIDTH 0 0, ocDep GRAD_ROT_WIDTH 0 1, ocDep GRAD_ROT_WIDTH 0 2, fcDep GRAD_ROT_WIDTH 0,
          bcDep GRAD_ROT_WIDTH 1 0, bcDep GRAD_ROT_WIDTH 1 1, bcDep GRAD_ROT_WIDTH 1 2,
          bcDep GRAD_ROT_WIDTH 1 3, icDep GRAD_ROT_WIDTH 1 0, icDep GRAD_ROT_WIDTH 1 1,
          icDep GRAD_ROT_WIDTH 1 2, icDep GRAD_ROT_WIDTH 1 3,
          ocDep GRAD_ROT_WIDTH 1 0, ocDep GRAD_ROT_WIDTH 1 1, ocDep GRAD_ROT_WIDTH 1 2, fcDep GRAD_ROT_WIDTH 1,
          bcDep GRAD_ROT_WIDTH 2 0, bcDep GRAD_ROT_WIDTH 2 1, bcDep GRAD_ROT_WIDTH 2 2,
          bcDep GRAD_ROT_WIDTH 2 3, icDep GRAD_ROT_WIDTH 2 0, icDep GRAD_ROT_WIDTH 2 1,
          icDep GRAD_ROT_WIDTH 2 2, icDep GRAD_ROT_WIDTH 2 3,
          ocDep GRAD_ROT_WIDTH 2 0, ocDep GRAD_ROT_WIDTH 2 1, ocDep GRAD_ROT_WIDTH 2 2, fcDep GRAD_ROT_WIDTH 2 ]).dedup.length == 36
-- The aux blocks start PAST the graduated rotated width (the traceWidth widening the flag-day pays).
#guard fcDep GRAD_ROT_WIDTH 2 ≥ GRAD_ROT_WIDTH
#guard fcDep GRAD_ROT_WIDTH 2 + 1 == 1626
-- The three-block weld adds 3 × 13 = 39 gates (each block: 8 is-zero + 3 fold-into + 1 refuse = 13).
#guard (deployedRefuseGates GRAD_ROT_WIDTH).length == 39
-- DISTINCT V1Face geometry (auxBase = 1553 = GRAD_ROT_WIDTH − 4 chip sites·7): setFieldDyn / custom
-- base their refuse at 1553 (floor cols 1565/1581/1597) and widen to 1598 over their OWN base — NOT
-- the fixed 1581 that would over-widen to 1626 and strand a 28-column dead gap.
#guard fcDep 1553 0 == 1565
#guard fcDep 1553 2 == 1597
#guard fcDep 1553 2 + 1 == 1598
private def toyBare : EffectVmDescriptor2 :=
  { name := "toy", traceWidth := 1581, piCount := 46, tables := [], constraints := [], hashSites := [],
    ranges := [] }
-- Standard member: widens 1581 → 1626 (byte-identical to the pre-heterogeneous weld).
#guard (gentianDeployedBareRefuse toyBare).traceWidth == 1626
#guard (gentianDeployedBareRefuse toyBare).constraints.length == 39
#guard (gentianDeployedBareRefuse toyBare).piCount == 46
private def toyDistinct : EffectVmDescriptor2 :=
  { name := "toy-distinct", traceWidth := 1553, piCount := 46, tables := [], constraints := [],
    hashSites := [], ranges := [] }
-- Distinct-geometry member: widens 1553 → 1598 over its OWN 1553 base (per-member geometry respected).
#guard (gentianDeployedBareRefuse toyDistinct).traceWidth == 1598
#guard (gentianDeployedBareRefuse toyDistinct).constraints.length == 39
#guard (refuseGatesAt (tagSettleEscrow : ℤ) ebDep (bcDep GRAD_ROT_WIDTH 0) (icDep GRAD_ROT_WIDTH 0)
  (ocDep GRAD_ROT_WIDTH 0) (fcDep GRAD_ROT_WIDTH 0)).length == 13
-- The decode over a committed manifest, both poles per capacity tag (declared ⟹ 1, absent ⟹ 0).
#guard tagBitZ (tagSettleEscrow : ℤ) [(tagSettleEscrow : ℤ)] == 1
#guard tagBitZ (tagDischargeObligation : ℤ) [(tagDischargeObligation : ℤ)] == 1
#guard tagBitZ (tagVaultDeposit : ℤ) [(tagVaultDeposit : ℤ)] == 1
#guard tagBitZ (tagSettleEscrow : ℤ) [(tagDischargeObligation : ℤ)] == 0

end Witnesses

/-! ## §7 — Axiom hygiene. -/

#assert_all_clean [
  manifestTags_of,
  gate_holds_of_mem,
  bit_decodes_at,
  floor_decodes_at,
  declared_tag_unsat_at,
  decode_mem_block,
  refuse_mem_block,
  block_mem_deployed,
  declared_capacity_unsat_deployed,
  declared_escrow_unsat_deployed,
  declared_discharge_unsat_deployed,
  declared_vault_unsat_deployed,
  memOpsOf_gentianDeployedBareRefuse,
  mapOpsOf_gentianDeployedBareRefuse,
  satisfied2_of_gentianDeployedBareRefuse
]
-- (helper filterMap lemmas inlined into the memOpsOf/mapOpsOf simp above.)

end Dregg2.Deos.BareCohortFloorRefuseDeployed
