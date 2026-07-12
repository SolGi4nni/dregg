/-
# `Dregg2.Circuit.AirChecksSatisfied` — AIR SOUNDNESS half (ii): the QUOTIENT/constraint check
forces the opened trace to satisfy the descriptor's ROW-LOCAL algebraic constraints.

`CircuitSoundness.StarkSound` (class, 0 instances) carries `verifyBatch accept ⟹ ∃ Satisfied2 witness`.
That extraction splits into two independent halves:

  * **(i) FRI / low-degree proximity** — the committed columns ARE a low-degree codeword, so the
    quotient identity spot-checked at the out-of-domain point ζ (`FriVerifier.TableOpening`:
    `constraintEval = vanishingAtZeta · quotientAtZeta`) lifts to an identity on the whole
    evaluation domain, hence to the OPENED trace on `H`. This is `AirSoundness.FriProximity` / the
    `Dregg2.Circuit.FriVerifier` field work — NOT this file.
  * **(ii) AIR soundness** — GIVEN the opened trace, the quotient/constraint check FORCES the trace
    to satisfy the descriptor's constraints. `AirSoundness.circuit_sound_via_fri` proves `CircuitSound`
    modulo `FriProximity` at a TOY VM (`Step State Effect`, an additive counter). THIS FILE is half
    (ii) at the DEPLOYED descriptor (`DescriptorIR2.EffectVmDescriptor2`, the v2 constraint grammar),
    connecting the quotient acceptance to the REAL `Satisfied2` fields, field by field.

## What "AIR acceptance on an opened trace" means for the deployed descriptor

The deployed p3 AIR verifier, per table, opens a QUOTIENT and checks the identity
`combinedConstraint = zerofier · quotient` (`FriVerifier.TableOpening.constraintEval =
vanishingAtZeta · quotientAtZeta`), recomputing the zerofier (`vanishingAtZeta + 1 = ζ^{2^db}`) so it
is not trusted. Its SOUNDNESS content, delivered by half (i) onto the opened trace, is: for each
declared constraint `c` there is an opened quotient value `quot i c` with

    arithResidual (envAt t i) … c  =  zerofier i · quot i c        (the quotient identity), and
    zerofier i = 0  for every trace row  i < t.rows.length          (the rows are roots of `Z_H`).

`arithResidual` is the SINGLE field element the deployed `builder.assert_zero(…)` vanishes for the
ARITHMETIC constraint forms (`base` gates / transitions / boundary / pi-binding, and the two-row
`windowGate`); it is `0` by construction for the interaction-bus kinds (`lookup` / `memOp` / `mapOp` /
`umemOp` / `proofBind`), whose soundness is NOT a row-local polynomial but the LogUp / table AIRs.
`MainAirAccept` bundles the identity + the domain fact; `mul_zero` then forces `arithResidual i c = 0`
at every trace row, and the arithmetic bridge turns that into the `Satisfied2` per-row denotation.

## Correspondence AIR-acceptance ↔ `Satisfied2` (which field rides which check)

  * `rowConstraints` on ARITHMETIC arms (`base`/`windowGate`)   — the MAIN-table quotient check. PROVED.
  * `rowConstraints` on `lookup`                                — the LogUp grand-product / interaction
        bus (`logupCumSum = 0`). NAMED dependency (LogUp permutation-argument soundness).
  * `rowConstraints` on `mapOp`                                 — the map-ops table AIR (Merkle-root
        recomposition) + its lookup. NAMED dependency (map-ops-table soundness).
  * `rowConstraints` on `memOp`/`umemOp`/`proofBind`           — `True` row-locally (content is global).
  * `rowHashes`                                                 — in-row Poseidon2 sites (arithmetic) OR
        the graduated Poseidon2 CHIP-table lookups. NAMED dependency (chip-table soundness) once
        graduated; the deployed `demoV2` has `hashSites = []`.
  * `rowRanges`                                                 — the range-TABLE lookup (or in-row
        bit-decomposition). NAMED dependency (`RangeTableSound`).
  * `memAddrsNodup`                                             — the memory-table sorted-address
        preprocessing / boundary. NAMED dependency.
  * `memClosed`                                                 — the memory address-inclusion bus. NAMED.
  * `memDisciplined`                                            — the memory-table per-row AIR (needs
        `memTableFaithful` first). NAMED.
  * `memBalanced` (`MemCheck`)                                  — the LogUp multiset balance
        (`logupCumSum = 0`). NAMED dependency (the LogUp permutation-argument soundness — the exact
        `permOutZ` scar zone: a bus "balanced" at a constant-zero permutation).
  * `memTableFaithful` / `mapTableFaithful`                     — the ASSEMBLY binding the aux tables to
        the gathered trace logs. NAMED dependency (table-assembly faithfulness — the `Satisfied2Faithful`
        failure mode; NOT faked here).

## HONEST SCOPE

The AIR quotient check on the opened trace PROVES the ARITHMETIC arms of `rowConstraints` (the
`base`/`windowGate` gates — the actual per-row VM-step algebra). It does NOT force the `lookup`/`mapOp`
arms, `rowRanges`, or any of the six memory/map-table legs: those ride the NAMED LogUp
permutation-argument / range-table / map-ops-table / table-assembly-faithfulness carriers. So this
yields `airAccept ⟹ Satisfied2` IN PART — the arithmetic per-row core proved, the LogUp/table legs
carried as EXPLICIT premises (exactly as `AirSoundness.circuit_sound_via_fri` carries `FriProximity`).
No `def …Sound` carrier is introduced; the deferred legs are honest hypotheses, not proved-by-assuming.

## Teeth (both instances)

  * an HONEST all-arithmetic trace is ACCEPTED (`honest_mainAirAccept`) and its `rowConstraints` FIRE
    (`honest_rowConstraints`);
  * a trace with a WRONG arithmetic gate CANNOT be accepted — the quotient identity is unsatisfiable at
    the offending trace row (`tampered_gate_unaccepted`): `zerofier` must vanish there (domain fact),
    but the residual is nonzero, so no `quot` closes the identity.
-/
import Dregg2.Circuit.DescriptorIR2

namespace Dregg2.Circuit.AirChecksSatisfied

open Dregg2.Circuit (Assignment)
open Dregg2.Circuit.Emit.EffectVmEmit
open Dregg2.Circuit.DescriptorIR2
open Dregg2.Crypto
open Dregg2.Exec.CircuitEmit (EmittedExpr)

/-- **DEBT-A bridge — an EXACT ℤ equality forces the mod-p congruence the deployed denotation demands.**
Post-DEBT-A, `VmConstraint.holdsVm` / `WindowConstraint.holdsAt` denote over BabyBear `p`
(`… ≡ 0 [ZMOD 2013265921]`), not `= 0` over ℤ. The `arithResidual` this file threads is still an EXACT
integer equation (a zero residual is `body.eval = 0` over ℤ), which is STRICTLY STRONGER than the mod-p
congruence — so lifting it is the easy direction, no range-check / canonicality envelope needed: any
witness satisfying the residual over ℤ a fortiori satisfies it mod `p`. -/
private theorem modEq_of_eq {a b : ℤ} (h : a = b) : a ≡ b [ZMOD 2013265921] := by rw [h]

/-- **The mod-p continuity step** — a difference congruent to `0` gives the two sides congruent. The
mod-p twin of `sub_eq_zero`: `holdsVm`'s `.transition` / `.piBinding` arms demand `a ≡ b [ZMOD p]`,
which the field residual `a - b ≡ 0 [ZMOD p]` delivers directly (no ℤ range envelope). -/
private theorem modEq_of_sub_modEq_zero {a b : ℤ} (h : a - b ≡ 0 [ZMOD 2013265921]) :
    a ≡ b [ZMOD 2013265921] := by simpa using h.add_right b

/-! ## §1 — `arithResidual`: the per-row field element the deployed `assert_zero` vanishes.

For each ARITHMETIC constraint form this is the polynomial the p3 `AirBuilder` asserts is zero on the
row window; for the interaction-bus kinds (`lookup`/`memOp`/`mapOp`/`umemOp`/`proofBind`) it is `0` by
construction — those contribute NOTHING to the quotient, their soundness being the LogUp / table AIRs.
The guards mirror `VmConstraint.holdsVm` / `WindowConstraint.holdsAt` EXACTLY (the `when_transition()` /
`when_first_row()` / `when_last_row()` arms), so the bridge below is guard-for-guard. -/
def arithResidual (env : VmRowEnv) (isFirst isLast : Bool) : VmConstraint2 → ℤ
  | .base (.gate body)              => match isLast with | true => 0 | false => body.eval env.loc
  | .base (.transition hi lo)       =>
      match isLast with | true => 0 | false => env.nxt (sbCol hi) - env.loc (saCol lo)
  | .base (.boundary .first b)      => match isFirst with | true => b.eval env.loc | false => 0
  | .base (.boundary .last b)       => match isLast  with | true => b.eval env.loc | false => 0
  | .base (.piBinding .first col k) => match isFirst with | true => env.loc col - env.pub k | false => 0
  | .base (.piBinding .last col k)  => match isLast  with | true => env.loc col - env.pub k | false => 0
  | .windowGate w                   =>
      match w.onTransition with
      | true  => (match isLast with | true => 0 | false => w.body.eval env)
      | false => w.body.eval env
  | .lookup _                       => 0
  | .memOp _                        => 0
  | .mapOp _                        => 0
  | .umemOp _                       => 0
  | .proofBind _                    => 0

/-- The ARITHMETIC constraint forms — the ones whose soundness IS the row-local quotient check
(`base` gates + the two-row `windowGate`). The interaction-bus kinds are excluded: their `arithResidual`
is `0` but their `holdsAt` is nontrivial (LogUp / table content), so `arithResidual = 0` does NOT force
them — they need the NAMED carriers. -/
def isArith : VmConstraint2 → Prop
  | .base _       => True
  | .windowGate _ => True
  | .lookup _     => False
  | .memOp _      => False
  | .mapOp _      => False
  | .umemOp _     => False
  | .proofBind _  => False

/-- **The arithmetic bridge — a mod-p-zero residual FORCES the row-local denotation.** For every
ARITHMETIC constraint form, `arithResidual env isFirst isLast c ≡ 0 [ZMOD p]` implies
`c.holdsAt hash tf env isFirst isLast`. Post-Phase-0 both sides live over BabyBear `p`: the residual
congruence is EXACTLY the field equation each `VmConstraint.holdsVm` / `WindowConstraint.holdsAt` arm
demands — a near-`rfl` (`gate`/`boundary`/`windowGate`: `body ≡ 0`) or the mod-p continuity step
(`transition`/`piBinding`: `a - b ≡ 0 ⟹ a ≡ b` via `modEq_of_sub_modEq_zero`). No ℤ→field lift and no
range envelope: the hypothesis is stated in the same field the denotation lives in. This is the whole
content of "the AIR constraint check forces the trace to satisfy the (arithmetic) constraints". -/
theorem arithResidual_zero_forces_holdsAt (hash : List ℤ → ℤ) (tf : TraceFamily)
    (env : VmRowEnv) (isFirst isLast : Bool) :
    ∀ c : VmConstraint2, isArith c →
      arithResidual env isFirst isLast c ≡ 0 [ZMOD 2013265921] →
      c.holdsAt hash tf env isFirst isLast := by
  intro c harith h0
  cases c with
  | base vc =>
    cases vc with
    | gate body =>
        cases isLast with
        | true  => exact trivial
        | false => simpa [VmConstraint2.holdsAt, VmConstraint.holdsVm, arithResidual] using h0
    | transition hi lo =>
        cases isLast with
        | true  => exact trivial
        | false =>
            have hs : env.nxt (sbCol hi) - env.loc (saCol lo) ≡ 0 [ZMOD 2013265921] := by
              simpa [arithResidual] using h0
            simpa [VmConstraint2.holdsAt, VmConstraint.holdsVm] using modEq_of_sub_modEq_zero hs
    | boundary row b =>
        cases row with
        | first =>
            cases isFirst with
            | true  =>
                simp only [VmConstraint2.holdsAt, VmConstraint.holdsVm]
                intro _; simpa [arithResidual] using h0
            | false =>
                simp only [VmConstraint2.holdsAt, VmConstraint.holdsVm]
                intro h; exact absurd h (by simp)
        | last =>
            cases isLast with
            | true  =>
                simp only [VmConstraint2.holdsAt, VmConstraint.holdsVm]
                intro _; simpa [arithResidual] using h0
            | false =>
                simp only [VmConstraint2.holdsAt, VmConstraint.holdsVm]
                intro h; exact absurd h (by simp)
    | piBinding row col k =>
        cases row with
        | first =>
            cases isFirst with
            | true  =>
                simp only [VmConstraint2.holdsAt, VmConstraint.holdsVm]
                intro _
                exact modEq_of_sub_modEq_zero (by simpa [arithResidual] using h0)
            | false =>
                simp only [VmConstraint2.holdsAt, VmConstraint.holdsVm]
                intro h; exact absurd h (by simp)
        | last =>
            cases isLast with
            | true  =>
                simp only [VmConstraint2.holdsAt, VmConstraint.holdsVm]
                intro _
                exact modEq_of_sub_modEq_zero (by simpa [arithResidual] using h0)
            | false =>
                simp only [VmConstraint2.holdsAt, VmConstraint.holdsVm]
                intro h; exact absurd h (by simp)
  | windowGate w =>
      simp only [VmConstraint2.holdsAt, WindowConstraint.holdsAt]
      cases hw : w.onTransition with
      | true =>
          cases isLast with
          | true  => intro h; exact absurd h (by simp)
          | false => intro _; simpa [arithResidual, hw] using h0
      | false => simpa [arithResidual, hw] using h0
  | lookup l    => exact absurd harith (by simp [isArith])
  | memOp m     => exact absurd harith (by simp [isArith])
  | mapOp m     => exact absurd harith (by simp [isArith])
  | umemOp m    => exact absurd harith (by simp [isArith])
  | proofBind m => exact absurd harith (by simp [isArith])

/-! ## §2 — `MainAirAccept`: the MAIN-table quotient check on the opened trace. -/

/-- **`MainAirAccept hash d t`** — the deployed AIR verifier ACCEPTS the opened trace `t` for
descriptor `d`. There is an opened per-constraint quotient `quot` and a recomputed zerofier such that
(1) the QUOTIENT IDENTITY `arithResidual … c = zerofier i · quot i c` holds at every row for every
declared constraint (`FriVerifier.TableOpening`'s `constraintEval = vanishingAtZeta · quotientAtZeta`,
delivered onto the opened trace by half (i)), and (2) the zerofier VANISHES on every trace row (the
rows are roots of `Z_H` — a structural fact of the evaluation-domain geometry, recomputed by the
verifier, NOT a crypto assumption). The verifier never sees `arithResidual` directly: it sees `quot`
and the recomputed zerofier and checks the identity — so a tampered gate (nonzero residual at a trace
row) is UNSATISFIABLE (`tampered_gate_unaccepted`). -/
def MainAirAccept (hash : List ℤ → ℤ) (d : EffectVmDescriptor2) (t : VmTrace) : Prop :=
  ∃ (quot : Nat → VmConstraint2 → ℤ) (zerofier : Nat → ℤ),
    (∀ i, ∀ c ∈ d.constraints,
        arithResidual (envAt t i) (i == 0) (i + 1 == t.rows.length) c = zerofier i * quot i c) ∧
    (∀ i < t.rows.length, zerofier i = 0)

/-- **AIR acceptance forces the per-row residual to VANISH at every trace row.** The core `mul_zero`
step: at a trace row `i < t.rows.length` the zerofier vanishes, so the quotient identity collapses the
residual to `0`. This is the whole soundness kernel of half (ii). -/
theorem mainAirAccept_forces_residual (hash : List ℤ → ℤ) (d : EffectVmDescriptor2) (t : VmTrace)
    (h : MainAirAccept hash d t) :
    ∀ i < t.rows.length, ∀ c ∈ d.constraints,
      arithResidual (envAt t i) (i == 0) (i + 1 == t.rows.length) c = 0 := by
  obtain ⟨quot, zerofier, hid, hdom⟩ := h
  intro i hi c hc
  rw [hid i c hc, hdom i hi, zero_mul]

/-! ### §2b — `MainAirAcceptF`: the CANONICAL field-valued AIR-accept predicate.

Phase-0 migrated `VmConstraint.holdsVm` / `WindowConstraint.holdsAt` to denote over BabyBear `p`
(`… ≡ 0 [ZMOD 2013265921]`). `MainAirAcceptF` is the AIR-accept predicate stated in the SAME field:
the per-row arithmetic residual is congruent to `0` mod `p` at every trace row. This is what the
deployed BabyBear main-table quotient check actually enforces — the OOD/quotient identity resolved to
the field residual (`FieldIntegerLift.ood_forces_mainAirAccept_field_of_residuals` produces exactly
this from the two crypto residuals `hood` + `hnonexc`). It SUPERSEDES the ℤ `MainAirAccept` as the
canonical target: for a multiplicative gate the ℤ residual can equal `p` (`≡ 0` mod `p`, `≠ 0` over ℤ),
so the ℤ predicate is UNREACHABLE for `transferV3`'s gates (`FieldIntegerLift.mainAirAcceptF_does_not_
imply_MainAirAcceptZ`). `MainAirAccept` (ℤ) survives only as the STRICTLY-STRONGER witness the teeth
and that counterexample use. -/
def MainAirAcceptF (d : EffectVmDescriptor2) (t : VmTrace) : Prop :=
  ∀ i < t.rows.length, ∀ c ∈ d.constraints,
    arithResidual (envAt t i) (i == 0) (i + 1 == t.rows.length) c ≡ 0 [ZMOD 2013265921]

/-- **The ℤ AIR-accept predicate is STRICTLY STRONGER than the field one.** An exact ℤ residual of `0`
a fortiori vanishes mod `p`, so `MainAirAccept ⟹ MainAirAcceptF`. (The converse FAILS at a
multiplicative wraparound gate — that is the whole reason `MainAirAcceptF` is the faithful target.) -/
theorem mainAirAccept_forces_mainAirAcceptF (hash : List ℤ → ℤ) (d : EffectVmDescriptor2) (t : VmTrace)
    (h : MainAirAccept hash d t) : MainAirAcceptF d t :=
  fun i hi c hc => modEq_of_eq (mainAirAccept_forces_residual hash d t h i hi c hc)

/-! ## §3 — AIR acceptance forces `rowConstraints` (arithmetic arms proved; bus arms carried). -/

/-- **`MainAirAccept` forces `Satisfied2.rowConstraints`.** The ARITHMETIC arms (`base`/`windowGate`)
are forced by the quotient check (`mainAirAccept_forces_residual` + the arithmetic bridge); the
interaction-bus arms (`lookup`/`mapOp`/`memOp`/…) are carried by `hbus` — the NAMED LogUp / map-ops-table
carriers' deliverable, an EXPLICIT premise (the AIR quotient check does not force them). This is the
exact split the deployed descriptor lives at: `demoV2` has one arithmetic constraint (a `transition`,
PROVED forced) plus a lookup, a memOp and a mapOp (carried). -/
theorem mainAirAccept_forces_rowConstraints (hash : List ℤ → ℤ) (d : EffectVmDescriptor2) (t : VmTrace)
    (h : MainAirAccept hash d t)
    (hbus : ∀ i < t.rows.length, ∀ c ∈ d.constraints, ¬ isArith c →
        c.holdsAt hash t.tf (envAt t i) (i == 0) (i + 1 == t.rows.length)) :
    ∀ i < t.rows.length, ∀ c ∈ d.constraints,
      c.holdsAt hash t.tf (envAt t i) (i == 0) (i + 1 == t.rows.length) := by
  intro i hi c hc
  by_cases hA : isArith c
  · exact arithResidual_zero_forces_holdsAt hash t.tf (envAt t i) (i == 0) (i + 1 == t.rows.length)
      c hA (modEq_of_eq (mainAirAccept_forces_residual hash d t h i hi c hc))
  · exact hbus i hi c hc hA

/-- **`MainAirAcceptF` forces `Satisfied2.rowConstraints`** — the CANONICAL field-valued lift. The
field predicate hands the mod-p residual `arithResidual … c ≡ 0 [ZMOD p]` per constraint DIRECTLY (no
`mul_zero`/quotient collapse — that is baked into `MainAirAcceptF`), which the mod-p arithmetic bridge
turns into the row-local denotation on ARITHMETIC arms; the bus arms ride `hbus`. This is the version
the deployed extraction chain consumes (the FRI/OOD side delivers `MainAirAcceptF`, not the ℤ one). -/
theorem mainAirAcceptF_forces_rowConstraints (hash : List ℤ → ℤ) (d : EffectVmDescriptor2)
    (t : VmTrace) (h : MainAirAcceptF d t)
    (hbus : ∀ i < t.rows.length, ∀ c ∈ d.constraints, ¬ isArith c →
        c.holdsAt hash t.tf (envAt t i) (i == 0) (i + 1 == t.rows.length)) :
    ∀ i < t.rows.length, ∀ c ∈ d.constraints,
      c.holdsAt hash t.tf (envAt t i) (i == 0) (i + 1 == t.rows.length) := by
  intro i hi c hc
  by_cases hA : isArith c
  · exact arithResidual_zero_forces_holdsAt hash t.tf (envAt t i) (i == 0) (i + 1 == t.rows.length)
      c hA (h i hi c hc)
  · exact hbus i hi c hc hA

/-- **The all-arithmetic corollary — full `rowConstraints` from the quotient check alone.** When every
declared constraint is arithmetic (the `embedV1` descriptor shape — no lookups / mem / map ops), AIR
acceptance forces the WHOLE `rowConstraints` field with NO carried premise: half (ii) discharges it
outright. -/
theorem mainAirAccept_forces_rowConstraints_allArith (hash : List ℤ → ℤ)
    (d : EffectVmDescriptor2) (t : VmTrace)
    (h : MainAirAccept hash d t) (hall : ∀ c ∈ d.constraints, isArith c) :
    ∀ i < t.rows.length, ∀ c ∈ d.constraints,
      c.holdsAt hash t.tf (envAt t i) (i == 0) (i + 1 == t.rows.length) :=
  mainAirAccept_forces_rowConstraints hash d t h
    (fun _ _ c hc hA => absurd (hall c hc) hA)

/-- **The all-arithmetic corollary for the FIELD predicate.** -/
theorem mainAirAcceptF_forces_rowConstraints_allArith (hash : List ℤ → ℤ)
    (d : EffectVmDescriptor2) (t : VmTrace)
    (h : MainAirAcceptF d t) (hall : ∀ c ∈ d.constraints, isArith c) :
    ∀ i < t.rows.length, ∀ c ∈ d.constraints,
      c.holdsAt hash t.tf (envAt t i) (i == 0) (i + 1 == t.rows.length) :=
  mainAirAcceptF_forces_rowConstraints hash d t h
    (fun _ _ c hc hA => absurd (hall c hc) hA)

/-! ## §4 — Compose toward `airAccept ⟹ Satisfied2` (the partial assembly).

`rowConstraints` is half (ii)'s PROVED contribution; the remaining eight `Satisfied2` fields ride the
NAMED carriers and are carried as EXPLICIT premises (each labelled with the carrier that delivers it).
This is the honest partial: the AIR quotient check + the named LogUp / range-table / map-ops-table /
table-assembly carriers ⟹ `Satisfied2`. It plugs UNDER `CircuitSoundness.StarkSound.extract`, whose
`∃ Satisfied2 witness` is exactly this `Satisfied2` — with `rowConstraints` supplied here by the AIR
acceptance and the bus/table legs by their carriers. -/
theorem airAccept_forces_satisfied2 (hash : List ℤ → ℤ) (d : EffectVmDescriptor2)
    (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (t : VmTrace)
    -- half (ii), PROVED here — the CANONICAL field-valued AIR acceptance:
    (hAir : MainAirAcceptF d t)
    -- the `lookup`/`mapOp` arms of `rowConstraints` — LogUp / map-ops-table carriers:
    (hbus : ∀ i < t.rows.length, ∀ c ∈ d.constraints, ¬ isArith c →
        c.holdsAt hash t.tf (envAt t i) (i == 0) (i + 1 == t.rows.length))
    -- `rowHashes` — in-row sites (arithmetic) OR the Poseidon2 CHIP-table carrier once graduated:
    (hHashes : ∀ i < t.rows.length, siteHoldsAll hash (envAt t i) d.hashSites)
    -- `rowRanges` — the range-TABLE lookup carrier (`RangeTableSound`):
    (hRanges : ∀ i < t.rows.length, ∀ r ∈ d.ranges, r.holds (envAt t i))
    -- the six memory/map-table legs — the LogUp balance / table-assembly-faithfulness carriers:
    (hNodup : maddrs.Nodup)
    (hClosed : ∀ op ∈ memLog d t, op.addr ∈ maddrs)
    (hDisc : MemoryChecking.Disciplined (memLog d t))
    (hBal : MemoryChecking.MemCheck minit mfin maddrs (memLog d t))
    (hMemTF : t.tf .memory = (memLog d t).map opRow)
    (hMapTF : t.tf .mapOps = mapLog d t) :
    Satisfied2 hash d minit mfin maddrs t where
  rowConstraints  := mainAirAcceptF_forces_rowConstraints hash d t hAir hbus
  rowHashes       := hHashes
  rowRanges       := hRanges
  memAddrsNodup   := hNodup
  memClosed       := hClosed
  memDisciplined  := hDisc
  memBalanced     := hBal
  memTableFaithful := hMemTF
  mapTableFaithful := hMapTF

#assert_axioms arithResidual_zero_forces_holdsAt
#assert_axioms mainAirAccept_forces_residual
#assert_axioms mainAirAccept_forces_mainAirAcceptF
#assert_axioms mainAirAccept_forces_rowConstraints
#assert_axioms mainAirAcceptF_forces_rowConstraints
#assert_axioms mainAirAccept_forces_rowConstraints_allArith
#assert_axioms mainAirAcceptF_forces_rowConstraints_allArith
#assert_axioms airAccept_forces_satisfied2

/-! ## §5 — TEETH (both instances load-bearing).

Toy descriptor `dArith`: a single arithmetic gate `col 0 = 0`. The honest 2-row trace (`col 0 = 0` on
every row) is ACCEPTED and its `rowConstraints` FIRE; a tampered 2-row trace (`col 0 = 5` on the first,
non-last row) is UNACCEPTABLE — the quotient identity has no solution at that row. -/
section Teeth

/-- The toy descriptor: one arithmetic per-row gate `col 0 = 0` (a `.base (.gate (.var 0))`). -/
def dArith : EffectVmDescriptor2 :=
  { name := "air-teeth", traceWidth := 1, piCount := 0
  , tables := [], constraints := [.base (.gate (.var 0))]
  , hashSites := [], ranges := [] }

/-- The all-zero row. -/
def zRow : Assignment := fun _ => 0
/-- A row with `col 0 = 5`, everything else `0` (the tamper). -/
def tRow : Assignment := fun c => if c = 0 then 5 else 0

/-- The HONEST 2-row trace: both rows `0` (so row 0 is a genuine, non-last transition row). -/
def tHonest : VmTrace := { rows := [zRow, zRow], pub := zRow, tf := fun _ => [] }
/-- The TAMPERED 2-row trace: row 0 has `col 0 = 5`. -/
def tTampered : VmTrace := { rows := [tRow, zRow], pub := zRow, tf := fun _ => [] }

/-- The single declared constraint is arithmetic. -/
theorem dArith_allArith : ∀ c ∈ dArith.constraints, isArith c := by
  intro c hc
  simp only [dArith, List.mem_singleton] at hc
  subst hc; exact trivial

/-- **RESPECTING INSTANCE — the honest trace is ACCEPTED.** With `quot := 0`, `zerofier := 0`: the
residual of the gate is `0` at every row (`col 0 = 0` throughout, and off-domain rows read `zeroAsg`),
so the quotient identity `0 = 0 · 0` holds and the zerofier vanishes on the trace rows. -/
theorem honest_mainAirAccept : MainAirAccept (fun _ => 0) dArith tHonest := by
  refine ⟨fun _ _ => 0, fun _ => 0, ?_, fun _ _ => rfl⟩
  intro i c hc
  simp only [dArith, List.mem_singleton] at hc
  subst hc
  -- arithResidual of `.base (.gate (.var 0))` = `if isLast then 0 else (envAt tHonest i).loc 0`;
  -- both branches are 0 here (`loc 0 = 0` on every row, incl. the off-the-end zeroAsg default).
  rcases i with _ | _ | i
  · rfl
  · rfl
  · simp [arithResidual, envAt, tHonest, EmittedExpr.eval, List.getD, zeroAsg]

/-- **…and its `rowConstraints` FIRE** — the AIR acceptance discharges the whole (all-arithmetic)
`rowConstraints` field on the honest trace. -/
theorem honest_rowConstraints :
    ∀ i < tHonest.rows.length, ∀ c ∈ dArith.constraints,
      c.holdsAt (fun _ => 0) tHonest.tf (envAt tHonest i) (i == 0) (i + 1 == tHonest.rows.length) :=
  mainAirAccept_forces_rowConstraints_allArith (fun _ => 0) dArith tHonest
    honest_mainAirAccept dArith_allArith

/-- **WRONG-GATE TOOTH (load-bearing).** The tampered trace CANNOT be AIR-accepted. At row `0`
(non-last: `0 + 1 ≠ 2`) the gate residual is `5`, but any `MainAirAccept` forces the zerofier to vanish
there (`0 < 2`), so the quotient identity reads `5 = 0 · quot = 0` — impossible. A prover cannot commit
a trace whose row lies about the arithmetic and still pass the AIR quotient check. -/
theorem tampered_gate_unaccepted : ¬ MainAirAccept (fun _ => 0) dArith tTampered := by
  rintro ⟨quot, zerofier, hid, hdom⟩
  have hmem : (VmConstraint2.base (.gate (.var 0))) ∈ dArith.constraints := by
    simp [dArith]
  have hz : zerofier 0 = 0 := hdom 0 (by simp [tTampered])
  have hidentity := hid 0 (.base (.gate (.var 0))) hmem
  -- residual at row 0 (isLast = (0+1 == 2) = false) is `(envAt tTampered 0).loc 0 = 5`.
  have hres : arithResidual (envAt tTampered 0) (0 == 0) (0 + 1 == tTampered.rows.length)
      (.base (.gate (.var 0))) = 5 := by
    simp [arithResidual, envAt, tTampered, tRow, EmittedExpr.eval, List.getD]
  rw [hres, hz, zero_mul] at hidentity
  exact absurd hidentity (by norm_num)

/-- **RESPECTING (FIELD) — the honest trace satisfies the CANONICAL field predicate.** The stronger ℤ
acceptance a fortiori gives the mod-p `MainAirAcceptF`. -/
theorem honest_mainAirAcceptF : MainAirAcceptF dArith tHonest :=
  mainAirAccept_forces_mainAirAcceptF (fun _ => 0) dArith tHonest honest_mainAirAccept

/-- **WRONG-GATE TOOTH (FIELD, load-bearing).** The tampered trace CANNOT satisfy `MainAirAcceptF`
either: at row `0` the gate residual is the integer `5`, and `5 ≢ 0 [ZMOD 2013265921]` (since
`0 < 5 < p`). So the field predicate is genuinely falsifiable by a lying arithmetic row — the mod-p
migration does NOT weaken the tooth (it is not vacuously true on tampered data). -/
theorem tampered_gate_unacceptedF : ¬ MainAirAcceptF dArith tTampered := by
  intro h
  have hres := h 0 (by simp [tTampered]) (.base (.gate (.var 0))) (by simp [dArith])
  rw [show arithResidual (envAt tTampered 0) (0 == 0) (0 + 1 == tTampered.rows.length)
        (.base (.gate (.var 0))) = 5 by
        simp [arithResidual, envAt, tTampered, tRow, EmittedExpr.eval, List.getD]] at hres
  rw [Int.modEq_zero_iff_dvd] at hres
  norm_num at hres

end Teeth

#assert_axioms honest_mainAirAccept
#assert_axioms honest_mainAirAcceptF
#assert_axioms honest_rowConstraints
#assert_axioms tampered_gate_unaccepted
#assert_axioms tampered_gate_unacceptedF

/-! ## §6 — the plug into `StarkSound` / `circuit_sound_via_fri`.

`Satisfied2` is precisely the witness `CircuitSoundness.StarkSound.extract` must produce from a
verifying batch; `airAccept_forces_satisfied2` is the half-(ii) assembly of that witness on an opened
trace — `rowConstraints` from the AIR quotient check (proved), the bus/table legs from their named
carriers. `AirSoundness.circuit_sound_via_fri` is the companion single-effect composition MODULO
`FriProximity` (half (i)); the two halves compose to the `StarkSound` extraction: half (i) delivers the
opened trace on `H` on which the constraints are spot-checked, half (ii) (this file) turns that opened
trace's quotient acceptance into the `Satisfied2` fields. -/
#check @Satisfied2
#check @airAccept_forces_satisfied2

end Dregg2.Circuit.AirChecksSatisfied
