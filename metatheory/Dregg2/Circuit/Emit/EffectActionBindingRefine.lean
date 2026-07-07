/-
# Dregg2.Circuit.Emit.EffectActionBindingRefine — the WHOLE-DESCRIPTOR functional-correctness
bridge for the effect-action binding family (`EffectActionBindingEmit`).

## What Rung-0 already proved (in `EffectActionBindingEmit.lean`)
`effectActionDesc` / `revokeCapabilityDesc` / `burnDesc` are byte-pinned to the hand AIR
(`effect_action_air.rs`), and each gate has a LOCAL soundness lemma (`cont_zero_iff`: the per-column
continuity poly vanishes iff that column chains; `cLo_zero_iff` / `cHi_zero_iff` /
`cBorrowBool_zero_iff` / `cWasBurnLo_zero_iff`: each Burn gate poly vanishes iff its local relation).

## What THIS file proves (Rung-1)
The census dossier for `effect_action` is `spec_status = NO_LEAN`: no proven semantic model existed.
So this file FIRST authors the missing functional spec — the genuine relation the binding AIR is
meant to compute — then proves the emitted descriptor refines it, WHOLE-DESCRIPTOR.

### The semantic relations (authored here)
`EffectActionAir` binds an effect's typed parameters into the STARK public inputs at full fidelity
and forces EVERY trace row (row 0 by the PI pins, every padding row by the transition continuity) to
carry EXACTLY that tuple — so a malicious prover cannot stash a different parameter set in a later
row (anti-malleability). The `Burn` schema additionally witnesses the two-limb u64 subtraction
`new_balance == old_balance − amount` with a boolean borrow, and pins the disclosure flag. The
authored functional spec is therefore:

  * `EffectRowBinds row pub P` / `EffectActionBinds t P` — every one of the `P` public-input columns
    of every trace row equals the published input (the faithful-binding / anti-stash relation).
  * `BurnSemantics env` — the u64 balance-conservation the Burn schema computes: the COMBINED
    two-limb subtraction `new_balance + amount = old_balance` (derived from the two per-limb gates,
    over ℤ — no range lookup needed for the algebraic identity), the borrow is a bit, and the
    `was_burn` flag is disclosed.

### The bridges (whole descriptor, not one gate)
`binds_of_gates` COMPOSES all PI pins (giving row 0) with all continuity gates (propagating row 0 to
every padding row by induction over the trace) into the whole-trace binding relation; it is
instantiated for the generic `effectActionDesc` (`effectActionDesc_satisfied2_binds`, SAT ⟹ SEM) and
for `burnDesc` (`burn_satisfied2_binds`). `burn_satisfied2_conserves` (SAT ⟹ SEM) additionally
derives the COMBINED u64 balance-conservation on every active row from the whole descriptor's Burn
gates. `revoke_binds_satisfied2` (SEM ⟹ SAT) completes the equivalence for the pure-binding schema,
so `revoke_satisfied2_iff` is the full IFF.

### Non-vacuity (the anti-scar proof)
`demoTrace_satisfied2` builds a CONCRETE satisfying witness for the pure-binding descriptor and
`burnTrace_satisfied2` a CONCRETE satisfying witness for the arithmetic `burnDesc` (a genuine
`old=new+amount` row) — the hypotheses are genuinely inhabited, and the bridges fire end-to-end on
them. `brokenBound_rejects` (PI pin bites), `brokenPad_rejects` (continuity bites — the exact
"stash a different tuple in a padding row" attack), and `badBurn_rejects` (the Burn low-limb
subtraction gate bites `601+400 ≠ 1000`) exhibit CONCRETE traces that FAIL `Satisfied2`.

## Axiom hygiene
`#assert_axioms` ⊆ {propext, Classical.choice, Quot.sound}. NO cryptographic carrier: this binding /
arithmetic family has no hash sites / ranges / map ops, so no Poseidon2 CR enters. NEW file; imports
read-only.
-/
import Dregg2.Circuit.Emit.EffectActionBindingEmit

namespace Dregg2.Circuit.Emit.EffectActionBindingRefine

open Dregg2.Circuit (Assignment)
open Dregg2.Exec.CircuitEmit (EmittedExpr)
open Dregg2.Circuit.Emit.EffectVmEmit (VmRowEnv VmConstraint VmRow)
open Dregg2.Circuit.DescriptorIR2
  (EffectVmDescriptor2 VmConstraint2 WindowConstraint WindowExpr Satisfied2 VmTrace TraceFamily
   TableId envAt zeroAsg memOpsOf mapOpsOf memLog mapLog opRow memCheck_nil)
open Dregg2.Circuit.Emit.EffectActionBindingEmit
  (contWindowBody contGate contGates piGate piGates effectActionDesc revokeCapabilityDesc burnDesc
   burnGates cLoBody cHiBody cBorrowBoolBody cWasBurnLoBody cWasBurnHiBody
   B_OLD_LO B_OLD_HI B_NEW_LO B_NEW_HI B_AMT_LO B_AMT_HI B_WASBURN_LO B_WASBURN_HI B_BORROW TWO_POW_32
   cont_zero_iff cLo_zero_iff cHi_zero_iff cBorrowBool_zero_iff cWasBurnLo_zero_iff)

set_option autoImplicit false

/-! ## §1 — The authored functional spec. -/

/-- A row BINDS the published tuple: every one of the `P` public-input columns equals the published
input. The identity-layout face of "this row carries exactly the effect's typed parameters". -/
def EffectRowBinds (row pub : Assignment) (P : Nat) : Prop :=
  ∀ c, c < P → row c = pub c

/-- **`EffectActionBinds t P`** — THE whole-trace binding relation the effect-action AIR computes:
every row of the trace binds the published `P`-column parameter tuple (anti-stash / anti-malleability
over the FULL trace, not just row 0). -/
def EffectActionBinds (t : VmTrace) (P : Nat) : Prop :=
  ∀ i, i < t.rows.length → EffectRowBinds (t.rows.getD i zeroAsg) t.pub P

/-- **`BurnSemantics env`** — THE u64 balance-conservation the `Burn` schema computes on a row: the
COMBINED two-limb subtraction `new_balance + amount = old_balance` (`balance := lo + 2^32·hi`), a
boolean borrow, and the disclosed `was_burn` flag. Derived over ℤ from the two per-limb gates — the
algebraic identity needs no range lookup (faithful to the hand AIR, which range-checks off-AIR). -/
def BurnSemantics (env : VmRowEnv) : Prop :=
  (env.loc B_NEW_LO + TWO_POW_32 * env.loc B_NEW_HI)
      + (env.loc B_AMT_LO + TWO_POW_32 * env.loc B_AMT_HI)
    = env.loc B_OLD_LO + TWO_POW_32 * env.loc B_OLD_HI
  ∧ (env.loc B_BORROW = 0 ∨ env.loc B_BORROW = 1)
  ∧ env.loc B_WASBURN_LO = 1
  ∧ env.loc B_WASBURN_HI = 0

/-! ## §2 — The per-constraint reductions (the STABLE surface to the three gate forms). -/

/-- A PI pin's per-row denotation IS its first-row PI equality (`pi_index == col`). -/
theorem piGate_holdsAt (hash : List ℤ → ℤ) (tf : TraceFamily) (env : VmRowEnv)
    (isFirst isLast : Bool) (c : Nat) :
    (piGate c).holdsAt hash tf env isFirst isLast ↔ (isFirst = true → env.loc c = env.pub c) :=
  Iff.rfl

/-- A continuity gate's per-row denotation IS "off the last row, this column chains" — via the
Rung-0 tooth `cont_zero_iff`. -/
theorem contGate_holdsAt (hash : List ℤ → ℤ) (tf : TraceFamily) (env : VmRowEnv)
    (isFirst isLast : Bool) (c : Nat) :
    (contGate c).holdsAt hash tf env isFirst isLast ↔ (isLast = false → env.nxt c = env.loc c) := by
  constructor
  · intro h hl; exact (cont_zero_iff env c).mp (h hl)
  · intro h hl; exact (cont_zero_iff env c).mpr (h hl)

/-- A Burn algebraic gate's per-row denotation IS "off the last row, this poly vanishes" — the
deployed `when_transition()` arm binds it on every active row. -/
theorem baseGate_holdsAt (hash : List ℤ → ℤ) (tf : TraceFamily) (env : VmRowEnv)
    (isFirst isLast : Bool) (body : EmittedExpr) :
    (VmConstraint2.base (VmConstraint.gate body)).holdsAt hash tf env isFirst isLast
      ↔ (isLast = false → body.eval env.loc = 0) := by
  cases isLast <;> simp [VmConstraint2.holdsAt, VmConstraint.holdsVm]

/-! ## §3 — Membership of the two binding families in the descriptors. -/

theorem contGate_mem_effectAction (name : String) (fc ac c : Nat) (hc : c < fc * 8 + ac * 2) :
    contGate c ∈ (effectActionDesc name fc ac).constraints := by
  show contGate c ∈ contGates (fc * 8 + ac * 2) ++ piGates (fc * 8 + ac * 2)
  exact List.mem_append_left _ (List.mem_map.mpr ⟨c, List.mem_range.mpr hc, rfl⟩)

theorem piGate_mem_effectAction (name : String) (fc ac c : Nat) (hc : c < fc * 8 + ac * 2) :
    piGate c ∈ (effectActionDesc name fc ac).constraints := by
  show piGate c ∈ contGates (fc * 8 + ac * 2) ++ piGates (fc * 8 + ac * 2)
  exact List.mem_append_right _ (List.mem_map.mpr ⟨c, List.mem_range.mpr hc, rfl⟩)

theorem contGate_mem_revoke (c : Nat) (hc : c < 10) : contGate c ∈ revokeCapabilityDesc.constraints := by
  show contGate c ∈ contGates 10 ++ piGates 10
  exact List.mem_append_left _ (List.mem_map.mpr ⟨c, List.mem_range.mpr hc, rfl⟩)

theorem piGate_mem_revoke (c : Nat) (hc : c < 10) : piGate c ∈ revokeCapabilityDesc.constraints := by
  show piGate c ∈ contGates 10 ++ piGates 10
  exact List.mem_append_right _ (List.mem_map.mpr ⟨c, List.mem_range.mpr hc, rfl⟩)

theorem contGate_mem_burn (c : Nat) (hc : c < 17) : contGate c ∈ burnDesc.constraints := by
  show contGate c ∈ contGates 17 ++ piGates 16 ++ burnGates
  exact List.mem_append_left _ (List.mem_append_left _ (List.mem_map.mpr ⟨c, List.mem_range.mpr hc, rfl⟩))

theorem piGate_mem_burn (c : Nat) (hc : c < 16) : piGate c ∈ burnDesc.constraints := by
  show piGate c ∈ contGates 17 ++ piGates 16 ++ burnGates
  exact List.mem_append_left _ (List.mem_append_right _ (List.mem_map.mpr ⟨c, List.mem_range.mpr hc, rfl⟩))

theorem burnGate_mem (body : EmittedExpr) (hb : VmConstraint2.base (VmConstraint.gate body) ∈ burnGates) :
    VmConstraint2.base (VmConstraint.gate body) ∈ burnDesc.constraints := by
  show VmConstraint2.base (VmConstraint.gate body) ∈ contGates 17 ++ piGates 16 ++ burnGates
  exact List.mem_append_right _ hb

/-! ## §4 — THE BINDING BRIDGE (SAT ⟹ SEM): a satisfying trace binds the published tuple in every row.

Parametric over the descriptor's PI-pin / continuity membership, so it fires for BOTH the generic
`effectActionDesc` and the arithmetic `burnDesc` — the whole descriptor, not one gate. -/

theorem binds_of_gates (P : Nat) (d : EffectVmDescriptor2)
    (hash : List ℤ → ℤ) (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (t : VmTrace)
    (h : Satisfied2 hash d minit mfin maddrs t)
    (hpi : ∀ c, c < P → piGate c ∈ d.constraints)
    (hcont : ∀ c, c < P → contGate c ∈ d.constraints) :
    EffectActionBinds t P := by
  -- boundary: row 0 binds the published tuple (the PI pins).
  have row0 : 0 < t.rows.length → EffectRowBinds (t.rows.getD 0 zeroAsg) t.pub P := by
    intro hpos c hc
    have hpin := h.rowConstraints 0 hpos _ (hpi c hc)
    rw [piGate_holdsAt] at hpin
    simpa [envAt] using hpin rfl
  -- continuity: consecutive active rows agree on every published column.
  have step : ∀ i, i + 1 < t.rows.length →
      EffectRowBinds (t.rows.getD (i + 1) zeroAsg) (t.rows.getD i zeroAsg) P := by
    intro i hi1 c hc
    have hgate := h.rowConstraints i (by omega) _ (hcont c hc)
    rw [contGate_holdsAt] at hgate
    have hlast : (i + 1 == t.rows.length) = false := by rw [beq_eq_false_iff_ne]; omega
    simpa [envAt] using hgate hlast
  -- induction: row 0 (PI pins) propagated to every row (continuity).
  intro i
  induction i with
  | zero => intro hi; exact row0 hi
  | succ k ih =>
    intro hi c hc
    have hk := ih (by omega) c hc
    have hs := step k hi c hc
    rw [hs, hk]

/-- **`effectActionDesc_satisfied2_binds` — the generic pure-binding soundness bridge.** A trace that
satisfies the whole `effectActionDesc name fc ac` binds the published `fc*8+ac*2`-column parameter
tuple in EVERY row. -/
theorem effectActionDesc_satisfied2_binds (name : String) (fc ac : Nat)
    (hash : List ℤ → ℤ) (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (t : VmTrace)
    (h : Satisfied2 hash (effectActionDesc name fc ac) minit mfin maddrs t) :
    EffectActionBinds t (fc * 8 + ac * 2) :=
  binds_of_gates (fc * 8 + ac * 2) (effectActionDesc name fc ac) hash minit mfin maddrs t h
    (fun c hc => piGate_mem_effectAction name fc ac c hc)
    (fun c hc => contGate_mem_effectAction name fc ac c hc)

/-- **`burn_satisfied2_binds`** — the Burn schema binds its published 16-column tuple in every row. -/
theorem burn_satisfied2_binds
    (hash : List ℤ → ℤ) (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (t : VmTrace)
    (h : Satisfied2 hash burnDesc minit mfin maddrs t) :
    EffectActionBinds t 16 :=
  binds_of_gates 16 burnDesc hash minit mfin maddrs t h
    (fun c hc => piGate_mem_burn c hc)
    (fun c hc => contGate_mem_burn c (by omega))

/-! ## §5 — THE BURN ARITHMETIC BRIDGE (SAT ⟹ SEM): balance conservation on every active row. -/

/-- Any Burn gate forces its body to vanish on an active (non-last) row. -/
theorem burn_active_gate
    (hash : List ℤ → ℤ) (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (t : VmTrace)
    (h : Satisfied2 hash burnDesc minit mfin maddrs t)
    (i : Nat) (hi : i < t.rows.length) (hnotlast : i + 1 ≠ t.rows.length)
    (body : EmittedExpr) (hb : VmConstraint2.base (VmConstraint.gate body) ∈ burnGates) :
    body.eval (envAt t i).loc = 0 := by
  have hrow := h.rowConstraints i hi _ (burnGate_mem body hb)
  rw [baseGate_holdsAt] at hrow
  have hlast : (i + 1 == t.rows.length) = false := by rw [beq_eq_false_iff_ne]; exact hnotlast
  exact hrow hlast

/-- **`burn_satisfied2_conserves` — THE whole-descriptor Burn functional bridge.** A trace that
satisfies the whole `burnDesc` conserves the u64 balance on EVERY active row: the COMBINED two-limb
subtraction `new_balance + amount = old_balance` (assembled by `omega` from the two per-limb gates),
the borrow is a bit, and the `was_burn` disclosure is set. This composes the FIVE Burn gates of the
whole descriptor into the genuine semantic relation — not a single-gate restatement. -/
theorem burn_satisfied2_conserves
    (hash : List ℤ → ℤ) (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (t : VmTrace)
    (h : Satisfied2 hash burnDesc minit mfin maddrs t)
    (i : Nat) (hi : i < t.rows.length) (hnotlast : i + 1 ≠ t.rows.length) :
    BurnSemantics (envAt t i) := by
  have hlo := (cLo_zero_iff (envAt t i).loc).mp
    (burn_active_gate hash minit mfin maddrs t h i hi hnotlast cLoBody (by simp [burnGates]))
  have hhi := (cHi_zero_iff (envAt t i).loc).mp
    (burn_active_gate hash minit mfin maddrs t h i hi hnotlast cHiBody (by simp [burnGates]))
  have hbor := (cBorrowBool_zero_iff (envAt t i).loc).mp
    (burn_active_gate hash minit mfin maddrs t h i hi hnotlast cBorrowBoolBody (by simp [burnGates]))
  have hwb := (cWasBurnLo_zero_iff (envAt t i).loc).mp
    (burn_active_gate hash minit mfin maddrs t h i hi hnotlast cWasBurnLoBody (by simp [burnGates]))
  have hwh : (envAt t i).loc B_WASBURN_HI = 0 := by
    have := burn_active_gate hash minit mfin maddrs t h i hi hnotlast cWasBurnHiBody (by simp [burnGates])
    simpa [cWasBurnHiBody, EmittedExpr.eval] using this
  refine ⟨?_, hbor, hwb, hwh⟩
  -- combine the two per-limb gates into the u64 balance identity (over ℤ, via omega).
  simp only [TWO_POW_32] at hlo hhi ⊢
  omega

/-! ## §6 — Completeness (SEM ⟹ SAT) for the pure-binding schema, and the full IFF. -/

theorem revoke_memOps : memOpsOf revokeCapabilityDesc = [] := rfl
theorem revoke_mapOps : mapOpsOf revokeCapabilityDesc = [] := rfl

theorem revoke_memLog (t : VmTrace) : memLog revokeCapabilityDesc t = [] := by
  simp only [memLog, revoke_memOps, List.filterMap_nil]
  induction t.rows with
  | nil => simp
  | cons a as ih => simp [ih]

theorem revoke_mapLog (t : VmTrace) : mapLog revokeCapabilityDesc t = [] := by
  simp only [mapLog, revoke_mapOps, List.filterMap_nil]
  induction t.rows with
  | nil => simp
  | cons a as ih => simp [ih]

/-- **`revoke_binds_satisfied2` — completeness.** A binding trace (no memory/map-ops tables) that
binds the published 10-column tuple in every row SATISFIES the whole `revokeCapabilityDesc`. -/
theorem revoke_binds_satisfied2 (t : VmTrace)
    (hmem : t.tf TableId.memory = []) (hmap : t.tf TableId.mapOps = [])
    (hbind : EffectActionBinds t 10) :
    Satisfied2 (fun _ => 0) revokeCapabilityDesc (fun _ => 0) (fun _ => (0, 0)) [] t := by
  refine ⟨?_, ?_, ?_, List.nodup_nil, ?_, ?_, ?_, ?_, ?_⟩
  · -- rowConstraints
    intro i hi c hc
    rw [show revokeCapabilityDesc.constraints = contGates 10 ++ piGates 10 from rfl] at hc
    rcases List.mem_append.mp hc with hcont | hpi
    · obtain ⟨c', hc', rfl⟩ := List.mem_map.mp hcont
      rw [contGate_holdsAt]
      intro hlast
      have hcw : c' < 10 := List.mem_range.mp hc'
      have hi1 : i + 1 < t.rows.length := by have := beq_eq_false_iff_ne.mp hlast; omega
      have hk := hbind i (by omega) c' hcw
      have hk1 := hbind (i + 1) hi1 c' hcw
      simp only [envAt]
      rw [hk1, hk]
    · obtain ⟨c', hc', rfl⟩ := List.mem_map.mp hpi
      rw [piGate_holdsAt]
      intro hfirst
      have hcw : c' < 10 := List.mem_range.mp hc'
      have hi0 : i = 0 := by simpa using hfirst
      subst hi0
      simpa [envAt] using hbind 0 hi c' hcw
  · intro i hi; trivial
  · intro i hi r hr; simp [revokeCapabilityDesc, effectActionDesc] at hr
  · intro op hop; rw [revoke_memLog t] at hop; simp at hop
  · rw [revoke_memLog t]; exact (by decide)
  · rw [revoke_memLog t]; exact memCheck_nil _ _
  · simp [hmem, revoke_memLog]
  · simp [hmap, revoke_mapLog]

/-- **`revoke_satisfied2_iff` — THE full equivalence.** Over a binding trace (no memory/map-ops
tables), the whole `revokeCapabilityDesc` accept-set is EXACTLY the traces that bind the published
10-column revoke-capability tuple in every row. -/
theorem revoke_satisfied2_iff (t : VmTrace)
    (hmem : t.tf TableId.memory = []) (hmap : t.tf TableId.mapOps = []) :
    Satisfied2 (fun _ => 0) revokeCapabilityDesc (fun _ => 0) (fun _ => (0, 0)) [] t
      ↔ EffectActionBinds t 10 := by
  constructor
  · exact effectActionDesc_satisfied2_binds "dregg-effect-revoke-capability-v1" 1 1 _ _ _ _ t
  · exact revoke_binds_satisfied2 t hmem hmap

/-! ## §7 — Non-vacuity (pure binding): a CONCRETE satisfying witness + two failing ones. -/

/-- A concrete published tuple: column `c` holds the distinct value `c`. -/
def demoPub : Assignment := fun c => (c : ℤ)

/-- A concrete satisfying binding trace: two rows, each carrying `demoPub`, published as the PIs. -/
def demoTrace : VmTrace := { rows := [demoPub, demoPub], pub := demoPub, tf := fun _ => [] }

theorem demoTrace_binds : EffectActionBinds demoTrace 10 := by
  intro i hi c _
  have hi2 : i < 2 := hi
  interval_cases i <;> rfl

/-- **Non-vacuity (accept) — the hypothesis is GENUINELY inhabited.** The demo trace SATISFIES the
whole `revokeCapabilityDesc`. -/
theorem demoTrace_satisfied2 :
    Satisfied2 (fun _ => 0) revokeCapabilityDesc (fun _ => 0) (fun _ => (0, 0)) [] demoTrace :=
  revoke_binds_satisfied2 demoTrace rfl rfl demoTrace_binds

/-- The binding bridge fires end-to-end on the concrete witness (SAT ⟹ SEM, non-vacuously). -/
theorem demoTrace_binds_via_bridge : EffectActionBinds demoTrace 10 :=
  effectActionDesc_satisfied2_binds "dregg-effect-revoke-capability-v1" 1 1 _ _ _ _ demoTrace
    demoTrace_satisfied2

/-- A forged row-0 whose limb 0 (`999`) does NOT match the published input (`0`). -/
def brokenBoundRow : Assignment := fun c => if c = 0 then 999 else (c : ℤ)
def brokenBoundTrace : VmTrace := { rows := [brokenBoundRow], pub := demoPub, tf := fun _ => [] }

/-- **Non-vacuity (reject — PI pin BITES).** The forged-limb trace FAILS `Satisfied2`: the column-0
PI pin forces `row0[0] = pub[0]`, i.e. `999 = 0`. -/
theorem brokenBound_rejects :
    ¬ Satisfied2 (fun _ => 0) revokeCapabilityDesc (fun _ => 0) (fun _ => (0, 0)) [] brokenBoundTrace := by
  intro h
  have hpin := h.rowConstraints 0 (by decide) _ (piGate_mem_revoke 0 (by decide))
  rw [piGate_holdsAt] at hpin
  have hbad := hpin rfl
  simp [envAt, brokenBoundTrace, brokenBoundRow, demoPub] at hbad

/-- A padding row (row 1) carrying a DIFFERENT limb 0 (`999`) than row 0 (`0`). -/
def brokenPadRow : Assignment := fun c => if c = 0 then 999 else (c : ℤ)
def brokenPadTrace : VmTrace := { rows := [demoPub, brokenPadRow], pub := demoPub, tf := fun _ => [] }

/-- **Non-vacuity (reject — continuity BITES).** The mismatched-padding trace FAILS `Satisfied2`: the
column-0 continuity gate on row 0 forces `row1[0] = row0[0]`, i.e. `999 = 0` — exactly the "prover
stashes a different tuple in a padding row" attack the descriptor forbids. -/
theorem brokenPad_rejects :
    ¬ Satisfied2 (fun _ => 0) revokeCapabilityDesc (fun _ => 0) (fun _ => (0, 0)) [] brokenPadTrace := by
  intro h
  have hgate := h.rowConstraints 0 (by decide) _ (contGate_mem_revoke 0 (by decide))
  rw [contGate_holdsAt] at hgate
  have hbad := hgate (by decide)
  simp [envAt, brokenPadTrace, brokenPadRow, demoPub] at hbad

/-! ## §8 — Non-vacuity (Burn arithmetic): a CONCRETE burn-valid witness + a failing one. -/

/-- A concrete burn-valid row: `old_balance = 1000`, `amount = 400`, `new_balance = 600`, `borrow = 0`,
`was_burn = 1` — i.e. `600 + 400 = 1000` at limb 0, everything else zero. -/
def burnRow : Assignment := fun c =>
  if c = 8 then 1000 else if c = 10 then 600 else if c = 12 then 400 else if c = 14 then 1 else 0

/-- Both rows carry the burn-valid tuple; published as the PIs. -/
def burnTrace : VmTrace := { rows := [burnRow, burnRow], pub := burnRow, tf := fun _ => [] }

theorem cLo_burnRow : cLoBody.eval burnRow = 0 := by
  rw [cLo_zero_iff]; simp only [B_NEW_LO, B_AMT_LO, B_OLD_LO, B_BORROW, burnRow, TWO_POW_32]; norm_num
theorem cHi_burnRow : cHiBody.eval burnRow = 0 := by
  rw [cHi_zero_iff]; simp only [B_NEW_HI, B_AMT_HI, B_BORROW, B_OLD_HI, burnRow]; norm_num
theorem cBorrowBool_burnRow : cBorrowBoolBody.eval burnRow = 0 := by
  rw [cBorrowBool_zero_iff]; left; simp [B_BORROW, burnRow]
theorem cWasBurnLo_burnRow : cWasBurnLoBody.eval burnRow = 0 := by
  rw [cWasBurnLo_zero_iff]; simp [B_WASBURN_LO, burnRow]
theorem cWasBurnHi_burnRow : cWasBurnHiBody.eval burnRow = 0 := by
  simp [cWasBurnHiBody, EmittedExpr.eval, B_WASBURN_HI, burnRow]

theorem burn_memOps : memOpsOf burnDesc = [] := rfl
theorem burn_mapOps : mapOpsOf burnDesc = [] := rfl

theorem burn_memLog (t : VmTrace) : memLog burnDesc t = [] := by
  simp only [memLog, burn_memOps, List.filterMap_nil]
  induction t.rows with
  | nil => simp
  | cons a as ih => simp [ih]

theorem burn_mapLog (t : VmTrace) : mapLog burnDesc t = [] := by
  simp only [mapLog, burn_mapOps, List.filterMap_nil]
  induction t.rows with
  | nil => simp
  | cons a as ih => simp [ih]

/-- **Non-vacuity (accept) — the Burn hypothesis is GENUINELY inhabited.** The concrete burn-valid
trace SATISFIES the whole arithmetic `burnDesc`: every continuity + PI pin + the FIVE Burn gates. -/
theorem burnTrace_satisfied2 :
    Satisfied2 (fun _ => 0) burnDesc (fun _ => 0) (fun _ => (0, 0)) [] burnTrace := by
  refine ⟨?_, ?_, ?_, List.nodup_nil, ?_, ?_, ?_, ?_, ?_⟩
  · -- rowConstraints
    intro i hi c hc
    rw [show burnDesc.constraints = contGates 17 ++ piGates 16 ++ burnGates from rfl] at hc
    have hi2 : i < 2 := hi
    interval_cases i
    · -- row 0: active + first — every gate fires and holds on the burn-valid row.
      rcases List.mem_append.mp hc with hcp | hburn
      · rcases List.mem_append.mp hcp with hcont | hpi
        · obtain ⟨c', _, rfl⟩ := List.mem_map.mp hcont
          rw [contGate_holdsAt]; intro _; simp [envAt, burnTrace]
        · obtain ⟨c', _, rfl⟩ := List.mem_map.mp hpi
          rw [piGate_holdsAt]; intro _; simp [envAt, burnTrace]
      · fin_cases hburn
        · rw [baseGate_holdsAt]; intro _; exact cLo_burnRow
        · rw [baseGate_holdsAt]; intro _; exact cHi_burnRow
        · rw [baseGate_holdsAt]; intro _; exact cBorrowBool_burnRow
        · rw [baseGate_holdsAt]; intro _; exact cWasBurnLo_burnRow
        · rw [baseGate_holdsAt]; intro _; exact cWasBurnHi_burnRow
    · -- row 1: last row — every gate is vacuous (its guard is false).
      rcases List.mem_append.mp hc with hcp | hburn
      · rcases List.mem_append.mp hcp with hcont | hpi
        · obtain ⟨c', _, rfl⟩ := List.mem_map.mp hcont
          rw [contGate_holdsAt]; intro hl; exact absurd hl (by decide)
        · obtain ⟨c', _, rfl⟩ := List.mem_map.mp hpi
          rw [piGate_holdsAt]; intro hf; exact absurd hf (by decide)
      · fin_cases hburn <;>
          (rw [baseGate_holdsAt]; intro hl; exact absurd hl (by decide))
  · intro i hi; trivial
  · intro i hi r hr; simp [burnDesc] at hr
  · intro op hop; rw [burn_memLog burnTrace] at hop; simp at hop
  · rw [burn_memLog burnTrace]; exact (by decide)
  · rw [burn_memLog burnTrace]; exact memCheck_nil _ _
  · have hm : burnTrace.tf TableId.memory = [] := rfl
    simp [hm, burn_memLog]
  · have hmp : burnTrace.tf TableId.mapOps = [] := rfl
    simp [hmp, burn_mapLog]

/-- The Burn arithmetic bridge fires end-to-end on the concrete witness: row 0 conserves the u64
balance (`600 + 400 = 1000`), the borrow is a bit, and the `was_burn` flag is disclosed. -/
theorem burnTrace_conserves0 : BurnSemantics (envAt burnTrace 0) :=
  burn_satisfied2_conserves (fun _ => 0) (fun _ => 0) (fun _ => (0, 0)) [] burnTrace
    burnTrace_satisfied2 0 (by decide) (by decide)

/-- A broken burn row: `new_lo = 601` so `601 + 400 ≠ 1000` — the low-limb subtraction is violated. -/
def badBurnRow : Assignment := fun c =>
  if c = 8 then 1000 else if c = 10 then 601 else if c = 12 then 400 else if c = 14 then 1 else 0

def badBurnTrace : VmTrace := { rows := [badBurnRow, badBurnRow], pub := badBurnRow, tf := fun _ => [] }

/-- **Non-vacuity (reject — Burn subtraction BITES).** The broken-balance trace FAILS `Satisfied2`:
the low-limb subtraction gate on the active row 0 forces `601 + 400 = 1000`, which is false. -/
theorem badBurn_rejects :
    ¬ Satisfied2 (fun _ => 0) burnDesc (fun _ => 0) (fun _ => (0, 0)) [] badBurnTrace := by
  intro h
  have hbad := burn_active_gate (fun _ => 0) (fun _ => 0) (fun _ => (0, 0)) [] badBurnTrace h
    0 (by decide) (by decide) cLoBody (by simp [burnGates])
  rw [cLo_zero_iff] at hbad
  simp only [envAt, badBurnTrace, badBurnRow, B_NEW_LO, B_AMT_LO, B_OLD_LO, B_BORROW, TWO_POW_32,
    List.getD_cons_zero] at hbad
  norm_num at hbad

/-! ### Shape pins. -/

#guard decide (demoTrace.rows.length = 2)
#guard decide (brokenBoundTrace.rows.length = 1)
#guard decide (brokenPadTrace.rows.length = 2)
#guard decide (burnTrace.rows.length = 2)
#guard decide (badBurnTrace.rows.length = 2)

#assert_axioms binds_of_gates
#assert_axioms effectActionDesc_satisfied2_binds
#assert_axioms burn_satisfied2_binds
#assert_axioms burn_satisfied2_conserves
#assert_axioms revoke_binds_satisfied2
#assert_axioms revoke_satisfied2_iff
#assert_axioms demoTrace_satisfied2
#assert_axioms brokenBound_rejects
#assert_axioms brokenPad_rejects
#assert_axioms burnTrace_satisfied2
#assert_axioms burnTrace_conserves0
#assert_axioms badBurn_rejects

end Dregg2.Circuit.Emit.EffectActionBindingRefine
