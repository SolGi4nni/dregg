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
The binding schema binds an effect's typed parameters into the STARK public inputs at full fidelity
and forces EVERY trace row (row 0 by the PI pins, every padding row by the transition continuity) to
carry EXACTLY that tuple — so a malicious prover cannot stash a different parameter set in a later
row (anti-malleability). The `Burn` schema additionally witnesses the FOUR-limb u64 subtraction
`new_balance == old_balance − amount` (16-bit limbs, `AMOUNT_LIMBS = 4`) with a three-bit borrow
CHAIN, and pins the disclosure flag. The authored functional spec is therefore:

  * `EffectRowBinds row pub P` / `EffectActionBinds t P` — every one of the `P` public-input columns
    of every trace row equals the published input (the faithful-binding / anti-stash relation).
  * `BurnSemantics env` — the FOUR per-limb borrow-chain congruences the Burn schema computes, each
    borrow a bit, and the `was_burn` flag disclosed. ⚑ Stated per-limb and mod `p`, which is exactly
    what a satisfying trace forces on its own.
  * `burn_satisfied2_exact` — and under the NAMED `BurnLimbsCanonical` hypothesis (what a
    `rangeTableDef 16` lookup would discharge), the chain lifts to the EXACT u64 identity
    `old_balance = new_balance + amount` over ℤ, plus `amount ≤ old_balance`. The retired 32-bit-limb
    shape could state neither: its combined relation was a single mod-`p` congruence over a
    recomposition that is not injective into the field.

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
import Dregg2.Circuit.Emit.EffectVmEmitTransfer

namespace Dregg2.Circuit.Emit.EffectActionBindingRefine

open Dregg2.Circuit.Emit.EffectVmEmitTransfer (eqToModEq gate_modEq_iff not_modEq_zero_of_canon pPrimeInt)

open Dregg2.Circuit (Assignment)
open Dregg2.Exec.CircuitEmit (EmittedExpr)
open Dregg2.Circuit.Emit.EffectVmEmit (VmRowEnv VmConstraint VmRow)
open Dregg2.Circuit.DescriptorIR2
  (EffectVmDescriptor2 VmConstraint2 WindowConstraint WindowExpr Satisfied2 VmTrace TraceFamily
   TableId envAt zeroAsg memOpsOf mapOpsOf memLog mapLog opRow memCheck_nil)
open Dregg2.Circuit.Emit.EffectActionBindingEmit
  (contWindowBody contWindowBody_eq contGate contGates piGate piGates effectActionDesc
   revokeCapabilityDesc burnDesc burnGates
   cSub0Body cSub1Body cSub2Body cSub3Body cBoolBody cBoolBody_eq
   cWasBurn0Body cWasBurn1Body cWasBurn2Body cWasBurn3Body
   B_OLD0 B_OLD1 B_OLD2 B_OLD3 B_NEW0 B_NEW1 B_NEW2 B_NEW3 B_AMT0 B_AMT1 B_AMT2 B_AMT3
   B_WB0 B_WB1 B_WB2 B_WB3 B_BRW0 B_BRW1 B_BRW2 LIMB_BASE u64Of BurnLimbsCanonical
   cont_zero_iff cSub0_zero_iff cSub1_zero_iff cSub2_zero_iff cSub3_zero_iff cBool_zero_iff
   cWasBurn0_zero_iff burn_chain_exact_of_modEq burn_no_underflow burn_chain_exact)

set_option autoImplicit false

/-! ## §1 — The authored functional spec. -/

/-- A row BINDS the published tuple: every one of the `P` public-input columns equals the published
input, AS FIELD ELEMENTS (`≡ [ZMOD p]`, `p` the BabyBear prime — the deployed constraint is a field
equality, and two canonical field cells are equal iff congruent mod `p`). The identity-layout face of
"this row carries exactly the effect's typed parameters". -/
def EffectRowBinds (row pub : Assignment) (P : Nat) : Prop :=
  ∀ c, c < P → row c ≡ pub c [ZMOD 2013265921]

/-- **`EffectActionBinds t P`** — THE whole-trace binding relation the effect-action AIR computes:
every row of the trace binds the published `P`-column parameter tuple (anti-stash / anti-malleability
over the FULL trace, not just row 0). -/
def EffectActionBinds (t : VmTrace) (P : Nat) : Prop :=
  ∀ i, i < t.rows.length → EffectRowBinds (t.rows.getD i zeroAsg) t.pub P

/-- **`BurnSemantics env`** — THE relation the `Burn` schema computes on a row: the FOUR per-limb
borrow-chain congruences (16-bit limbs, borrow weight `2^16`), each borrow a field bit, and the
`was_burn` flag disclosed. ⚑ Stated PER LIMB and mod `p` — that is exactly, and only, what a
satisfying trace forces on its own. The lift to a single ℤ identity over the decoded u64s is
`burn_satisfied2_exact`, and it takes `BurnLimbsCanonical` as a NAMED hypothesis. -/
def BurnSemantics (env : VmRowEnv) : Prop :=
  (env.loc B_NEW0 + env.loc B_AMT0
      ≡ env.loc B_OLD0 + LIMB_BASE * env.loc B_BRW0 [ZMOD 2013265921])
  ∧ (env.loc B_NEW1 + env.loc B_AMT1 + env.loc B_BRW0
      ≡ env.loc B_OLD1 + LIMB_BASE * env.loc B_BRW1 [ZMOD 2013265921])
  ∧ (env.loc B_NEW2 + env.loc B_AMT2 + env.loc B_BRW1
      ≡ env.loc B_OLD2 + LIMB_BASE * env.loc B_BRW2 [ZMOD 2013265921])
  ∧ (env.loc B_NEW3 + env.loc B_AMT3 + env.loc B_BRW2 ≡ env.loc B_OLD3 [ZMOD 2013265921])
  ∧ (env.loc B_BRW0 ≡ 0 [ZMOD 2013265921] ∨ env.loc B_BRW0 ≡ 1 [ZMOD 2013265921])
  ∧ (env.loc B_BRW1 ≡ 0 [ZMOD 2013265921] ∨ env.loc B_BRW1 ≡ 1 [ZMOD 2013265921])
  ∧ (env.loc B_BRW2 ≡ 0 [ZMOD 2013265921] ∨ env.loc B_BRW2 ≡ 1 [ZMOD 2013265921])
  ∧ env.loc B_WB0 ≡ 1 [ZMOD 2013265921]
  ∧ env.loc B_WB1 ≡ 0 [ZMOD 2013265921]
  ∧ env.loc B_WB2 ≡ 0 [ZMOD 2013265921]
  ∧ env.loc B_WB3 ≡ 0 [ZMOD 2013265921]

/-! ## §2 — The per-constraint reductions (the STABLE surface to the three gate forms). -/

/-- A PI pin's per-row denotation IS its first-row PI equality (`pi_index == col`). -/
theorem piGate_holdsAt (hash : List ℤ → ℤ) (tf : TraceFamily) (env : VmRowEnv)
    (isFirst isLast : Bool) (c : Nat) :
    (piGate c).holdsAt hash tf env isFirst isLast
      ↔ (isFirst = true → env.loc c ≡ env.pub c [ZMOD 2013265921]) :=
  Iff.rfl

/-- A continuity gate's per-row denotation IS "off the last row, this column chains, mod `p`" — the
`window_gate` asserts `nxt c - loc c ≡ 0 [ZMOD p]`, i.e. the two field cells agree. -/
theorem contGate_holdsAt (hash : List ℤ → ℤ) (tf : TraceFamily) (env : VmRowEnv)
    (isFirst isLast : Bool) (c : Nat) :
    (contGate c).holdsAt hash tf env isFirst isLast
      ↔ (isLast = false → env.nxt c ≡ env.loc c [ZMOD 2013265921]) := by
  simp only [contGate, VmConstraint2.holdsAt, WindowConstraint.holdsAt, if_true]
  constructor
  · intro h hl
    exact (gate_modEq_iff (by simp only [contWindowBody_eq, WindowExpr.eval]; ring)).mp (h hl)
  · intro h hl
    exact (gate_modEq_iff (by simp only [contWindowBody_eq, WindowExpr.eval]; ring)).mpr (h hl)

/-- A Burn algebraic gate's per-row denotation IS "off the last row, this poly vanishes mod `p`" — the
deployed `when_transition()` arm binds it on every active row as a field equality. -/
theorem baseGate_holdsAt (hash : List ℤ → ℤ) (tf : TraceFamily) (env : VmRowEnv)
    (isFirst isLast : Bool) (body : EmittedExpr) :
    (VmConstraint2.base (VmConstraint.gate body)).holdsAt hash tf env isFirst isLast
      ↔ (isLast = false → body.eval env.loc ≡ 0 [ZMOD 2013265921]) := by
  cases isLast <;> simp [VmConstraint2.holdsAt, VmConstraint.holdsVm]

/-! ## §3 — Membership of the two binding families in the descriptors. -/

theorem contGate_mem_effectAction (name : String) (fc ac c : Nat) (hc : c < fc * 8 + ac * 4) :
    contGate c ∈ (effectActionDesc name fc ac).constraints := by
  show contGate c ∈ contGates (fc * 8 + ac * 4) ++ piGates (fc * 8 + ac * 4)
  exact List.mem_append_left _ (List.mem_map.mpr ⟨c, List.mem_range.mpr hc, rfl⟩)

theorem piGate_mem_effectAction (name : String) (fc ac c : Nat) (hc : c < fc * 8 + ac * 4) :
    piGate c ∈ (effectActionDesc name fc ac).constraints := by
  show piGate c ∈ contGates (fc * 8 + ac * 4) ++ piGates (fc * 8 + ac * 4)
  exact List.mem_append_right _ (List.mem_map.mpr ⟨c, List.mem_range.mpr hc, rfl⟩)

theorem contGate_mem_revoke (c : Nat) (hc : c < 12) : contGate c ∈ revokeCapabilityDesc.constraints := by
  show contGate c ∈ contGates 12 ++ piGates 12
  exact List.mem_append_left _ (List.mem_map.mpr ⟨c, List.mem_range.mpr hc, rfl⟩)

theorem piGate_mem_revoke (c : Nat) (hc : c < 12) : piGate c ∈ revokeCapabilityDesc.constraints := by
  show piGate c ∈ contGates 12 ++ piGates 12
  exact List.mem_append_right _ (List.mem_map.mpr ⟨c, List.mem_range.mpr hc, rfl⟩)

theorem contGate_mem_burn (c : Nat) (hc : c < 27) : contGate c ∈ burnDesc.constraints := by
  show contGate c ∈ contGates 27 ++ piGates 24 ++ burnGates
  exact List.mem_append_left _ (List.mem_append_left _ (List.mem_map.mpr ⟨c, List.mem_range.mpr hc, rfl⟩))

theorem piGate_mem_burn (c : Nat) (hc : c < 24) : piGate c ∈ burnDesc.constraints := by
  show piGate c ∈ contGates 27 ++ piGates 24 ++ burnGates
  exact List.mem_append_left _ (List.mem_append_right _ (List.mem_map.mpr ⟨c, List.mem_range.mpr hc, rfl⟩))

theorem burnGate_mem (body : EmittedExpr) (hb : VmConstraint2.base (VmConstraint.gate body) ∈ burnGates) :
    VmConstraint2.base (VmConstraint.gate body) ∈ burnDesc.constraints := by
  show VmConstraint2.base (VmConstraint.gate body) ∈ contGates 27 ++ piGates 24 ++ burnGates
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
    exact hs.trans hk

/-- **`effectActionDesc_satisfied2_binds` — the generic pure-binding soundness bridge.** A trace that
satisfies the whole `effectActionDesc name fc ac` binds the published `fc*8+ac*4`-column parameter
tuple in EVERY row. -/
theorem effectActionDesc_satisfied2_binds (name : String) (fc ac : Nat)
    (hash : List ℤ → ℤ) (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (t : VmTrace)
    (h : Satisfied2 hash (effectActionDesc name fc ac) minit mfin maddrs t) :
    EffectActionBinds t (fc * 8 + ac * 4) :=
  binds_of_gates (fc * 8 + ac * 4) (effectActionDesc name fc ac) hash minit mfin maddrs t h
    (fun c hc => piGate_mem_effectAction name fc ac c hc)
    (fun c hc => contGate_mem_effectAction name fc ac c hc)

/-- **`burn_satisfied2_binds`** — the Burn schema binds its published 24-column tuple in every row. -/
theorem burn_satisfied2_binds
    (hash : List ℤ → ℤ) (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (t : VmTrace)
    (h : Satisfied2 hash burnDesc minit mfin maddrs t) :
    EffectActionBinds t 24 :=
  binds_of_gates 24 burnDesc hash minit mfin maddrs t h
    (fun c hc => piGate_mem_burn c hc)
    (fun c hc => contGate_mem_burn c (by omega))

/-! ## §5 — THE BURN ARITHMETIC BRIDGE (SAT ⟹ SEM): balance conservation on every active row. -/

/-- Any Burn gate forces its body to vanish on an active (non-last) row. -/
theorem burn_active_gate
    (hash : List ℤ → ℤ) (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (t : VmTrace)
    (h : Satisfied2 hash burnDesc minit mfin maddrs t)
    (i : Nat) (hi : i < t.rows.length) (hnotlast : i + 1 ≠ t.rows.length)
    (body : EmittedExpr) (hb : VmConstraint2.base (VmConstraint.gate body) ∈ burnGates) :
    body.eval (envAt t i).loc ≡ 0 [ZMOD 2013265921] := by
  have hrow := h.rowConstraints i hi _ (burnGate_mem body hb)
  rw [baseGate_holdsAt] at hrow
  have hlast : (i + 1 == t.rows.length) = false := by rw [beq_eq_false_iff_ne]; exact hnotlast
  exact hrow hlast

/-- A borrow-bit gate forces the bit to be a FIELD bit: `b·(b−1) ≡ 0` and `p` prime. -/
theorem burn_borrow_bit
    (hash : List ℤ → ℤ) (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (t : VmTrace)
    (h : Satisfied2 hash burnDesc minit mfin maddrs t)
    (i : Nat) (hi : i < t.rows.length) (hnotlast : i + 1 ≠ t.rows.length)
    (b : Nat) (hb : VmConstraint2.base (VmConstraint.gate (cBoolBody b)) ∈ burnGates) :
    (envAt t i).loc b ≡ 0 [ZMOD 2013265921] ∨ (envAt t i).loc b ≡ 1 [ZMOD 2013265921] := by
  have hb0 := burn_active_gate hash minit mfin maddrs t h i hi hnotlast (cBoolBody b) hb
  have hkey : (cBoolBody b).eval (envAt t i).loc
      = (envAt t i).loc b * ((envAt t i).loc b - 1) := by
    simp only [cBoolBody_eq, EmittedExpr.eval]; ring
  rw [hkey, Int.modEq_zero_iff_dvd] at hb0
  rcases pPrimeInt.dvd_mul.mp hb0 with hd | hd
  · exact Or.inl (by rw [Int.modEq_zero_iff_dvd]; exact hd)
  · exact Or.inr (by rw [Int.modEq_iff_dvd]; obtain ⟨k, hk⟩ := hd; exact ⟨-k, by omega⟩)

/-- **`burn_satisfied2_conserves` — THE whole-descriptor Burn functional bridge.** A trace that
satisfies the whole `burnDesc` carries the four per-limb borrow-chain congruences on EVERY active
row, each borrow a field bit, and the `was_burn` disclosure pinned across all four of its limbs. This
composes ALL ELEVEN Burn gates of the whole descriptor into the semantic relation. -/
theorem burn_satisfied2_conserves
    (hash : List ℤ → ℤ) (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (t : VmTrace)
    (h : Satisfied2 hash burnDesc minit mfin maddrs t)
    (i : Nat) (hi : i < t.rows.length) (hnotlast : i + 1 ≠ t.rows.length) :
    BurnSemantics (envAt t i) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (gate_modEq_iff (by simp only [cSub0Body, EmittedExpr.eval, LIMB_BASE]; ring)).mp
      (burn_active_gate hash minit mfin maddrs t h i hi hnotlast cSub0Body (by simp [burnGates]))
  · exact (gate_modEq_iff (by simp only [cSub1Body, EmittedExpr.eval, LIMB_BASE]; ring)).mp
      (burn_active_gate hash minit mfin maddrs t h i hi hnotlast cSub1Body (by simp [burnGates]))
  · exact (gate_modEq_iff (by simp only [cSub2Body, EmittedExpr.eval, LIMB_BASE]; ring)).mp
      (burn_active_gate hash minit mfin maddrs t h i hi hnotlast cSub2Body (by simp [burnGates]))
  · exact (gate_modEq_iff (by simp only [cSub3Body, EmittedExpr.eval]; ring)).mp
      (burn_active_gate hash minit mfin maddrs t h i hi hnotlast cSub3Body (by simp [burnGates]))
  · exact burn_borrow_bit hash minit mfin maddrs t h i hi hnotlast B_BRW0 (by simp [burnGates])
  · exact burn_borrow_bit hash minit mfin maddrs t h i hi hnotlast B_BRW1 (by simp [burnGates])
  · exact burn_borrow_bit hash minit mfin maddrs t h i hi hnotlast B_BRW2 (by simp [burnGates])
  · exact (gate_modEq_iff (by simp only [cWasBurn0Body, EmittedExpr.eval]; ring)).mp
      (burn_active_gate hash minit mfin maddrs t h i hi hnotlast cWasBurn0Body (by simp [burnGates]))
  · simpa [cWasBurn1Body, EmittedExpr.eval] using
      burn_active_gate hash minit mfin maddrs t h i hi hnotlast cWasBurn1Body (by simp [burnGates])
  · simpa [cWasBurn2Body, EmittedExpr.eval] using
      burn_active_gate hash minit mfin maddrs t h i hi hnotlast cWasBurn2Body (by simp [burnGates])
  · simpa [cWasBurn3Body, EmittedExpr.eval] using
      burn_active_gate hash minit mfin maddrs t h i hi hnotlast cWasBurn3Body (by simp [burnGates])

/-- **`burn_satisfied2_exact` — THE ℤ LIFT, and the whole point of the 16-bit encoding.** Under the
NAMED `BurnLimbsCanonical` hypothesis (every chain limb in `[0, 2^16)`, every borrow a bit — what a
`rangeTableDef 16` lookup on the twelve chain limbs would discharge in-circuit), a satisfying trace
forces the EXACT u64 identity `old_balance = new_balance + amount` over ℤ on the DECODED values, and
`amount ≤ old_balance`.

⚑ The hypothesis is load-bearing and is NOT free: nothing in `burnDesc` pins a limb to `[0, 2^16)`.
It is stated, never assumed. What the retired 32-bit shape had instead was a single mod-`p`
congruence over `lo + 2^32·hi` — a recomposition that is not injective into the field, so NO
canonicality hypothesis could have lifted it to a `2^64` ℤ statement. -/
theorem burn_satisfied2_exact
    (hash : List ℤ → ℤ) (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (t : VmTrace)
    (h : Satisfied2 hash burnDesc minit mfin maddrs t)
    (i : Nat) (hi : i < t.rows.length) (hnotlast : i + 1 ≠ t.rows.length)
    (hcanon : BurnLimbsCanonical (envAt t i).loc) :
    u64Of ((envAt t i).loc B_OLD0) ((envAt t i).loc B_OLD1) ((envAt t i).loc B_OLD2)
        ((envAt t i).loc B_OLD3)
      = u64Of ((envAt t i).loc B_NEW0) ((envAt t i).loc B_NEW1) ((envAt t i).loc B_NEW2)
          ((envAt t i).loc B_NEW3)
        + u64Of ((envAt t i).loc B_AMT0) ((envAt t i).loc B_AMT1) ((envAt t i).loc B_AMT2)
            ((envAt t i).loc B_AMT3) :=
  burn_chain_exact_of_modEq (envAt t i).loc hcanon
    (burn_active_gate hash minit mfin maddrs t h i hi hnotlast cSub0Body (by simp [burnGates]))
    (burn_active_gate hash minit mfin maddrs t h i hi hnotlast cSub1Body (by simp [burnGates]))
    (burn_active_gate hash minit mfin maddrs t h i hi hnotlast cSub2Body (by simp [burnGates]))
    (burn_active_gate hash minit mfin maddrs t h i hi hnotlast cSub3Body (by simp [burnGates]))

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
binds the published 12-column tuple in every row SATISFIES the whole `revokeCapabilityDesc`. -/
theorem revoke_binds_satisfied2 (t : VmTrace)
    (hmem : t.tf TableId.memory = []) (hmap : t.tf TableId.mapOps = [])
    (hbind : EffectActionBinds t 12) :
    Satisfied2 (fun _ => 0) revokeCapabilityDesc (fun _ => 0) (fun _ => (0, 0)) [] t := by
  refine ⟨?_, ?_, ?_, List.nodup_nil, ?_, ?_, ?_, ?_, ?_⟩
  · -- rowConstraints
    intro i hi c hc
    rw [show revokeCapabilityDesc.constraints = contGates 12 ++ piGates 12 from rfl] at hc
    rcases List.mem_append.mp hc with hcont | hpi
    · obtain ⟨c', hc', rfl⟩ := List.mem_map.mp hcont
      rw [contGate_holdsAt]
      intro hlast
      have hcw : c' < 12 := List.mem_range.mp hc'
      have hi1 : i + 1 < t.rows.length := by have := beq_eq_false_iff_ne.mp hlast; omega
      have hk := hbind i (by omega) c' hcw
      have hk1 := hbind (i + 1) hi1 c' hcw
      simp only [envAt]
      exact hk1.trans hk.symm
    · obtain ⟨c', hc', rfl⟩ := List.mem_map.mp hpi
      rw [piGate_holdsAt]
      intro hfirst
      have hcw : c' < 12 := List.mem_range.mp hc'
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
12-column revoke-capability tuple in every row. -/
theorem revoke_satisfied2_iff (t : VmTrace)
    (hmem : t.tf TableId.memory = []) (hmap : t.tf TableId.mapOps = []) :
    Satisfied2 (fun _ => 0) revokeCapabilityDesc (fun _ => 0) (fun _ => (0, 0)) [] t
      ↔ EffectActionBinds t 12 := by
  constructor
  · exact effectActionDesc_satisfied2_binds "dregg-effect-revoke-capability-v1" 1 1 _ _ _ _ t
  · exact revoke_binds_satisfied2 t hmem hmap

/-! ## §7 — Non-vacuity (pure binding): a CONCRETE satisfying witness + two failing ones. -/

/-- A concrete published tuple: column `c` holds the distinct value `c`. -/
def demoPub : Assignment := fun c => (c : ℤ)

/-- A concrete satisfying binding trace: two rows, each carrying `demoPub`, published as the PIs. -/
def demoTrace : VmTrace := { rows := [demoPub, demoPub], pub := demoPub, tf := fun _ => [] }

theorem demoTrace_binds : EffectActionBinds demoTrace 12 := by
  intro i hi c _
  have hi2 : i < 2 := hi
  interval_cases i <;> rfl

/-- **Non-vacuity (accept) — the hypothesis is GENUINELY inhabited.** The demo trace SATISFIES the
whole `revokeCapabilityDesc`. -/
theorem demoTrace_satisfied2 :
    Satisfied2 (fun _ => 0) revokeCapabilityDesc (fun _ => 0) (fun _ => (0, 0)) [] demoTrace :=
  revoke_binds_satisfied2 demoTrace rfl rfl demoTrace_binds

/-- The binding bridge fires end-to-end on the concrete witness (SAT ⟹ SEM, non-vacuously). -/
theorem demoTrace_binds_via_bridge : EffectActionBinds demoTrace 12 :=
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
  -- field-faithful reject: `999 ≢ 0 [ZMOD p]` because `0 < 999 < p` so `p ∤ 999`.
  have hl : (envAt brokenBoundTrace 0).loc 0 = 999 := rfl
  have hp : (envAt brokenBoundTrace 0).pub 0 = 0 := rfl
  rw [Int.modEq_iff_dvd, hl, hp] at hbad
  omega

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
  -- field-faithful reject: `999 ≢ 0 [ZMOD p]` (the stashed padding limb differs by `< p`).
  have hn : (envAt brokenPadTrace 0).nxt 0 = 999 := rfl
  have hl : (envAt brokenPadTrace 0).loc 0 = 0 := rfl
  rw [Int.modEq_iff_dvd, hn, hl] at hbad
  omega

/-! ## §8 — Non-vacuity (Burn arithmetic): a CONCRETE burn-valid witness + a failing one. -/

/-- A concrete burn-valid row: `old_balance = 65536` (limb1 = 1), `amount = 1`, `new_balance = 65535`,
`was_burn = 1`. ⚑ The low limb UNDERFLOWS (`65535 + 1 = 65536`), so `b_0 = 1`: the borrow chain is
genuinely EXERCISED by this witness, not satisfied by pinning every borrow to zero. -/
def burnRow : Assignment := fun c =>
  if c = B_OLD1 then 1 else if c = B_NEW0 then 65535 else if c = B_AMT0 then 1
  else if c = B_BRW0 then 1 else if c = B_WB0 then 1 else 0

/-- Both rows carry the burn-valid tuple; published as the PIs. -/
def burnTrace : VmTrace := { rows := [burnRow, burnRow], pub := burnRow, tf := fun _ => [] }

theorem burnRow_gates : cSub0Body.eval burnRow = 0 ∧ cSub1Body.eval burnRow = 0
    ∧ cSub2Body.eval burnRow = 0 ∧ cSub3Body.eval burnRow = 0
    ∧ (cBoolBody B_BRW0).eval burnRow = 0 ∧ (cBoolBody B_BRW1).eval burnRow = 0
    ∧ (cBoolBody B_BRW2).eval burnRow = 0
    ∧ cWasBurn0Body.eval burnRow = 0 ∧ cWasBurn1Body.eval burnRow = 0
    ∧ cWasBurn2Body.eval burnRow = 0 ∧ cWasBurn3Body.eval burnRow = 0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

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
    rw [show burnDesc.constraints = contGates 27 ++ piGates 24 ++ burnGates from rfl] at hc
    have hi2 : i < 2 := hi
    interval_cases i
    · -- row 0: active + first — every gate fires and holds on the burn-valid row.
      rcases List.mem_append.mp hc with hcp | hburn
      · rcases List.mem_append.mp hcp with hcont | hpi
        · obtain ⟨c', _, rfl⟩ := List.mem_map.mp hcont
          rw [contGate_holdsAt]; intro _; apply eqToModEq; simp [envAt, burnTrace]
        · obtain ⟨c', _, rfl⟩ := List.mem_map.mp hpi
          rw [piGate_holdsAt]; intro _; apply eqToModEq; simp [envAt, burnTrace]
      · fin_cases hburn
        · rw [baseGate_holdsAt]; intro _; exact eqToModEq burnRow_gates.1
        · rw [baseGate_holdsAt]; intro _; exact eqToModEq burnRow_gates.2.1
        · rw [baseGate_holdsAt]; intro _; exact eqToModEq burnRow_gates.2.2.1
        · rw [baseGate_holdsAt]; intro _; exact eqToModEq burnRow_gates.2.2.2.1
        · rw [baseGate_holdsAt]; intro _; exact eqToModEq burnRow_gates.2.2.2.2.1
        · rw [baseGate_holdsAt]; intro _; exact eqToModEq burnRow_gates.2.2.2.2.2.1
        · rw [baseGate_holdsAt]; intro _; exact eqToModEq burnRow_gates.2.2.2.2.2.2.1
        · rw [baseGate_holdsAt]; intro _; exact eqToModEq burnRow_gates.2.2.2.2.2.2.2.1
        · rw [baseGate_holdsAt]; intro _; exact eqToModEq burnRow_gates.2.2.2.2.2.2.2.2.1
        · rw [baseGate_holdsAt]; intro _; exact eqToModEq burnRow_gates.2.2.2.2.2.2.2.2.2.1
        · rw [baseGate_holdsAt]; intro _; exact eqToModEq burnRow_gates.2.2.2.2.2.2.2.2.2.2
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

/-- The Burn arithmetic bridge fires end-to-end on the concrete witness: row 0 carries the four
chain congruences, the three borrows are bits, and the `was_burn` flag is disclosed. -/
theorem burnTrace_conserves0 : BurnSemantics (envAt burnTrace 0) :=
  burn_satisfied2_conserves (fun _ => 0) (fun _ => 0) (fun _ => (0, 0)) [] burnTrace
    burnTrace_satisfied2 0 (by decide) (by decide)

/-- The row is canonical (every chain limb `< 2^16`, every borrow a bit). -/
theorem burnRow_canonical : BurnLimbsCanonical burnRow := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> [skip; decide; decide; decide]
  intro c hc
  rcases hc with h|h|h|h|h|h|h|h|h|h|h|h <;> subst h <;> exact ⟨by decide, by decide⟩

/-- **THE ℤ LIFT FIRES, ACROSS A LIMB BOUNDARY, ON A REAL BURN.** `65536 = 65535 + 1` is recovered as
an EXACT integer identity on the decoded u64s — with the borrow bit doing genuine work. This is the
statement the retired 32-bit encoding could not make at any resolution. -/
theorem burnTrace_exact0 :
    u64Of ((envAt burnTrace 0).loc B_OLD0) ((envAt burnTrace 0).loc B_OLD1)
        ((envAt burnTrace 0).loc B_OLD2) ((envAt burnTrace 0).loc B_OLD3)
      = u64Of ((envAt burnTrace 0).loc B_NEW0) ((envAt burnTrace 0).loc B_NEW1)
          ((envAt burnTrace 0).loc B_NEW2) ((envAt burnTrace 0).loc B_NEW3)
        + u64Of ((envAt burnTrace 0).loc B_AMT0) ((envAt burnTrace 0).loc B_AMT1)
            ((envAt burnTrace 0).loc B_AMT2) ((envAt burnTrace 0).loc B_AMT3) :=
  burn_satisfied2_exact (fun _ => 0) (fun _ => 0) (fun _ => (0, 0)) [] burnTrace
    burnTrace_satisfied2 0 (by decide) (by decide) burnRow_canonical

/-- …and the recovered values are GENUINE (`65536 = 65535 + 1`), not a trivial `0 = 0`. -/
theorem burnTrace_exact_values :
    u64Of ((envAt burnTrace 0).loc B_OLD0) ((envAt burnTrace 0).loc B_OLD1)
        ((envAt burnTrace 0).loc B_OLD2) ((envAt burnTrace 0).loc B_OLD3) = 65536
    ∧ u64Of ((envAt burnTrace 0).loc B_NEW0) ((envAt burnTrace 0).loc B_NEW1)
        ((envAt burnTrace 0).loc B_NEW2) ((envAt burnTrace 0).loc B_NEW3) = 65535 := by
  refine ⟨?_, ?_⟩ <;> decide

/-- ⚑ **A FORGED BORROW.** The honest row with `b_1` conjured to `1` while every limb is unchanged:
the limb-1 chain gate no longer closes. This is the exact forgery the felt-sized borrow weight exists
to refuse — a prover fabricating `2^16` of balance out of a free aux bit. -/
def badBurnRow : Assignment := fun c => if c = B_BRW1 then 1 else burnRow c

def badBurnTrace : VmTrace := { rows := [badBurnRow, badBurnRow], pub := badBurnRow, tf := fun _ => [] }

/-- **Non-vacuity (reject — THE FORGED BORROW BITES).** The forged-borrow trace FAILS `Satisfied2`:
the limb-1 chain gate on the active row 0 residual is `−65536`, and `p ∤ 65536`. -/
theorem badBurn_rejects :
    ¬ Satisfied2 (fun _ => 0) burnDesc (fun _ => 0) (fun _ => (0, 0)) [] badBurnTrace := by
  intro h
  have hbad := burn_active_gate (fun _ => 0) (fun _ => 0) (fun _ => (0, 0)) [] badBurnTrace h
    0 (by decide) (by decide) cSub1Body (by simp [burnGates])
  have hv : cSub1Body.eval (envAt badBurnTrace 0).loc = -65536 := rfl
  rw [Int.modEq_iff_dvd, hv] at hbad
  omega

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
#assert_axioms burn_satisfied2_exact
#assert_axioms burnTrace_exact0
#assert_axioms burnTrace_exact_values
#assert_axioms burnRow_canonical
#assert_axioms revoke_binds_satisfied2
#assert_axioms revoke_satisfied2_iff
#assert_axioms demoTrace_satisfied2
#assert_axioms brokenBound_rejects
#assert_axioms brokenPad_rejects
#assert_axioms burnTrace_satisfied2
#assert_axioms burnTrace_conserves0
#assert_axioms badBurn_rejects

end Dregg2.Circuit.Emit.EffectActionBindingRefine
