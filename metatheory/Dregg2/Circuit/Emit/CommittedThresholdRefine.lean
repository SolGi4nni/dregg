/-
# Dregg2.Circuit.Emit.CommittedThresholdRefine — the WHOLE-DESCRIPTOR functional-correctness bridge
for the committed-threshold predicate family.

`CommittedThresholdEmit` byte-pins the descriptor and proves per-GATE lemmas
(`binary_body_zero_iff`, `diff_body_zero_iff`). This file composes those gates into the
WHOLE-descriptor bridge: a trace `Satisfied2` of `committedThresholdDesc` corresponds to the GENUINE
semantic relation the circuit is meant to compute — "the private value meets the committed threshold,
and the public threshold-commitment is a genuine Poseidon2 preimage of `(threshold, blinding)`."

## The semantic relation (`MeetsCommittedThreshold`)

At the active row environment `e`, given the abstract Poseidon2 `hash`:
  * ORDER      — `e.loc THRESHOLD ≤ e.loc PRIVATE_VALUE`  (value ≥ threshold);
  * BINDING    — `e.loc THRESHOLD_COMMITMENT = hash [e.loc THRESHOLD, e.loc BLINDING]`
                 (the public commitment is a genuine hash preimage — the load-bearing soundness fix);
  * PI         — `e.loc THRESHOLD_COMMITMENT = e.pub 0` and `e.loc FACT_COMMITMENT = e.pub 1`.

## The weld (SPEC_EXISTS_NO_EMIT → existing model's conclusions)

The ORDER side welds to `Dregg2.Exec.RecordCircuit.range_proves_le` — the EXACT lemma
`Crypto/RangeProof.lean`'s `range_sound_step` uses (booleanity + recomposition of `value − threshold`
⟹ `threshold ≤ value`). The BINDING side welds to `DescriptorIR2.chip_lookup_sound` (a sound Poseidon2
chip table forces the digest column to the genuine hash of the inputs).

## Direction

SAT_IMPLIES_SEM (soundness): `Satisfied2 … ⟹ MeetsCommittedThreshold …`. The ORDER + PI legs need NO
crypto carrier (pure algebra over the boolean bits + the PI pins). The BINDING leg rides the NAMED
`ChipTableSound hash (t.tf .poseidon2)` carrier (Poseidon2 collision-resistance family), passed as a
hypothesis — never a Lean axiom.

## Axiom hygiene

`#assert_axioms` ⊆ {propext, Classical.choice, Quot.sound}; the ONLY cryptographic residue is the
NAMED `ChipTableSound` hypothesis (Poseidon2 CR). NEW file; imports read-only.
-/
import Dregg2.Circuit.Emit.CommittedThresholdEmit
import Dregg2.Exec.RecordCircuit

namespace Dregg2.Circuit.Emit.CommittedThresholdRefine

open Dregg2.Circuit (Assignment)
open Dregg2.Exec.CircuitEmit (EmittedExpr)
open Dregg2.Circuit.Emit.EffectVmEmit (VmRowEnv VmConstraint VmRow)
open Dregg2.Circuit.DescriptorIR2
  (EffectVmDescriptor2 VmConstraint2 Satisfied2 VmTrace TraceFamily envAt Lookup
   ChipTableSound chip_lookup_sound chipLookupTuple chipRow CHIP_RATE CHIP_OUT_LANES)
open Dregg2.Circuit.Emit.CommittedThresholdEmit
open Dregg2.Exec.RecordCircuit (bitsToInt Boolean range_sound range_proves_le)

set_option autoImplicit false

/-! ## §1 — The recomposition-gate arithmetic: the emitted fold IS `bitsToInt` over the bit columns.

The recomposition gate body is `Σ_{i<30} 2^i·bit_i − diff`. §1 proves that the emitted right-fold
equals `bitsToInt [bit_0, …, bit_29] − diff`, so a satisfied recomposition gate says exactly
`bitsToInt (the bit columns) = diff`. This is the bridge from the wire-form fold to the
`RecordCircuit` range-gadget denotation. Pure algebra — no descriptor, no carrier. -/

/-- `pow2` (the emit file's kernel-reducible power) IS `2 ^ ·`. -/
theorem pow2_eq (n : Nat) : pow2 n = 2 ^ n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [pow2, ih, pow_succ]; ring

/-- Appending a HIGH bit `y` past a little-endian bit list adds it at weight `2 ^ |xs|`. -/
theorem bitsToInt_append_singleton (xs : List ℤ) (y : ℤ) :
    bitsToInt (xs ++ [y]) = bitsToInt xs + 2 ^ xs.length * y := by
  induction xs with
  | nil => simp [bitsToInt]
  | cons b rest ih =>
    simp only [List.cons_append, bitsToInt, ih, List.length_cons, pow_succ]
    ring

/-- The pow2-weighted sum over `range n` equals `bitsToInt` of the mapped bit list. -/
theorem sum_pow2_eq_bitsToInt (n : Nat) (w : Nat → ℤ) :
    ((List.range n).map (fun i => pow2 i * w i)).sum = bitsToInt ((List.range n).map w) := by
  induction n generalizing w with
  | zero => simp [bitsToInt]
  | succ n ih =>
    simp only [List.range_succ, List.map_append, List.sum_append, List.map_cons, List.map_nil,
      List.sum_cons, List.sum_nil, add_zero]
    rw [ih w, bitsToInt_append_singleton, List.length_map, List.length_range, pow2_eq]

/-- The emitted right-fold over any index list evaluates to the pow2-weighted sum plus the tail. -/
theorem fold_eval (l : List Nat) (tail : EmittedExpr) (a : Assignment) :
    (l.foldr (fun i acc => EmittedExpr.add (.mul (.const (pow2 i)) (.var (diffBit i))) acc) tail).eval a
      = (l.map (fun i => pow2 i * a (diffBit i))).sum + tail.eval a := by
  induction l with
  | nil => simp only [List.foldr_nil, List.map_nil, List.sum_nil, zero_add]
  | cons x xs ih =>
    simp only [List.foldr_cons, EmittedExpr.eval, ih, List.map_cons, List.sum_cons]
    ring

/-- The bit columns of a row, as a `List ℤ` (the 30-bit little-endian decomposition witness). -/
def bitVals (a : Assignment) : List ℤ := (List.range COMMITTED_DIFF_BITS).map (fun i => a (diffBit i))

/-- **The recomposition gate body IS `bitsToInt (bit columns) − diff`.** So the emitted recomposition
gate vanishing says exactly `bitsToInt (bit columns) = diff`. -/
theorem recomp_eval (a : Assignment) :
    recompBody.eval a = bitsToInt (bitVals a) - a DIFF := by
  rw [recompBody, fold_eval, sum_pow2_eq_bitsToInt COMMITTED_DIFF_BITS (fun i => a (diffBit i))]
  simp only [bitVals, EmittedExpr.eval]
  ring

/-! ## §2 — Membership of each descriptor gate in `committedThresholdDesc.constraints`. -/

-- The descriptor is `core ++ ctLastGateFix`, `core = ([lookup, gate c3, gate c4, gate recomp] ++
-- binaryGates ++ [pi0, pi1, gate highbit])` (left-assoc). Navigation strips the outer `++
-- ctLastGateFix` (one extra `mem_append_left`) before reaching the `core` legs; the last-row lemmas
-- take `mem_append_right` into `ctLastGateFix`.

theorem mem_lookup : hash2Lookup ∈ committedThresholdDesc.constraints := by
  simp only [committedThresholdDesc]
  apply List.mem_append_left; apply List.mem_append_left; apply List.mem_append_left
  apply List.mem_cons_self

theorem mem_factHash : factHashLookup ∈ committedThresholdDesc.constraints := by
  simp only [committedThresholdDesc]
  apply List.mem_append_left; apply List.mem_append_left; apply List.mem_append_left
  apply List.mem_cons_of_mem; apply List.mem_cons_self

theorem mem_factCommit : factCommitLookup ∈ committedThresholdDesc.constraints := by
  simp only [committedThresholdDesc]
  apply List.mem_append_left; apply List.mem_append_left; apply List.mem_append_left
  apply List.mem_cons_of_mem; apply List.mem_cons_of_mem; apply List.mem_cons_self

theorem mem_c3 : VmConstraint2.base (.gate c3Body) ∈ committedThresholdDesc.constraints := by
  simp only [committedThresholdDesc]
  apply List.mem_append_left; apply List.mem_append_left; apply List.mem_append_left
  apply List.mem_cons_of_mem; apply List.mem_cons_of_mem; apply List.mem_cons_of_mem
  apply List.mem_cons_self

theorem mem_c4 : VmConstraint2.base (.gate c4Body) ∈ committedThresholdDesc.constraints := by
  simp only [committedThresholdDesc]
  apply List.mem_append_left; apply List.mem_append_left; apply List.mem_append_left
  apply List.mem_cons_of_mem; apply List.mem_cons_of_mem; apply List.mem_cons_of_mem
  apply List.mem_cons_of_mem; apply List.mem_cons_self

theorem mem_recomp : VmConstraint2.base (.gate recompBody) ∈ committedThresholdDesc.constraints := by
  simp only [committedThresholdDesc]
  apply List.mem_append_left; apply List.mem_append_left; apply List.mem_append_left
  apply List.mem_cons_of_mem; apply List.mem_cons_of_mem; apply List.mem_cons_of_mem
  apply List.mem_cons_of_mem; apply List.mem_cons_of_mem; apply List.mem_cons_self

theorem mem_bin (j : Nat) (hj : j < COMMITTED_DIFF_BITS) :
    VmConstraint2.base (.gate (binBody j)) ∈ committedThresholdDesc.constraints := by
  simp only [committedThresholdDesc]
  apply List.mem_append_left; apply List.mem_append_left; apply List.mem_append_right
  simp only [binaryGates]
  exact List.mem_map.mpr ⟨j, List.mem_range.mpr hj, rfl⟩

theorem mem_pi0 :
    VmConstraint2.base (.piBinding VmRow.first THRESHOLD_COMMITMENT 0)
      ∈ committedThresholdDesc.constraints := by
  simp only [committedThresholdDesc]
  apply List.mem_append_left; apply List.mem_append_right; apply List.mem_cons_self

theorem mem_pi1 :
    VmConstraint2.base (.piBinding VmRow.first FACT_COMMITMENT 1)
      ∈ committedThresholdDesc.constraints := by
  simp only [committedThresholdDesc]
  apply List.mem_append_left; apply List.mem_append_right
  apply List.mem_cons_of_mem; apply List.mem_cons_self

/-! The last-row fix (`ctLastGateFix`) memberships: `ctLastGateFix = [bnd c3, bnd c4, bnd recomp] ++
(range).map (bnd ∘ binBody) ++ [bnd highbit]` sits at the RIGHT of the descriptor append. -/

theorem mem_c3_last :
    VmConstraint2.base (.boundary VmRow.last c3Body) ∈ committedThresholdDesc.constraints := by
  simp only [committedThresholdDesc, ctLastGateFix]
  apply List.mem_append_right; apply List.mem_append_left; apply List.mem_append_left
  apply List.mem_cons_self

theorem mem_c4_last :
    VmConstraint2.base (.boundary VmRow.last c4Body) ∈ committedThresholdDesc.constraints := by
  simp only [committedThresholdDesc, ctLastGateFix]
  apply List.mem_append_right; apply List.mem_append_left; apply List.mem_append_left
  apply List.mem_cons_of_mem; apply List.mem_cons_self

theorem mem_recomp_last :
    VmConstraint2.base (.boundary VmRow.last recompBody) ∈ committedThresholdDesc.constraints := by
  simp only [committedThresholdDesc, ctLastGateFix]
  apply List.mem_append_right; apply List.mem_append_left; apply List.mem_append_left
  apply List.mem_cons_of_mem; apply List.mem_cons_of_mem; apply List.mem_cons_self

theorem mem_bin_last (j : Nat) (hj : j < COMMITTED_DIFF_BITS) :
    VmConstraint2.base (.boundary VmRow.last (binBody j)) ∈ committedThresholdDesc.constraints := by
  simp only [committedThresholdDesc, ctLastGateFix]
  apply List.mem_append_right; apply List.mem_append_left; apply List.mem_append_right
  exact List.mem_map.mpr ⟨j, List.mem_range.mpr hj, rfl⟩

/-! ## §3 — The whole-descriptor soundness bridge. -/

/-- **`MeetsCommittedThreshold hash e`** — the genuine semantic relation the committed-threshold
circuit computes at a row environment `e` (given the abstract Poseidon2 `hash`): the private value
meets the committed threshold (`THRESHOLD ≤ PRIVATE_VALUE`), the public threshold commitment is a
genuine hash preimage of `(threshold, blinding)`, and the two commitments are the public inputs. -/
def MeetsCommittedThreshold (hash : List ℤ → ℤ) (e : VmRowEnv) : Prop :=
  e.loc THRESHOLD ≤ e.loc PRIVATE_VALUE
  ∧ e.loc THRESHOLD_COMMITMENT = hash [e.loc THRESHOLD, e.loc BLINDING]
  ∧ e.loc THRESHOLD_COMMITMENT = e.pub 0
  ∧ e.loc FACT_COMMITMENT = e.pub 1
  -- THE VALUE↔FACT WELD (held forgery #2): the committed fact commitment opens, in-circuit, to a
  -- `hash_fact` of a fact whose VALUE slot is the SAME `PRIVATE_VALUE` column the ORDER leg bounds —
  -- bound with `state_root`. So the value proven `≥ threshold` IS the value inside the committed fact
  -- (Poseidon2 collision resistance, the named chip carrier). `FACT_MARK`, `0`, `1` are `hash_fact`'s
  -- domain constants (`state[4]=0, state[5]=0xFACF, state[6]=1`).
  ∧ e.loc FACT_HASH = hash [e.loc PREDICATE_SYM, e.loc PRIVATE_VALUE, e.loc TERM1, e.loc TERM2,
                            0, FACT_MARK, 1]
  ∧ e.loc FACT_COMMITMENT = hash [e.loc FACT_HASH, e.loc STATE_ROOT]

/-- **THE WHOLE-DESCRIPTOR BRIDGE (SAT_IMPLIES_SEM).** A multi-table witness that `Satisfied2` the
committed-threshold descriptor, against a SOUND Poseidon2 chip table (the NAMED `ChipTableSound`
carrier — Poseidon2 collision-resistance) on ANY non-empty trace (`0 < rows.length` — INCLUDING a
height-1 trace, where row 0 IS the last row), forces the genuine semantic relation on row 0: the
private value meets the committed threshold, the public commitment is a genuine hash preimage, and the
commitments are the public inputs.

⚑ The height-1 coverage is the FIX (the `ctLastGateFix` last-row re-lowering): the semantic gates are
transition-only `.base (.gate …)`, VACUOUS on the last row (`holdsVm … isLast=true (.gate _) = True`),
so on a height-1 trace they would drop the whole range/diff/binding chain. Each is now ALSO emitted as
`.base (.boundary VmRow.last …)`, so `gate_forces` derives `body = 0` on row 0 in BOTH cases (via the
`.gate` when row 0 is not last, via the last-row boundary when it is). This is exactly what closes the
forgery the older `1 < rows.length` bridge could not rule out.

The ORDER leg composes `diff_body_zero_iff` + `binary_body_zero_iff` + the recomposition-fold algebra
(`recomp_eval`) into `RecordCircuit.range_proves_le` — the EXACT conclusion `Crypto/RangeProof.lean`
derives. The BINDING leg rides `chip_lookup_sound` + the equality gate `c3`. The PI leg reads the two
`piBinding` pins. Whole descriptor, not a single gate. -/
theorem committedThreshold_satisfied2_sound
    (hash : List ℤ → ℤ) (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (t : VmTrace)
    (hChip : ChipTableSound hash (t.tf .poseidon2))
    (hsat : Satisfied2 hash committedThresholdDesc minit mfin maddrs t)
    (hlen : 0 < t.rows.length) :
    MeetsCommittedThreshold hash (envAt t 0) := by
  have hi0 : 0 < t.rows.length := hlen
  -- every semantic gate forces its body to vanish on row 0 — via the transition `.gate` when row 0 is
  -- NOT the last row, and via its `.boundary VmRow.last` counterpart (the `ctLastGateFix` fix) when it
  -- IS. So the range/diff/binding chain binds on row 0 for EVERY trace height, including height-1.
  have gate_forces : ∀ g : EmittedExpr,
      VmConstraint2.base (.gate g) ∈ committedThresholdDesc.constraints →
      VmConstraint2.base (.boundary VmRow.last g) ∈ committedThresholdDesc.constraints →
      g.eval (envAt t 0).loc = 0 := by
    intro g hgate hbnd
    by_cases hlast : (0 + 1 == t.rows.length) = true
    · -- row 0 IS the last row (height-1 trace): the last-row boundary fires.
      have h := hsat.rowConstraints 0 hi0 _ hbnd
      simp only [VmConstraint2.holdsAt, VmConstraint.holdsVm] at h
      exact h hlast
    · -- row 0 is NOT the last row: the transition `.gate` fires.
      have hfalse : (0 + 1 == t.rows.length) = false := by
        simp only [Bool.not_eq_true] at hlast; exact hlast
      have h := hsat.rowConstraints 0 hi0 _ hgate
      simp only [VmConstraint2.holdsAt, VmConstraint.holdsVm, hfalse] at h
      exact h
  -- the two PI pins bind on the first row.
  have pi_forces : ∀ (col k : Nat),
      VmConstraint2.base (.piBinding VmRow.first col k) ∈ committedThresholdDesc.constraints →
      (envAt t 0).loc col = (envAt t 0).pub k := by
    intro col k hmem
    have h := hsat.rowConstraints 0 hi0 _ hmem
    simp only [VmConstraint2.holdsAt, VmConstraint.holdsVm] at h
    exact h rfl
  -- === ORDER: threshold ≤ value, welded to RecordCircuit.range_proves_le ===
  have hdiff : (envAt t 0).loc DIFF
      = (envAt t 0).loc PRIVATE_VALUE - (envAt t 0).loc THRESHOLD :=
    (diff_body_zero_iff (envAt t 0).loc).mp (gate_forces c4Body mem_c4 mem_c4_last)
  have hrec : bitsToInt (bitVals (envAt t 0).loc) = (envAt t 0).loc DIFF := by
    have h := recomp_eval (envAt t 0).loc
    rw [gate_forces recompBody mem_recomp mem_recomp_last] at h
    omega
  have hbool : Boolean (bitVals (envAt t 0).loc) := by
    intro b hb
    simp only [bitVals, List.mem_map, List.mem_range] at hb
    obtain ⟨j, hj, rfl⟩ := hb
    exact (binary_body_zero_iff j (envAt t 0).loc).mp
      (gate_forces (binBody j) (mem_bin j hj) (mem_bin_last j hj))
  have horder : (envAt t 0).loc THRESHOLD ≤ (envAt t 0).loc PRIVATE_VALUE :=
    range_proves_le _ _ (bitVals (envAt t 0).loc) hbool (hrec.trans hdiff)
  -- === BINDING: threshold_commitment = hash(threshold, blinding), welded to chip_lookup_sound ===
  have hlook := hsat.rowConstraints 0 hi0 hash2Lookup mem_lookup
  simp only [VmConstraint2.holdsAt, hash2Lookup, Lookup.holdsAt] at hlook
  have hdig := chip_lookup_sound hash (t.tf .poseidon2) hChip (envAt t 0).loc
    [.var THRESHOLD, .var BLINDING] POSEIDON2_RESULT CHIP_LANES (by decide) hlook
  simp only [List.map_cons, List.map_nil, EmittedExpr.eval] at hdig
  have hpr : (envAt t 0).loc POSEIDON2_RESULT = (envAt t 0).loc THRESHOLD_COMMITMENT := by
    have h := gate_forces c3Body mem_c3 mem_c3_last
    simp only [c3Body, subE, EmittedExpr.eval] at h
    omega
  have hbind : (envAt t 0).loc THRESHOLD_COMMITMENT
      = hash [(envAt t 0).loc THRESHOLD, (envAt t 0).loc BLINDING] := hpr.symm.trans hdig
  -- === THE WELD leg 1: fact_hash = hash_fact(pred, [private_value, term1, term2]) ===
  have hlookF := hsat.rowConstraints 0 hi0 factHashLookup mem_factHash
  simp only [VmConstraint2.holdsAt, factHashLookup, Lookup.holdsAt] at hlookF
  have hfh := chip_lookup_sound hash (t.tf .poseidon2) hChip (envAt t 0).loc
    [.var PREDICATE_SYM, .var PRIVATE_VALUE, .var TERM1, .var TERM2,
     .const 0, .const FACT_MARK, .const 1] FACT_HASH FACTHASH_LANES (by decide) hlookF
  simp only [List.map_cons, List.map_nil, EmittedExpr.eval] at hfh
  -- === THE WELD leg 2: fact_commitment = hash_2_to_1(fact_hash, state_root) ===
  have hlookC := hsat.rowConstraints 0 hi0 factCommitLookup mem_factCommit
  simp only [VmConstraint2.holdsAt, factCommitLookup, Lookup.holdsAt] at hlookC
  have hfc := chip_lookup_sound hash (t.tf .poseidon2) hChip (envAt t 0).loc
    [.var FACT_HASH, .var STATE_ROOT] FACT_COMMITMENT FACTCOMMIT_LANES (by decide) hlookC
  simp only [List.map_cons, List.map_nil, EmittedExpr.eval] at hfc
  -- === PI: commitments are the public inputs ===
  exact ⟨horder, hbind, pi_forces THRESHOLD_COMMITMENT 0 mem_pi0,
    pi_forces FACT_COMMITMENT 1 mem_pi1, hfh, hfc⟩

#assert_axioms committedThreshold_satisfied2_sound

/-- **THE WELD, packaged (SAT ⟹ the committed fact carries the PROVEN value).** From the whole-
descriptor soundness, the public fact commitment `pub 1` — the value a verifier binds to a trusted
credential — equals, in the genuine Poseidon2 `hash`, the DOUBLE hash of a fact whose value slot is
the SAME `PRIVATE_VALUE` the ORDER leg proved `≥ threshold`. So a satisfying proof cannot name a fact
commitment whose value differs from the value it proves about. This is the exact statement the held
forgery #2 violated (value proven-about decoupled from the committed fact's value). -/
theorem committedFact_opens_to_proven_value
    (hash : List ℤ → ℤ) (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (t : VmTrace)
    (hChip : ChipTableSound hash (t.tf .poseidon2))
    (hsat : Satisfied2 hash committedThresholdDesc minit mfin maddrs t)
    (hlen : 0 < t.rows.length) :
    (envAt t 0).pub 1
      = hash [hash [(envAt t 0).loc PREDICATE_SYM, (envAt t 0).loc PRIVATE_VALUE,
                    (envAt t 0).loc TERM1, (envAt t 0).loc TERM2, 0, FACT_MARK, 1],
              (envAt t 0).loc STATE_ROOT] := by
  obtain ⟨_, _, _, hpi1, hfh, hfc⟩ :=
    committedThreshold_satisfied2_sound hash minit mfin maddrs t hChip hsat hlen
  rw [← hpi1, hfc, hfh]

/-- **THE WELD BITES (value ≠ committed value ⟹ REJECT).** Under Poseidon2 collision resistance —
the named chip carrier, here as injectivity of the fact double-hash in its value slot — a proof whose
fact witnesses (predicate / terms / state_root) match a trusted credential of value `v0`, but whose
proven `private_value ≠ v0`, CANNOT satisfy the descriptor. The honest Lean face of the emit-gate
forge probe: the range gadget alone let a 700-value proof carry a 300-value fact commitment; the weld
forecloses it. `v0 ≠ private_value` is freely satisfiable, so this rejection is non-vacuous. -/
theorem committedValue_forge_rejected
    (hash : List ℤ → ℤ) (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (t : VmTrace)
    (hChip : ChipTableSound hash (t.tf .poseidon2))
    (hlen : 0 < t.rows.length) (v0 : ℤ)
    (hcred : (envAt t 0).pub 1
      = hash [hash [(envAt t 0).loc PREDICATE_SYM, v0, (envAt t 0).loc TERM1,
                    (envAt t 0).loc TERM2, 0, FACT_MARK, 1], (envAt t 0).loc STATE_ROOT])
    (hinj : ∀ a b : ℤ,
      hash [hash [(envAt t 0).loc PREDICATE_SYM, a, (envAt t 0).loc TERM1,
                  (envAt t 0).loc TERM2, 0, FACT_MARK, 1], (envAt t 0).loc STATE_ROOT]
        = hash [hash [(envAt t 0).loc PREDICATE_SYM, b, (envAt t 0).loc TERM1,
                  (envAt t 0).loc TERM2, 0, FACT_MARK, 1], (envAt t 0).loc STATE_ROOT] → a = b)
    (hforge : (envAt t 0).loc PRIVATE_VALUE ≠ v0) :
    ¬ Satisfied2 hash committedThresholdDesc minit mfin maddrs t := by
  intro hsat
  have hopen := committedFact_opens_to_proven_value hash minit mfin maddrs t hChip hsat hlen
  exact hforge (hinj _ _ (hopen.symm.trans hcred))

#assert_axioms committedFact_opens_to_proven_value
#assert_axioms committedValue_forge_rejected

/-! ## §4 — NON-VACUITY: a concrete SATISFYING assignment, and constraints that BITE.

The anti-scar witnesses. §4a exhibits `acceptLoc`, a concrete assignment on which EVERY declared
constraint body vanishes, the lookup tuple is a GENUINE Poseidon2 chip row, and the PI equalities
hold — so the `Satisfied2` hypothesis is genuinely inhabitable — together with `acceptEnv_meets`
proving the CONCLUSION holds on it with real, distinct numbers (`3 ≤ 5`, `99 = 99`), NOT a `P → P`.
§4b exhibits `rejectLoc`, on which the difference gate BITES, plus the model-welded proof that an
under-threshold value has NO range witness, plus `underThreshold_rejected` — a concrete `Satisfied2`
that FAILS whenever the row-0 value is below the threshold. §4c inhabits the `ChipTableSound` carrier
so it is not a vacuous/unusable hypothesis. -/

/-! ### §4a — the ACCEPT side. -/

/-- A concrete Poseidon2 model for the accept witness: the threshold commitment `hash[3,0] = 0`, the
fact hash `hash_fact(7,[5,0,0]) = hash[7,5,0,0,0,FACT_MARK,1] = 77`, and the fact commitment
`hash[77,11] = 88`. Distinct nonzero fact digests exhibit the value↔fact weld with REAL numbers: the
committed fact 88 opens to a fact hash 77 whose VALUE slot is exactly the proven value 5. -/
def acceptHash : List ℤ → ℤ := fun l =>
  if l = [3, 0] then 0
  else if l = [7, 5, 0, 0, 0, FACT_MARK, 1] then 77
  else if l = [77, 11] then 88
  else 0

/-- A concrete satisfying local row: private value `5`, threshold `3`, blinding `0`, diff `2`
(bit 1 set); the fact witnesses `predicate_sym 7`, `state_root 11`, `fact_hash 77`, `fact_commitment
88` — so the weld's two chip lookups open genuinely; everything else `0`. -/
def acceptLoc : Assignment := fun c =>
  if c = PRIVATE_VALUE then 5
  else if c = THRESHOLD then 3
  else if c = DIFF then 2
  else if c = diffBit 1 then 1
  else if c = PREDICATE_SYM then 7
  else if c = STATE_ROOT then 11
  else if c = FACT_HASH then 77
  else if c = FACT_COMMITMENT then 88
  else 0

/-- The matching public inputs: `pi[0] = 0` (the threshold commitment), `pi[1] = 88` (the fact
commitment, the genuine double-hash of the value-5 fact). -/
def acceptPub : Assignment := fun k => if k = 1 then 88 else 0

/-- The satisfying row environment. -/
def acceptEnv : VmRowEnv := { loc := acceptLoc, nxt := acceptLoc, pub := acceptPub }

-- Every declared gate body VANISHES on the satisfying assignment (the accept witness, gate by gate).
#guard decide (c3Body.eval acceptLoc = 0)
#guard decide (c4Body.eval acceptLoc = 0)
#guard decide (recompBody.eval acceptLoc = 0)
#guard decide ((binBody 0).eval acceptLoc = 0)
#guard decide ((binBody 1).eval acceptLoc = 0)
#guard decide ((binBody 29).eval acceptLoc = 0)
#guard decide ((EmittedExpr.var (diffBit (COMMITTED_DIFF_BITS - 1))).eval acceptLoc = 0)
-- The lookup tuple is a GENUINE Poseidon2 chip row of the constant-`0` hash (so a singleton chip
-- table carrying it is `ChipTableSound`, and the lookup constraint is satisfiable).
#guard decide ((chipLookupTuple [.var THRESHOLD, .var BLINDING] POSEIDON2_RESULT CHIP_LANES).map
                 (·.eval acceptLoc)
               = chipRow (fun _ => 0) [acceptLoc THRESHOLD, acceptLoc BLINDING] [0, 0, 0, 0, 0, 0, 0])
-- The PI equalities hold.
#guard decide (acceptLoc THRESHOLD_COMMITMENT = acceptPub 0)
#guard decide (acceptLoc FACT_COMMITMENT = acceptPub 1)

/-- **The CONCLUSION is non-trivially inhabited.** The semantic relation `MeetsCommittedThreshold`
holds on the satisfying environment with REAL, distinct numbers (`3 ≤ 5`, threshold commitment `= 0`,
and — the WELD — the committed fact commitment `88` opens to a fact hash `77` whose value slot is the
proven value `5`) — so the bridge's conclusion is genuine, not a `True`/`P → P` shell. -/
theorem acceptEnv_meets : MeetsCommittedThreshold acceptHash acceptEnv := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [acceptEnv, acceptLoc, acceptPub, acceptHash, PRIVATE_VALUE, THRESHOLD, BLINDING,
      DIFF, DIFF_BITS_START, diffBit, THRESHOLD_COMMITMENT, FACT_COMMITMENT,
      PREDICATE_SYM, TERM1, TERM2, STATE_ROOT, FACT_HASH, FACT_MARK, COMMITTED_DIFF_BITS] <;> decide

/-- **The `ChipTableSound` carrier is genuinely inhabitable** — a singleton chip table carrying the
accept row is sound, so the bridge's Poseidon2 hypothesis is usable, not vacuous. -/
theorem chipTableSound_singleton_inhabited :
    ChipTableSound (fun _ => (0 : ℤ)) [chipRow (fun _ => 0) [3, 0] [0, 0, 0, 0, 0, 0, 0]] := by
  intro r hr
  simp only [List.mem_singleton] at hr
  exact ⟨[3, 0], [0, 0, 0, 0, 0, 0, 0], by decide, by decide, hr⟩

/-! ### §4b — the REJECT side (the constraint BITES). -/

/-- The accept assignment with the private value LOWERED below the threshold (`1 < 3`), keeping the
diff column — so the difference gate can no longer vanish. -/
def rejectLoc : Assignment := fun c => if c = PRIVATE_VALUE then 1 else acceptLoc c

/-- **The difference gate BITES** on the under-threshold assignment (`diff − value + threshold
= 2 − 1 + 3 = 4 ≠ 0`): the constraint system rejects it. -/
theorem reject_c4_bites : ¬ (c4Body.eval rejectLoc = 0) := by decide

/-- **Model-welded reject (the honest soundness bite).** An under-threshold value has NO range
witness: the honest diff `value − threshold = 1 − 3 = −2` cannot be a boolean bit-decomposition,
because `bitsToInt` of boolean bits is non-negative (`RecordCircuit.range_sound`). So the range
gadget is UNSATISFIABLE for `value < threshold`. -/
theorem underThreshold_has_no_range_witness :
    ¬ ∃ bits : List ℤ, Boolean bits ∧ bitsToInt bits = (1 : ℤ) - 3 := by
  rintro ⟨bits, hbool, hrec⟩
  have h := (range_sound bits hbool).1
  rw [hrec] at h
  omega

/-- **`underThreshold_rejected` — a concrete `Satisfied2` that FAILS (constraint bites, whole
descriptor).** ANY witness whose row-0 private value is strictly below the threshold CANNOT satisfy
the committed-threshold descriptor (against a sound chip table, on ANY non-empty trace — `0 <
rows.length`, INCLUDING a single-row trace). The hypothesis `value < threshold` is freely
satisfiable, so this rejection is non-vacuous — the descriptor is a genuine, biting filter, not a
rubber stamp. Directly contraposes the (now height-1-covering) soundness bridge, so the height-1
last-row-vacuity forge the transition-only `.gate` lowering used to admit is now REJECTED. -/
theorem underThreshold_rejected
    (hash : List ℤ → ℤ) (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (t : VmTrace)
    (hChip : ChipTableSound hash (t.tf .poseidon2))
    (hlen : 0 < t.rows.length)
    (hunder : (envAt t 0).loc PRIVATE_VALUE < (envAt t 0).loc THRESHOLD) :
    ¬ Satisfied2 hash committedThresholdDesc minit mfin maddrs t := by
  intro hsat
  have := (committedThreshold_satisfied2_sound hash minit mfin maddrs t hChip hsat hlen).1
  omega

#assert_axioms acceptEnv_meets
#assert_axioms chipTableSound_singleton_inhabited
#assert_axioms underThreshold_has_no_range_witness
#assert_axioms underThreshold_rejected

end Dregg2.Circuit.Emit.CommittedThresholdRefine
