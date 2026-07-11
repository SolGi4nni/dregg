/-
# Dregg2.Circuit.Emit.GarbledEvalRefine — the WHOLE-DESCRIPTOR functional-correctness bridge for
GARBLED-CIRCUIT EVALUATION (Rung 1 refinement over `GarbledEvalEmit`).

## What this file IS (and why it is the NO_LEAN-flavoured, spec-authoring case)

`GarbledEvalEmit.lean` (Rung 0) byte-pins the 56-column garbled-evaluation descriptor
(`garbledEvalDesc`) and proves the per-GATE decryption tooth (`decryption_body_zero_iff`). What was
MISSING — and what this file supplies — is the whole-descriptor bridge: a trace SATISFYING the
descriptor's `Satisfied2` acceptance predicate corresponds to a genuine garbled-circuit evaluation
run.

The census names `Dregg2.Crypto.GarbledJoint.lean` as the family's Lean spec, and it IS the real
semantic twin — but at the PROTOCOL layer: `GarbledKernel` models Yao's 2PC as an abstract
`garble`/`eval`/`correct`/`private_sim` interface over a joint predicate `P : A → B → Bool`. That
model deliberately abstracts away the AIR TRACE LAYOUT (there is no `P`, no input labels, no
per-lane one-time-pad decryption inside `GarbledKernel`), exactly as `GarbledEvalEmit`'s own header
states ("they model the protocol, not this AIR trace layout, so they do NOT feed this emit"). So
there is NO trace-level model to weld `Satisfied2` to. This file therefore AUTHORS that missing
functional spec — `GarbledEvalRun`, the relation the 56-column AIR is meant to compute — and proves
`Satisfied2 ⟹ GarbledEvalRun` (`satisfied2_implies_garbledEvalRun`). This is the AIR realization of
the ONE-TIME-PAD DECRYPTION step (`output = table_entry − hash_out`) that `GarbledKernel.eval`
models abstractly: the evaluator, holding the input labels and their garbling hash, recovers each
output label by subtracting the hash from the garbled table entry.

`GarbledEvalRun` captures, per ACTIVE (non-last) row (base gates and window gates are vacuous on the
last row in the faithful denotation — `holdsVm`/`WindowConstraint.holdsAt`):

  * **decryption** (`GateDecrypts`) — a non-padding row recovers every output label by one-time-pad
    decryption `output(j) = table_entry(j) − hash_out(j)` (Yao decryption);
  * **gate well-formedness** (`GateWellFormed`) — the six selectors are boolean AND a non-padding
    row selects EXACTLY one of the four gate types (`is_and+is_or+is_xor+is_not = 1`);
  * **wire chaining** (`WiresChain`) — a `chain_flag` row threads its output labels into the next
    gate's left input (`next.left(j) = output(j)`);

and, on the first row, the public binding (`CommitmentBound`: the committed circuit-commitment /
output-label-hash columns equal the published PIs) and the `gate_index_delta = 0` boundary.

## Direction + scope

The load-bearing direction is SAT ⟹ SEM (`satisfied2_implies_garbledEvalRun`): descriptor-acceptance
forces the genuine evaluation relation. A full `Satisfied2 ↔ GarbledEvalRun` is NOT a theorem, and
deliberately so: `Satisfied2` additionally bundles the multi-table plumbing (memory / map / table
faithfulness), which for THIS descriptor is empty and is not part of the garbled-evaluation
semantics — so the reverse would have to re-inject that plumbing as hypotheses, muddying the
semantic statement. The Poseidon2 garbling hash is the named executor-verified carrier (off
descriptor, per `GarbledEvalEmit`), so no Poseidon2 chip lookup / CR carrier enters here.

## Non-vacuity (the anti-scar witnesses, both IN THIS FILE)

* `garbled_honest_satisfied2` — a CONCRETE two-row honest trace `t₀` with `Satisfied2` PROVEN, so the
  bridge hypothesis is genuinely inhabited; `garbled_honest_decrypts_nonvacuous` shows its first row
  is non-padding (`is_padding = 0`) so the decryption constraint is ACTIVE (not the padding escape)
  and the decryption equality genuinely holds.
* `garbled_forged_not_satisfied2` — a CONCRETE trace `tBad` whose forged output label breaks the
  lane-0 decryption gate on an active row, so `Satisfied2` is REFUTED: the constraint bites.

## The field-faithful denotation (mod-p) and the canonicality envelope

`VmConstraint.holdsVm` / `WindowConstraint.holdsAt` pin gate bodies only `≡ 0 [ZMOD p]`
(`p = 2013265921`, BabyBear). The Yao decryption clause is HONESTLY a congruence
(`output ≡ table_entry − hash_out [ZMOD p]`): labels are full field elements, so the field
subtraction genuinely wraps when `table_entry < hash_out` — the ℤ equality is FALSE there, and the
congruence IS the deployed one-time-pad. The booleanity / exclusivity / chaining / commitment
conclusions are read back over ℤ through the EXPLICIT range-check envelope `GarbledTraceCanon`
(§4.5), inhabited concretely by `t₀_canon`.

## Axiom hygiene

`#assert_axioms` ⊆ {propext, Classical.choice, Quot.sound} (Classical enters only via `by_cases`
on padding / chain flags). NEW file; imports read-only.
-/
import Dregg2.Circuit.Emit.GarbledEvalEmit
import Dregg2.Circuit.Emit.EffectVmEmitTransfer

namespace Dregg2.Circuit.Emit.GarbledEvalRefine

open Dregg2.Circuit (Assignment)
open Dregg2.Exec.CircuitEmit (EmittedExpr)
open Dregg2.Circuit.Emit.EffectVmEmit
  (VmRowEnv VmConstraint VmRow siteHoldsAll holdsVm_gate_false holdsVm_piFirst_true
   holdsVm_boundaryFirst_true)
open Dregg2.Circuit.DescriptorIR2
  (EffectVmDescriptor2 VmConstraint2 Satisfied2 VmTrace envAt WindowConstraint WindowExpr
   zeroAsg memLog mapLog memOpsOf mapOpsOf)
open Dregg2.Circuit.Emit.GarbledEvalEmit
open Dregg2.Circuit.Emit.EffectVmEmitTransfer (pPrimeInt gate_modEq_iff eqToModEq)
open Dregg2.Crypto

set_option autoImplicit false

/-! ## §1 — The genuine semantic relation the garbled-evaluation AIR computes (AUTHORED spec). -/

/-- **`GateDecrypts env`** — the row correctly decrypts every output label, OR it is a padding row.
Non-padding ⇒ each of the 8 output-label felts is recovered by one-time-pad decryption
`output(j) ≡ table_entry(j) − hash_out(j) [ZMOD p]` (the AIR realization of Yao's per-gate
decryption). HONESTLY a congruence: labels are full field elements, so the field subtraction
wraps when `table_entry < hash_out` — the mod-`p` congruence IS the deployed one-time-pad. -/
def GateDecrypts (env : VmRowEnv) : Prop :=
  env.loc IS_PADDING = 1 ∨
    ∀ j, j < 8 →
      env.loc (OUTPUT j)
        ≡ env.loc (TABLE_ENTRY j) - env.loc (HASH_OUT j) [ZMOD 2013265921]

/-- **`GateWellFormed env`** — the six selectors are boolean, and a non-padding row selects EXACTLY
one of the four gate types (`is_and + is_or + is_xor + is_not = 1`). -/
def GateWellFormed (env : VmRowEnv) : Prop :=
  (env.loc IS_AND = 0 ∨ env.loc IS_AND = 1)
  ∧ (env.loc IS_OR = 0 ∨ env.loc IS_OR = 1)
  ∧ (env.loc IS_XOR = 0 ∨ env.loc IS_XOR = 1)
  ∧ (env.loc IS_NOT = 0 ∨ env.loc IS_NOT = 1)
  ∧ (env.loc CHAIN_FLAG = 0 ∨ env.loc CHAIN_FLAG = 1)
  ∧ (env.loc IS_PADDING = 0 ∨ env.loc IS_PADDING = 1)
  ∧ (env.loc IS_PADDING = 1
      ∨ env.loc IS_AND + env.loc IS_OR + env.loc IS_XOR + env.loc IS_NOT = 1)

/-- **`WiresChain env`** — a `chain_flag` row threads its output labels into the next gate's left
input (`next.left(j) = output(j)`), OR the chain flag is off. -/
def WiresChain (env : VmRowEnv) : Prop :=
  env.loc CHAIN_FLAG = 0 ∨ ∀ j, j < 8 → env.nxt (LEFT j) = env.loc (OUTPUT j)

/-- **`CommitmentBound env`** — the committed circuit-commitment (4 felts) / output-label-hash
(4 felts) columns equal the published public inputs. -/
def CommitmentBound (env : VmRowEnv) : Prop :=
  (∀ j, j < 4 → env.loc (CIRCUIT_COMMITMENT + j) = env.pub j)
  ∧ (∀ j, j < 4 → env.loc (OUTPUT_LABEL_HASH + j) = env.pub (4 + j))

/-- **`GarbledEvalRun t`** — the whole-trace functional spec of the garbled-evaluation AIR: every
active (non-last) row decrypts, is a well-formed gate, and chains its wires; the first row binds the
public commitment/output-hash and initializes `gate_index_delta`. This is the relation the emitted
descriptor is proven to refine. -/
structure GarbledEvalRun (t : VmTrace) : Prop where
  decrypts   : ∀ i, i + 1 < t.rows.length → GateDecrypts (envAt t i)
  wellFormed : ∀ i, i + 1 < t.rows.length → GateWellFormed (envAt t i)
  chains     : ∀ i, i + 1 < t.rows.length → WiresChain (envAt t i)
  committed  : 0 < t.rows.length → CommitmentBound (envAt t 0)
  gateInit   : 0 < t.rows.length → (envAt t 0).loc GATE_INDEX_DELTA = 0

/-! ## §2 — Per-body zero-iff lemmas (the decryption one is reused from `GarbledEvalEmit`). -/

/-- The boolean-selector body vanishes iff the selector is `0` or `1`. -/
theorem bin_body_zero_iff (c : Nat) (a : Assignment) :
    (binBody c).eval a = 0 ↔ a c = 0 ∨ a c = 1 := by
  simp only [binBody, EmittedExpr.eval]
  constructor
  · intro h
    rcases mul_eq_zero.mp h with h0 | h1
    · exact Or.inl h0
    · exact Or.inr (by omega)
  · rintro (h | h)
    · exact mul_eq_zero_of_left h _
    · exact mul_eq_zero_of_right _ (by omega)

/-- The exclusivity body vanishes iff the row is padding OR exactly one gate type is selected. -/
theorem excl_body_zero_iff (a : Assignment) :
    (exclusivityBody).eval a = 0 ↔
      a IS_PADDING = 1 ∨ a IS_AND + a IS_OR + a IS_XOR + a IS_NOT = 1 := by
  simp only [exclusivityBody, notPadding, EmittedExpr.eval]
  constructor
  · intro h
    rcases mul_eq_zero.mp h with h0 | h1
    · exact Or.inl (by omega)
    · exact Or.inr (by omega)
  · rintro (h | h)
    · exact mul_eq_zero_of_left (by omega) _
    · exact mul_eq_zero_of_right _ (by omega)

/-- The wire-chaining window body vanishes iff the chain flag is off OR the output feeds the next
row's left input, at lane `j`. -/
theorem chain_body_zero_iff (j : Nat) (env : VmRowEnv) :
    (chainBody j).eval env = 0 ↔
      env.loc CHAIN_FLAG = 0 ∨ env.nxt (LEFT j) = env.loc (OUTPUT j) := by
  simp only [chainBody, WindowExpr.eval]
  constructor
  · intro h
    rcases mul_eq_zero.mp h with h0 | h1
    · exact Or.inl h0
    · exact Or.inr (by omega)
  · rintro (h | h)
    · exact mul_eq_zero_of_left h _
    · exact mul_eq_zero_of_right _ (by omega)

/-! ## §3 — Membership of each declared constraint in the descriptor's constraint list. -/

/-- The descriptor's constraint list, spelled out = the 7-part core ++ the last-row binding fix
(defeq to `garbledEvalDesc.constraints`). Every core-constraint membership lemma below threads one
extra `mem_append_left` (the core is now the LEFT of `core ++ garbledLastRowFix`). -/
private def CONSTRAINTS : List VmConstraint2 :=
  commitmentPins ++ outputHashPins ++ decryptionGates ++ selectorBinaryGates
    ++ [.base (.gate exclusivityBody)] ++ chainingGates ++ [gateIndexDeltaBoundary]
    ++ garbledLastRowFix

theorem decGate_mem (j : Nat) (hj : j < 8) :
    VmConstraint2.base (.gate (decBody j)) ∈ garbledEvalDesc.constraints := by
  show _ ∈ CONSTRAINTS
  exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
    (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _
      (List.mem_map.mpr ⟨j, List.mem_range.mpr hj, rfl⟩))))))

theorem chainGate_mem (j : Nat) (hj : j < 8) :
    VmConstraint2.windowGate ⟨chainBody j, true⟩ ∈ garbledEvalDesc.constraints := by
  show _ ∈ CONSTRAINTS
  exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _
    (List.mem_map.mpr ⟨j, List.mem_range.mpr hj, rfl⟩)))

theorem selGate_mem (c : VmConstraint2) (hc : c ∈ selectorBinaryGates) :
    c ∈ garbledEvalDesc.constraints := by
  show c ∈ CONSTRAINTS
  exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
    (List.mem_append_left _ (List.mem_append_right _ hc))))

theorem excl_mem :
    VmConstraint2.base (.gate exclusivityBody) ∈ garbledEvalDesc.constraints := by
  show _ ∈ CONSTRAINTS
  exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
    (List.mem_append_right _ (List.mem_singleton.mpr rfl))))

theorem bnd_mem :
    VmConstraint2.base (.boundary VmRow.first (.var GATE_INDEX_DELTA))
      ∈ garbledEvalDesc.constraints := by
  show _ ∈ CONSTRAINTS
  exact List.mem_append_left _ (List.mem_append_right _ (List.mem_singleton.mpr rfl))

theorem commitPin_mem (j : Nat) (hj : j < 4) :
    VmConstraint2.base (.piBinding VmRow.first (CIRCUIT_COMMITMENT + j) j)
      ∈ garbledEvalDesc.constraints := by
  show _ ∈ CONSTRAINTS
  exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
    (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
      (List.mem_append_left _ (List.mem_map.mpr ⟨j, List.mem_range.mpr hj, rfl⟩)))))))

theorem outHashPin_mem (j : Nat) (hj : j < 4) :
    VmConstraint2.base (.piBinding VmRow.first (OUTPUT_LABEL_HASH + j) (4 + j))
      ∈ garbledEvalDesc.constraints := by
  show _ ∈ CONSTRAINTS
  exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
    (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
      (List.mem_append_right _ (List.mem_map.mpr ⟨j, List.mem_range.mpr hj, rfl⟩)))))))

/-! ## §4 — Extracting one forced constraint from `Satisfied2` on an ACTIVE (non-last) row. -/

/-- A declared base-gate body vanishes mod `p` on an active row of a satisfying trace. -/
theorem gate_forces
    (hash : List ℤ → ℤ) (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (t : VmTrace)
    (h : Satisfied2 hash garbledEvalDesc minit mfin maddrs t)
    (i : Nat) (hi : i < t.rows.length) (hlast : i + 1 ≠ t.rows.length)
    (body : EmittedExpr)
    (hmem : VmConstraint2.base (.gate body) ∈ garbledEvalDesc.constraints) :
    body.eval (envAt t i).loc ≡ 0 [ZMOD 2013265921] := by
  have hrow := h.rowConstraints i hi _ hmem
  have hlf : (i + 1 == t.rows.length) = false := by
    simp only [beq_eq_false_iff_ne]; exact hlast
  rw [hlf] at hrow
  simpa [VmConstraint2.holdsAt] using hrow

/-- A declared wire-chaining window body vanishes mod `p` on an active row of a satisfying trace. -/
theorem window_forces
    (hash : List ℤ → ℤ) (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (t : VmTrace)
    (h : Satisfied2 hash garbledEvalDesc minit mfin maddrs t)
    (i : Nat) (hi : i < t.rows.length) (hlast : i + 1 ≠ t.rows.length)
    (j : Nat) (hj : j < 8) :
    (chainBody j).eval (envAt t i) ≡ 0 [ZMOD 2013265921] := by
  have hrow := h.rowConstraints i hi _ (chainGate_mem j hj)
  have hlf : (i + 1 == t.rows.length) = false := by
    simp only [beq_eq_false_iff_ne]; exact hlast
  rw [hlf] at hrow
  simpa [VmConstraint2.holdsAt, WindowConstraint.holdsAt] using hrow

/-- A declared first-row PI binding pins the column to the public input mod `p`. -/
theorem pi_forces
    (hash : List ℤ → ℤ) (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (t : VmTrace)
    (h : Satisfied2 hash garbledEvalDesc minit mfin maddrs t)
    (h0 : 0 < t.rows.length) (col k : Nat)
    (hmem : VmConstraint2.base (.piBinding VmRow.first col k) ∈ garbledEvalDesc.constraints) :
    (envAt t 0).loc col ≡ (envAt t 0).pub k [ZMOD 2013265921] := by
  have hrow := h.rowConstraints 0 h0 _ hmem
  simpa [VmConstraint2.holdsAt] using hrow

/-- A declared first-row boundary body vanishes mod `p` on the first row of a satisfying trace. -/
theorem boundary_forces
    (hash : List ℤ → ℤ) (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (t : VmTrace)
    (h : Satisfied2 hash garbledEvalDesc minit mfin maddrs t)
    (h0 : 0 < t.rows.length) (b : EmittedExpr)
    (hmem : VmConstraint2.base (.boundary VmRow.first b) ∈ garbledEvalDesc.constraints) :
    b.eval (envAt t 0).loc ≡ 0 [ZMOD 2013265921] := by
  have hrow := h.rowConstraints 0 h0 _ hmem
  simpa [VmConstraint2.holdsAt] using hrow

/-! ## §4.5 — the canonicality envelope: reading the ℤ conclusions back off the mod-`p` congruences.

The deployed AIR constrains cells only as BabyBear field elements; the range-check invariant is
carried as the EXPLICIT hypothesis `GarbledTraceCanon` — inhabited concretely by `t₀_canon` (§6),
so the envelope is not vacuous. The decryption clause needs NO envelope (it is honestly a
congruence); the envelope covers the flags (whose booleanity must be EXACT), the chained label
lanes, and the committed/bound first-row columns. -/

/-- Canonical-representative predicate: the deployed range-check invariant `0 ≤ x < p`. -/
def CanonCell (x : ℤ) : Prop := 0 ≤ x ∧ x < 2013265921

/-- Two canonical representatives congruent mod `p` are EQUAL. -/
theorem eq_of_modEq_of_canon {a b : ℤ} (h : a ≡ b [ZMOD 2013265921])
    (ha : CanonCell a) (hb : CanonCell b) : a = b := by
  obtain ⟨ha0, ha1⟩ := ha; obtain ⟨hb0, hb1⟩ := hb
  obtain ⟨k, hk⟩ := h.dvd
  omega

/-- A canonical cell whose booleanity gate vanishes mod `p` IS `0` or `1` over ℤ: primality splits
`p ∣ x·(x−1)`, and canonicality collapses each factor. -/
theorem bin_cases {x : ℤ} (h : x * (x + -1) ≡ 0 [ZMOD 2013265921]) (hc : CanonCell x) :
    x = 0 ∨ x = 1 := by
  obtain ⟨h0, h1⟩ := hc
  have hd : (2013265921 : ℤ) ∣ x * (x + -1) := Int.modEq_zero_iff_dvd.mp h
  rcases pPrimeInt.dvd_mul.mp hd with hx | hx
  · obtain ⟨k, hk⟩ := hx; left; omega
  · obtain ⟨k, hk⟩ := hx; right; omega

/-- **The garbled-evaluation canonicality envelope**: the six selector flags and the chained label
lanes (`LEFT`/`OUTPUT`) canonical on every row; the first row's committed/bound columns and the
eight bound public inputs canonical. (`TABLE_ENTRY`/`HASH_OUT` are NOT here — the decryption
clause is a congruence and needs no range fact.) -/
structure GarbledTraceCanon (t : VmTrace) : Prop where
  selAnd : ∀ i, i < t.rows.length → CanonCell ((envAt t i).loc IS_AND)
  selOr : ∀ i, i < t.rows.length → CanonCell ((envAt t i).loc IS_OR)
  selXor : ∀ i, i < t.rows.length → CanonCell ((envAt t i).loc IS_XOR)
  selNot : ∀ i, i < t.rows.length → CanonCell ((envAt t i).loc IS_NOT)
  chainFlag : ∀ i, i < t.rows.length → CanonCell ((envAt t i).loc CHAIN_FLAG)
  padding : ∀ i, i < t.rows.length → CanonCell ((envAt t i).loc IS_PADDING)
  left : ∀ i, i < t.rows.length → ∀ j, j < 8 → CanonCell ((envAt t i).loc (LEFT j))
  output : ∀ i, i < t.rows.length → ∀ j, j < 8 → CanonCell ((envAt t i).loc (OUTPUT j))
  commit : ∀ j, j < 4 → CanonCell ((envAt t 0).loc (CIRCUIT_COMMITMENT + j))
  ohash : ∀ j, j < 4 → CanonCell ((envAt t 0).loc (OUTPUT_LABEL_HASH + j))
  gid : CanonCell ((envAt t 0).loc GATE_INDEX_DELTA)
  pubs : ∀ k, k < 8 → CanonCell (t.pub k)

/-! ## §5 — THE WHOLE-DESCRIPTOR BRIDGE (SAT ⟹ SEM). -/

/-- **`satisfied2_implies_garbledEvalRun` — THE BRIDGE.** A trace satisfying the emitted garbled-
evaluation descriptor's `Satisfied2` acceptance predicate is a genuine garbled-circuit evaluation
run: every active row decrypts (Yao one-time-pad), selects exactly one well-formed gate, and chains
its wires; the first row binds the public commitment/output-hash and initializes the gate index.
The descriptor is therefore a proven functional refinement of `GarbledEvalRun`, not a byte-pinned
blob. -/
theorem satisfied2_implies_garbledEvalRun
    (hash : List ℤ → ℤ) (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (t : VmTrace)
    (hcanon : GarbledTraceCanon t)
    (h : Satisfied2 hash garbledEvalDesc minit mfin maddrs t) :
    GarbledEvalRun t := by
  constructor
  · -- decrypts: prime-split the gated product; the non-padding factor is killed EXACTLY (the flag
    -- is canonical), leaving the one-time-pad congruence.
    intro i hact
    have hi : i < t.rows.length := by omega
    have hlast : i + 1 ≠ t.rows.length := by omega
    by_cases hp : (envAt t i).loc IS_PADDING = 1
    · exact Or.inl hp
    · refine Or.inr (fun j hj => ?_)
      have hg := gate_forces hash minit mfin maddrs t h i hi hlast (decBody j) (decGate_mem j hj)
      have hd := Int.modEq_zero_iff_dvd.mp hg
      rw [show (decBody j).eval (envAt t i).loc
          = (1 - (envAt t i).loc IS_PADDING)
            * ((envAt t i).loc (OUTPUT j)
                - ((envAt t i).loc (TABLE_ENTRY j) - (envAt t i).loc (HASH_OUT j))) from by
        simp only [decBody, notPadding, EmittedExpr.eval]; ring] at hd
      rcases pPrimeInt.dvd_mul.mp hd with hx | hx
      · obtain ⟨hp0, hp1⟩ := hcanon.padding i hi
        obtain ⟨k, hk⟩ := hx
        exact absurd (show (envAt t i).loc IS_PADDING = 1 by omega) hp
      · exact (gate_modEq_iff rfl).mp (Int.modEq_zero_iff_dvd.mpr hx)
  · -- wellFormed: booleanity via prime split + canonicality; exclusivity then collapses over ℤ
    -- (the selector sum is confined to [0,4] ⊂ [0,p)).
    intro i hact
    have hi : i < t.rows.length := by omega
    have hlast : i + 1 ≠ t.rows.length := by omega
    have hAnd := bin_cases (by
      simpa only [binBody, EmittedExpr.eval] using
        gate_forces hash minit mfin maddrs t h i hi hlast (binBody IS_AND)
          (selGate_mem _ (by simp [selectorBinaryGates]))) (hcanon.selAnd i hi)
    have hOr := bin_cases (by
      simpa only [binBody, EmittedExpr.eval] using
        gate_forces hash minit mfin maddrs t h i hi hlast (binBody IS_OR)
          (selGate_mem _ (by simp [selectorBinaryGates]))) (hcanon.selOr i hi)
    have hXor := bin_cases (by
      simpa only [binBody, EmittedExpr.eval] using
        gate_forces hash minit mfin maddrs t h i hi hlast (binBody IS_XOR)
          (selGate_mem _ (by simp [selectorBinaryGates]))) (hcanon.selXor i hi)
    have hNot := bin_cases (by
      simpa only [binBody, EmittedExpr.eval] using
        gate_forces hash minit mfin maddrs t h i hi hlast (binBody IS_NOT)
          (selGate_mem _ (by simp [selectorBinaryGates]))) (hcanon.selNot i hi)
    have hChain := bin_cases (by
      simpa only [binBody, EmittedExpr.eval] using
        gate_forces hash minit mfin maddrs t h i hi hlast (binBody CHAIN_FLAG)
          (selGate_mem _ (by simp [selectorBinaryGates]))) (hcanon.chainFlag i hi)
    have hPad := bin_cases (by
      simpa only [binBody, EmittedExpr.eval] using
        gate_forces hash minit mfin maddrs t h i hi hlast (binBody IS_PADDING)
          (selGate_mem _ (by simp [selectorBinaryGates]))) (hcanon.padding i hi)
    refine ⟨hAnd, hOr, hXor, hNot, hChain, hPad, ?_⟩
    have hg := gate_forces hash minit mfin maddrs t h i hi hlast exclusivityBody excl_mem
    have hd := Int.modEq_zero_iff_dvd.mp hg
    rw [show exclusivityBody.eval (envAt t i).loc
        = (1 - (envAt t i).loc IS_PADDING)
          * ((envAt t i).loc IS_AND + (envAt t i).loc IS_OR + (envAt t i).loc IS_XOR
              + (envAt t i).loc IS_NOT - 1) from by
      simp only [exclusivityBody, notPadding, EmittedExpr.eval]; ring] at hd
    have b1 : 0 ≤ (envAt t i).loc IS_AND ∧ (envAt t i).loc IS_AND ≤ 1 := by
      rcases hAnd with h' | h' <;> omega
    have b2 : 0 ≤ (envAt t i).loc IS_OR ∧ (envAt t i).loc IS_OR ≤ 1 := by
      rcases hOr with h' | h' <;> omega
    have b3 : 0 ≤ (envAt t i).loc IS_XOR ∧ (envAt t i).loc IS_XOR ≤ 1 := by
      rcases hXor with h' | h' <;> omega
    have b4 : 0 ≤ (envAt t i).loc IS_NOT ∧ (envAt t i).loc IS_NOT ≤ 1 := by
      rcases hNot with h' | h' <;> omega
    rcases pPrimeInt.dvd_mul.mp hd with hx | hx
    · obtain ⟨k, hk⟩ := hx
      rcases hPad with hp | hp
      · exfalso; omega
      · exact Or.inl hp
    · obtain ⟨k, hk⟩ := hx
      exact Or.inr (by omega)
  · -- chains: prime-split the gated product; the flag factor is killed EXACTLY, and both chained
    -- label cells are canonical, so the threading equality holds over ℤ.
    intro i hact
    have hi : i < t.rows.length := by omega
    have hlast : i + 1 ≠ t.rows.length := by omega
    by_cases hcf : (envAt t i).loc CHAIN_FLAG = 0
    · exact Or.inl hcf
    · refine Or.inr (fun j hj => ?_)
      have hw := window_forces hash minit mfin maddrs t h i hi hlast j hj
      have hd := Int.modEq_zero_iff_dvd.mp hw
      rw [show (chainBody j).eval (envAt t i)
          = (envAt t i).loc CHAIN_FLAG
            * ((envAt t i).nxt (LEFT j) - (envAt t i).loc (OUTPUT j)) from by
        simp only [chainBody, WindowExpr.eval]; ring] at hd
      rcases pPrimeInt.dvd_mul.mp hd with hx | hx
      · obtain ⟨hc0, hc1⟩ := hcanon.chainFlag i hi
        obtain ⟨k, hk⟩ := hx
        exact absurd (show (envAt t i).loc CHAIN_FLAG = 0 by omega) hcf
      · exact eq_of_modEq_of_canon
          ((gate_modEq_iff rfl).mp (Int.modEq_zero_iff_dvd.mpr hx))
          (hcanon.left (i + 1) (by omega) j hj) (hcanon.output i hi j hj)
  · -- committed: mod-p pins collapsed by canonicality of both sides.
    intro h0
    have hc1 : ∀ j, j < 4 → (envAt t 0).loc (CIRCUIT_COMMITMENT + j) = (envAt t 0).pub j := by
      intro j hj
      exact eq_of_modEq_of_canon
        (pi_forces hash minit mfin maddrs t h h0 (CIRCUIT_COMMITMENT + j) j
          (commitPin_mem j hj)) (hcanon.commit j hj)
        (hcanon.pubs j (Nat.lt_of_lt_of_le hj (by norm_num)))
    have hc2 : ∀ j, j < 4 →
        (envAt t 0).loc (OUTPUT_LABEL_HASH + j) = (envAt t 0).pub (4 + j) := by
      intro j hj
      exact eq_of_modEq_of_canon
        (pi_forces hash minit mfin maddrs t h h0 (OUTPUT_LABEL_HASH + j) (4 + j)
          (outHashPin_mem j hj)) (hcanon.ohash j hj)
        (hcanon.pubs (4 + j) (Nat.lt_of_lt_of_le (Nat.add_lt_add_left hj 4) (by norm_num)))
    exact ⟨hc1, hc2⟩
  · -- gateInit: mod-p boundary collapsed by canonicality.
    intro h0
    have hb := boundary_forces hash minit mfin maddrs t h h0 (.var GATE_INDEX_DELTA) bnd_mem
    have hb' : (envAt t 0).loc GATE_INDEX_DELTA ≡ 0 [ZMOD 2013265921] := by
      simpa only [EmittedExpr.eval] using hb
    exact eq_of_modEq_of_canon hb' hcanon.gid ⟨by norm_num, by norm_num⟩

#assert_axioms satisfied2_implies_garbledEvalRun

/-! ## §6 — Non-vacuity, part A: a CONCRETE honest trace SATISFYING the descriptor. -/

/-- The published public inputs of the honest witness (distinct, non-zero commitment felts). -/
def honestPub : Assignment := fun k => (k : ℤ) + 100

/-- An honest garbled-evaluation row: an AND gate (`is_and = 1`), chained (`chain_flag = 1`),
non-padding (`is_padding = 0`), all label/hash/table lanes `0` (so decryption `0 = 0 − 0` holds),
the commitment (cols 41..44) / output-label-hash (cols 45..48) blocks bound to the PIs. -/
def honestRow0 : Assignment := fun c =>
  if c = 41 then honestPub 0        -- circuit_commitment[0] ← pi[0]
  else if c = 42 then honestPub 1   -- circuit_commitment[1] ← pi[1]
  else if c = 43 then honestPub 2   -- circuit_commitment[2] ← pi[2]
  else if c = 44 then honestPub 3   -- circuit_commitment[3] ← pi[3]
  else if c = 45 then honestPub 4   -- output_label_hash[0] ← pi[4]
  else if c = 46 then honestPub 5   -- output_label_hash[1] ← pi[5]
  else if c = 47 then honestPub 6   -- output_label_hash[2] ← pi[6]
  else if c = 48 then honestPub 7   -- output_label_hash[3] ← pi[7]
  else if c = 49 then 1             -- IS_AND
  else if c = 53 then 1             -- CHAIN_FLAG
  else 0

/-- The honest two-row witness (row 1 is the last row; its output feeds nothing new since every
label lane is `0`, so the chaining leg `next.left = output` reads `0 = 0`). -/
def t₀ : VmTrace := { rows := [honestRow0, honestRow0], pub := honestPub, tf := fun _ => [] }

theorem envAt0_loc : (envAt t₀ 0).loc = honestRow0 := rfl
theorem envAt0_nxt : (envAt t₀ 0).nxt = honestRow0 := rfl

/-- Every lane column (`< 41`) reads `0` on the honest row. -/
theorem honestRow0_below41 (c : Nat) (h : c < 41) : honestRow0 c = 0 := by
  interval_cases c <;> decide

theorem honestRow0_output (j : Nat) (hj : j < 8) : honestRow0 (OUTPUT j) = 0 :=
  honestRow0_below41 _ (by unfold OUTPUT; omega)
theorem honestRow0_table (j : Nat) (hj : j < 8) : honestRow0 (TABLE_ENTRY j) = 0 :=
  honestRow0_below41 _ (by unfold TABLE_ENTRY; omega)
theorem honestRow0_hash (j : Nat) (hj : j < 8) : honestRow0 (HASH_OUT j) = 0 :=
  honestRow0_below41 _ (by unfold HASH_OUT; omega)
theorem honestRow0_left (j : Nat) (hj : j < 8) : honestRow0 (LEFT j) = 0 :=
  honestRow0_below41 _ (by unfold LEFT; omega)

theorem honestRow0_and : honestRow0 IS_AND = 1 := by decide
theorem honestRow0_or : honestRow0 IS_OR = 0 := by decide
theorem honestRow0_xor : honestRow0 IS_XOR = 0 := by decide
theorem honestRow0_not : honestRow0 IS_NOT = 0 := by decide
theorem honestRow0_chain : honestRow0 CHAIN_FLAG = 1 := by decide
theorem honestRow0_padding : honestRow0 IS_PADDING = 0 := by decide
theorem honestRow0_gid : honestRow0 GATE_INDEX_DELTA = 0 := by decide

theorem honestRow0_commit (j : Nat) (hj : j < 4) :
    honestRow0 (CIRCUIT_COMMITMENT + j) = honestPub j := by
  interval_cases j <;> decide

theorem honestRow0_ohash (j : Nat) (hj : j < 4) :
    honestRow0 (OUTPUT_LABEL_HASH + j) = honestPub (4 + j) := by
  interval_cases j <;> decide

/-- Row 1 of `t₀` is `honestRow0` too, so the last-row window reads it as the local row. -/
theorem envAt1_loc : (envAt t₀ 1).loc = honestRow0 := rfl

/-! ### Body-vanishing facts on `honestRow0` (shared by the row-0 active proof AND the last-row
`garbledLastRowFix` boundary proof — both must vanish on the honest row). -/

/-- The decryption body vanishes on the honest row (`0 = 0 − 0`, non-padding). -/
theorem decBody_honest (j : Nat) (hj : j < 8) : (decBody j).eval honestRow0 = 0 := by
  simp only [decBody, notPadding, EmittedExpr.eval, honestRow0_output j hj,
    honestRow0_table j hj, honestRow0_hash j hj, honestRow0_padding]; ring

/-- A boolean-selector body vanishes on the honest row when the selector reads `0` or `1`. -/
theorem binBody_honest (c : Nat) (h : honestRow0 c = 0 ∨ honestRow0 c = 1) :
    (binBody c).eval honestRow0 = 0 := by
  simp only [binBody, EmittedExpr.eval]
  rcases h with h | h <;> rw [h] <;> ring

/-- The exclusivity body vanishes on the honest row (`is_and = 1`, others `0`, non-padding). -/
theorem exclBody_honest : exclusivityBody.eval honestRow0 = 0 := by
  simp only [exclusivityBody, notPadding, EmittedExpr.eval, honestRow0_and, honestRow0_or,
    honestRow0_xor, honestRow0_not, honestRow0_padding]; ring

/-- A base gate holds on the honest FIRST row (active) from a body-vanishing fact (the ℤ zero is
lifted to the field congruence — the POSITIVE direction is mechanical). -/
theorem honest_gate_holds (hash : List ℤ → ℤ) (body : EmittedExpr)
    (h : body.eval honestRow0 = 0) :
    (VmConstraint2.base (.gate body)).holdsAt hash t₀.tf (envAt t₀ 0) (0 == 0)
      (0 + 1 == t₀.rows.length) := eqToModEq h

/-- A first-row PI binding holds on the honest first row from a column equation. -/
theorem honest_pi_holds (hash : List ℤ → ℤ) (col k : Nat) (h : honestRow0 col = honestPub k) :
    (VmConstraint2.base (.piBinding VmRow.first col k)).holdsAt hash t₀.tf (envAt t₀ 0) (0 == 0)
      (0 + 1 == t₀.rows.length) := fun _ => eqToModEq h

/-- The first-row boundary holds on the honest first row from a body-vanishing fact. -/
theorem honest_boundary_holds (hash : List ℤ → ℤ) (b : EmittedExpr) (h : b.eval honestRow0 = 0) :
    (VmConstraint2.base (.boundary VmRow.first b)).holdsAt hash t₀.tf (envAt t₀ 0) (0 == 0)
      (0 + 1 == t₀.rows.length) := fun _ => eqToModEq h

/-- A wire-chaining window gate holds on the honest first row from a body-vanishing fact. -/
theorem honest_chain_holds (hash : List ℤ → ℤ) (j : Nat)
    (h : (chainBody j).eval (envAt t₀ 0) = 0) :
    (VmConstraint2.windowGate ⟨chainBody j, true⟩).holdsAt hash t₀.tf (envAt t₀ 0) (0 == 0)
      (0 + 1 == t₀.rows.length) := fun _ => eqToModEq h

theorem honest_memOpsOf_nil : memOpsOf garbledEvalDesc = [] := by
  simp [memOpsOf, garbledEvalDesc, garbledCoreConstraints, garbledLastRowFix, commitmentPins,
    outputHashPins, decryptionGates, selectorBinaryGates, chainingGates, gateIndexDeltaBoundary,
    List.filterMap_append, List.filterMap_map]

theorem honest_mapOpsOf_nil : mapOpsOf garbledEvalDesc = [] := by
  simp [mapOpsOf, garbledEvalDesc, garbledCoreConstraints, garbledLastRowFix, commitmentPins,
    outputHashPins, decryptionGates, selectorBinaryGates, chainingGates, gateIndexDeltaBoundary,
    List.filterMap_append, List.filterMap_map]

theorem honest_memLog_nil : memLog garbledEvalDesc t₀ = [] := by
  simp [memLog, honest_memOpsOf_nil]

theorem honest_mapLog_nil : mapLog garbledEvalDesc t₀ = [] := by
  simp [mapLog, honest_mapOpsOf_nil]

/-- **`garbled_honest_satisfied2` — the SATISFYING witness.** The concrete honest two-row trace `t₀`
satisfies the emitted garbled-evaluation descriptor's `Satisfied2` (against the empty memory
boundary — the descriptor declares no mem/map ops). So the bridge hypothesis is genuinely
inhabited. -/
theorem garbled_honest_satisfied2 (hash : List ℤ → ℤ) :
    Satisfied2 hash garbledEvalDesc (fun _ => 0) (fun _ => (0, 0)) [] t₀ := by
  refine
    { rowConstraints := ?_, rowHashes := ?_, rowRanges := ?_, memAddrsNodup := ?_,
      memClosed := ?_, memDisciplined := ?_, memBalanced := ?_, memTableFaithful := ?_,
      mapTableFaithful := ?_ }
  · -- rowConstraints
    intro i hi
    rw [show t₀.rows.length = 2 from rfl] at hi
    interval_cases i
    · -- FIRST row (active): every constraint genuinely holds; the last-row fix is vacuous here
      simp only [garbledEvalDesc, garbledCoreConstraints]
      refine List.forall_mem_append.mpr ⟨List.forall_mem_append.mpr ⟨List.forall_mem_append.mpr
        ⟨List.forall_mem_append.mpr ⟨List.forall_mem_append.mpr ⟨List.forall_mem_append.mpr
          ⟨List.forall_mem_append.mpr ⟨?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩
      · -- commitmentPins
        intro c hc; simp only [commitmentPins, List.mem_map, List.mem_range] at hc
        obtain ⟨j, hj, rfl⟩ := hc
        exact honest_pi_holds hash _ _ (honestRow0_commit j hj)
      · -- outputHashPins
        intro c hc; simp only [outputHashPins, List.mem_map, List.mem_range] at hc
        obtain ⟨j, hj, rfl⟩ := hc
        exact honest_pi_holds hash _ _ (honestRow0_ohash j hj)
      · -- decryptionGates
        intro c hc; simp only [decryptionGates, List.mem_map, List.mem_range] at hc
        obtain ⟨j, hj, rfl⟩ := hc
        exact honest_gate_holds hash (decBody j) (by
          simp only [decBody, notPadding, EmittedExpr.eval, honestRow0_output j hj,
            honestRow0_table j hj, honestRow0_hash j hj, honestRow0_padding]; ring)
      · -- selectorBinaryGates
        intro c hc
        simp only [selectorBinaryGates, List.mem_cons, List.not_mem_nil,
          or_false] at hc
        rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
        · exact honest_gate_holds hash _ (by
            simp only [binBody, EmittedExpr.eval, honestRow0_and]; ring)
        · exact honest_gate_holds hash _ (by
            simp only [binBody, EmittedExpr.eval, honestRow0_or]; ring)
        · exact honest_gate_holds hash _ (by
            simp only [binBody, EmittedExpr.eval, honestRow0_xor]; ring)
        · exact honest_gate_holds hash _ (by
            simp only [binBody, EmittedExpr.eval, honestRow0_not]; ring)
        · exact honest_gate_holds hash _ (by
            simp only [binBody, EmittedExpr.eval, honestRow0_chain]; ring)
        · exact honest_gate_holds hash _ (by
            simp only [binBody, EmittedExpr.eval, honestRow0_padding]; ring)
      · -- [exclusivityBody]
        intro c hc; simp only [List.mem_singleton] at hc; subst hc
        exact honest_gate_holds hash exclusivityBody (by
          simp only [exclusivityBody, notPadding, EmittedExpr.eval, honestRow0_and, honestRow0_or,
            honestRow0_xor, honestRow0_not, honestRow0_padding]; ring)
      · -- chainingGates
        intro c hc; simp only [chainingGates, List.mem_map, List.mem_range] at hc
        obtain ⟨j, hj, rfl⟩ := hc
        exact honest_chain_holds hash j (by
          simp only [chainBody, WindowExpr.eval, envAt0_loc, envAt0_nxt, honestRow0_chain,
            honestRow0_left j hj, honestRow0_output j hj]; ring)
      · -- [gateIndexDeltaBoundary]
        intro c hc; simp only [List.mem_singleton] at hc; subst hc
        exact honest_boundary_holds hash (.var GATE_INDEX_DELTA) (by
          simp only [EmittedExpr.eval]; exact honestRow0_gid)
      · -- garbledLastRowFix: last-row boundaries, VACUOUS on the (non-last) FIRST row (isLast = false)
        simp only [garbledLastRowFix]
        refine List.forall_mem_append.mpr ⟨List.forall_mem_append.mpr ⟨?_, ?_⟩, ?_⟩
        · intro c hc; simp only [List.mem_map, List.mem_range] at hc
          obtain ⟨j, _, rfl⟩ := hc
          exact fun hcon => absurd hcon (by decide)
        · intro c hc; simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
          rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;>
            exact fun hcon => absurd hcon (by decide)
        · intro c hc; simp only [List.mem_singleton] at hc; subst hc
          exact fun hcon => absurd hcon (by decide)
    · -- LAST row: the transition gates/pins/window are vacuous; the last-row FIX bodies genuinely fire
      simp only [garbledEvalDesc, garbledCoreConstraints]
      refine List.forall_mem_append.mpr ⟨List.forall_mem_append.mpr ⟨List.forall_mem_append.mpr
        ⟨List.forall_mem_append.mpr ⟨List.forall_mem_append.mpr ⟨List.forall_mem_append.mpr
          ⟨List.forall_mem_append.mpr ⟨?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩
      · intro c hc; simp only [commitmentPins, List.mem_map, List.mem_range] at hc
        obtain ⟨j, _, rfl⟩ := hc
        exact fun hcon => absurd hcon (by decide)
      · intro c hc; simp only [outputHashPins, List.mem_map, List.mem_range] at hc
        obtain ⟨j, _, rfl⟩ := hc
        exact fun hcon => absurd hcon (by decide)
      · intro c hc; simp only [decryptionGates, List.mem_map, List.mem_range] at hc
        obtain ⟨j, _, rfl⟩ := hc
        exact True.intro
      · intro c hc
        simp only [selectorBinaryGates, List.mem_cons, List.not_mem_nil,
          or_false] at hc
        rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> exact True.intro
      · intro c hc; simp only [List.mem_singleton] at hc; subst hc; exact True.intro
      · intro c hc; simp only [chainingGates, List.mem_map, List.mem_range] at hc
        obtain ⟨j, _, rfl⟩ := hc
        exact fun hcon => absurd hcon (by decide)
      · intro c hc; simp only [List.mem_singleton] at hc; subst hc
        exact fun hcon => absurd hcon (by decide)
      · -- garbledLastRowFix: on the LAST row these boundaries FIRE (isLast = true); bodies vanish on
        -- honestRow0 (row 1 = honestRow0), exactly as they do on the active first row.
        simp only [garbledLastRowFix]
        refine List.forall_mem_append.mpr ⟨List.forall_mem_append.mpr ⟨?_, ?_⟩, ?_⟩
        · intro c hc; simp only [List.mem_map, List.mem_range] at hc
          obtain ⟨j, hj, rfl⟩ := hc
          exact fun _ => by rw [envAt1_loc]; exact eqToModEq (decBody_honest j hj)
        · intro c hc; simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
          rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
          · exact fun _ => by
              rw [envAt1_loc]; exact eqToModEq (binBody_honest _ (Or.inr honestRow0_and))
          · exact fun _ => by
              rw [envAt1_loc]; exact eqToModEq (binBody_honest _ (Or.inl honestRow0_or))
          · exact fun _ => by
              rw [envAt1_loc]; exact eqToModEq (binBody_honest _ (Or.inl honestRow0_xor))
          · exact fun _ => by
              rw [envAt1_loc]; exact eqToModEq (binBody_honest _ (Or.inl honestRow0_not))
          · exact fun _ => by
              rw [envAt1_loc]; exact eqToModEq (binBody_honest _ (Or.inr honestRow0_chain))
          · exact fun _ => by
              rw [envAt1_loc]; exact eqToModEq (binBody_honest _ (Or.inl honestRow0_padding))
        · intro c hc; simp only [List.mem_singleton] at hc; subst hc
          exact fun _ => by rw [envAt1_loc]; exact eqToModEq exclBody_honest
  · -- rowHashes (hashSites = [])
    intro i _; exact True.intro
  · -- rowRanges (ranges = [])
    intro i _ r hr; exact absurd hr (by simp [garbledEvalDesc])
  · exact List.nodup_nil
  · intro op hop; rw [honest_memLog_nil] at hop; exact absurd hop (by simp)
  · rw [honest_memLog_nil]; exact True.intro
  · rw [honest_memLog_nil]
    simp [MemoryChecking.MemCheck, MemoryChecking.initSet, MemoryChecking.finalSet]
  · rw [honest_memLog_nil]; rfl
  · rw [honest_mapLog_nil]; rfl

/-- **`garbled_honest_decrypts_nonvacuous`** — the honest first row is NON-PADDING, so the decryption
constraint is ACTIVE (not the padding escape), and its Yao decryption equality genuinely holds
(`output = table − hash` on every lane). This is why the satisfying witness is not vacuous. -/
theorem garbled_honest_decrypts_nonvacuous :
    (envAt t₀ 0).loc IS_PADDING = 0
    ∧ ∀ j, j < 8 →
        (envAt t₀ 0).loc (OUTPUT j)
          = (envAt t₀ 0).loc (TABLE_ENTRY j) - (envAt t₀ 0).loc (HASH_OUT j) := by
  refine ⟨honestRow0_padding, fun j hj => ?_⟩
  simp only [envAt0_loc, honestRow0_output j hj, honestRow0_table j hj, honestRow0_hash j hj,
    sub_zero]

/-- **The honest witness inhabits the canonicality envelope** — every enveloped cell of both rows
is `0`/`1` and the bound columns/public inputs are the small values `100..107`, all canonical. -/
theorem t₀_canon : GarbledTraceCanon t₀ := by
  have hlen : t₀.rows.length = 2 := rfl
  have hrow : ∀ i, i < t₀.rows.length → (envAt t₀ i).loc = honestRow0 := by
    intro i hi
    rw [hlen] at hi
    interval_cases i <;> rfl
  have hsel : ∀ c : Nat, (0 ≤ honestRow0 c ∧ honestRow0 c < 2013265921) →
      ∀ i, i < t₀.rows.length → CanonCell ((envAt t₀ i).loc c) := by
    intro c hc i hi
    rw [hrow i hi]; exact hc
  refine ⟨hsel _ ⟨by decide, by decide⟩, hsel _ ⟨by decide, by decide⟩,
    hsel _ ⟨by decide, by decide⟩, hsel _ ⟨by decide, by decide⟩,
    hsel _ ⟨by decide, by decide⟩, hsel _ ⟨by decide, by decide⟩,
    ?_, ?_, ?_, ?_, ⟨by decide, by decide⟩, ?_⟩
  · intro i hi j hj
    interval_cases j <;> exact hsel _ ⟨by decide, by decide⟩ i hi
  · intro i hi j hj
    interval_cases j <;> exact hsel _ ⟨by decide, by decide⟩ i hi
  · intro j hj
    interval_cases j <;> exact ⟨by decide, by decide⟩
  · intro j hj
    interval_cases j <;> exact ⟨by decide, by decide⟩
  · intro k hk
    interval_cases k <;> exact ⟨by decide, by decide⟩

/-- The honest trace is a genuine `GarbledEvalRun` — the bridge fired on a real satisfying witness. -/
theorem garbled_honest_run : GarbledEvalRun t₀ :=
  satisfied2_implies_garbledEvalRun (fun _ => 0) (fun _ => 0) (fun _ => (0, 0)) [] t₀
    t₀_canon (garbled_honest_satisfied2 (fun _ => 0))

/-! ## §7 — Non-vacuity, part B: a CONCRETE trace the descriptor REJECTS (the constraint bites). -/

/-- A forged row: output label lane 0 is `5` while its table/hash lanes are `0`, so the lane-0
decryption `output(0) = table_entry(0) − hash_out(0)` (`5 = 0 − 0`) is BROKEN on a non-padding row. -/
def forgedRow0 : Assignment := fun c => if c = OUTPUT 0 then 5 else 0

/-- A two-row trace carrying the forged row first. -/
def tBad : VmTrace := { rows := [forgedRow0, zeroAsg], pub := zeroAsg, tf := fun _ => [] }

/-- **`garbled_forged_not_satisfied2` — the REJECTING witness.** The forged trace's broken lane-0
decryption makes the decryption gate FAIL on the active first row, so the descriptor's `Satisfied2`
is refuted: the constraint genuinely bites (this is not a `True`/`P → P` hypothesis). -/
theorem garbled_forged_not_satisfied2
    (hash : List ℤ → ℤ) (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) :
    ¬ Satisfied2 hash garbledEvalDesc minit mfin maddrs tBad := by
  intro h
  have hi : (0 : Nat) < tBad.rows.length := by decide
  have hlast : (0 : Nat) + 1 ≠ tBad.rows.length := by decide
  have hg := gate_forces hash minit mfin maddrs tBad h 0 hi hlast (decBody 0)
    (decGate_mem 0 (by decide))
  have hval : (decBody 0).eval (envAt tBad 0).loc = 5 := by
    have e0 : (envAt tBad 0).loc = forgedRow0 := rfl
    rw [e0]
    simp only [decBody, notPadding, EmittedExpr.eval, forgedRow0, OUTPUT, TABLE_ENTRY, HASH_OUT,
      IS_PADDING]
    norm_num
  -- The forged lane's gate residual is `5`, and `p ∤ 5` — the field gate bites.
  rw [hval] at hg
  obtain ⟨k, hk⟩ := Int.modEq_zero_iff_dvd.mp hg
  omega

#assert_axioms garbled_honest_satisfied2
#assert_axioms garbled_forged_not_satisfied2

end Dregg2.Circuit.Emit.GarbledEvalRefine
