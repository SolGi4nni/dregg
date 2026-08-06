/-
# Dregg2.Circuit.Emit.GarbledEvalRefineBridge — the FOLDED `air_accepts ⟺ spec` bridge for the
GARBLED-EVALUATION family: ONE named carrier bundle, accept-SET ↔ spec, ∀-soundness ∧ ∃-completeness.

## Why this file exists (the assurance-perimeter template, applied to garbled-eval)

`GarbledEvalRefine` (RUNG 1) proves `satisfied2_implies_garbledEvalRun` (SAT ⟹ SEM against the
`GarbledTraceCanon` range envelope) and inhabits it with a CONCRETE honest witness
(`garbled_honest_satisfied2` at the single point `t₀`). `GarbledEvalRung2` supplies the
executor-verified Poseidon2 garbling-hash carrier `GarblingHashBound` and, under it, discharges the
free-`hash_out` residual (`garbled_rung2_no_output_forgery`: SAT + canon + hash ⟹ the genuine
one-time-pad decryption `output = HonestOutput`).

This file does the LAST MILE the assurance-perimeter campaign asks for, mirroring
`NonRevocationRefineBridge` (`209d543e5`): **fold the residual trust into ONE named carrier bundle
(`GarbledCarriers`) and state the honest two-directional object** — an accept-SET ↔ spec biconditional
(`garbled_accepts_iff`) plus a ∀-soundness ∧ ∃-completeness bridge (`garbled_bridge`), the completeness
leg **generalizing `garbled_honest_satisfied2` from the single point `t₀` to the whole `∀`-family**
(any canonical public commitment + any canonical output labels), constructing the trace AND its carriers
(not assuming them). See `docs/DESIGN-assurance-perimeter-closure.md`.

## THE 5-STEP SCHEMA (mirrors the non-rev header)

  1. **Semantic relation.** `GarbledEvalRunH gh t` (§1) — `GarbledEvalRun t` (RUNG 1's whole-trace
     functional spec) PLUS the H-strengthened decryption leg `output(j) ≡ HonestOutput gh (row) j`
     (the genuine Yao one-time-pad under the REAL garbling hash `gh`).
  2. **SAT ⟹ SEM vs NAMED carriers.** `garbled_sound` (§2): a satisfying trace + the named bundle
     force `GarbledEvalRunH`. Folds `satisfied2_implies_garbledEvalRun` (via `canon`) and
     `garbled_rung2_no_output_forgery` (via `hash`) behind `GarbledCarriers`.
  3. **Construct the satisfying trace.** `hRowG` / `honestTraceG` (§3), PARAMETRIC over
     `(pub, o, hsh)`; `honestG_satisfied2` proves `Satisfied2` UNCONDITIONALLY (like the non-rev
     `sem_satisfied` — the gates vanish by the table-entry derivation `table = output + hash`,
     independent of the values), generalizing `garbled_honest_satisfied2` off the point `t₀`.
  4. **Construct AND PROVE the carriers (never assume).** `honestG_canon` (`GarbledTraceCanon` from
     canonicality of `pub`,`o`) and `honestG_hashBound` (`GarblingHashBound` from the derived
     `hash_out(j) = gh [inputs] j` — the ONE place the garbling-hash carrier is built, not assumed).
  5. **Round-trip / compose the `⟺`.** `garbled_accepts_iff` (§5, accept-set = canonical instances,
     both directions load-bearing modulo the folded carriers) and `garbled_bridge` (§6, the
     ∀-soundness ∧ ∃-completeness conjunction concluding the literal `GarbledEvalRunH`).

## The ONE named carrier bundle (the honest floor, shared with the non-rev template's shape)

`GarbledCarriers gh t` (§1) folds EVERYTHING between `Satisfied2` and `GarbledEvalRunH`:
  * `canon` — `GarbledTraceCanon` (the deployed 30-bit range-check envelope: selectors/labels/committed
              columns canonical — the ℤ-vs-BabyBear wrap-freeness the decryption/booleanity read back);
  * `hash`  — `GarblingHashBound gh` (the executor-verified Poseidon2 garbling-hash binding
              `hash_out(j) = gh [left‖right‖gate_index] j` — the off-descriptor carrier `GarbledEvalEmit`
              NAMES; Poseidon2 preimage/collision resistance is what makes forging `hash_out` hard).
The multi-table plumbing (`memOps`/`mapOps`/`hashSites`/`ranges`) is EMPTY for this descriptor and is
discharged as a hygiene fact (`memLogG_nil` / `mapLogG_nil`), not a trusted carrier.

## Why accept-SET ↔ spec, not a per-trace `Satisfied2 ↔ GarbledEvalRunH`

The reusable lesson (same as non-rev): `honestG_satisfied2` proves `Satisfied2` on the constructed
family **unconditionally** — the honest table entry is DERIVED (`table = output + hash`), so the
decryption gate `output − table + hash = 0` vanishes for ANY `output`/`hash`, and the canonicality /
genuine-hash content lives in the `canon` / `hash` CARRIERS, not the gates. So a single-trace iff would
degenerate (`Satisfied2` constant-true on the family). The honest renderings:
  * `garbled_accepts_iff` — the accept-set (constructed traces the deployed descriptor SATISFIES with
    both carriers) is EXACTLY the canonical instances: `AirAccepts gh pub o ↔ CanonInstance pub o`.
    Both directions real, modulo the carriers folded into `AirAccepts`; `garbled_accepts_run` is the tie
    to the human spec (an accepted instance IS a genuine garbled-eval run under the real hash).
  * `garbled_bridge` — soundness over ALL traces (the hostile-prover guarantee) ∧ completeness (∃ a
    satisfying trace realizing any canonical instance), the codebase idiom.

## Axiom hygiene
`#assert_axioms` ⊆ {propext, Classical.choice, Quot.sound}. No `sorry`/`axiom`/`native_decide`. The
crypto trust enters ONLY as the named `GarbledCarriers` fields. NEW file; every import read-only; the
committed RUNG-1 / RUNG-2 proofs are untouched.
-/
import Dregg2.Circuit.Emit.GarbledEvalRung2

namespace Dregg2.Circuit.Emit.GarbledEvalRefineBridge

open Dregg2.Circuit (Assignment)
open Dregg2.Exec.CircuitEmit (EmittedExpr)
open Dregg2.Circuit.DescriptorIR2
  (EffectVmDescriptor2 VmConstraint2 Satisfied2 VmTrace envAt WindowConstraint WindowExpr
   zeroAsg memLog mapLog memOpsOf mapOpsOf)
open Dregg2.Circuit.Emit.EffectVmEmit (VmConstraint VmRow VmRowEnv)
open Dregg2.Circuit.Emit.GarbledEvalEmit
open Dregg2.Circuit.Emit.GarbledEvalRefine
open Dregg2.Circuit.Emit.GarbledEvalRung2
open Dregg2.Circuit.Emit.EffectVmEmitTransfer (eqToModEq)
open Dregg2.Crypto

set_option autoImplicit false

/-! ## §1 — the ONE named carrier bundle + the H-strengthened whole-trace spec. -/

/-- **`GarbledCarriers gh t` — THE named carrier bundle.** Everything the soundness bridge trusts
between a satisfying trace and a genuine garbled-circuit evaluation under the REAL garbling hash `gh`,
folded into one structure: the deployed range-check envelope (`canon`) and the executor-verified
Poseidon2 garbling-hash binding (`hash`). Nothing else is assumed; the empty multi-table plumbing is a
hygiene fact, not a carrier. This is the single honest floor the garbled surface shares. -/
structure GarbledCarriers (gh : List ℤ → Nat → ℤ) (t : VmTrace) : Prop where
  /-- The deployed 30-bit range-check envelope (selectors/labels/committed columns canonical). -/
  canon : GarbledTraceCanon t
  /-- The executor-verified Poseidon2 garbling-hash binding (`hash_out(j) = gh [inputs] j`). -/
  hash  : GarblingHashBound gh t

/-- **`GarbledEvalRunH gh t` — the H-strengthened whole-trace spec.** `GarbledEvalRun t` (RUNG 1's
functional spec: every active row decrypts, is a well-formed gate, chains its wires; the first row binds
the commitment/output-hash and initializes the gate index) PLUS the decryption leg read back under the
GENUINE garbling hash: each active non-padding row's `output(j)` is EXACTLY the honest one-time-pad
decryption `HonestOutput gh (row) j = table_entry(j) − gh [inputs] j` (mod `p` — the deployed field
subtraction wraps, so honestly a congruence). This is output-label NON-FORGEABILITY: no forged label
survives the free-`hash_out` residual once the garbling-hash carrier pins the digest columns. -/
structure GarbledEvalRunH (gh : List ℤ → Nat → ℤ) (t : VmTrace) : Prop where
  /-- RUNG 1's whole-trace functional relation (decrypts / wellFormed / chains / committed / gateInit). -/
  base : GarbledEvalRun t
  /-- The genuine Yao decryption under the REAL garbling hash, per active non-padding row/lane. -/
  decryptsHonest : ∀ i, i + 1 < t.rows.length → (envAt t i).loc IS_PADDING = 0 →
    ∀ j, j < 8 →
      (envAt t i).loc (OUTPUT j) ≡ HonestOutput gh (envAt t i).loc j [ZMOD 2013265921]

/-! ## §2 — the SOUNDNESS leg, folded (step 2 of the schema). -/

/-- **`garbled_sound` — the SOUNDNESS leg, folded.** A satisfying trace carrying the named bundle is a
genuine garbled-circuit evaluation run under the real hash: `Satisfied2 ⟹ GarbledEvalRunH gh t`. This
is the hostile-prover guarantee (∀ traces, not the constructed family); it repackages RUNG 1's
`satisfied2_implies_garbledEvalRun` (via `canon`) and RUNG 2's `garbled_rung2_no_output_forgery` (via
`hash`) behind `GarbledCarriers`. -/
theorem garbled_sound (gh : List ℤ → Nat → ℤ)
    (hash : List ℤ → ℤ) (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (t : VmTrace)
    (C : GarbledCarriers gh t)
    (hsat : Satisfied2 hash garbledEvalDesc minit mfin maddrs t) :
    GarbledEvalRunH gh t where
  base := satisfied2_implies_garbledEvalRun hash minit mfin maddrs t C.canon hsat
  decryptsHonest := garbled_rung2_no_output_forgery gh hash minit mfin maddrs t C.canon hsat C.hash

/-! ## §3 — the parametric honest trace (generalizing `garbled_honest_satisfied2` off the point `t₀`).

`hRowG pub o hsh` is one honest garbled-gate row: an AND gate (`is_and = 1`), non-padding, NOT chaining
(`chain_flag = 0`), whose output lanes are the free labels `o`, whose digest lanes are `hsh`, and whose
GARBLED-TABLE lanes are the honest ENCRYPTION `table_entry(j) = output(j) + hash_out(j) = o j + hsh j`
(so decryption `output − table + hash = o − (o+hsh) + hsh = 0` holds by DERIVATION, for ANY `o`,`hsh`),
with the commitment / output-label-hash blocks bound to the 8 public inputs `pub`. All input labels
(`left`,`right`,`gate_index`) are `0`, so the garbling preimage is the constant `zeroInputs`. -/
def hRowG (pub : Assignment) (o hsh : Nat → ℤ) : Assignment := fun c =>
  if 17 ≤ c ∧ c ≤ 24 then hsh (c - 17)                    -- HASH_OUT j (17..24)
  else if 25 ≤ c ∧ c ≤ 32 then o (c - 25) + hsh (c - 25)  -- TABLE_ENTRY j (25..32) = o j + hsh j
  else if 33 ≤ c ∧ c ≤ 40 then o (c - 33)                 -- OUTPUT j (33..40)
  else if 41 ≤ c ∧ c ≤ 44 then pub (c - 41)               -- CIRCUIT_COMMITMENT+j (41..44)
  else if 45 ≤ c ∧ c ≤ 48 then pub (c - 41)               -- OUTPUT_LABEL_HASH+j (45..48) = pub(4+(c-45))
  else if c = 49 then 1                                    -- IS_AND
  else 0

/-- The two-row honest witness (row 1 is the last row). Both rows are `hRowG`; the descriptor declares
no mem/map ops, so the boundary is empty. -/
def honestTraceG (pub : Assignment) (o hsh : Nat → ℤ) : VmTrace :=
  { rows := [hRowG pub o hsh, hRowG pub o hsh], pub := pub, tf := fun _ => [] }

theorem envAtG0_loc (pub : Assignment) (o hsh : Nat → ℤ) :
    (envAt (honestTraceG pub o hsh) 0).loc = hRowG pub o hsh := rfl
theorem envAtG0_nxt (pub : Assignment) (o hsh : Nat → ℤ) :
    (envAt (honestTraceG pub o hsh) 0).nxt = hRowG pub o hsh := rfl
theorem envAtG1_loc (pub : Assignment) (o hsh : Nat → ℤ) :
    (envAt (honestTraceG pub o hsh) 1).loc = hRowG pub o hsh := rfl
theorem honestTraceG_len (pub : Assignment) (o hsh : Nat → ℤ) :
    (honestTraceG pub o hsh).rows.length = 2 := rfl

/-! ### Column reads on `hRowG` (parametric — the family cursor). -/

theorem hRowG_hash (pub : Assignment) (o hsh : Nat → ℤ) (j : Nat) (hj : j < 8) :
    hRowG pub o hsh (HASH_OUT j) = hsh j := by
  rw [show HASH_OUT j = 17 + j from rfl]; unfold hRowG
  rw [if_pos (by omega : 17 ≤ 17 + j ∧ 17 + j ≤ 24)]
  congr 1; omega

theorem hRowG_table (pub : Assignment) (o hsh : Nat → ℤ) (j : Nat) (hj : j < 8) :
    hRowG pub o hsh (TABLE_ENTRY j) = o j + hsh j := by
  rw [show TABLE_ENTRY j = 25 + j from rfl]; unfold hRowG
  rw [if_neg (by omega : ¬ (17 ≤ 25 + j ∧ 25 + j ≤ 24)),
    if_pos (by omega : 25 ≤ 25 + j ∧ 25 + j ≤ 32)]
  have h : 25 + j - 25 = j := by omega
  rw [h]

theorem hRowG_output (pub : Assignment) (o hsh : Nat → ℤ) (j : Nat) (hj : j < 8) :
    hRowG pub o hsh (OUTPUT j) = o j := by
  rw [show OUTPUT j = 33 + j from rfl]; unfold hRowG
  rw [if_neg (by omega : ¬ (17 ≤ 33 + j ∧ 33 + j ≤ 24)),
    if_neg (by omega : ¬ (25 ≤ 33 + j ∧ 33 + j ≤ 32)),
    if_pos (by omega : 33 ≤ 33 + j ∧ 33 + j ≤ 40)]
  congr 1; omega

theorem hRowG_commit (pub : Assignment) (o hsh : Nat → ℤ) (j : Nat) (hj : j < 4) :
    hRowG pub o hsh (CIRCUIT_COMMITMENT + j) = pub j := by
  rw [show CIRCUIT_COMMITMENT + j = 41 + j from rfl]; unfold hRowG
  rw [if_neg (by omega : ¬ (17 ≤ 41 + j ∧ 41 + j ≤ 24)),
    if_neg (by omega : ¬ (25 ≤ 41 + j ∧ 41 + j ≤ 32)),
    if_neg (by omega : ¬ (33 ≤ 41 + j ∧ 41 + j ≤ 40)),
    if_pos (by omega : 41 ≤ 41 + j ∧ 41 + j ≤ 44)]
  rw [show (41 + j - 41 : Nat) = j from by omega]

theorem hRowG_ohash (pub : Assignment) (o hsh : Nat → ℤ) (j : Nat) (hj : j < 4) :
    hRowG pub o hsh (OUTPUT_LABEL_HASH + j) = pub (4 + j) := by
  rw [show OUTPUT_LABEL_HASH + j = 45 + j from rfl]; unfold hRowG
  rw [if_neg (by omega : ¬ (17 ≤ 45 + j ∧ 45 + j ≤ 24)),
    if_neg (by omega : ¬ (25 ≤ 45 + j ∧ 45 + j ≤ 32)),
    if_neg (by omega : ¬ (33 ≤ 45 + j ∧ 45 + j ≤ 40)),
    if_neg (by omega : ¬ (41 ≤ 45 + j ∧ 45 + j ≤ 44)),
    if_pos (by omega : 45 ≤ 45 + j ∧ 45 + j ≤ 48)]
  rw [show (45 + j - 41 : Nat) = 4 + j from by omega]

theorem hRowG_and (pub : Assignment) (o hsh : Nat → ℤ) : hRowG pub o hsh IS_AND = 1 := by
  simp only [IS_AND, hRowG]; norm_num

theorem hRowG_or (pub : Assignment) (o hsh : Nat → ℤ) : hRowG pub o hsh IS_OR = 0 := by
  simp only [IS_OR, hRowG]; norm_num

theorem hRowG_xor (pub : Assignment) (o hsh : Nat → ℤ) : hRowG pub o hsh IS_XOR = 0 := by
  simp only [IS_XOR, hRowG]; norm_num

theorem hRowG_not (pub : Assignment) (o hsh : Nat → ℤ) : hRowG pub o hsh IS_NOT = 0 := by
  simp only [IS_NOT, hRowG]; norm_num

theorem hRowG_chain (pub : Assignment) (o hsh : Nat → ℤ) : hRowG pub o hsh CHAIN_FLAG = 0 := by
  simp only [CHAIN_FLAG, hRowG]; norm_num

theorem hRowG_padding (pub : Assignment) (o hsh : Nat → ℤ) : hRowG pub o hsh IS_PADDING = 0 := by
  simp only [IS_PADDING, hRowG]; norm_num

theorem hRowG_gid (pub : Assignment) (o hsh : Nat → ℤ) : hRowG pub o hsh GATE_INDEX_DELTA = 0 := by
  simp only [GATE_INDEX_DELTA, hRowG]; norm_num

theorem hRowG_gindex (pub : Assignment) (o hsh : Nat → ℤ) : hRowG pub o hsh GATE_INDEX = 0 := by
  simp only [GATE_INDEX, hRowG]; norm_num

theorem hRowG_left (pub : Assignment) (o hsh : Nat → ℤ) (j : Nat) (hj : j < 8) :
    hRowG pub o hsh (LEFT j) = 0 := by
  rw [show LEFT j = 0 + j from rfl]; unfold hRowG
  rw [if_neg (by omega : ¬ (17 ≤ 0 + j ∧ 0 + j ≤ 24)),
    if_neg (by omega : ¬ (25 ≤ 0 + j ∧ 0 + j ≤ 32)),
    if_neg (by omega : ¬ (33 ≤ 0 + j ∧ 0 + j ≤ 40)),
    if_neg (by omega : ¬ (41 ≤ 0 + j ∧ 0 + j ≤ 44)),
    if_neg (by omega : ¬ (45 ≤ 0 + j ∧ 0 + j ≤ 48)),
    if_neg (by omega : ¬ (0 + j = 49))]

theorem hRowG_right (pub : Assignment) (o hsh : Nat → ℤ) (j : Nat) (hj : j < 8) :
    hRowG pub o hsh (RIGHT j) = 0 := by
  rw [show RIGHT j = 8 + j from rfl]; unfold hRowG
  rw [if_neg (by omega : ¬ (17 ≤ 8 + j ∧ 8 + j ≤ 24)),
    if_neg (by omega : ¬ (25 ≤ 8 + j ∧ 8 + j ≤ 32)),
    if_neg (by omega : ¬ (33 ≤ 8 + j ∧ 8 + j ≤ 40)),
    if_neg (by omega : ¬ (41 ≤ 8 + j ∧ 8 + j ≤ 44)),
    if_neg (by omega : ¬ (45 ≤ 8 + j ∧ 8 + j ≤ 48)),
    if_neg (by omega : ¬ (8 + j = 49))]

/-! ### The garbling preimage of `hRowG` is the constant all-zero-input list. -/

/-- The garbling preimage of the honest row: all input labels are `0`, so
`GateInputs (hRowG …) = 0^8 ‖ 0^8 ‖ [0]`. -/
def zeroInputs : List ℤ :=
  (List.range 8).map (fun _ => (0 : ℤ)) ++ (List.range 8).map (fun _ => (0 : ℤ)) ++ [(0 : ℤ)]

theorem GateInputs_hRowG (pub : Assignment) (o hsh : Nat → ℤ) :
    GateInputs (hRowG pub o hsh) = zeroInputs := by
  simp only [GateInputs, zeroInputs, hRowG_gindex]
  refine congrArg₂ (· ++ ·) (congrArg₂ (· ++ ·) ?_ ?_) rfl
  · exact List.map_congr_left (fun j hj => hRowG_left pub o hsh j (List.mem_range.mp hj))
  · exact List.map_congr_left (fun j hj => hRowG_right pub o hsh j (List.mem_range.mp hj))

/-! ### Body-vanishing facts on `hRowG` (the gates vanish by DERIVATION, for ANY `pub`,`o`,`hsh`). -/

/-- The decryption body vanishes: `output − table + hash = o j − (o j + hsh j) + hsh j = 0` (the
honest table entry is `table = output + hash`, so decryption holds for ANY labels). -/
theorem decBodyG_zero (pub : Assignment) (o hsh : Nat → ℤ) (j : Nat) (hj : j < 8) :
    (decBody j).eval (hRowG pub o hsh) = 0 := by
  simp only [decBody, notPadding, EmittedExpr.eval, hRowG_output pub o hsh j hj,
    hRowG_table pub o hsh j hj, hRowG_hash pub o hsh j hj, hRowG_padding]; ring

/-- The AND selector body vanishes (`is_and = 1`, `1·(1−1) = 0`). -/
theorem binBodyG_and (pub : Assignment) (o hsh : Nat → ℤ) :
    (binBody IS_AND).eval (hRowG pub o hsh) = 0 := by
  simp only [binBody_eq, EmittedExpr.eval, hRowG_and]; ring

/-- A boolean-selector body vanishes when its selector reads `0`. -/
theorem binBodyG_off (pub : Assignment) (o hsh : Nat → ℤ) (c : Nat)
    (h : hRowG pub o hsh c = 0) : (binBody c).eval (hRowG pub o hsh) = 0 := by
  simp only [binBody_eq, EmittedExpr.eval, h]; ring

/-- The exclusivity body vanishes (`is_and = 1`, others `0`, non-padding). -/
theorem exclBodyG_zero (pub : Assignment) (o hsh : Nat → ℤ) :
    exclusivityBody.eval (hRowG pub o hsh) = 0 := by
  simp only [exclusivityBody, notPadding, EmittedExpr.eval, hRowG_and, hRowG_or, hRowG_xor,
    hRowG_not, hRowG_padding]; ring

/-- The wire-chaining body vanishes on row 0 (`chain_flag = 0`, so `0 · (…) = 0`). -/
theorem chainBodyG_zero (pub : Assignment) (o hsh : Nat → ℤ) (j : Nat) :
    (chainBody j).eval (envAt (honestTraceG pub o hsh) 0) = 0 := by
  simp only [chainBody_eq, WindowExpr.eval, envAtG0_loc, envAtG0_nxt, hRowG_chain]; ring

/-! ### Constraint-holds helpers on the honest two-row trace (lift ℤ-zero to the field congruence). -/

/-- A base gate holds on the honest FIRST (active) row from a body-vanishing fact. -/
theorem hg_gate (hash : List ℤ → ℤ) (pub : Assignment) (o hsh : Nat → ℤ)
    (body : EmittedExpr) (h : body.eval (hRowG pub o hsh) = 0) :
    (VmConstraint2.base (.gate body)).holdsAt hash (honestTraceG pub o hsh).tf
      (envAt (honestTraceG pub o hsh) 0) (0 == 0) (0 + 1 == (honestTraceG pub o hsh).rows.length) :=
  eqToModEq h

/-- A first-row PI binding holds on the honest first row from a column equation. -/
theorem hg_pi (hash : List ℤ → ℤ) (pub : Assignment) (o hsh : Nat → ℤ)
    (col k : Nat) (h : hRowG pub o hsh col = pub k) :
    (VmConstraint2.base (.piBinding VmRow.first col k)).holdsAt hash (honestTraceG pub o hsh).tf
      (envAt (honestTraceG pub o hsh) 0) (0 == 0) (0 + 1 == (honestTraceG pub o hsh).rows.length) :=
  fun _ => eqToModEq h

/-- The first-row boundary holds on the honest first row from a body-vanishing fact. -/
theorem hg_boundary (hash : List ℤ → ℤ) (pub : Assignment) (o hsh : Nat → ℤ)
    (b : EmittedExpr) (h : b.eval (hRowG pub o hsh) = 0) :
    (VmConstraint2.base (.boundary VmRow.first b)).holdsAt hash (honestTraceG pub o hsh).tf
      (envAt (honestTraceG pub o hsh) 0) (0 == 0) (0 + 1 == (honestTraceG pub o hsh).rows.length) :=
  fun _ => eqToModEq h

/-- A wire-chaining window gate holds on the honest first row from a body-vanishing fact. -/
theorem hg_chain (hash : List ℤ → ℤ) (pub : Assignment) (o hsh : Nat → ℤ)
    (j : Nat) (h : (chainBody j).eval (envAt (honestTraceG pub o hsh) 0) = 0) :
    (VmConstraint2.windowGate ⟨chainBody j, true⟩).holdsAt hash (honestTraceG pub o hsh).tf
      (envAt (honestTraceG pub o hsh) 0) (0 == 0) (0 + 1 == (honestTraceG pub o hsh).rows.length) :=
  fun _ => eqToModEq h

/-- A last-row boundary fix holds on the honest LAST row from a body-vanishing fact (row 1 is `hRowG`). -/
theorem hlast_boundary (hash : List ℤ → ℤ) (pub : Assignment) (o hsh : Nat → ℤ)
    (b : EmittedExpr) (h : b.eval (hRowG pub o hsh) = 0) :
    (VmConstraint2.base (.boundary VmRow.last b)).holdsAt hash (honestTraceG pub o hsh).tf
      (envAt (honestTraceG pub o hsh) 1) (1 == 0) (1 + 1 == (honestTraceG pub o hsh).rows.length) :=
  fun _ => eqToModEq h

/-! ### Memory/map plumbing is empty for this descriptor (hygiene, not a carrier). -/

theorem memLogG_nil (pub : Assignment) (o hsh : Nat → ℤ) :
    memLog garbledEvalDesc (honestTraceG pub o hsh) = [] := by
  simp [memLog, honest_memOpsOf_nil]

theorem mapLogG_nil (pub : Assignment) (o hsh : Nat → ℤ) :
    mapLog garbledEvalDesc (honestTraceG pub o hsh) = [] := by
  simp [mapLog, honest_mapOpsOf_nil]

/-! ## §4 — `honestG_satisfied2`: the PARAMETRIC satisfying witness (generalizes `garbled_honest_satisfied2`). -/

/-- **`honestG_satisfied2` — the SATISFYING witness, PARAMETRIC over `(pub, o, hsh)`.** The honest
two-row trace `honestTraceG pub o hsh` satisfies the emitted garbled-evaluation descriptor's
`Satisfied2` UNCONDITIONALLY — for ANY public commitment `pub`, output labels `o`, digest lanes `hsh`.
This generalizes RUNG 1's single-point `garbled_honest_satisfied2` (fixed `pub = 100..107`, `o = 0`,
`chain = 1`) to the whole family: the decryption gate vanishes because the table entry is DERIVED
(`table = output + hash`), the selectors are the fixed AND pattern, `chain_flag = 0` makes the wire
chaining vacuous, and the commitment/output-hash blocks are pinned to `pub`. -/
theorem honestG_satisfied2 (hash : List ℤ → ℤ) (pub : Assignment) (o hsh : Nat → ℤ) :
    Satisfied2 hash garbledEvalDesc (fun _ => 0) (fun _ => (0, 0)) [] (honestTraceG pub o hsh) := by
  refine
    { rowConstraints := ?_, rowHashes := ?_, rowRanges := ?_, memAddrsNodup := ?_,
      memClosed := ?_, memDisciplined := ?_, memBalanced := ?_, memTableFaithful := ?_,
      mapTableFaithful := ?_ }
  · intro i hi
    rw [show (honestTraceG pub o hsh).rows.length = 2 from rfl] at hi
    interval_cases i
    · -- FIRST row (active): every constraint genuinely holds; the last-row fix is vacuous here.
      simp only [garbledEvalDesc, garbledCoreConstraints]
      refine List.forall_mem_append.mpr ⟨List.forall_mem_append.mpr ⟨List.forall_mem_append.mpr
        ⟨List.forall_mem_append.mpr ⟨List.forall_mem_append.mpr ⟨List.forall_mem_append.mpr
          ⟨List.forall_mem_append.mpr ⟨?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩
      · intro c hc; simp only [commitmentPins, List.mem_map, List.mem_range] at hc
        obtain ⟨j, hj, rfl⟩ := hc
        exact hg_pi hash pub o hsh _ _ (hRowG_commit pub o hsh j hj)
      · intro c hc; simp only [outputHashPins, List.mem_map, List.mem_range] at hc
        obtain ⟨j, hj, rfl⟩ := hc
        exact hg_pi hash pub o hsh _ _ (hRowG_ohash pub o hsh j hj)
      · intro c hc; simp only [decryptionGates, List.mem_map, List.mem_range] at hc
        obtain ⟨j, hj, rfl⟩ := hc
        exact hg_gate hash pub o hsh (decBody j) (decBodyG_zero pub o hsh j hj)
      · intro c hc
        simp only [selectorBinaryGates, List.mem_cons, List.not_mem_nil, or_false] at hc
        rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
        · exact hg_gate hash pub o hsh _ (binBodyG_and pub o hsh)
        · exact hg_gate hash pub o hsh _ (binBodyG_off pub o hsh _ (hRowG_or pub o hsh))
        · exact hg_gate hash pub o hsh _ (binBodyG_off pub o hsh _ (hRowG_xor pub o hsh))
        · exact hg_gate hash pub o hsh _ (binBodyG_off pub o hsh _ (hRowG_not pub o hsh))
        · exact hg_gate hash pub o hsh _ (binBodyG_off pub o hsh _ (hRowG_chain pub o hsh))
        · exact hg_gate hash pub o hsh _ (binBodyG_off pub o hsh _ (hRowG_padding pub o hsh))
      · intro c hc; simp only [List.mem_singleton] at hc; subst hc
        exact hg_gate hash pub o hsh exclusivityBody (exclBodyG_zero pub o hsh)
      · intro c hc; simp only [chainingGates, List.mem_map, List.mem_range] at hc
        obtain ⟨j, _, rfl⟩ := hc
        exact hg_chain hash pub o hsh j (chainBodyG_zero pub o hsh j)
      · intro c hc; simp only [List.mem_singleton] at hc; subst hc
        exact hg_boundary hash pub o hsh (.var GATE_INDEX_DELTA) (by
          simp only [EmittedExpr.eval]; exact hRowG_gid pub o hsh)
      · -- garbledLastRowFix: last-row boundaries, VACUOUS on the (non-last) FIRST row.
        simp only [garbledLastRowFix]
        refine List.forall_mem_append.mpr ⟨List.forall_mem_append.mpr ⟨?_, ?_⟩, ?_⟩
        · intro c hc; simp only [List.mem_map, List.mem_range] at hc
          obtain ⟨j, _, rfl⟩ := hc
          exact fun hcon => absurd hcon (by rw [honestTraceG_len]; decide)
        · intro c hc; simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
          rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;>
            exact fun hcon => absurd hcon (by rw [honestTraceG_len]; decide)
        · intro c hc; simp only [List.mem_singleton] at hc; subst hc
          exact fun hcon => absurd hcon (by rw [honestTraceG_len]; decide)
    · -- LAST row: the transition gates/pins/window are vacuous; the last-row FIX bodies genuinely fire.
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
        simp only [selectorBinaryGates, List.mem_cons, List.not_mem_nil, or_false] at hc
        rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> exact True.intro
      · intro c hc; simp only [List.mem_singleton] at hc; subst hc; exact True.intro
      · intro c hc; simp only [chainingGates, List.mem_map, List.mem_range] at hc
        obtain ⟨j, _, rfl⟩ := hc
        exact fun hcon => absurd hcon (by rw [honestTraceG_len]; decide)
      · intro c hc; simp only [List.mem_singleton] at hc; subst hc
        exact fun hcon => absurd hcon (by decide)
      · -- garbledLastRowFix: on the LAST row these boundaries FIRE; bodies vanish on `hRowG` (row 1).
        simp only [garbledLastRowFix]
        refine List.forall_mem_append.mpr ⟨List.forall_mem_append.mpr ⟨?_, ?_⟩, ?_⟩
        · intro c hc; simp only [List.mem_map, List.mem_range] at hc
          obtain ⟨j, hj, rfl⟩ := hc
          exact hlast_boundary hash pub o hsh (decBody j) (decBodyG_zero pub o hsh j hj)
        · intro c hc; simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
          rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
          · exact hlast_boundary hash pub o hsh _ (binBodyG_and pub o hsh)
          · exact hlast_boundary hash pub o hsh _ (binBodyG_off pub o hsh _ (hRowG_or pub o hsh))
          · exact hlast_boundary hash pub o hsh _ (binBodyG_off pub o hsh _ (hRowG_xor pub o hsh))
          · exact hlast_boundary hash pub o hsh _ (binBodyG_off pub o hsh _ (hRowG_not pub o hsh))
          · exact hlast_boundary hash pub o hsh _ (binBodyG_off pub o hsh _ (hRowG_chain pub o hsh))
          · exact hlast_boundary hash pub o hsh _ (binBodyG_off pub o hsh _ (hRowG_padding pub o hsh))
        · intro c hc; simp only [List.mem_singleton] at hc; subst hc
          exact hlast_boundary hash pub o hsh exclusivityBody (exclBodyG_zero pub o hsh)
  · intro i _; exact True.intro
  · intro i _ r hr; exact absurd hr (by simp [garbledEvalDesc])
  · exact List.nodup_nil
  · intro op hop; rw [memLogG_nil] at hop; exact absurd hop (by simp)
  · rw [memLogG_nil]; exact True.intro
  · rw [memLogG_nil]; simp [MemoryChecking.MemCheck, MemoryChecking.initSet, MemoryChecking.finalSet]
  · rw [memLogG_nil]; rfl
  · rw [mapLogG_nil]; rfl

/-! ## §5 — construct AND prove the carriers (never assume). -/

/-- **`honestG_canon` — the range envelope, CONSTRUCTED.** The honest trace inhabits `GarbledTraceCanon`
whenever the public commitment and output labels are canonical: the selectors are the `0`/`1` AND
pattern, the label lanes are `0`/`o` (canonical by `ho`), the committed columns are `pub` (canonical by
`hpub`). No `hsh` canonicality is needed (the decryption clause is a congruence). -/
theorem honestG_canon (pub : Assignment) (o hsh : Nat → ℤ)
    (hpub : ∀ k, k < 8 → CanonCell (pub k)) (ho : ∀ j, j < 8 → CanonCell (o j)) :
    GarbledTraceCanon (honestTraceG pub o hsh) := by
  have hlen : (honestTraceG pub o hsh).rows.length = 2 := rfl
  have hrow : ∀ i, i < (honestTraceG pub o hsh).rows.length →
      (envAt (honestTraceG pub o hsh) i).loc = hRowG pub o hsh := by
    intro i hi; rw [hlen] at hi; interval_cases i <;> rfl
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i hi; rw [hrow i hi, hRowG_and]; exact ⟨by norm_num, by norm_num⟩
  · intro i hi; rw [hrow i hi, hRowG_or]; exact ⟨by norm_num, by norm_num⟩
  · intro i hi; rw [hrow i hi, hRowG_xor]; exact ⟨by norm_num, by norm_num⟩
  · intro i hi; rw [hrow i hi, hRowG_not]; exact ⟨by norm_num, by norm_num⟩
  · intro i hi; rw [hrow i hi, hRowG_chain]; exact ⟨by norm_num, by norm_num⟩
  · intro i hi; rw [hrow i hi, hRowG_padding]; exact ⟨by norm_num, by norm_num⟩
  · intro i hi j hj; rw [hrow i hi, hRowG_left pub o hsh j hj]; exact ⟨by norm_num, by norm_num⟩
  · intro i hi j hj; rw [hrow i hi, hRowG_output pub o hsh j hj]; exact ho j hj
  · intro j hj
    rw [hrow 0 (by rw [hlen]; norm_num), hRowG_commit pub o hsh j hj]
    exact hpub j (Nat.lt_of_lt_of_le hj (by norm_num))
  · intro j hj
    rw [hrow 0 (by rw [hlen]; norm_num), hRowG_ohash pub o hsh j hj]
    exact hpub (4 + j) (Nat.add_lt_add_left hj 4)
  · rw [hrow 0 (by rw [hlen]; norm_num), hRowG_gid]; exact ⟨by norm_num, by norm_num⟩
  · intro k hk; exact hpub k hk

/-- **`honestG_hashBound` — the Poseidon2 garbling-hash carrier, CONSTRUCTED (never assumed).** The
honest trace whose digest lanes are DERIVED from the real garbling hash `hsh j := gh zeroInputs j`
satisfies `GarblingHashBound gh`: on the active row the input labels are `0`, so
`GateInputs (row) = zeroInputs`, and `hash_out(j) = gh zeroInputs j = gh (GateInputs row) j`. -/
theorem honestG_hashBound (gh : List ℤ → Nat → ℤ) (pub : Assignment) (o : Nat → ℤ) :
    GarblingHashBound gh (honestTraceG pub o (fun j => gh zeroInputs j)) := by
  intro i hact _ j hj
  have hi0 : i = 0 := by
    have h2 : i + 1 < 2 := by rw [honestTraceG_len] at hact; exact hact
    omega
  subst hi0
  rw [envAtG0_loc, GateInputs_hRowG]
  exact hRowG_hash pub o (fun j => gh zeroInputs j) j hj

/-! ## §6 — the accept-set, the literal `⟺`, and the two-direction bridge. -/

/-- The honest trace whose digest lanes are the GENUINE garbling hash (so the carrier `hash` holds). -/
def honestTrace (gh : List ℤ → Nat → ℤ) (pub : Assignment) (o : Nat → ℤ) : VmTrace :=
  honestTraceG pub o (fun j => gh zeroInputs j)

/-- Reading the output lanes of `honestTrace` back (keyed to `honestTrace` for downstream `rw`). -/
theorem honestTrace_out (gh : List ℤ → Nat → ℤ) (pub : Assignment) (o : Nat → ℤ) (j : Nat) (hj : j < 8) :
    (envAt (honestTrace gh pub o) 0).loc (OUTPUT j) = o j :=
  hRowG_output pub o _ j hj

/-- **`CanonInstance pub o`** — a valid honest garbled instance: the public commitment and the output
labels are field-canonical (the range-envelope content the AIR's accept-set equals). -/
def CanonInstance (pub : Assignment) (o : Nat → ℤ) : Prop :=
  (∀ k, k < 8 → CanonCell (pub k)) ∧ (∀ j, j < 8 → CanonCell (o j))

/-- **`AirAccepts gh pub o`** — the deployed descriptor ACCEPTS the honest realization of `(pub, o)`
(the canonical trace `honestTrace gh pub o`) with BOTH carriers holding. The descriptor's
garbled-evaluation judgment on the instance. -/
def AirAccepts (gh : List ℤ → Nat → ℤ) (pub : Assignment) (o : Nat → ℤ) : Prop :=
  Satisfied2 (fun _ => 0) garbledEvalDesc (fun _ => 0) (fun _ => (0, 0)) [] (honestTrace gh pub o)
    ∧ GarbledCarriers gh (honestTrace gh pub o)

/-- **`garbled_accepts_iff` — THE LITERAL `⟺` (accept-set = spec).** The descriptor's accept-set (the
honest realizations it SATISFIES with both carriers) is EXACTLY the canonical instances:
`AirAccepts gh pub o ↔ CanonInstance pub o`. Both directions real, modulo the carriers folded into
`AirAccepts`: `→` projects the canonicality out of the range envelope (`canon`); `←` CONSTRUCTS the
satisfying trace (`honestG_satisfied2`, unconditional) and PROVES both carriers (`honestG_canon`,
`honestG_hashBound`). The security tie to the human spec is `garbled_accepts_run`. -/
theorem garbled_accepts_iff (gh : List ℤ → Nat → ℤ) (pub : Assignment) (o : Nat → ℤ) :
    AirAccepts gh pub o ↔ CanonInstance pub o := by
  constructor
  · rintro ⟨_hsat, C⟩
    refine ⟨fun k hk => C.canon.pubs k hk, fun j hj => ?_⟩
    have hc := C.canon.output 0 (by rw [show (honestTrace gh pub o).rows.length = 2 from rfl]; decide) j hj
    rw [honestTrace_out gh pub o j hj] at hc
    exact hc
  · rintro ⟨hpub, ho⟩
    exact ⟨honestG_satisfied2 (fun _ => 0) pub o _,
      ⟨honestG_canon pub o _ hpub ho, honestG_hashBound gh pub o⟩⟩

/-- **`garbled_accepts_run` — the security corollary.** The descriptor accepting the instance PROVES the
human spec: an accepted `(pub, o)` IS a genuine garbled-circuit evaluation run under the REAL garbling
hash (`GarbledEvalRunH gh (honestTrace gh pub o)`) — every active row decrypts to the honest one-time-pad
label, selects one well-formed gate, chains its wires, and binds the commitment. Composes `AirAccepts`
(both carriers) with `garbled_sound`. -/
theorem garbled_accepts_run (gh : List ℤ → Nat → ℤ) (pub : Assignment) (o : Nat → ℤ)
    (h : AirAccepts gh pub o) : GarbledEvalRunH gh (honestTrace gh pub o) :=
  garbled_sound gh (fun _ => 0) (fun _ => 0) (fun _ => (0, 0)) [] (honestTrace gh pub o) h.2 h.1

/-- **`garbled_bridge` — the two-direction bridge (∀-soundness ∧ ∃-completeness).**
  * SOUNDNESS (∀-trace): every trace carrying the named bundle and satisfying the descriptor is a
    genuine garbled-evaluation run under the real hash (`garbled_sound`) — the hostile-prover guarantee.
  * COMPLETENESS (∃-trace): ANY canonical instance `(pub, o)` yields a trace that genuinely satisfies
    the descriptor with SOUND, CONSTRUCTED range + garbling-hash carriers, reading back `pub` and `o`
    (`honestG_satisfied2`, `honestG_canon`, `honestG_hashBound`).
Together: the descriptor's accept-set (∀→) and the semantic relation (∃←) agree on the whole family. -/
theorem garbled_bridge (gh : List ℤ → Nat → ℤ) :
    (∀ (hash : List ℤ → ℤ) (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (t : VmTrace),
        GarbledCarriers gh t →
        Satisfied2 hash garbledEvalDesc minit mfin maddrs t →
        GarbledEvalRunH gh t)
    ∧
    (∀ (pub : Assignment) (o : Nat → ℤ),
        CanonInstance pub o →
        ∃ t : VmTrace,
          Satisfied2 (fun _ => 0) garbledEvalDesc (fun _ => 0) (fun _ => (0, 0)) [] t
          ∧ GarbledCarriers gh t
          ∧ (∀ k, k < 8 → t.pub k = pub k)
          ∧ (∀ j, j < 8 → (envAt t 0).loc (OUTPUT j) = o j)) :=
  ⟨fun hash minit mfin maddrs t C hsat => garbled_sound gh hash minit mfin maddrs t C hsat,
   fun pub o ⟨hpub, ho⟩ =>
     ⟨honestTrace gh pub o, honestG_satisfied2 (fun _ => 0) pub o _,
      ⟨honestG_canon pub o _ hpub ho, honestG_hashBound gh pub o⟩,
      fun _ _ => rfl, fun j hj => honestTrace_out gh pub o j hj⟩⟩

#assert_axioms garbled_sound
#assert_axioms honestG_satisfied2
#assert_axioms honestG_canon
#assert_axioms honestG_hashBound
#assert_axioms garbled_accepts_iff
#assert_axioms garbled_accepts_run
#assert_axioms garbled_bridge

/-! ## §7 — the mutation canary (load-bearing witnesses, both directions) + the demo. -/

/-- **CANARY — the garbling-hash carrier is a REAL filter (the `hash` leg of the bundle is
load-bearing).** RUNG 2's `t₀` is provably `Satisfied2` yet VIOLATES `GarblingHashBound (fun _ _ => 1)`
(its `hash_out = 0 ≠ 1`): so `Satisfied2` does NOT entail the carrier; deleting `hash` from the bundle
would let a trace whose digest columns are NOT the genuine garbling hash through, and the `decryptsHonest`
leg of `GarbledEvalRunH` would fail on it (`garbled_satisfied2_alone_insufficient`). -/
theorem carrier_hash_load_bearing : ¬ GarblingHashBound (fun _ _ => (1 : ℤ)) t₀ :=
  garbled_cheat_not_hashBound

/-- **CANARY — the decryption GATE is load-bearing (soundness direction).** A forged-output trace
`Satisfied2`s the fix-less core descriptor yet is REJECTED by the real `garbledEvalDesc`, and its output
is NOT the honest one-time-pad decryption. Breaking the last-row decryption boundary reds this
rejection — the gate is essential to `garbled_sound`. Delegates to RUNG 2's `garbled_lastRowFix_load_bearing`. -/
theorem soundness_gate_load_bearing :
    ∃ t : VmTrace, ∀ (hash : List ℤ → ℤ) (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ),
      ¬ Satisfied2 hash garbledEvalDesc minit mfin maddrs t :=
  ⟨_, fun hash minit mfin maddrs => garbled_lastRowFix_load_bearing.2.1 hash minit mfin maddrs⟩

/-- **THE BRIDGE RUN END-TO-END on an inhabited instance.** For a concrete canonical instance
(`pub k = k + 100`, `o j = j + 1`), the `←` completeness leg of `garbled_accepts_iff` builds the
accepting trace, and `garbled_accepts_run` turns the descriptor's acceptance into a genuine
`GarbledEvalRunH` under the real (all-zero) garbling hash. Not a hollow green. -/
theorem garbled_bridge_demo :
    GarbledEvalRunH (fun _ _ => (0 : ℤ))
      (honestTrace (fun _ _ => 0) (fun k => (k : ℤ) + 100) (fun j => (j : ℤ) + 1)) := by
  have hci : CanonInstance (fun k => (k : ℤ) + 100) (fun j => (j : ℤ) + 1) := by
    constructor
    · intro k hk
      change CanonCell ((k : ℤ) + 100)
      have : (k : ℤ) < 8 := by exact_mod_cast hk
      exact ⟨by omega, by omega⟩
    · intro j hj
      change CanonCell ((j : ℤ) + 1)
      have : (j : ℤ) < 8 := by exact_mod_cast hj
      exact ⟨by omega, by omega⟩
  exact garbled_accepts_run _ _ _ ((garbled_accepts_iff _ _ _).mpr hci)

#assert_axioms carrier_hash_load_bearing
#assert_axioms soundness_gate_load_bearing
#assert_axioms garbled_bridge_demo

end Dregg2.Circuit.Emit.GarbledEvalRefineBridge
