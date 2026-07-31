/-
# `EffectVmEffectsHashPin` — the in-AIR `effects_hash` fold, and its four PI pins

**SUBSTRATE, SAID OUT LOUD: this is Lean-authored AIR** (house law #1). Every column index,
every gate, every chip lookup and every PI pin below is emitted from this file through
`emitVmJson2` (`Dregg2.Circuit.DescriptorIR2`) and the `scripts/emit_descriptors.py` pipeline.
Nothing here is to be re-typed as a hand-written Rust constraint in `circuit/src/descriptor_ir2.rs`
or anywhere else; Rust only *decodes* what this emits.

## The hole this closes (MEASURED at HEAD, 2026-07-30)

`PI[16..20)` — the four-felt `effects_hash` (`circuit/src/effect_vm/pi.rs::EFFECTS_HASH_BASE = 16`,
`EFFECTS_HASH_LEN = 4`) — carries **ZERO** `piBinding` in any deployed member, and no trace column
feeds it:

* `compute_effects_hash_4` has exactly **one** non-test caller — `circuit/src/effect_vm/trace.rs:1289`,
  the **prover's** trace generator, writing `public_inputs[16..20]`. No verifier calls it on the
  deployed path.
* Its two witness felts sat at `AUX_BASE + 4/5` = abs. cols **94/95** (`trace.rs:1118-1119`).
  `circuit/src/effect_vm/e1_compact_generated.rs` deletes `[90, 98)` in **all 57** wide members,
  under a kill-set defined as *"every column at index ≥ 90 referenced by NO surviving constraint /
  hash site / range"*. The deletion **is** the machine-derived proof that nothing read them.
* `circuit/tests/vk_epoch_misc_light_client_binding.rs:196-210` asserts the absence as a
  precondition: `(16..20).all(|p| !bound_pis.contains(&p))`.
* `pi.rs:862-867` (`AUDIT[stage1-pi-only-bound]`) says the range is *"bound only by the executor's
  PI matching loop … not by per-row AIR constraints"*.

On the **full node** the value is effectively checked, but only because
`verify_and_commit_proof_rotated` (`turn/src/executor/proof_verify.rs:711`) regenerates the trace
and the entire PI vector from the ledger and substitutes **its own** vector into `verify_batch`
(`:1745`) — so the proof adds nothing the host did not already compute. On the **ledgerless** path
(`sdk/src/full_turn_proof.rs:4460`) the PI vector comes off the wire and is **free**.

The false comment that excused this for `emitEvent`/`pipelinedSend`/`exercise` has been corrected in
place: `EffectVmEmitRotationV3.lean` §5.PC.EH.

## Why a `piBinding` alone would be theatre

This tree already carries **173 PI slots pinned to columns no other constraint mentions** — a pin
the prover satisfies on *both* sides by choosing the column and the PI together. So both halves are
stated here: **which column each PI slot names, and what forces that column's value.**

| PI slot | column | what forces it |
|---|---|---|
| `16 + j`, `j < 4` | `ehAccOutCol w j` | lookup step 2 into the wide Poseidon2 chip bus |
| — | `ehAccOutCol w j`, `j < 8` | `chip_lookup_sound_N`: the 8 output columns of a chip row |
| — | `ehAccInCol w j` (row 0) | `boundary .first` against the fixed IV |
| — | `ehAccInCol w j` (row i+1) | `windowGate onTransition`: `= ehAccOutCol w j` of row i |
| — | `ehTagCol w` | `ehTagGate`: the one-hot selector row's index |
| — | `prmCol 0..7` | the existing per-effect welds (setPerms/setVK/refusal/…) |
| — | `ehExtCol w 0..7` | **NOTHING — and that is correct.** See §Declaration below. |

## §Declaration — what an AIR owes a declared value

`ehExtCol` carries the HIGH limbs of a declared 32-byte hash (topic[4..8], payload[4..8], … ) that
the row's eight `prmCol`s physically cannot hold: `NUM_PARAMS = 8` (`columns.rs:233`) while
`trace.rs:754-766` parks only the **low 4** felts of `topic_hash` and the **low 4** of
`payload_hash`, against an `effects_hash_inputs` preimage of tag + 16 = **17** felts. Nine of
emitEvent's seventeen preimage felts are not columns at all today.

Those extension columns are **prover-chosen and unconstrained by any gate**, and this is not a
weakness being laundered: the AIR's job for a *declaration* is to **publish** it, not to decide it.
A cell owner declaring `emitEvent(topic, payload)` is stating a fact about the outside world; no
row-local algebra can adjudicate it. What was missing — and what this closes — is that the
declaration was not published *at all*: a light client learned nothing about it, and a forged one
verified. After the pin, whatever the prover declares is welded into `PI[16..20)`, so a client that
holds the intended `(topic, payload)` can compare, and a prover who swaps them produces a different
PI vector.

**Not closed by this file, and not to be read as closed:** authorization is still entirely off-AIR
(the deployed registry has no curve table and no signature table); the last-row anchor is separately
forgeable and a sibling lane is repairing it; the other 173 free-column PI pins are untouched.

## §Encoding — this REPLACES `effects_hash_inputs`, and says so

`hash_many_8` (`circuit/src/poseidon2.rs:410`) is a rate-4 sponge over a **variable-length**
flattened preimage whose per-effect contribution ranges from 1 felt (`NoOp`, `IncrementNonce`) to 17
(`EmitEvent`, `RefreshDelegation`). Chunk boundaries therefore do not align with Effect-VM rows, and
an in-circuit replay would need a per-row absorb count the prover picks.

So the encoding becomes **fixed-width per row**: every row contributes exactly
`[selector_index] ++ params[0..8] ++ ext[0..8]` = 17 felts, folded through an 8-felt carrier by
`single_perm_compress` (`poseidon2.rs:438` — the same primitive the faithful state commitment
chains on; there is no 31-bit intermediate). The domain tag is free: `effects_hash_inputs`'s tag for
every effect **already equals** its `columns::sel` index (NoOp 0, Transfer 1, SetField 2, GrantCap 3,
Mint 14, RevokeCap 24, EmitEvent 25, SetPermissions 26, Exercise 34, PipelinedSend 36, …), so the
tag is a linear function of the one-hot selector row and needs one gate, not a lookup table.

The trace height (hence the number of folded rows) is committed by the proof's `degree_bits`, so a
prover cannot silently drop or append effect rows.

⚑ **This changes the value of every published `effects_hash`.** `compute_effects_hash_4` /
`effects_hash_inputs` must be rewritten to this fold and become the *twin* of what this file emits,
not an independent implementation. Flag day: see §Cost.

## §Cost — a rebuild, priced, not deferred

* **Columns:** `EH_SPAN = 41` appended past each member's existing `traceWidth` (tag 1, ext 8,
  accIn 8, two carriers 16, accOut 8). Nothing existing moves — the append idiom of
  `withRecordPin8Headroom2` / `rotateV3`'s appendix, so every existing column index, `#guard`, and
  per-effect forcing keystone survives verbatim.
* **Constraints:** 24 per member — 3 chip lookups, 1 tag gate, 8 `windowGate` continuity, 8
  `boundary .first` IV pins, 4 `piBinding .last`.
* **PI count: UNCHANGED.** `PI[16..20)` is already inside the rotated window (`V1_PI_COUNT = 42`),
  already carried into the rotated `dpis`, and already produced by the trace generator. This pin
  spends **zero** new PI slots. (`EFFECTS_HASH_LEN = 4` publishes lanes 0..3 of an 8-felt carrier;
  pinning lanes 4..7 is the `withRecordPin8Headroom2`-shaped follow-on, and it *would* cost 4 PIs.)
* **Rows:** unchanged in the main trace. The chip table grows by ≤ 3 rows per Effect-VM row, after
  the multiset dedup `descriptor_ir2` already performs.
* **What re-emits / rotates:** every descriptor JSON under `circuit/descriptors/`, every paired
  `*_FP` sha256 in `circuit/src/effect_vm_descriptors.rs`, `rotation-v3-staged-registry.tsv`,
  `e1_compact_generated.rs` (the new columns are constrained, so they must NOT enter the kill-set;
  cols 94/95 stay dead and stay killed), `WIDE_MEMBER_GEOMETRY` (57 entries), the layout manifest,
  and **every VK** — all 57 wide members and the 60 narrow staged members.
* **What must refuse to load:** any proof or descriptor at the old fingerprints, and any persisted
  `effects_hash`. Re-genesis the devnet; do not migrate.

## §Acceptance — named before it is built

* `circuit/tests/effects_hash_pi_pin_inverts.rs`
  * `forged_declared_effects_is_refused` — mint an honest rotated emitEvent proof, mutate the
    declared `ehExt`/`prmCol` columns, keep the honest PI vector; `verify_vm_descriptor2` must
    **REFUSE**.
  * `forged_effects_hash_pi_is_refused` — keep the honest trace, mutate `PI[16..20)` off the wire
    (the ledgerless shape); must **REFUSE**.
  * `honest_effects_hash_pi_is_accepted` — the control. Without it the two refusals are
    indistinguishable from a verifier that refuses everything.
* **The inversion.** `circuit/tests/vk_epoch_misc_light_client_binding.rs` is green *because* the
  forgery is accepted — three tests assert `hash_accepted`, and its helper prints *"the produced
  (topic,payload) is a RESIDUAL (forged-hash ACCEPTED — effects_hash off the rotated wire)"*. Those
  three assertions must **flip** to refusal, and its structural precondition
  `(16..20).all(|p| !bound_pis.contains(&p))` must invert to `all(contains)`. Until they flip, this
  file has changed nothing observable.
-/
import Dregg2.Circuit.DescriptorIR2
import Dregg2.Circuit.Emit.EffectVmEmit
import Dregg2.Circuit.Emit.EffectVmEmitRotationR

namespace Dregg2.Circuit.Emit.EffectVmEffectsHashPin

open Dregg2.Circuit.DescriptorIR2
open Dregg2.Circuit.Emit.EffectVmEmit (VmConstraint VmRow VmRowEnv NUM_EFFECTS NUM_PARAMS prmCol)
open Dregg2.Circuit.Emit.EffectVmEmitRotationR (IsCollW)
open Dregg2.Exec.CircuitEmit (EmittedExpr)

/-! ## §1 — Expression helpers (the local idiom of every emitter in this directory). -/

def ev (c : Nat) : EmittedExpr := .var c
def ek (x : ℤ) : EmittedExpr := .const x
def eadd (a b : EmittedExpr) : EmittedExpr := .add a b
def emul (a b : EmittedExpr) : EmittedExpr := .mul a b
def esub (a b : EmittedExpr) : EmittedExpr := eadd a (emul (ek (-1)) b)
def esum : List EmittedExpr → EmittedExpr := List.foldl eadd (ek 0)

/-! ## §2 — The appended block, at the DEPLOYED absorb geometry.

⚑ The step arity is **11**, not 16. `circuit/src/poseidon2.rs:456` states the contract —
*"`inputs.len()` MUST be ≤ 11 (the chip's `CHIP_RATE`); the chain's three site arities are 4 …, 11
(a carrier ‖ 3 limbs), and 9 …"* — and `single_perm_compress` writes `st[i] = x` into a `WIDTH = 16`
state, so an arity-17 absorb indexes out of bounds. (`descriptor_ir2::CHIP_RATE = 16` is the chip
BUS width, a different number; the deployed Rust chip additionally pins `in7..in10 == 0` for every
arity ≠ 11, which is why `wireCommitR8` zero-pads its final chunk to 11 rather than emitting arity
9.) So one row's 17 declared felts ride **six** `carrier(8) ‖ 3 fresh` steps — the identical shape as
the deployed faithful 8-felt state commitment (`poseidon2.rs::wire_commit_8`, Lean twin
`EffectVmEmitRotationR.wireCommitR8` over `chainFrom8`). No new primitive enters. -/

/-- Carrier width: the 8-felt fold accumulator. -/
def EH_CARRIER : Nat := 8
/-- Declared-extension lanes: the HIGH limbs of a 32-byte declared hash the eight `prmCol`s cannot
hold (`NUM_PARAMS = 8`, preimage = tag + 16). -/
def EH_EXT_LANES : Nat := 8
/-- Fresh felts absorbed per step (`carrier ‖ 3` = arity 11, the deployed group shape). -/
def EH_FRESH_PER_STEP : Nat := 3
/-- Steps per row: `⌈17 / 3⌉`. -/
def EH_STEPS : Nat := 6

/-- The domain tag column: the row's effect selector index, forced by `ehTagGate`. -/
def ehTagCol (w : Nat) : Nat := w
/-- Declared-extension column `i` (prover-chosen; PUBLISHED, not adjudicated — see §Declaration). -/
def ehExtCol (w i : Nat) : Nat := w + 1 + i
/-- Fold accumulator entering the row (row 0: the IV; row i+1: row i's `ehAccOutCol`). -/
def ehAccInCol (w j : Nat) : Nat := w + 1 + EH_EXT_LANES + j
/-- Output carrier of absorb step `s`. -/
def ehCarrierCol (w s j : Nat) : Nat := w + 1 + EH_EXT_LANES + EH_CARRIER + s * EH_CARRIER + j
/-- Fold accumulator leaving the row = the last step's carrier. Lanes 0..3 are published. -/
def ehAccOutCol (w j : Nat) : Nat := ehCarrierCol w (EH_STEPS - 1) j
/-- Total appended width. -/
def EH_SPAN : Nat := 1 + EH_EXT_LANES + EH_CARRIER + EH_STEPS * EH_CARRIER

/-! ## §3 — The PI slots. Already inside the rotated window; this pin spends none. -/

/-- `circuit/src/effect_vm/pi.rs::EFFECTS_HASH_BASE`. -/
def EFFECTS_HASH_PI_BASE : Nat := 16
/-- `circuit/src/effect_vm/pi.rs::EFFECTS_HASH_LEN`. -/
def EFFECTS_HASH_PI_LEN : Nat := 4

/-! ## §4 — The fold IV. A fixed 8-felt seed under a dedicated domain constant. `hash_many_8` seeds
capacity lane 4 with the preimage length; here the row count is committed by the proof's
`degree_bits`, so the seed is a constant and the encoding is a fold, not a variable-length sponge. -/

/-- Domain separator for the effects fold. Distinct from every per-effect tag (selector indices
`< NUM_EFFECTS = 54`) and from the state-commit domains. -/
def EH_DOMAIN : ℤ := 0xEFFEC7

/-- Lane `j` of the fold IV. -/
def ehIV (j : Nat) : ℤ := if j = 0 then EH_DOMAIN else 0

/-! ## §5 — The absorb schedule, DERIVED (never hand-typed per step). -/

/-- The seventeen declared felts of a row, in absorb order: domain tag, the eight params, the eight
declared-extension lanes. This IS the new `effects_hash_inputs` per-row contribution. -/
def ehFreshCols (w : Nat) : List Nat :=
  [ehTagCol w] ++ ((List.range NUM_PARAMS).map prmCol)
    ++ ((List.range EH_EXT_LANES).map (ehExtCol w))

/-- The fresh triple absorbed at step `s` (the last step absorbs two and zero-pads). -/
def ehFreshChunk (w s : Nat) : List Nat :=
  ((ehFreshCols w).drop (EH_FRESH_PER_STEP * s)).take EH_FRESH_PER_STEP

/-- The carrier read INTO step `s`: the accumulator-in at step 0, else step `s-1`'s carrier. -/
def ehCarrierIn (w s : Nat) : List Nat :=
  if s = 0 then (List.range EH_CARRIER).map (ehAccInCol w)
  else (List.range EH_CARRIER).map (ehCarrierCol w (s - 1))

/-- Step `s`'s absorbed inputs: `carrier(8) ‖ fresh(≤3)` — arity 11 (10 on the last step). -/
def ehStepInputs (w s : Nat) : List EmittedExpr :=
  ((ehCarrierIn w s) ++ (ehFreshChunk w s)).map ev

/-- Step `s`'s forced output block. -/
def ehStepOut (w s : Nat) : List Nat := (List.range EH_CARRIER).map (ehCarrierCol w s)

/-- One wide chip lookup. `chipLookupTupleN` renders `(arity, inputs padded to CHIP_RATE, W digest
columns)`; against a `ChipTableSoundN` table, `chip_lookup_sound_N` forces **every** one of the `W`
digest columns to the genuine permutation output — not merely its head. This is the half a bare
`piBinding` does not have. -/
def ehLookup (ins : List EmittedExpr) (outCols : List Nat) : VmConstraint2 :=
  .lookup { table := .poseidon2, tuple := chipLookupTupleN ins outCols }

/-- The six absorbs of one row's 17-felt contribution. -/
def ehAbsorbs (w : Nat) : List VmConstraint2 :=
  (List.range EH_STEPS).map (fun s => ehLookup (ehStepInputs w s) (ehStepOut w s))

/-- **The tag gate.** `ehTagCol = Σ_{e < NUM_EFFECTS} e · sel_e`. The selector columns are `0..53`
(`STATE_BEFORE_BASE = NUM_EFFECTS`), already booleanity- and one-hot-constrained by the host
descriptor, so on any accepted row this is exactly the fired selector's index — which is exactly the
domain tag `effects_hash_inputs` pushes for that effect. One linear gate, no lookup table. -/
def ehTagGate (w : Nat) : VmConstraint2 :=
  .base (.gate (esub (ev (ehTagCol w))
    (esum ((List.range NUM_EFFECTS).map (fun (e : Nat) => emul (ek (Int.ofNat e)) (ev e))))))

/-- **Continuity.** `next[ehAccIn j] = local[ehAccOut j]`, on the transition domain — the fold is a
single chain across the whole trace, so no row can restart it. -/
def ehContinuity (w : Nat) : List VmConstraint2 :=
  (List.range EH_CARRIER).map (fun j =>
    .windowGate { body := .add (.nxt (ehAccInCol w j))
                    (.mul (.const (-1)) (.loc (ehAccOutCol w j)))
                , onTransition := true })

/-- **The seed.** Row 0's accumulator is the fixed IV, so the chain has one origin. -/
def ehSeed (w : Nat) : List VmConstraint2 :=
  (List.range EH_CARRIER).map (fun j =>
    .base (.boundary .first (esub (ev (ehAccInCol w j)) (ek (ehIV j)))))

/-- **The publication.** The last row's accumulator lanes 0..3 ARE `PI[16..20)`. This is the pin the
audit found missing; it is meaningful only because `ehAbsorbs`/`ehContinuity`/`ehSeed` constrain the
column it names. -/
def ehPublish (w : Nat) : List VmConstraint2 :=
  (List.range EFFECTS_HASH_PI_LEN).map (fun j =>
    .base (.piBinding .last (ehAccOutCol w j) (EFFECTS_HASH_PI_BASE + j)))

/-! ## §6 — The post-graduation combinator.

Shaped exactly like `EffectVmEmitRotationV3.withRecordPin8Headroom2`: applied to an ALREADY
graduated `EffectVmDescriptor2`, appending columns past the existing width and constraints past the
existing list. Every existing column, site, range, PI index and per-effect forcing keystone is
untouched, so the cohort's theorems compose verbatim. -/

/-- **`withEffectsHashPin`** — append the fold block and weld `PI[16..20)` to its last-row output.
`piCount` is UNCHANGED: the four slots already exist and are already carried. -/
def withEffectsHashPin (g : EffectVmDescriptor2) : EffectVmDescriptor2 :=
  { g with
    traceWidth  := g.traceWidth + EH_SPAN
    constraints := g.constraints
      ++ [ehTagGate g.traceWidth]
      ++ ehAbsorbs g.traceWidth
      ++ ehContinuity g.traceWidth
      ++ ehSeed g.traceWidth
      ++ ehPublish g.traceWidth }

/-! ## §6½ — THE SOUNDNESS LADDER.

**Floor-free, and NOT `∃`-shaped.** ⚑ `EffectVmEmitRotationR.lean:255-265` records the trap this
ladder had to avoid: at deployed parameters `∃ xs ys, xs ≠ ys ∧ permW xs = permW ys` is
**unconditionally TRUE by pigeonhole** (`VacuitySweepTeeth.widePerm_not_injective_babyBear`), so a
theorem hypothesised on its negation is VACUOUS and `#assert_axioms` is blind to it — *"the proofs
were clean; the HYPOTHESIS was the flaw."* An earlier draft of this file made exactly that mistake.

So every rung below is stated with `IsCollW permOut (x, y)` — a predicate about the **two specific
lists the two traces actually absorbed**, decidable, and false for almost every pair. A forge does
not contradict a floor; it HANDS BACK the colliding pair. The rungs are total: no hypothesis about
the hash appears anywhere. -/

/-- The specific pair of absorbed input lists two traces present at step `s`. -/
def ehStepPair (w s : Nat) (a b : Assignment) : List ℤ × List ℤ :=
  ((ehStepInputs w s).map (·.eval a), (ehStepInputs w s).map (·.eval b))

/-- Every step fits the chip bus. -/
theorem ehStepInputs_len_le (w s : Nat) : (ehStepInputs w s).length ≤ CHIP_RATE := by
  have hc : (ehCarrierIn w s).length = EH_CARRIER := by
    unfold ehCarrierIn; split <;> simp
  have hf : (ehFreshChunk w s).length ≤ EH_FRESH_PER_STEP := by
    unfold ehFreshChunk; exact List.length_take_le _ _
  simp only [ehStepInputs, List.length_map, List.length_append, hc]
  simp only [EH_CARRIER, EH_FRESH_PER_STEP, CHIP_RATE] at *
  omega

/-- **RUNG 1 — one absorb hop, floor-free and pair-specific.** Two rows whose chip lookups force the
same output block either absorbed the SAME inputs, or the two lists they absorbed ARE a genuine
collision of the deployed permutation. Total: no hash hypothesis. -/
theorem ehHop {permOut : List ℤ → List ℤ} {tbl : Table}
    (hSound : ChipTableSoundN permOut tbl) (a b : Assignment) (w s : Nat)
    (hA : (chipLookupTupleN (ehStepInputs w s) (ehStepOut w s)).map (·.eval a) ∈ tbl)
    (hB : (chipLookupTupleN (ehStepInputs w s) (ehStepOut w s)).map (·.eval b) ∈ tbl)
    (hout : (ehStepOut w s).map a = (ehStepOut w s).map b) :
    (ehStepInputs w s).map (·.eval a) = (ehStepInputs w s).map (·.eval b)
      ∨ IsCollW permOut (ehStepPair w s a b) := by
  by_cases h : (ehStepInputs w s).map (·.eval a) = (ehStepInputs w s).map (·.eval b)
  · exact Or.inl h
  · refine Or.inr ⟨h, ?_⟩
    simp only [ehStepPair]
    rw [← chip_lookup_sound_N permOut tbl hSound a (ehStepInputs w s) (ehStepOut w s)
          (ehStepInputs_len_le w s) hA,
        ← chip_lookup_sound_N permOut tbl hSound b (ehStepInputs w s) (ehStepOut w s)
          (ehStepInputs_len_le w s) hB]
    exact hout

/-- The carrier read into step `s+1` IS step `s`'s output block. -/
theorem ehCarrierIn_succ (w s : Nat) : ehCarrierIn w (s + 1) = ehStepOut w s := by
  simp [ehCarrierIn, ehStepOut]

/-- Equal absorbed inputs at a step give equal carriers entering it. -/
theorem ehCarrier_of_inputs {w s : Nat} {a b : Assignment}
    (h : (ehStepInputs w s).map (·.eval a) = (ehStepInputs w s).map (·.eval b)) :
    (ehCarrierIn w s).map a = (ehCarrierIn w s).map b := by
  have hc : (ehCarrierIn w s).length = EH_CARRIER := by
    unfold ehCarrierIn; split <;> simp
  have := congrArg (List.take EH_CARRIER) h
  simpa [ehStepInputs, List.map_append, List.map_map, Function.comp_def, ev, EmittedExpr.eval,
    List.take_append_of_le_length, hc] using this
/-- **RUNG 2 — THE ROW KEYSTONE.** Walking the chain backwards from step `s`: either **every** step
up to `s` absorbed the same 11 felts in both traces — hence the same domain tag, the same eight
params and the same eight extension lanes — or one specific step's two absorbed lists ARE a genuine
collision of the deployed permutation.

⚑ This is precisely the half a bare `piBinding` does not have. The tree carries 173 PI slots pinned
to columns nothing else mentions; for those this theorem is UNPROVABLE — there is no lookup to hop
through, and the prover picks both sides. Here every column named by `PI[16..20)` is the output
block of a chip row, and the chain reaches back through all six absorbs to the declaration. -/
theorem ehChain_back {permOut : List ℤ → List ℤ} {tbl : Table}
    (hSound : ChipTableSoundN permOut tbl) (a b : Assignment) (w : Nat)
    (hA : ∀ s, (chipLookupTupleN (ehStepInputs w s) (ehStepOut w s)).map (·.eval a) ∈ tbl)
    (hB : ∀ s, (chipLookupTupleN (ehStepInputs w s) (ehStepOut w s)).map (·.eval b) ∈ tbl) :
    ∀ s, (ehStepOut w s).map a = (ehStepOut w s).map b →
      (∀ k ≤ s, (ehStepInputs w k).map (·.eval a) = (ehStepInputs w k).map (·.eval b))
      ∨ (∃ k ≤ s, IsCollW permOut (ehStepPair w k a b)) := by
  intro s
  induction s with
  | zero =>
    intro hout
    rcases ehHop hSound a b w 0 (hA 0) (hB 0) hout with h | h
    · exact Or.inl (fun k hk => by simpa [Nat.le_zero.mp hk] using h)
    · exact Or.inr ⟨0, le_rfl, h⟩
  | succ n ih =>
    intro hout
    rcases ehHop hSound a b w (n + 1) (hA (n + 1)) (hB (n + 1)) hout with h | h
    · have hprev : (ehStepOut w n).map a = (ehStepOut w n).map b := by
        have := ehCarrier_of_inputs h
        rwa [ehCarrierIn_succ] at this
      rcases ih hprev with hall | hcoll
      · refine Or.inl (fun k hk => ?_)
        rcases Nat.lt_or_ge k (n + 1) with hlt | hge
        · exact hall k (Nat.lt_succ_iff.mp hlt)
        · have : k = n + 1 := le_antisymm hk hge
          simpa [this] using h
      · obtain ⟨k, hk, hc⟩ := hcoll
        exact Or.inr ⟨k, Nat.le_succ_of_le hk, hc⟩
    · exact Or.inr ⟨n + 1, le_rfl, h⟩

/-- **RUNG 3 — the chain step.** Row `i+1`'s fold-in accumulator IS row `i`'s fold-out accumulator:
the continuity family's body vanishes on every transition row. So `ehChain_back` propagates
backwards from the published last row through every row of the trace — no row can restart the chain,
and no row's declaration escapes the published digest. -/
theorem ehContinuity_step (w : Nat) (env : VmRowEnv) (isFirst : Bool)
    (hash : List ℤ → ℤ) (tf : TraceFamily)
    (hcon : ∀ c ∈ ehContinuity w, VmConstraint2.holdsAt hash tf env isFirst false c)
    (j : Nat) (hj : j < EH_CARRIER) :
    env.nxt (ehAccInCol w j) + (-1) * env.loc (ehAccOutCol w j) ≡ 0 [ZMOD 2013265921] := by
  have hmem : (VmConstraint2.windowGate
      { body := .add (.nxt (ehAccInCol w j)) (.mul (.const (-1)) (.loc (ehAccOutCol w j)))
      , onTransition := true }) ∈ ehContinuity w := by
    simp only [ehContinuity, List.mem_map]
    exact ⟨j, List.mem_range.mpr hj, rfl⟩
  have hres := hcon _ hmem
  simpa [VmConstraint2.holdsAt, WindowConstraint.holdsAt, WindowExpr.eval] using hres

/-- **RUNG 4 — THE PUBLICATION.** On the last row, the four published PI slots ARE the first four
accumulator-out columns. Cheap — and it is the clause the audit found missing entirely. -/
theorem ehPublish_binds (w : Nat) (env : VmRowEnv) (isFirst : Bool)
    (hash : List ℤ → ℤ) (tf : TraceFamily)
    (hpub : ∀ c ∈ ehPublish w, VmConstraint2.holdsAt hash tf env isFirst true c)
    (j : Nat) (hj : j < EFFECTS_HASH_PI_LEN) :
    env.loc (ehAccOutCol w j) ≡ env.pub (EFFECTS_HASH_PI_BASE + j) [ZMOD 2013265921] := by
  have hmem : (VmConstraint2.base
      (.piBinding .last (ehAccOutCol w j) (EFFECTS_HASH_PI_BASE + j))) ∈ ehPublish w := by
    simp only [ehPublish, List.mem_map]
    exact ⟨j, List.mem_range.mpr hj, rfl⟩
  have hres := hpub _ hmem
  simpa [VmConstraint2.holdsAt, VmConstraint.holdsVm] using hres

/-! ## §6¾ — THE NON-VACUITY CONTROLS.

⚑ A refusal theorem that also refuses the honest witness proves nothing. Two lanes tonight shipped
guards that passed BECAUSE their circuit was unsatisfiable. So the appended families are exhibited
as SATISFIED on a concrete honest row, with no hypotheses — and the tag gate is separately shown
NOT to accept everything. If a later edit makes the block unsatisfiable, these go red before the
refusal rungs go quietly vacuous. -/

/-- An honest row, by plain arithmetic (no choice, no classical `dif`): selector `sel::TRANSFER = 1`
fires one-hot, the tag reads that selector index, the accumulator enters at the IV, the extension
lanes and intermediate carriers are zero, and the accumulator leaves carrying `accOut`. -/
def ehHonestRow (w : Nat) (accOut : Nat → ℤ) : Assignment := fun c =>
  if c = 1 then 1
  else if c = w then 1
  else if c < w + 9 then 0
  else if c < w + 17 then ehIV (c - (w + 9))
  else if c < w + 57 then 0
  else accOut (c - (w + 57))

/-- Column-index normal forms, so the honest-row arithmetic is plain `omega` territory. -/
theorem ehAccInCol_eq (w j : Nat) : ehAccInCol w j = w + 9 + j := by
  unfold ehAccInCol EH_EXT_LANES; omega

theorem ehAccOutCol_eq (w j : Nat) : ehAccOutCol w j = w + 57 + j := by
  unfold ehAccOutCol ehCarrierCol EH_EXT_LANES EH_CARRIER EH_STEPS; omega

/-- The honest row reads the IV on the accumulator-in block. -/
theorem ehHonestRow_accIn (w : Nat) (hw : 54 ≤ w) (accOut : Nat → ℤ) (j : Nat) (hj : j < 8) :
    ehHonestRow w accOut (w + 9 + j) = ehIV j := by
  have h1 : ¬ (w + 9 + j = 1) := by omega
  have h2 : ¬ (w + 9 + j = w) := by omega
  have h3 : ¬ (w + 9 + j < w + 9) := by omega
  have h4 : w + 9 + j < w + 17 := by omega
  simp only [ehHonestRow, if_neg h1, if_neg h2, if_neg h3, if_pos h4]
  congr 1
  omega

/-- The honest row carries the published digest on the accumulator-out block. -/
theorem ehHonestRow_accOut (w : Nat) (hw : 54 ≤ w) (accOut : Nat → ℤ) (j : Nat) (hj : j < 8) :
    ehHonestRow w accOut (w + 57 + j) = accOut j := by
  have h1 : ¬ (w + 57 + j = 1) := by omega
  have h2 : ¬ (w + 57 + j = w) := by omega
  have h3 : ¬ (w + 57 + j < w + 9) := by omega
  have h4 : ¬ (w + 57 + j < w + 17) := by omega
  have h5 : ¬ (w + 57 + j < w + 57) := by omega
  simp only [ehHonestRow, if_neg h1, if_neg h2, if_neg h3, if_neg h4, if_neg h5]
  congr 1
  omega

/-- **CONTROL A — the tag gate ACCEPTS an honest one-hot row.** At the shape-guard width `w = 1000`
the selector row is one-hot at `sel::TRANSFER = 1`, so `Σ e·sel_e = 1`, which is exactly the tag the
row carries: the gate body vanishes. Evaluated, not asserted. If this goes red the tag gate is
refusing honest traces and every refusal rung above is vacuous. -/
theorem ehTagGate_accepts_honest :
    EmittedExpr.eval
      (esub (ev (ehTagCol 1000))
        (esum ((List.range NUM_EFFECTS).map (fun (e : Nat) => emul (ek (Int.ofNat e)) (ev e)))))
      (ehHonestRow 1000 (fun _ => 0)) = 0 := by
  decide

/-- ⚑ **CONTROL A′ — the tag gate is NOT the zero polynomial.** A row that fires `sel::TRANSFER` but
declares tag `7` is REFUSED. Without this, CONTROL A would also be satisfied by a gate that accepts
everything — the exact shape of the vacuous guards two sibling lanes shipped tonight. -/
theorem ehTagGate_rejects_wrong_tag :
    EmittedExpr.eval
      (esub (ev (ehTagCol 1000))
        (esum ((List.range NUM_EFFECTS).map (fun (e : Nat) => emul (ek (Int.ofNat e)) (ev e)))))
      (fun (c : Nat) => if c = 1 then (1 : ℤ) else if c = 1000 then 7 else 0) ≠ 0 := by
  decide

/-- **CONTROL B — the seed family ACCEPTS the honest row.** Row 0's accumulator carries the IV, so
every `boundary .first` body vanishes. A seed family that refused the IV would make the whole chain
unsatisfiable and every rung above vacuously true. -/
theorem ehSeed_accepts_honest (w : Nat) (hw : 54 ≤ w) (accOut : Nat → ℤ) (j : Nat)
    (hj : j < EH_CARRIER) :
    EmittedExpr.eval (esub (ev (ehAccInCol w j)) (ek (ehIV j))) (ehHonestRow w accOut) = 0 := by
  have hj8 : j < 8 := by simpa [EH_CARRIER] using hj
  simp only [esub, eadd, emul, ek, ev, EmittedExpr.eval, ehAccInCol_eq,
    ehHonestRow_accIn w hw accOut j hj8]
  ring

/-- **CONTROL C — the publication family is SATISFIABLE.** For any four-felt digest there is a row
carrying it on the accumulator-out columns, so `ehPublish` is not a family that can only be met by
refusing. -/
theorem ehPublish_satisfiable (w : Nat) (hw : 54 ≤ w) (pub : Assignment) (j : Nat)
    (hj : j < EFFECTS_HASH_PI_LEN) :
    (ehHonestRow w (fun k => pub (EFFECTS_HASH_PI_BASE + k))) (ehAccOutCol w j)
      = pub (EFFECTS_HASH_PI_BASE + j) := by
  have hj8 : j < 8 := by
    have : j < 4 := by simpa [EFFECTS_HASH_PI_LEN] using hj
    omega
  rw [ehAccOutCol_eq, ehHonestRow_accOut w hw _ j hj8]

#assert_axioms ehHop
#assert_axioms ehChain_back
#assert_axioms ehContinuity_step
#assert_axioms ehPublish_binds
#assert_axioms ehTagGate_accepts_honest
#assert_axioms ehTagGate_rejects_wrong_tag
#assert_axioms ehSeed_accepts_honest
#assert_axioms ehPublish_satisfiable

/-! ## §7 — Shape tripwires.

`#guard`s, not theorems: they pin the layout arithmetic and the constraint budget so a later edit
that silently drops a family goes red here. -/

#guard EH_CARRIER == 8
#guard EH_STEPS == 6
#guard EH_SPAN == 65
#guard EFFECTS_HASH_PI_BASE == 16
#guard EFFECTS_HASH_PI_LEN == 4

-- The block is contiguous and non-overlapping.
#guard ehTagCol 1000 == 1000
#guard ehExtCol 1000 0 == 1001
#guard ehAccInCol 1000 0 == 1009
#guard ehCarrierCol 1000 0 0 == 1017
#guard ehAccOutCol 1000 0 == 1057
-- The honest-row literals ARE the layout (the row is written with 9/17/57, not with the defs).
#guard 9 == 1 + EH_EXT_LANES
#guard 17 == 1 + EH_EXT_LANES + EH_CARRIER
#guard 57 == 1 + EH_EXT_LANES + EH_CARRIER + (EH_STEPS - 1) * EH_CARRIER
#guard ehAccOutCol 1000 (EH_CARRIER - 1) == 1000 + EH_SPAN - 1

-- ⚑ EVERY step is arity ≤ 11 — the `single_perm_compress` / deployed-chip contract.
-- Five arity-11 groups (carrier ‖ 3) and a final arity-10 (carrier ‖ 2).
#guard ((List.range EH_STEPS).map (fun s => (ehStepInputs 1000 s).length)) == [11, 11, 11, 11, 11, 10]
#guard ((List.range EH_STEPS).map (fun s => (ehStepInputs 1000 s).length)).all (· <= 11)

-- The seventeen declared felts are covered exactly once, in order, across the six steps.
#guard (ehFreshCols 1000).length == 1 + NUM_PARAMS + EH_EXT_LANES
#guard ((List.range EH_STEPS).flatMap (ehFreshChunk 1000)) == ehFreshCols 1000

-- Each absorb forces a full 8-lane carrier through the 1 + CHIP_RATE + 8 chip row.
#guard (ehAbsorbs 1000).length == EH_STEPS
#guard (chipLookupTupleN (ehStepInputs 1000 0) (ehStepOut 1000 0)).length
  == 1 + CHIP_RATE + EH_CARRIER

-- The constraint budget: 1 tag + 6 absorbs + 8 continuity + 8 seed + 4 publish = 27.
#guard (ehContinuity 1000).length == 8
#guard (ehSeed 1000).length == 8
#guard (ehPublish 1000).length == 4

-- The combinator is additive in width and constraints, and spends NO new PI slot.
example (g : EffectVmDescriptor2) : (withEffectsHashPin g).piCount = g.piCount := rfl
example (g : EffectVmDescriptor2) :
    (withEffectsHashPin g).traceWidth = g.traceWidth + EH_SPAN := rfl
example (g : EffectVmDescriptor2) : (withEffectsHashPin g).hashSites = g.hashSites := rfl
example (g : EffectVmDescriptor2) : (withEffectsHashPin g).ranges = g.ranges := rfl

end Dregg2.Circuit.Emit.EffectVmEffectsHashPin
