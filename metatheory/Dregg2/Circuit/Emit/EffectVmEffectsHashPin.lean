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

namespace Dregg2.Circuit.Emit.EffectVmEffectsHashPin

open Dregg2.Circuit.DescriptorIR2
open Dregg2.Circuit.Emit.EffectVmEmit (VmConstraint VmRow NUM_EFFECTS NUM_PARAMS prmCol)
open Dregg2.Exec.CircuitEmit (EmittedExpr)

/-! ## §1 — Expression helpers (the local idiom of every emitter in this directory). -/

def ev (c : Nat) : EmittedExpr := .var c
def ek (x : ℤ) : EmittedExpr := .const x
def eadd (a b : EmittedExpr) : EmittedExpr := .add a b
def emul (a b : EmittedExpr) : EmittedExpr := .mul a b
def esub (a b : EmittedExpr) : EmittedExpr := eadd a (emul (ek (-1)) b)
def esum : List EmittedExpr → EmittedExpr := List.foldl eadd (ek 0)

/-! ## §2 — The appended block.

Laid out past a member's existing `traceWidth` (`w`), so no existing column index moves. -/

/-- Carrier width: the 8-felt fold accumulator (`CHIP_OUT_LANES`). -/
def EH_CARRIER : Nat := CHIP_OUT_LANES

/-- Declared-extension lanes: the HIGH limbs of a 32-byte declared hash that the eight `prmCol`s
cannot hold (`NUM_PARAMS = 8`, preimage = tag + 16). -/
def EH_EXT_LANES : Nat := 8

/-- The domain tag column: the row's effect selector index, forced by `ehTagGate`. -/
def ehTagCol (w : Nat) : Nat := w
/-- Declared-extension column `i` (prover-chosen; PUBLISHED, not adjudicated — see §Declaration). -/
def ehExtCol (w i : Nat) : Nat := w + 1 + i
/-- Fold accumulator entering this row (row 0: the IV; row i+1: row i's `ehAccOutCol`). -/
def ehAccInCol (w j : Nat) : Nat := w + 1 + EH_EXT_LANES + j
/-- Intermediate carrier `s` (`s < 2`) of the three-step absorb. -/
def ehMidCol (w s j : Nat) : Nat := w + 1 + EH_EXT_LANES + EH_CARRIER + s * EH_CARRIER + j
/-- Fold accumulator leaving this row. Lanes 0..3 are the published `effects_hash`. -/
def ehAccOutCol (w j : Nat) : Nat := w + 1 + EH_EXT_LANES + 3 * EH_CARRIER + j
/-- Total appended width. -/
def EH_SPAN : Nat := 1 + EH_EXT_LANES + 4 * EH_CARRIER

/-! ## §3 — The PI slots. Already inside the rotated window; this pin spends none. -/

/-- `circuit/src/effect_vm/pi.rs::EFFECTS_HASH_BASE`. -/
def EFFECTS_HASH_PI_BASE : Nat := 16
/-- `circuit/src/effect_vm/pi.rs::EFFECTS_HASH_LEN`. -/
def EFFECTS_HASH_PI_LEN : Nat := 4

/-! ## §4 — The fold IV.

A fixed 8-felt seed under a dedicated domain constant. `hash_many_8` seeds capacity lane 4 with the
preimage length; here the row count is committed by the proof's `degree_bits` instead, so the seed
is a constant and the encoding is a fold rather than a variable-length sponge. -/

/-- Domain separator for the effects fold. Distinct from every `effects_hash_inputs` per-effect tag
(which are selector indices `< NUM_EFFECTS = 54`) and from the state-commit domains. -/
def EH_DOMAIN : ℤ := 0xEFFEC7

/-- Lane `j` of the fold IV. -/
def ehIV (j : Nat) : ℤ := if j = 0 then EH_DOMAIN else 0

/-! ## §5 — The constraints.

Five families. Each names a column and what forces it; none is a PI pin over a free column. -/

/-- **The tag gate.** `ehTagCol = Σ_{e < NUM_EFFECTS} e · sel_e`. The selector columns are `0..53`
(`STATE_BEFORE_BASE = NUM_EFFECTS`), already booleanity- and one-hot-constrained by the host
descriptor, so on any accepted row this is exactly the fired selector's index — which is exactly the
domain tag `effects_hash_inputs` pushes for that effect. One linear gate, no lookup table. -/
def ehTagGate (w : Nat) : VmConstraint2 :=
  .base (.gate (esub (ev (ehTagCol w))
    (esum ((List.range NUM_EFFECTS).map (fun (e : Nat) => emul (ek (Int.ofNat e)) (ev e))))))

/-- Absorb step 0: `accIn(8) ‖ tag ‖ prm[0..7]` — 16 inputs, the full `CHIP_RATE`. -/
def ehAbsorb0Inputs (w : Nat) : List EmittedExpr :=
  ((List.range EH_CARRIER).map (fun j => ev (ehAccInCol w j)))
    ++ [ev (ehTagCol w)]
    ++ (List.range 7).map (fun i => ev (prmCol i))

/-- Absorb step 1: `mid0(8) ‖ prm[7] ‖ ext[0..7]` — 16 inputs. -/
def ehAbsorb1Inputs (w : Nat) : List EmittedExpr :=
  ((List.range EH_CARRIER).map (fun j => ev (ehMidCol w 0 j)))
    ++ [ev (prmCol 7)]
    ++ (List.range 7).map (fun i => ev (ehExtCol w i))

/-- Absorb step 2: `mid1(8) ‖ ext[7]` — 9 inputs, zero-padded to `CHIP_RATE` by `chipLookupTupleN`.
The arity tag in the tuple head keeps the short absorb distinguishable from a 16-lane one, which is
the padding-confusion clause of `chip_lookup_sound_N`. -/
def ehAbsorb2Inputs (w : Nat) : List EmittedExpr :=
  ((List.range EH_CARRIER).map (fun j => ev (ehMidCol w 1 j)))
    ++ [ev (ehExtCol w (EH_EXT_LANES - 1))]

/-- One wide chip lookup. `chipLookupTupleN` renders `(arity, inputs padded to CHIP_RATE, W digest
columns)`; against a `ChipTableSoundN` table, `chip_lookup_sound_N` forces **every** one of the `W`
digest columns to the genuine permutation output — not merely its head. This is the half a bare
`piBinding` does not have. -/
def ehLookup (ins : List EmittedExpr) (outCols : List Nat) : VmConstraint2 :=
  .lookup { table := .poseidon2, tuple := chipLookupTupleN ins outCols }

/-- The three absorbs of one row's 17-felt contribution. -/
def ehAbsorbs (w : Nat) : List VmConstraint2 :=
  [ ehLookup (ehAbsorb0Inputs w) ((List.range EH_CARRIER).map (ehMidCol w 0))
  , ehLookup (ehAbsorb1Inputs w) ((List.range EH_CARRIER).map (ehMidCol w 1))
  , ehLookup (ehAbsorb2Inputs w) ((List.range EH_CARRIER).map (ehAccOutCol w)) ]

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

/-! ## §7 — Shape tripwires.

These are `#guard`s, not theorems: they pin the arithmetic of the layout and the constraint budget
so a later edit that silently drops a family goes red here. The SOUNDNESS statements
(`withEffectsHashPin_rejects_forged_declaration`, and its non-vacuity control) are the build request,
not asserted here — see the header's §Acceptance. -/

#guard EH_CARRIER == 8
#guard EH_SPAN == 41
#guard EFFECTS_HASH_PI_BASE == 16
#guard EFFECTS_HASH_PI_LEN == 4

-- The block is contiguous and non-overlapping: tag, ext, accIn, mid0, mid1, accOut.
#guard ehTagCol 1000 == 1000
#guard ehExtCol 1000 0 == 1001
#guard ehAccInCol 1000 0 == 1009
#guard ehMidCol 1000 0 0 == 1017
#guard ehMidCol 1000 1 0 == 1025
#guard ehAccOutCol 1000 0 == 1033
#guard ehAccOutCol 1000 (EH_CARRIER - 1) == 1000 + EH_SPAN - 1

-- Every absorb fits the chip bus, and the two full ones saturate it.
#guard (ehAbsorb0Inputs 1000).length == CHIP_RATE
#guard (ehAbsorb1Inputs 1000).length == CHIP_RATE
#guard (ehAbsorb2Inputs 1000).length == 9
#guard (ehAbsorb2Inputs 1000).length <= CHIP_RATE

-- Each absorb forces a full 8-lane carrier, and the tuples are the 1 + CHIP_RATE + 8 chip row.
#guard (ehAbsorbs 1000).length == 3
#guard (chipLookupTupleN (ehAbsorb0Inputs 1000)
  ((List.range EH_CARRIER).map (ehMidCol 1000 0))).length == 1 + CHIP_RATE + EH_CARRIER
#guard (chipLookupTupleN (ehAbsorb2Inputs 1000)
  ((List.range EH_CARRIER).map (ehAccOutCol 1000))).length == 1 + CHIP_RATE + EH_CARRIER

-- The 17-felt per-row contribution is covered exactly once: tag + prm[0..8] + ext[0..8].
#guard (ehAbsorb0Inputs 1000).length + (ehAbsorb1Inputs 1000).length
  + (ehAbsorb2Inputs 1000).length - 3 * EH_CARRIER == 1 + NUM_PARAMS + EH_EXT_LANES

-- The constraint budget: 1 tag + 3 absorbs + 8 continuity + 8 seed + 4 publish = 24.
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
