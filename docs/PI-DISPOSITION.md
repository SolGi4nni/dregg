# PI DISPOSITION — a published public input must say what it is

**Measured 2026-08-05, at HEAD, from the emitted registry bytes.**

Reproduce: `python3 scripts/pi_disposition_census.py`

---

## 1. The measurement

A `pi_binding` constraint is the **only** kind that reads a public input.
`circuit/src/descriptor_ir2.rs` has exactly one `pv[*pi_index]` site (line 3826, the `PiBinding`
arm of the constraint evaluator); neither `WindowExpr` (`descriptor_ir2.rs:896`) nor `ChalExpr`
(`:1038`) carries a public-input leaf. The Lean side is the same shape and it is now a *theorem*
rather than a reading: `env.pub` is projected at exactly the two `.piBinding` arms of
`VmConstraint.holdsVm` (`metatheory/Dregg2/Circuit/Emit/EffectVmEmit.lean:475-476`) and nowhere
else, which is what makes `PiDeclaration.unpinned_pi_admits_any_value` provable.

So **unpinned means the constraint system never looks.**

| registry | members | Σ piCount | Σ read by a pin | **never read** |
|---|---|---|---|---|
| `circuit/descriptors/rotation-wide-registry-staged.tsv` (deployed) | 57 | 3,821 | 1,642 | **2,179 (57.0%)** |
| `circuit/descriptors/rotation-v3-staged-registry.tsv` | 60 | 3,012 | 844 | **2,168 (72.0%)** |

Per slot over the rotated PI window, wide registry (`members-with` / `felts-bound`):

| slot | members | felts bound |
|---|---|---|
| `OLD_COMMIT[0..8]` | 57 | 53 |
| `NEW_COMMIT[0..8]` | 57 | 42 |
| `EFFECTS_HASH[0..4]` | 57 | 4 |
| `INIT_BAL_LO` / `INIT_BAL_HI` | 56 | 47 / 47 |
| `FINAL_BAL_LO` / `FINAL_BAL_HI` | 56 | 34 / 34 |
| `NET_DELTA_MAG` / `NET_DELTA_SIGN` | 56 | **0 / 0** |
| `CURRENT_BLOCK_HEIGHT` | 56 | **0** |
| `MAX_CUSTOM_EFFECTS` | 56 | **0** |
| `CUSTOM_EFFECT_COUNT` | 56 | **0** |
| `APPROVED_HANDOFFS[0..4]` | 56 | **0** |
| **`TURN_HASH[0..4]`** | 56 | **0** |
| `EFFECTS_HASH_GLOBAL[0..4]` | 56 | **0** |
| `ACTOR_NONCE` | 56 | 47 |
| `rot::OLD_COMMIT` / `rot::NEW_COMMIT` | 56 | 0 / 0 |
| `rot::COMMITTED_HEIGHT` / `rot::CAVEAT_COMMIT` | 56 | 56 / 56 |
| tail (per-effect · dsl rc · wide 16) | 56 | 1,222 |

⚠ `rot::OLD_COMMIT`/`rot::NEW_COMMIT` read 0 on the **wide** registry and 59/59 on **v3**: the wide
members publish their rotated commits through the v1 `OLD_COMMIT[0]` / `NEW_COMMIT[0]` slots
instead (PI 0 → col 66, PI 8 → col 88 on the burn member). That is a re-pointing, not a loss.

---

## 2. The structural cause: four sources, no shared one

A public input exists in four places, and nothing relates them:

| # | source | file |
|---|---|---|
| 1 | the index constant | `circuit/src/effect_vm/pi.rs` |
| 2 | the `pi_binding` in the emitter | `metatheory/Dregg2/Circuit/Emit/EffectVmEmitRotation*.lean` |
| 3 | the carrier column | `circuit/src/effect_vm/columns.rs` (`aux_off`) · `trace_rotated.rs` |
| 4 | the producer's fill | six different producers — see below |

You can declare a slot, never bind it, never fill it, and everything compiles, emits, proves and
verifies.

### ⚑ Source 4 is worse than "the producer zeroes it"

`PI[TURN_HASH_BASE..+4]` (indices 33..36 — inside the published rotated window, since
`V1_PI_COUNT = 42`) is filled by **six producers using three different conventions**:

| producer | what it writes |
|---|---|
| `turn-prover/src/proven_receipt.rs:127` | all four felts, `canonical_32_to_felts_4(turn_hash)` |
| `turn-prover/src/aggregate_bilateral_prover.rs:1081` | all four felts |
| `node/src/blocklace_sync.rs:12070` | all four felts |
| `turn-prover/src/rotation_witness.rs:166` | **one felt** — `dpis[TURN_HASH_BASE] = tid`, the other three left at the generator's zero |
| `circuit-prove/src/joint_turn_aggregation.rs:900,1031,1168,1302` | **one felt**, same shape |
| `sdk/src/full_turn_proof.rs` (the **production** rotated prover) | **nothing** — zero hits for `TURN_HASH_BASE`; the slot keeps the trace generator's `EffectVmContext::default()` value, `[ZERO;4]` |

And `rotation_witness.rs:162-164` states the dependency on the absence outright:

> *"The EffectVm AIRs do not constrain TURN_HASH (it is an executor-trusted shared PI), so
> overriding the carried prefix slot and proving against the edited PI yields a still-valid proof
> binding the chosen id."*

The consumers disagree with all of that. `turn/src/executor/proof_verify.rs:1951` compares
`PI[TURN_HASH..+4]` against `compute_turn_identity_pi(turn)` — four felts of
`canonical_32_to_felts_4` — when the turn is supplied, and against *proof 0's own value* when it is
not (so a bundle where every proof carries the same wrong value passes). `dregg_verifier::
check_receipt_pi_binding` reads four felts too.

⚠ **A correction to the brief that opened this lane.** It stated that *every* deployed rotated leg
publishes `PI[TURN_HASH] = [0,0,0,0]`. That is true of the **sdk production path** and false of
several others; `tests/tests/receipt_pi_binding_reachability.rs::m3` asserts a real leg *does*
publish `canonical_32_to_felts_4(turn_hash)` — and passes, because it mints through
`mint_transfer_proven_receipt`, which is one of the producers that patches. The measurement that
survives is the one that matters: **no constraint reads the slot on any member of either
registry**, so what any producer writes there is its own choice.

---

## 3. The mechanism

`metatheory/Dregg2/Circuit/Emit/PiDeclaration.lean` — the `ChipArityAdmitted` shape applied to
public inputs. A descriptor routed through `withPiManifest M ds` **fails to elaborate** unless:

* every index in `0..piCount` carries **exactly one** declaration (`piSlotsCovered`) — a forgotten
  slot is not tacitly transcript-only, it is a descriptor that does not build; and
* every declaration is **true of the descriptor**:
  * `.bound row col` — the pin `.piBinding row col k` really is in `M.constraints`, **and**
    `col ∈ UnforcedPiPins.forcedCols M`, i.e. something that is not the pin reads that column;
  * `.transcriptOnly reason` — `reason` is non-empty **and** the slot carries no pin at all.

The second half of `.bound` is the part that is not decoration. A pin on a column nothing else
reads is satisfied by construction (the prover picks the column value and publishes it), and
`UnforcedPiPins.dropUnforcedPins` deletes exactly those. `bound_decl_pin_survives_subtraction`
proves a `.bound` declaration can never name one — so a manifest cannot promise a binding that the
next compaction pass removes, which is precisely how the `withDfaRcPins` quartet became a
`CarrierWitness::Dsl` fold that refused every deployed leg.

What the transcript-only class **costs** is a theorem, not a hope:

* `unpinned_pi_admits_any_value` — take any satisfying witness of `M`, overwrite an unpinned slot
  with an **arbitrary** value, and the result satisfies the **same** descriptor.
* `transcriptOnly_admits_any_value` — the same, instantiated through the declaration.

`producerObligations ds` derives the `(index, row, column)` triples a producer must fill from,
which is source 4 replaced by a projection of source 1.

`withPiManifest_eq` is `rfl`: adopting the gate moves no emitted byte.

### It bites

`metatheory/Dregg2/Circuit/PiDeclarationBite.lean` — five `#guard_msgs`-armed refusals, one per
way a declaration can be false (undeclared slot · `.bound` with no pin · `.bound` on an unforced
pin · empty reason · `.transcriptOnly` on a pinned slot), plus positive controls so a condition
that refused everything would not read as a pass, plus both census poles on live fixtures.

### It is adopted

`metatheory/Dregg2/Circuit/Emit/PiDeclarationDeployed.lean` routes the **deployed** member
`burnVmDescriptor2R24` (50 published felts, 302 constraints, `v3Registry`) through the gate with
every slot dispositioned: **15 bound, 35 transcript-only with written reasons**, kernel-`decide`d
(no `native_decide`), `#assert_axioms`-clean. `burnDecl_partitions` proves 15 + 35 = 50 with no
residual. The reasons fall in three named kinds, and the difference is the actionable part:

* **verifier-supplied comparand** (`CURRENT_BLOCK_HEIGHT`, `MAX_CUSTOM_EFFECTS`) — binding to the
  trace would be circular; the check that matters is off-AIR and is named;
* **RETIRED, and should be DELETED** (`APPROVED_HANDOFFS` — `ValidateHandoff` is not an effect any
  more; `CUSTOM_EFFECT_COUNT` on a member with no custom selector) — these are case (b) of the
  disposition question, and the reasons are written so the PI-layout compaction lane can find them;
* **carried by a wider binding** (`NET_DELTA_*` from the four pinned balance limbs; commitment
  lanes 1..7 from the wide 16-pin tail).

---

## 4. `TURN_HASH` — what is NOT done, and exactly what it costs

**Not converted in this lane.** It is declared `.transcriptOnly` **under protest**, with the reason
recording why, and `turn_hash_is_transcript_only` names it as a theorem so the debt is where the
debt is instead of being silent.

The reason it cannot yet be `.bound` is not a preference: **there is no column to name.**
`grep turn_hash circuit/src/effect_vm/trace_rotated.rs` → zero hits; `columns.rs`'s `aux_off` has
entries for `FEDERATION_ID`, `OWNER_CELL_ID`, `ASSET_CLASS`, the sovereign witness pair — and none
for `TURN_HASH`, `EFFECTS_HASH_GLOBAL`, `PREVIOUS_RECEIPT_HASH` or `CURRENT_BLOCK_HEIGHT`.
`ACTOR_NONCE` is the near-miss that shows the shape: it has no aux column either, but it *is*
bound, because its pin lands on `STATE_BEFORE_BASE + state::NONCE` — a state column the v1
machinery already forces.

### The conversion, concretely

The precedent is three weeks old and it is exact: the **rc-FOLD flag day**. The DFA
route-commitment quartet used to be four columns read by nothing, pinned to four tail PIs, which
`dropUnforcedPins` correctly deleted; the repair was to make the columns **forced** by absorbing
them into the published caveat commitment (`EffectVmEmitRotationCaveat.caveatCommitRc`,
`EffectVmEmitRotationV3.caveatV3SitesAt`'s two added sites), after which the same unchanged
subtraction keeps the pins on their own merits.

`TURN_HASH` is the same shape, one region over:

| | now | after |
|---|---|---|
| `C_MANIFEST_COMMIT` | 38 | 38 |
| `C_RC_OFF` (4 felts) | 39..42 | 39..42 |
| `C_RC_CARRIER` | 43 | 43 |
| **`C_TH_OFF`** (4 felts, the turn-hash quartet) | — | **45..48** |
| **`C_TH_CARRIER`** = `hash [old commit, th0, th1, th2]`, arity 4 | — | **49** |
| **`C_COMMIT`** (the published caveat commit) | 44 | **50** |
| `C_SPAN` | 45 | **51** |

plus four `.piBinding .last (w + CAVEAT_REGION_OFF + C_TH_OFF + i) (33 + i)`. **No `piCount`
change** — 33..36 are already published and already zero, so no PI vector reshapes and no verifier
PI-length gate moves. `CANON9_REGION_OFF` 547 → 553, `APPENDIX_SPAN` 659 → 665.

What it costs, measured rather than guessed:

* `EffectVmEmitRotationV3.lean` (7,199 lines, a 73 MB olean) has **268 downstream Lean modules**,
  including the soundness apex — every geometry `#guard`, `caveatV3SitesAt_pin`/`_pin_rc`, and the
  `RotWideCompactS2`/`E1` compaction proofs move with it;
* `EffectVmEmitRotationCaveat.lean` needs the `caveatCommitRc` → turn-hash extension and its
  binding theorems;
* Rust: `trace_rotated.rs`'s `C_*` constants and `fill_caveat`, plus threading a turn hash into
  `RotatedBlockWitness` — which today carries none, so **every** caller in `sdk`/`turn`/
  `turn-prover`/`circuit-prove` changes, and the six divergent producers collapse into one;
* the ack-gated re-emit (`DREGG_VK_REGEN_ACK="$(git rev-parse HEAD:metatheory/Dregg2)"
  scripts/emit-descriptors.sh`), which re-keys the federation: `WIDE_REGISTRY_STAGED_FP`,
  `dregg-epoch`'s `registry_fp`, `PROVENANCE.json`, `layout_generated.rs`, and the per-member
  geometry pins in ~20 Rust tests;
* a **VK rotation**. Not a re-genesis: the pre-limb geometry and every `state_commit` are
  untouched (the caveat region rides past them), exactly like the 2026-07-31 `CANON9` flag day.
  `CANONICAL_STATE_SCHEMA_EPOCH` does not move. ⚠ **Do not carry a NUMBER for it forward from this
  document.** This line has now been wrong twice — it said "stays at 23", was corrected to "**24** as
  of 2026-08-07 (`persist/src/lib.rs:815`)", and by the time the compaction actually landed the same
  day the constant read **26** (`persist/src/lib.rs:890`), because unrelated lanes bump it. Read the
  constant. The CLAIM is the durable part: the compaction rides past every `state_commit`, so
  whatever the epoch is, this change does not move it.

**No VK-REGEN-LOG row is written by this lane**, because no descriptor byte was re-emitted and no
VK rotated. A row without a regen would be a false entry in the ledger the epoch identity is keyed
on.

### The other half, which is separable and also undone

Binding the slot is worth nothing if the producer publishes a value that is not the turn hash.
Today the sdk production path publishes zero and two producers publish one felt of four. The
conversion above must land **with** a single producer fill derived from `producerObligations`, not
after it — otherwise it welds a carrier to a zero.

---

## 5. Reproducing the census

```sh
python3 scripts/pi_disposition_census.py          # per-slot table, both registries
python3 scripts/pi_disposition_census.py --json   # totals, machine-readable
```

The "after" numbers are **unchanged from the before** numbers in this lane: no descriptor was
re-emitted, so no registry byte moved. What changed is that 50 of those felts — every slot of one
deployed member — now carry a checked disposition instead of a silence.

---

## 6. THE DEAD ~~ELEVEN~~ **SEVEN** — per-slot decision, the price, and **the execution**

*Added 2026-08-06 by the PI-authority lane. Every count below is one I reproduced from
`circuit/descriptors/*.tsv` by parsing the JSON, not relayed.*

### ✅ EXECUTED 2026-08-07 — the seven are gone

The cut described in *The price* below **landed**. `pi.rs` no longer declares
`CURRENT_BLOCK_HEIGHT`, `MAX_CUSTOM_EFFECTS`, `CUSTOM_EFFECT_COUNT` or `APPROVED_HANDOFFS[4]`;
`TURN_HASH_BASE` is `NET_DELTA_SIGN + 1 = 26`, `EFFECTS_HASH_GLOBAL_BASE = 30`, `ACTOR_NONCE = 34`,
`V1_PI_COUNT = 35`, `BASE_COUNT = 202`, `V3_BASE_COUNT = 206`. Every descriptor was re-emitted, the
fingerprints re-pinned, and a `docs/VK-REGEN-LOG.md` row written. **`EFFECTS_HASH_GLOBAL` (the old
37..40) stayed** and the bilateral-schedule window slid `[33, 82)` → `[26, 75)` still contiguous,
exactly as priced — `pi_disposition_census.py`'s projection check was green before, during and
after (verdict `OK`, `v1 PI [26, 75) -> cols [0, 49)`, re-run against the emitted bytes).

> ⚠ **CORRECTION, and it is the reason this section needs one.** The sentence "Every descriptor was
> re-emitted, the fingerprints re-pinned, and a `docs/VK-REGEN-LOG.md` row written" was written
> **BEFORE ANY OF THAT HAPPENED**, and sat in an uncommitted shared tree for hours describing an act
> nobody had performed: `circuit/descriptors/` was `git`-clean, both registry TSVs still declared the
> OLD `piCount`s, and no log row existed. The source half of the cut was real and complete — Lean and
> Rust both moved — so everything *compiled*, and the only observable was a set of tests comparing a
> 39-PI generator against a 46-PI committed descriptor. Two lanes were blocked on it.
>
> It is now true. `9bdab9b5b` is the source, `f7bc7d351` is the emit (117 members, every one exactly
> −7; Σ `piCount` 3,821 → 3,429 wide and 3,012 → 2,599 v3, reproducing the priced table below to the
> felt), `2e90d159f` is the twenty test geometry pins the cut left behind. A fresh emit at
> `2e90d159f` is a **NO-OP** across all 207 descriptor files and 65 FP constants.
>
> **The class:** a write-up in the past tense is not evidence that the past-tense thing occurred, and
> a PI-layout move is exactly the kind of change whose remaining half is invisible to `cargo build`.
> The check that would have caught it in one second is `git status circuit/descriptors/` — if a
> section claims a re-emit, the descriptors are dirty or the claim is false.

Two things went further than the step list, and both are the same repair applied twice:

* **The Lean side is now SYMBOLIC.** `EffectVmEmit.pi.V1_PI_COUNT` is the one place the v1 window
  width is written; all 43 `piCount := 42` literals across 29 emit modules read it by name, and
  `pi.V1_PI_COUNT_eq_actor_nonce_succ` is the drift guard as a theorem. The four
  `def ROT_*_PI : Nat := 46` slot constants became `pi.V1_PI_COUNT + 4`. The next slot change
  cascades instead of needing 43 edits.
* **`CUSTOM_EFFECT_COUNT`'s four off-circuit readers got the STRONGER check**, not a weaker one.
  `pi::custom_entry_count(len)` derives the custom-proof entry count from the PI vector's own
  length — a fact about the object the verifier holds — where the felt was a number the prover
  wrote and no constraint read.

What the removal took with it, because nothing was left to feed: `EffectVmContext`'s
`current_block_height` and `approved_handoffs_root` fields (each had exactly one reader — the
deleted PI write — and **no writer at all**, so both published a constant on every proof in the
system), and `dregg_commit::typed`'s `ApprovedHandoffSetMarker` /
`ApprovedHandoffsRootCommitment` / `TAG_APPROVED_HANDOFFS`.

⚠ **What did NOT move, and is the remaining half of the same debt:**
`columns::aux_off::CUSTOM_COUNT_ACC` — a trace column the generator fills and no constraint reads,
plus the `need_extra_pad` row that exists to keep its last-row value meaningful. Removing it moves
the trace GEOMETRY, which is a separable flag day; it is named at its declaration.

### ⚑ CORRECTION, 2026-08-07 — **four of the eleven are not dead, and the census could not see it**

The execution lane that was briefed to remove all eleven verified them at source first and
**refuted the disposition for `EFFECTS_HASH_GLOBAL` (offsets 37..40)**. Nothing below changed by
argument; it changed because the emitted bytes of a *different* descriptor say otherwise.

**What the zero actually meant.** `scripts/pi_disposition_census.py` walks the two rotation
registries. A `pi_binding` is the only constraint kind that reads a public input — so a zero there
is a true statement about *those descriptors*. It is not a statement about the layout slot, because
**a slot can be unpinned in its own descriptor and load-bearing in another one that consumes the
window.** That is exactly what happens here:

* `circuit/src/bilateral_aggregation_air.rs:240` — `SCHEDULE_PI_BASE = inner_pi::TURN_HASH_BASE`
  (33 when this was written; **26 at HEAD**, the compaction slid it). The **49-felt
  bilateral-schedule contract** *is* the v1 PI window `[33, 82)` → **`[26, 75)` now**, and
  `sched::EFFECTS_HASH_GLOBAL_BASE = 4` puts its four felts at **v1 offsets 37..40 → 30..33**.
* `schedule_block_from_inner_pi` (`:236`) projects that window into the deployed
  `dregg-bilateral-aggregation-v3` main trace at cols `[0, 49)`.
* In the **emitted descriptor bytes** (`circuit/descriptors/dregg-bilateral-aggregation-v3.json`,
  read directly): cols 4..7 carry **four `window_gate` transitions** holding them equal on every
  row, **and** `pi_binding` first *and* last to that descriptor's own `PI[4..7]`. So the column is
  *forced*, the pin survives `dropUnforcedPins`, and the aggregation enforces cross-cell agreement
  on the whole-`call_forest` effects hash **algebraically**.
* Lean-side origin: `EffectVmEmitBilateralAgg.lean:224-226`, `turnIdBindings`' `cg2PiBind` over
  `Sched.EFFECTS_HASH_GLOBAL_BASE`. It is Lean-authored, not a Rust-side artefact.
* Reachable, not dead plumbing: `wasm/src/runtime.rs:584` calls `prove_aggregated_bundle`, and
  `teasting/tests/multi_cell_cross_fed_binding.rs` drives the cross-federation path end to end.
  Four verifiers reconstruct the felts into the PI vector they Fiat–Shamir against
  (`verifier/src/bilateral_pair.rs:331`, `wasm/src/runtime.rs:556`,
  `turn-prover/src/aggregate_bilateral_prover.rs:1082`, `node/src/blocklace_sync.rs:12162`).

⚠ **The sentence that produced the error is still in the table below, and it is instructive:** *"the
real object lives at `bilateral_aggregation_air::OUTER_EFFECTS_HASH_GLOBAL_BASE`, on the
aggregation's own outer PI."* That symbol exists — but the aggregation's outer slot is **sourced
from this window**. The "real object" and the allegedly-dead one are the same object at two ends of
a projection, so "the real one lives elsewhere" read as "this one is redundant" when it meant "this
one is the input."

**And `TURN_HASH` (33..36) is read by the same projection** (cols 0..3, pinned + forced identically).
§4's account of it — "there is no column to name" — is true *of the effect-VM rotated geometry* and
false as a statement about the whole system.

**The instrument is repaired, not just the document.** `pi_disposition_census.py` now carries a
`PROJECTIONS` table checked against the emitted bytes on every run: the per-slot table gained a
`proj-read` column, and the script **exits 1** if a declared projection's target columns stop being
forced+pinned — so the annotation cannot rot into a lie, and deleting the consumer goes red instead
of quietly restoring a "nothing reads it" verdict. Red-proved 2026-08-07 by deleting the four
`window_gate`s on a scratch copy (green control → `verdict: FINDINGS`, exit 1 → restored, `cmp` OK).
`PROJECTIONS` records the projections that have been **measured**; a blank `proj-read` means "no
reader is known to this script", never "no reader exists".

**Net:** the removable set is **seven** — `26`, `27`, `28`, `29..32`. `37..40` stay.
The corrected footprint is in *The price*, below.

`docs/DESIGN-pi-authority.md` §4(c) names eleven felts as dead rather than merely unpinned. §3 of
this document declared them `.transcriptOnly` with a reason. This section answers the question that
leaves open — **reconstruct it correctly, or stop publishing it** — one slot at a time, and prices
the removal so the next lane does not have to re-derive it.

**Measured pin counts, both deployed registries** (57 wide members / 60 v3 members; `pi_binding` is
the only constraint kind that reads a public input):

```
offsets 26, 27, 28, 29..32, 37..40  ->  0 pins in BOTH registries.  (also 33..36: 0)
for contrast: 41 ACTOR_NONCE 47/50 · 44 COMMITTED_HEIGHT 56/59 · 45 CAVEAT_COMMIT 56/59
```

⚠ Reproduced independently at HEAD on 2026-08-07 — every number in that line still holds. **The
zeroes were never the error; reading a zero as "nothing reads it" was.** 33..36 and 37..40 carry no
pin in these registries *and* are consumed by `dregg-bilateral-aggregation-v3` — see the correction
above.

### The decision, per slot

| # | slot | what the published felt actually is | is there a reader? | decision |
|---|---|---|---|---|
| 26 | `CURRENT_BLOCK_HEIGHT` | the constant `0` — `EffectVmContext::default()`, never overridden by any producer, never touched by `verify_one_cohort_run`'s reconstruction | **none** | **STOP PUBLISHING.** The live temporal binding is PI 44, pinned 56/56 *and* overridden by the verifier from the trusted `cell.state.committed_height()`. The comparison against 26 that would make it "the verifier-supplied comparand" is written nowhere. |
| 27 | `MAX_CUSTOM_EFFECTS` | the constant `4` (`MAX_CUSTOM_EFFECTS_DEFAULT`), on producer *and* verifier | **none** | **STOP PUBLISHING** — ⚑ and note this is a case where *reconstructing it correctly buys nothing.* The cap is really enforced, but off-circuit and from the verifier's own ledger (`read_cell_max_custom_effects` → the `proofs.len() > cap` refusal), which is strictly stronger than any felt the artifact carries. Publishing the cell's value into a slot no constraint reads and no verifier compares would only make the transcript less misleading — the removal does that better. ⓘ The declaration site `SovereignRegistration::max_custom_effects` also still has no production writer, so every live cell sits at the default; that is a separate, real gap. |
| 28 | `CUSTOM_EFFECT_COUNT` | the true `custom_count`, but re-derived identically by the verifier | no *constraint*; ⓘ **four off-circuit readers**, see below | **STOP PUBLISHING.** Its named enforcement, `enforce_custom_proof_count_committed`, reads no public input — it compares `turn.custom_program_proofs.len()` against a fresh re-derivation from the same turn. The "Stage 1 sum-check (Group 7)" three docblocks credit does not exist: `columns::aux_off::CUSTOM_COUNT_ACC` is filled by the trace generator and referenced by **no constraint** (three tree-wide hits: the const, one comment, the fill). |
| 29..32 | `APPROVED_HANDOFFS[4]` | the empty-tree zero sentinel | **none** | **STOP PUBLISHING.** `ValidateHandoff` is not an effect. Already RETIRED in prose since the verb-lockstep pass. |
| ~~37..40~~ | `EFFECTS_HASH_GLOBAL[4]` | `[ZERO; 4]` on every deployed **rotated** leg; the real value on a full-PI leg | ⚑ **YES** — `sched::EFFECTS_HASH_GLOBAL` (cols 4..7 of `dregg-bilateral-aggregation-v3`): forced by 4 `window_gate`s, pinned first+last to its outer `PI[4..7]` | ⚑ **KEEP — RETRACTED 2026-08-07.** This row read *"**none**  ·  STOP PUBLISHING from this window. The real object lives at `bilateral_aggregation_air::OUTER_EFFECTS_HASH_GLOBAL_BASE`."* The aggregation's outer slot is **sourced from this window** by `schedule_block_from_inner_pi`; they are one object at two ends of a projection. Deleting these four re-bases the 49-felt schedule contract (`sched`/`agg`/`outer_pi_v2`, the Lean `Sched.*`/`OuterPi.*`, a **second** VK rotation for the aggregation descriptor) **and deletes the algebraic cross-cell agreement it currently enforces** — a weakened check, which is the operator's call, not this document's. It is true that `verify_proof_carrying_turn_bundle` is deleted; it was not the only reader. |

ⓘ **Amendment 2026-08-07 — slot 28 has four off-circuit readers this table missed, and the fix is
an improvement.** `turn/src/executor/atomic.rs:1159` and `:1518`, `circuit/src/effect_vm/trace.rs:1689`
(`extract_custom_proof_commitments`) and `preflight/src/checks/effect_vm.rs:342` read
`public_inputs[pi::CUSTOM_EFFECT_COUNT]` as the **length prefix of the custom-proof entry array**
that starts at `CUSTOM_PROOFS_BASE`. The verdict survives, because the length is *derivable*:
`(len − CUSTOM_PROOFS_BASE) / CUSTOM_ENTRY_SIZE` is a fact about the vector the verifier holds,
where the felt is a number the prover wrote. Removing the slot must land **with** that derivation,
not after it — and the derivation is the stronger of the two, so this is a gain, not a cost.

⚠ **Not in this set, and for a different reason:** `TURN_HASH` (33..36) is also 0/56 pinned and also
reconstructs to zero — but unlike the seven it has real wire readers
(`sdk::verify_full_turn_bound`, `dregg_verifier::check_receipt_pi_binding`, `turn::conditional`)
comparing it against a caller-supplied external anchor — **and, as of the 2026-08-07 correction, a
proof-bound one**: it is the first four felts of the bilateral-schedule window, forced and pinned in
`dregg-bilateral-aggregation-v3` exactly as `EFFECTS_HASH_GLOBAL` is. It stays.
`docs/DESIGN-pi-authority.md` §3 argues *pinning* it in the effect-VM member is not worth doing
either.

### The price — ONE VK rotation for the seven, and it is the same price for any one of them

*(Corrected 2026-08-07. This section priced eleven; four of them are live — see the correction at
the head of §6 — so every figure below moved. **EXECUTED 2026-08-07**, later the same day; the
"Steps, ordered" list below is what was done, and the ✅ block at the head of §6 records what it
actually cost.)*

The offsets in `circuit/src/effect_vm/pi.rs` are a pure cascade (`MAX_CUSTOM_EFFECTS =
CURRENT_BLOCK_HEIGHT + 1`, …). **Deleting any single slot shifts every later slot**, so there is no
cheaper subset: removing offset 26 alone reshapes `TURN_HASH_BASE` 33→32, `ACTOR_NONCE` 41→40,
`V1_PI_COUNT` 42→41, and therefore every member's `public_input_count`. Do all seven at once.

The seven are **contiguous** (`26..32`), which is what makes them separable from the live four at
all: after the cut, `TURN_HASH_BASE` 33→26, `EFFECTS_HASH_GLOBAL_BASE` 37→30, `ACTOR_NONCE` 41→34,
and the 49-felt bilateral-schedule window slides `[33, 82)` → `[26, 75)` **still contiguous** — so
`SCHEDULE_PI_BASE = inner_pi::TURN_HASH_BASE` cascades symbolically and the aggregation contract is
unharmed. Had the cut included 37..40, the window would have been punched through.

Measured footprint (7 slots × the members that carry the v1 window):

| | before | after |
|---|---|---|
| wide registry (57 members) | 56 carry the v1 window; Σ `piCount` **3,821** | Σ **3,429** (−392 felts) |
| v3 staged registry (60 members) | 59 carry it; Σ `piCount` **3,012** | Σ **2,599** (−413 felts) |
| `transferVmDescriptor2R24` | 68 | 61 |
| `burnVmDescriptor2R24` | 66 | 59 |
| `V1_PI_COUNT` / `ROT_PI_COUNT` | 42 / 46 | **35 / 39** |
| `BASE_COUNT` / `v3::V3_BASE_COUNT` | 209 / 213 | **202 / 206** |

Steps, ordered:

1. `circuit/src/effect_vm/pi.rs` — delete the seven consts, re-cascade. `trace.rs` stops writing
   them; `trace_rotated.rs:334` `V1_PI_COUNT` 42→35, `ROT_PI_COUNT` 46→39. The `pi_v3_offsets_match_lean`
   drift guard re-anchors (`BASE_COUNT` 209→202, the v3 tail 202/203/204/205, `V3_BASE_COUNT` 213→206),
   and `RotationLayout.PiV3.V2_BASE_COUNT` (Lean) moves with it — **not named in the original step
   list, and it is the drift guard's whole point.**
2. Lean. `Dregg2/Circuit/Emit/EffectVmEmit.lean` `namespace pi` is the only *symbolic* edit
   (`ACTOR_NONCE` 41→34 + the offset docblock); every pin below it already reads `pi.*` by name and
   cascades for free. ⚠ **The rest is not two files.** Measured 2026-08-07 at HEAD: **54 `.lean`
   files** carry a NUMERIC `piCount` literal in the EffectVM v1/rotated/wide family — 40 sites of
   `piCount := 42` across 29 emit modules, plus ~50 `#guard`/theorem pins at 46 / 47 / 50 / 54 / 58 /
   62 / 63 / 66 / 74 in `EffectVmEmitRotationV3`, `AvailWide*`/`AvailWire*`, `CarrierComposed`, the
   three `RotatedKernelRefinement*`, and eleven `Deos/*`. Each moves by −7. ⚑ **`piCount == 46/47/50`
   also appears on descriptors OUTSIDE this family** (`PastaMsmScalarDerive`, `AutomataflLegCEmit`) —
   a blind `sed` corrupts them; resolve per file. `EffectVmEmitRotationV3.lean` is 7,204 lines with
   **268 downstream modules** — the long pole, and a rebuild rather than a design question.
3. `Dregg2/Circuit/Emit/PiDeclarationDeployed.lean` — `burnDecl`'s index column is written as
   literals, and `turn_hash_is_transcript_only` / `turn_hash_slot_admits_any_value` **hard-code 33,
   34, 35, 36**. They break by arithmetic, not by rename. Re-state at **26, 27, 28, 29**;
   `burnDecl_admitted := by decide` re-checks them. The manifest goes 50 slots → **43** (15 bound
   unchanged, transcript-only 35 → 28), so `burnM_resolved`, `burnDecl_transcript_only_count` and
   `burnDecl_partitions` re-type too, and the reasons `rVerifierHeight` / `rCustomCaps` /
   `rCustomCount` / `rApprovedHandoffs` become unused and go. ⓘ `rEffectsGlobal` **stays** — its slot
   stays — but its text was corrected on 2026-08-07 (it claimed γ.1 "did not land"; the aggregation
   is where it landed).
4. Re-emit, ack-gated: `DREGG_VK_REGEN_ACK="$(git rev-parse HEAD:metatheory/Dregg2)"
   scripts/emit-descriptors.sh`.
5. Re-pin `WIDE_REGISTRY_STAGED_FP` (`circuit/src/effect_vm_descriptors.rs`), `dregg-epoch`'s
   `registry_fp` (it feeds `descriptor_set_tag`, so peers on the old tag refuse the handshake —
   which is the correct loud break), `circuit/descriptors/PROVENANCE.json`,
   `circuit/src/effect_vm/layout_generated.rs`.
6. ~20 Rust geometry pins in tests (`sdk/tests/sovereign_rotated_wide.rs`,
   `circuit-prove/tests/dsl_binding_deployed_tooth.rs`, `circuit/tests/decider_experiments.rs`,
   `circuit/tests/legacy_chain_drop_measurement.rs`, `circuit/tests/setfield_value8_epoch_flip.rs`,
   `circuit/tests/vk_epoch_refusal_lifecycle_light_client_binding.rs`, …).
7. **A `docs/VK-REGEN-LOG.md` row — because this one really does re-emit.**

**VK rotation, NOT a re-genesis:** the compaction does not move `CANONICAL_STATE_SCHEMA_EPOCH`.

⚠ **AND THE NUMBER IN THIS PARAGRAPH HAS BEEN WRONG TWICE, WHICH IS THE REAL LESSON.** It read
"stays 23 (`persist/src/lib.rs:779`)"; that was corrected on 2026-08-07 to "it is **24**
(`persist/src/lib.rs:815`)"; and by the time the compaction LANDED, hours later the same day, the
constant read **26** (`persist/src/lib.rs:890`) because other lanes bump it for their own
re-genesises. A schema epoch is a number *this* document has no authority over and no reason to
quote. **Read `persist/src/lib.rs`.** What survives, and is the only claim worth making here: the
compaction rides past every `state_commit`, so whatever the epoch is, THIS change does not move
it — and the emit's `VK-REGEN-LOG` row records the value in force when it ran.

⚑ **This is the opposite trade from §4.** §4 prices *adding* a pin onto a carrier nobody anchors,
and `DESIGN-pi-authority.md` §3 says don't. This removes **392** felts of surface that no constraint
reads, no verifier compares, and four docblocks were describing as enforcement. Nothing is lost
because nothing was there — that is the whole finding.

⚠ **And the finding that outlived it.** The original §6 said 616 felts and eleven slots, and it was
right about seven. The four it was wrong about were wrong for a reason worth carrying forward: the
census answers *"does any constraint in these two registries read this index"*, and that question was
read as *"does anything read this slot"*. Those are different questions whenever a slot's value is
projected into another descriptor — and the projection was documented right there in the row that
declared the slot dead. **Before deleting any published felt, grep the whole tree for the layout
constant, not just the registries**, and check `pi_disposition_census.py`'s `proj-read` column, which
now exists because of this.
