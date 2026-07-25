<!-- ⚑ This repo runs MULTIPLE concurrent /goal sessions — see GOALS-INDEX.md.
     This file is the **proof-assurance** lane trail. Edit only this one. -->

> ⚑ **Multiple goals are live — see [`GOALS-INDEX.md`](GOALS-INDEX.md).** This is the
> **proof-assurance** lane. Adjacent by design: `honest-verification` (carrier debt) and
> `greens-that-mean-something` (vacuous theorems). Coordinate, don't collide.

# GOAL — PROOF ASSURANCE: make the arguments SENSIBLE, not just green

**Standing goal:** grind down proof engineering / assurance / argument-sensibility / refactor /
replacement. Re-set 2026-07-25, running to **9pm**. Thrust has moved from the Lean apex to the
**Rust/Lean boundary** — and, per ember, to **deleting Rust so the logic lives in Lean**.

## The thesis
A proof can be kernel-clean, `sorry`-free, non-vacuous *in its own terms*, and still say nothing —
because its **premise is empty**, its **antecedent is the wrong object**, its **reach doesn't cover
the regime it's quoted for**, or its **types model a different system than the deployed one**. This
lane hunts and heals that class.

Governing rule: *a carrier vacuous at deployed parameters is a **sin**, not a hypothesis to carry.*
Cutovers, not parallel towers.

## The wound classes (calibrated from real finds, not theory)
1. **Empty premises.** PROVED: the landed extraction bundle forces `verifyBatch` to reject *every*
   input, so the apex quantified over an empty accepting set and was vacuously true.
   `#assert_axioms` is **structurally blind** to this — the vacuous apex was kernel-clean and true.
2. **Wrong-object antecedents.** `FriLdtExtractV3` was assumed over a verifier the tree *itself*
   proves is foolable, while the deployed apex uses a stronger one.
3. **Vacuous named residuals.** `TranscriptWordCommitment` is literally `Classical.em` pointwise.
4. **Field-typing infidelity.** Deployed quartic-extension challenges modelled as base felts —
   *not* a restriction (lane-0 projection isn't multiplicative), a **different equation**.
5. **Reach ≠ truth.** Theorems true, clean, non-vacuous — and not covering the regime cited.
6. **Out-of-CI proof.** A seven-file subtree outside the build target; committed imports pointing
   at untracked files (has broken a fresh checkout **three times** today).

## ⚑ VERIFICATION HYGIENE — a false green this lane produced twice

**`lake build … | tail` reports the PIPELINE's exit status, not lake's.** A failing build reads as
success. This produced a false green twice today: once in my own check, and once in a lane that
*reported green on a file with 8 compile errors*. Capture the status **inside** the subshell before any
pipe (`( lake build X; echo EXIT=$? ) | tail`), or redirect to a file and grep. And `lake env lean <file>`
is fast and authoritative for compile errors — use it before reporting.

This is the "greens that mean something" class turned on our own tooling, which is why it belongs here.

## The two instruments, and why BOTH are needed

They catch disjoint classes, and neither sees the other's:

| | catches | blind to |
|---|---|---|
| `#assert_axioms` (in-tree, fires on build) | `sorryAx` and non-kernel axioms — *what a proof rests on* | an **empty premise**: the vacuous apex was kernel-clean, sorry-free, and *true* |
| `PremiseInhabitability` | premises nothing can satisfy | a **carrier-gated** class whose `extractable : Prop` is `True` — that mode never mentions acceptance |
| `CarrierAudit` | evasive `True` carriers — demands a *refutation* at a broken sibling oracle | **mode 3** (below), and it *misclassifies* an **honest** `True` |
| `ConclusionTotal` / `WitnessBearing` | mode 3, and honest-vs-evasive `True` | the deployment question — see the ceiling |

### ⚑ THE THREE VACUITY MODES

Modes 1 and 2 live on the **antecedent**. Mode 3 lives on the **conclusion**, and was found by the
instrument built to check modes 1–2 — proving that criterion insufficient:

3. **A total conclusion** makes a gated theorem free with the carrier *and* the acceptance hypothesis
   **deleted**, while `CarrierLive` reports green, axioms are clean, and no `sorry` exists.

Live instance, and the strongest verdict in the sweep: **`nonmembership_verify_sound` is a tautology at
every instantiation** — its conclusion `∃ leaves, NonMember leaves stmt.elem` is discharged by
`leaves := []` and never mentions `stmt.root`. **No deployment can repair it.** And the polarity
*inverts* on the reference Merkle kernel: the **forge** kernel's conclusion bites while the
**reference** one does not — the instance cited as the family's reassurance is the one saying nothing.

### The sweep that finds hygiene leaks (repeatable)

`( lake build; echo FULL=$? ) > log 2>&1` then `grep "axiom-hygiene FAIL"`. **The tripwire only fires
when someone actually builds the module** — which is why two RED-at-HEAD leaks sat unnoticed today, each
written off as contention by a lane that never got a clean build. Run 2026-07-25: **zero failures outside
`Games.Dungeon`**, whose eight are `*_admitted` placeholders in three files a co-tenant has open. The
FRI/soundness cone is hygiene-clean.

## The instrument
`Dregg2/Circuit/PremiseInhabitability.lean` — `Empties P acc := P → RejectsAll acc`, `Extracts`,
`empties_of_refuted`, `empties_proves_anything`, `not_of_empties_of_acceptsSome`. Turns "audit note"
into "theorem". **Repair obligation:** every fix must prove the corrected conjuncts are *implied by
acceptance* (hence add zero strength) — a repair that swaps one vacuity for another is worse than
none, because it looks fixed.

## ⚑ THE APEX IS CUT OVER (2026-07-25)

`starkSound_of_friLdtExtract_transferV3` keeps its name and now takes `FriLdtExtractV3Faithful` instead
of the bundle **proved** to force `verifyBatch` to reject every input. All 8 consumers migrated; verified
myself that the only remaining hypothesis sites on a proved-empty bundle are a *labelled subsumption
receipt* and a *transport*, not consumers. **No soundness conclusion in the tree is drawn from a
proved-empty premise.**

Every migration is a **strengthening** (`V3 → Cons → Faithful`), and `retiredPremise_imp_apexPremise`
proves migration costs a consumer nothing. What it buys, exactly: the premise no longer *forces*
universal rejection. It does **not** prove satisfiability at the opaque `cfg*` args — nothing can.

## In flight
- `eval-oracle` — `ir2_eval_accepts` rejects *everything*, making 3 assertions unfalsifiable
- `ci-did-it-run` — CI cannot distinguish "passed" from "never ran"
- `delegAdmit` — one Lean `def`, **three** Rust copies; export + FFI + delete (wasm seam to handle honestly)
- `wide_value_binding` — 639 lines of Rust AIR added *for the felt-width repair*; Lean route

## ⚑ LANDED: the param-compose production path is OFF the Rust AIR

`param-compose/src/witness.rs` + `lean_descriptor.rs` + the `entity-compose` rewire are **committed and
type-verified** — `CHECK_PARAM_COMPOSE=0` on the shared dir plus four green side-checks in a private
target dir. Zero `param_compose::air|builder` imports remain on any production path;
`entity-compose::air_accepts` is deleted. **1028 lines now dead to production but not yet removed.**

Still held (correctly): `braid-hook` + `dreggnet-companion` — their `--features prove` surfaces are the
deepest part of the rewire and are **not type-checked**. Also held: the `delegAdmit` Rust side.

**Technique worth reusing:** when the shared cargo lock is saturated (this session hit **load 419 on 12
cores**), a private `CARGO_TARGET_DIR` side channel gets an independent type-check through. It pays the
cold-build cost but it is not blocked.

## ⚑ (superseded) HELD, PENDING TYPE-CHECK — do not commit until green

The `param-compose` witness producer + production rewire is **written but never compiled**: the shared
cargo lock was saturated all session (75 procs, load 193/12 cores), so *not one* invocation ran.
- Uncommitted: `param-compose/src/witness.rs` (804), `lean_descriptor.rs` (100),
  `tests/lean_witness.rs` (399), plus the `entity-compose` / `braid-hook` rewire.
- **Production path is already off the Rust AIR** — zero `param_compose::air|builder` imports remain,
  and `entity-compose::air_accepts` is deleted.
- What *is* verified without a compiler: `rustfmt` parses all 12 files, and the layout was checked
  against the **emitted bytes** at ~40 independent points (all 37 PI bindings at both shapes, all 18
  chip tuples, `forced_ge0` expanded coefficient-for-coefficient). Logic checked; **types are not**.
- Gate: `/tmp/lane-verify.log` or `/tmp/pc_verify.log` showing `= 0`.

**Deletion still blocked on two things, both recorded in the ratchet itself** (`721cca7843`): ~1935 lines
of `param-compose/tests/*` exercise shapes Lean has **not** pinned (only `pcMin`/`pcRealistic` are
emitted), and the two BASELINE rows must die *in the same commit* as the files or the stale-entry check
fires.

## ⚑ THE BOUNDARY FINDINGS (2026-07-25 afternoon)

**CI had been dead for five days.** A PQ-lane commit about ML-KEM deleted the FriLedger FFI binding while
two committed tests still imported it. `cargo test --workspace` compiles *all* targets before running
*any* — so zero tests ran, silently disabling the law-1 ratchet and all 23 emit gates. Restored; gates
green (181 passed, **no drift** across the blackout). Full record:
`docs/WOUND-ci-gates-dead-since-2026-07-20.md`.

**The bucket root does not bind.** `⟨by decide, rfl⟩`, zero axioms: two distinct `Object`s share one
deployed content root. Cause isolated to `Int.toNat` clamping in one line; fix is a wire change on the
`@[export]` path. *Injectivity could never have found this — it is false at both encoders.* That is the
argument for the whole game-floor cutover.

**The forgery teeth all bite.** Four soundness teeth were red; **zero live soundness holes**. The
constraint system refused every forgery — the harness couldn't *observe* it, because p3 **panics** before
`Err` is reachable. `refusal.rs` had this wrong: the discriminator is **lookups**, not the `check` flag.

**A Rust AIR nobody could see.** `param-compose` — 1028 lines *with* `air_accepts`, live on the deployed
`Effect::Custom` door, no Lean route, invisible to the ratchet (wrong scope *and* an unmatched dialect).
Its own doc reveals it was copied out of automatafl's builder **before** that AIR was deleted. Now fully
authored in Lean and byte-pinned.

## Next moves (my pick)
0. ~~Bare-premise cutover~~ · ~~`TranscriptWordCommitment`~~ · ~~duplication debt~~ · ~~base-field
   typing sites~~ · ~~`∀ S`~~ — **all DONE**.
1. **The felt-width adjacency**: `SingleAirOpening.alpha`, `TableOpening.constraintEval` /
   `vanishingAtZeta` / `quotientAtZeta` still store ONE felt. The ext work types the *statement's*
   challenge; it does not widen the serialized record.
2. **Price the LogUp ε** — `LogUpSoundness.exceptionalSet_card_lt` exists; nobody has put it in the
   game frame, so `BusModelOk.nonexceptional` has no `winProb` bound at either field.
3. **The other branch of the dichotomy** — `∀ S` proves farness survives for a *fold-consistent* prover;
   that a fold-**inconsistent** prover is caught by the query phase is proved nowhere in-tree.

## ⚑ R11 REFINED — honest `True` vs evasive `True`

Both look identical to `rg "extractable := True"`. They are not the same finding:

* **EVASIVE** (the wound; all eight carrier-gated reference kernels): the carrier is `True` to AVOID
  proving something, so the soundness theorem is true-and-unappliable. `CarrierAudit` catches these —
  it demands a *refutation* at a broken sibling oracle, which `True` can never have.
* **HONEST** (`PrivateLeg.honestPrivVerifier`, retired as a false positive): the proof TYPE is
  `Σ pl, PLift (PrivLegHolds …)`, so the witness is structurally present and extraction is free *by
  construction*; the real content is in `verify_sound`, which is **proved**.

The checkable test: **is the carrier discharging work, or recording that there is none?**

## ⚑ THE FOLD DICHOTOMY IS CLOSED — and it named the next blocker exactly

`∀ S` proved farness survives for a **fold-consistent** prover; the canary proved the complement is
where a prover wins with probability **1**. So the quantifier was *decorative*. Now the complement is
priced and `strategy_soundness_compose` has **no consistency gate in its statement**.

**The shaping finding, a theorem not a remark:** *exact consistency is not spot-checkable.* The gate is
an **equality**, so its negation gives **one** disagreeing point, while the query bound pays only above
`δ·|ι|` points — at the exact gate the payment is **nothing**. A fact about the **protocol**. Hence the
graded gate (`FoldCloseAlong`, definitionally the exact one at `d = 0`).

**The blocker, located precisely:** not the tower — `FriSetupTower` landed that — but its **radius**.
*Every landed schedule runs at `d = 0`*, so the margin in `goodδ_card_lt` is zero and `ChainStepGap` has
no positive-radius instance. Note `FriPositiveRadiusPayment` already found positive-radius farness
**uninhabited** at `|L| = 16`, so this must be attempted at the `2^19` tower, not the toy instance.

**Ceiling, unchanged:** this is a ROM/FS statement about an **unbound word-committing** prover. The
commitment is not tied to a Merkle root, so nothing stops a prover answering different queries from
different words. It discharges **no** part of the FRI/STARK floor.


## ⚑ BLOCKED ON EMBER — one deploy decision

Deleting `wide_value_binding.rs`'s AIR half is **not** blocked by any proof gap: the whole AIR is
authored in Lean, byte-pinned, and **every emitted constraint carries a proven theorem**. What blocks it
is that the deployed sidecar rides `prove_dsl_zk` on a **v1 `DslCircuit`** with no IR-2 → v1 lowering, so
routing it through the Lean descriptor changes the **proof bytes on the Turn wire**
(`turn/src/action.rs:995`, `turn-prover/src/shielded_transfer_verifier.rs`). Hiding is *not* lost —
`Plonky3HidingFriReference` is an existing hiding IR-v2 backend. Asked; proceeding on everything else.

## ⚑ DELETION IN FLIGHT — every blocker cleared

`param-compose`'s 1028-line Rust AIR: **production path off it and type-verified (8/8 checks green)**,
**all 16 corpus shapes byte-pinned** in Lean (181 `#guard`s), **resolver landed** reaching all 18. The
lane now running migrates the corpus, deletes `air.rs` + `builder.rs`, and drops the two law-1 BASELINE
rows in the same change.

Three traps handed to it rather than left to be rediscovered — the sharpest being that **pinning a shape
broke the test that used its unpinnedness as a witness** (`an_unpinned_shape_is_refused_rather_than_faked`
had `n3p4l3k2` as its witness; now moved to `i27`). A negative test whose witness becomes positive under
you is not a bug in either half.

## Boundary campaign — landed today

- **CI ran ZERO tests for five days** and nobody noticed: red was the *steady state* (60 runs → **0
  success**, 16 failure, 43 cancelled). Route restored, ratchet widened to the whole workspace, and
  `scripts/check-gates-executed.py` now **parses libtest output** so "did not run" (exit 1) is distinct
  from "ran and failed" (exit 3). Demonstrated red on 8 poles including *the incident verbatim*.
- **`param-compose`**: whole AIR authored in Lean; production path rewired off it and **type-verified**.
  1028 lines dead to production. Delete waits on Lean shape pins (lane running).
- **`wide_value_binding`**: whole AIR in Lean. `legacy_join_cannot_separate_aliases` proves the one-felt
  join is blind to a `v` / `v+p` alias pair **with no crypto and no hypotheses** — the felt-width wound,
  proved not argued. Floor scoped by checking pigeonhole *first* (whole-opening injectivity would be
  ~345 bits into ~248, i.e. false).
- **`delegAdmit`**: one Lean `def`, `@[export]`ed, three Rust copies deleted, wasm handled as a
  **fail-closed refusal** rather than a fallback that would re-grow the twin. Lean half committed and
  verified to `nm -g`; Rust half held pending type-check.
- **135 lines of Rust deleted**, including a **second un-gated copy of the conservation decision** in the
  proof-bundle leg — the twin whose own doc records it once drifted into the asset-blind inflation bug.
- **Zero live soundness holes** in the four red forgery teeth: all three bit; the harness couldn't
  *observe* the refusal because p3 panics before `Err` is reachable.
- **I retracted a wrong correction**: I compared a *past CI run* to a *present tree*. Recorded in the
  wound doc, since that doc exists to stop exactly that reasoning.

## Done log
- **`∀ S` — the fold chain is de-honested** (`7f655b5c55`). Every survival theorem instantiated
  `Strategy := honestStrategy`; now generalized under a path-local fold-consistency gate, with
  `honest_foldConsistentAlong` proving nothing is lost and the existing statements becoming one-line
  instances. The **canary** is the point: `consistencyFreeSurvival_false` *refutes* the ungated
  statement, and at the **same instance** with the gate restored the bound is `≤ 0`. One instance, both
  signs. Honest scope in all four headers: this is strategy-quantification, **not** prover soundness.
- **A RED module at HEAD leaking `sorryAx` into 3 keystones** (`7abd7f6dbf`) — two lanes had written it
  off as contention; it wasn't. `maxRecDepth` was *masking* the real fault: `noteSpendV3` had grown a
  third map op and the `rfl`-fed shape lemma still passed two. Fixing it also unblocked the kernel/config
  receipts that had been stranded unverified behind it.
- **The R11 repair BIT a real victim** (`d59290c4d1`): `StripeAttest` was discharging
  `DecoVerifierKernel.extractable` with `trivial : True` — which only typechecked *because* the carrier
  was `True`. RED at HEAD, leaking `sorryAx` into a pinned keystone. Fixed with the real proof, not by
  restoring `trivial`. **Second** RED-at-HEAD `sorryAx` leak found today.
- **Duplication killed** (`672c169a31`) — `hitWin`/`hit_cond`/`hit_bound` deduped by measured closures
  (51 vs 295 modules), 661→538 lines, all four consumers build **unedited**.
- L0–L6 correlated-agreement ladder landed; crux `polishchuk_spielman` PROVEN (Cramér–Nardi-fixed).
  No Mathlib gap blocked it — the `resultant` API carried it, refuting the plan's own fragility §.
- `DecimLift` discharged from the landed tower; `RlcDistributes` discharged at deployed params.
- Apex premise vacuity **PROVED**; repair pattern + `PremiseInhabitability` instrument built.
- `docs/WOUND-apex-premise-vacuity-2026-07-24.md` — wound proved, replacement path built.
- **CENSUS corrected**: 392 occurrences / 35 files, not the doc's "~35 consumers" (prose conflated with
  code). By binder position: bare `FriLdtExtract` 8 — *all vacuity-subjects*; `Cons` 47 migrated;
  `V3` 14 with 8 genuine consumers still empty; `V3Cons/Faithful` 7 migrated.
- **Bare-premise cutover COMPLETE** (`756efedb01`, `fb741c815f`) — zero soundness consumers left on it,
  verified by grepping binder positions myself. Found + migrated an **orphan fan-out**
  (`AlgoStarkSoundFanoutSetField`) the campaign inventory never listed.
- **The subtle find**: `decodedLdtLink_of_friLdtExtract` was the ONLY entry into `DecodedLdtLink`, and
  composing `_imp_cons` downstream would NOT have repaired it — *composing after an empty premise leaves
  the entry empty*. Deleted; cons-shaped entry written. This is why a cutover ≠ adding a variant beside.
- **Non-emptiness went past the bar**: `..._noOodShape` derives the conclusion from a premise mentioning
  no OOD conjunct *at all* — a premise cannot be emptied by a conjunct it does not contain.
- **Caveat promoted to theorem, not inherited quietly**: an accepting run with `tableOpenings = []`
  refutes the corrected premise. So the cutover trades a premise empty *everywhere* for one whose
  emptiness is *conditional and undecided* at the opaque `cfg*` args — an improvement, **not a closure**.
  And the exhibited pole is `Nat`-typed while the premises are `ℤ`-typed: what is refuted is the
  **schema**, not the deployed instance.
- **The instrument SWEPT the tree** (`PremiseInhabitabilitySweep`, 37 theorems, green): enumeration
  *mechanical* (39 structural candidates + 13 the filter missed), every candidate with a recorded
  verdict. Settled `StarkComplete` (collapses), `GroundedApex.BindingExtract` (**free** — zero
  information), `AccumulatorSound` (**negative at deployment**, correcting the earlier pass: *a verdict
  about an abstract class is not a verdict about its instantiation*).
- **⚑ R11 — a new wound class nobody was looking for**: 13 classes gate extraction on a self-chosen
  `extractable : Prop` and **all eight** reference instances set it to `True`. Two *independent* vacuity
  modes proved — one of which the instrument **structurally cannot see**, since it isn't about
  acceptance at all. `PortalFloor` is the same tree doing it right, so this is a **default**, not an
  accident.
- **`TranscriptWordCommitment` given content** — and *characterized*: supplying an extractor ⟺ proving
  transcript-binding. Non-triviality by **unsatisfiability** (excluded middle is never unsatisfiable),
  with the empty shape retained under an honest name and its emptiness proved.
- **Rooted the subtree via one aggregator** (`ProofAssurance.lean`) after individual import lines were
  dropped by contending commits *again* — second time that lesson was paid for.
