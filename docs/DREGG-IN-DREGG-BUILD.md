# DREGG-IN-DREGG — the self-settlement effect: design + first slice

*Companion to `docs/DREGG-IN-DREGG-SCOPE.md` (the have-vs-new survey). ⚑ **Read §3 and §5 first —
both were re-measured on 2026-07-28 and §3's original "remaining step" turned out not to exist.**
That doc established that
dregg already has the recursion primitive, the IVC accumulator, the base case, and a Lean-proven
gap-free composition — and that what is missing is the Zeko-style **self-settlement loop**. This doc
is the design of that loop's effect and the record of the FIRST SLICE, which is Lean only.*

**Substrate, said out loud (HOUSE LAW #1): this is Lean-authored.** The settlement's verification
predicate is authored in Lean (`metatheory/Dregg2/Distributed/SelfSettlement.lean`). No Rust AIR was
written or extended for it. The constraint set a prover will eventually run is to be **emitted from
Lean** (a descriptor under `metatheory/Dregg2/Circuit/Emit/`, reusing `ivc_turn_chain`'s in-circuit
recursion verifier as the gadget); Rust will only call the emitted artifact. **That emit is step 2
below and is NOT done.**

---

## 1. What landed (the slice) — and what it is not

> **Provenance (the commit trail is split — read this before `git log`).** The slice's content landed
> in `ce6da9766` (first version, swept in by a concurrent lane's broad commit while this lane's files
> were staged) and `e9a6605d5` (this lane's floor-ratchet fix). **Both carry another lane's commit
> subject** — that lane's message file overwrote this one's in a shared scratchpad between write and
> commit. Neither commit was amended: HEAD had already moved, and rewriting history in a tree with
> concurrent lanes is not safe. So the subject line above those two commits is wrong; this doc is the
> findable record of what they contain.

**Landed:** `metatheory/Dregg2/Distributed/SelfSettlement.lean`, green on hbox
(`scripts/hbuild eth-lc-air 'cd metatheory && lake build Dregg2.Distributed.SelfSettlement'`),
**20** keystones pinned with `#assert_axioms` (⊆ {`propext`, `Classical.choice`, `Quot.sound`}), no
`sorry`, no `native_decide`. **[CORRECTED 2026-07-27 — this said 21.]** There are exactly 20
`theorem`s and 20 pins; the 21st grep hit was prose at `SelfSettlement.lean:103`. Coverage is
otherwise complete and 1:1 — no headline theorem is unpinned (audit F-B3, §2.2).

> **[ADDED 2026-07-27 — how this shipped, which the original text did not say.]** The module landed
> in `ce6da9766` imported by **nothing**: not in `metatheory/Dregg2.lean`, not in
> `scripts/lean-orphans-allow.txt`, not in `AXIOM_GUARD_TARGETS`. The repo's own gate reported
> `check-lean-orphans: FAIL — 2 Dregg2 module(s) are reachable from NOTHING`. The line above claiming
> `#assert_axioms`-clean *"Verified with `lake build Dregg2.Distributed.SelfSettlement`"* was true —
> **and that hand-typed command was the only thing that ever compiled it**, so all 20 pins ran in no
> CI target. Repaired by a concurrent lane at `e61619e06` (`Dregg2.Claims` imports `Dregg2`, and CI
> runs `lake build Dregg2.Claims`), so the pins now elaborate in a real target. **Residual: still
> absent from the stricter `AXIOM_GUARD_TARGETS`.** Also **[UNVERIFIED]**: whether the orphan gate's
> red ever *blocked* anything — `main` is not branch-protected here, so in practice it reported.
> (audit F-B1, §6.5.)

**NOT landed — there is no working L2.** Nothing executes, nothing is emitted, no Rust calls this,
no descriptor exists, no account cell is persisted. This slice is the effect's *semantics and its
acceptance predicate*, proved to deliver the L2-commitment binding. Everything in §5 is remaining.

> **[UPDATED 2026-07-28.]** Two of those clauses are now false and the rest are not. **A descriptor
> DOES exist** — `Dregg2/Circuit/Emit/SelfSettlementEmit.lean`, Lean-authored and byte-pinned (§6) —
> and the **height register is now proof-bound** (§3, which also records that the "residual" it named
> never existed). Still true, and still the whole gap: **nothing executes**, no Rust calls this, no
> account cell is persisted. §5 is re-measured accordingly.
>
> **[SUPERSEDED, SAME DAY, later pass.]** Two more of those clauses have since become false. **The
> account cell EXISTS** (`Dregg2/Distributed/RollupAccountCell.lean`) and **the settlement's account
> write EXECUTES** on the shipped `execFullTurnA`, with the registered-genesis pin, the Nomad law
> and the settler authorization enforced by the executor's slot-caveat gate — §5.4. What does not
> execute is the **verification leg**: no turn can be made to refuse a settlement whose child proof
> does not verify, and no Rust resolves `dregg-self-settlement-v1`. §5.1 re-prices that.

### The objects

| Name | What it is |
|---|---|
| `RollupAccount` | The dregg-L1 account: `childId`, **`childGenesis`** (the child chain's *cryptographic* identity), `latestRoot : Option ℤ`, `latestHeight`. The native mirror of `chain/contracts/DreggPeerRegistry.sol`'s `_latestRoot`/`_latestHeight`. |
| `SettleChildChain` | The effect payload: the child's `Aggregate Proof` (= `WholeChainProof`), its `FinalityCert`, the shown finalized root, the claimed height. |
| `SettleAccepts` | The **verification predicate** — seven legs (below). |
| `applySettle` | The account write: commit the child root, advance the height. The only writer. |
| `SettleReceipt` / `emitReceipt` | The receipt the parent turn leaves (`DreggPeerRegistry`'s `PeerFinalityProven`). |

### The verification predicate (`SettleAccepts`)

Legs 1–4 are **exactly** the hypotheses of the already-proven
`FinalizedLightClient.light_client_accepts_finalized_history`:

1. `engine` — `RecursiveAggregation.EngineSound` for the child aggregate (the named native-BabyBear
   in-circuit recursion boundary);
2. `root_ok` — `verify childAgg.root = true` (one succinct verify, re-witnessing nothing);
3. `bound` — the root seam: aggregate root = cert root = shown root;
4. `cert_ok` — `CertValid`: a genuine super-ratification quorum under the node's real
   `ordering.rs::tau` rule.

Three added by the account model:

5. `genesis_ok` — the child aggregate's public genesis root **is the account's registered
   `childGenesis`**;
6. `height_is_count` — the claimed height is the aggregate's public `numTurns` (**proof-backed
   since 2026-07-28** — §3; it was advisory, and the register was griefable);
7. `monotone` — the height strictly advances.

### The theorems

- `settle_attests_finalized_child` — accepting a settlement yields `FinalizedHistoryAttested` for the
  child: every child turn executed, the chain is ordered, the endpoint is the genuine fold, and that
  root was quorum-finalized. The parent re-executes nothing.
- **`settled_root_is_child_final_fold`** and **`receipt_root_is_child_final_fold`** — *the
  L2-commitment binding lemma*, account side and receipt side: the root the L1 now holds (and the root
  in the parent turn's receipt) **is** `foldedFinalRoot … g steps`, the genuine fold of the child's
  whole history. One field element on the L1 commits to the entire child chain.
- `settlement_root_is_unique` — two accepted settlements of the same child history commit the *same*
  root, whatever accounts/certs/heights they carry (anti-equivocation).
- `settle_starts_at_registered_genesis` — the registered `childGenesis` *is* the first step's
  pre-root, via `AggregateAttests.genesis_pinned`. The account is not merely *told* which chain it
  settled.
- `settle_conserves_child_producer_witness` — conservation over the child's history from an
  executor-genuine `StateChained` witness. This is the *weak* form and is labelled as such; the strong
  one is refused, see §3b.
- `settle_advances_monotone`, `settled_account_proves_root`, `settle_preserves_registration`.
- Teeth (all refusals): `stale_settlement_rejected` (replay), `forged_anchor_cannot_settle`
  (non-leader anchor), `root_mismatch_cannot_settle` (proof of A + cert for B),
  **`fabricated_genesis_cannot_settle`** (a freshly fabricated child chain cannot settle into a
  registered account), `unset_account_proves_nothing` (the Nomad law, absent by construction via
  `Option`).
- Non-vacuity: `settle_fires_on_real_child` fires the predicate on `RecursiveAggregation`'s realizing
  child chain + `FinalizedLightClient`'s `trace3` finality cert (with the two executable `#guard`s over
  the node's real finality rule), and `real_settlement_binds_child_fold` / `real_settlement_advances`
  fire the binding and the advance on it.

---

## 2. What reuses the proven recursion (and what it deliberately avoids)

The settlement does **not** re-derive any recursion soundness. Legs 1–4 are passed verbatim into
`light_client_accepts_finalized_history`, so the effect inherits:

- `metatheory/Dregg2/Circuit/RecursiveAggregation.lean` — `light_client_verifies_whole_history` (one verify ⇒ the whole
  child history executed, ordered, genuine fold), and the fact that
  `recursive_sound` is *derived* whole-tree by `RecursiveSoundFromNodes.lean`;
- `Distributed/FinalizedLightClient.lean` — the third (quorum/`tau`) leg and its teeth.

> **[CORRECTED 2026-07-27 — `conserves_from_verification` was listed here and is NOT inherited.]**
> This list claimed the effect inherits `conserves_from_verification`. It does not: **§3b of this same
> document says that leg was written and then REMOVED**, because it rides
> `compressInjective`/`cellLeafInjective` — floors this tree proves **FALSE** at deployed BabyBear
> width. `SelfSettlement.lean:80` carries the same leftover, still listing "the verification-derived
> conservation" among what the slice authors, contradicting §7 of its own file. Both are leftovers
> from a pre-removal draft. (audit F-B4. The `.lean` line is **not** fixed by this pass — this pass is
> docs-only — so `SelfSettlement.lean:80` remains wrong and is flagged here.)

> **[ADDED 2026-07-27 — read the non-vacuity witness at its real resolution.]** The commit and this
> document present `settle_fires_on_real_child` (`SelfSettlement.lean:535`) as non-vacuity "fired on
> the realizing child chain." It fires at the `zCH/zRH/zcmb/zcompress/zcompressN` portal
> (`RecursiveAggregation.lean:429-433`), **all of which are constant zero** — machine-confirmed by
> `rfl`: `foldedFinalRoot zCH … g steps = 0`, `realAccount.childGenesis = 0`,
> `(applySettle RealProof realAccount realSettle).latestRoot = some 0`. So
> `real_settlement_binds_child_fold` has the content **`some 0 = some 0`**;
> `fabricated_genesis_cannot_settle`'s discriminator is constant (`genesis_ok := rfl` is `0 = 0`, not
> a check passing); and **not one of the five teeth is instantiated on the realizing instance.** The
> abstract `settled_root_is_child_final_fold` **is** genuinely quantified and real — but the tree
> exhibits **no instance in which the equation is non-trivial.** Inherited from
> `RecursiveAggregation`, not introduced here (whose `:511` at least exhibits refutation at
> `genesisRoot + 1`), but the claim must be read at that resolution. (audit F-B2.)

> **[ADDED 2026-07-27 — two theorem descriptions over-read their own statements (audit F-B5).]**
> `SelfSettlement.lean:41-42` calls `settle_conserves_child_producer_witness` *"the parent **inherits**
> child value-conservation"* — the statement mentions no parent, no settlement and no account; it is
> `finalized_history_conserves` under a new name. `SelfSettlement.lean:39-40` calls
> `settlement_root_is_unique` *"the anti-equivocation edge … a prover cannot present one child chain
> to two parents"* — both settlements are quantified over the **same** `g` and `steps`, so the
> interesting case (one aggregate, two claimed histories) is **not excluded**, and `g`/`steps` are
> ghost parameters the parent never sees (the file says so at `:173`). Both are `.lean` doc comments
> and are **not** fixed by this docs-only pass; they are flagged here so this document does not repeat
> them. The best theorem in the scope is untouched by any of this and worth naming:
> `engineSound_numTurns_irrelevant`, an honestly-stated **negative** result (the settled height is
> provably not engine-pinned) lifted to a demonstrated griefing attack by
> `settle_accepts_inflated_height`. **[SUPERSEDED 2026-07-28 — both are DELETED; §3 has the repair.
> The negative was true of the MODEL and false of the deployed AIR, which had pinned the count all
> along. The best theorem in the scope is now the tooth that replaced it,
> `inflated_height_cannot_settle`.]**

The residual crypto floor is therefore **unchanged and named**: the per-node in-circuit FRI recursion
verifier of the plonky3 recursion fork (native BabyBear). Nothing app-specific was added to it.

**The wrap is deliberately not used.** Self-settlement recurses through the native BabyBear engine, not
the cross-field STARK→BN254→Groth16 gnark wrap, whose `FriLowDegreeSound` carrier is proven vacuous
(`FriCarrierVacuity.lean`; ~31-bit deployed query ceiling, `FriCarrierEpsilon.lean`). The wrap remains
the *external-EVM* path only. This is the scope doc's §5 constraint, honoured.

---

## 3. ⚑ RESOLVED 2026-07-28 — the height register IS pinned, and the residual named here never existed

**What this section used to say.** `Aggregate.numTurns` appears in no leg of `EngineSound`;
`engineSound_numTurns_irrelevant` proves it by transporting any witness across an arbitrary count;
`settle_accepts_inflated_height` lifts that to a griefing attack; **remaining step: pin `numTurns` to
the leaf count in the chain-binding AIR.**

**That remaining step did not exist.** The AIR has pinned the count since it was emitted. Constraint
14 of `metatheory/Dregg2/Circuit/Emit/EffectVmEmitTurnChainBinding.lean` is
`real_count[last] = pi[num_turns]` (`lastRealCountBind`, `PI_NUM_TURNS = 2`), it is inside the
byte-golden `TURN_CHAIN_BINDING_GOLDEN`, and `firstRealCount` / `realCountAccum` / `realMonotone`
make `real_count` the genuine count of real rows. `BindingAirSound.Satisfies.count` is the model of
exactly that constraint, and it has always been a field of the keystone's hypothesis.

**The leak was one layer up, and it was a leak of something already in hand.**
`binding_air_discharges_binding_sound` took `Satisfies` — `count` field and all — and concluded
THREE of the four facts it could. So `EngineSound.binding_sound` had no slot for the count,
`Aggregate.numTurns` reached every downstream client as an unconstrained public register, and the
settlement's `height_is_count` leg tied a claimed height to a free number. Fixing it cost no crypto:
`Satisfies.count` plus a new structural `represents_length`.

### What changed shape (rebuild, do not migrate — nothing holds the old shape)

| object | change |
|---|---|
| `EngineSound.binding_sound` | fourth conjunct `agg.numTurns = steps.length` |
| `AggregateAttests` | new field `turns_pinned` (one construction site in the tree) |
| `GroundedApex.BindingExtract` | new conjunct `agg.numTurns = pub.numTurns` — `numTurns` is a public input of the same AIR and was the only one of the four the extraction did not re-export |
| `binding_air_discharges_binding_sound` | fourth conclusion `pub.numTurns = steps.length` |
| pass-through hypotheses restating `binding_sound` | widened in `RecursiveSoundFromNodes`, `WitnessRealizing`, `EngineSoundOfApex` (x3) |

**DELETED, not kept alongside:** `engineSound_numTurns_irrelevant` (now FALSE),
`settle_accepts_inflated_height`, `inflated_height_commits_same_root`.

**What replaces them, saying the opposite:** `settle_height_is_child_turn_count`,
`settled_account_height_is_child_turn_count`, `inflated_height_cannot_settle` (the tooth),
`settlement_height_is_unique`, `replayed_settlement_cannot_advance` — a child chain can no longer be
settled twice into one account, because advancing now requires the CHILD to advance rather than a
number to be inflated.

**The lesson, since it is the second time this shape has cost something here:** the instrument that
would have caught this is not an axiom check and not a vacuity sweep. It is asking, of every
discharge lemma, *does its conclusion use everything its hypothesis gives it?* `Satisfies.count` sat
unread in a keystone for as long as the keystone existed, and every gate in the tree was green over it.

---

## 3b. ⚑ The conservation leg the L1 cannot yet have — a refused import

The settlement *should* let the parent derive child value-conservation from its own crypto legs
(`engine` + `root_ok`), with no prover-supplied `StateChained`. That form was written, riding
`RecursiveAggregation.conserves_from_verification` — and the tree's own floor ratchet rejected it:

```
theorem settle_conserves_child_from_verification
  carries: cellLeafInjective, compressInjective, compressNInjective
```

Those are floors this tree **proves false** at deployed BabyBear parameters. A settlement-level
restatement under them would be vacuously true at deployment — it would tell an operator nothing about
the shipping system. The theorem was therefore **removed, not recorded as a new floor carrier** (adding
a carrier is a deliberate, reviewable decision and belongs to the operator, not to a build lane).

What ships instead is the honest producer-witness form, explicitly labelled as consuming a witness
rather than the settlement. **Remaining step: the `_or_collides` + total-extractor port of
`conserves_from_verification`** — until then, an L1 settling a child inherits the child's *correctness,
ordering, genuine fold and finality* from verification, but **not** its conservation.

---

## 4. Zeko, concretely

| Ingredient | Zeko / Mina | dregg |
|---|---|---|
| Recursion primitive | Pickles, in-circuit | `ivc_turn_chain` native BabyBear in-circuit FRI recursion — **live, node-wired** |
| Soundness of the recursion composition | **Not machine-checked** | `RecursiveAggregation` + `RecursiveSoundFromNodes`, `#assert_axioms`-clean; the residual is the per-node FRI floor only |
| Finality leg (accept only a *finalized* root) | inherited from Mina consensus | `FinalizedLightClient` — the node's real `tau` super-ratification, with refusal teeth |
| Unbounded accumulator | Pickles, perpetual | induction **proven** (`accumulate_preserves_wellformed`); the O(1)-memory driver is **unbuilt** |
| L2 state commitment on an L1 **account** | zkApp account on Mina L1 — **built, in production** | **a real cell, advanced by a real turn** (2026-07-28): `RollupAccountCell.lean`, 5 of a `Value`'s 8 field slots, written by `setFieldA` through `execFullTurnA`, genesis pin + Nomad law executor-enforced as slot caveats, decoded back to the proved `RollupAccount` by `readAccount_settle_is_applySettle` — §5.4 |
| Settlement effect verifying the child proof | zkApp method | `SettleAccepts` proved, **and since 2026-07-28 EMITTED** as a Lean-authored byte-golden descriptor (§6). Still no executor threading, and nothing in Rust resolves it. |
| Settled HEIGHT bound to the proof | Mina's account update is protocol-enforced | **bound since 2026-07-28** (§3). It was a griefable advisory register, and the AIR that fixes it had been emitting the constraint the whole time. |
| Deposits / withdrawals binding the commitment | built | **not built** (`metatheory/Dregg2/Bridge/HoldingFoldRecursive.lean` is the reusable holdings leg) |

**What dregg has that Zeko does not.** The recursion-to-light-client composition is a
machine-checked theorem (`RecursiveAggregation` + `RecursiveSoundFromNodes`, `#assert_axioms`-clean,
the recursion leg DERIVED not carried), the finality leg is checked against the node's real `tau`
rule with refusal teeth, and — as of this pass — the settlement's constraint set is *authored in
Lean with machine-checked forcing lemmas over the emitted object*, not hand-written in the prover's
host language. Pickles' recursion soundness and Zeko's settlement circuit are neither
machine-checked nor emitted from a proof assistant. **At the composition layer a dregg recursive
rollup would be more verified than the prior art. That has been true for a while and is not what is
missing.**

**What Zeko has that dregg does not: a working L2 — and the gap is now ONE leg, not the whole loop.**
The account model, the settlement loop, the deposit/withdraw bridge and the perpetual accumulator are
built and running there. Here, after 2026-07-28, the semantics are proved, the height is bound, the
constraint set is emitted and byte-pinned, and **the L1 account is a real cell advanced by a real
turn** (§5.4) with the genesis pin and the Nomad law enforced BY THE EXECUTOR. What still cannot run
is the **verification leg**: a turn cannot be made to REFUSE a settlement whose child proof does not
verify, because that gate has to ride on the effect and `SettleChildChain` has no `FullActionA`
constructor; nor does anything in Rust resolve `dregg-self-settlement-v1`. §5.1 measures that
constructor honestly, and it is **not** the additive 30-constructor ripple this document previously
called it — every LIVE constructor is also a per-effect circuit-closure campaign at the deployed
apex, priced from the record at ~2,000 lines across ~6 modules.

**The honest one-line comparison, at current resolution:** dregg's settlement is *better verified
and not running*; Zeko's is *running and not verified*. Nothing in this pass changed which side of
that sentence dregg is on — it moved the descriptor from "named residual" to "emitted and pinned",
which is one of the two things standing between the two halves.

---

## 5. Ordered remaining steps — re-measured 2026-07-28

**Step 3 (pin `numTurns`) is DONE** and turned out not to be an AIR change at all (§3).
**Step 2 (the Lean-authored EMIT) is DONE** — see §6.

1. **Thread the effect into the turn model — ⚑ RE-MEASURED 2026-07-28, and the earlier estimate was
   the wrong SHAPE, not merely the wrong size.**

   What this step used to say: one constructor on
   `Dregg2.Exec.TurnExecutorFull.PerAsset.FullActionA` (`PerAsset.lean:1551`, 30 constructors, 138
   files) plus an `actionTag` / `fullActionStep` / `execFullTurnA` / `dispatchArm` / `Rfix` weld —
   an ADDITIVE ripple, "a new arm at every exhaustive match". And it said two effects were queued
   behind it, citing `Dregg2.lean:1010`'s `setProgramA` residual.

   **`setProgramA` is NOT queued — it already landed.** The constructor exists
   (`PerAsset.lean`), it dispatches (`execFullA` → `stateStep … programField`), it has `actionTag`
   13, a `SetProgramSpec` arm, an `actionAirName`, a deployed registry position
   (`actionTagToPos 13 = 51`, `Rfix 13 = setProgramV3`) and an apex closure
   (`closedLogExtract_setProgram_closed`). **`Dregg2.lean:1010`'s residual line is STALE** and should
   be struck; only ONE effect is queued behind this step, not two.

   **The measured ripple.** A LIVE constructor's ripple is exact and reproducible: `heapWriteA`,
   `refreshDelegationA` and `setProgramA` each have **34 pattern arms across the SAME 18 files**.
   That set is the whole mechanical cost, and ~27 of the 34 arms are mechanical (a tag, a name, a
   target cell, a `[]`-delta, a `subst; rfl`).

   **The other 7 arms are not mechanical, and they are the actual blocker.** Because the apex
   theorems case-split on `FullActionA` (`closedLogExtract_all_genuine_live` is
   `∀ e, LiveTag e → …` proved by `rintro ⟨fa, rfl⟩; cases fa`), a new LIVE constructor is a new
   obligation at the deployed circuit apex. It needs, at minimum:

   * a leaf `Circuit/Spec/*.lean` spec + the `execFullA_… _iff_spec` arm (`ActionDispatch`, x2);
   * a `Circuit/Inst/*.lean` instance AIR + `effectEmitRegistry` entry (`EffectEmitRegistry`);
   * a `settleChildCircuitStep` + `_circuit_refines_spec` (`TurnEffectRefinement`, x2);
   * an emitted encoder + `_emitted_refines_spec` (`TurnEmit`; the `stepEmittedSat` DEF has a
     catch-all, the THEOREM does not);
   * a DEPLOYED descriptor in `v3RegistryHeap` **and** an `actionTagToPos` position — without one,
     `Rfix <newtag>` falls through to `transferDescr`, so any `closedLogExtract_…_closed` at that
     tag would be forced from the TRANSFER AIR, which is a lie;
   * a `RotatedKernelRefinement*` trace readout + a `_closedLog_sat` rung + a new readout field on
     `ClosureReadoutsLive` (`ClosureFanoutGenuine`, `ClosureReadoutsRealizable`);
   * a real handler + the handler↔executor kernel-agreement lemma (`HandlerExecutor`, x2).

   **The price, from the record rather than from estimate.** The last constructor added
   ("THE ROTATION", `heapWriteA`) shipped `Circuit/Inst/heapWriteA.lean` (242 lines) +
   `Circuit/Spec/heapwrite.lean` (194) + its emit and refinement modules; `refreshDelegationA`
   shipped ~1,980 lines across five modules. `git log -S heapWriteA -- metatheory/` is **48
   commits.** So the honest price of one live `FullActionA` constructor in this tree is on the order
   of **2,000+ lines of new circuit Lean across ~6 new modules, plus 34 arms in 18 files** — a
   campaign, not a rider.

   **Two shortcuts exist and BOTH are forbidden by this repo's own doctrine**, recorded here so the
   next lane does not re-derive them: (a) carrying `ClosedLogExtract` for the new tag as a raw field
   instead of a trace readout + rung is assuming the conclusion; (b) defining the
   `fullActionCircuitStep` arm as the spec itself is `hole_circuit_step`, which
   `Circuit/CircuitOpenFronts.lean` names and forbids ("Silent spec-fallback … is forbidden") and
   which the tree closed 20/20.

   **Design fork for the operator, named because the repo has already taken it four times.** dregg3
   F1b DELETED the escrow / obligation / committed-escrow / bridge-L-F-C constructors from
   `FullActionA` and re-landed those families as verified FACTORY CELLS with slot caveats
   (`Apps/{EscrowFactory,ObligationFactory,BridgeCell}.lean`) — precisely because a live constructor
   is a per-effect circuit campaign. Step 4 below is now that route's first half, landed.
2. ~~Emit the verification constraint FROM LEAN.~~ **DONE** — §6.
3. ~~Pin `numTurns`.~~ **DONE** — §3.
4. **NEW-C, the account cell — ⚑ LANDED 2026-07-28, and it WAS independently landable.**
   `metatheory/Dregg2/Distributed/RollupAccountCell.lean`. This step used to say the account cell
   "needs the same `FullActionA` constructor as step 1 — the account cell and the executor threading
   are one piece of work, not two." That was wrong in the direction that mattered: the write is
   `setFieldA`-shaped, and `setFieldA` is **already** fully threaded, deployed and apex-closed, so
   the account runs on the shipped executor today.

   `RollupAccount` occupies **five of a `Value`'s eight developer slots** (`child_id`,
   `child_genesis`, `latest_root`, `latest_root_set`, `latest_height`) — none of them one of the
   four protocol-managed slots, so a developer `setFieldA` may write them. `readAccount` decodes the
   cell back to the *same* `SelfSettlement.RollupAccount` the binding lemma quantifies over
   (`readAccount_settle_is_applySettle`), so composed with `settled_root_is_child_final_fold` the
   field element in a real cell's `latest_root` slot **is** the child's genuine whole-history fold.

   **Three of `SettleAccepts`' seven legs are now EXECUTOR-ENFORCED**, as factory-installed slot
   caveats rather than as hypotheses: `genesis_ok` (`.immutable child_genesis` — the account cannot
   be re-homed, `rollup_genesis_cannot_be_rehomed`, unconditional), the Nomad law (`.monotonic` on
   the presence flag plus a decode that reads a `0` flag as `none` whatever the root slot holds), and
   who may settle (`.senderAuthorized` on the root slot). The settlement's account write RUNS:
   `#guard`s execute `execFullTurnA` on a registered account and read the committed root back out.

   **Two legs are NOT executor-enforced, and this is where step 1 actually bites.** (a) `engine` /
   `root_ok` — a `setFieldA` carries no proof argument, so the executor cannot refuse a settlement
   whose child proof does not verify; that needs a constructor carrying the verification shadow (the
   shape `noteSpendA`'s `spendProof : Bool` already has). (b) `monotone` — the caveat vocabulary has
   `.monotonic` (`old ≤ new`) and `.monotonicSeq` (`new = old + 1`) and **no strict-`<` member**, so a
   REPLAY at the already-settled height is admitted by the caveat gate. That is exhibited, not
   hidden: `rollup_replay_at_same_height_is_admitted` plus a `#guard` that runs it.

   ⚑ **ROOT IMPORT NOT ADDED** (this lane does not edit `metatheory/Dregg2.lean`). Until
   `import Dregg2.Distributed.RollupAccountCell` lands there, the module's 10 `#assert_axioms` pins
   and 16 `#guard`s run in **no CI target** — the same F-B1 shape §1 records twice.

   Deposits/withdrawals binding the commitment (`Dregg2/Bridge/HoldingFoldRecursive.lean`) come
   after.
5. **Port `conserves_from_verification`** off its refuted CR floor (§3b), so a settling L1 can
   inherit child conservation from the proof rather than from a producer witness. Unchanged.
6. **The quorum AIR.** `SettleAccepts.cert_ok` is a genuine super-ratification quorum under
   `BlocklaceFinality.finalLeaderAt`/`isSuperRatified` over a lace. The settlement descriptor (§6)
   deliberately does NOT contain it — it carries the cert's finalized root as a column and binds the
   SEAM only. This was implicit before and is now named because the emit made it visible.
7. **NEW-A, the online fold driver.** Drive `fold_two_turns`
   (`circuit-prove/src/ivc_turn_chain.rs:5678`) as a running fold with the previous running proof
   re-verified in-circuit (O(1) memory), for an unbounded settled child. Soundness is already the
   Lean induction; this is fork/crypto engineering. Optional for a bounded-window rollup.

---

## 6. The EMIT — `Dregg2/Circuit/Emit/SelfSettlementEmit.lean` (landed 2026-07-28)

**Substrate, said out loud (HOUSE LAW #1): Lean-authored.** The constraint set is a `def` producing
an `EffectVmDescriptor2`, byte-pinned as `SELF_SETTLEMENT_GOLDEN` (1996 bytes) by `emitVmJson2`, with
forcing lemmas over the emitted gates. **No Rust AIR was written or extended**; Rust's job is to CALL
the golden, exactly as the eventual cutover for `TURN_CHAIN_BINDING_GOLDEN` does.

`dregg-self-settlement-v1`: 12 main columns, 6 public inputs, 13 constraints — 6 arithmetic
`windowGate`s (`onTransition := false`, because a v2 `.base (.gate …)` is evaluated under
`when_transition()` and would be VACUOUS on the only row of a one-row trace), 6 `.piBinding`s, and
one `.proofBind`. A 32-bit range tooth on the `HEIGHT_SLACK` column makes the strict advance a
genuine `<` rather than a wraparound.

**What it FORCES:** the L1 account write is exactly the child aggregate's published, proof-bound
commitments. No other root, no other height, no re-homing of the registered genesis, no failure to
advance. Rung 1 (`settle_descriptor_refines_air`) and Rung 2 (`settle_descriptor_iff_air`) over the
emitted gates; a canonicity BRIDGE (`settle_row_forces_settle_legs`) delivering `SettleAccepts`'s four
arithmetic legs as ℤ equalities; four UNSAT teeth (fabricated genesis, proof-seam mismatch, cert-seam
mismatch, stale height); and a concrete satisfying row whose equations are `11 = 11` and `29 = 29` —
worth stating plainly, because the abstract non-vacuity witness in `SelfSettlement` is limited to the
constant-zero portal and reads `0 = 0` (audit F-B2).

**What it does NOT force, stated in the module header before any code:**

  * `engine` / `root_ok` — the child aggregate's recursion proof verifying. That is the `.proofBind`
    op, whose row-local `holdsAt` is `True` and whose content is `Satisfied2Custom.proofBound` /
    `proofBind_bound` against the named engine — the SAME native-BabyBear boundary
    `EngineSound.recursive_sound` names, and never the gnark wrap whose `FriLowDegreeSound` carrier
    is proven vacuous.
  * `cert_ok` — the quorum. Not in this descriptor at all (step 6 above).

**⚑ ORPHAN STATUS — CLOSED 2026-07-28.** This section used to record that `SelfSettlementEmit` was
imported by nothing, so its **12 `#assert_axioms` pins ran in NO CI target** (the F-B1 shape that let
`SelfSettlement`'s own 20 pins ship uncompiled), and that `Dregg2.lean`'s `SelfSettlement` annotation
still advertised the deleted `settle_accepts_inflated_height`. **Both are now fixed:**
`metatheory/Dregg2.lean:1544` carries `import Dregg2.Circuit.Emit.SelfSettlementEmit` and `:1545`'s
annotation is rewritten. Verified by building the root on hbox: `lake build Dregg2` compiles both
modules, so all 32 pins elaborate in a real target. The emit is gated.

(That build also fixes the tree's baseline for anyone following: the root is green except for
`#floor_ratchet`, which reports exactly **1** pre-existing violation —
`Emit.AutomataflRevealRefine.not_revealColl_of_hash4NoCollision`. Any lane touching this campaign
should still see 1.)

---

**Step 4 is done. Step 1 is the last thing between "a proven predicate with an emitted descriptor"
and "an effect a turn can run" — and it is a campaign, not a rider.** The honest description of this
work at current resolution:

> the self-settlement effect's Lean semantics, verification predicate, L2-commitment binding lemma,
> height pin and emitted constraint set exist and are proved; **the L1 account is a real cell that a
> real turn advances, with the child's cryptographic identity and the Nomad law enforced by the
> executor**; and the child-proof verification gate does not run, because it has to ride on a
> `FullActionA` constructor and that constructor costs a per-effect circuit-closure campaign at the
> deployed apex (§5.1).

The one-line comparison with Zeko therefore moves, but not all the way: dregg's settlement is *better
verified, with its account running and its verification leg not*; Zeko's is *running and not
verified*.
