# DREGG-IN-DREGG — the self-settlement effect: design + first slice

*Companion to `docs/DREGG-IN-DREGG-SCOPE.md` (the have-vs-new survey). That doc established that
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
6. `height_is_count` — the claimed height is the aggregate's public `numTurns` (**advisory** — §3);
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
> `settle_accepts_inflated_height`.

The residual crypto floor is therefore **unchanged and named**: the per-node in-circuit FRI recursion
verifier of the plonky3 recursion fork (native BabyBear). Nothing app-specific was added to it.

**The wrap is deliberately not used.** Self-settlement recurses through the native BabyBear engine, not
the cross-field STARK→BN254→Groth16 gnark wrap, whose `FriLowDegreeSound` carrier is proven vacuous
(`FriCarrierVacuity.lean`; ~31-bit deployed query ceiling, `FriCarrierEpsilon.lean`). The wrap remains
the *external-EVM* path only. This is the scope doc's §5 constraint, honoured.

---

## 3. ⚑ Measured while building: the height register is not proof-pinned

`Aggregate.numTurns` is a public field that appears in **no leg** of
`RecursiveAggregation.EngineSound` — `binding_sound` pins `genesisRoot` and `finalRoot` only. The slice
*proves* this rather than noting it:

- `engineSound_numTurns_irrelevant` — any `EngineSound` witness transports across an arbitrary
  `numTurns`;
- `settle_accepts_inflated_height` — hence from any accepted settlement, an inflated-height settlement
  of the *same* child history is also accepted;
- `inflated_height_commits_same_root` — and the root committed is **unchanged**.

So the settled height is an advisory, griefable monotone register; the *commitment* is bound. This is
not a defect introduced here — it is a property of the existing aggregate model, surfaced by trying to
build on it. **Remaining step: pin `numTurns` to the leaf count in the chain-binding AIR** (Lean-emitted
constraint work, listed below).

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
| L2 state commitment on an L1 **account** | zkApp account on Mina L1 — **built, in production** | `RollupAccount` **as a Lean model only**; no cell, no persistence |
| Settlement effect verifying the child proof | zkApp method | `SettleAccepts` **as a Lean predicate only**; no descriptor, no executor threading |
| Deposits / withdrawals binding the commitment | built | **not built** (`metatheory/Dregg2/Bridge/HoldingFoldRecursive.lean` is the reusable holdings leg) |

**What dregg has that Zeko does not:** the recursion-to-light-client composition is a machine-checked
theorem, and the finality leg is checked against the node's real rule. A dregg recursive rollup would
be *more verified* at the composition layer.

**What Zeko has that dregg does not:** a working L2. The account model, the settlement loop, the
deposit/withdraw bridge and the perpetual accumulator are all built and running there; here they are a
proven predicate, a proven binding lemma, and the four residuals below.

---

## 5. Ordered remaining steps

1. **Thread the effect into the turn model.** Add `SettleChildChain` to `Dregg2.Exec.Effect` and its
   semantics to the executor (`recCexec` / `execFullTurnA`), following the `SetField` family as the
   write-a-computed-value template. Cheapest real step; makes the effect *exist* in a turn.
2. **Emit the verification constraint FROM LEAN.** A descriptor under `Dregg2/Circuit/Emit/` whose
   gadget is `ivc_turn_chain`'s in-circuit recursion verifier, plus the refinement rung tying the
   emitted object to `SettleAccepts`. **This is the AIR step and it is Lean-authored — do not
   hand-write it in Rust, and do not extend an existing Rust AIR.**
3. **Pin `numTurns`** to the leaf count in the chain-binding AIR (§3), then strengthen
   `height_is_count` from advisory to proof-backed.
4. **NEW-C, the account cell.** Persist `RollupAccount` as a real `RecordKernelState` cell advanced
   only by the effect (registration fixes `childGenesis`), then deposits/withdrawals binding the
   commitment via `metatheory/Dregg2/Bridge/HoldingFoldRecursive.lean`.
5. **Port `conserves_from_verification`** off its refuted CR floor (§3b), so a settling L1 can inherit
   child conservation from the proof rather than from a producer witness.
6. **NEW-A, the online fold driver.** Drive `fold_two_turns`
   (`circuit-prove/src/ivc_turn_chain.rs:5678`) as a running fold with the previous running proof
   re-verified in-circuit (O(1) memory), for an unbounded settled child. Soundness is already the Lean
   induction; this is fork/crypto engineering. Optional for a bounded-window rollup.

Steps 1–2 are what turn "a proven predicate" into "an effect a turn can run". Until then, the honest
description of this work is: **the self-settlement effect's Lean semantics, verification predicate and
L2-commitment binding lemma exist and are proved; the loop does not run.**
