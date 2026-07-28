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

**Landed:** `metatheory/Dregg2/Distributed/SelfSettlement.lean`, green on hbox
(`scripts/hbuild eth-lc-air 'cd metatheory && lake build Dregg2.Distributed.SelfSettlement'`),
21 keystones pinned with `#assert_axioms` (⊆ {`propext`, `Classical.choice`, `Quot.sound`}), no
`sorry`, no `native_decide`.

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
- `settle_conserves_child_from_verification` — the parent inherits child value-conservation **from the
  settlement's own legs** (`h.engine` + `h.root_ok`), through
  `RecursiveAggregation.conserves_from_verification`, with **no** prover-supplied `StateChained`.
  (`settle_conserves_child_producer_witness` is the weaker alternate route, labelled as such.)
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

- `Circuit/RecursiveAggregation.lean` — `light_client_verifies_whole_history` (one verify ⇒ the whole
  child history executed, ordered, genuine fold), `conserves_from_verification`, and the fact that
  `recursive_sound` is *derived* whole-tree by `RecursiveSoundFromNodes.lean`;
- `Distributed/FinalizedLightClient.lean` — the third (quorum/`tau`) leg and its teeth.

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

## 4. Zeko, concretely

| Ingredient | Zeko / Mina | dregg |
|---|---|---|
| Recursion primitive | Pickles, in-circuit | `ivc_turn_chain` native BabyBear in-circuit FRI recursion — **live, node-wired** |
| Soundness of the recursion composition | **Not machine-checked** | `RecursiveAggregation` + `RecursiveSoundFromNodes`, `#assert_axioms`-clean; the residual is the per-node FRI floor only |
| Finality leg (accept only a *finalized* root) | inherited from Mina consensus | `FinalizedLightClient` — the node's real `tau` super-ratification, with refusal teeth |
| Unbounded accumulator | Pickles, perpetual | induction **proven** (`accumulate_preserves_wellformed`); the O(1)-memory driver is **unbuilt** |
| L2 state commitment on an L1 **account** | zkApp account on Mina L1 — **built, in production** | `RollupAccount` **as a Lean model only**; no cell, no persistence |
| Settlement effect verifying the child proof | zkApp method | `SettleAccepts` **as a Lean predicate only**; no descriptor, no executor threading |
| Deposits / withdrawals binding the commitment | built | **not built** (`Bridge/HoldingFoldRecursive.lean` is the reusable holdings leg) |

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
   commitment via `Bridge/HoldingFoldRecursive.lean`.
5. **NEW-A, the online fold driver.** Drive `fold_two_turns`
   (`circuit-prove/src/ivc_turn_chain.rs:5678`) as a running fold with the previous running proof
   re-verified in-circuit (O(1) memory), for an unbounded settled child. Soundness is already the Lean
   induction; this is fork/crypto engineering. Optional for a bounded-window rollup.

Steps 1–2 are what turn "a proven predicate" into "an effect a turn can run". Until then, the honest
description of this work is: **the self-settlement effect's Lean semantics, verification predicate and
L2-commitment binding lemma exist and are proved; the loop does not run.**
