# DREGG-IN-DREGG — recursive self-verification: have-vs-new scope

*A source-grounded assessment of whether dregg already has the ingredients for a
recursive self-verifying dregg (a dregg proof verifying a prior dregg proof), the
way Zeko builds a recursive L2 on Mina. Read-only survey + this doc; every claim
pins a file:line in the tree at the time of writing.*

**One-line verdict.** The hard cryptographic core — **a dregg STARK verifying a
dregg STARK in-circuit, folded over a whole chain, Lean-proven gap-free above the
FRI floor, and wired live into the node** — already EXISTS as real code, not a
sketch. What a full Zeko-style *dregg-L2-recursively-settling-onto-a-dregg-L1* would
add is a **focused assembly**, not a from-scratch build: a dregg-native settlement
*effect* that verifies a child proof inside a turn, an L2-state-commitment-on-an-L1
account model, and (for unboundedness) the online fold driver. ember's intuition —
"we pretty much already have the ingredients" — is **correct for the recursion
primitive and the accumulator; not yet correct for the self-settlement loop.**

---

## 0. What "dregg-in-dregg" means, and the Zeko yardstick

Zeko is a Mina L2 that is a *recursive rollup*: its state is a zkApp account on Mina
L1; each L2 block produces a recursive SNARK (Pickles) attesting the L2 state
transition; the running proof is folded so the L1 account can verify the *whole* L2
history in constant work; and because the L1 verifier is *itself a Mina proof*, Mina
verifies Mina — the rollup settles to the same proof system it is built from.

Decomposed into ingredients, a recursive self-verifying system needs:

1. **A recursion primitive** — a proof that verifies another proof *in-circuit*.
2. **An IVC / accumulator** — fold N step-proofs into ONE running proof, constant
   verify cost, ideally O(1) prover memory (unbounded).
3. **A base case** — a genesis the fold starts from and pins.
4. **An L1 that verifies the L2's proof natively and holds its state commitment** —
   the "settle to itself" account model.
5. **The recursion threading** — the L1's own verification is expressed *in the same
   system*, and deposits/withdrawals bind the L2 commitment.

The rest of this doc maps each ingredient to what dregg HAS and what a full
dregg-in-dregg would NEED.

---

## 1. HAVE — the recursion primitive (STARK-verifies-STARK in-circuit) is REAL and LIVE

This is the load-bearing "yes." dregg does genuine **in-circuit FRI recursion**, not
a hash-chain summary.

| Piece | File:line | State |
|---|---|---|
| Whole-chain recursive fold (prover) | `circuit-prove/src/ivc_turn_chain.rs:2226` `prove_turn_chain_recursive` | ALIVE-WIRED |
| Whole-chain recursive verify | `circuit-prove/src/ivc_turn_chain.rs:5447` `verify_turn_chain_recursive` | ALIVE-WIRED |
| The succinct aggregate object | `circuit-prove/src/ivc_turn_chain.rs:1867` `struct WholeChainProof` (`genesis_root`, `final_root`, `chain_digest`, `num_turns`) | ALIVE-WIRED |
| The recursion engine | `p3_recursion::{BatchOnly, build_and_prove_next_layer, into_recursion_input_pinned}` (imported `ivc_turn_chain.rs:224`) | plonky3 **recursion fork** — genuine in-circuit FRI verifier |
| Live node consumer | `node/src/mcp/handlers_verify.rs:159` (`tool_compress_history` → `prove_turn_chain_recursive`) | ALIVE-WIRED |
| Live retention seam | `node/src/blocklace_sync.rs:8050`, `node/src/turn_proving.rs:1695` (`mint_and_encode_finalized_turn`), seam test `node/tests/retained_history_ivc_seam.rs` | ALIVE-WIRED |
| Light-client consumer | `lightclient/src/lib.rs:201` `verify_history` (cost independent of N) | ALIVE-WIRED |

**What the leaf actually is (the recursion is real, not a digest).** Each finalized
turn's leaf is the **real Lean-descriptor turn circuit** (`transferVmDescriptor2R24`
&c on `participant.rotated`) re-proven recursion-compatibly and **verified IN-CIRCUIT
by the fork's verifier**; all leaves are aggregated up a binary tree
(`build_and_prove_aggregation_layer`) to ONE root batch-STARK. Module doc:
`circuit-prove/src/ivc_turn_chain.rs:49-105`. This is the statement-equality argument
(`ivc_turn_chain.rs:63-81`): the production batch-STARK and the recursion uni-STARK
are two FRI instantiations of the *same* `EffectVmDescriptorAir` constraint set, so
the fold re-proves the identical statement and verifies it inside the recursion
circuit.

**The soundness composition is Lean-proven gap-free** — the part Mina does NOT have
machine-checked:

- `metatheory/Dregg2/Circuit/RecursiveAggregation.lean:206`
  `light_client_verifies_whole_history` — a client checking ONLY `verify agg.root`
  obtains `AggregateAttests` (every turn executed, chain ordered, final root is the
  genuine fold). `#assert_axioms`-clean. The three engine-soundness facts are
  `structure` fields of `EngineSound` (`RecursiveAggregation.lean:121`), NOT axioms.
- The `recursive_sound` leg (root ⇒ all leaves verify) is **DERIVED, not carried**,
  by the whole-tree fold: `metatheory/Dregg2/Circuit/RecursiveSoundFromNodes.lean:170`
  `recursive_sound_from_nodes` (+ `engineSound_recursive_derived:190`), an induction
  over a proof-carrying `PTree`. So the residual is *only* the per-node in-circuit
  recursion-verifier soundness (the fork's FRI floor), nothing app-specific.
- Anti-ghost teeth: `RecursiveAggregation.lean:544` `tampered_aggregate_cannot_bind`
  (reorder/drop/insert rejected), `:560` `leaf_pairing_defeats_swap`,
  `:270` `anchored_attests_rejects_fabricated_genesis`.

**The two fork follow-ups the older census flagged as the "carry-home" are now
CLOSED in-code** (the census `metatheory/docs/RECURSION-AGGREGATION-CENSUS.md` is
dated 2026-06-24 and is stale on exactly this point). Per the current module doc:
child-circuit VK identity is pinned via `into_recursion_input_pinned`
(`ivc_turn_chain.rs:171-183`) and leaf public values are re-exposed at the root
(`:184-191`). The whole-chain claim `[genesis, final, num_turns, chain_digest]` is
now the ordered SEGMENT ACCUMULATOR derived by construction from the real descriptor
leaves and host-checked (`ivc_turn_chain.rs:107-146`), closing the "executed A,
claimed B" forgery (`CRITICAL HOLES #1/#2/#6`).

> **Honest floor (named, not hidden).** The one thing outside Lean is the fork's
> in-circuit FRI verifier soundness — the SAME standard FRI/STARK assumption every
> recursive STARK chain (Mina/Plonky3) carries (`ivc_turn_chain.rs:148-157`). This is
> a *native BabyBear* recursion floor and is genuine (it does verify a STARK in a
> STARK). It is DISTINCT from the on-chain cross-field wrap discussed in §5, whose
> carrier is currently vacuous.

---

## 2. HAVE — the IVC accumulator + base case + the unbounded INDUCTION (crypto driver is the gap)

- **Bounded-K fold: LIVE.** `prove_turn_chain_recursive` folds an arbitrary finite K
  into one constant-cost root proof, resident or streaming
  (`ivc_turn_chain.rs:193-221`, `prove_turn_chain_recursive_streaming`).
- **Base case: proven both ends.** `RecursiveAggregation.lean:634` `genesisAcc`
  (empty fold from genesis), `:238` genesis anchor, `:191` `final_is_genuine_fold`.
- **Unbounded online accumulator — the SOUNDNESS SKELETON is Lean-proven; only the
  crypto driver is unbuilt.** `RecursiveAggregation.lean:722` `accumulate` (the
  running left-fold step), `:745` `accumulate_preserves_wellformed` (the IVC
  invariant), `:762` `acc_attests_whole_history` (by induction from genesis, O(1)
  memory in the spec). The 2-step inductive core in Rust is
  `circuit-prove/src/ivc_turn_chain.rs:5678` `fold_two_turns`. The DRIVER — drive it
  as a running fold (not a K-tree) with the previous running proof re-verified
  in-circuit so memory stays O(1) — is the named gap (`ivc_turn_chain.rs:199-205`).
  This is Mina/Zeko's unboundedness; dregg has the *proof* of the induction, and
  needs the fork wiring.

**Finality leg (beyond internal correctness).** A recursive rollup must accept only
a *finalized* root, not any internally-consistent fork. dregg has this:
`metatheory/Dregg2/Distributed/FinalizedLightClient.lean:165`
`FinalizedHistoryAttested` + `:281` `finalized_light_client_fires_for` — the client
takes `(aggregate, finalizedRoot, finalityCert)` and accepts only when the aggregate
verifies AND its `finalRoot` matches AND a genuine super-ratification quorum
(`BlocklaceFinality.isSuperRatified`, the node's real `ordering.rs::tau`) anchors
that root. This is the L2-block-is-final check a real bridge needs.

---

## 3. HAVE — an L1 that verifies dregg's proof and holds its state commitment (for EXTERNAL L1s)

dregg already does ingredient (4) — an L1 verifying dregg's whole-history proof and
recording the state commitment — **for external EVM chains**:

- `chain/contracts/DreggSettlement.sol` — an EVM (Base) contract that verifies
  dregg's 25-lane whole-history **Groth16-wrapped STARK** (`genesis_root ++
  final_root ++ num_turns ++ chain_digest`, the `WholeChainProof` lanes) and records
  every proven root. Nomad-law fail-closed.
- `chain/contracts/DreggPeerRegistry.sol:130` `submitPeerFinality` — the mirror: an
  on-chain verifier of a **peer chain's** finalized state via a
  light-client-STARK→Groth16, permissionless and proof-gated ("the proof IS the
  capability"), monotone finality, Nomad-law. Doc: "each chain's on-chain verifier
  can check the OTHER's consensus proof: TRUE PEERS."

**Crucial direction caveat.** Both are Solidity contracts on *external* L1s. dregg
currently settles *outward* (Base/Cosmos/Solana/Midnight per the True-Peers memory).
There is **no dregg-native L1 verifier** — no dregg turn/effect that verifies a child
dregg's `WholeChainProof` and commits its state root into dregg state. That
absent piece is exactly the "settle to itself" of Zeko (§6-NEW-B).

---

## 4. HAVE — supporting recursion/fold machinery (adjacent, reusable)

- **Attenuation-depth IVC** (the task's "`EffectVmEmitIvcStateTransition`"):
  `circuit/src/ivc.rs` is a Poseidon2 **hash-chain** state-transition trace for
  delegation depth (`MAX_FOLD_DEPTH`), Lean-emitted as
  `metatheory/Dregg2/Circuit/Emit/EffectVmEmitIvcStateTransition.lean`
  (`ivcStateTransitionDescriptor`), gated by
  `circuit-prove/tests/ivc_state_transition_emit_gate.rs`, Lean soundness twin
  `metatheory/Dregg2/Circuit/StateTransitionAirSound.lean`. **Be precise:** this is a
  *hash-chain accumulator, NOT recursive proof-carrying-proof.* The simulated IVC
  engine (`prove_ivc`/`verify_ivc`) was DELETED 2026-07-16 as a mock
  (`circuit/src/ivc.rs:16-26`). So "IvcStateTransition" is a fold *shape*, not the
  recursion — the recursion is §1's `ivc_turn_chain`.
- **Recursive proof-of-holdings fold:**
  `metatheory/Dregg2/Bridge/HoldingFoldRecursive.lean` `fold_sound` — an IVC light
  client folds N holding proofs into ONE aggregate; the additive homomorphism a
  recursive light client exploits. Reusable for an L2→L1 holdings bridge.
- **Cross-cell width aggregation** (orthogonal axis): `circuit/src/bilateral_aggregation_air.rs`
  + live `/turns/aggregate` route (`node/src/api.rs` `post_aggregate_bundle`).

---

## 5. HAVE-BUT-HONEST-PARTIAL — the cross-field wrap (STARK→gnark BN254→Groth16)

This is the "a STARK verifying a STARK" the task asks about at
`FriVerifier.lean`, and it is the one place to be careful, because the memory flags a
**vacuity**:

- `metatheory/Dregg2/Circuit/FriVerifier.lean:1012` `GnarkRefines` (the gnark BN254
  circuit computes the same accept Boolean as the specified `verifyAlgo`), `:1037`
  `wrap_sound` (GnarkRefines + the FRI carrier ⇒ the gnark circuit inherits the
  spec's soundness). The deployed gnark is `chain/gnark/fri_verifier.go`.
- **⚑ The FRI carrier is PROVEN VACUOUS.**
  `metatheory/Dregg2/Circuit/FriVerifier.lean:995` `FriLowDegreeSound` is `↔ True`
  (`FriCarrierVacuity.lean`); the honest deployed wrap
  (`FriWrapHonest.lean::emitVerifier_wrap_sound_honest`) concludes ONLY
  `proof.exposedSegment = pub.segment`. The deployed FRI *query* leg's honest ceiling
  is **~31 bits, not the config's claimed 130** (`FriCarrierEpsilon.lean`,
  `deployed_wrap_ceiling`). So the on-chain wrap **binds the segment** but does NOT
  deliver a per-proof FRI extraction.

**Why this matters for dregg-in-dregg, and why it does NOT block it.** The cross-field
gnark wrap is the *EVM settlement* path (BabyBear STARK → BN254 → Groth16, for
contracts that can only do a pairing check). A *dregg-native* self-settlement (§6-B)
would verify the child proof with the **native BabyBear in-circuit recursion of §1**,
whose floor is genuine, NOT this vacuous cross-field carrier. So dregg-in-dregg should
**recurse through `ivc_turn_chain`, not through the gnark wrap** — the wrap is only
needed if the L1 is a foreign EVM chain. This is the single most important design
constraint the honest reading yields.

---

## 6. NEW — what a full Zeko-style dregg-in-dregg would still need

Mapping the Zeko ingredients (§0) onto the have-vs-new split:

| Ingredient | dregg state | New work |
|---|---|---|
| (1) recursion primitive | **HAVE, live** (`ivc_turn_chain`, native BabyBear in-circuit FRI recursion) | none |
| (2) IVC accumulator | **HAVE bounded-K, live + node-wired**; unbounded **induction proven**, driver unbuilt | **NEW-A**: the online fold driver |
| (3) base case | **HAVE, proven** (`genesisAcc`, genesis/final anchors) | none |
| (4) L1 verifies L2 proof + holds commitment | **HAVE for external EVM L1s** (`DreggSettlement`/`DreggPeerRegistry`); NOT for a dregg-native L1 | **NEW-B**: a dregg settlement *effect* |
| (5) recursion threading / rollup account | partial (peer-registry pattern on EVM; content-addressed state) | **NEW-C**: L2-commitment-on-dregg-L1 account + deposit/withdraw bridge |

**NEW-A — the unbounded online accumulator driver.** Drive `fold_two_turns`
(`ivc_turn_chain.rs:5678`) as a running fold with the previous running proof
re-verified in-circuit (O(1) memory), matching Mina's unbounded recursion. The
*soundness* is already the Lean induction (`accumulate_preserves_wellformed`); this is
fork/crypto engineering, not new metatheory. **Optional** for a bounded-window rollup;
required to exactly match Zeko's perpetual accumulator.

**NEW-B — a dregg-native L1 verifier as an EFFECT (the "settle to itself").** The core
missing loop. Today the in-circuit recursion-verify happens as a *light-client /
compression op* (`handlers_verify.rs`), not as a *turn effect* in the executor forest.
A Zeko-style self-settlement needs an effect whose semantics is "verify a child/L2
dregg `WholeChainProof` and commit its `final_root` into (parent) dregg state" — the
`DreggPeerRegistry` pattern, but as a dregg effect verified *inside a turn circuit*,
recursing through the native BabyBear engine of §1 (NOT the gnark wrap, per §5).
**Discipline:** per the Lean-authored-AIR law, the new settlement-verify constraint set
is AUTHORED IN LEAN (a descriptor + refinement rung), reusing `ivc_turn_chain`'s
in-circuit verifier as the gadget and `FinalizedLightClient`'s three-leg check as the
acceptance predicate; Rust only calls the emitted artifact. This is the piece that is
genuinely *not built* — real code exists for every input it composes, but the effect
itself and its Lean descriptor do not yet exist.

**NEW-C — the L2-commitment-on-L1 account + bridge.** A rollup account model on a
dregg L1: an L1 cell/record that holds the L2's committed state root, advanced only by
NEW-B's settlement effect, with deposits/withdrawals binding the commitment
(reusing `HoldingFoldRecursive` for the holdings leg). This is assembly over existing
primitives (content-addressed state, the peer-registry monotone-finality pattern), not
research.

**Adjacent, not required:** the partial-turn / suspendable-continuation work
(`Dregg2/Exec/ConditionalTurn.lean`, `Dregg2/Await.lean`, and the NON-VK lift
`Dregg2/Exec/ConditionalTurnLift.lean:480` `execFullTurnA_lift_value`) is promise
*pipelining within/across turns*, not a proof-verifying-a-proof. It composes
state-transitions recursively at the *executor* layer but is orthogonal to the
recursion-threading dregg-in-dregg needs. Do not conflate.

---

## 7. VERDICT — "already latent / small assembly / real build"?

**It is BETWEEN "small assembly" and "real build," strongly toward the assembly end,
because the hard part is done.**

- **The recursion primitive + IVC accumulator + base case + Lean-proven composition
  are REAL, LIVE code** (§§1-2), not aspiration. dregg genuinely verifies a dregg
  STARK inside a dregg STARK today, folds a whole chain into one proof, and a light
  client (and the node) consumes it. This is the ingredient list ember is right about.
- **A compression-style "dregg verifies its own history" already ships** — that IS
  `verify_history` over `WholeChainProof`. If that is all "dregg-in-dregg" means, it
  exists.
- **A true Zeko-style recursive L2-on-a-dregg-L1** is a **real (but focused) build**:
  it needs NEW-B (a dregg-native settlement effect verifying a child proof inside a
  turn, Lean-authored) and NEW-C (the L2-commitment-on-L1 account + bridge), plus
  optionally NEW-A (unbounded driver). None of these is research — every dependency
  exists as code — but the self-settlement *loop* is genuinely unbuilt, and calling it
  "already latent" would overclaim.

**Honest ledger of real-vs-aspirational:**

- REAL, LIVE: `ivc_turn_chain` prove/verify, node wiring, `verify_history`, the segment
  accumulator + VK-pin + leaf-public re-expose (fork follow-ups closed),
  `RecursiveAggregation` + `RecursiveSoundFromNodes` + `FinalizedLightClient`,
  `DreggSettlement` + `DreggPeerRegistry` (deployed EVM).
- REAL BUT PARTIAL: the on-chain gnark FRI wrap (segment-binding only, FRI carrier
  vacuous, ~31-bit query floor — §5); the unbounded accumulator (induction proven,
  driver unbuilt).
- NOT BUILT: the dregg-native settlement effect (NEW-B), the L2-account-on-dregg-L1
  model (NEW-C), the recursion-as-effect threading.

---

## 8. Ordered next steps (smallest leverage first)

1. **State it truthfully in the record first.** dregg already does recursive
   whole-chain self-verification (bounded-K, gap-free above the native FRI floor,
   node-wired). Correct the stale "carry-home" in
   `metatheory/docs/RECURSION-AGGREGATION-CENSUS.md` (the two fork follow-ups it names
   are CLOSED per `ivc_turn_chain.rs:171-191`).
2. **Spec NEW-B on paper against the real signatures.** Define the dregg settlement
   effect: input = a child `WholeChainProof` + `finalityCert`; acceptance =
   `FinalizedLightClient.FinalizedHistoryAttested`; commitment = write child
   `final_root` into an L1 cell. Author the descriptor **in Lean** (law), reusing
   `ivc_turn_chain`'s in-circuit verifier as the gadget. No Rust AIR.
3. **NEW-C the rollup account.** An L1 record holding the L2 commitment, advanced only
   by the NEW-B effect (monotone, Nomad-law, mirroring `DreggPeerRegistry`);
   deposit/withdraw via `HoldingFoldRecursive`.
4. **(Larger, optional) NEW-A the unbounded driver.** Drive `fold_two_turns` as a
   running fold (prev proof verified in-circuit, O(1) memory) — the crypto half of the
   already-proven `accumulate_preserves_wellformed` induction. This is the frontier
   *after* the self-settlement loop exists.
5. **Never route self-settlement through the gnark wrap.** Recurse through the native
   BabyBear engine (§1); the cross-field wrap is EVM-only and its FRI carrier is
   vacuous (§5).

---

## Cross-references

- `metatheory/docs/RECURSION-AGGREGATION-CENSUS.md` — the fuller ALIVE/STALE census
  (2026-06-24; stale on the two now-closed fork follow-ups).
- Memory: `project-universal-fold-buff-lightclient` (the whole-history recursion
  vision, "the finale FIRED" — all 8 carriers deployed);
  `project-dregg2-architecture` (dregg2 = the Lean implementation);
  `project-lightclient-stark-true-peers` (the peer-registry / settlement true-peers
  campaign); `project-partial-turn-promises` (the adjacent, non-recursion
  promise-pipelining work).
- Honesty carriers for §5: `metatheory/Dregg2/Circuit/FriCarrierVacuity.lean`,
  `FriCarrierEpsilon.lean`, `FriWrapHonest.lean`.
</content>
</invoke>
