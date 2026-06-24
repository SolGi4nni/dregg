# DESIGN — Recursive-Aggregation Soundness (the magnesium → gold bridge)

*Status: LANDED (Lean proofs `#assert_axioms`-clean + Rust light client builds + tests). This is the
soundness MODEL + light-client verifier the post-cutover "rewire the live aggregation prover onto
descriptor proofs" follow-on (task #94) plugs into. It does NOT itself rewire the live prover.*

## What this delivers

The IVC accumulator `circuit/src/ivc_turn_chain.rs::prove_turn_chain_recursive` folds a chain of N
finalized turns into ONE `WholeChainProof`; `verify_turn_chain_recursive` checks only the root, at
cost independent of N. **What did that succinct proof MEAN, gap-free?** This work answers it:

- **`Dregg2/Distributed/HistoryAggregation.lean`** — the FOLD model. A chain of `ChainStep`s, each a
  genuine `recCexec` transition over `RecChainedState` (the verified executor) whose roots are the §8
  `recStateCommit` (the injective full-state commitment the whole-turn triangle pins). The
  `TurnChainBindingAir` temporal tooth `new_root[i] == old_root[i+1]` is `Continues`/`ChainBound`.
  - HEADLINE `wellformed_attests_whole_history`: a well-formed chain ⇒ (1) every turn `recCexec`-correct,
    (2) `ChainBound` ordered, (3) the whole chain is a `Run recChainedSystem` from genesis whose
    endpoint commits to the genuine fold ⇒ `wellformed_history_conserves` (no mint/burn over ALL of
    history).
  - `root_tooth_pins_state` — the **CR recovery**: under `compressInjective cmb` (`recStateCommit_binds`),
    matching seam roots ⇒ equal `cellDigest` + `RH`, i.e. the §8 root IS the full-state commitment. So a
    light client seeing only ROOTS genuinely learns STATE continuity.
  - Non-vacuity BOTH ways: `honest_chain_wellformed` (positive, over `teethGenesis`) +
    `tooth_rejects_broken_order` (a reordered chain is NOT `ChainBound`).

- **`Dregg2/Circuit/RecursiveAggregation.lean`** — the SNARK recursion layer + **the light-client
  headline**. Opaque `(Proof, verify)` = plonky3 `RecursionCompatibleProof` / `verify_recursive_batch_
  proof`. `EngineSound` bundles the THREE named, realizable soundness hypotheses you cannot prove in
  Lean:
  - `recursive_sound` — root verifies ⇒ all child leaves verify (the ONE FRI obligation, §H1 of
    `DESIGN-recursion-aggregation-private-joint-turns.md`).
  - `leaf_sound` — a **positional `Forall₂` pairing** leaf↔step ⇒ a verifying leaf attests its `recCexec`
    step (the EffectVm circuit⟺executor soundness, already proved per-effect in Lean, lifted to the leaf
    boundary). The positional pairing is load-bearing: a leaf is bound to its OWN step → no leg swap.
  - `binding_sound` — a verifying `TurnChainBindingAir` leaf ⇒ `ChainBound` + the genesis/final root pins.
  - HEADLINE `light_client_verifies_whole_history`: checking ONLY `verify agg.root` (re-witnessing
    NOTHING) ⇒ `AggregateAttests` (every turn correct + ordered + final = genuine fold).
    `attested_history_conserves` is inherited. **Proofs are additive attestation — the verification IS the
    trust.**
  - Anti-ghost: `tampered_aggregate_cannot_bind` (a reordered chain ⇒ `binding_sound` would force
    `ChainBound` = FALSE ⇒ no verifying aggregate) + `leaf_pairing_defeats_swap` (positional pairing ⇒
    a leaf is not re-pointable).
  - Non-vacuity BOTH ways: `real_engine_sound` / `light_client_fires_on_real_chain` /
    `real_chain_first_turn_executed` (witnessed over the honest `teethGenesis` step).
  - The named hypotheses are `structure` FIELDS, **not axioms** — `#assert_axioms`-clean ⊆ {propext,
    Classical.choice, Quot.sound}.

- **`lightclient/` (`dregg-lightclient`)** — the Rust embodiment. `verify_history(&WholeChainProof)`
  runs the single succinct check (`verify_turn_chain_recursive`) and returns `AttestedHistory` (the Rust
  mirror of `AggregateAttests` — genesis/final root, chain digest, num turns), re-witnessing nothing.
  Tests fold a real K=4 chain + light-verify it, and reject a corrupted aggregate.

## The honest trust boundary

`verify_turn_chain_recursive` is plonky3's recursive-STARK verifier; its FRI soundness is the named
`recursive_sound` hypothesis — NOT re-proved in Lean (you cannot prove plonky3 FRI in Lean). What is
gap-free is the **composition**: IF the aggregate verifies (engine sound) THEN the whole history is
attested. That composition is exactly where a real aggregation bug (verify proof-of-step-7 but export
step-3's roots; swap a leg; drop a turn) would surface — and the three teeth show it cannot.

## Where the rewiring (task #94) plugs in

The live aggregation prover currently wraps EffectVm-shape leaves (`ivc_turn_chain.rs` `prove_turn_leaf`).
The post-cutover follow-on routes the LEAVES onto descriptor-interpreter proofs. That swap changes WHICH
proof discharges `leaf_sound`'s `verify p = true → recCexec …` obligation — but **not the model**: the
`EngineSound` interface and the `light_client_verifies_whole_history` headline are unchanged. The light
client (`dregg-lightclient::verify_history`) is the stable surface the rewired prover proves against.
