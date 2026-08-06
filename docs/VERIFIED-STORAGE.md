# Verified decentralized storage

Dregg's storage layer is **formally verified**: the commitment, erasure/fountain coding,
proof-of-retrievability, and the provider-slashing market are machine-checked theorems in Lean
(`metatheory/Dregg2/Storage/`), not just incentive arguments. Live demo:

```
cargo run -p dregg-storage --example verified_storage
```

## The one line

Every decentralized-storage network you know (Filecoin, Arweave, Storj, Sia) is *"trust the
incentives."* Dregg's storage core is **proven** — 50 machine-checked theorems across **17** modules
(`metatheory/Dregg2/Storage/`), `#assert_axioms`-clean. Everything else — k-of-n reconstruction, the
trustless read, the audit refusing a forgery, the slash burning a provider's bond, the deal
lifecycle conserving value — is a theorem.

> ⚑ **The cryptographic assumption was RE-GROUNDED on 2026-07-25, and this line used to overstate
> it.** It is no longer "Poseidon2 is collision-resistant" as a *literal injectivity* hypothesis:
> that spelling is **refuted at deployed BabyBear parameters** —
> `Dregg2/Storage/DeployedFloorRegrounded.lean:474` proves
> `storage_old_hypothesis_unavailable : ¬ Poseidon2SpongeCR poseidon2Hash`. The floor is now the
> quantitative collision *game* `FloorGames.HashCRHardQuant`, and the binding theorems were rewritten
> from `_injective` into `_binds_or_collides` form: each concludes *either* the binding *or* an
> explicit colliding pair a total extractor hands back. The old `_injective` statements survive only
> as the hypothesis-taking `*_injective_of_binds_or_collides` corollaries.

## What is proven (the theorems)

| Construction | Theorem(s) | In English |
|---|---|---|
| **Content commitment** | `contentRoot_binds_or_collides`, `read_sound_or_collides` (was `contentRoot_injective` / `read_sound`, DELETED 2026-07-25) | the root binds the object set (no ghost hides under a genuine root) *or* the extractor returns a Poseidon2 collision; likewise a served object that opens IS the committed one |
| **Reed–Solomon erasure** | `rs_decode_correct`, `no_wrong_reconstruction` | any *k* of *n* shards reconstruct the original, and the decoder can't be tricked into a wrong blob |
| **Fountain / rateless (LT)** | `fountain_decode_unique`, `no_wrong_recovery` | rateless decode recovers the unique message; distinct messages can't share droplets |
| **Proof-of-retrievability** | `por_sound_or_collides`, `por_refuses_substitution_of_or_collides` | a provider that passes an audit holds the genuine data; a substitution is refused (or forces a collision — `por_substitution_forces_collision`) |
| **End-to-end availability** | `verifiable_erasure_recovers` | a client holding only the root recovers the true blob from any *k* audited shards — no provider trust |
| **Provider market** | `unauthorized_claim_rejected`, `open_deal_only`, `slash_decreases_collateral` | only a bonded provider claims a deal; no double-sell; a failed audit *strictly* burns the bond |
| **Deal lifecycle** | `DealLifecycle` + `DealLifecycleTrace` theorems | the deal state machine (`Open → Claimed → Active → Audited → Settled/Slashed`) is guard-sound, strictly forward-only (no un-settling, no cycles), and a slash *requires* a failed audit in its history |
| **Deal payment** | conservation theorems in `DealPayment` | bond + escrow only move between buckets — settle pays the provider and returns the bond, slash burns the bond and refunds the client; no value minted or destroyed |
| **Provider registry** | `serves_only_if_registered`, `slash_requires_registered` | a provider serves only once registered with positive stake; the stake is never conjured |
| **Market integrity** | `MarketAudit` composition | the PoR verdict drives the lifecycle: an honest provider can never be slashed; a withholding one is |
| **Executor refinement** | `MarketRefinement`, `DealCell` | the executor-wired cell-program's transitions ARE the abstract protocol's, all six legs, under an explicit abstraction — not a lookalike |
| **End-to-end client protocol** | `ClientProtocol` | the composed promise: store erasure-coded across *n* providers, and the data survives while any *k* pass audit |
| **Deployed-hash instantiation** | `contentRootDeployed_binds_or_collides` (`Deployed.lean`; was `contentRootDeployed_injective`, DELETED 2026-07-25) | the bucket content root over the *deployed* Poseidon2 (Lean logic calling the fast Rust hash via `@[extern]`) binds the committed object set, or yields the collision |
| **The floor, re-grounded** | `deployedFloor_refuted_by_modp_alias`, `deployed_ghost_object_exists`, `storage_old_hypothesis_unavailable` (`DeployedFloorRegrounded.lean`) | ⚠ at the *deployed encoder* the collision game is **won by a constant adversary with advantage 1**, and a real ghost object is exhibited under a genuine content root. This is the point of the cutover — a floor that can go red for a *reason* — not a clean pass |

The binding results reduce to one carrier, threaded as a hypothesis and verified by `#assert_axioms`
to depend on nothing but the three standard Lean axioms. ⚑ That carrier is now the quantitative
collision game `FloorGames.HashCRHardQuant (spongeFamily D)`, **not** the literal `Poseidon2SpongeCR`
this line used to name — see the re-grounding note above.

## The honest boundary (say this — it makes the claim stronger, not weaker)

- **The Lean is the *specification*; the fast Rust is *checked against* it** — for the storage
  codecs, today. The RS/commitment Rust are the production impl, and their tests assert the exact
  property the Lean proves (a mutation canary confirms the tests bite).
- **"The Lean *is* the runtime" is not aspirational — it already ships, for the kernel.** The core
  turn executor runs as **Lean compiled to native code, linked into the binary** (`@[export]` via
  `leanc`; `dregg-lean-ffi/libdregg_lean.a` is a native archive of the machine-checked Lean, and
  `dregg-lean-ffi`'s tests call it from Rust). Storage stands on the same path: the **bucket content
  root already runs as Lean at the deployed hash** — `Dregg2.Storage.Deployed` computes
  `contentRootDeployed` as verified Lean logic calling the fast Rust Poseidon2 through a
  native-scalar `@[extern]`, exports it back to Rust (`@[export dregg_storage_content_root]`), and
  `contentRootDeployed_injective` is the binding theorem at the deployed hash. So the honest ladder
  is: kernel + the content root = *Lean-is-the-runtime today*; the remaining storage codecs
  (RS/fountain) = *checked-against-Lean today, extraction is the same mechanical `@[export]` step.*
- **The Merkle/commitment binding is proved down to Poseidon2 collision-resistance** — a standard,
  named assumption, not hand-waving. We do not claim Poseidon2 is unbreakable; we claim everything
  above it is a theorem *given* it.
- **Not yet deployed to a live public network** — that's a separate lane (a fresh genesis).
- The fountain codec and the market template are Lean-proven; their Rust wiring is partial.

## The numbers

- **50** theorems · **17** modules · **~1,250** lines of Lean · `#assert_axioms`-clean.
- **1** cryptographic assumption — the quantitative collision game `HashCRHardQuant`, which at the
  *deployed* encoder is refuted (`deployedFloor_refuted_by_modp_alias`). The residual `Eff` cost
  model is named and undischarged.
- **0** `sorry`, **0** laundered carriers for the math (RS/fountain are real field algebra, no carrier).

## Anticipated hostile questions

- *"Verified how? Marketing-verified?"* → No: `metatheory/Dregg2/Storage/*.lean`, checked by the Lean
  kernel, `#assert_axioms`-pinned. Run `lake build`. The demo prints the theorem name per step.
- *"So the Rust could still be wrong."* → The Rust is bound to the proven spec by property-tests that
  a mutation canary shows will go red on a broken codec; the endgame (`@[export]`) makes the proven
  Lean *be* the runtime. We're explicit about which rung we're on.
- *"Is it live?"* → The proofs and the codec are real today; a live public network is the next lane.
  This is the verified *core*, shipping in the open.
- *"How is this different from Filecoin's PoRep?"* → Filecoin *tests* + incentivizes; here the
  retrievability soundness and the slashing are **theorems** reduced to one hash assumption.

## Where to look

`metatheory/Dregg2/Storage/{BucketCommitment,Erasure,Fountain,Retrievability,Availability,
ProviderMarket,DealLifecycle,DealLifecycleTrace,DealPayment,DealCell,MarketAudit,MarketRefinement,
ProviderRegistry,ClientProtocol,Deployed,DeployedFloorRegrounded}.lean
· the bound Rust: `storage/src/{erasure,bucket_commitment}.rs` (the `lean_spec_binding` test module
lives in `storage/src/erasure.rs:801`; `bucket_commitment.rs` has no such module).
