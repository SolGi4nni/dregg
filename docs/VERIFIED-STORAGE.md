# Verified decentralized storage

Dregg's storage layer is **formally verified**: the commitment, erasure/fountain coding,
proof-of-retrievability, and the provider-slashing market are machine-checked theorems in Lean
(`metatheory/Dregg2/Storage/`), not just incentive arguments. Live demo:

```
cargo run -p dregg-storage --example verified_storage
```

## The one line

Every decentralized-storage network you know (Filecoin, Arweave, Storj, Sia) is *"trust the
incentives."* Dregg's storage core is **proven** — 17 machine-checked theorems across 6 modules,
`#assert_axioms`-clean, and the *only* cryptographic assumption is that **Poseidon2 is
collision-resistant.** Everything else — k-of-n reconstruction, the trustless read, the
audit refusing a forgery, the slash burning a provider's bond — is a theorem.

## What is proven (the theorems)

| Construction | Theorem(s) | In English |
|---|---|---|
| **Content commitment** | `contentRoot_injective`, `read_sound` | the root binds the object set (no ghost hides under a genuine root); a served object that opens IS the committed one |
| **Reed–Solomon erasure** | `rs_decode_correct`, `no_wrong_reconstruction` | any *k* of *n* shards reconstruct the original, and the decoder can't be tricked into a wrong blob |
| **Fountain / rateless (LT)** | `fountain_decode_unique`, `no_wrong_recovery` | rateless decode recovers the unique message; distinct messages can't share droplets |
| **Proof-of-retrievability** | `por_sound`, `por_refuses_substitution` | a provider that passes an audit holds the genuine data; a substitution is refused |
| **End-to-end availability** | `verifiable_erasure_recovers` | a client holding only the root recovers the true blob from any *k* audited shards — no provider trust |
| **Provider market** | `unauthorized_claim_rejected`, `open_deal_only`, `slash_decreases_collateral` | only a bonded provider claims a deal; no double-sell; a failed audit *strictly* burns the bond |

All reduce to the one carrier `Poseidon2SpongeCR` (collision-resistance), threaded as a hypothesis —
verified by `#assert_axioms` to depend on nothing but the three standard Lean axioms.

## The honest boundary (say this — it makes the claim stronger, not weaker)

- **The Lean is the *specification*; the fast Rust is *checked against* it.** The RS/commitment Rust
  codecs are the production impl, and their tests assert the exact property the Lean proves (a
  mutation canary confirms the tests bite). Compiling the Lean itself to the runtime via `@[export]`
  (like the kernel already does) is in progress — it's the next step, not a claim we make today.
- **The Merkle/commitment binding is proved down to Poseidon2 collision-resistance** — a standard,
  named assumption, not hand-waving. We do not claim Poseidon2 is unbreakable; we claim everything
  above it is a theorem *given* it.
- **Not yet deployed to a live public network** — that's a separate lane (a fresh genesis).
- The fountain codec and the market template are Lean-proven; their Rust wiring is partial.

## The numbers

- **17** theorems · **6** modules · **482** lines of Lean · `#assert_axioms`-clean.
- **1** cryptographic assumption (Poseidon2 collision-resistance).
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

`metatheory/Dregg2/Storage/{BucketCommitment,Erasure,Fountain,Retrievability,Availability,ProviderMarket}.lean`
· the bound Rust: `storage/src/{erasure,bucket_commitment}.rs` (see the `lean_spec_binding` tests).
