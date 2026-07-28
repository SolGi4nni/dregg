# Pickles reality-gate extractor — a REAL Mina block, verified by Mina's own verifier

This produces `metatheory/mina_real_block_proof.json`, which
`metatheory/Dregg2/Circuit/Emit/MinaRealBlockGate.lean` consumes. Unlike everything that came
before it in this campaign, the object here was not made by us:

| gate | object | provenance |
|---|---|---|
| `KimchiRealProofGate` | one Kimchi proof, `k = 16`, Vesta-committed | **we** proved `create_circuit(0, 5)` |
| `PicklesRecursion` P0–P2 | Step/Wrap decision runs | **synthetic** witnesses at a `2^5` domain |
| **`MinaRealBlockGate`** | **a Mina devnet block's Wrap proof**, `k = 15`, Pallas-committed, `prev_challenges = 2` | **Mina produced it**; a public devnet node served it |

## The block

* network **devnet**, chain id `29936104443aaf264a7f0192ac64b1c7173198c1ed404c1bcff5e562e05eb7f6`
* genesis `3NL93SipJfAMNDBRfQ8Uo8LPovC74mnJZfZYB5SK7mTtkL72dsPx`
* state hash `3NLmVB6Fs3dm4kXNkgwheHXzJXNpCCwEDe76RpTVeBTNujm12zNk`, blockchain length **539508**
* fetched 2026-07-28 from `https://api.minascan.io/node/devnet/v1/graphql`, query
  `bestChain(maxLength: 1) { stateHash protocolStateProof { base64 } … }` — **read-only, no keys,
  no transactions.** The response is pinned verbatim in `mina_devnet_block.json`; the proof field
  is the base64url of the binprot `Mina_base.Proof.Stable.V2` (11138 bytes).

## The ground truth — asserted, in this order, before a single number is emitted

1. `ledger::proofs::verifiers::BlockVerifier::make()` — openmina's own embedded **devnet
   blockchain verifier index**, loaded unmodified: `public = 40`, `prev_challenges = 2`,
   `domain = 2^14`, `max_poly_size = 2^15`, `zk_rows = 3`.
2. `ledger::proofs::accumulator_check::accumulator_check(&srs, &[proof]) = true` — openmina's own
   `sg` accumulator discharge on Vesta (`batch_dlog_accumulator_check`).
3. `kimchi::verifier::verify::<Pallas, …> = Ok(())` — **o1-labs' own Kimchi verifier**, on the
   Wrap proof re-marshalled from the wire types, against the 40-element public input assembled by
   openmina's own `PreparedStatement::to_public_input`.

2 and 3 are the body of openmina's `verification::verify_block`
(`= accumulator_check && verify_impl`; `verify_impl = verify_with` — the call in 3 — plus
`run_checks`, a private feature-flag/domain check).

**Why not literally call `verify_block`?** It takes a whole `MinaBlockHeaderStableV2` so it can
compute the protocol-state hash, and public Mina GraphQL does not serve blocks in binprot. We take
the block's own `stateHash` and decode it to `Fp` instead. That substitution is **self-checking**:
the protocol-state hash is the `app_state` folded into `messages_for_next_step_proof`'s digest,
which is part of the Wrap public input, which is absorbed by the Fq-sponge — one wrong bit and
step 3 rejects. It does not.

Then, still in Rust and still as `assert!` rather than prints, the extractor checks that the
emitted numbers reproduce `proof.oracles(...)`:

```
[cross-check] C8 fold over 47 es-entries reproduces oracles().combined_inner_product : true
[cross-check] C5 body over the emitted inputs reproduces oracles().ft_eval0 : true
[cross-check] Lean zkPolyR == kimchi permutation_vanishing_polynomial : true
[cross-check] omega^(n-3) == index.w() : true
[cross-check] K4c bEval reproduces RecursionChallenge::evals[0] : zeta=true zeta_omega=true
[cross-check] K4c bEval reproduces RecursionChallenge::evals[1] : zeta=true zeta_omega=true
```

## Build and run

The crate is deliberately **outside** the breadstuffs workspace (its own `[workspace]`), so that
arkworks 0.5 / proof-systems 0.3.0 / the forked `num-bigint` never enter the breadstuffs lockfile.
It expects `mina-rust` as a **sibling checkout** of this repo (`../../../../mina-rust`), openmina
rev **`82480cd468`** (v0.19.0).

```
cd metatheory/fixtures/pickles-extractors
cargo run --release -- devnet > ../../mina_real_block_proof.json
```

### The second binary — the GROUP side

`src/main.rs` dumps the **scalar** side. `src/bin/wrap_group_export.rs` dumps what a **group**
check needs: the linearization MSM's `(commitment, scalar)` pairs, the chunked `t_comm`, `ft_comm`,
and the 47 commitments `combine_commitments` feeds to the terminal MSM.

```
cargo run --release --bin wrap_group_export > ../../mina_real_block_wrap_group.json
```

`kimchi::verifier::to_batch` is **private**, so `f_comm` / `ft_comm` are rebuilt here from
`verifier.rs:897-963` using o1-labs' own `perm_scalars`, `PolishToken::evaluate`,
`Context::get_column`, `PolyComm::multi_scalar_mul`, `chunk_commitment` and `scale`. A
transcription is not a ground truth, so the reconstruction is then **pinned**: it is handed, inside
the full 47-entry `evaluations` list, to o1-labs' own `SRS::verify` — the real verifier's final IPA
opening check — which returns `true`; and re-run with `ft_comm` displaced by `+G`, which returns
`false`. Nothing is emitted unless both hold, so the gold cannot be a restatement of our own
arithmetic and the pin cannot be vacuous.

It also prints two measurements the plan in `docs/MINA-REAL-BLOCK-GATE.md` §6.1 rests on:
`linearization.index_terms = 0` (hence `f_comm` is a **one-term** MSM), and that the terminal
`msm == 0` runs over **82 non-SRS points + `|srs.g| = 32768`**.

The extra `rand = "0.8"` dependency exists only because `SRS::verify`'s `RngCore + CryptoRng`
bounds come from rand 0.8 and nothing in the graph re-exports it.

`Cargo.lock` is committed and is **seeded from mina-rust's own lock on purpose**: resolving fresh
fails, because `multihash 0.18.1` requires `core2 = "^0.4.0"` and `core2 0.4.0` is **yanked**. A
lockfile that already pins it is the only way this resolves.

## A measured openmina defect: the mainnet verifier index does not load

`cargo run --release -- mainnet` reproduces it. At openmina `82480cd468`,
`crates/ledger/src/proofs/data/mainnet_{blockchain,transaction}_verifier_index.json` are in a
**stale serde format**:

* `PolyComm` is `{"unshifted": [...], "shifted": null}` — the pre-`chunks` kimchi shape;
* `zk_rows` is absent entirely;
* `domain` is a 172-byte arkworks-0.3 `Radix2EvaluationDomain` encoding written as a JSON **int
  array** (172 = `u64 + u32 + 5·32`; the pinned ark-poly 0.5 layout is a different length),

while the pinned proof-systems `0.3.0` `o1_utils::serialization::SerdeAs` deserialises a **hex
string** from any human-readable format. So
`serde_json::from_str::<VerifierIndex<Fq>>(mainnet json)` fails with
`invalid type: sequence, expected a hex encoded string` and `BlockVerifier::make()` **panics**.
This is not feature-dependent — `serde_json` is always human-readable — so openmina cannot verify a
mainnet block at this revision. The **devnet** files were regenerated (`chunks`, `zk_rows: 3`, hex)
and work, which is why the gate is a devnet block.

`mina_mainnet_block_header.json` is kept alongside: it is a real **mainnet** block header (height
**359606**, genesis `3NK4BpDSekaqsG6tx8Nse2zJchRft2JpnbvMiog55WCr5xJZaKeP` — confirmed against
`api.minascan.io/node/mainnet` `genesisBlock.stateHash`), lifted from openmina's tracked p2p RPC
fixture `crates/p2p/tests/files/rpc/best_tip_with_proof_response.json`. It deserialises fine; only
the VK blocks it. When openmina regenerates the mainnet index, `-- mainnet` becomes a second gate
that calls `verify_block` literally.

## The lesson this directory encodes

The Kimchi extractors lived only as untracked files inside `~/dev/proof-systems` — one `git clean`
from gone. This one is tracked, its input fixture is tracked, and the rev it builds against is
written down in `Cargo.toml` and in this file.
