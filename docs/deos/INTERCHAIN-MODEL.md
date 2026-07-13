# dregg's interchain model: networked proofs of holdings

*Present-tense, what-is. The canonical statement of how dregg relates to other chains,
so the model is clear from the repo — not inferred from a chat thread. Honest per-chain
maturity is a table below; nothing here is a roadmap promise.*

## The one sentence

**dregg networks *proofs*, not tokens.** A dregg state transition is proven with math,
and any chain's verifier can check that proof for itself — no bridge validators, no wrapped
tokens, no custody handed to a multisig. Where a chain has a bridge (IBC, Hyperlane,
LayerZero), dregg plugs in and replaces a *vote* with a *proof*; where it has none, dregg
proves directly.

## What "universal" means here (and what it does not)

"Universal" is a claim about **architecture**, backed by a real proof-point:

- dregg's settlement layer is a **field-parameterized native-hash shrink**
  (`circuit-prove/src/dregg_outer_config.rs` — a generic `StarkGenericConfig`; the recursion
  verifier is field-generic, not curve-hardcoded). A dregg proof is re-committed with a hash
  native to the *target chain's* field, so that chain's verifier hashes cheaply.
- **EVM = the BN254 instantiation** (built + verified — see the table). **Mina = the Pasta
  instantiation** of the *identical* code (scoped, not built). One design, many chains.

It does **not** mean:
- …that $DREGG is minted on other chains. **$DREGG is native to Solana.** It is *represented
  inside dregg's own state*; other chains verify proofs *about* dregg. No multi-chain supply,
  no cross-chain minting — that would be a deliberate tokenomics decision, and it is not what
  the architecture requires or what is built.
- …that it is live on any mainnet. The verifiers work in test; **mainnet deployment and the
  production MPC trusted-setup ceremony are not done** (the current Groth16 setup is a
  single-party dev ceremony — toxic-waste-known).

## Two directions (both are "networked proofs of holdings")

1. **Inbound — prove your holdings on a chain, then govern.** A holder proves, cryptographically,
   that they hold a designated asset on a chain (a stake-weighted ≥2/3 supermajority + accounts
   inclusion on Solana; an ERC-20 storage proof on EVM; a bank-balance proof on Cosmos), binds
   their identity non-custodially (the binding trilogy: Ed25519 Solana · secp256k1 EVM-addr ·
   secp256k1 Cosmos-addr), and casts a **holding-weighted vote**. Custody never leaves the
   holder's wallet. (`dregg-governance/`, `bridge/src/solana_holdings.rs`, the light-clients.)
2. **Outbound — settle a dregg proof onto a chain.** dregg produces a proof of its state
   transition; the target chain's on-chain verifier checks it and settles. (`chain/gnark` →
   `chain/contracts/DreggSettlement.sol` for EVM; the Mina/Cosmos analogues in progress.)

The non-custodial guarantee is the same both ways: **you never move tokens into a bridge
wallet.** You prove, you don't lock.

## Per-chain maturity (honest — this is the load-bearing table)

| chain | inbound (prove holdings → govern) | outbound (chain verifies a dregg proof) |
|---|---|---|
| **Solana** | **REAL** — consensus-anchored ≥2/3 stake supermajority + accounts inclusion, governance-pinned anchor (forgery closed); runs end-to-end (`cargo test -p dregg-governance` green) | asset lock/unlock = **M-of-N oracle-attested** (honest: not proof-carrying) |
| **EVM** | ERC-20 storage-proof holding + secp256k1 binding **built**; the compiled join into governance is landing | **REAL** — a genuine Groth16 proof of a dregg state transition **verifies on-chain** (Foundry) against a generated Solidity verifier; forgeries reject; survived four adversarial audits. On dev-ceremony setup, not mainnet. |
| **Cosmos** | bank-balance holding + secp256k1/bech32 binding **built** (inbound side) | **IN PROGRESS** — a Cosmos-side verifier of dregg proofs (IBC / CosmWasm) is the earlier direction; not yet demonstrated |
| **Robinhood Chain** (EVM Arbitrum-Orbit L2, chain id 46630, tokenized stocks/RWA) | **REAL — weak-subjectivity.** A genuine `eth_getProof` for a faucet-dropped tokenized-stock (TSLA) balance on the live testnet verifies through the SAME EIP-1186 machinery into a dregg `ProvenForeignHolding` tagged `Evm(46630)` (`eth-lightclient` `verify_erc20_holding_wide` — the OZ-v5 ERC-7201 namespaced-storage glue; `dregg-interchain-gov` `tests/robinhood_inbound.rs`). Verified against a **supplied** L2 state root → `StructureOnly` / `consensus_proven:false` (an Orbit L2 has no Altair sync committee). **Trustless upgrade (named, not built): verify the L2 root against its L1 (Ethereum) Arbitrum-rollup anchor** — only then `consensus_proven:true`. | — (outbound = settle a dregg proof onto Robinhood Chain; the EVM/BN254 wrap applies but is not demonstrated there) |
| **Mina** | — | **SCOPED, NOT BUILT** — the Pasta instantiation of the EVM wrap; a go/no-go (Pasta-Poseidon-vs-o1js KAT + Kimchi verifier constraint count) precedes the multi-week build. The old Kimchi/Pickles relay was *vacuous* (never verified the proof in-circuit) and was removed. |

Rule for talking about this: **present-tense claims track the table.** "EVM verifies dregg
proofs" is demonstrated; "Cosmos/Mina verify" is architecture-in-progress. Say which.

## Why this is not a bridge (the security point)

Every bridge (LayerZero, Hyperlane, IBC, Wormhole) answers "did X happen on chain Y?" by
**trusting a set of validators** — the attack surface that keeps getting drained for hundreds
of millions. dregg answers the same question with a **proof the other side checks itself**. So
dregg is not *plugged into* one bridge's trust; it is the plug that fits all of them, upgrading
a vote to a proof where a socket exists and proving directly where none does.

## See also

- `docs/deos/WRAP-NATIVE-HASH-DECISION.md` — the field-parameterized shrink + the EVM (BN254) wrap, measured.
- `docs/deos/PROOF-OF-HOLDINGS.md` — the inbound holdings proofs (anchored Solana path).
- `docs/deos/TOKEN-MIRROR-BRIDGE.md` — the settlement targets (`ethereum`, `li`/Mina, `midnight`).
- `docs/x-article-interchain.md` — the community-facing "plug, not the socket" telling.
- The go/no-go + full-flow work is tracked in `GOAL-MULTICHAIN-SETTLEMENT.md` / `HORIZONLOG.md`.
