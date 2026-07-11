# Finding: the legacy census — EVM contracts, bridge trust models, and chain-agnostic participation (2026-07-11)

Three parallel file:line-grounded sweeps (contracts vs proving stack; governance/voting/passkeys;
bridge trust models) answering: what is legacy, what needs vast upgrading, and what is missing for
(a) no-wrap multi-chain, (b) non-custodial voting, (c) governance anyone can join from any chain.

## 1. The Solidity layer is pinned to a pre-v11 proof shape (structural, not cosmetic)

The live `WholeChainProof` claim is **25 BabyBear lanes**: `genesis_root8 ++ final_root8 ++
num_turns ++ chain_digest8` (`SEG_ANCHOR_WIDTH = 8` at `circuit-prove/src/ivc_turn_chain.rs:267`,
`SEG_DIGEST_WIDTH = 8` at `:254`, host tooth `:2807-2811`, envelope v3 postcard `:1751-1755`).
Everything EVM-side still encodes the **pre-widening 4-scalar model**:

- `IDreggSettlement.settle(...)` takes `bytes32 genesisRoot, bytes32 finalRoot, uint64 numTurns,
  bytes32 chainDigest` (`chain/contracts/IDreggSettlement.sol:43-51`); its own doc comment (`:18-22`)
  states the stale "four public inputs" spec. A Groth16 verifier's public-input vector length is
  fixed by its circuit — a 4-input ABI cannot bind a 25-input statement.
- `EthPublicInputs` (`bridge/src/ethereum.rs:260-270`) has single-word roots; `to_calldata` writes a
  104-byte tail and `from_tail` hard-rejects anything else (`:186-207`).
- `DreggVault.withdraw` decodes yet a third shape — Solidity
  `abi.decode(...,(bool,bytes32,address,uint256,address,bytes32))` (`DreggVault.sol:175-182`).
- **Three mutually incompatible public-value encodings** coexist (Solidity abi.encode / 104-byte
  bridge tail / postcard v3), and **no concrete settlement contract exists** (interface only;
  `Deploy.s.sol` deploys vault+gate only; the bridge is `SnarkSystem::BindingOnly`, a BLAKE3
  binding — `ethereum.rs:119,295-304`).

`docs/deos/ETH-NATIVE-WRAP.md` §0 also cites the 4-public shape; corrected alongside this finding.
**The gnark wrap circuit must target the 25-lane statement from day one.**

## 2. Contract-level defects beyond the shape

- **Fail-open verifier call**: both contracts `staticcall` `verifyProof(bytes32,bytes,bytes)` and
  check only success (`DreggVault.sol:163-171`, `DreggCredentialGate.sol:128-136`). A staticcall to
  a codeless address returns `(true, "")` → a misconfigured verifier immutable accepts everything.
  The foundry mocks normalize the same pattern (`DreggVault.t.sol:15-22`).
- **The vault's on-chain Merkle tree is decorative**: keccak (notes are Poseidon2 —
  `IDreggVault.sol:24,45`), O(n) full recompute per deposit (`_computeRoot`,
  `DreggVault.sol:228-253`, self-labeled "in production… incremental"), odd leaves promoted
  unhashed — and `withdraw()` **discards the proof's root** rather than comparing
  (`DreggVault.sol:181`). The security path never uses the tree.
- **No solvency/fee/relayer model**: withdraw checks token identity but never that the vault holds
  matching deposits; no relayer fee field; no `nonReentrant`; raw low-level ERC-20 `call`.
- **CredentialGate is demo-grade governance**: permanent single `admin` key (no rotation/timelock,
  `DreggCredentialGate.sol:33,95-108`); votes are bare `yes/no` uint counters with no proposal
  lifecycle/quorum/weighting/enactment (`:52-53,254-258`); non-standard ERC-721 (no
  transfer/approve/165, caller-chosen tokenId, `tokenURI` never written); **global** mint nullifier
  contradicting the interface's per-(serial,domain,tokenId) spec (`:196-197` vs
  `IDreggCredentialGate.sol:60-62`) — and the tests bake the wrong behavior in as intended.

## 3. Bridge trust models vs the bar ("wraps only exist where you lack proofs")

| Surface | Today | Distance to the bar |
|---|---|---|
| ETH settlement (dregg→ETH) | real proof *design*; Groth16 core absent (`BindingOnly`) | the gnark wrap (runway already laid) |
| Solana inbound $DREGG mirror | threshold-oracle attestation (`solana_mirror.rs:446-455`) | Option-B succinct wrapper |
| Solana consensus-verified path | REAL Tower-BFT verify in Rust — stake-weighted Ed25519 supermajority, bank-hash recompute, PoH segment (`solana_consensus.rs:286-343`) — but off-circuit, re-executing-validator grade | fold into an AIR (the multi-month item, `SOLANA-SUCCINCT-WRAPPER.md:160-166`) |
| ETH/Base inbound deposits | RPC `finalized`-tag trust; Base listener waits **2 confirmations** (`chain/src/listener.rs:85-96`) | sync-committee BLS + MPT proof — **no BLS12-381 verification exists in-tree at all** |
| Midnight | inbound: federation observes GRANDPA finality via WS-RPC; outbound: 2-of-3 attestation upgraded to 1-of-N watchtower fraud-proof (`midnight_verified.rs`); mirror-tree hash still a BLAKE3 `TODO(mirror-hash)` placeholder (`midnight_inclusion.rs:918`) | GRANDPA light client feasible, not built; wire the real Poseidon |
| Mina | binding-commitment + relay-liveness only (the old Kimchi "Level 2" recursion was VACUOUS and was removed — `mina.rs:154-159`) | in-circuit Ouroboros verify; do not resurrect the vacuous wrap |
| Stripe money-in | **the one deployed inbound proof**: DECO/zkTLS attestation verified in-AIR, Lean-proven (`stripe_deco.rs`) | already at the bar |

Standing constraints on any rebuild (all on record in `BRIDGE-ARCHITECTURE-SOUNDNESS.md`):
every inbound mint must route through the committed consume-once `lock_nullifier` gate (the
double-mint fix, `turn/src/executor/bridge_ledger.rs`); the deployed `proofBind` constraint is
**vacuous** (Lean `True`; the real recursion is not folded into the IVC chain) — closing it is a
gated VK epoch together with the `bridge_action_air` fold and the 4→8-felt lift; proof-to-action
binding is currently executor-side ("Silver"), not in-circuit.

The Solana paradox: the hardest chain has the most built (a real consensus verifier + the
weak-subjectivity/stake-rotation template any future light client can copy). The easiest chain
(ETH: 512-key sync committee) has nothing — BLS12-381 aggregate verification is the single missing
primitive.

## 4. Governance / non-custodial voting / passkeys — what exists

- **`dregg-governance`**: `FederationGovernance` wired to the REAL `ConstitutionManager` —
  proposals open polls whose electorate is the constitution's participant set, 2n/3+1 threshold,
  auto-enact on quorum (`src/governance.rs:80-151`, tests in `tests/teeth.rs`). Plus community
  polls with content-addressed causal `VoteBlock`s (dropped ballot ⇒ root mismatch) and
  non-amplifying liquid delegation. In-memory engine; not node-wired.
- **`collective-choice`**: a second, executor-backed engine on the real `EmbeddedExecutor` —
  WriteOnce ballot cells, monotone tallies, quorum as an `AffineLe` constraint, `Mandate`
  sub-delegation, nullifier set + per-voter blinding tokens (3-depth sybil resistance). The two
  `VoteEngine`s are explicitly unreconciled (`dregg-governance/src/lib.rs:49-56`).
- **`starbridge-apps/privacy-voting` + `polis`**: the cell substrate (ballot/poll factories;
  council/constitution/mandate/KERI-style identity organs). One-vote + tamper-evident tally;
  ballot *secrecy* (mixnet unlinkability) is a named open follow-up.
- **EVM voting**: `DreggCredentialGate.voteWithCredential` — ring membership + predicate + a
  per-proposal nullifier. This IS the non-custodial voting shape (prove, don't escrow), **but** the
  "balance ≥ X" predicate is a federation-attested credential attribute, not a proof over a real
  chain balance, and the on-chain tally is siloed from the in-protocol engines.
- **Passkeys — further along than remembered**: `extension/src/passkey.ts` (`PasskeyCustody`) uses
  the WebAuthn **PRF extension** to AES-GCM-wrap a dregg mnemonic (fail-closed without PRF), and a
  biometric assertion unwraps → signs a real **hybrid ed25519+ML-DSA `SignedTurn`**. The
  `demo/run-passkey.mjs` demo proves an **extension-less** passkey ballot on the real wasm
  `CollectiveChoiceEngine` (tally +1, duplicate refused). Missing: library glue binding passkey
  identities into electorates/credentials; `webauth-core`'s HTTP login half is unported.

## 5. The spine — primitive BUILT (2026-07-11), three welds remain

**UPDATE (2026-07-11): the primitive is now BUILT and Lean-verified.** The rest of this
section's framing ("nothing derives weight from holdings") described the state *before* the
proof-of-holdings primitive landed. It now exists, non-custodially, and closes item 1 below; the
three welds (2–4) remain. Primary design note: `docs/deos/PROOF-OF-HOLDINGS.md`.

The historical gap: every engine was one-voter-one-vote (+ delegation) over a static enumerated
`[u8;32]` electorate, and nothing derived weight from token holdings. The "$DREGG holder on
Solana/Base participates in dregg governance without moving custody" goal needed one new primitive
and three welds:

1. **Proof-of-holding → eligibility/weight** (the primitive): prove "an account I control held ≥ W
   $DREGG at snapshot S on chain C" into a `VoterId` binding. **BUILT + Lean-verified,
   non-custodially** (2026-07-11):
   - `bridge/src/solana_holdings.rs` — `ProvenHolding`, `prove_holding_consensus` (reads the
     holder's OWN SPL token account, verifies a stake-weighted ≥2/3 super-majority + 16-ary
     accounts-hash inclusion under a finalized bank hash → `LockProofTrust::ConsensusVerified`),
     the owner-program forgery refusal (`NotSplTokenProgram`), and `is_consensus_proven` fail-closed
     (a `StructureOnly` RPC echo grants nothing). Tested both polarities by default in
     `bridge/tests/solana_holdings.rs`.
   - `dregg-governance/src/holding_weight.rs` — `grant_weight` (the ed25519 owner→voter binding,
     snapshot slot, per-`(poll, token_account)` no-double-count nullifier), the decision routed
     through the verified Lean core via FFI (Lean-first, no Rust fallback for the verdict).
   - `metatheory/Dregg2/Bridge/ProofOfHoldings.lean` — `grantWeightCore_eq_grantsWeight` (the
     `@[export]`ed core realizes the spec) and `weight_backed_and_noncustodial` (granted weight is
     backed AND custody is definitionally preserved), axiom-clean.

   Custody never moves: no vault, no lock, no wrapped token. The lock/mirror path
   (`docs/deos/TOKEN-MIRROR-BRIDGE.md`) is retained as the *exception* — value-import / slashable
   bond — not the way you participate. The CredentialGate presentation shape (ring + predicate +
   nullifier) remains the right envelope for the *EVM* holdings source (item 4); its issuer would
   upgrade from federation-attested to chain-proven the same way. Residuals on the built primitive:
   the live-feed wire-format adapter, the in-circuit fold (`SOLANA-SUCCINCT-WRAPPER.md`), and the
   FFI splice (wired-but-staged) — see `PROOF-OF-HOLDINGS.md`.
2. **One engine** (weld): reconcile the two `VoteEngine`s (collective-choice's executor-backed one
   is the keeper; `dregg-governance`'s constitution/auto-enact face plugs onto it) and wire to the
   node so participation is networked, not in-process.
3. **One identity** (weld): passkey-custody keys as first-class electorate members (the demo
   already proves the mechanics; make it a library, not demo-page glue).
4. **One tally** (weld): EVM-side votes (gate) aggregate into the in-protocol tally as bridged
   ballots rather than a parallel Solidity counter — or retire on-EVM tallying and keep EVM as a
   proof-of-holding source only.
