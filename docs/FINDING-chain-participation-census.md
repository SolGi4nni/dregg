# Finding: the legacy census — EVM contracts, bridge trust models, and chain-agnostic participation (2026-07-11)

> ⚑ **Dated finding — §1's and §3's headline gaps have since been closed.**
> §1 (2026-07-12): the 25-lane statement is bound end-to-end —
> `DreggSettlement.sol` + `DreggGroth16Verifier25.sol` exist and a real Groth16
> proof settles in Foundry (dev trusted setup; residuals in
> `docs/deos/WRAP-NATIVE-HASH-DECISION.md` §CURRENT STATE). §3's loudest gap:
> `eth-lightclient/` is a real Altair sync-committee light-client verify core —
> blst-based BLS12-381 aggregate signature verification over the 512-validator
> committee plus the SSZ Merkle committee-rotation branch
> (`eth-lightclient/src/lib.rs`), with Base modules beside it (`base.rs`,
> `base_fault_proof.rs`) — so "no BLS12-381 verification exists in-tree" is no
> longer true. The findings below record the pre-close state that drove that
> work; §3's table is a snapshot, not a live assessment.

Three parallel file:line-grounded sweeps (contracts vs proving stack; governance/voting/passkeys;
bridge trust models) answering: what is legacy, what needs vast upgrading, and what is missing for
(a) no-wrap multi-chain, (b) non-custodial voting, (c) governance anyone can join from any chain.

## 1. The Solidity layer is pinned to a pre-v11 proof shape (structural, not cosmetic)

The live `WholeChainProof` claim is **25 BabyBear lanes**: `genesis_root8 ++ final_root8 ++
num_turns ++ chain_digest8` (`SEG_ANCHOR_WIDTH = 8` at `circuit-prove/src/ivc_turn_chain.rs:267`,
`SEG_DIGEST_WIDTH = 8` at `:254`, host tooth `:2807-2811`, envelope v3 postcard `:1751-1755`).
At the census date, everything EVM-side encoded the **pre-widening 4-scalar model**:

- The settlement interface took 4 scalars *(closed — see banner: at HEAD
  `chain/contracts/IDreggSettlement.sol` pins the 25-lane BabyBear public-input contract in its
  header, and `settle` (`:168`) takes the Groth16 points plus `uint32[8] genesisRoot,
  uint32[8] finalRoot, uint32 numTurns, uint32[8] chainDigest, bytes32 outboundMessageRoot`)*.
  A Groth16 verifier's public-input vector length is fixed by its circuit — a 4-input ABI cannot
  bind a 25-input statement; the widened interface removes that mismatch.
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

- **Fail-open verifier call** *(closed at HEAD)*: the census found both contracts `staticcall`ing
  `verifyProof(bytes32,bytes,bytes)` and checking only success — a staticcall to a codeless
  address returns `(true, "")`, so a misconfigured verifier immutable accepted everything. Both
  contracts fail closed on a codeless verifier at HEAD: `DreggVault` refuses a codeless verifier
  (and settlement client) at construction and again on the verify path (`DreggVault.sol:186-194`,
  `:545-549`), and `DreggCredentialGate`'s constructor does the same
  (`DreggCredentialGate.sol:115-118`).
- **The vault's on-chain Merkle tree is a labeled placeholder**: keccak where notes are Poseidon2
  (self-labeled stand-in, `DreggVault.sol:65`), O(n) full recompute per deposit (`_computeRoot`,
  `DreggVault.sol:576`, self-labeled "in production… incremental"), odd leaves promoted unhashed
  (`:594`). The census's "withdraw() discards the proof's root" defect is closed at HEAD:
  `withdraw` checks the proof's committed root against the recent-root ring buffer
  (`if (!isKnownRoot(proofRoot)) revert UnknownRoot(proofRoot)`, `DreggVault.sol:273-311`) — the
  security path consults the tree.
- **No fee/relayer model**: no relayer fee field; raw low-level ERC-20 `call`. The census's
  solvency/reentrancy gaps are closed at HEAD: `withdraw` is `nonReentrant`, enforces
  `amount <= tokenBalances[token]` (`InsufficientVaultBalance`), and marks the nullifier used
  before any external transfer (`DreggVault.sol:273-311`).
- **CredentialGate is demo-grade governance**: single `admin` key with two-step rotation
  (`proposeAdmin`/`acceptAdmin`, `DreggCredentialGate.sol:134-146`) but no timelock; votes are
  bare `yes/no` uint counters with no proposal
  lifecycle/quorum/weighting/enactment (`:52-53,254-258`); non-standard ERC-721 (no
  transfer/approve/165, caller-chosen tokenId, `tokenURI` never written). The census's
  global-vs-per-(serial,domain,tokenId) nullifier contradiction is closed at HEAD: interface and
  contract agree that the BARE presentation nullifier is the replay key — one presentation mints
  exactly one token (`IDreggCredentialGate.sol:56-64`; check at `DreggCredentialGate.sol:239-241`).
  The contract classifies per-tokenId scoping as UNSOUND under the current proof format (tokenId is
  a caller argument the proof does not bind, so scoping the key by it would allow replay-mints,
  `DreggCredentialGate.sol:26-36`); the global nullifier is the fail-closed design, not a defect.

## 3. Bridge trust models vs the bar ("wraps only exist where you lack proofs")

| Surface | Today | Distance to the bar |
|---|---|---|
| ETH settlement (dregg→ETH) | real proof *design*; Groth16 core absent (`BindingOnly`) | the gnark wrap *(closed — see banner, §1)* |
| Solana inbound $DREGG mirror | threshold-oracle attestation (`solana_mirror.rs:446-455`) | Option-B succinct wrapper |
| Solana consensus-verified path | REAL Tower-BFT verify in Rust — stake-weighted Ed25519 supermajority, bank-hash recompute, PoH segment (`solana_consensus.rs:286-343`) — but off-circuit, re-executing-validator grade | fold into an AIR (the multi-month item, `SOLANA-SUCCINCT-WRAPPER.md:160-166`) |
| ETH/Base inbound deposits | RPC `finalized`-tag trust; Base listener waits **2 confirmations** (`chain/src/listener.rs:85-96`) | sync-committee BLS + MPT proof *(closed: `eth-lightclient` carries the BLS12-381 verify — see banner)* |
| Midnight | inbound: federation observes GRANDPA finality via WS-RPC; outbound: 2-of-3 attestation upgraded to 1-of-N watchtower fraud-proof (`midnight_verified.rs`); mirror-tree hash still a BLAKE3 `TODO(mirror-hash)` placeholder (`midnight_inclusion.rs:918`) | GRANDPA light client feasible, not built; wire the real Poseidon |
| Mina | binding-commitment + relay-liveness only (the old Kimchi "Level 2" recursion was VACUOUS and was removed — `mina.rs:154-159`) | in-circuit Ouroboros verify; do not resurrect the vacuous wrap |
| Stripe money-in | **the one deployed inbound proof**: DECO/zkTLS attestation verified in-AIR, Lean-proven (`stripe_deco.rs`) | already at the bar |

Standing constraints on any rebuild (all on record in `BRIDGE-ARCHITECTURE-SOUNDNESS.md`):
every inbound mint must route through the committed consume-once `lock_nullifier` gate (the
double-mint fix, `turn/src/executor/bridge_ledger.rs`); the deployed `proofBind` constraint is
**vacuous** (Lean `True`; the real recursion is not folded into the IVC chain) — closing it is a
gated VK epoch together with the `bridge_action_air` fold and the 4→8-felt lift; proof-to-action
binding is currently executor-side ("Silver"), not in-circuit.

The Solana paradox, as of the census: the hardest chain had the most built (a real consensus
verifier + the weak-subjectivity/stake-rotation template any future light client can copy), while
the easiest chain (ETH: 512-key sync committee) had nothing — BLS12-381 aggregate verification was
the single missing primitive *(closed: `eth-lightclient` — see banner)*.

## 4. Governance / non-custodial voting / passkeys — what exists

- **`dregg-governance`**: `FederationGovernance` wired to the REAL `ConstitutionManager` —
  proposals open polls whose electorate is the constitution's participant set, 2n/3+1 threshold,
  auto-enact on quorum (`src/governance.rs:80-151`, tests in `dregg-governance/tests/teeth.rs`). Plus community
  polls with content-addressed causal `VoteBlock`s (dropped ballot ⇒ root mismatch) and
  non-amplifying liquid delegation. Executor-backed at HEAD (`FederationGovernance` ≡
  `substrate::ExecutorGovernance`); not node-wired.
- **`collective-choice`**: the executor-backed engine on the real `EmbeddedExecutor` —
  WriteOnce ballot cells, monotone tallies, quorum as an `AffineLe` constraint, `Mandate`
  sub-delegation, nullifier set + per-voter blinding tokens (3-depth sybil resistance). At HEAD
  this is THE engine: `dregg-governance`'s crate header declares every face (federation
  self-governance, community polls, story branch-votes) driven through
  `collective_choice::VoteEngine`, with the host ballot box demoted to a non-governance host-side
  derivation aid (`dregg-governance/src/lib.rs:1-58`).
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
proof-of-holdings primitive landed. It now exists, non-custodially, and closes item 1 below;
weld 2's engine-reconciliation half is landed (its node-wiring half remains) and welds 3–4
remain. Primary design note: `docs/deos/PROOF-OF-HOLDINGS.md`.

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
2. **One engine** (weld — reconciliation half landed): the constitution/auto-enact face runs on
   the executor-backed `collective_choice` engine (`governance.rs`/`substrate.rs`, with
   `reactor::GovernanceEnactReactor` auto-enacting on the real `ConstitutionManager`;
   `dregg-governance/src/lib.rs:27-38`). Remaining: wire to the node so participation is
   networked, not in-process.
3. **One identity** (weld): passkey-custody keys as first-class electorate members (the demo
   already proves the mechanics; make it a library, not demo-page glue).
4. **One tally** (weld): EVM-side votes (gate) aggregate into the in-protocol tally as bridged
   ballots rather than a parallel Solidity counter — or retire on-EVM tallying and keep EVM as a
   proof-of-holding source only.
