# OCIP — the DREGG security-provider socket

*DREGG as a security provider you PLUG INTO, not a chain you MIGRATE to.* A
third-party contract, on another chain, consumes a DREGG attestation — it accepts
a trade / settlement / solvency claim only if a DREGG proof attests it — while
keeping its own state and custody. This doc is how a third party integrates.

**Grade.** INTERFACE + a tested DEMO. The socket wraps the EXISTING on-chain
verifier (the VK-epoch registry); the demo consumer genuinely gates on the
attestation (a forged proof is refused by the real BN254 pairing). The proof it
consumes rides a single-party DEV Groth16 ceremony — so this is a demo of the
INTERFACE, not production trust (see §Caveats). Cited to source at HEAD, this
session (2026-07-14).

---

## 0. The shape

```
   ANOTHER CHAIN (e.g. an external L2 / DEX)          DREGG (private, rotatable)
   ┌───────────────────────────┐                      ┌────────────────────────┐
   │ TrustsADreggClearing       │                      │ STARK apex fold        │
   │  (your contract, your      │                      │  → BN254 shrink        │
   │   state, your custody)     │                      │  → gnark Settlement    │
   │                            │                      │    Circuit → Groth16   │
   │  acceptClearing(proof,stmt)│                      └───────────┬────────────┘
   └────────────┬───────────────┘                                  │ wrap proof
                │ verifyStatement(proof, stmt) → bool               │ (25-lane
                ▼                                                   │  statement)
   ┌───────────────────────────┐        wraps          ┌───────────▼────────────┐
   │ DreggVerifier  (SOCKET)    │─────────────────────▶ │ DreggGroth16Verifier   │
   │  VK-rotation-absorbing     │  registry.verifyProof │  Upgradeable (registry)│
   │  entry point               │  (current epoch)      │  epoch→VK, advanceEpoch│
   └───────────────────────────┘                        └────────────────────────┘
```

The external contract depends on the SOCKET, never on a verifying key. A DREGG
VK rotation (a GAP-flip, the nullifier flip, a re-genesis) is a single
`advanceEpoch` tx on the registry and is invisible to every consumer.

Files (all in `chain/`):
- `contracts/socket/DreggVerifier.sol` — the socket (`DreggVerifier`,
  `IDreggVerifier`, the `DreggAttestation` library with the `Proof`/`Statement`
  types + the 25-lane `encode`).
- `contracts/socket/TrustsADreggClearing.sol` — the demo external consumer.
- `test/DreggSocket.t.sol` — 11 tests, both polarities, over the real wrap proof.

It wraps (does NOT reimplement): `contracts/DreggGroth16VerifierUpgradeable.sol`
(the VK-epoch registry) and `contracts/IGroth16VerifierRegistry.sol`.

---

## 1. What a DREGG attestation ATTESTS

The proof is a Groth16(BN254) wrap of the DREGG whole-history STARK apex. Its 25
public inputs are the pinned settlement statement (`IGroth16Verifier25`):

| lanes | field | meaning |
|---|---|---|
| `[0..8)` | `genesis_root` | the DREGG state the chain started from — WHICH dregg instance |
| `[8..16)` | `final_root` | the DREGG state it reached |
| `[16]` | `num_turns` | how many turns were folded into the transition |
| `[17..25)` | `chain_digest` | segment accumulator over every `(old_root, new_root)` pair |

Each lane is a canonical BabyBear residue (`< 2^31 - 2^27 + 1`). A valid proof
attests: *there is a sequence of `num_turns` VALID DREGG turns carrying
`genesis_root` to `final_root` — each turn a sound exercise of a proof-carrying
token over owned state* — i.e. a conserved, rule-abiding state transition. When
the folded turns are a uniform-price clearing (the launchpad statement,
`Market/Optimality.lean`: every winner pays the same clearing price p*, no leg
arbitrages) or a pool settlement, the same proof attests THAT clearing /
settlement was fair / solvent / conserved.

**The socket verifies the PROOF; the semantic is the DREGG statement.** A
consumer trusts DREGG for "what `final_root` MEANS" exactly as it trusts any
security provider for its claim — see §Caveats.

---

## 2. How a third party integrates (three steps)

### Step 1 — import the socket types

```solidity
import {IDreggVerifier, DreggAttestation} from "dregg/socket/DreggVerifier.sol";
```

### Step 2 — hold a reference to a deployed `DreggVerifier`

Deploy one `DreggVerifier` per DREGG instance you expose (constructor takes the
VK-epoch registry address). Every consumer on the chain points at it:

```solidity
IDreggVerifier public immutable socket;
uint32[8] private _trustedAnchor;   // the ONE dregg instance you trust

constructor(IDreggVerifier socket_, uint32[8] memory trustedAnchor_) {
    socket = socket_;
    _trustedAnchor = trustedAnchor_;
}
```

### Step 3 — gate your logic on the attestation

```solidity
function acceptClearing(
    DreggAttestation.Proof calldata proof,
    DreggAttestation.Statement calldata statement
) external {
    // (a) which dregg — the attested genesis must be the one you trust
    require(
        DreggAttestation.packLanes(statement.genesisRoot)
            == DreggAttestation.packLanes(_trustedAnchor),
        "untrusted dregg instance"
    );
    // (b) is it valid — the real BN254 pairing, current VK epoch
    require(socket.verifyStatement(proof, statement), "attestation rejected");

    // ...your gated logic: record the attested final_root, unlock a trade, etc.
}
```

`verifyStatement` returns a bool (fail-closed: false on a failed pairing, an
unset epoch, a codeless registry). It reverts only when the STATEMENT is
ill-formed (a non-canonical lane) — a caller bug, distinct from a forgery. For a
pre-encoded 25-lane vector use `verifyDreggAttestation(proof, uint256[25])`.

**VK rotation is absorbed.** `verifyStatement` always checks the registry's
current epoch — you react to nothing when DREGG rotates. A proof minted under an
old VK stays verifiable at its epoch via `verifyStatementAtEpoch(epoch, …)`.

---

## 3. Is it real? — the tested demo

`test/DreggSocket.t.sol` wires `registry → socket → TrustsADreggClearing` and
runs the REAL 2-turn wrap fixture (`test/fixtures/settlement_groth16.json` — the
same fresh proof verified by the Base 7/7, Solana 2/2, Cosmos 5/5 suites in
`CROSS-CHAIN-SETTLEMENT-REALNESS.md`). **11/11 pass**, both polarities:

- **VALID → ACCEPT** (`test_ConsumerAcceptsValidClearing`): the external contract
  accepts the DREGG-attested clearing and then settles a trade against the
  attested root.
- **FORGED → REJECT**: a tampered proof point (`test_ConsumerRejectsForgedClearing`),
  a lied-about final root (`test_ConsumerRejectsWrongFinalRoot`), and a foreign
  dregg instance (`test_ConsumerRejectsUntrustedDreggInstance`) are each refused;
  nothing is recorded.
- **rotation absorbed** (`test_SocketAbsorbsVkRotation`): after `advanceEpoch` to
  a non-matching VK, the UNCHANGED consumer rejects against the new epoch, while
  the proof stays valid at epoch 0 via the epoch-targeted path.
- socket wiring, codeless-registry refusal, non-canonical-lane revert, and the
  gated `settleTrade` (reverts on a never-attested root) round out the suite.

So yes: *an external contract consumes a DREGG attestation* is a real, tested,
on-chain thing — the real gnark verifier on the accept path, a real forgery
refused by the real pairing.

---

## 4. The multi-chain story

The socket pattern is Solidity here; the SAME shape holds on the other chains
whose real verifiers already exist and verify this same wrap proof
(`CROSS-CHAIN-SETTLEMENT-REALNESS.md`):

- **EVM (worked example)** — `DreggVerifier` wraps `DreggGroth16VerifierUpgradeable`;
  a consumer calls `verifyStatement`. Verified on Base-Sepolia's real pairing.
- **Solana** — the `solana-settlement` BPF program verifies the same proof via
  the `alt_bn128` syscalls (2/2). An external Solana program consumes the
  attestation by CPI-ing / inlining the same verify, gating its instruction on
  the returned bool — the socket is the verify entrypoint + the WHICH-dregg
  anchor check.
- **Cosmos (CosmWasm)** — the `cosmos-settlement` contract verifies via arkworks
  BN254 (5/5). An external CosmWasm contract queries it (or embeds the verify)
  and gates its `execute` on the result.

Solidity is the fully-wired example; the Solana/Cosmos sockets are the same two
checks (WHICH dregg + IS IT VALID) over the same real proof, on verifiers that
already exist.

---

## Caveats (honest)

1. **Dev ceremony ⇒ this is a DEMO of the interface, not production trust.** The
   registry's epoch-0 VK is a SINGLE-PARTY dev Groth16 setup (toxic-waste-known;
   `chain/DEPLOYMENTS.md`). Whoever ran that setup could forge a proof. So a
   consumer wired to a dev-ceremony registry demonstrates the INTERFACE working
   end-to-end; it is NOT a production security guarantee. Production trust needs
   the MPC ceremony (ember-gated) — swap the registry's epoch-0 VK for the
   ceremony VK and every consumer above is UNCHANGED (that is the point of the
   socket).

2. **The socket verifies the PROOF, not "the semantics are what you assume."**
   `verifyStatement` returns true iff a valid DREGG proof of THAT statement
   exists. What `final_root` MEANS — that the folded turns were a fair clearing /
   a solvent pool — is the DREGG circuit + its Lean-proved mechanism. A consumer
   trusts DREGG for that, as it would any security provider. Pin the RIGHT
   `genesis_root` (the dregg instance whose mechanism you audited) and the socket
   binds the proof to it.

3. **VK trust = registry-owner trust.** The VK-epoch registry's setter is
   `onlyOwner`; a malicious owner could install an accept-anything VK. For a
   public instance the owner MUST be governance behind a timelock
   (`UPGRADEABLE-VK-REGISTRY.md`). The socket inherits exactly the registry's
   trust model — it adds no trust and removes none.

4. **This lane does not deploy or broadcast.** The socket + consumer + tests are
   built and green locally; a funded-key broadcast and the ceremony are
   ember-gated (`CROSS-CHAIN-SETTLEMENT-REALNESS.md` §5).
