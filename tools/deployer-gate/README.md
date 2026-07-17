# dregg deployer-gate

**Gate the deployer — privately.** The complementary anti-scam layer for the
dregg launchpad.

Our launchpad already makes the **mechanism** unruggable
(`chain/contracts/launchpad/DreggLaunchpad.sol`): disclosed supply that must
close, a single one-shot mint, sealed commit→reveal, uniform-price clearing
proved in Lean, a creator vesting-lock, and a solvency-floored graduated pool.
The contract *cannot* rug.

This gates the **deployer** — *who* may register a launch at all. Today
`registerLaunch` gates *bidders* (`ILaunchEligibility`, `commitBid` line 274) but
lets anyone deploy. The community insight (ember): *"launchpads should tokengate
or socially gatekeep the deployers; thousands of scam coins would disappear."*

## The mechanism

A deployer must present a **deploy capability**: an attenuable, proof-carrying
token (a real `dregg-macaroon`) that the operator issues only when a pluggable
**gate arm** is satisfied, and that the launchpad re-checks at deploy time. This
is the dregg through-line exactly — *"a turn = the exercise of an attenuable
proof-carrying token over owned state"* — **deploying is a turn; the deploy
capability is the token.**

### The pluggable arms (operator picks one or a combination via a bitmask)

| Arm | What it proves | Why a scammer can't fake it |
|-----|----------------|-----------------------------|
| **Bond** | ≥ `minBond` staked, slashable on a proven rug | Real money at risk, lost on a rug |
| **Interview** (marquee) | Passed a structured interview with a hard-to-convince Opus 4.8 | Can't hype past a skeptic asking real questions |
| **Audit** | Token spec cleared `tools/dregg-audit` | The pipeline actually ran |

### The marquee: the skeptical-Opus interview

*"Convince a skeptical Opus your project is real, prove you did it in
zero-knowledge, then you may deploy."*

`interview/interviewer-prompt.md` briefs Opus 4.8 to be **hard to convince** —
probe for rug-intent, undisclosed/uncontrolled supply, vaporware, evasive
use-of-funds, incoherent tokenomics; refuse to move on hype. It ran for real
against two specs:

- `spec-legit.md` ("Meridian Grid": live pilots, capped disclosed supply,
  published audit hash, 50 ETH slashable bond) → **`runs/verdict-legit.txt`:
  PASS (0.85)**
- `spec-rug.md` ("QuantumYield AI": retained mint, 40% insider unlock,
  guaranteed-2%-daily Ponzi, anonymous + no product) → **`runs/verdict-rug.txt`:
  FAIL (0.99)**

The skeptic passed the real project and failed the rug. A PASS mints the deploy
capability's interview caveat.

## Gate the deployer *without doxxing* (the differentiator)

The interview arm carries only a **hiding commitment** to the verdict (`src/private.rs`).
The launchpad authorizes on membership of that commitment in the trusted
passed-and-attested set — it learns **only "gated: true"**, never the interview
content, the deployer's identity, or which attestation. A scammer cannot produce
the commitment; an honest builder is not KYC-doxxed. This is the same
`View ≈ Sim∘Q` reveal-nothing shape as the rest of dregg.

On-chain, the private arm composes the **real `DreggCredentialGate`**: the
deployer proves an anonymous "interview-passed" credential (ring membership +
`keccak256("interview-passed")` predicate, unlinkable, per-deploy nullifier) —
the gate never learns who they are.

## What is real vs. the named weld

**Real (this PoC):**
- The capability primitive is the real `dregg-macaroon` (HMAC-chained,
  attenuation-only, unforgeable without the issuing key).
- The three-arm pluggable gate + issuance + deploy-time re-check + live-recheck
  tooth (a slashed bond / revoked attestation fails *after* issuance).
- The two interview transcripts are **real** hard-to-convince Opus 4.8 output,
  both polarities — captured **once, offline** (see the honest-scope note below).
- The hiding-commitment reveal-nothing layer (gate sees only "gated").
- The on-chain gate composing the real `DreggCredentialGate` for the private arm.
- The `deploy-gate` CLI (`src/bin/deploy-gate.rs`): the **Audit arm wired
  end-to-end** — `tools/token-factory` registers a verified-safe report hash,
  issues a real macaroon capability, and authorizes it (or is refused
  `NotGated` for a rejected token). File-backed operator state, off-chain.

**Honest scope — the interview arm is NOT live:** this crate has **no LLM client
and no HTTP**. The automated path parses and replays the two frozen transcripts
above; a scammer today would face the *design*, not a fresh skeptical Opus. The
live per-applicant interview (grain-jail / hosted provider) is a named weld
below, and the zkTLS attestation of a live session is doc-and-type-shape
(`src/private.rs::zktls`).

**Named weld (designed, reuses existing machinery):**
- **Full unlinkable ZK** so the gate doesn't even see *which* commitment — reuse
  `DreggCredentialGate`'s anonymous-credential presentation end-to-end.
- **zkTLS/DECO attestation** that the interview truly ran against the real Opus
  endpoint and passed, revealing nothing about the transcript — reuse
  `zkoracle-prove` (the repo's DECO/TLSNotary carrier: `prove_zkoracle`,
  `verify_zkoracle`, `FieldSpan::extract`, `content_commitment`, the STARK leg).
  See `src/private.rs::zktls`.
- The interview-verdict oracle / proof-of-personhood **social source** feeding
  the attester set.

## Run

```sh
# The capability-gate PoC (composes real dregg-macaroon), both polarities:
cargo test -p dregg-deployer-gate           # 14 lib tests + 2 CLI tests

# The on-chain gate (composes real DreggCredentialGate), both polarities:
cd chain && forge test --match-contract DreggDeployerGateTest   # 17 tests

# The Audit-arm CLI (the token-factory gate wire):
cargo build -p dregg-deployer-gate --bins
target/debug/deploy-gate init /tmp/gate.state
target/debug/deploy-gate register-audit /tmp/gate.state path/to/report.audit.md
target/debug/deploy-gate issue /tmp/gate.state --deployer alice \
  --launch-params spec.json --report-hash <hex64>       # refuses if unregistered
target/debug/deploy-gate authorize /tmp/gate.state --deployer alice \
  --launch-params spec.json --capability <token>        # AUTHORIZED / refused
```

## The launchpad hook — LANDED

`DreggLaunchpad.registerLaunch` now enforces the gate, mirroring the bidder gate
at `commitBid`:

```solidity
bytes32 paramsHash = keccak256(abi.encode(s));
if (address(deployerGate) != address(0) && !deployerGate.authorizeDeploy(msg.sender, paramsHash, capability)) {
    revert DeployerNotGated(msg.sender);
}
```

The gate is **pinned at construction and immutable** (`new DreggLaunchpad(gate)`;
`address(0)` = permissionless deploy) — a launchpad's deploy policy is a public
fact of that deployment, not a switch an operator can flip under a live launch.
The launchpad pins only the GATE; which arm satisfies it stays this crate's
pluggable policy. Both polarities in
`chain/test/P0ParityLaunchLoop.t.sol`: a bonded deployer and an audit-cleared
deployer each register; an ungated one is refused `DeployerNotGated`, and a
deployer whose accepted arm the operator disabled is refused too.

Composes with the AI-token-factory lane (`tools/token-factory`): a
**proven-safe token** + a **proven-gated deployer** = the two anti-scam layers.
The audit arm carries the factory's VERIFIED-SAFE bundle hash, and
`attestAuditFor(reportHash, launchParamsHash, cleared)` **binds that clearance to
one disclosed schedule** — an audit obtained for one disclosure cannot be spent
on another (`auditScope`). `attestAudit` remains the unscoped, deployer-level
form.
