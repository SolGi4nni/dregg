# The dregg launchpad — verify the sale yourself

*A token launchpad where the three ways launches rug retail — sniping the first block,
hiding insider supply, and draining the liquidity — are **impossible by construction**, not
guardrails a platform promises. Every number a buyer sees, they recompute from the chain
themselves. It's a real Solidity contract (71 passing adversarial tests, an independent audit
that found and fixed a real bug), and its header already names **Robinhood Chain** as a deploy
target. This is the partner-facing pitch; the mechanism design is `DREGG-LAUNCHPAD-DESIGN.md`.*

---

## In one paragraph

Most launchpads are a casino where the house, the insiders, and the bots can all see your cards.
The dregg launchpad removes the cards from the table. A launch is a **sealed-bid batch auction
that clears at one uniform price** — not a bonding curve — so there is no first block to snipe
and no ordering edge to buy. The token is **minted once, to a disclosed cap, with no second
mint door**. The liquidity graduates into a pool that **cannot be drained below a disclosed
floor**. And the whole launch emits a **receipt a buyer verifies against the contract itself** —
not "trust our fair launch," but "here is the launch, check it."

The one-line difference: every other launchpad's anti-abuse feature is, by the platforms' own
words, a *mitigation* — pump.fun says its guardrails "do not eliminate market risk" and its
anti-snipe is "not a guarantee of fairness." On dregg the three dominant abuses aren't settings
that can be tuned or turned off; they're **properties the contract can't express a way around**.
A competitor can copy the slogan. It cannot copy a receipt you check against its own bytecode.

---

## Why now

Robinhood Chain went live July 1, 2026 (an Arbitrum-Orbit L2, permissionless, Uniswap and
friends already deployed) and immediately became a memecoin venue — "built for tokenized
stocks, memecoins took over." Within two weeks the dominant launchpad (NOXA/Pons, ~75% of
deployments, ~$12M in fees) **went dark — stopped accepting launches and lost control of its
domains.** The premier "fair-launch" alternative is barely used. A 2025 Solidus Labs study found
**~98.6%** of pump.fun tokens showed rug / scam / pump-and-dump characteristics.

The gap that just opened isn't for a faster bonding curve. It's for a launchpad where
**fairness is checkable, not promised** — on the exact chain where the last leader just vanished.
That's the one launchpad thesis dregg is built to carry: its whole posture is *verify me, not
trust me*.

---

## What actually runs today

This is a real contract with a real test suite and a working front end — reproducible on any
machine right now:

- **The contract** — `chain/contracts/launchpad/` — a 718-line `DreggLaunchpad` plus a
  hard-capped one-shot-mint token, a floored constant-product pool, a permissionless refund
  backstop, and pluggable clearing-attestor and deployer-gate arms. It enforces the full
  lifecycle on-chain: register → sealed commit → reveal → uniform-price clear → settle →
  graduate.
- **71 adversarial tests pass** (`forge test`, 6 suites, 0 failing): hidden-supply reverts,
  no-peek and no-late-switch on sealed bids, verified non-drop clearing permutation,
  no-second-mint-door, solvency-drain reverts, creator vesting-lock enforced, the timeout-refund
  disjoint window, the committee-attestor signature discipline and its fraud-proof slash, the
  Groth16 proof-attestor discipline (a valid wrap-proof attests; a forged or unbound one
  refuses), and **the audit's permanent-loss exploit test recovering the trapped escrow.**
- **A working web app + browser extension** drive the *real* contract with the user's own
  wallet (`launchpad-web/`, `extension/`). A local end-to-end gate deploys the contract to a
  throwaway chain and runs a full honest launch plus the adversarial reverts against the
  deployed bytecode. In the reference run the book clears at one uniform price, the sale fills,
  the below-clearing bidder fills **zero**, the pool graduates solvent, and a drain below the
  floor **reverts**.
- **The receipt is the product.** Each launch produces a static, self-contained page where the
  clearing price, the sealed book and its fills, the disclosed schedule (with its commitment
  hash recomputed and matched on the page), and the pool reserves all re-derive from chain
  state. It's the shareable proof-of-fairness a buyer inspects.

---

## The three rugs, and why they can't happen here

| How launches rug retail | Why it can't happen on dregg | How sure we are |
|---|---|---|
| **Snipe the first block / front-run** | One uniform clearing price means there is no earliest block to win and no time-priority edge — the value of ordering is zero. Sealed commit→reveal hides bid content on top. | Machine-checked in Lean (`uniform_price_no_arbitrage`), enforced + tested on-chain |
| **Hide insider / second-mint supply** | The token mints exactly once, to the disclosed cap, and there is no second mint door in the code. Supply that closes is a registration requirement. | Machine-checked in Lean (`execMintA_iff_spec`, a full post-state biconditional over the real kernel) **and** symbolically proven on the compiled token bytecode; enforced + tested on-chain |
| **Drain the liquidity (the classic rug)** | Graduated liquidity is pool-owned with a disclosed floor the reserves can never cross; there is no creator-withdrawal door. | Machine-checked in Lean (`pool_solvent_forever`) **and** symbolically proven on the compiled pool bytecode; enforced + tested on-chain |
| **Trap funds with no recovery (rug-by-liveness)** | If a launch never clears, every committer takes a permissionless full refund once the window elapses; the clear and refund windows are disjoint, so the worst case is stall-then-refund. | Built + tested (this is the vector the audit found a hole in — now fixed and pinned) |

Two more, graded honestly because they're real and *not* fully closed: a team can raise fairly
and then **walk away** (the "soft rug") — the contract can't force anyone to keep shipping; a
disclosed-vesting violation is disincentivized by a holder-compensating conduct bond whose
launch wiring is **designed, not yet written**. And a **corrupt clearing attestation** is bounded
by an on-chain fraud proof (a committee that signs a wrong-price or non-descending clearing gets
slashed and the launch falls back to the refund path) — a corrupt quorum can misallocate within
bounds but cannot over-mint, drain, or over-charge.

---

## The assurance behind the claim

The "impossible by construction" claim isn't one piece of evidence — it's four kinds that
converge:

1. **The mechanism is proved in Lean.** The fairness properties are machine-checked theorems in
   the metatheory, axiom-clean (no hidden assumptions, no `sorry`). The strongest is the mint
   biconditional — a mint commits *if and only if* the disclosed, issuer-authorized spec holds,
   with every other kernel field pinned unchanged. The uniform-price and pool-solvency theorems
   are real fold-invariants over the market model.
2. **The contract is re-checked symbolically over its own compiled bytecode.** Both load-bearing
   invariants — the token's hard-cap / single-mint and the pool's never-drain-below-floor — are
   proven with a symbolic-EVM tool over the *real compiled bytecode*, all inputs symbolic (token
   4/4 checks, pool 3/3, plus a reentrancy-safety check). Each carries a mutation canary: flip
   the property and the tool produces a counterexample, so the proofs aren't vacuous. It's
   symbolic execution within a bounded call depth — strong evidence over all inputs in the bound,
   not an unbounded proof.
3. **An independent adversarial audit found a real bug — and we fixed it.** A hostile external
   auditor (a frontier reasoning model, run at maximum effort) found a genuine permanent-loss
   trap: a bidder who committed escrow but never revealed could be locked out of it once a
   launch cleared. It's fixed (an unrevealed committer now settles as a full refund), pinned by
   a test that fails before the fix and passes after. The audit's verdict otherwise: no theft,
   rug, second-mint, pool-drain, reentrancy, or signature vector.
4. **The known rug doors are structurally absent.** We dissected real historical rugs — proxy
   `upgradeTo` swaps, whitelist sell-blocking honeypots, privileged team-vault withdrawals,
   owner-`mint` inflation — and checked each door against our source. The forensics are in
   `RUG-FORENSICS-VS-DREGG.md`.

---

## It works without dregg — that's the point

A launch does **not** depend on a live, stable dregg. Custody is entirely on the public chain:
the escrow, the one-shot mint, and the un-drainable pool are enforced by contract code dregg
cannot alter, and **dregg never holds a user asset.** A dregg re-genesis, key rotation, or total
outage can do exactly *nothing* to a launch's funds.

So **a public launch needs zero dregg in the loop.** A stranger with a browser and a testnet
wallet can register a launch, let the sealed windows elapse, and have every buyer verify the
receipt against the contract — clearing recomputed on-chain, no dregg node anywhere. The private
dregg engine is an *upgrade* (a real cryptographic clearing attestation, then shielded bidding),
not a prerequisite. That's the most important sentence in this doc: **the fundable product runs
standalone, today.**

---

## Honest scope — what the proof does and doesn't cover

The honesty *is* the product, so it's stated plainly and it stays.

- **Not deployed with value at stake.** The contract passes its tests and its gate against a
  local chain and dry-runs cleanly against a public testnet. It is **one command from a live
  testnet launch** — but that command hasn't been fired, and a mainnet deploy carrying real
  funds is a separate, security-reviewed step with a production proving ceremony (the current
  proof arm rides a single-party dev ceremony — fine for a demo, not for value).
- **"Provably solvent" means never-drains-to-zero, not price protection.** The floor is a
  disclosed fraction of the seed; the rest can still exit through ordinary priced swaps. A sell
  wave can crater price toward the floor. Solvency ≠ no-loss.
- **The soft rug is real.** A team can raise fairly, take its fairly-earned proceeds, and
  abandon the project. The contract makes the *mechanics* non-rug-pullable and the on-chain
  conduct publicly replayable; it can't make a bad team good or a bad token valuable — and it
  says so.
- **Symbolic ≠ unbounded.** The bytecode proofs are symbolic execution within a bounded call
  depth — strong evidence over all inputs in the bound, not an unbounded inductive proof. The
  full-launchpad escrow-conservation proof is specified but not yet run.
- **The ZK clearing attestor is not yet production-trustless.** It works, but on a dev proving
  key, and the "this proof is *this* launch's clearing" binding is currently a trusted assertion
  (a corrupt binder can only stall→refund, never misprice, because price is recomputed
  on-chain). A production ceremony and a price-carrying proof are the named next steps.
- **Out of scope, named.** Sybil uniqueness is an identity-layer problem. Wash-for-attention is
  detection, not prevention. Regulatory / KYC / securities exposure — especially anything
  pairing against tokenized stocks — is legal-and-BD work no theorem touches.

---

## The Robinhood Chain hook

The contract's own header names **Robinhood Chain (Arbitrum-Orbit L2, chainId 46630)** as a
deploy target — the launch mechanism is standard EVM (native-ETH quote, `keccak256`, no exotic
precompiles), so it drops onto any Orbit L2. *This is a target the contract names, not a
partnership or listing; "the next pump.fun on Robinhood" is a business bet, not an engineering
claim.* Base-Sepolia (84532) is the equivalent standard-L2 target for a first public demo.

There's a real composition here worth naming: Robinhood's **Stock Tokens are standard,
transferable ERC-20s**, so a graduated pool can be priced against a *tokenized stock* instead of
the gas token — "launch a coin, graduate it into a pool priced in a real stock, and every number
checkable." Nobody on the chain is pairing coins against stocks yet. That's a differentiated
product on top of the verifiable-fairness core — and, like all of the above, it's an honest
opportunity, not a shipped feature.

```
# ⚠ EMBER RUNS THIS — the outward broadcast step. Prepared + dry-ran, NOT fired.
export DEPLOYER_PRIVATE_KEY=0x<funded key>
forge script script/DeployLaunchpad.s.sol:DeployLaunchpad \
    --rpc-url base_sepolia --broadcast --verify        # or: --rpc-url robinhood_testnet
```

---

## See also

- `docs/deos/DREGG-LAUNCHPAD-DESIGN.md` — the deep mechanism design + the abuse→antidote table with file:line citations.
- `docs/deos/LAUNCHPAD-OPPORTUNITY.md` — the moment + the buildable-now-vs-BD split.
- `docs/deos/RUG-FORENSICS-VS-DREGG.md` — the dissected rug doors vs our contracts.
- `docs/deos/LAUNCHPAD-CONTRACT-AUDIT.md` — the independent audit + the confirmed bug + the fix.
- `chain/contracts/launchpad/` — the EVM realization; `chain/test/DreggLaunchpad*.t.sol` (71 tests, 6 suites); `chain/formal-verification/` (the symbolic proofs); `chain/script/DeployLaunchpad.s.sol` (the one-command deploy).
- `launchpad-web/` — the product layer driving the real contract; `gate/run-gate.sh` (the e2e gate), `gate/make-receipt.sh` (the static verifiable receipt).
