# The fair batch market — protocol design

*The genuinely-more-fair-than-PumpSwap/Meteora launchpad + secondary market: a permissionless,
batch-cleared, uniform-price AMM whose fairness properties are machine-checked theorems over the
**real EVM bytecode** (Verifereum, HOL4), not tests. This is the design of record; the existing
sealed-bid launchpad (`DREGG-LAUNCHPAD-DESIGN.md`) is the launch half we already built, and this
generalizes its one uniform-price clear into the ongoing market too.*

Design rubric (ember, 2026-07-19): **gas-cheap · maximally fair/transparent · best-possible
assurance · basically-ready · permissionless as much as possible.**

---

## The core idea: one clearing function, everywhere

The whole protocol is a single **batch clearing function** used in two places:

```
clear(orders, reserves) → (uniformPrice, fills)
```

- **At launch:** run it once over the sealed launch bids → the fair-launch clearing (what we have).
- **In the market:** run it every block over that block's orders against the pool reserves → the
  secondary market.

Proving this *one* function fair (uniform price, conservation, solvency, no-ordering-edge) buys the
fairness of both the launch and every subsequent trade. That reuse is the heart of the assurance
story.

## Why this beats a continuous AMM (the fairness argument)

Continuous AMMs (PumpSwap, Meteora, any `x·y=k` you swap against one trade at a time) are
*structurally* a speed game: whoever acts first at the margin wins. That is the same flaw HFT
exploits in TradFi order books, and it is the source of **sandwiching, front-running, and
snipe-the-first-block** on-chain. The fix is not a better curve — it is removing continuous time
(Budish–Cramton–Shim, *Frequent Batch Auctions*). A batch that clears at **one uniform price**:

- **kills sandwiching + front-running** — there is no intra-batch ordering to exploit; everyone in
  the batch gets the same price;
- **kills LVR** (loss-versus-rebalancing, the silent arbitrage tax LPs pay on every continuous AMM)
  — arbitrageurs must compete *inside* the batch, not snipe the block (Canidio–Fritsch);
- keeps real `x·y=k` liquidity + composability (what a launchpad needs) — only the batch's **net**
  imbalance touches the curve; coincidence-of-wants matches buyers against sellers directly.

## Layers

1. **Launch (distribution).** Uniform-price sealed-bid batch auction (built). Optional pro-rata /
   overflow fixed-price mode for pure broad distribution. Both are one uniform clear.
2. **Secondary market.** A batch-cleared uniform-price AMM over the coin/stock reserves. Graduation
   seeds *this* pool directly — same reserves, same curve, cleared in batches from block one.
3. **Sealing.** Orders arrive sealed. Rung 1: plaintext commit→reveal (already proven-shaped). Rung
   2: **fhegg FHE / threshold-decryption** drop-in — orders encrypted, decrypted only at batch
   close, so there is not even a mempool leak to front-run. Same clearing function; the seal is a
   module, not entangled with the core theorem.
4. **Assurance (verifiable-first).** Every contract is bytecode with a **Verifereum refinement
   proof** over the real EVM. Proofs replace tests, and we are obligated to discharge them. Spec
   objects (WETH-example-style): token single-mint-under-cap; the batch clear's **uniform-price**,
   **conservation** (Σin = Σout + fee), **solvency** (reserves never below floor), and the fairness
   theorem — **no order improves by being placed differently in the batch** (the machine-checked
   statement of "you cannot be front-run here").
5. **Gas + permissionlessness.** The heavy work — decrypt, sort, compute the clearing price — is
   done **off-chain by permissionless solvers** (anyone submits a valid clear; the best valid one
   wins). On-chain only *verifies* the submitted clear in O(n) cheap checks (all fills at the
   claimed price? net balances against the curve? conserved?), the pattern the current launchpad
   already uses. A **permissionless fraud-proof** slashes a wrong clear and falls back to the
   refund/no-op path. No admin keys, no privileged solver, no roles.

## Locked decisions (ember, 2026-07-19)

- **Permissionless as much as possible** — anyone launches, anyone solves (best valid clear wins),
  anyone challenges. No admin, no roles, no privileged operator.
- **(A) verifiable-first** — stand up the Verifereum proof pipeline and prove the token invariant
  *before* building the market contracts; design the market contracts to be provable, not
  feature-first. (B) the Solidity product still gets built, at the appropriate time.
- **Batch cadence:** per-block to start (the block *is* the batch — simplest to prove; tunable).
- **Seal:** commit→reveal first, fhegg encryption as an additive rung-2 module.
- **Solver:** permissionless "anyone submits a valid clear, best wins," fraud-proof backstop.
- **Graduation seeds the batch-cleared pool** (one market, fair from block one).
- **Clearing rule:** start with uniform-price-against-the-curve (tractable first proof); architect so
  the FM-AMM / CoW-matching upgrade (net-to-curve, strictly better for LPs) slots in as a later rung.

## Build ladder

- **Rung 0 — pipeline.** Verifereum built against our HOL4; the WETH example reproduced (toolchain
  proven end-to-end).
- **Rung 1 — token proven.** The hard-capped single-mint token: bytecode → abstract spec → discharged
  Verifereum refinement over the real EVM. Establishes the method; our #1 anti-rug invariant, proven.
- **Rung 2 — the clearing function.** Minimal, provable batch-clear contract; prove uniform-price +
  conservation + solvency + no-ordering-edge.
- **Rung 3 — the market.** Wire launch + graduation + per-block secondary clearing over the coin/stock
  pool; a mock stock token; the permissionless solver + fraud-proof.
- **Rung 4 — the seal.** fhegg-encrypted orders as a drop-in.
- **Deploy (ember-gated).** Robinhood Chain testnet; demo frontend at `rhlp.fg-goose.online`; optional
  dregg integration via the extension / node / public devnet when ready.

## Honesty posture (stays)

Every fairness claim is graded at its true resolution: a discharged Verifereum refinement is
sound over the real EVM (the strongest guarantee); anything not yet discharged says so. The pitch
(`LAUNCHPAD-PITCH.md`) upgrades layer-by-layer as rungs land — "Halmos symbolic-bounded" → "proven
sound over the real EVM." No claim outruns the proof.
