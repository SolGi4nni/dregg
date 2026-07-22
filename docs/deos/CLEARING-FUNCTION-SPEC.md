# The clearing function — precise spec

*The one function at the heart of the fair market (`FAIR-BATCH-MARKET-DESIGN.md`): a
uniform-price batch clear against a constant-product pool. Written precisely enough to be
BOTH the Solidity contract's behavior AND the HOL/Verifereum spec we refine the bytecode
against. Used once at launch, then every block for the coin/stock secondary market. Prove it
fair once → both are fair.*

Design posture: the contract does **not compute** the clear (expensive). A permissionless
**solver** submits a candidate clear; the contract **verifies** it in O(n) cheap checks. The
theorems below are stated about the *verified* result, so they hold for whatever a solver
submits — no trust in the solver.

---

## State

Pool reserves before the batch: `Rt` (token), `Rq` (quote = the paired asset — a stock token,
or ETH). Invariant constant `k = Rt · Rq`. Disclosed floors `ft`, `fq` (reserves may never
cross these). Pool fee `φ` (bps), taken on the pool leg (LP revenue).

A **batch** is a multiset `O` of orders. Each order `o = (side, ℓ, q, who)`:
- `BUY`: wants up to `q` tokens, paying quote, at any price ≤ `ℓ` (quote per token).
- `SELL`: offers up to `q` tokens, for quote, at any price ≥ `ℓ`.

Orders arrive **sealed** (commit→reveal, then fhegg-encrypted) so `O` is fixed before any
price is known — no order can react to another.

## The uniform clearing price

At a candidate price `p`:
- in-the-money buys: `ℓ ≥ p`; in-the-money sells: `ℓ ≤ p`.
- book demand `Dbuy(p) = Σ q` over in-money BUYs; book supply `Ssell(p) = Σ q` over in-money SELLs.
- **net order imbalance** `I(p) = Dbuy(p) − Ssell(p)`. `I` is monotonically **non-increasing** in `p`
  (raising the price drops buyers, adds sellers).

Buyers match sellers directly (coincidence of wants); only the **net** `I(p)` touches the pool.
Crucially, the pool participates in the batch **at the same uniform price `p*` as everyone else**
— it does *not* walk its bonding curve one swap at a time (that walk is exactly what leaks LVR to
arbitrageurs). As a price-taker at `p`, a constant-product LP is willing to sell
`g(p) = Rt − √(k/p)` tokens — the amount that brings its *curve-marginal* up to `p` — for `p·g(p)`
quote at the uniform price. `g` is monotonically **non-decreasing** in `p`.

**The clearing price `p*` is where total token demand equals total token supply:**
`Dbuy(p*) = Ssell(p*) + g(p*)`, i.e. `I(p*) = g(p*)`. `I` is non-increasing, `g` non-decreasing ⇒
the crossing is unique. Two cases:
- **flat crossing** — `p*` lands strictly between two order limits: no rationing; the pool sets `p*`.
- **step crossing** — `p*` equals an order's limit and `g(p*)` lands inside `I`'s vertical drop
  there: infra-marginal orders fully fill and the single **marginal** order is **pro-rata
  rationed** by exactly the amount that makes tokens conserve.

A no-order batch clears with `Δt = 0` at the pool's current marginal price. *(Numerically validated
end-to-end — token + quote both conserve to machine epsilon, `k` non-decreasing — in
`/tmp/clearing_check3.py`; the naive "pool walks its curve" formulation fails quote conservation,
which is the bug this uniform-price-pool formulation fixes.)*

**Because the pool trades at `p*`, `k` strictly increases by the captured LVR.** Selling
`Δt = g(p*)` at the flat price `p*` (≥ the pool's average curve price for that move) leaves the pool
at `(Rt − Δt, Rq + p*·Δt)` with `k' ≥ k`. The surplus `k' − k` is the loss-versus-rebalancing a
continuous AMM hands arbitrageurs every block — here it **stays with the LP**. So the batch clear
beats a continuous AMM on *both* sides at once: traders can't be sandwiched (one price), and LPs
keep the arb surplus.

## What the solver submits, and what the contract verifies (all O(n))

Solver submits `(p*, fills[], Δt)` where `fills[i]` is order `i`'s filled quantity and `Δt` is the
pool's token delta (the pool's quote delta is then `p*·Δt` — it trades at the uniform price). The
contract **verifies**, and only these checks are on-chain:

1. **Right-side fills.** Every `fills[i] > 0` BUY has `ℓ_i ≥ p*`; every filled SELL has `ℓ_i ≤ p*`.
   No order trades through its own limit.
2. **No left-on-table (uniform-price optimality).** Every in-the-money order is fully filled
   *except* at the single marginal price level `= p*`, where the shortfall is pro-rata. (An
   in-money order left unfilled while the opposite side or the pool had capacity ⇒ reject.)
3. **Imbalance = pool delta.** `Σ BUY fills − Σ SELL fills = Δt` (the net the pool provides/absorbs).
4. **Pool trades at `p*`, solvent, LP-positive.** The pool's token delta is pinned by its
   price-taker condition — it sells until its *curve-marginal* reaches `p*` — checked **sqrt-free**
   as the integer polynomial `p*·(Rt − Δt)² = k` (net-buy; `p*·(Rt + Δt)² = k` net-sell). Its
   *quote* delta is the uniform `p*·Δt` (not the curve integral), so the pool moves to
   `(Rt − Δt, Rq + p*·Δt)`; verify the new product `k' = (Rt − Δt)·(Rq + p*·Δt) ≥ k` (**`k`
   non-decreasing** — the LVR-capture condition, *stronger* than "stays on the curve": the pool ends
   strictly richer), and `Rt − Δt ≥ ft`, `Rq + p*·Δt ≥ fq`. *(No on-chain `sqrt`; `Δt = g(p*)` is
   pinned by the polynomial. Confirmed equal to the validated model in `/tmp/clearing_check3.py`.)*
5. **Conservation (Σδ = 0 per asset).** All legs at `p*`: quote paid by buyers `= Σ` quote to
   sellers `+ p*·Δt` to the pool; tokens to buyers `= Σ` tokens from sellers `+ Δt` from the pool.
   No token or unit of quote is created or destroyed.
6. **Uniform price.** Every nonzero fill is priced at exactly `p*` (buyer pays `p*·fill`, seller
   receives `p*·fill`).

A candidate failing any check is **rejected** (no state change). A permissionless
**fraud-proof** lets anyone challenge a clear that was mistakenly accepted off a cheaper valid
alternative; the backstop for a block with no valid clear is no-trade (orders refund/roll).

## The theorems (the assurance story — proved over the real EVM bytecode via Verifereum)

Let `clear(O, R)` be *the accepted result* (the unique one passing 1–6).

- **T1 Uniform price.** Every filled order in a batch trades at the same `p*`. *(⇒ no sandwich:
  an attacker cannot buy low and sell high within one batch — there is one price.)*
- **T2 Order-permutation invariance (the crown — "front-running is unconstructable").**
  `clear(O, R)` depends only on the multiset `O`, not on any order of arrival, and each order's
  fill is a function `fill(o, p*)` of its own `(side, ℓ, q)` and `p*` alone — not its position.
  *(⇒ no trader can improve their price or fill by transacting earlier/later, by gas-priority,
  or by reordering. This is the machine-checked statement of "you cannot be front-run here,"
  and it is the one continuous AMMs and order books can never satisfy.)*
- **T3 Conservation.** For each asset, total in = total out (check 5). No inflation, no drain.
- **T4 Solvency.** Post-batch reserves ≥ the disclosed floors, and `k` is non-decreasing
  (check 4). *(⇒ the classic LP-drain rug has no door, over the real EVM.)*
- **T4′ LVR-capture (LP-positive).** Because the pool trades at the uniform `p*`, `k′ ≥ k` every
  batch, and the surplus `k′ − k` is the loss-versus-rebalancing that a continuous AMM leaks to
  arbitrageurs. *(⇒ LPs are strictly better off here than on a continuous AMM — the fairness is
  not paid for by the liquidity providers; they gain.)*
- **T5 Limit honesty.** No order trades through its stated limit (check 1). *(⇒ you get your
  price or better, or nothing.)*
- **T6 No-improvement / individual optimality.** Given `p*`, no order could have been filled
  more favorably by any valid alternative clear (check 2 + the fraud-proof). *(The solver can't
  quietly shortchange you.)*

T2 is the reason this beats PumpSwap/Meteora on the axis that matters: on a continuous AMM the
fill depends on *when* your transaction lands relative to others (the MEV surface). Here it is a
theorem that it does not.

## Reuse: one function, two call-sites

- **Launch:** run `clear` once over the sealed launch bids (all BUYs against the seed reserves)
  ⇒ the fair-launch clearing (generalizes the existing sealed-bid uniform-price launch).
- **Secondary market:** run `clear` each block over that block's orders against the live pool ⇒
  the batch-cleared coin/stock market.

Proving T1–T6 about `clear` once discharges the fairness of *both*. That reuse is why the
verifiable-first cost is bounded: one function, one set of theorems, everywhere.

## Rung path (proof-carrying)

- **R2a** — `clear` as a pure function + the verification predicate (checks 1–6) in the
  contract; T1, T3, T4, T5 (the "local" invariants) proved over the bytecode.
- **R2b** — T2 (permutation invariance) + T6 (optimality) — the harder, higher-value theorems.
- **R2c** — the FM-AMM upgrade (net-to-curve CoW matching strictly improves LP outcomes);
  re-prove T1–T6 under the improved matching. Architected to slot in without changing the
  interface.
