# The protocol-native economy — from mock-custodial to conserved effects

*Design doc. The path from the pragmatic custodial payment bridge that exists today to the
endgame the payment crate itself names: every value flow a conserving move under the kernel's
per-asset value law, with no operator holding user funds. Present-tense what-is for the current
state, imperative for the plan. Maturity labels follow the `docs/TOKENOMICS.md` convention
(**RUNS** — a test/demo exercises it green; **BUILT** — real code, not exercised live end-to-end;
**NAMED** — stub or doc only; **VISION** — design). This doc must not contradict
`docs/TOKENOMICS.md` (the canonical four-role statement); where it touches roles 1 and 4 it
sharpens their maturity, it does not restate their scope. Sibling sources cited inline:
`dregg-pay/src/lib.rs`, `docs/ops/PAYMENTS-GO-LIVE.md`, `docs/deos/COMPUTRON-POLICY.md`,
`docs/deos/DREGG-BOND-DESIGN.md`, `docs/deos/DREX-DESIGN.md`.*

## 1. The through-line

dregg's value law is one kernel invariant: a `Transfer` effect is `LinearityClass::Conservative`,
so per asset Σδ = 0 across any turn the executor admits, and that check holds across app
boundaries because an asset *is* its issuer cell's `token_id`
(`dregg-payable/src/payable.rs:19`, `turn/src/action.rs:1069`). Everything the token economy needs
to do — pay for a run, refill compute, post a bond, pay out a slash — is expressible as one or more
conserving `Transfer`s desugared through the single verified `resolve_pay` router
(`dregg-payable/src/payable.rs:24`). The distance between that endgame and today is **custody**:
the live payment rail (`dregg-pay/`) accepts real value into HD-derived deposit addresses whose
seed one operator holds and sweeps (`dregg-pay/src/lib.rs:18-20`), and it tracks run budgets as an
off-chain sqlite number (`dregg-pay/src/ledger.rs::credit_once`), not a conserved cell balance. The
crate names this gap itself — "the endgame is protocol-native settlement — run budget as a conserved
on-chain `Effect::Transfer` balance, so no operator holds user funds. This backend is the pragmatic
bridge to that" (`dregg-pay/src/lib.rs:56-58`). This doc stages the walk from that bridge to that
endgame: prove the custodial rail earns one real dollar (rung 1), then move the run budget onto the
conserved rail and delete the seed (rung 2), then let a proven market — not a hand-set number —
price compute (rung 3), then open the one genuinely new token sink the design admits (rung 4).

## 2. Current resolution (with citations, maturity-labeled)

**The payment rail is real code, custodial by construction, and unfired on mainnet.**
`dregg-pay` implements four pluggable pieces (`dregg-pay/src/lib.rs:6-20`): a
`DepositAddressProvider` (`HdDeposit`, SLIP-0010 ed25519 hardened derivation `m/44'/501'/index'`
from one `Seed`), a `Watcher` (`MockWatcher` driven / `SolanaWatcher` real, reusing the bridge's
consensus-verified SPL decode), a `CreditLedger` (per-user RUN credits, idempotent per payment
reference over a pluggable store the bot persists via sqlite), and a `Sweeper` — "the custody
point — it holds the seed" (`dregg-pay/src/lib.rs:20`). The dual-asset economics are BUILT: USDC is
fuel drawn by `Treasury::spend_inference_usd`, which fails closed on empty
(`dregg-pay/src/treasury.rs:206`); `$DREGG` is the pile accumulated by `Treasury::record_payment`
(`dregg-pay/src/treasury.rs:139`). **RUNS on mock chains** (`cargo test -p dregg-pay` green,
Discord bot loop wired); the mainnet flip is a deliberate operator env decision and **has not been
made** — no real `$DREGG` has been accepted for a service (`docs/TOKENOMICS.md` §role-1). The
go-live runbook is written and unfired (`docs/ops/PAYMENTS-GO-LIVE.md`).

**The custody it names is real and irreducible on ed25519.** Deriving a deposit address requires
the secret seed — there is no watch-only (xpub) trick (`dregg-pay/src/lib.rs:49-51`,
`docs/ops/PAYMENTS-GO-LIVE.md` §custody). Whoever runs the sweeper can move every user's deposit;
the mitigation is "sweep often → float stays tiny" and running the seed-holding sweeper as a
separate secured service (`docs/ops/PAYMENTS-GO-LIVE.md` §custody). Signer-gated edges (the
liquidity vote, the Jupiter `$DREGG→SOL→USDC` swap, OTC settlement) are BUILT behind an injected
operator signer; `dregg-pay` holds no key, but a live swap still needs a real HTTP transport, the
operator's secured signer, and broadcast (`dregg-pay/src/lib.rs:59-68`).

**The conserved rail the endgame targets already exists and is proven.** `resolve_pay` desugars
`pay(asset, amount, to)` to exactly one `Effect::Transfer` through the shared verified descriptor,
`Signature`-gated, and the same route table serves both the app-framework signed-turn `pay` and the
SDK metered gateway charge — "the SAME conserving `Transfer`, not a parallel hand-rolled effect"
(`dregg-payable/src/payable.rs:16-30`). The kernel enforces per-asset conservation on every
admitted `Transfer` (`turn/src/action.rs:1069`). This is the rail run budgets must land on; today
they do not — they land in sqlite behind a seed.

**Computron refill (the compute-purchase inflow) is BUILT with a named voucher-binding residual.**
An operator sells computrons out of its own pre-funded cell: `computron_credit` does the
fail-closed conversion (`node/src/relay_service.rs:241`) and `apply_computron_refill` lands it as a
conserving `computron_transfers` entry — "a refill is a transfer, never a mint," pinned by
`computron_refill_accepted_conserves_exactly` (`node/src/relay_service.rs:278`,
`docs/deos/COMPUTRON-POLICY.md` §3). The rate is a hand-set `AssetRatePolicy::rate_micros`, operator-
local, fail-closed default-empty, **no protocol peg** (`docs/deos/COMPUTRON-POLICY.md` §1-2). The
named residual: rung 1 does not verify the external payment — `RefillVoucher`
(`node/src/relay_service.rs:176`) is the operator's own accounting input, safe only because a false
voucher costs the operator its own computrons (`docs/deos/COMPUTRON-POLICY.md` §3).

**The market that would price compute is proven; the rate-discovery weld is designed, not built.**
DrEX rung-2 aggregation (`Market/Aggregation.lean` — faithful, no drop/insert/substitution/reorder)
and rung-1/5 priced clearing (`Market/Priced.lean`, `priced_clearing_keystone`, ledger-realized
through the real executor via `Market/LedgerRealization*.lean`) are **PROVED, axiom-clean**
(`docs/deos/DREX-DESIGN.md` §2). Feeding a cleared price into `AssetRatePolicy::rate_micros` is
DESIGN (`docs/deos/COMPUTRON-POLICY.md` §5, `docs/deos/DREX-DESIGN.md` — VISION for this purpose).

**The bond sink is fully designed, entirely unbuilt.** `docs/deos/DREGG-BOND-DESIGN.md` specifies a
quote-floored two-tranche bond — quote-asset senior carries the deterrence floor, `$DREGG` is a
junior first-loss tranche that never counts toward the floor — riding the existing relay-operator
slash loop (`node/src/relay_dispute.rs`, RUNS in test). Every rung there is **NAMED/VISION**; the
Lean obligations "do not exist yet" (`docs/deos/DREGG-BOND-DESIGN.md` §5-6).

## 3. The target

An economy where no operator can move a user's funds because the protocol never gives it custody.
A user holds bridged `$DREGG` (or computrons) in their own `Payable` cell; they pay for a run, a
subscription, or a compute refill by authorizing a conserving `Transfer` with their own key; the
operator receives value the same way it receives any fee — as a balance in a cell, auditable and
conserved, never as a swept deposit it could have redirected. The run-credit ledger is not a sqlite
row an operator trusts itself to honor; it is the receipt of a Transfer the kernel already
conserved. Compute is priced by a proven market when operators want market rates, and by a sovereign
local quote when they do not — never by a protocol peg. The one place the token is genuinely locked
against future value (the bond junior tranche) is honestly sized and never load-bearing for
security. The custodial HD backend survives only as the pragmatic on-ramp for users who arrive with
raw SPL tokens and no dregg cell — a bridge into the conserved rail, not the rail itself.

The discipline that makes this coherent: **separate what creates genuine token demand from neutral
plumbing, and never narrate plumbing as demand.** Genuine `$DREGG` demand comes from (a) real
service purchase, (b) operators accepting `$DREGG` for compute refills at their local rate, and (c)
the bond junior tranche. The conservation machinery, the fee router, the OTC/swap recycling, the
computron metering, and the DrEX clearing are neutral plumbing — they route value that demand
created; they do not create it. No staking, no burn, no P2E, no protocol fee routed to the token
(`docs/TOKENOMICS.md` §"what deliberately does not exist"); this doc adds no new demand shape except
the bond sink role-4 already admits.

## 4. Staged rungs (smallest-first, each with a gate)

### Rung 1 — one real dollar through the custodial rail (external trigger: the mainnet flip)

The `dregg-pay` mainnet flip is ember-gated; treat it as an external trigger and design the
watch-only → one-payment sequence around it, so that when the flip comes the smallest real revenue
step is a rehearsed procedure, not an improvisation. This rung ships **no new code** — it is the
disciplined firing of `docs/ops/PAYMENTS-GO-LIVE.md` steps 1-3.

*Do:* (1) provision the durable notary key and publish its verifying key out-of-band; (2) run the
**watch-only dry run** — `DREGG_PAY_NETWORK=mainnet`, real RPC, **no sweeper key loaded** — and
confirm the `SolanaWatcher` (consensus-verified, requiring the pinned `WeakSubjectivityAnchor`, not
RPC-trusting) *sees* a real deposit to a derived address and credits the right user, spending
nothing; (3) take **one small real payment** end-to-end: a few `$DREGG` to a derived deposit address
→ watcher credits → one paid `/dungeon` run on real Bedrock under the per-user cap → the MPC-TLS
attestation handed back.

*Gate:* one paid run executed against real inference, with the run's credit idempotent under
`credit_once` (a replayed watcher event credits nothing new — `dregg-pay/src/ledger.rs:308`
`credit_runs_is_idempotent_and_uniform`), and **the sweeper key never loaded during steps 1-3** (the
at-risk balance is only un-swept float, and float is zero until step 4). The revenue is real; the
custody risk is bounded and named. This rung proves the token has service demand at all — the
premise everything above rests on — while conceding the custody it must later delete.

*What it does NOT do:* it does not reduce custody. Enabling the sweeper (`PAYMENTS-GO-LIVE.md` step
4) loads the seed and makes the operator custodial over swept balances. Rung 1 earns the first
dollar on the pragmatic bridge; rung 2 is what removes the bridge's custody.

### Rung 2 — protocol-native run budget: conserved balance, no seed

Move the run budget from the off-chain custodial ledger onto the conserved rail, so a run is paid by
a `Transfer` the *user* authorizes into the operator's cell — deleting the HD seed and the sweeper
from the value path. This is the endgame `dregg-pay/src/lib.rs:56-58` names, staged in two sub-steps
so the asset dependency does not block the mechanism.

*Do (2a — mechanism, internal asset, no bridge value):* a run credit becomes a cell balance. The
user holds a run-budget balance in their own `Payable` cell; spending a run is
`resolve_pay(user_cell, RUN_ASSET, price, operator_cell, …)` — one conserving `Effect::Transfer`,
`Signature`-gated by the user's key (`dregg-payable/src/payable.rs:24`,
`turn/src/action.rs:1069`). The run-credit ledger (`dregg-pay/src/ledger.rs`) becomes a *read* of
the conserved receipt log, not an authority: `credit_once` idempotency is subsumed by the kernel's
nonce/replay discipline on the Transfer turn. Denominate the run-budget asset in computrons or a
dedicated `Payable` asset first — **no bridged value, so no dependence on the open bridge
suspects.** The operator receives runs the same way it receives relay fees today (a cell balance,
`docs/deos/COMPUTRON-POLICY.md` §4), and the seed/sweeper are simply absent from this path.

*Do (2b — asset cutover to bridged `$DREGG`):* once bridged `$DREGG` is a spendable `Payable` asset
(the vault mint, `turn/src/executor/bridge_ledger.rs`), swap the run-budget asset for it. This is a
one-line asset-id change at the `pay` call site because `resolve_pay` is asset-generic — but it is
**gated on the three bridge value-path suspects closing** (finality over-claim, stake-set
completeness, rotation signer binding; P1, `HORIZONLOG.md`, `docs/TOKENOMICS.md` §role-3). Until
then 2b holds real value nowhere; 2a is the shippable mechanism.

*Gate:* an adversarial test, both polarities, that a paid run is a conserving Transfer the operator
cannot have authorized (only the user's `Signature` cap admits it) and that no code path holds a
seed that could move the user's run-budget cell — i.e. `dregg-pay`'s `Sweeper`/`Seed` types do not
appear in the protocol-native run path. Per-asset Σδ = 0 asserted across the pay turn (the kernel
check, exercised). The falsifiable claim: **grep the run-execution path for `Seed`/`Sweeper`/
`DREGG_PAY_SEED` and find nothing** — if custody types are reachable from a protocol-native run, the
rung is not done.

*Migration off the HD backend:* the HD backend does not die; it demotes. For users who arrive with
raw SPL `$DREGG` and no dregg cell, the custodial deposit address remains the on-ramp — but its job
shrinks to "get the user's value into their own `Payable` cell once," after which every run is
conserved and custody-free. The at-risk balance shrinks from "every user's run budget" to "the
one-time on-ramp float of users mid-onboarding," and vanishes entirely for users who bridge `$DREGG`
directly into a cell. This is the honest end-state of `docs/ops/PAYMENTS-GO-LIVE.md` — the sweeper
becomes an on-ramp convenience, not the treasury's custodian.

### Rung 3 — market-priced compute (DrEX sets the rate; the operator keeps the veto)

Replace the hand-set `AssetRatePolicy::rate_micros` origin with a cleared market price, per
`docs/deos/COMPUTRON-POLICY.md` §5 rung-2. The refill *mechanism* (§2's conserving transfer out of
the operator's own cell) is unchanged; only the number's provenance changes.

*Do:* map a refill order type — *sell computron-refill for asset X* / *buy refill with X* — onto the
DrEX exact-book matcher's `(offer_asset, want_asset)` pairs, entering the aggregated book under the
PROVED rung-2 aggregation theorems so an operator cannot be front-run out of the book it quoted into
(`docs/deos/DREX-DESIGN.md` §2, `Market/Aggregation.lean`). The priced clearing
(`Market/Priced.lean`, `priced_clearing_keystone`, conservation ledger-realized) clears crossing
offers; the fill price *is* the discovered rate for that instance. Feed the cleared price into
`AssetRatePolicy::rate_micros`; **the table's `enabled` bit and fail-closed default remain the
operator's local veto** — DrEX discovers the number, the operator still chooses to accept it
(`docs/deos/COMPUTRON-POLICY.md` §5). Still no peg: a clearing instance binds only its participants;
different operators clear at different prices, no global constant emerges by construction.

*Gate:* a cleared refill fill lands as the same conserving `apply_computron_refill` transfer
(`computron_refill_accepted_conserves_exactly` still holds — the settlement leg is unchanged), and a
disabled/absent policy row still refuses a cleared fill (the sovereign veto bites: a cleared price
the operator did not enable credits nothing). The two teeth prove the market sets the *rate* without
touching the *settlement discipline* or the *operator's sovereignty*.

*Dependency, stated plainly:* rung 3 also requires the voucher-binding residual closed — a cleared
fill must observe a REAL deposit, not an operator-trusted `RefillVoucher`
(`docs/deos/COMPUTRON-POLICY.md` §3, §5). With rung 2 landed, the natural binding is the
protocol-native pay-in itself: the user's conserving Transfer *is* the real deposit, so the voucher
residual and rung 2 close together.

*Demand honesty:* computrons are neutral plumbing — the metering unit, not the token
(`docs/TOKENOMICS.md` §"computrons are not the token"). Rung 3 creates `$DREGG` demand **only insofar
as operators choose to accept `$DREGG` as a refill asset** at their local rate. It is not a peg and
must never be narrated as "the token powers dregg compute" — that claim is unsupported at HEAD
(`docs/TOKENOMICS.md`) and rung 3 does not make it true; it makes `$DREGG` *one accepted asset among
several* at operator-set, market-discovered rates.

### Rung 4 — the `$DREGG` bond junior tranche (the one genuinely new sink)

Ship rung 1 of `docs/deos/DREGG-BOND-DESIGN.md` §6: the two-tranche bond on the existing relay-
operator slash loop, senior computron-denominated exactly as today, junior `$DREGG` posted via
`resolve_pay` as a first-loss forfeit.

*Do:* extend the bond cell with a junior `$DREGG` holding (a `Payable` holding posted by
`resolve_pay` — one conserving Transfer, `dregg-payable/src/payable.rs:24`); extend
`SlashPlan`/`SlashPayout` to a per-asset vector with the **proportional junior-forfeit rule**
(`seized_junior = min(junior_amount, ⌊junior_amount × seized_senior / slashable_senior_headroom⌋)`,
integer arithmetic, **no price input**); emit the junior leg from `build_slash_turn` as a third
conserving Transfer to the remainder cell (`docs/deos/DREGG-BOND-DESIGN.md` §4, §6 rung 1). **All
internal, no bridge, no oracle** — the junior tranche at this rung is pure first-loss forfeit.

*Gate:* adversarial tests, both polarities (`docs/deos/DREGG-BOND-DESIGN.md` §6 rung 1): (i) a
conviction seizes senior penalty + proportional junior, per-asset conservation asserted (restitution
+ remainder = seized, per asset); (ii) an acquit touches neither tranche; (iii) junior forfeit
capped at `junior_amount`; (iv) **a `SlashPlan` constructed with a price argument does not compile**
(the oracle-independence obligation's Rust shadow — the slash path stays a pure function of cell
state + verdict). The forfeit tooth is real from day one.

*Demand honesty:* this rung — and only it in this whole doc — creates a *new* token-demand shape:
operators acquire and lock `$DREGG` to buy operating headroom (the rung-2 tier of the bond design)
and stand to forfeit it on proven misconduct. It is staking-*shaped* (acquire, lock, slashable)
without staking's lie: no yield, no emission, no pretense the locked tokens secure the deterrence
floor (the quote senior does that). Demand is `Σ over operators (junior posting)` and is **zero if
nobody runs bonded services** (`docs/deos/DREGG-BOND-DESIGN.md` §7). The standing anti-theater rule
carries: if a future iteration proposes letting the junior tranche count toward the deterrence floor
"at a conservative haircut," that is the rejected all-token-bond design wearing a coat — the
correlation argument (a bond loses value exactly when the misconduct it polices occurs) is the
standing falsifier (`docs/deos/DREGG-BOND-DESIGN.md` §1, §7).

## 5. Dependencies on other tracks

- **The bridge value-path suspects (P1, `HORIZONLOG.md`, `docs/TOKENOMICS.md` §role-3).** Rung 2b
  (bridged `$DREGG` as the run-budget asset) and rung 4 rung-3 (external USDC senior,
  `docs/deos/DREGG-BOND-DESIGN.md` §6) both hold real bridged value and are **gated on these closing**.
  Rung 2a (internal asset) and rung 4 rung-1 (computron senior + `$DREGG` junior, no bridge) do not
  touch bridged value and proceed independently. This is the load-bearing sequencing decision: the
  *mechanisms* ship on internal/mirror assets before any *real external value* rides them.
- **DrEX rung 5 substrate (PROVED, `docs/deos/DREX-DESIGN.md` §2).** Rung 3's rate discovery rides
  the priced-clearing keystone and rung-2 aggregation, both already proven axiom-clean. What rung 3
  adds is the refill-order → `(offer_asset, want_asset)` mapping, not new market theory.
- **The Payable rail + kernel conservation (PROVED/BUILT, `dregg-payable/src/payable.rs`,
  `turn/src/action.rs:1069`).** Every rung's value move is a `resolve_pay` desugar to one conserving
  `Transfer`; this doc rides that rail and does not extend the kernel. No rung here is a kernel
  change.
- **The slash loop (RUNS in test, `node/src/relay_dispute.rs`).** Rung 4 extends `SlashPlan`/
  `SlashPayout`/`build_slash_turn` to per-asset; the referee, floor-cap, and restitution-bound
  machinery are reused, not rebuilt.
- **The Lean obligations for the two-tranche plan (NAMED, `docs/deos/DREGG-BOND-DESIGN.md` §5).**
  Rung 4's Rust ships against unit tests; the five Lean obligations (per-asset conservation,
  no-seizure-beyond-bond, restitution-quote-only, oracle-independence, deterrence-floor preservation)
  land with the storage-template metatheory as a follow-on, not a blocker for the Rust rung.

## 6. Risks and the load-bearing falsifier

**The load-bearing assumption is that a run payment can be made non-custodial without losing the
onboarding path.** The whole design's claim to "no operator holds user funds" rests on rung 2 moving
the run budget onto a `Transfer` the user authorizes. The risk: users arrive with raw SPL `$DREGG`
on Solana and *no dregg cell*, and getting their value into a cell requires *some* on-ramp that, on
ed25519, has no watch-only trick (`dregg-pay/src/lib.rs:49-51`) — so the custodial deposit address
does not fully disappear; it demotes to a one-time on-ramp. If that demotion is illusory — if in
practice every user routes every run through the custodial address because bridging-into-a-cell is
too costly — then rung 2 has moved a database row but not the custody, and the endgame is unmet.

*Falsifier:* after rung 2, trace the accept-path of a protocol-native run and confirm the custody
types are unreachable — **grep the run-execution path for `Seed`, `Sweeper`, and `DREGG_PAY_SEED`
and find nothing**, and confirm the paid-run turn is `Signature`-gated by the *user's* cell, not the
operator's. If a seed is reachable from a run's settlement, or the operator's signature can authorize
a debit of the user's run-budget cell, the rung is custodial in fact regardless of its framing. The
honest measure is not "we built a conserved ledger" but "no key an operator holds can move a paying
user's balance" — and that is decidable by reading the accept path, not by trusting this doc.

**Secondary risks, each with its named guard:**
- *Bridge value rides a mechanism before the bridge is sound.* Guard: rungs 2a and 4-rung-1 use
  internal/mirror assets; 2b and external-senior are hard-gated on the three suspects
  (`HORIZONLOG.md`).
- *Rung 3 gets narrated as a peg.* Guard: the operator's `enabled` bit is a tested tooth (a cleared
  price the operator did not enable credits nothing); "no global constant emerges by construction"
  is the design property, not a hope (`docs/deos/COMPUTRON-POLICY.md` §5).
- *Rung 4's junior tranche gets promoted toward the deterrence floor.* Guard: the standing
  correlation falsifier — no positive lower bound on crash-conditional token price exists
  (`docs/deos/DREGG-BOND-DESIGN.md` §1), and the oracle-independence gate (a `SlashPlan` with a price
  argument does not compile) makes a regression type-visible.
- *Tokenomics theater — plumbing narrated as demand.* Guard: §3 and every rung's "demand honesty"
  paragraph name exactly what creates `$DREGG` demand (service purchase, operator-accepted refills,
  the bond junior) and mark the rest (conservation, fee routing, OTC recycling, computron metering,
  DrEX clearing) as neutral. The line to hold, present-tense: no staking, no burn, no P2E, no
  protocol fee routed to the token (`docs/TOKENOMICS.md`).
