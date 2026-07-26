# The dregg economy, mapped as ONE system — scholar, visionary, critic

*2026-07-26. A read-only audit: no cargo, no build. Every claim is a `file:line` citation or a
direct read of on-disk state. Where I could not verify a runtime fact I say so.*

**The one-sentence verdict.** dregg has, by a wide margin, the best-verified market machinery of any
game project alive — a 90-file, ~37,800-line Lean tower under `metatheory/Market/` with real
per-asset conservation theorems bound to the real executor — and it has **no economy**, because
every surface that would let one human being trade with another is either unadvertised, has no
production caller, or computes an obligation and returns without moving anything.

The proofs are not the bottleneck. They have not been the bottleneck for a long time.

---

## 0. The shape, before the details

There are **three** economies in this tree and they do not touch each other.

| # | economy | unit | where | status |
|---|---|---|---|---|
| **A** | **Operator** — USDC fuel, $DREGG pile, run credits, computrons/DEC | `dregg-pay/`, `discord-bot/src/pay.rs`, `node/src/relay_service.rs` | player-side credit is genuinely careful; **operator-side accounting does not move** (§3.1–3.2) |
| **B** | **Verified market** — DrEX ring clearing, fhEgg batch, Dark Bazaar, Oracle Pit | `intent/`, `fhegg-*`, `dreggnet-market/` | crypto and proofs REAL and running in a real supervisor; **nothing can put an order in** (§3.5) |
| **C** | **Game** — loot, relics, materials, trade-coins | `dungeon-on-dregg/src/loot.rs`, `dreggnet-craft`, `dreggnet-surfaces` | a **single-player shop with canned stock**; the shipped game's loot never reaches it (§3.6–3.9) |

Each is individually good. The two seams between them — *loot → market* and *market → real money* —
are each **one function call wide**, and neither call exists in production.

---

# PART 1 — SCHOLAR: what exists, and what is real versus theatre

## 1. The conservation question, answered properly

There are exactly **four** distinct answers to *"is value conserved, and by what?"* in this tree, and
they are not equally strong.

### Tier 1 — a Lean `@[export]` decides, and an unregistered gate REFUSES

`intent/src/verified_settle.rs:324-337`:

```rust
// Conservation (the Lean `settleRing_conserves`): every touched asset's total supply must be
// preserved across the whole ring. A committed fold cannot leak; surfaced fail-closed if it did.
for asset in touched_assets(legs) {
    let before = k0.total_asset(&asset);
    let after  = k.total_asset(&asset);
    if before != after {
        return Err(VerifiedSettleError::ConservationViolated { asset, before, after });
    }
}
```

The per-leg decider is `settle_leg_authoritative` (`:351-388`, `#[cfg(not(test))]`), calling the real
Lean export `dregg_record_kernel_step` (`metatheory/Dregg2/Exec/FFI/Narrow.lean:398`) and failing
closed on divergence. With **no gate registered the ring is refused, not settled in Rust** —
regression-tested by `intent/tests/settle_fail_closed.rs`.

This is the real thing. It also produced the best engineering line in the tree:
`dreggnet-market/src/lib.rs:825-851` distinguishes *refused* from *never judged*, and tells the
player so —

> `"WIRING BUG in this host, not a problem with the auction: no verified executor gate is
> installed, so the award was NEVER JUDGED — it was not rejected."`

### Tier 2 — a Lean theorem over a model, honestly not ledger-realized

`metatheory/Market/` — 90 files, ~37,793 lines, ~1,496 theorem/lemma declarations. Genuinely proven,
non-vacuous, with two-polarity teeth:

- `clearing_conserves_per_asset` (`Market/Clearing.lean:248`), `mint_refused` (`:433`),
  `unfair_refused` (`:448`), `ringBook_bilateral_stuck` (`:349`)
- `clearedBatch_conserves` (`Market/FhEggClearing.lean:386`), `clearedVolume_optimal` (`:360`)
- `allocation_conserves_at_Vstar` (`Market/FhEggAllocation.lean:476`), `ration_fair` (`:364`)
- `priced_clearing_keystone` (`Market/Priced.lean:240`), `clearing_respects_limits`
  (`Market/Fairness.lean:112`)
- the LAW itself, `Dregg2/Spec/Conservation.lean`: the six-colour `LinearityClass`,
  `conservation_over_monoid` (`:217`), `committed_iff_cleartext` (`:333`),
  `multi_domain_independent` (`:372`) — all `#assert_axioms`-pinned kernel-clean
  (`docs/reference/lean-conserve.md`).

The house's own merciless review (`docs/reference/MARKET-METATHEORY-REVIEW.md`, 2026-07-17) is the
single most valuable document in this repo and I am not re-doing its work. Its findings stand: one
MIRROR (`FhIRAdmissible.lean`), one LAUNDERED conjunction + one VACUOUS tautology
(`InterchainCustody.lean:341`, `:445`), an OVER-NAMED descriptor headline
(`CertFDescriptor.lean:547` delivers ~2.5 of 5 claimed families), and the MPC "joined theorem"
revealing the *suboptimal* balance-threshold clearing while calling it optimal.

### Tier 3 — a Rust invariant that runs, but is not the safety property

`fhegg-solver/src/clearing.rs:208-211`:

```rust
/// True iff the two sides moved equal volume (value-conservation).
pub fn conserves(&self) -> bool { self.buy_volume == self.sell_volume }
```

The crate's own test at `:545-570` proves this a **decoy**:
`assert!(moved.conserves(), "conserves() alone misses the theft")`. The real gate is
`Allocation::validate` (`:224-256`) — per-order caps, individual rationality, and
`buy == sell == V*` rather than merely `buy == sell`. **Any consumer gating on `conserves()` is
exploitable.**

This is the house law *conservation is not correctness* in its purest form: a thief who steals from
one buyer and gives to another conserves perfectly. The same lesson was learned twice more,
independently:

- `intent/src/drex_routing.rs:308-311` — a fixed bug where `minted`/`locked` came from the SAME
  `leg.amount`, so conservation reduced to `x <= x`, *"a constant `true` that admitted an unbacked
  offer (a party locking 1 could claim 1_000_000 and still route)"*.
- `dreggnet-market/src/certified_clearing.rs:580-598` — a tamper that **keeps** conservation and is
  caught only by the LP duality gap.

### Tier 4 — a `HashMap` that "stays balanced by construction"

`dregg_pay::RunBudgetLedger` (`dregg-pay/src/protocol_native.rs:240-244`) is
`HashMap<CellId, u64>`, self-described as *"a read-model of conserved balances… The kernel is the
authority on conservation; this book applies the same kernel-shaped `Transfer` and stays balanced by
construction."* `charge_run` (`:294-337`) is careful — resolve → assert single Transfer → compute
both new balances before writing either → fail closed, with an explicit net-zero self-transfer arm.

**But** `from_balances` (`:251`) is the only way balances enter, and nothing proves the snapshot came
from real conserved on-chain state. It is a conserving book over an unverified opening balance.

### What a conservation tooth does NOT prove

Named once, because everything above rests on it.

1. **Not distribution.** `SumEqualsAcross` says totals match, not that the right person holds them.
   The `fhegg-solver` theft test is exactly this.
2. **Not funding.** `Market/FhEggLedgerBinding.lean`'s `fhEggSettlePre` (`:96-106`) FUNDS both sides
   by construction — "settles" is conditional on funding, not a claim the ledger holds funds.
3. **Not range.** `RangeObligation` (`Dregg2/Spec/Conservation.lean:413`) is a named premise, not a
   discharged fact. Under commitments a prover can satisfy `Σ = 0` with an out-of-range value and
   hide inflation.
4. **Not the price.** Conservation is indifferent to whether the trade was a good idea.
5. **Not that it ran.** This is §3, and it is where almost all of the value in this audit is.

---

## 2. The currencies

| unit | type / id | faucet | sink | store | conserved by |
|---|---|---|---|---|---|
| **$DREGG (real SPL)** | fixed-supply, ~1B, pump.fun | never minted by protocol (POLICY) | DAO-votable, none today | Solana | the SPL. Only `bridge/`, `solana-lock/`, `solana-settlement/` depend on Solana; the latter two are in the root `exclude` list (`Cargo.toml:90`) |
| **$DREGG (treasury pile)** | `u64` atomic | `Treasury::record_payment(Dregg)` (`dregg-pay/src/treasury.rs:139`) on an observed deposit; also once from a slash remainder (`node/src/slash_treasury_mirror.rs:115`) | `withdraw_dregg` via OTC/swap (`otc.rs:245`, `swap.rs:1080`) | sqlite `pay_treasury` | nothing — an operator number |
| **USDC "fuel"** | `u64` atomic | `record_payment(Usdc)` | `spend_inference_usd` (`treasury.rs:206`) — **ZERO production callers** | sqlite `pay_treasury` | nothing |
| **run credits** | `CreditLedger` | `credit()` (`dregg-pay/src/ledger.rs:225`) + admin grant | `debit()` (`:279`) via `commit_paid_credit` | sqlite `pay_credits` — **persistent, and live** | hold-then-commit, `Drop`-released |
| **computrons == DEC** | cell `balance`, signed 64-bit (`cell/src/ledger.rs`) | `/api/faucet` — a real signed Transfer from the genesis-funded faucet cell (`node/src/api.rs:7615-7630`), 1/cell/60s + 10/IP/60s | subscription fee, per-message deposit, GC sweep (`COMPUTRON-POLICY.md` §4) | node ledger + redb checkpoint | **a real transfer, never a mint** — `computron_refill_accepted_conserves_exactly` |
| **operator USD** | `f64` `BudgetLedger` | reservation | true-up | **a per-run JSON file, `remove_file`d after every run** | nothing cumulative exists |
| **protocol-native run-credit** | `RunBudgetLedger` | `from_balances` snapshot | `charge_run` | `HashMap` in RAM | Tier 4 |
| **trade-coins** | *non-fungible notes*; balance = `coins().len()` (`dreggnet-surfaces/src/trade.rs:115-116`) | `seed_trade_stock` at world creation | none | `Rc<RefCell<GameWorld>>`; durable by replay **only if `DREGGNET_WEB_SESSION_DIR` is set** (`dreggnet-web/src/lib.rs:6710-6735`) | real owner-signed `AssetWorld::transfer`; a re-pay with a spent coin is a genuine executor refusal (`trade.rs:227-238`) |
| **loot / relics** | `LootItem { asset_id, rarity, owner }` (`dungeon-on-dregg/src/loot.rs:344-350`) — **no `value` or `price` field** | `LootVault::claim` off a committed run seed | `CraftForge::burn` (`dreggnet-craft/src/forge.rs:503-506`, owner-signed, fires on mint **and** botch) — but see §2(d) | per-session `LootVault` over an in-memory `AssetWorld` (`dreggnet-asset/src/lib.rs:587`, zero persistence primitives) | provenance chain re-verification |
| **echoes** | `ECHOES_SLOT: u8 = 6` (`dungeon-on-dregg/src/meta.rs:133`) | `grant_echoes_at_depth`, gated `FieldEquals(dead,1)` — **only on a real death**; `10 + 5·depth` (`meta.rs:193`) | ⚑ **NONE — by construction.** `echoes` is globally `Monotonic`; `BOON_PRICE` is *"a threshold to REACH, not a cost to spend"* (`meta.rs:184-186`) | sqlite `characters.echoes` (`discord-bot/src/db.rs:866`) — **the only durable game value** | a kernel `Monotonic` + `StrictMonotonic` + `WriteOnce(boon)` tooth |
| **in-scene gold** | a cell slot in the `BAZAAR` scene (`dungeon-on-dregg/src/lib.rs:2819`) | re-seeded to `OPENING_PURSE = 120` at genesis **every run** (`lib.rs:2955`) | `FieldDelta` exact-payment cases (`bazaar_compiled()`, `lib.rs:3009`) | nothing — no gold column in any table, no gold on `CharacterSheet`, no gold in `GameWorld` | real `FieldDelta` teeth; but selling **mints gold from nothing** (in-file, `lib.rs:2775-2795`) |
| **game "$DREGG"** | `*b"dreggnet-trade--DREGG-value-tok!"` (`dreggnet-trade/src/lib.rs:90`) | `fund_dregg` (`:461`) — a bare `credit_balance`, **no matching debit** | none | `HashMap<String, Cell>`, **no serde** | nothing. It is a mint. |

Five observations that matter more than the table.

**(a) DEC and computrons are the same unit, and the product copy says they are two.**
`discord-bot/src/commands/pay.rs:262-267` renders *"The three monies: **DEC** · the on-network devnet
currency… **$DREGG** · the token… **computrons** · the metered unit of compute a turn consumes."*
Same copy at `commands/start.rs:262-264` and `commands/menus.rs:1590-1591`. The code disagrees:
`cell/src/ledger.rs:73-74` names the field `computron_transfers`;
`discord-bot/src/bin/coordinate_live.rs:50` says *"moves the node's native computron balance
(DEC)"*; and `discord-bot/src/commands/explorer.rs:487` prints the computron fee as
`format!("{} DEC", turn.fee)`. **Three monies are presented; two exist.**

**(b) The in-game currency is named `$DREGG`.** `dreggnet-trade/src/lib.rs:87-90` calls it *"the
$DREGG value token… the illiquid service-pile currency"* and its faucet is `fund_dregg`. It is a
`HashMap` with a mint function, sharing a name and a doc-comment with a real SPL that has real
holders. §11 and §14/T1.

**(c) The computron path is the best-designed unit here and nobody talks about it.**
`docs/deos/COMPUTRON-POLICY.md` is the only economics document in the tree that starts from *"what
is a protocol question and what is not"* and answers correctly: no global peg, per-operator
acceptance tables, fail-closed on an unknown asset, and the one thing the protocol fixes is the
conservation discipline. Its §5 (DrEX rate discovery) is the right next rung and is DESIGN.

**(d) ⚑ The one durable game value is deliberately unspendable, and this is a design fork nobody
has named.** `echoes` is the only value in the whole system that a player earns, keeps across a
restart, and uses. It is also, by explicit kernel constraint, **never deducted**. `meta.rs:184-186`:
*"Because `echoes` is monotone this is a threshold to REACH, not a cost to spend."* The talent tree
extends the same shape — `dreggnet-gear/src/talents.rs:104` calls its `price` field *"The accrued-echoes
THRESHOLD (a `FieldGte` floor) the claim requires"*, and `talents.rs:25` reasons explicitly from
`echoes` being `Monotonic`.

That is a good decision for progression (no power-creep, no grind-to-spend, and
`talents.rs:34` records that the *"buy-with-dregg" method default-denies* — a real anti-P2W tooth).
It is fatal for a trade economy, which requires that value *leaves* the holder. **dregg's one
durable game currency is not a currency; it is an achievement score.** A trading economy needs a
second, spendable, non-monotone unit — and choosing to introduce one is an architectural commitment,
not a lane task. See §14/E1.

**(e) The one real sink does not bite on anything a player earned.** `CraftForge` genuinely destroys
its inputs — `dreggnet-craft/src/forge.rs:503-506` is an owner-signed `AssetWorld::burn` that fires
on **both** a successful mint and a botch, with provenance snapshotted first because *"after the burn
the inputs are gone"* (`:501`). But `CraftForge::with_assets` — the constructor that opens the forge
over a real loot ledger — has no non-test caller. Production uses `CraftForge::new()`
(`forge.rs:236`) over a fresh empty `AssetWorld` seeded by `SharedWorld::demo`. **The sink burns
demo materials, correctly and verifiably, and nothing a player rolled.**

---

## 3. ⚑ THE THEATRE INVENTORY

*A number displayed as an accounting fact with no movement behind it. This is the most valuable
section of the audit. There are more than the mandate named, and one of them is worse.*

### 3.1 The treasury fuel gauge cannot move, and the REFUEL alarm cannot fire

`dregg-pay/src/treasury.rs:200-206`:

```rust
/// This is called for EVERY run regardless of how it was paid: a `$DREGG`-paid run
/// still burns USD inference (fuel out) while only the pile grew...
pub fn spend_inference_usd(&self, cost_usd: f64) -> Result<u64, TreasuryError> {
```

**It is called for no run.** Every occurrence in the tree is a test
(`dregg-pay/tests/dual_asset_e2e.rs:125,140,142`; `treasury_swap_flow_e2e.rs:175-293`;
`treasury.rs:260-300`), a doc comment, or the pass-through wrapper
`PayState::treasury_spend_inference_usd` (`discord-bot/src/pay.rs:1216`) whose only caller is
`pay.rs:4298`, inside `mod tests` (which opens at `pay.rs:3025`). The tank is credited by
`poll_and_credit` → `pool.record_payment` → `treasury.record_payment(Usdc)` (`pay.rs:1126`) and
**never drained**. `usdc_balance` is monotonically non-decreasing in any deployed process.

The consequence is not "a number is wrong". It is that **the admin treasury panel is a projection
wearing a gauge's clothes.** `discord-bot/src/commands/admin.rs:809-826`:

```rust
let runs = (fuel_usd / usd).floor() as u64;
if runs == 0 {
    format!("🔴 **REFUEL NOW.** ${fuel_usd:.4} of fuel does not cover even one run at the \
             ${usd:.4} per-run ceiling. `spend_inference_usd` fails closed with \
             `InsufficientFuel`, so real-AI runs will start refusing.")
} else if runs < 20 { ... "🟡 ... low." } else { ... "🟢 ..." }
```

`fuel` never falls, so `runs` never falls, so the light never goes yellow, the alarm never goes red,
and *"real-AI runs will start refusing"* is false in every configuration. Two more user-facing
surfaces repeat the claim: `commands/pay.rs:298` (*"burned per real-AI run; fails closed
(must-refuel) on empty"*) and `commands/admin.rs:831-833` (*"Every run burns USD fuel regardless of
how the player paid"*).

An operator running real mainnet inference would watch a green light while the real money burned
somewhere the code cannot see. This is the repo's own **fail-open gate class**, in the one place
where the units are dollars.

### 3.2 The operator spend on the player's card is a real measurement of a ledger that is deleted

`discord-bot/src/pay.rs:560-581`:

```rust
let seq  = RUN_SEQ.fetch_add(1, Ordering::Relaxed);
let path = self.ledger_dir.join(format!("run-{}-{seq}.json", std::process::id()));
let ledger = BudgetLedger::new(&path, self.usd_per_run);
let result = metered_converse(&ledger, &self.registry, self.backend.as_ref(), request);
let usd_spent = ledger.spent_usd().unwrap_or(0.0);
// Best-effort cleanup of the ephemeral per-run budget file + its lock sidecar.
let _ = std::fs::remove_file(&path);
```

→ `PaidConverse::operator_spend_micro_usd()` (`pay.rs:649`) → `commands/fiction.rs:1292` → the consent
card (`dreggnet-offerings/src/chutes_consent.rs:192`, *"operator spend $0.012345"*).

Be precise about which part is fake. The **number is honest**: a real token count times a pinned
price carrying a graded `PriceSource`, and `usd_to_micro_usd` rounds *up* so a disclosure never
understates (`pay.rs:656`). What is fake is the **accounting**:

1. `run_ledger_dir()` defaults to `std::env::temp_dir().join("dregg-pay-runs")` (`pay.rs:3011-3015`).
   It is a scratch file by design.
2. The ledger is **fresh and zeroed every run**, so the `$20` global ceiling
   (`DREGG_NARRATOR_BUDGET_USD`, `narrator/src/ledger.rs:189`) **does not apply to the paid player
   path at all**. Total operator exposure is `N × per-run cap` with no `N`.
3. `ledger.spent_usd().unwrap_or(0.0)` — a read failure renders `$0.000000` on a player's card as an
   accounting fact.
4. On the Descent path the value is not even printed — it is **dropped**
   (`discord-bot/src/commands/descent.rs:2875-2878` uses `n.text` and `n.provider()` and discards
   `n.usd_spent`). The credit debit is real; the corresponding operator cost is booked nowhere.

The persistent global ledger is real and well-built, and I read it:
`~/.dregg/narrator-ledger.json` holds `total_spent_usd: 0.12272012` over `84 calls`, with per-model
price provenance including an explicit `ConservativeUpperBound` rationale for Haiku 4.5. That is
exemplary. **The paid path bypasses it.**

### 3.3 `/bounty` reports "Bounty Paid" and there is no transfer anywhere

The sharpest instance, and it was not in the mandate. `starbridge-apps/bounty-board/src/lib.rs:295-310`:

```rust
pub fn build_payout_action(cipherclerk: &AppCipherclerk, bounty_cell: CellId) -> Action {
    let paid = field_from_u64(STATE_PAID);
    let effects = vec![
        Effect::SetField  { cell: bounty_cell, index: STATE_SLOT as u64, value: paid },
        Effect::EmitEvent { cell: bounty_cell, event: Event::new(symbol("bounty-paid"), vec![paid]) },
    ];
    cipherclerk.make_action(bounty_cell, "payout_bounty", effects)
}
```

**No `Effect::Transfer`.** The reward itself is also just a field element
(`lib.rs:207-227`, `SetField(REWARD_SLOT, reward_f)`). Yet the Discord surface renders:

- `discord-bot/src/commands/bounty.rs:188` — `.field("Reward", format!("{reward} DEC"), true)`
- `discord-bot/src/commands/bounty.rs:307` — `success_embed("Bounty Paid")`
- `discord-bot/src/commands/bounty.rs:337` — `.field("Escrowed", format!("{} DEC", details.balance), true)`

The last one is the worst: it reads the cell's *real* balance — which nothing ever funded — and
labels it **"Escrowed"**, attaching a custody claim to a number that is zero for the same reason the
reward is a scalar. The option is even labelled in a third unit (`bounty.rs:64`, *"Reward amount
(computrons)"*).

The crate **has** a real value organ — `BountyTreasury::payout`
(`starbridge-apps/bounty-board/src/lib.rs:795-810`, a genuine `Payable` → `Effect::Transfer`). Its
only references outside its own tests are
`starbridge-apps/escrow-market/tests/cross_app_value_flow.rs:173,258`. The Discord path does not use
it.

### 3.4 `/leaderboard` sums inbound only and calls it "top DEC holders"

`discord-bot/src/db.rs:2625-2632`:

```rust
/// Get top holders (by number of faucet claims — proxy for balance in local ledger).
pub async fn get_leaderboard(&self, limit: u32) -> Result<Vec<(String, i64)>, sqlx::Error> {
    let rows: Vec<(String, i64)> = sqlx::query_as(
        "SELECT to_user, SUM(amount) as total FROM transactions GROUP BY to_user ORDER BY total DESC LIMIT ?",
```

Only the credit side of each row is summed; `from_user` outflows are never subtracted. The doc
comment itself admits it is a *proxy*. The command description is *"Show top DEC holders"*
(`commands/social.rs:18`), rendered at `social.rs:137` as `"{medal} **#{}** {user} · {total} DEC"`,
under the reassurance at `social.rs:170-174`: *"Totals summed from the bot's local ledger. Every
transfer behind them committed as a real turn."*

A player who received 1000 and sent 1000 away still ranks at 1000. `from_user = "faucet"` appears as
a competitor. And faucet rows insert with `tx_hash = "faucet"` and no chain receipt
(`social.rs:89-92`), so the "re-check on the chain" affordance skips exactly the rows that dominate
the totals (`commands/tx_recheck.rs:30`).

### 3.5 ⚑ The Dark Bazaar runs a real ZK supervisor over a queue nothing can fill

This is the most surprising finding in the audit, and it is a **wiring** failure rather than a
built-never-used one — which makes it more serious, not less.

The bazaar is **mounted in three production binaries**, all behind `private-bazaar-live`, all
exiting rather than degrading on partial config:
`dreggnet-web/src/bin/dreggnet-web-server.rs:138-181`,
`dreggnet-telegram/src/bin/dreggnet-telegram-bot.rs:192-220`, `discord-bot/src/main.rs:1100-1128`.
The supervisor genuinely runs the proof each tick —
`dreggnet-catalog/src/private_bazaar_service.rs:586-588` → `settle_and_capture` →
`deployment.settle_private_clearing_verified(...)` (`private_bazaar_service.rs:124`) →
`dreggnet-market/src/private_clearing.rs:1020 settle_private_verified`. There is not one `todo!()`,
`unimplemented!()` or `#[ignore]` across `dreggnet-catalog/`, `dreggnet-market/`, `dreggnet-trade/`,
`dreggnet-offerings/` or `circuit-prove/src/dark_bazaar_private.rs`. **This code is complete.**

And `PrivateBazaarSealedIngressQueue::submit` (`private_bazaar_ingress.rs:272`) — the only way a bid
enters — has **zero production callers**. Every caller is in a test module:

```
private_bazaar_ingress.rs:862, 867, 920            (mod tests opens at :736)
private_bazaar_live.rs:1496,1595,1611,1622,1636,1645,1664,1711   (mod tests opens at :723)
```

The module says so itself (`private_bazaar_live.rs:230-234`): *"This is what a production bid
collector holds. It is deliberately not reachable from any frontend action: `OfferingHost` routes
carry Enter and nothing else."* **That bid collector does not exist in this repo.** The only public
affordance the raid offering exposes is a single `Enter`, firing a `TURN_LIST`
(`private_bazaar_live_host.rs:229-263`). A player can open the market. Nobody can bid into it.

Corroborated by disk: a full-filesystem search finds **zero** instances of
`sealed-ingress-v1.queue` (`private_bazaar_ingress.rs:60`) or `finalized-private-bazaar-v3.spool`
(`private_bazaar_worker.rs:36`) — the two artifacts only a real run can produce — and nothing
matching the 64-hex `by-blind/*.binding` shape of `private_clearing.rs:881`. No
`DREGG_PRIVATE_BAZAAR_*` variable is set in any script, Dockerfile, systemd unit or deploy config;
without `DREGG_PRIVATE_BAZAAR_DEPLOYMENT_ID` the deployment resolves `Ok(None)` and every binary
takes the plain `make_app_parts()` branch.

And it is compile-only by explicit policy. `scripts/feature-tiers.tsv:116`:

> `dregg-discord-bot  private-bazaar-live  T3  the opt-in private/proven Bazaar raid.` **`THIS IS
> THE KNOWN WOUND: a verified settling gate shipped inside this feature and was registered nowhere,
> so every settling test in it could not go green on any host. Compiling it is the floor, not the
> fix`**

T3 means *must at least compile* (`.github/workflows/feature-surface.yml:26`), and
`feature-surface.yml:19` names `private-bazaar-live` among 91 features *"fed to rustc by no CI job
at all."*

**Correction to the status docs.** `docs/deos/THE-DARK-BAZAAR.md:59` and
`docs/deos/DREX-TIER-STATUS-2026-07-24.md:188-198` both assert the worker never calls
`settle_private_verified` and the live clearing settles by plaintext bid revelation. **That was
fixed on 2026-07-25** by `4aeba707d` (*"market: the proven private-book relation was reachable only
from tests — the production worker now calls it"*), followed by `2bab1cfe5`, `e2a517cdf`,
`ad88024c8`. Those two docs now understate the bazaar. The missing piece is the ingress *producer*,
not the proof.

### 3.6 The Oracle Pit computes a payout and returns

The best-engineered instrument in the economy tells you itself
(`dreggnet-market/src/oracle_pit.rs:97-99`):

> *"Value does not move here. The pit computes obligations (`pool`, `payout_per_share`, a
> claimant's payout) and stops. Escrow and transfer are the `MarketOffering` /
> `dregg_intent::verified_settle` seam; a public escrow leg would leak position size."*

Everything above that line is real, and genuinely novel:

- a `WriteOnce` subject digest in the `SELLER` register so a live pit cannot be re-pointed (`:14-17`);
- an oracle that is **exact re-execution** rather than a committee vote — `read_verified_run`
  (`:414`) refuses a record whose `seed`/`day_seed` differ, then replays it through
  `NativeDescentOffering::resume_record`, recomputing every `turn_hash`, the post-state and the
  journal root (`:19-31`);
- a frozen `pit_verdict` in `WINNER_SLOT` under `WriteOnce` + `StrictMonotonic(PHASE)`, so a verdict
  cannot be re-announced (`:42-45`, `:1180-1190`);
- positions as BFV ciphertexts under an n-of-n collective key, with the *unbacked* side receiving
  `Enc(0)` so the side itself is hidden (`:926-933`);
- odds as marginal prices of a quadratic cost function (`PitCostMatrix`, `:616`), opened only by
  full-quorum threshold decrypt (`quote()`, `:1013`).

It states its own limits honestly: `combine` refusing `n−1` is an API check not a proof (`:79-85`);
the parties run in one process (`:86-89`); `MAX_POSITION_STAKE = 32` (`:145`) is bounded by the BFV
plaintext modulus, not by economics; and the **run-designation hole** (`:224-236`) — `(seed,
day_seed)` names *the day's world, not a run of it*, so an unpinned pit *"settles on whichever
verified terminal run of that day's world reaches it first, which hands the outcome to whoever
settles rather than to the dungeon."*

It is not in `CATALOG_KEYS` (`dreggnet-catalog/src/lib.rs:551-579` lists 23 keys; `oracle-pit` and
`dark-pool` are absent). `OraclePitOffering::new` is called only from
`dreggnet-market/tests/oracle_pit_descent_market.rs:351` and its own `#[cfg(test)]` mod. Its feature
is T3, and the only script that enables it is the `dark` gauntlet mode —
`scripts/test-gauntlet.sh:97`: *"⚠ These have never executed in CI. Expect real failures; that is the
information."*

A prediction market with real cryptography, a real oracle, real odds — no stake, no settlement, no
positions ledger.

### 3.7 `SHIPPED_KEYS` — the economy is not on any shelf

`dreggnet-catalog/src/lib.rs:551` declares `CATALOG_KEYS: [&str; 23]` — *"the 23 offerings that
EXIST. All mounted, all routable"* — including `market`, `bazaar`, `trade`, `inventory`, `craft`.

`dreggnet-catalog/src/lib.rs:617`:

```rust
pub const SHIPPED_KEYS: [&str; 3] = ["descent", "automatafl", "tug"];
```

`apply_ship_list` marks every other key unadvertised, and *every* shelf — the web catalog page, the
Telegram `/offerings` and `/play` menus, the WeChat menu, the Mini App, the Discord Activity — paints
only `list_advertised_offerings`. The discord-bot reads `is_shipped` directly.

**Not one economic surface is advertised anywhere.** They are openable by URL if you know the key.
This is a deliberate, documented, correct decision — and it settles the question "does the market
have counterparties" before any code question is asked: no player can find it.

### 3.8 `TradeWorld` has no production constructor, and the item cross has no production caller

The type that holds game `$DREGG` wallets and loot notes is constructed **only in tests**. Every
`TradeWorld::new()` / `::with_assets(...)` outside `dreggnet-trade/src` is in a `tests/` file or a
`#[cfg(test)]` helper (`dreggnet-market/src/fhegg_source_binding.rs:619`). It has no `serde` derive
at all.

So `MarketSession::settle_winning_asset` (`dreggnet-market/src/lib.rs:1599`) — the one function where
a game item crosses to a bidder for money — has **zero production callers**:

```
dreggnet-market/tests/descent_asset_bazaar.rs:67,100
dreggnet-market/tests/banked_relic_bazaar.rs:95
dreggnet-market/tests/descent_dark_bazaar_private.rs:190
dreggnet-market/src/fhegg_source_binding.rs:623      (refusal test)
```

And the loop it completes is genuinely good.
`dreggnet-market/tests/descent_asset_bazaar.rs:32-78` runs: a committed run seed → `roll_drop` →
`LootVault::claim` (provenance `verified`) → `TradeWorld::with_assets` → sealed `DarkBazaarOffering`
LIST/BID/BID/SETTLE → `settle_winning_asset` → `lineage_len == 3` (mint → escrow → winner),
`dregg_balance(WINNER) == 0`, `dregg_balance(SELLER) == 90`. The sibling test asserts the correct
refusal when the winner cannot pay, and the loot returns to the seller with provenance intact.

**That is the game economy, and it exists only as an assertion.**

### 3.9 The shipped game mints loot into a vault with one caller, a test — and the inventory is a different ledger

`dreggnet-offerings/src/native_descent.rs:505-517`:

```rust
/// Take the session's loot vault, to hand the LIVE note world on to a market/inventory
/// organ (`vault.into_assets()` → `dreggnet_trade::TradeWorld::with_assets`). The minted
/// notes keep their existing lineage and owner; a consumer must never re-mint them from
/// display metadata.
pub fn into_loot_vault(self) -> LootVault {
```

Sole caller: `dreggnet-offerings/tests/native_descent_banked_relics.rs:407`.

`descent` is one of the three shipped offerings. It mints real provenance-carrying relic notes at
settlement. Those notes die with the session — because the player's *inventory* is a different
ledger entirely. `dreggnet-surfaces/src/world.rs:281-287`:

```rust
pub fn demo(player: impl Into<String>) -> Self {
    let world = SharedWorld::new(player);
    world.seed_craft_bench();
    world.seed_items(&crate::inventory::demo_items());
    world.seed_trade_stock(crate::trade::BUYER);
    world
}
```

Every player's world is a fresh `SharedWorld::demo`. Its ledger is `Rc<RefCell<GameWorld>>`, one per
identity via `PlayerWorlds`. It is simply **not** the `LootVault` the descent run mints into. **Two
disjoint item ledgers, and nothing joins them.**

And its durability is **conditional on an env var**. `resolve_player_worlds`
(`dreggnet-web/src/lib.rs:6710-6735`) attaches a per-identity `FileResumeStore` under
`<DREGGNET_WEB_SESSION_DIR>/players/<blake3(identity)>` — and if the variable is unset or empty it
returns `PlayerWorlds::new()` and the world is RAM-only. Same shape in
`dreggnet-telegram/src/runtime.rs:1816-1819`. The mechanism is real and well-built (store the
reproducible inputs, reopen by replay, per-identity isolation by directory); it is simply off by
default. Note also that nothing serializes an *inventory* — `GameWorld`
(`dreggnet-surfaces/src/world.rs:142`) is `{ forge, player, items, materials, benches, coins }`,
plain in-memory vectors, and `AssetWorld` (`dreggnet-asset/src/lib.rs:587`) contains no persistence
primitive at all.

What *is* unconditionally durable is narrower than it looks: the sqlite `characters` table
(`discord-bot/src/db.rs:866`) carries `xp, level, class, abilities_used, dead, echoes, boon` — **no
gold column, no inventory column**, which `discord-bot/src/character_store.rs:26-28` names as a
follow-up. Descent leaderboard runs are durable and re-verified by replay on boot
(`dreggnet-web/src/descent_store.rs:13-18`), gated on `DATABASE_URL`.

### 3.10 The "market" a player can actually open is a single-player shop

`dreggnet-surfaces/src/trade.rs:53-58`:

```rust
const SELLER:  &str = "seller";
pub(crate) const BUYER: &str = "buyer";
const CUSTODY: &str = "market-custodian";
```

`TradeOffering::open` (`:346-362`) either adopts the player's shared world or stands up a private one
with canned stock and a seeded purse. The player is the seller; the buyer is a constant string.
Prices are a `usize` on `ItemRecord` (`world.rs:98`) set at seed time. The purse is `coins().len()`
and payment is a loop of `price` individual note transfers (`trade.rs:244-256`).

The transfers and refusals are real. **There is no second party, no price formation, and no sink.**

It also bypasses the trustless escrow that exists for exactly this, and says so
(`dreggnet-surfaces/src/trade.rs:28-32`): *"NAMED NEXT: routing the settle through
`dreggnet-trade`'s sealed-escrow `TradeWorld::buy`… once that path surfaces a per-turn
`TurnReceipt` for the Offering seam (today its `Settlement` return carries no receipt…)"*.

### 3.11 There is a complete in-scene shop economy, and it is auto-played

`dungeon-on-dregg/src/lib.rs:2690` opens a whole universe for it: *"A FOURTH UNIVERSE — 'The
Merchant's Bazaar': an ECONOMY (buy / sell) + QUANTITIES"*, and `:2695`: *"the mechanic they all
lacked — **an economy**: a shop where a purse of gold BUYS goods and goods SELL back for gold."*
The scene (`BAZAAR`, `lib.rs:2819`) has real affordances —

```
* [Buy a healing potion for 50 gold]   ~ gold -= 50 ; ~ potions += 1
* [Sell the amber amulet for 120 gold] ~ amulet -= 1 ; ~ gold += 120
* [Pay your way into the counting room] { gold >= 100 }
```

— a real price schedule (`POTION_PRICE=50`, `AMULET_PRICE=120`, `POTION_STOCK=2`,
`COUNTING_ROOM_TOLL=100`, `OPENING_PURSE=120`, `lib.rs:2943-2957`), and real `FieldDelta`
exact-payment teeth compiled into the cell program (`bazaar_compiled()`, `lib.rs:3009`). It is
honest about its own ceiling in-file (`lib.rs:2775-2795`): a real merchant would be a second cell,
so *"the merchant's payments are not debited from a merchant's purse"* — **selling mints gold from
nothing** — and dynamic pricing is named, not built.

Its only reference outside `lib.rs` is `dungeon-on-dregg/src/overworld.rs:127`, as a `Universe`
whose `win_script` (`:130-141`) is a **fixed move list**. The Discord adapter is candid about what
that means (`discord-bot/src/commands/overworld.rs:15`): *"'Clear' auto-plays the location's dungeon
to the win."*

**No human has ever pressed "Buy a healing potion for 50 gold."** The same pattern appears in
tournaments, which **auto-play each qualifier's run** and whose own doc names prize settlement as
deliberately absent (`dreggnet-tournament/src/lib.rs:53`: *"glory, not yield … (no P2E)"*).

### 3.12 Inert crates and modules

Three sizable pieces are compiled and never called:

- **`dungeon-on-dregg/src/dialogue.rs`** — 960 lines, the Lantern-Keeper's Vigil, NPC
  disposition/menace/topic-unlock as executor-gated cell state. `grep -rn "dialogue::"` returns
  **not one hit** in the tree. Every mention is a doc comment in `dreggnet-faction/src/lib.rs:3,65`
  and `dreggnet-quest/src/lib.rs:11,72,150,203`, both saying they *re-home* the idea. Its only
  exercise is its own nine `#[cfg(test)]` tests.
- **`dreggnet-tavern`** — 737 lines, **zero reverse dependencies**. `dreggnet-surfaces/src/tavern.rs:3-4`
  explicitly refuses to depend on it (*"that path pulls the deos-host (mozjs) + node + axum weight,
  so it stays OUT"*) and reimplements the surface.
- **`dreggnet-adventure`** — 1,749 lines, zero dependents, no bin, no example; its only consumer is
  its own `dreggnet-adventure/tests/verified_progression.rs`.

**Correction to the mandate's framing:** `combat.rs` (2,027 lines) is *not* unreached — it has two
production importers, `dreggnet-party/src/encounter.rs:45` and `dreggnet-surfaces/src/party.rs:35`
(the `Arena`, `WARDEN`, `is_hero`). `loot.rs` is reached in production by the shipped
`native_descent`. `dialogue.rs` is the one with zero importers.

**On the 864 words:** the literal figure appears nowhere in the tree. Measured across all 13
spween-DSL scene consts in the game crates, the total is **838 words of room prose across 35
passages** (~1,650 counting choice labels). The claim is right in magnitude. `mud-dregg` and
`dreggnet-adventure` ship **no prose at all**; the one real DSL content file,
`dungeon-on-dregg/dungeons/salt_reliquary.dungeon`, is 99 lines of which about half is a comment
header that calls itself *"An authoring MEASUREMENT, not a demo"* (`:3`).

### 3.13 Dead-but-documented production paths

Four instruments whose doc-comments say "production" and whose only callers are tests:

- **`PayState::try_paid_run`** (`discord-bot/src/pay.rs:1245`), documented at `pay.rs:12` as *"A paid
  `/dungeon` run … debits ONE credit"*. Callers: `pay.rs:4006,4040,4044,4048,4153` — all inside
  `#[cfg(test)]`. (The debit itself *is* real; the live path calls `hold_paid_credit` /
  `commit_paid_credit` directly.)
- **`CreditPaymaster`** (`dreggnet-offerings/src/session.rs:890`), described at `:52` as *"the real
  binding"* and `:849` *"The production binding"*. Sole users:
  `dreggnet-offerings/tests/session_paymaster.rs:66,150`.
- **`EpochMinter`** (`turn/src/economics.rs:205`). `set_epoch_minter` (`turn/src/executor/mod.rs:2308`)
  is called by no binary. Honest in-source: *"epoch minting remains an ex-nihilo credit — the LAST
  non-conserving verb in the executor. The deployed chain does not configure an `epoch_minter`."*
- **Proven cross-chain holdings** — `commands/pay.rs:313` calls `pay.treasury_holdings(&[])` with a
  hard-coded empty slice, then prints *"{} position(s) proven across {} chain(s), total `{}`
  atomic"*. Always 0/0/0 by construction. (This one *is* labelled a residual in the next sentence.)

And one that is candid up front: `auditable-fund/src/fund.rs:21` — *"⚑ PAPER-ONLY. `simulate_fill`
moves numbers in this process. There is NO exchange order, no custody, no real money."*

### 3.14 Two layers of build-level silence over the whole economy

- `dreggnet-market`, `dreggnet-catalog`, `dreggnet-offerings`, `dreggnet-web`, `dreggnet-telegram`,
  `fhegg-core`, `fhegg-fhe`, `fhegg-solver`, `narrator`, `mud-dregg`, `dungeon-on-dregg` are workspace
  `members` but **not** `default-members` (`Cargo.toml:45`). A bare `cargo test` at the root builds
  none of them.
- `dreggnet-market/Cargo.toml:8` declares `default = []` with nine opt-in features. Even
  `cargo test -p dreggnet-market` runs ~13 of ~105 integration tests.
- Many gated test files use an inner `#![cfg(feature = "...")]` (e.g.
  `dreggnet-market/tests/dark_amm_game.rs:4`) rather than `required-features`, so they **compile to
  an empty binary and report `test result: ok` having asserted nothing** — indistinguishable from a
  pass in any log.
- `.github/dark-targets.txt:230-238` names the sharpest instance itself: seven `fhegg-fhe tfhe_*`
  tests are *"DOUBLE-DARK… every one opens with `if std::env::var_os("DREGG_REQUIRE_WGPU").is_none()
  { eprintln!("skipped"); return; }` … a suite that reports `ok` having asserted nothing."*
- **No CI job touches DrEX or fhegg at all** — zero hits for `drex|fhegg` under `.github/workflows/`.
- `discord-bot` is a separate workspace for a sound technical reason (`Cargo.toml:56-58`, one
  `links="sqlite3"` per workspace), but the consequence stands: `cargo test --workspace` never builds
  the surface where the money code lives.

### 3.15 What is NOT theatre — say this too

- The **player-side run credit** is careful, exactly as the mandate says: hold-then-commit,
  `Drop`-released on failure, debited once after the receipt verifies, one conserving
  `Effect::Transfer`, fail-closed on empty (`dregg-pay/src/protocol_native.rs:294-337`,
  `demo/real-dungeon-service/src/run_credit.rs:1-21`). Caveats: the default mode is the **free
  custodial mock rail** unless `REAL_DUNGEON_SETTLEMENT=protocol-native`, and the player/operator
  cells are constants `[0x11;32]`/`[0x22;32]`.
- **`/credits` refuses to render a storage failure as zero** (`pay.rs:1012-1023`,
  `commands/pay.rs:146-151`). That is the correct shape and it is the counter-example to §3.2's
  `unwrap_or(0.0)`.
- **`/send`** submits a real conserving turn (`commands/transfer.rs:175-208`); **`/cipherclerk
  balance`** reads the live node (`commands/cipherclerk.rs:253-261`); **admin grants say
  "MINTED"** (`commands/admin.rs:894`).
- The **computron refill** conserves exactly, every refusal arm adversarially tested, and a refill is
  a transfer and never a mint (`docs/deos/COMPUTRON-POLICY.md` §3).
- The **grain economy** is the one place value genuinely moves across cells for a service today:
  `HostedLease` gates → settles → discharges under one tenant lock, with meter/pay drift
  **unrepresentable as a type** (`docs/reference/grain-economy.md` §3).
- The **offering resume store** is durability done right: store the reproducible inputs, reopen by
  replay, refuse a tampered log rather than reopen to a forged state
  (`dreggnet-offerings/src/resume.rs:1-44`).
- The **admin surface is honest**: `commands/admin.rs:733` renders *"⚠ **NOTHING IS WATCHING**"* when
  the watcher is a mock, and `select_watcher` **panics** rather than silently mocking on mainnet
  (`pay.rs:1343-1359`). The frontends label `live:false` where it is false.

**The dishonesty risk in this codebase is genuinely low. The gap is functionality, not candour** —
with the four exceptions in §3.1, §3.3, §3.4 and §3.11, which are the ones to fix.

---

# PART 2 — VISIONARY: what a real MUD economy would be here

## 4. The argument, not a wishlist

An in-game economy works when four things hold. dregg has an unusual position on each.

**(i) Scarcity must be enforced, not declared.** Most games declare it: a row says you have 14 iron.
dregg *enforces* it — a loot note is an owned cell with a provenance lineage, a non-owner listing is
a real executor refusal, and a spent coin cannot be re-spent (`dreggnet-surfaces/src/trade.rs:227-238`).
Already true, already built. This is the foundation nobody else has.

**(ii) There must be sinks, or every faucet is inflation.** There is exactly one real sink —
`CraftForge`'s owner-signed burn (`dreggnet-craft/src/forge.rs:503-506`) — and in production it
opens over demo materials, not looted ones (§2(e)). Everything else — `seed_items`,
`seed_trade_stock`, `fund_dregg`, `LootVault::claim`, and the Bazaar scene's sell-side which mints
gold from nothing (`lib.rs:2775-2795`) — is a faucet. A one-sink economy with six faucets has one
equilibrium, and it is worthless items.

Note the deeper problem: the *durable* game value, `echoes`, is `Monotonic` **by kernel constraint**
and can never be spent at all (§2(d)). The progression system has already decided that spending is
bad. A trade economy requires spending. Those two commitments are in direct tension and nobody has
adjudicated them.

**(iii) Prices must be discovered, not assigned.** Today `ItemRecord.price` is a `usize` set at seed
time (`dreggnet-surfaces/src/world.rs:98`). The machinery to replace it exists and is proven:
`uniform_price_optimal` (`Market/Optimality.lean:174`) and the volume-argmax clearing
(`Market/FhEggClearing.lean:360`) over `fhegg-solver`'s batch auction.

**(iv) There must be a reason to trade with a *player* rather than the system.** This is where every
game economy dies, and where dregg has the one genuinely novel answer.

## 5. Ring trades kill the double coincidence of wants

The standard failure of a small-player market is that A wants what B has, B does not want what A has,
and nothing clears. dregg's matcher does not require that. `intent/src/solver.rs:1-17`:

> *"Instead of pairwise matching (A wants B, B wants A), this solver finds **ring trades** — cycles
> in the intent compatibility graph where A→B, B→C, C→A can all settle atomically without a common
> denominator."* — Johnson (1975) elementary circuits + Shapley–Scarf (1974) Top Trading Cycles +
> Roth's kidney-exchange lineage.

`Market/Clearing.lean` proves the point with teeth: `crossBid_needs_market` shows a cross-asset bid
has **no** bilateral fill; `ringBook_bilateral_stuck` (`:349`) shows every entry in the worked book is
bilaterally stuck and every proper sub-book fails to balance; `ringClearing_conserves` (`:374`) shows
the 3-party ring clears what no pair can. `drex_clear` even reports `twoCycles` — *"0 proves the ring
is genuinely multilateral"* (`exec-lean/src/bin/drex_clear.rs:153`).

**For a MUD with 30 players and 400 item types, this is the difference between a dead market and a
live one.** Nobody else has it because nobody else needs it: a game with a gold currency solves the
double-coincidence problem with money and eats the inflation. dregg can run a *barter* economy that
clears — and that is a different game, not a better version of the same one.

## 6. What machine-checked conservation and third-party-verifiable settlement actually buy

Three things no other game can offer, in ascending order of how much they change the product.

**(a) A trade nobody has to trust.** The winner of a Bazaar auction receives the *exact note* the
dungeon minted — same cell, same lineage, never re-minted from display metadata
(`native_descent.rs:512-516`). A buyer verifies the item's whole history without trusting the seller,
the market, or us. `world.lineage_len(loot.asset_id) == 3` in `descent_asset_bazaar.rs:75` is that
property as an assertion.

**(b) A market whose oracle is a re-execution.** The Oracle Pit does not ask a committee whether a
run was crowned. It replays the run through the real executor carrying the Lean-emitted
`dungeonProgram` teeth and reads the outcome off the replayed session (`oracle_pit.rs:19-40`).
`WorldCell::from_compiled` derives the world-owner key deterministically from `(scene_id, seed)`, so
*the same run produces the same turn hashes on a stranger's machine*. A prediction market on a video
game, settled by anyone who can re-run the game. I have not seen that anywhere.

**(c) A settlement a third party can verify without the private state.** `RevealNothing.lean`,
`MpcClearingSecurity.lean`'s `perfect_hiding` (`:149`), and the N4K4 HidingFRI private-book relation
say a clearing can be *proven fair while nobody sees the book*. For a game this is not privacy
theatre: sealed loot allocation, hidden-hand legality, private guild bargaining and season-end
netting are all the same organ (`THE-DARK-BAZAAR.md` §5).

## 7. The loop, concretely

**Daily.** You run the day's Descent (shipped). The day-seed is beacon-derived and unpredictable
until revealed, so today's map is genuinely today's. You bank relics — real notes minted into your
vault at settlement, provenance rooted at the day-seed.

**You spend.** One run credit at the run boundary — a conserving transfer you authorize, fail-closed
on empty (`charge_run`). Crafting consumes materials permanently, on the loot you actually rolled.
Both are real sinks. (`echoes` stays exactly as it is: monotone, earned only by dying, unlocking
talents by threshold. **It is the progression track and it must not become the trade currency** —
keeping those two units distinct is what preserves the no-P2W teeth in
`dreggnet-gear/src/talents.rs:34`.)

**You earn.** Relics of a rarity you didn't roll, and materials you did. Because the day-seed is
shared, *everyone's* relics come from the same table today — so what you have is not what you need,
and what you need somebody has.

**You trade — with a person.** Post an intent: *"I give the Tide-Warden's crown, I want two way-keys,
minimum."* You do not need to find someone who wants a crown. `RingSolver::find_rings` finds the
cycle; `settleRing` clears it atomically or refuses; `clearing_respects_limits` guarantees you are
never debited above your offer nor credited below your minimum, on both sides, with refusing teeth.
You get a receipt a third party can check.

**You speculate.** The Oracle Pit takes positions on today's run: will the crown be taken before the
third floor? Odds public, positions private, settlement by the run's own replay. You cannot bribe the
oracle because the oracle is the game.

**You come back tomorrow** because (1) the map is new and unpredictable, (2) the relic you need for
the recipe you want is in someone else's vault and the ring will find it, (3) your Pit position
resolves when the day resolves, and (4) your crafted item carries a lineage saying *you* forged it
from *that* run — a provenance that cannot be duplicated because the run cannot be.

## 8. How the dungeon feeds the bazaar and the bazaar feeds the dungeon

The mandate's framing needs one correction and then it is exactly right.

**Correction.** `combat.rs` (2,027 lines) is *not* unreached — it is consumed by
`dreggnet-party/src/encounter.rs:45` and `dreggnet-surfaces/src/party.rs:35` (the `Arena`, `WARDEN`,
`is_hero`). `loot.rs` is reached in production by the shipped `native_descent`. The module with
**zero code importers** is `dialogue.rs` (960 lines) — every reference is a doc comment in
`dreggnet-faction/src/lib.rs:3,65` and `dreggnet-quest/src/lib.rs:11,72,150,203`, both of which say
they *re-home* its idea rather than call it.

**The right statement:** loot and combat are reached; **loot has nowhere to go.**

- **Dungeon → bazaar** is `into_loot_vault()` → `vault.into_assets()` →
  `TradeWorld::with_assets(...)`. It is written down, in a doc comment, on the function
  (`native_descent.rs:512-516`). It has one caller and it is a test.
- **Bazaar → dungeon** already exists and is the *stronger* half. `THE-DARK-BAZAAR.md` §2.2 records a
  LIVE durable private consequence plane — `private_bazaar_worker.rs` →
  `private_clearing_consequence.rs` → a cap-bounded `SignedTurn` against the same authenticated
  character world the Dungeon/Descent surfaces use, with `Prepared → Dispatching → Applied →
  Committed` crash recovery and an authenticated durable target registry
  (`private_bazaar_targets.rs`). **A market outcome can already change the dungeon.** What it cannot
  be is *caused* by something the dungeon produced.

The pipe from market to world is built and durable. The pipe from world to market is one call and one
durable item ledger away.

---

# PART 3 — CRITIC: what goes wrong

## 9. Inflation

Five faucets, one sink. `TradeWorld::fund_dregg` (`dreggnet-trade/src/lib.rs:461`) is literally
`credit_balance(amount)` with no source debit — a mint, in a currency named after a real token.
`SharedWorld::demo` re-seeds a fresh purse and shelf per player. `LootVault::claim` mints on every
fair roll with no cap. `dreggnet-trade`'s own residual list (`lib.rs:69-76`) names it: **"no
settlement path takes a cut today."**

If the loop in §7 ships without sinks, the terminal state is: everyone has every relic, prices go to
zero, and the ring solver finds cycles nobody cares about. **The sink must ship in the same release
as the faucet, not after.** Primitives that already exist: craft consumption (real), the sigil burn
(`dreggnet-surfaces/src/private_raid.rs:333-358` — a `WriteOnce` + `FieldDelta(+1)` executor turn),
a listing fee to a treasury cell, and relic decay at day-seed rollover.

## 10. Dead markets — worse than the two-player-game problem

**First, the counterparty problem is `n`-way, not 2-way.** `dreggnet-market` has *no matchmaking at
all* — no lobby, no cross-session book, no bid-ask crossing. Counterparty discovery is "be in the
same Discord channel" (`discord-bot/src/commands/offering.rs:261` keys the session by channel id) or
"have the same URL" (`dreggnet-web/src/lib.rs:2916`). A game with two players and no matchmaking is
boring. **A market with two participants and no matchmaking is not a market — it is a haggle.**

**Second, and this is the part that is easy to miss: liquidity is a *time* problem, not a *count*
problem.** Even with 200 players, a continuous market where everyone logs in at a different hour has
no counterparty at any instant. The fix is structural and dregg already has it: **batch.** A daily
call auction at a fixed hour concentrates every participant into one clearing event.
`fhegg-solver`'s uniform-price batch (`clearing.rs:180`) is exactly that mechanism, and
`clearedVolume_optimal` proves the argmax maximizes executed volume. **A batch auction is the correct
microstructure for a small MUD, and it is the one already proven here.**

Do **not** ship a continuous order book. It will be empty at every instant and will look broken.

## 11. ⚑ Where the line belongs with the real token

$DREGG is a real fixed-supply SPL on Solana with real holders and a real market cap
(`docs/TOKENOMICS.md`). A game economy that touches it is a financial surface in every jurisdiction
that has an opinion. My position, plainly:

**NEVER touch the real token:**

1. **Loot, relics, crafted items, materials.** Minted by a random roll. A random roll that produces a
   real-money asset is a lottery. These must stay game notes with no redemption path.
2. **The Oracle Pit, and anything else resolving on an outcome.** A prediction market on a game
   outcome denominated in a tradable token is a betting product. Denominate it in a
   non-transferable pit-chip minted from play and burned on settlement. The Pit's cryptography and
   oracle are excellent research; the denomination is what would turn it into a regulated activity.
3. **The dungeon-fed bazaar.** If loot can be sold for real money, the dungeon becomes a job and every
   balance change becomes a market event. Fastest possible route to an unfun game and a token that is
   a security.
4. **`dreggnet-trade`'s `DREGG_ASSET`.** ⚑ Trivially fixable and it should be fixed today: the
   in-game currency constant is `*b"dreggnet-trade--DREGG-value-tok!"` and its doc-comment describes
   the real token's policy (`dreggnet-trade/src/lib.rs:87-90`). It is a `HashMap` with a mint
   function. Rename it. Someone will screenshot `fund_dregg(player, 1000)`. See §14/T1.

**MAY touch the real token, at exactly one seam:**

- **Services.** $DREGG → run credits, hosting, cosmetics. Exactly what `docs/TOKENOMICS.md` already
  commits to: *"Buys services, never power… never yield."* The pay rail is built for it and the
  mainnet flip is already ember-gated.
- **The line is: value flows IN from the token to a service, and never OUT from the game to the
  token.** One-way. A player can spend $DREGG to play. A player can never earn $DREGG by playing.
  That single rule keeps the whole game economy out of financial-surface territory while preserving
  the token's only honest utility.

Four structural facts already enforce this and should be preserved **deliberately, not by
accident**:

- The talent tree's `"buy-with-dregg"` method **default-denies**
  (`dreggnet-gear/src/talents.rs:34`), and echoes *"cannot be injected without a real death"*. The
  no-P2W boundary is already a kernel refusal, not a policy. Keep it that way.

- Only `bridge/`, `solana-lock/`, `solana-settlement/` depend on Solana; the latter two are in the
  root `exclude` list (`Cargo.toml:90`).
- **No binary in this repo can move an SPL token.** The sweeper is a trait seam
  (`dregg-pay/src/sweeper.rs:139-142 pub trait TxSubmitter`) and the **only** `impl TxSubmitter` in
  the entire tree is at `sweeper.rs:305`, inside `#[cfg(test)] mod tests`. `SolanaSweeper` is
  constructed once, at `sweeper.rs:334`, in that same test module. Same shape for `NftTxSubmitter`
  (`nft_mint.rs:821`) and the Jupiter venue (`swap.rs:672`, `MockSwapVenue`).
- No mint address is hardcoded anywhere; `DREGG_PAY_MINT` / `DREGG_PAY_USDC_MINT` are required
  operator env values (`dregg-pay/src/config.rs:359-360`).

**Add a test that asserts all three** (§14/T2). A structural guarantee nobody checks is one refactor
from gone.

Residual worth naming: `PayState::from_env_or_devnet` constructs
`DepositSource::Custodial(HdDeposit::new(&config))` (`pay.rs:1393`), which loads `DREGG_PAY_SEED` and
can derive every user's deposit key. It warns loudly (`pay.rs:1376-1392`) and the watch-only path
gated on `DREGG_PAY_ADDRESS_BOOK` is the documented production posture. That posture should be the
default, not the documented alternative.

## 12. Whale capture, and three attacks the proofs do NOT stop

- **Book capture.** Uniform-price clearing is envy-free and individually rational and still lets one
  participant with 10× everyone's budget take the entire cleared volume at a price nobody else would
  set. `clearing_respects_limits` says nobody is worse off than *their own declaration* — a whale's
  declaration is "I'll pay anything."
- **Sybil rings.** `RingSolver` finds cycles in an intent graph. Nothing in the solver or the Lean
  authenticates that participants are distinct humans. One actor with `k` identities can manufacture
  a ring that clears at a price they set, laundering an item's price history through what looks like
  a multilateral market. `aggregate_sound` proves the book faithfully represents the *submitted*
  orders; it says nothing about who submitted them.
- **Provenance as a deanonymizer.** The lineage that makes a relic verifiable also makes it
  traceable. In a small market, "who held this before" identifies people. The Dark Bazaar work is the
  right answer and it is unreachable (§3.5).

And one the mandate did not name: **the Oracle Pit's subject is content we control.** A market
settling on our dungeon is a market where the content team are insiders. The `WriteOnce` subject
digest and the beacon-derived day-seed are exactly the right mitigations and should be stated
publicly as such, not merely implemented. Its own run-designation hole (`oracle_pit.rs:224-236` —
an unpinned pit settles on *whichever* terminal run of the day reaches it first) must be closed
before a single chip is at stake.

## 13. The honest limits of the verification story

Because this doc will be cited, three things must never be over-read.

1. **`Market/` is model-level in most places.** Rung 1 (limit-respecting fairness) is ledger-realized
   through `settleRing`; rungs 4–6 (uniform-price optimality, envy-freeness, pool solvency) are proved
   over the priced `Fill` model and are **not** welded to the executor
   (`docs/deos/DREGGFI-VISION.md` §7, `docs/reference/MARKET-METATHEORY-REVIEW.md`).
2. **The Rust↔Lean denotation is trust-by-reading.** `FhEggRustDenotation.lean` re-authors the Rust
   algorithm in Lean and names the gap as an undischarged residual. Honest, un-mechanized.
3. **The FRI floor is undischarged.** Every reveal-nothing claim rests on `HidingFriPcs`.
   `RevealNothing.lean`'s header says so outright, and that honesty is the model to follow. A market
   pitch must not launder it.

---

# PART 4 — THE PLAN

**[RULES]** = Lean, machine-checked, a real theorem over the emitted object.
**[SURFACE]** = Rust/wiring, invents no law.
The house law is that rules live in Lean and a surface never invents one; every item is marked.

## 14. This week — trivial, named, and I would do them today

| id | item | kind | why now |
|---|---|---|---|
| **T1** | Rename `dreggnet_trade::DREGG_ASSET` / `fund_dregg` / `dregg_balance` to a game-currency name. Fix the doc-comment at `lib.rs:87-90` that describes the real token's policy. | [SURFACE] | A `HashMap` mint sharing a name with a real SPL is one screenshot from a bad day. Mechanical. |
| **T2** | Tests asserting (a) no game crate transitively depends on `bridge`/`solana-*`, and (b) `TxSubmitter` / `NftTxSubmitter` have no non-`cfg(test)` impl. `cargo metadata`'s resolve is the oracle. | [SURFACE] | Makes §11's structural separation a **detected** fact rather than a documented one. |
| **T3** | Call `spend_inference_usd` where a run completes, **or** delete the fuel panel and the two copy strings that promise it burns. Not both. | [SURFACE] | §3.1. The REFUEL alarm cannot fire. This is real money. |
| **T4** | Fix `get_leaderboard` to net outflows (`SUM(in) − SUM(out)`), exclude `to_user='faucet'`, or rename the command. | [SURFACE] | §3.4. Three-line SQL change; the current label is false. |
| **T5** | Either route `/bounty` payout through the real `BountyTreasury::payout`, or stop rendering "Bounty Paid" / "Escrowed: N DEC". | [SURFACE] → see M6 | §3.3. A success embed for a state-flag write is the worst instance in the tree. |
| **T6** | Replace `ledger.spent_usd().unwrap_or(0.0)` (`pay.rs:572`) with a refusal to render a spend line. Carry `usd_spent` on the Descent path instead of dropping it (`descent.rs:2875-2878`). | [SURFACE] | `/credits` already does the right thing (`pay.rs:1012-1023`); copy that shape. |
| **T7** | Fix the "three monies" copy — DEC **is** computrons (`pay.rs:262-267`, `start.rs:262-264`, `menus.rs:1590-1591`). | [SURFACE] | Two monies, described as three, in the onboarding text. |
| **T8** | Convert every inner `#![cfg(feature = ...)]` in `dreggnet-market/tests/` to `required-features`. | [SURFACE] | ~8 files. An empty test binary reporting `ok` is the repo's own worst class. |
| **T9** | Refresh `THE-DARK-BAZAAR.md:59` and `DREX-TIER-STATUS-2026-07-24.md:188-198` — both **understate** the bazaar since `4aeba707d` (2026-07-25). | [SURFACE] | A stale doc that undersells is still a stale doc. |
| **T10** | Add `spend_inference_usd`, `settle_winning_asset`, `into_loot_vault`, `PrivateBazaarSealedIngressQueue::submit`, `CraftForge::with_assets`, `BountyTreasury::payout`, `try_paid_run`, `CreditPaymaster` and `Market.EmitSameOpeningGadget` to an explicit **production-caller census**, the way `.github/dark-targets.txt` already registers dark tests. | [SURFACE] | ⚑ **The highest-leverage item on this list.** The instrument that would have caught all of §3 does not exist. Everything in §3 is one `grep -v cfg(test)` away from being detected automatically. |
| **T11** | Turn `DREGGNET_WEB_SESSION_DIR` on by default, or log at ERROR (not `warn!`) that every player's craft/inventory/trade is RAM-only. | [SURFACE] | §3.9. A durability mechanism that is off by default is not durability. |

### ⚑ E1 — the one ember decision this plan needs before M-anything

**Does the game get a second, spendable, non-monotone unit?**

`echoes` is `Monotonic` by kernel constraint and is a threshold, never a cost (§2(d)). That is a
deliberate anti-power-creep, anti-P2W commitment with real teeth
(`dreggnet-gear/src/talents.rs:25,34`). A trade economy needs a unit that *leaves* the holder.

The three answers, and their consequences:

1. **Keep echoes monotone; add a separate spendable trade unit.** (My recommendation.) Progression
   and commerce stay orthogonal; the no-P2W teeth are untouched; the trade unit is free to have real
   sinks. Cost: a new unit to design, and a new `LinearityClass` obligation to discharge (M6).
2. **Trade in items only, no unit at all.** Ring trades make this genuinely viable — barter clears
   without a common denominator (§5). Purest form, and the most novel. Cost: no price signal exists,
   so nothing can be *quoted*, only matched.
3. **Make echoes spendable.** Cheapest to build, and it destroys the property the progression system
   was built to protect. I would not.

This is an architecture commitment, not a lane task, and every item in §15 assumes an answer.

## 15. One month — make the loop real

**M1. One durable item ledger per player.** [SURFACE]
Join `NativeDescentSession`'s `LootVault` to `PlayerWorlds`' `SharedWorld` so a settled run's relics
land in the player's inventory. The seam is named on the function (`native_descent.rs:512-516`); the
durability mechanism exists (`FileResumeStore`, replay-based). Delete `SharedWorld::demo`'s
`seed_items` for real players — a canned inventory and a real one must not coexist.
*Gate:* run a descent, restart the host, find the relic in the inventory.

**M2. Make `TradeWorld` constructible in production, or delete it.** [SURFACE]
Today it is a test fixture holding the only asset-crossing path in the tree, with no `serde`. Either
give it a production constructor and a persistence story, or fold `settle_winning_asset` onto
`SharedWorld` and retire it. **Do not leave a third item ledger.**

**M3. Build the bid collector.** [SURFACE]
`private_bazaar_ingress::submit` is the missing 200 lines between a complete, mounted, proof-running
supervisor and a working sealed market (§3.5). This is the single largest ratio of *value unlocked*
to *code written* anywhere in the economy.

**M4. One sink per faucet, measured — starting by pointing the existing sink at real loot.** [SURFACE, with M6]
The cheapest sink in the plan is already written: give `CraftForge::with_assets` a production caller
so the forge burns the notes a player actually rolled instead of demo materials (§2(e)). Then add a
listing fee (coins → a treasury cell) and relic decay at day-seed rollover. Also fix the Bazaar
scene's sell-side, which mints gold from nothing (`dungeon-on-dregg/src/lib.rs:2775-2795`) — a second
merchant cell is what that needs, and it is the multi-cell ceiling the crate names itself.
**Publish the faucet:sink ratio.** An economy without a measured ratio is not designed, it is hoped.

**M5. A daily batch auction, not a continuous book.** [SURFACE]
Concentrate all trade into one clearing event per day-seed epoch using `fhegg-solver`'s uniform-price
batch (`clearing.rs:180`), with `Allocation::validate` — **never** `conserves()` — as the gate. This
is the highest-leverage *decision* in the plan: it converts a liquidity problem from "we need more
players" into "we need players *today*".

**M6. ⚑ A value-deciding rule is a RULE.** [RULES]
The moment a listing fee, a decay schedule, or a bounty payout decides how much value leaves a
player, that is a constraint over state, and by house law it is authored in Lean and emitted — not a
Rust `if`. The precedents exist (`Market/Priced.lean`, `Market/Fairness.lean`), and
`Dregg2/Spec/Conservation.lean`'s `LinearityClass` already forces the question *"is this
`Conservative`, `Generative` or `Annihilative`?"* to be answered before the effect compiles. A decay
is `Annihilative` and therefore owes a **disclosure**, not a `Σδ = 0` — that is
`disclosed_non_conservation` (`Conservation.lean:270`), and it should be discharged, not assumed.
**T5's bounty payout belongs here**: the correct fix is a Lean-authored payout relation, not a Rust
`Effect::Transfer` bolted on.

**M7. Put ONE economic surface on the ship list.** [SURFACE]
`SHIPPED_KEYS` is a 3-element array (`dreggnet-catalog/src/lib.rs:617`). Nothing else in this plan
matters until a fourth element exists. Recommendation: `trade`, **after** M1 and M2, because it is
the surface with real executor refusals already behind it.

## 16. One quarter — the differentiator

**Q1. Ring trades between real players, end to end.** [SURFACE + one [RULES] weld]
`intent/`'s solver, `settleRing` and the verified gate all exist. Missing: an intent pool spanning
sessions, and a matching cadence. Ride M5's daily batch — collect intents all day, run Johnson + TTC
at the epoch boundary, settle the cycles, publish the receipts.
*The [RULES] weld:* the intent's admissibility predicate (what makes an offer well-formed and
eligible) is a rule and belongs in Lean beside `Market/Aggregation.lean`'s `aggregate_sound`.

**Q2. The Oracle Pit becomes a market.** [SURFACE + [RULES]]
Missing, by its own doc: order intake, a positions ledger, settlement and payout. The oracle (exact
replay) and the pricing (`Market/OraclePitQuadratic.lean`) are the hard parts and they are done.
**[RULES]:** `payout_per_share` and the claim predicate are value-deciding relations and are authored
in Lean. **Prerequisite:** close the run-designation hole (`oracle_pit.rs:224-236`). Denominate in a
non-transferable pit-chip (§11).

**Q3. Ledger-realize the priced rungs.** [RULES]
`uniform_price_optimal`, `uniform_price_envy_free` and `pool_solvent_forever` are proved over the
priced `Fill` model and not welded to `settleRing`/`recKExec`. Rung 1 already carries that tie
(`cycleValid_fulfilled_respects_limits`). Doing the same for rungs 4–6 is the difference between "we
proved a market is fair" and "we proved *this* market is fair". Highest-value Lean work the economy
has, and it is engineering, not research.

**Q4. Wire the same-opening gadget.** [SURFACE of a [RULES] object]
`Market.EmitSameOpeningGadget` is proved and byte-pinned with zero Rust consumers
(`THE-DARK-BAZAAR.md:64-68`). Highest security-per-effort item in
`docs/PRIVATE-MARKET-DEV-PLAN-2026-07-25.md` §4; it upgrades "house-blind" from a threshold-decrypt
property to the real apex.

**Q5. Fix the `epsilon` mismatch or retire the Cert-F STARK button.** [SURFACE]
`circuit-prove/src/cert_f_air.rs:355-376` registers exactly two programs (`epsilon: 0`,
`epsilon: 2000`); `fhegg-solver/src/bin/fhegg_clear.rs:235` hardcodes `let epsilon = 0.5f64;`. No
user order can ever match, and two independent consumers hit the same wall
(`dreggnet-market/src/certified_clearing.rs:29-33`). Register a family the solver can hit, or stop
offering the button.

## 17. Research — name it, do not promise it

- **Discharge the FRI floor.** Everything reveal-nothing rests on `HidingFriPcs`. Per
  `docs/PRIVATE-MARKET-DEV-PLAN-2026-07-25.md` §⚡, discharging it unlocks the **committee-free**
  private DEX (Path 3), which structurally beats every competitor in the field. Ember-gated strategic
  fork.
- **Distributed no-single-viewer ceremony.** Every "party" is currently a thread in one test binary
  (`fhegg-fhe/tests/dark_clearing_e2e.rs:14-15`). The crypto is finished; the perimeter is ops.
- **Sybil-resistant ring formation.** No proof here distinguishes `k` identities from `k` people. For
  a market that is not a nice-to-have.
- **Mechanize the Rust↔Lean denotation.** The re-authored models are honest and the source-refinement
  residuals are trust-by-reading. Pinning them with extracted-Rust differentials is the de-laundering
  move.

---

## 18. The blunt version

**The bazaar is a demo.** Not a pejorative — a precise description. It has a sealed auction with a
real `WriteOnce` commit board, a real phase machine, a Lean-emitted byte-pinned HidingFRI proof, a
durable crash-recovering supervisor mounted in three production binaries — and:

- no counterparty discovery of any kind;
- **no production caller for the function that accepts a bid** (`private_bazaar_ingress.rs:272`), so
  the supervisor drains a queue nothing can fill, and zero bytes of its state exist on this machine;
- no production constructor for the world its items live in;
- one call away from the dungeon that mints those items, and that call has one caller, a test;
- and it is not on any shelf.

**Here is what it would take to be a market**, in order: (1) one durable per-player item ledger the
shipped game writes to; (2) a production `TradeWorld`, or its retirement onto `SharedWorld`; (3) the
bid collector — the ~200 lines that make `submit()` reachable; (4) one sink per faucet, measured;
(5) a **daily batch** clearing event rather than a continuous book; (6) a fourth element in
`SHIPPED_KEYS`.

Items 1–4 are a month. Item 5 is the existing `fhegg-solver` batch behind a scheduler. Item 6 is one
line — and it is the one that decides whether any of the rest was real.

---

*Read for this document:* `docs/deos/THE-DARK-BAZAAR.md`, `docs/deos/DREX-TIER-STATUS-2026-07-24.md`,
`docs/deos/COMPUTRON-POLICY.md`, `docs/deos/DREGGFI-VISION.md`, `docs/TOKENOMICS.md`,
`docs/PRIVATE-MARKET-DEV-PLAN-2026-07-25.md`, `docs/DESIGN-bazaar-apex-v4.md`,
`docs/reference/MARKET-METATHEORY-REVIEW.md`, `docs/reference/lean-conserve.md`,
`docs/reference/grain-economy.md`, `.github/dark-targets.txt`, `scripts/feature-tiers.tsv`, and the
cited source. *On-disk state verified:* `~/.dregg/narrator-ledger.json`; absence of
`sealed-ingress-v1.queue`, `finalized-private-bazaar-v3.spool` and any `by-blind/*.binding`
(full-filesystem search). *Measured, not asserted:* 838 words of room prose across 35 passages in 13
spween scene consts — the mandate's "864 words" is right in magnitude, though the literal figure
appears nowhere in the tree.

*Taken from the mandate and NOT independently verified here:* the emptiness of the `crown_folds`
table in production. Its route **is** merged into the live app (`dreggnet-web/src/lib.rs:7286`) and
its writer **is** installed (`discord-bot/src/main.rs:881`), so its emptiness would be an *adoption*
gap — a strictly different, and much less serious, diagnosis than the bazaar's *wiring* gap.

*Two corrections to the mandate's framing, made in-text:* `combat.rs` is reached in production
(`dreggnet-party/src/encounter.rs:45`, `dreggnet-surfaces/src/party.rs:35`) — `dialogue.rs` is the
module with zero importers; and the two status docs `THE-DARK-BAZAAR.md:59` /
`DREX-TIER-STATUS-2026-07-24.md:188-198` now **understate** the bazaar, which was wired to the real
proof on 2026-07-25 by `4aeba707d`.
