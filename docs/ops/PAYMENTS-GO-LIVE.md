# PAYMENTS-GO-LIVE — taking the $DREGG/USDC rail from devnet to mainnet

The native `dregg-pay` rail (supersedes the dropped Stripe USD-credit rail; see
[README.md](README.md)) sells the **service** (real-AI narration compute) for
`$DREGG` and USDC. This runbook is the **go-live sequence** and the **custody
contract**. Everything defaults to devnet/mock; going live is an operator-env
flip. **The operator (you) holds every key; the platform is watch-only where it
can be.** Nothing mainnet is hardcoded in the repo (grep-clean).

## The economic model (what you are operating)
- **USDC = fuel.** Real inference costs real USD; the USDC treasury balance funds it.
- **`$DREGG` = pile.** A `$DREGG`-paid run consumes inference (USD) but adds only
  illiquid `$DREGG`. So the fuel drains, the pile grows, and the community must
  periodically **refuel** (a collective-voted Jupiter swap `$DREGG→SOL→USDC`, a
  manual USDC top-up, or the friendly OTC — users buy the pile's `$DREGG` at a
  10% discount).
- **Pricing:** a run = `$0.10` USDC (config); paying in `$DREGG` is ~20% cheaper,
  price-fed via a Jupiter `$DREGG/USDC` quote (stable real value, rewards holders).

## Operator env (`PayConfig::from_env` — the ONLY route to real funds)
Set these in the operator's secured env (`/etc/dregg/pay.env`, mode 0600 — see
[KEY-MANAGEMENT.md](KEY-MANAGEMENT.md)); never commit them:

| Var | Meaning |
|---|---|
| `DREGG_PAY_NETWORK` | `devnet` (default) or `mainnet` — the go-live flip |
| `DREGG_PAY_MINT` | the `$DREGG` SPL mint (mainnet: `XkeTXo1125vz5H9svJpGiw4JvLbN8VmMu9cmMvspump`) |
| `DREGG_PAY_USDC_MINT` | the USDC SPL mint |
| `DREGG_PAY_TREASURY` | the treasury address deposits sweep to (mainnet: `J2pW9PQdkJTy2PTzdFUnYFHgbT8btCaY7ZqYHpMFJF5G`) |
| `DREGG_PAY_SEED` | the HD seed for deposit-address derivation **and** the sweeper — **the custody point; operator-only** |
| `DREGG_PAY_RPC` | the Solana RPC endpoint |
| `DREGG_PAY_PRICE_USD` / `DREGG_PAY_PRICE_PER_RUN` | run price in USDC / `$DREGG` |
| `DREGG_PAY_DREGG_DISCOUNT_BPS` | `$DREGG` holder discount (default 2000 = 20%) |
| `DREGG_PAY_OTC_DISCOUNT_BPS` | OTC discount (default 1000 = 10%) |
| `DREGG_PAY_DREGG_DECIMALS` | mint decimals (6) |

## Custody contract (non-negotiable)
- The **seed** (`DREGG_PAY_SEED`) derives per-user deposit addresses *and* signs
  sweeps. On ed25519 there is **no watch-only derivation** — deriving needs the
  seed — so the seed lives in a **secured operator sweeper service you run**, not
  in the bot process and never in the repo.
- The **bot/platform stays watch-only** where possible: it watches the derived
  deposit addresses and credits users; the seed-holding sweeper is a *separate*
  operator service. (The bot's encrypted `key_vault` is the fallback only if you
  choose to run it self-contained for a small demo — accept the higher risk.)
- **Un-swept float is the only at-risk balance.** Sweep often → float stays tiny.

## Go-live sequence (each step gates the next)
1. **Provision the durable notary key** and publish its verifying key out-of-band
   as the trust root (so provenance is verifiable). `dregg-pay`'s hosted notary is
   a separate pinned party — see `zkoracle-live/src/notary_server.rs`.
2. **Watch-only dry run.** `DREGG_PAY_NETWORK=mainnet`, real `DREGG_PAY_RPC`, **no
   sweeper key loaded.** Confirm the `SolanaWatcher` (reusing `bridge/src/
   solana_holdings.rs`'s consensus-verified SPL decode) *sees* a real deposit to a
   derived address and credits the right user. No spending yet. For the
   consensus-verified (not RPC-trusting) read the watcher requires a pinned
   `WeakSubjectivityAnchor` — configure the real governance-chosen
   `(epoch, stake_table_root)`; the anchored path fails closed without it.
3. **One small real payment**, end-to-end: send a few `$DREGG` to a user's derived
   deposit address → the watcher credits → a paid `/dungeon` run executes on real
   Bedrock under the per-user cap → the **MPC-TLS attestation** is handed back
   ("you paid for real Claude, here's the proof").
4. **Enable the sweeper** (operator service, seed loaded) → it sweeps deposits to
   `DREGG_PAY_TREASURY` on a cadence. Verify the treasury USDC/`$DREGG` balances
   update (`Treasury::record_payment` routes USDC→fuel, `$DREGG`→pile).
5. **Fund the inference budget** from the USDC treasury; monitor
   `spend_inference_usd` drawdown (it fails closed on empty — the **refuel
   signal**). Alert when USDC fuel is low.
6. **Open the OTC** (quote only until settlement is wired): `otc_quote` gives
   `$DREGG`-out for USDC-in at the 10% discount, pile-checked.

## Deferred — behind YOUR signer (vote authorizes, you sign)
Never automated; each executes only under an operator-held signature:
- **Jupiter swap execution** (`$DREGG→SOL→USDC`) — pricing/quote wired; a passed
  **collective liquidity vote** (the `collective_choice` quorum) *authorizes* it;
  **you sign** the swap tx.
- **OTC transfer settlement** (`otc_settle`) — `otc_quote` computes + checks; moving
  the `$DREGG` to the buyer is operator-signed.

## Rollback
Set `DREGG_PAY_NETWORK=devnet` (or unset the mainnet env) → the rail reverts to
mock instantly. Un-swept mainnet deposits stay recoverable via the seed (the
sweeper). See [DISASTER-RECOVERY.md](DISASTER-RECOVERY.md) for a lost-seed drill —
**a lost `DREGG_PAY_SEED` strands un-swept deposits**, so back it up like any
treasury key ([KEY-MANAGEMENT.md](KEY-MANAGEMENT.md)).
