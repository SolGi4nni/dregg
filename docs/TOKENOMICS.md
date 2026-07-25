# $DREGG and the units of the dregg economy

*What the token is, what it does, what it deliberately doesn't. Present-tense, code-grounded.
Maturity labels: **LIVE** (mainnet/live surface), **RUNS** (green on test/mock), **BUILT** (real
code, not exercised live), **POLICY** (a governed choice, not a protocol law), **DESIGN** (intended,
not built).*

## $DREGG in a paragraph

$DREGG is a fixed-supply SPL token on Solana (~1B units, pump.fun launch). The protocol never mints
it — that's a **POLICY** backed by a real fixed SPL, not a claim about the kernel. When $DREGG enters
dregg's state it's a 1:1 mirror against tokens locked in a vault; the executor refuses any mirror-mint
that would break `live_supply ≤ currently_locked`, and redeeming burns the mirror before release
(**BUILT**). No mainnet mint address is pinned in code — it's an operator env decision; confirm the
canonical contract out-of-band.

## The kernel doesn't set monetary policy — it enforces authorization

Every turn is net-zero per asset (**LIVE**) — you can't create value inside a transfer. Tokens come
into existence exactly one way: a capability-gated **mint** by the token's issuer (and a cell can't
coin its own supply). A **burn** is the permissionless inverse and is *conserving* — it moves tokens
to an issuer well that holds negative supply, so circulating supply falls while the books stay
balanced. Nothing is ever destroyed out of the accounting.

The consequence worth stating once: the kernel supports mintable **and** fixed-supply tokens. Which
one $DREGG is, is $DREGG's policy. Other tokens run whatever policy their issuer chooses. There's no
protocol-level inflation of $DREGG because we chose a fixed SPL — not because the kernel forbids
minting.

## What $DREGG does

- **Buys services, never power.** The pay rail (`dregg-pay`) gives each user a Solana deposit address;
  send $DREGG or USDC → run-credits. A run is ~$0.10 in USDC; paying in $DREGG earns a ~20% holder
  discount (Jupiter oracle). **RUNS on mock; the mainnet flip is not made** — the live game is free.
- **Governs, by proof-of-holdings.** Voting weight is a snapshot proof that you hold your own $DREGG;
  per-poll nullifiers defeat flash-loan voting. No staking, no lockups, no yield. **BUILT.**
- **Never buys features.** Across the games: $DREGG buys credits/hosting/cosmetics — never power,
  never yield. In-play units (gold, hp, echoes, relics, soulbound badges) are decoupled from real
  value; power is earned by playing, not purchased. **LIVE.**

## Security is game-based, and penalties redistribute

The base can't inflate, so security comes from bonds and forfeiture, not emissions:
- **Conduct bonds** — a deployer posts a bond, escrow-locked while a launch is live, slashable on
  proven misconduct behind a timelocked, vetoable process. **BUILT (PoC).**
- **Relay dispute slashing** — a dropped custody obligation is convicted by a referee; the bond
  **redistributes** (restitution to the wronged party, remainder to a treasury). **LIVE.**
- **Equivocation court** — two conflicting blocks for one slot → an auto-firing court seizes the bond.
  **RUNS.**

Penalties **redistribute, they don't destroy** — at worst into a **DAO-governed treasury**, and the
**DAO can vote to burn**. Burning is a governance policy on a redistributing base, not a hardcoded
protocol sink. (One mechanism, the court, *can* be configured to send its seizure to an unspendable
sink — the metering unit, not $DREGG — but that's an option, not the rule.) And bonds aren't
denominated in the token they police: the senior deterrence tranche is in a quote/metering unit,
$DREGG at most a junior first-loss (**DESIGN**).

## Treasury and business

"USDC is the fuel, $DREGG is the pile." USDC funds inference and fails closed when empty; $DREGG
accrues to an illiquid treasury that's **recycled, not market-dumped** (a governed swap, or an OTC
desk selling pile $DREGG at a discount to people bringing USDC). No $DREGG is market-sold to pay
bills, and none is burned today (**BUILT/POLICY**). The one product that moves value across cells
today is **agent-platform** — renting confined agent "grains" for per-period rent (**RUNS**) —
alongside AI-narration credits, execution leases, a compute exchange, async STARK proving, and TEE
attestation.

## Not built yet (so nobody's surprised)

- **No native fungible-token standard** (no ERC-20/Token-2022 equivalent with lifecycle hooks). The
  primitive is `cell + token_id + issuer-well`. Interim: issue on Solana/EVM and settle a proof about
  that L2 into dregg (the on-chain peer-verification we're building). Native dreggic tokens with
  lifecycle hooks are **DESIGN**.
- **Burns as value accrual.** The burn primitives exist; today value accrues via services + the
  recycled treasury. If burns ever accrue value, it'll be a DAO **POLICY**, named and voted.
- **The mainnet payment flip.** Real $DREGG has never been accepted; the go-live runbook is gated.

---
*Sibling docs: `docs/deos/INTERCHAIN-MODEL.md`, `docs/deos/PROOF-OF-HOLDINGS.md`,
`docs/deos/DREGG-BOND-DESIGN.md`, `docs/deos/TOKEN-MIRROR-BRIDGE.md`.*
