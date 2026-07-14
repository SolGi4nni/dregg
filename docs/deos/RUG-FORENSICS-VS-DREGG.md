# Rug Forensics vs. DreggLaunchpad — validating the anti-rug thesis against REAL rugs

**What this is.** A forensic scrape-and-compare. We pulled the mechanism of real,
documented launchpad / DegenFi rugs (NOXA's orbit, HypervaultFi, Meerkat Finance,
SQUID) and dissected *exactly how each drains*, then went vector-by-vector against
our own launchpad contracts
(`chain/contracts/launchpad/{DreggLaunchpad,DreggLaunchToken,DreggSolventPool,IClearingAttestor}.sol`)
to confirm we structurally lack each rug door — or flag, honestly, any door we do
not close.

**Honest sourcing note (read first).** Public block explorers (Etherscan, BscScan,
Hacken) return **HTTP 403 to automated fetch** (Cloudflare), and x.com returns 402,
so we could **not** byte-for-byte pull the verified Solidity into this doc. We did
**not** fabricate contract source to fill the gap. Instead every rug below is cited
to a **published post-mortem / rekt writeup that quotes the on-chain mechanism and
function selectors**, with the contract address where reporting gives one. Our own
contract citations ARE first-hand (`file:line`, read directly from the repo at HEAD).
Where a specific contract could not be located (NOXA), we say so and fall back to the
documented behavior rather than invent code.

---

## 1. The dissected rugs (real cases, cited)

### 1.1 NOXA (@Noxa_Fi) — the headline, honestly characterized

The brief named NOXA ("First DegenFi protocol… always first on new blockchains,"
built by @AmunPhantom) as "recently rugged." **We could not confirm a clean
contract-level NOXA rug event, and we will not invent one.** What the record
actually shows:

- NOXA is itself a **DegenFi launchpad + DEX** — and, notably, it is live **on
  Robinhood Chain**, the *same* Arbitrum-Orbit L2 (chainId 46630) our
  `DreggLaunchpad` targets. It reportedly generated ~$7.66M in fees over 7 days on
  Robinhood Crypto (Onchain Lens, X). So NOXA is best read as a **direct competitor
  concept** to our launchpad, not a single rugged token.
- There are multiple `$NOXA` deployments: a **pump.fun token on Solana**
  (`5xyQAiYGQ4DZwGXxTjP2kfR7gKEuRZVjW9sVjgeDpump` — the `…pump` suffix marks a
  pump.fun bonding-curve launch) and an earlier **DBK Chain** launch (built by
  DeBankDeFi, 2025) that "remained inactive," followed by a reported **40% supply
  burn**. NOXA's own DEX on HyperEVM has `v2Factory
  0xeC4a56061d86955D0Df883efb2E5791d99Ea71f2` / `v2Router
  0xfDE31CCAf95b8bF65a0D3805CD1668969787992c` (Uniswap-v2-style AMM).
- The most concrete "rug"-adjacent event in reporting is a **malicious token
  (`$HOODETF`) launched *through* a NOXA-style immutable launchpad**, which
  commentators noted was *easy to shut down precisely because* "projects launch
  without the team controlling the contract or the liquidity… everything is
  immutable and verifiable on-chain" (Flowslikeosmo, X).

**Why this is the sharpest framing anyway.** The interesting comparison is not
"NOXA the token rugged" (unconfirmed) but the *category*: a permissionless DegenFi
launchpad on the same chain we deploy to, where the launchpad is immutable but the
**tokens launched on it are the actual rug surface**. That is exactly the surface
our per-launch invariants (§2) are built to close. So the taxonomy below draws its
concrete mechanism from three rugs whose on-chain behavior IS documented, and treats
NOXA as the category exemplar / competitor.

Sources: [NOXA docs](https://docs.noxa.fi/), [DefiLlama: NOXA](https://defillama.com/protocol/noxa),
[Onchain Lens on NOXA fees / 40% burn](https://x.com/OnchainLens/status/2076396620623855650),
[Flowslikeosmo on the $HOODETF shutdown](https://x.com/Flowslikeosmo/status/2076030374979735880),
[NOXA Fun launchpad](https://fun.noxa.fi/robinhood).

### 1.2 HypervaultFi — owner-controlled vault drain (~$3.6M, Hyperliquid, Sep 2025)

A yield-vault protocol on Hyperliquid promising up to 76–95% APY. **Mechanism:**
user deposits pooled into a **team-controlled vault**; the operator withdrew the
pooled principal, **bridged it out** of Hyperliquid to Ethereum via DeBridge,
swapped to ETH, and deposited **752 ETH into Tornado Cash**, then deactivated X and
Discord. PeckShield flagged the withdrawal. ~1,100 depositors hit. The published
reporting does **not** disclose the precise privileged function (admin key vs. proxy
upgrade), but the class is unambiguous: **custodial pooled deposits + a privileged
withdrawal path = owner-drain.** This is the vector our launchpad's *absence of any
admin/operator custody* addresses.

Sources: [Cryptopolitan](https://www.cryptopolitan.com/hypervaultfi-suspected-rug-pull-takes-3-6m/),
[The Currency Analytics](https://thecurrencyanalytics.com/altcoins/hypervaultfi-rug-pull-drains-3-6m-from-hyperliquid-users-and-disappears-201016),
[Yahoo Finance](https://finance.yahoo.com/news/hyperliquid-based-project-faces-3-093814438.html).

### 1.3 Meerkat Finance — proxy-upgrade backdoor (~$31M, BSC, Mar 2021)

A BSC yield-farm. **Mechanism (documented at the selector level):** the vaults used
**OpenZeppelin's Transparent Proxy** pattern. The deployer **did not hand the proxy
admin to the timelock**, so they could call **`upgradeTo(address newImplementation)`
directly on the proxy**, swap in malicious logic, and then invoke a drain function
(selector **`0x70fcb0a7`**) that transferred **13,968,039 BUSD + 73,635 WBNB** to
the attacker as recipient. Framed as a "hack," the on-chain data (deployer-initiated
upgrade, no timelock) reads as a planned exit. This is the canonical
**proxy-upgrade backdoor**: the code you audited is not the code that runs.

Sources: [Obelisk Auditing post-mortem](https://obeliskauditing.com/blog/articles/meerkat-rug-article),
[Meerkat malicious-proxy post-mortem (HackMD)](https://hackmd.io/@mLAPku2WQZmso5oX4kzPOg/BkNlZv0zO),
[rekt.news](https://rekt.news/meerkat-finance-bsc-rekt),
[Vidma anatomy](https://www.vidma.io/blog/meerkat-finance-anatomy-of-a-31-million-defi-rug-pull-on-binance-smart-chain).

### 1.4 SQUID (Squid Game token) — honeypot transfer restriction (~$3.3M, BSC, Nov 2021)

The Netflix-hype token that ran to ~$2,860 (+40,000%) then to ~$0 in minutes.
**Mechanism (documented):** the **`transfer` / `transferFrom`** path carried an
extra condition that **blocked the *sell* direction unless the sender was the owner
or an address in a privileged `marketersAndDevs` mapping** (`onlyOwner` +
whitelist bypass). Buyers could buy; only the devs could sell. When retail piled in,
the devs sold and the price collapsed. This is the **honeypot** vector: liquidity is
visible but non-owner sells revert.

Sources: [Threatpost](https://threatpost.com/squid-game-crypto-scammers-investors/175951/),
[Kraken Learn: honeypots](https://www.kraken.com/learn/honeypot-crypto-scam),
[dev.to rug-pull analysis](https://dev.to/copyleftdev/cryptocurrency-rug-pull-scams-a-comprehensive-analysis-18ga).

### 1.5 Mintable-supply classic — owner `mint()` inflation

Not a single project but the most common launchpad-token rug and the one our token
is purpose-built against: the token exposes **`function mint(address,uint256)
external onlyOwner`** (or an unlocked minter role). The dev waits for the price to
rise, mints an "overdose" of new supply to their own wallet, and dumps it into the
pool. Reported repeatedly in honeypot/rug taxonomies (Coinmonks, DEXTools).

Sources: [Coinmonks: types of scam in the smart contract](https://medium.com/coinmonks/main-types-of-scam-how-to-find-in-the-smartcontract-ac0380dd234b),
[DEXTools rug checklist 2026](https://www.dextools.io/tutorials/how-to-spot-a-rug-pull-2026-checklist).

---

## 2. Rug-vector × our-defense matrix

Legend: **✅ STRUCTURALLY ABSENT** = the door does not exist in our source at all;
**⚠ BOUNDED** = a related capability exists but is constrained so it cannot rug;
**⚑ GAP** = a real residual we do not close in-contract (§3).

| # | Rug vector | How the real rug does it (cited) | Our defense — or GAP (cited `file:line`) | Verdict |
|---|-----------|----------------------------------|------------------------------------------|---------|
| 1 | **Hidden / mintable supply** | Owner `mint()` inflates supply after pump (§1.5); dev dumps new tokens | `DreggLaunchToken.mint` is one-shot: `if (msg.sender != minter) revert NotMinter`; `if (minted) revert AlreadyMinted`; `if (amount > cap) revert CapExceeded` — `cap`/`minter` are `immutable`, `minted` is a latch, **no second mint path exists** (`DreggLaunchToken.sol:28,33,37,65-73`). Launchpad also forces `saleSupply+creatorAllocation+poolAllocation == totalSupply` or reverts `SupplyDoesNotClose` (`DreggLaunchpad.sol:219`). | ✅ ABSENT |
| 2 | **Owner-drain of pooled funds** | Team-controlled vault; privileged withdraw of depositor principal → bridge → Tornado (HypervaultFi §1.2) | **There is no owner/admin/governance role in any of our contracts** (grep: no `Ownable`, `onlyOwner`, `admin`, `pause`). Escrow is per-bidder; `settleBid` pays each bidder *their own* tokens+refund (`:428`); `reclaimEscrow` is permissionless and returns `msg.sender`'s *own* `deposit` (`:462`). No function sends pooled funds to an operator. | ✅ ABSENT |
| 3 | **LP-pull / liquidity removal** | Dev `removeLiquidity` / burns LP and takes reserves | **`DreggSolventPool` has no `removeLiquidity`, no LP token, no owner-withdraw.** Reserves move only via `buy`/`sell`, each floored: `if (reserveTokenAfter < floorToken) revert PoolFloorBreached` (`:135`) and `if (reserveQuoteAfter < floorQuote) revert PoolFloorBreached` (`:161`). No privileged path drains the pool below the disclosed floor. | ✅ ABSENT (see §3.2 on floor size) |
| 4 | **Honeypot (buy-but-can't-sell)** | `transfer`/`transferFrom` blocks the sell direction unless sender ∈ owner/`marketersAndDevs` whitelist (SQUID §1.4) | `DreggLaunchToken._transfer` has **no owner check, no whitelist/blacklist, no direction condition** — only `if (bal < value) revert InsufficientBalance` (`:95-103`). `DreggSolventPool.sell` is open to any caller who `approve`s (`:149`); the only gate is the solvency floor, never identity. | ✅ ABSENT |
| 5 | **Proxy-upgrade backdoor** | `upgradeTo(newImpl)` on a Transparent Proxy (no timelock) swaps in draining logic (Meerkat §1.3, selector `0x70fcb0a7`) | **No proxy pattern in our source** (grep: no `delegatecall`, `upgradeTo`, `implementation` slot). Token and pool are deployed with `new DreggLaunchToken` / `new DreggSolventPool` (`DreggLaunchpad.sol:228,576`) — immutable bytecode, non-upgradeable. `initialize` is the pool's latch-guarded one-shot seed, **not** a proxy initializer (`DreggSolventPool.sol:106-116`, guarded by `graduation` + `initialized`). | ✅ ABSENT in-source — but see §3.1 (deployment integrity) |
| 6 | **Blacklist / pausable-then-drain** | `pause()` freezes holders so only owner trades; or `blacklist[victim]` blocks sells | **No `Pausable`, no `pause`, no `blacklist`/`blocklist` mapping anywhere** (grep clean). No global switch can freeze trading or single out a holder. | ✅ ABSENT |
| 7 | **Hidden allocation / stealth pre-mint / hidden clearing** | Dev pre-mints a chunk, or clears the sale at a hidden price/allocation to insiders | Creator allocation is **disclosed and vesting-locked**: `claimCreatorAllocation` reverts before `creatorLockUntil` (`DreggLaunchpad.sol:511-520`). Clearing is **uniform-price + permutation-checked**: `_assertPermutation` enforces no-drop/no-insert and `_runClearing` requires descending price — a hidden extra fill cannot be inserted, and every winner pays the same `clearingPrice` (`:381-420`). | ✅ ABSENT |
| 8 | **Fake LP lock** | "LP locked" but the lock is owner-controlled / a no-op | **No LP token to fake-lock.** The pool *is* the liquidity and is non-withdrawable + floored; graduation seeding is deterministic and enforced (`GraduationSeedMismatch` if the seed is wrong/skimmed, `DreggLaunchpad.sol:566-568`). No lock to trust. | ✅ ABSENT (trust eliminated, not asserted) |
| 9 | **Rug-via-liveness (funds stuck, no recovery)** | Contract stalls; deposits are trapped with no refund path | `reclaimEscrow` gives every committer a **permissionless full refund** once the clearing window (`revealEnd + REFUND_GRACE = 7 days`) elapses without a clearing; the clearing and refund windows are **disjoint** (`ClearingWindowClosed`), so worst case is stall-then-refund, never loss (`DreggLaunchpad.sol:132,339-374,462-482`). | ✅ ABSENT |

**Grep evidence for the "ABSENT" claims** (run over
`chain/contracts/launchpad/*.sol` at HEAD): no match for
`ownable|onlyOwner|admin|governance` (the sole `owner` token is the standard ERC-20
`Approval` event parameter), no match for `pause|blacklist|blocklist|whitelist`, no
match for `delegatecall|upgradeTo|proxy|implementation`, no match for
`selfdestruct`. The two `initialize` hits are the pool's one-shot seed, not proxy
initializers.

---

## 3. Honest gaps and boundaries — where the thesis is *narrower* than "rug-proof"

The nine vectors above are structurally closed **in our source**. But "rug-proof"
is an overclaim, and the brief demands we flag the residual honestly. None of these
is an exploitable in-contract drain door; each is a boundary of the guarantee.

### 3.1 Deployment integrity is an *operational* assumption, not self-enforced (residual trust)
Every "no proxy / immutable" claim is about **the source as written**. A deployer
could, in principle, place the *launchpad itself* behind a proxy, or deploy modified
bytecode. The launchpad cannot prove-about-itself that it is not proxied. **Residual
trust:** a verifier must check that the *deployed* `DreggLaunchpad` bytecode matches
this audited source and is not behind an upgradeable proxy. (Note the token and pool
*are* safe by construction *given* an honest launchpad, because the launchpad
deploys them itself via `new` — so this residual collapses to a single object: the
launchpad's own deployment.) This is a real caveat, not a code vector; it should be
stated wherever the anti-rug claim is made.

### 3.2 "Provably solvent" means never-drains-to-zero, NOT price protection
The pool floor is `FLOOR_BPS = 2000` = **20% of the seed** (`DreggLaunchpad.sol:79`).
So up to **80% of a reserve can still legitimately exit** through priced swaps
(`sell` takes ETH out down to `floorQuote`; each such swap *adds* tokens to the other
reserve — it is market activity, not a free drain). The guarantee is
`pool_solvent_forever` = **the pool can never be emptied below its floor by anyone,
including via any privileged path — there is none**. It is **not** a promise that
the *price* holds: a coordinated sell wave can still crater the price toward the
floor. Solvency ≠ no-loss. State the floor precisely; do not let "provably solvent"
be read as "can't lose money."

### 3.3 The launchpad guarantees a FAIR SALE + SOLVENT MARKET, not project delivery ("soft rug")
`withdrawProceeds` sends the raise proceeds to the creator
(`DreggLaunchpad.sol:495-505`). This is **legitimate by design** — it is the buyers'
payment for tokens *actually delivered at a fair uniform clearing price*, with
non-winners and over-deposits refunded — and it is emphatically *not* the
HypervaultFi vector (it is not depositor principal held in custody for yield). But it
does mean the contract cannot stop a **"soft rug"**: a team that raises fairly, takes
its fairly-earned proceeds, and then abandons the project. The creator allocation is
vesting-locked (dev-dump guard) and the pool stays solvent, but the *proceeds* are
the creator's. This is the honest outer boundary of the anti-rug thesis: **we make
the *launch mechanics* non-rug-pullable; we do not underwrite the team's diligence.**

### 3.4 Scope the brief already flags (not gaps, but not "done")
Per `DREGG-LAUNCHPAD-DESIGN.md` §0: uniform-price clearing *fairness* is PROVED in
Lean and the on-chain compute is a faithful **replayable** implementation, but the
real dregg-Groth16 clearing **attestation** (`IClearingAttestor`, rung 2) is a named
weld — a launch today runs on rung 1 (replayable) with the attestor slot open. Full
bonded-conduct slashing / shielded participation is designed-not-built. These are
labeled resolutions on the trajectory, not rug vectors.

---

## 4. Verdict

**Sharpest finding.** The three rugs whose mechanism is documented at the code level
each exploit a door our contracts **do not have**:

- Meerkat's `upgradeTo` proxy-swap → we ship **non-upgradeable `new`-deployed**
  contracts (no `delegatecall`, no proxy).
- SQUID's owner/whitelist **sell-blocking `transfer`** → our `_transfer` and pool
  `sell` have **no identity gate** at all.
- HypervaultFi's team-vault **privileged withdrawal** → we have **no
  owner/admin/operator role and no custody of pooled principal** (per-bidder escrow,
  permissionless refund).

And the classic **mintable-supply** rug dies against our one-shot, hard-capped,
single-minter `DreggLaunchToken`.

**The real residual (flagged, not hand-waved).** We are **not** "rug-proof," and the
doc says so precisely: (1) the whole story rests on **deployment integrity** — verify
the deployed launchpad bytecode matches this source and is not itself proxied (§3.1);
(2) "provably solvent" is **never-to-zero (20% floor), not price protection** (§3.2);
(3) the contract cannot prevent a **soft rug** where a team takes fairly-raised
proceeds and walks (§3.3). None of these is an in-contract drain vector — they are
the honest edges of the guarantee.

**Conclusion.** Against real, documented rugs — not hypotheticals — DreggLaunchpad's
contracts **structurally lack all nine dissected rug doors at the source level**. The
anti-rug thesis holds *for launch mechanics*, with three named boundaries
(deployment integrity, solvency-≠-price, soft-rug) that must travel with the claim
every time it is made.
