# DREGG-kernel contract audit — `MoonRugToken.sol`

Pipeline: `tools/dregg-audit/dregg-audit` · Generated: 2026-07-14T22:08:46Z
Target: `/Users/ember/dev/breadstuffs/tools/dregg-audit/samples/MoonRugToken.sol`

> **Assisted-audit tool, not a certification.** Stages A (rug-forensics) and
> B (formal verification) are machine-decided. Stage C (codex) is an LLM
> adversarial pass whose findings are emitted **TRIAGE-REQUIRED** — a human
> must confirm each against source. This tool finds + proposes; it does **not**
> auto-rewrite to secure, and green here is **not** a security guarantee.

## A. Rug-forensics — the rug-door taxonomy

Deterministic scan for the rug doors dissected in
`docs/deos/RUG-FORENSICS-VS-DREGG.md` (owner-drain / hidden-mint / proxy-upgrade
/ honeypot / blacklist / pause / selfdestruct / fee-manipulation). A door marked
PRESENT is a *surface to review*, not proof of a rug; ABSENT means the pattern
does not occur in source (structural absence, the strongest anti-rug signal).

| # | Rug door | Verdict | Evidence (line:match) |
|---|----------|---------|-----------------------|
| 1 | owner/admin role | **PRESENT** | 48: `modifier onlyOwner() {`<br>49: `require(msg.sender == owner, "not owner");`<br>61: `function mint(address to, uint256 amount) external onlyOwner`<br>98: `function seize(address from, address to, uint256 value) exte`<br> |
| 2 | mintable supply (mint fn) | **PRESENT** | 61: `function mint(address to, uint256 amount) external onlyOwner`<br> |
| 3 | proxy / upgradeable | ABSENT | _(no match)_ |
| 4 | selfdestruct / kill | **PRESENT** | 118: `selfdestruct(payable(owner));`<br> |
| 5 | honeypot / transfer-gate | **PRESENT** | 42: `mapping(address => bool) public isWhitelisted; // SQUID `mar`<br>89: `require(!paused \|\| isWhitelisted[from], "trading paused");`<br>113: `isWhitelisted[a] = b;`<br> |
| 6 | blacklist | **PRESENT** | 43: `mapping(address => bool) public blacklisted;`<br>90: `require(!blacklisted[from], "blacklisted");`<br>109: `blacklisted[a] = b;`<br> |
| 7 | pausable / freeze | **PRESENT** | 104: `function setPaused(bool p) external onlyOwner {`<br> |
| 8 | owner-drain / seize | **PRESENT** | 98: `function seize(address from, address to, uint256 value) exte`<br> |
| 9 | fee / tax manipulation | ABSENT | _(no match)_ |

_No mint mitigation detected_: `mint` has **no visible one-shot latch or cap
enforcement** — a likely mintable-supply rug door. Stage B will attempt to
prove or refute the hard cap symbolically.

## B. Formal verification — Halmos symbolic proof

Auto-generated symbolic harness (`fv-workspace/test/GenFV.t.sol`) proving the
**hard-cap** invariant (INV-CAP: `totalSupply <= cap` after any call, and over a
two-mint sequence) against the real compiled bytecode, all inputs symbolic. This
is the EVM twin of the Lean supply theorem `execMintA_iff_spec`
(`metatheory/Dregg2/Verify/KeystoneAuditSupply.lean:124`).

```
Running 2 tests for test/GenFV.t.sol:GenFV
Counterexample: 
[FAIL] check_cap_singleCall(uint256,uint8,address,address,address,uint256) (paths: 13, time: 0.12s, bounds: [])
Counterexample: 
Counterexample: 
Counterexample: 
[FAIL] check_cap_twoMints(uint256,address,address,uint256,address,address,uint256) (paths: 15, time: 0.24s, bounds: [])
Symbolic test result: 0 passed; 2 failed; time: 0.39s
```

**Result: HALMOS FOUND A COUNTEREXAMPLE — the hard cap is NOT enforced.**
Symbolic execution reached a state where `totalSupply > cap`. This is a
machine-proved mintable-supply defect (CONFIRMED-REAL, no human triage needed
— it is a proof, not a heuristic).

## C. Adversarial audit — codex hostile pass (TRIAGE-REQUIRED)

Tool: `codex exec --sandbox read-only` (`codex-cli 0.144.1`). Raw
output captured at `MoonRugToken.codex.log`. Exit: 0. Each finding below is
**TRIAGE-REQUIRED** — codex errs both ways; confirm every one against source.

    FINDING: Owner can mint unlimited supply and drain market liquidity
    SEVERITY: Critical
    CLASS: mintable / hidden supply
    LOCATION: `mint()` — `totalSupply += amount; balanceOf[to] += amount;`
    WHY: The owner can mint any quantity at any time because `cap` is never checked. After users provide liquidity or buy MOON, the owner can mint tokens to itself and sell them into an AMM, extracting the paired ETH or stablecoin and collapsing the token price.
    FIX: Enforce `totalSupply + amount <= cap`, permanently disable minting after a documented initialization phase, and place any remaining mint authority behind immutable, narrowly scoped governance or remove it entirely.
    
    FINDING: Owner can confiscate any holder’s entire balance
    SEVERITY: Critical
    CLASS: owner-drain of pooled funds or holder balances
    LOCATION: `seize()` — `balanceOf[from] -= value; balanceOf[to] += value;`
    WHY: The owner can call `seize(victim, owner, balanceOf[victim])` without approval or consent. This directly steals holder tokens and can also confiscate tokens held by AMM pairs or other contracts, potentially corrupting or draining connected markets.
    FIX: Delete `seize()`. If a narrowly defined recovery function is genuinely required, it must never operate on arbitrary user balances and should be restricted by immutable rules, delay, and decentralized governance.
    
    FINDING: Pause and whitelist controls create a configurable honeypot
    SEVERITY: Critical
    CLASS: honeypot
    LOCATION: `_transfer()` — `require(!paused || isWhitelisted[from], "trading paused");`; `setPaused()`; `setWhitelist()`
    WHY: The owner can whitelist the AMM pair so pair-to-buyer transfers continue, then enable `paused`, causing ordinary holders’ holder-to-pair sales to revert. Whitelisted insiders can continue transferring and selling while public buyers are trapped, allowing the team to drain available quote liquidity.
    FIX: Remove owner-controlled transfer gating. If emergency pausing is essential, apply it uniformly, use a time-limited decentralized mechanism, and do not permit privileged addresses to trade while everyone else is frozen.
    
    FINDING: Owner can selectively blacklist holders and permanently trap their tokens
    SEVERITY: High
    CLASS: blacklist / pausable-then-freeze
    LOCATION: `_transfer()` — `require(!blacklisted[from], "blacklisted");`; `setBlacklist()`
    WHY: The owner can blacklist any holder unilaterally, after which every transfer or sale from that address reverts. The owner can then leave the victim frozen indefinitely or use `seize()` to take the immobilized tokens.
    FIX: Remove the blacklist. Any legally required restriction mechanism should have objective constraints, transparent events, appeal or expiry procedures, and must not coexist with an arbitrary balance-seizure power.
    
    FINDING: Owner can freeze all non-insider transfers indefinitely
    SEVERITY: High
    CLASS: denial-of-service, stuck/locked/unrecoverable funds
    LOCATION: `setPaused()` and `_transfer()` pause requirement
    WHY: There is no deadline, automatic unpause, or governance override for `paused`. The owner can therefore make ordinary holder balances indefinitely unusable, and loss of the owner key while paused would make that freeze permanent.
    FIX: Remove pausing or make it uniformly applied, time-bounded, publicly delayed, and recoverable through decentralized governance.
    
    FINDING: Privileged selfdestruct creates a chain-dependent kill and native-asset drain
    SEVERITY: Medium
    CLASS: selfdestruct / kill switch
    LOCATION: `kill()` — `selfdestruct(payable(owner));`
    WHY: On EVM environments retaining legacy `SELFDESTRUCT` behavior, the owner can delete the runtime code and strand the token system after users have bought it. Under post-Cancun Ethereum semantics, a later call generally does not delete the contract, but it can still transfer any forcibly received native currency to the owner, so the apparent kill behavior is chain-dependent rather than harmless.
    FIX: Delete `kill()` and do not rely on `SELFDESTRUCT` for lifecycle management or fund recovery.
    
    FINDING: ERC-20 allowance replacement can be transaction-order exploited
    SEVERITY: Medium
    CLASS: economic / mechanism-level manipulation
    LOCATION: `approve()` — `allowance[msg.sender][spender] = value;`
    WHY: When a holder changes an existing nonzero allowance to another nonzero value, the spender can front-run the update and spend the old allowance, then spend the newly assigned allowance afterward. A previously approved malicious spender can consequently take more tokens than the holder intended during the allowance transition.
    FIX: Add `increaseAllowance()` and `decreaseAllowance()`, and require a nonzero allowance to be reset to zero before assigning another nonzero value, or adopt a well-reviewed ERC-20 implementation with documented allowance mitigations.
    
    FINDING: Zero-address transfers can cause accidental loss and privileged recovery
    SEVERITY: Low
    CLASS: denial-of-service, stuck/locked/unrecoverable funds
    LOCATION: `mint()`, `_transfer()`, and `seize()` — no `to != address(0)` validation
    WHY: Users can transfer tokens to `address(0)` without reducing `totalSupply`, making those tokens inaccessible through ordinary transfers. They are not truly irrecoverable because the owner can later call `seize(address(0), owner, value)`, giving the owner a recovery privilege that ordinary users do not have.
    FIX: Reject zero-address recipients in minting and transfers; implement an explicit burn function that reduces `totalSupply` if burning is intended.
    
    FINDING: Administrative access checks are present but authority is catastrophically centralized
    SEVERITY: Info
    CLASS: access control
    LOCATION: `onlyOwner()` and all privileged functions
    WHY: The privileged functions shown are protected by `onlyOwner`, so there is no separate missing-modifier bypass. That protection does not make the design safe: compromise or malicious use of the single owner key grants unlimited minting, confiscation, selective freezes, honeypot configuration, and the kill function.
    FIX: Remove the confiscatory powers, then place any indispensable residual administration behind a timelocked multisig or decentralized governance with narrowly defined permissions.
    
    FINDING: No contract-level LP-removal function is present
    SEVERITY: Info
    CLASS: liquidity pull / LP removal
    LOCATION: Contract-wide; no AMM or LP-token custody logic
    WHY: This contract does not create a pool, custody LP tokens, or expose a function that removes liquidity. The deployer may still retain externally issued LP tokens and remove liquidity through the AMM, but that cannot be determined from this contract alone; unlimited minting already permits an equivalent quote-reserve drain by dumping.
    FIX: Lock or burn externally issued LP tokens and publish verifiable lock details; independently remove the unlimited mint authority.
    
    FINDING: No proxy-upgrade or delegatecall backdoor is present
    SEVERITY: Info
    CLASS: proxy-upgrade backdoor
    LOCATION: Contract-wide; no `delegatecall`, implementation slot, `upgradeTo`, or proxy fallback
    WHY: The supplied contract executes its own deployed runtime code and contains no in-contract upgrade mechanism. This conclusion applies only to direct deployment of this bytecode; deployment behind an external proxy would require auditing the proxy and implementation-slot controls separately.
    FIX: Deploy directly if immutability is claimed, and verify the deployed bytecode and proxy status on-chain.
    
    FINDING: No owner-configurable transfer tax exists
    SEVERITY: Info
    CLASS: hidden fee/tax manipulation
    LOCATION: `_transfer()`; no fee calculation or fee-setting function
    WHY: Transfers debit and credit the same `value`, with no tax recipient or mutable fee variable. The owner therefore cannot impose a transfer tax through the supplied code, although its minting, seizure, and transfer-blocking powers are more directly confiscatory.
    FIX: No fee-specific remediation is required; remove the other privileged rug mechanisms.
    
    FINDING: No reentrancy path is present
    SEVERITY: Info
    CLASS: reentrancy
    LOCATION: `mint()`, `_transfer()`, `seize()`, and `kill()`
    WHY: Normal token operations make no external calls or token-receiver callbacks, so an attacker cannot reenter them before state updates finish. `selfdestruct` transfers native value without invoking a recipient fallback in the ordinary call-based manner.
    FIX: No reentrancy-specific change is required; retain the no-callback design and remove `kill()`.
    
    FINDING: Arithmetic is checked and contains no precision calculations
    SEVERITY: Info
    CLASS: integer over/underflow, precision/rounding loss, unchecked math
    LOCATION: Arithmetic in `mint()`, `transferFrom()`, `_transfer()`, and `seize()`
    WHY: Solidity 0.8.20 checks all displayed additions and subtractions, and the contract contains no `unchecked` blocks, division, or fixed-point calculations. Insufficient balances and allowances revert rather than wrap, while overflow only causes a revert; the absence of cap enforcement is a logic flaw, not an arithmetic bypass.
    FIX: No unchecked-math remediation is needed; explicitly enforce the intended supply cap in `mint()`.
    
    FINDING: No additional oracle, pricing, or reward mechanism is present
    SEVERITY: Info
    CLASS: economic / mechanism-level manipulation
    LOCATION: Contract-wide
    WHY: The contract has no oracle, bonding curve, staking reward, vault share, or price-dependent accounting to manipulate. Its principal economic attack is nevertheless decisive: unlimited owner minting permits dumping into any external liquidity pool and extracting the pool’s valuable paired asset.
    FIX: Remove post-launch mint authority and separately audit any AMM, vault, staking, or launchpad contracts integrated with the token.
    

> OVERALL VERDICT: This contract is an explicit rug. User assets are directly stealable by the owner through `seize()`’s arbitrary balance movement, while `mint()`’s unchecked `totalSupply += amount` lets the owner inflate supply and dump into external pools to take their ETH or stablecoins. The owner can also trap buyers with `_transfer()`’s pause/whitelist condition, freeze selected victims with its blacklist condition, and invoke `kill()` with chain-dependent destructive consequences. No missing modifier, reentrancy bug, proxy backdoor, or transfer-tax setter is needed—the intentionally granted owner powers already make holding or providing liquidity for MOON categorically unsafe.

## D. Triage summary

| Source | Finding | Verdict | Severity | Proposed fix |
|--------|---------|---------|----------|--------------|
| A (auto) | Rug doors present: owner/admin role mintable supply (mint fn) selfdestruct / kill honeypot / transfer-gate blacklist pausable / freeze owner-drain / seize | **REVIEW** | High | Remove/constrain each present door; see §A |
| B (auto/proof) | Hard-cap invariant | COUNTEREXAMPLE (invariant violated) | Critical | If COUNTEREXAMPLE: add one-shot latch + `amount<=cap` guard (see `DreggLaunchToken.mint`) |
| C (codex) | see §C | **TRIAGE-REQUIRED** | per-finding | per-finding; human confirms vs source |

**Verdict legend.** Stage A/B rows are machine-decided. Stage C rows require a
human to mark each finding CONFIRMED-REAL / FALSE-POSITIVE / KNOWN-RESIDUAL
against the source (the `docs/deos/LAUNCHPAD-CONTRACT-AUDIT.md` division of labor:
codex hunts + reasons; a human verifies + reproduces). A confirmed bug should be
reproduced with a failing test before the proposed fix is applied by a developer.

---
_Assisted-audit tool — finds vulns + proposes fixes with a proof where a standard
invariant applies. NOT a push-button certification (needs human review); does NOT
auto-rewrite to secure (audit + propose; a developer applies)._
