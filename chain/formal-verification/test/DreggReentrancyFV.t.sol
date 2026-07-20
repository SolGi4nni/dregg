// SPDX-License-Identifier: MIT
pragma solidity ^0.8.20;

import {Test} from "forge-std/Test.sol";
import {DreggLaunchToken} from "contracts/launchpad/DreggLaunchToken.sol";
import {DreggSolventPool} from "contracts/launchpad/DreggSolventPool.sol";
import {LibClone1167} from "contracts/launchpad/LibClone1167.sol";

/// @title REENTRANCY-FREEDOM — SYMBOLIC formal verification (Halmos)
/// @notice A NEW anti-rug invariant, PROVEN not grepped: a state-changing function
///         that makes an external call is CHECKS-EFFECTS-INTERACTIONS correct, so a
///         re-entrant caller cannot drain funds it is not owed. This is the machine
///         proof of the reentrancy class that Stage-A grep never covered (it is a
///         Stage-C code-review class, `DREGG-AUDIT-SERVICE.md §C`) — turned into a
///         symbolic proof over the real compiled bytecode.
///
/// THE INVARIANT (INV-REENTRANCY): a contract that holds funds on behalf of many
/// parties never lets one party's external call (and its re-entrant callback)
/// reduce the funds owed to OTHERS. The classic reentrancy drain (DAO / CEI
/// violation: `send` BEFORE the balance write) lets a re-entrant attacker withdraw
/// its balance twice, stealing others' deposits. A CEI-correct contract (the effect
/// lands BEFORE the interaction) has no such door: the re-entrant read sees the
/// already-applied effect, so the second withdraw is refused.
///
/// TWO POLARITIES (mirrors DreggNoDrainFV):
///   * SAFE   — `SafeVault` (effect-before-interaction) and the REAL
///     `DreggSolventPool.sell` (reserves updated BEFORE `_sendEth`, pool source
///     lines 155-166) are PROVEN reentrancy-safe: a re-entrant caller cannot take
///     other holders' ETH / cannot push a reserve below its disclosed floor.
///   * UNSAFE — `ReentrantVault` (interaction-before-effect, the CEI VIOLATION)
///     admits a re-entrant-drain COUNTEREXAMPLE: an attacker deposits D, re-enters,
///     and extracts 2·D, stealing D from other depositors. Grep for `.call{value:}`
///     finds the external call; THIS proves whether the ordering is exploitable.
///
/// WHY HALMOS: identical to the sibling specs — the pool's guards use custom errors
/// (`PoolFloorBreached`) which solc CHC models as fall-through; Halmos runs the
/// bytecode. See README §1.
///
/// BOUND: reentrancy FV is symbolic-BOUNDED in re-entry DEPTH — the inline attacker
/// re-enters a bounded number of times (here: once, `reentries < 1`), so Halmos
/// proves "no drain up to that re-entry depth", not the unbounded ∀-depth statement.
/// All amounts symbolic; call depth bounded. Symbolic-bounded, like the siblings.
contract DreggReentrancyFV is Test {
    // ── SAFE: a CEI-correct vault is proven reentrancy-safe ──────────────────────
    // The attacker deposits D and attacks; a re-entrant withdraw during the ETH
    // callback sees the ALREADY-ZEROED balance and is refused. So the vault never
    // pays the attacker more than D, and the OTHER depositors' funds (`victimDep`)
    // are untouchable. PROVES reentrancy-freedom on the effect-before-interaction
    // shape, over all symbolic amounts, for the bounded re-entry depth.
    function check_safeVault_noReentrantDrain(uint256 victimDep, uint256 atkDep) public {
        vm.assume(victimDep != 0 && victimDep < 1e30);
        vm.assume(atkDep != 0 && atkDep < 1e30);
        SafeVault vault = new SafeVault();

        // A victim deposits real funds the attacker must not be able to steal.
        address victim = address(uint160(0xdead));
        vm.deal(victim, victimDep);
        vm.prank(victim);
        vault.deposit{value: victimDep}();

        ReentrantAttacker atk = new ReentrantAttacker(address(vault));
        vm.deal(address(atk), atkDep);
        atk.attack{value: atkDep}();

        // THE REENTRANCY TOOTH: the vault still fully covers the victim's deposit —
        // the attacker could not drain other holders' funds by re-entering.
        assert(address(vault).balance >= victimDep);
    }

    // ── UNSAFE: the CEI-violation vault admits a re-entrant-drain counterexample ──
    // `ReentrantVault` sends BEFORE zeroing the balance, so the attacker re-enters
    // and withdraws twice, stealing the victim's deposit. Halmos MUST find the
    // counterexample — proving the invariant has teeth (grep sees `.call{value:}`;
    // THIS proves the ordering is an exploitable drain).
    function check_reentrantVault_isAProvenDrain(uint256 victimDep, uint256 atkDep) public {
        vm.assume(victimDep != 0 && victimDep < 1e30);
        vm.assume(atkDep != 0 && atkDep < 1e30);
        ReentrantVault vault = new ReentrantVault();

        address victim = address(uint160(0xdead));
        vm.deal(victim, victimDep);
        vm.prank(victim);
        vault.deposit{value: victimDep}();

        ReentrantAttacker atk = new ReentrantAttacker(address(vault));
        vm.deal(address(atk), atkDep);
        atk.attack{value: atkDep}();

        assert(address(vault).balance >= victimDep); // EXPECTED: Counterexample (drain)
    }

    // ── SAFE (real surface): DreggSolventPool.sell is reentrancy-safe ────────────
    // The pool updates `reserveQuote`/`reserveToken` and enforces the solvency floor
    // BEFORE `_sendEth` (source lines 155-166). A re-entrant seller whose `receive`
    // calls `sell` again therefore sees the already-decremented reserves, and the
    // floor guard holds on the re-entrant call too. PROVES the disclosed floor
    // survives re-entry on the REAL compiled pool bytecode — the on-chain twin of
    // `pool_solvent_forever` under an adversarial re-entrant caller.
    function check_pool_sellIsReentrancySafe(
        uint256 quoteSeed, uint256 tokenSeed, uint256 floorQuote, uint256 floorToken, uint16 feeBps,
        uint256 tokenIn
    ) public {
        vm.assume(feeBps < 10000);
        vm.assume(quoteSeed != 0 && quoteSeed < 1e27);
        vm.assume(tokenSeed != 0 && tokenSeed < 1e27);
        vm.assume(floorToken <= tokenSeed && floorQuote <= quoteSeed);
        vm.assume(tokenIn != 0 && tokenIn < 1e27);

        DreggLaunchToken token = new DreggLaunchToken("N", "S", 1e30, address(this));
        token.mint(address(this), 1e30 - 1);
        // LIVE deployment shape (EIP-1167): clone the inert impl, seed tokens in,
        // then initialize (see DreggSolventPool §Deployment shape).
        DreggSolventPool impl = new DreggSolventPool();
        DreggSolventPool pool = DreggSolventPool(LibClone1167.clone(address(impl)));
        token.transfer(address(pool), tokenSeed);
        vm.deal(address(this), quoteSeed);
        pool.initialize{value: quoteSeed}(address(token), 1, floorQuote, floorToken, feeBps, tokenSeed);

        // A re-entrant seller: its `receive` re-enters `pool.sell` once.
        ReentrantSeller seller = new ReentrantSeller(address(pool), address(token));
        token.transfer(address(seller), tokenIn);
        seller.attack(tokenIn);

        // THE SOLVENCY TOOTH under re-entry: the disclosed floor is never breached,
        // even by an adversarial re-entrant caller.
        (uint256 rQuote,) = pool.reserves();
        (uint256 flQuote,) = pool.floors();
        assert(rQuote >= flQuote);
    }
}

// ─── Inline vaults (the reentrancy polarity pair; self-contained like RuggableToken) ─

/// A CEI-CORRECT vault: the effect (zeroing the balance) lands BEFORE the external
/// interaction (the ETH send). A re-entrant withdraw sees the zeroed balance and is
/// refused — no drain. This is the shape INV-REENTRANCY proves safe.
contract SafeVault {
    mapping(address => uint256) public balanceOf;

    function deposit() external payable {
        balanceOf[msg.sender] += msg.value;
    }

    function withdraw() external {
        uint256 amount = balanceOf[msg.sender];
        require(amount > 0, "nothing");
        balanceOf[msg.sender] = 0; // EFFECT first (checks-effects-interactions)
        (bool ok,) = msg.sender.call{value: amount}(""); // INTERACTION after
        require(ok, "send failed");
    }
}

/// The CEI-VIOLATION vault (DAO shape): the external interaction (ETH send) happens
/// BEFORE the effect (zeroing the balance). A re-entrant withdraw during the send
/// sees the STALE non-zero balance and withdraws again — the drain INV-REENTRANCY
/// must catch. Reconstructed, self-contained, audit-target only.
contract ReentrantVault {
    mapping(address => uint256) public balanceOf;

    function deposit() external payable {
        balanceOf[msg.sender] += msg.value;
    }

    function withdraw() external {
        uint256 amount = balanceOf[msg.sender];
        require(amount > 0, "nothing");
        (bool ok,) = msg.sender.call{value: amount}(""); // INTERACTION before effect
        require(ok, "send failed");
        balanceOf[msg.sender] = 0; // EFFECT after — the reentrancy door
    }
}

/// A generic re-entrant attacker: deposits, calls `withdraw`, and re-enters ONCE
/// from its `receive` while the vault still holds funds. Bounded re-entry depth
/// (`reentries < 1`) — the symbolic-bounded honesty note on the spec.
interface IVault {
    function deposit() external payable;
    function withdraw() external;
}

contract ReentrantAttacker {
    IVault public immutable target;
    uint256 public reentries;

    constructor(address t) {
        target = IVault(t);
    }

    function attack() external payable {
        target.deposit{value: address(this).balance}();
        target.withdraw();
    }

    receive() external payable {
        if (reentries < 1 && address(target).balance >= msg.value) {
            reentries++;
            try target.withdraw() {} catch {}
        }
    }
}

/// A re-entrant seller against the REAL pool: on receiving ETH from `sell`, it
/// re-enters `sell` once. Because the pool is CEI-correct, the re-entrant sell
/// operates on already-updated reserves and cannot breach the floor.
interface IPool {
    function sell(uint256 tokenIn, uint256 minQuoteOut) external returns (uint256);
}

interface IToken {
    function approve(address spender, uint256 value) external returns (bool);
    function balanceOf(address a) external view returns (uint256);
}

contract ReentrantSeller {
    IPool public immutable pool;
    IToken public immutable token;
    uint256 public reentries;

    constructor(address p, address t) {
        pool = IPool(p);
        token = IToken(t);
    }

    function attack(uint256 tokenIn) external {
        token.approve(address(pool), type(uint256).max);
        pool.sell(tokenIn, 0);
    }

    receive() external payable {
        if (reentries < 1) {
            reentries++;
            uint256 bal = token.balanceOf(address(this));
            if (bal > 0) {
                try pool.sell(bal, 0) {} catch {}
            }
        }
    }
}
