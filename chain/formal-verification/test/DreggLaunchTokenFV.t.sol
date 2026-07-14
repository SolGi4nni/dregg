// SPDX-License-Identifier: MIT
pragma solidity ^0.8.20;

import {Test} from "forge-std/Test.sol";
import {DreggLaunchToken} from "contracts/launchpad/DreggLaunchToken.sol";

/// @title DreggLaunchToken — SYMBOLIC formal verification (Halmos)
/// @notice Proves the on-chain twins of the Lean supply theorems against the REAL
///         compiled `DreggLaunchToken` bytecode, over ALL inputs (symbolic), for a
///         bounded call sequence.
///
/// LEAN TIE:
///   * `execMintA_iff_spec` (metatheory/Dregg2/Verify/KeystoneAuditSupply.lean:124,
///     via Dregg2.Circuit.Spec.SupplyCreation) — the supply-authority biconditional:
///     "a supply the schedule does not disclose cannot enter circulation; the ledger
///     has no other mint door." The EVM twin proved here: NO sequence of calls mints
///     beyond `cap` or mints a second time.
///
/// WHY HALMOS (not solc SMTChecker/CHC): the guards use custom errors
/// (`revert CapExceeded(...)`, `revert AlreadyMinted()`). solc's CHC engine (0.8.26
/// and 0.8.30) does NOT model a `revert CustomError()` as a blocking path — it falls
/// through and reports SPURIOUS counterexamples (verified: `require` proves safe,
/// `revert CustomError()` does not). Halmos executes the compiled bytecode, where a
/// custom-error revert is just a REVERT opcode, so it is sound on these contracts.
///
/// BOUND: symbolic over ALL inputs (cap, caller, to, amount, selector); call-depth
/// bounded (the `_seqK` tests). This is a symbolic-bounded proof, NOT an unbounded
/// one — see README §The honest gap.
contract DreggLaunchTokenFV is Test {
    // Selector dispatch over the token's full external surface. `caller` is symbolic
    // (vm.prank), args symbolic; a revert leaves state unchanged (try/catch), which
    // is exactly what the invariant must survive.
    function _step(
        DreggLaunchToken t,
        uint8 sel,
        address caller,
        address a,
        address b,
        uint256 v
    ) internal {
        uint256 k = sel % 4;
        if (k == 0) {
            vm.prank(caller);
            try t.mint(a, v) {} catch {}
        } else if (k == 1) {
            vm.prank(caller);
            try t.transfer(a, v) {} catch {}
        } else if (k == 2) {
            vm.prank(caller);
            try t.approve(a, v) {} catch {}
        } else {
            vm.prank(caller);
            try t.transferFrom(a, b, v) {} catch {}
        }
    }

    // ── INVARIANT 1 — HARD CAP: totalSupply <= cap after ANY single call ──────────
    // The theorem-form of the "no supply beyond cap" forge test, over all inputs.
    function check_cap_singleCall(
        uint256 cap,
        address minter,
        uint8 sel,
        address caller,
        address a,
        address b,
        uint256 v
    ) public {
        vm.assume(cap != 0);
        DreggLaunchToken t = new DreggLaunchToken("N", "S", cap, minter);
        assert(t.totalSupply() == 0); // pre: nothing minted
        _step(t, sel, caller, a, b, v);
        assert(t.totalSupply() <= t.cap()); // INV holds after any call
    }

    // ── INVARIANT 1 — HARD CAP over a 3-call sequence (any selectors/callers) ─────
    // NO sequence of 3 arbitrary calls (by anyone) can push supply past the cap.
    function check_cap_seq3(
        uint256 cap,
        address minter,
        uint8 s1, address c1, address a1, address b1, uint256 v1,
        uint8 s2, address c2, address a2, address b2, uint256 v2,
        uint8 s3, address c3, address a3, address b3, uint256 v3
    ) public {
        vm.assume(cap != 0);
        DreggLaunchToken t = new DreggLaunchToken("N", "S", cap, minter);
        _step(t, s1, c1, a1, b1, v1);
        assert(t.totalSupply() <= t.cap());
        _step(t, s2, c2, a2, b2, v2);
        assert(t.totalSupply() <= t.cap());
        _step(t, s3, c3, a3, b3, v3);
        assert(t.totalSupply() <= t.cap());
    }

    // ── INVARIANT 2 — SINGLE MINT ("no hidden supply", the `minted` latch) ────────
    // Only `minter` can mint; the first mint sets totalSupply==amount<=cap and the
    // latch; EVERY subsequent mint (any caller, any amount) reverts and leaves
    // totalSupply frozen. The EVM twin of `execMintA_iff_spec`: one disclosed door.
    function check_singleMint_noSecondSupply(
        uint256 cap,
        address minter,
        address to1,
        uint256 amt1,
        address caller2,
        address to2,
        uint256 amt2
    ) public {
        vm.assume(cap != 0);
        DreggLaunchToken t = new DreggLaunchToken("N", "S", cap, minter);

        // First mint by the minter; if it succeeds, supply is fixed at amt1<=cap.
        vm.prank(minter);
        try t.mint(to1, amt1) {
            assert(t.minted());
            assert(t.totalSupply() == amt1);
            assert(amt1 <= cap);
        } catch {
            assert(!t.minted());
            assert(t.totalSupply() == 0);
        }

        uint256 supplyBefore = t.totalSupply();
        bool mintedBefore = t.minted();

        // ANY second mint attempt (any caller, any amount).
        vm.prank(caller2);
        try t.mint(to2, amt2) {
            // A second success is only reachable if the FIRST mint reverted
            // (i.e. this is really the first successful mint) — never two mints.
            assert(!mintedBefore);
        } catch {
            // If it reverted, supply is untouched.
            assert(t.totalSupply() == supplyBefore);
        }
        // In all cases: supply never exceeds cap and there is never a 2nd mint.
        assert(t.totalSupply() <= t.cap());
        assert(t.minted() == (t.totalSupply() > 0) || t.totalSupply() == 0);
    }

    // ── Only the minter may mint (the authority half of the biconditional) ────────
    function check_onlyMinterMints(
        uint256 cap,
        address minter,
        address caller,
        address to,
        uint256 amount
    ) public {
        vm.assume(cap != 0);
        vm.assume(caller != minter);
        DreggLaunchToken t = new DreggLaunchToken("N", "S", cap, minter);
        vm.prank(caller);
        try t.mint(to, amount) {
            assert(false); // a non-minter must NEVER succeed
        } catch {
            assert(t.totalSupply() == 0);
        }
    }
}
