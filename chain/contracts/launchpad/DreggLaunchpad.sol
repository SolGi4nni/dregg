// SPDX-License-Identifier: MIT
pragma solidity ^0.8.20;

import {DreggLaunchToken} from "./DreggLaunchToken.sol";
import {ILaunchEligibility} from "./ILaunchEligibility.sol";
import {IClearingAttestor} from "./IClearingAttestor.sol";

/// @title DreggLaunchpad
/// @notice The provably-fair token launchpad — the EVM realization of the four
///         verified turns in `docs/deos/DREGG-LAUNCHPAD-DESIGN.md` §2, deployable
///         to Robinhood Chain (Arbitrum-Orbit L2, chainId 46630). A launch is:
///
///   (a) REGISTRATION with a DISCLOSED supply/vesting schedule, committed
///       on-chain and publicly checkable — NO HIDDEN SUPPLY (§2.1). The token is
///       a `DreggLaunchToken`: hard-capped, minted exactly once for the whole
///       disclosed supply, no second mint door.
///   (b) a SEALED-BID batch raise: bidders commit `H(price‖qty‖salt‖bidder)`
///       during the commit window, then reveal (§2.2, `SealedAuction`). No bid is
///       observable before clearing, and a reveal that does not open its
///       commitment is rejected — NO SNIPE / NO LATE-SWITCH.
///   (c) UNIFORM-PRICE clearing: the whole revealed book clears at ONE price,
///       computed on-chain by a permutation-checked descending sort (no-drop /
///       no-insert, `Market/Aggregation.lean`) + a marginal-fill walk. Every
///       winner pays the SAME price — the mechanism whose fairness is PROVED in
///       `Market/Optimality.lean` (`uniform_price_no_arbitrage`,
///       `uniform_price_envy_free`). An optional `IClearingAttestor` binds a real
///       dregg Groth16 clearing proof (the PROVED rung; the named weld).
///   (d) NON-CUSTODIAL settlement: each winner pays the clearing price, receives
///       tokens, and is refunded the rest of its deposit; the creator withdraws
///       proceeds; the creator allocation is VESTING-LOCKED until the disclosed
///       cliff — the dev-dump guard (§3, vector A).
///
/// ## Trust grades (honest, per `DREGG-LAUNCHPAD-DESIGN.md` §0 spine)
/// - supply disclosure + one-shot mint: BUILT/on-chain-enforced (no hidden door).
/// - sealed commit→reveal (no peek / no late-switch): BUILT/on-chain-enforced.
/// - uniform-price clearing fairness: the MECHANISM is PROVED in Lean; the
///   on-chain computation is a faithful REPLAYABLE implementation; a real
///   dregg-Groth16 clearing attestation is the named weld (rung 2).
/// - creator vesting lock (dev-dump guard): BUILT/on-chain-enforced.
/// - full bonded-conduct slashing / shielded participation: designed-not-built
///   (§4, §5) — NOT in this MVP.
///
/// Quote currency is native ETH (Robinhood Chain / Base-Sepolia gas token).
contract DreggLaunchpad {
    // ─── Phases ───────────────────────────────────────────────────────────────
    enum Phase {
        None, // 0 — no such launch
        Commit, // 1 — accepting sealed commitments
        Reveal, // 2 — accepting reveals
        Cleared, // 3 — uniform price computed, settling
        Finalized // 4 — creator withdrew proceeds
    }

    // ─── The disclosed schedule (the committed public inputs of creation) ───────
    struct Schedule {
        uint256 totalSupply; // whole tokens, the disclosed cap
        uint256 saleSupply; // whole tokens offered in the raise
        uint256 creatorAllocation; // whole tokens kept by the creator (locked)
        uint64 creatorLockUntil; // vesting cliff: creator alloc claimable after
        uint256 reservePrice; // min wei-per-whole-token for a winning bid
    }

    struct Launch {
        address creator;
        DreggLaunchToken token;
        bytes32 scheduleCommit; // keccak(abi.encode(Schedule)) — publicly checkable
        uint256 totalSupply;
        uint256 saleSupply;
        uint256 creatorAllocation;
        uint64 creatorLockUntil;
        uint256 reservePrice;
        uint64 commitEnd;
        uint64 revealEnd;
        Phase phase;
        uint256 clearingPrice; // the uniform price (set at finalizeClearing)
        uint256 soldQty; // whole tokens actually cleared
        uint256 proceeds; // wei collected (winners' payments)
        bool proceedsWithdrawn;
        bool creatorAllocClaimed;
        ILaunchEligibility gate; // 0 = open participation
        IClearingAttestor attestor; // 0 = REPLAYABLE-only (rung 1)
        bool clearingAttested; // true iff a dregg clearing proof attested it
        uint256 revealedCount;
    }

    struct Bid {
        bytes32 sealedHash; // H(price‖qty‖salt‖bidder)
        uint256 deposit; // ETH escrowed at commit (>= max payment)
        bool committed;
        bool revealed;
        uint256 price; // wei per whole token (revealed)
        uint256 qty; // whole tokens demanded (revealed)
        uint256 filled; // whole tokens awarded (set at clearing)
        bool settled;
    }

    uint256 public constant TOKEN_UNIT = 1e18;

    uint256 public launchCount;
    mapping(uint256 => Launch) private _launches;
    mapping(uint256 => mapping(address => Bid)) private _bids;
    mapping(uint256 => address[]) private _revealedBidders;

    // ─── Events ───────────────────────────────────────────────────────────────
    event LaunchRegistered(
        uint256 indexed launchId,
        address indexed creator,
        address token,
        bytes32 scheduleCommit,
        uint64 commitEnd,
        uint64 revealEnd
    );
    event BidCommitted(uint256 indexed launchId, address indexed bidder, bytes32 sealedHash, uint256 deposit);
    event BidRevealed(uint256 indexed launchId, address indexed bidder, uint256 price, uint256 qty);
    event Cleared(uint256 indexed launchId, uint256 clearingPrice, uint256 soldQty, bool attested);
    event BidSettled(uint256 indexed launchId, address indexed bidder, uint256 filled, uint256 paid, uint256 refunded);
    event ProceedsWithdrawn(uint256 indexed launchId, address indexed creator, uint256 amount);
    event CreatorAllocationClaimed(uint256 indexed launchId, address indexed creator, uint256 amount);

    // ─── Errors ───────────────────────────────────────────────────────────────
    error SupplyDoesNotClose(uint256 sale, uint256 creator, uint256 total); // hidden supply
    error BadWindow();
    error NoSuchLaunch(uint256 launchId);
    error NotCommitPhase();
    error NotRevealPhase();
    error NotClearPhase();
    error AlreadyCommitted();
    error NotEligible(address bidder);
    error NoCommit();
    error BidMismatch(); // reveal does not open the commitment
    error AlreadyRevealed();
    error UnderCollateralized(uint256 deposit, uint256 needed);
    error RevealWindowOpen();
    error BadPermutation(); // not a permutation of revealed bids (drop/insert)
    error NotSortedDescending(); // book not in uniform-clearing order
    error ClearingNotAttested();
    error NothingToSettle();
    error NotCreator();
    error CreatorLockActive(uint64 until);
    error AlreadyDone();
    error TransferFailed();

    // ─── (a) Registration — disclosed supply, no hidden door ────────────────────

    /// @notice Register a launch with a fully DISCLOSED schedule. The accounting
    ///         MUST close: `saleSupply + creatorAllocation == totalSupply`. A
    ///         schedule that hides supply (does not close) reverts — there is no
    ///         undisclosed allocation. A hard-capped token is minted ONCE for the
    ///         whole disclosed supply into launchpad custody: `saleSupply` for the
    ///         raise, `creatorAllocation` held under the vesting lock.
    function registerLaunch(
        string calldata tokenName,
        string calldata tokenSymbol,
        Schedule calldata s,
        uint64 commitDuration,
        uint64 revealDuration,
        ILaunchEligibility gate,
        IClearingAttestor attestor
    ) external returns (uint256 launchId) {
        // NO HIDDEN SUPPLY: the disclosed parts must exactly account for the cap.
        if (s.saleSupply + s.creatorAllocation != s.totalSupply || s.totalSupply == 0) {
            revert SupplyDoesNotClose(s.saleSupply, s.creatorAllocation, s.totalSupply);
        }
        if (commitDuration == 0 || revealDuration == 0) revert BadWindow();

        launchId = ++launchCount;

        DreggLaunchToken token =
            new DreggLaunchToken(tokenName, tokenSymbol, s.totalSupply * TOKEN_UNIT, address(this));
        // The single disclosed mint — the whole cap, into launchpad custody.
        token.mint(address(this), s.totalSupply * TOKEN_UNIT);

        uint64 commitEnd = uint64(block.timestamp) + commitDuration;
        uint64 revealEnd = commitEnd + revealDuration;

        Launch storage L = _launches[launchId];
        L.creator = msg.sender;
        L.token = token;
        L.scheduleCommit = keccak256(abi.encode(s));
        L.totalSupply = s.totalSupply;
        L.saleSupply = s.saleSupply;
        L.creatorAllocation = s.creatorAllocation;
        L.creatorLockUntil = s.creatorLockUntil;
        L.reservePrice = s.reservePrice;
        L.commitEnd = commitEnd;
        L.revealEnd = revealEnd;
        L.phase = Phase.Commit;
        L.gate = gate;
        L.attestor = attestor;

        emit LaunchRegistered(launchId, msg.sender, address(token), L.scheduleCommit, commitEnd, revealEnd);
    }

    /// @notice Publicly check a disclosed schedule against the on-chain commitment.
    ///         Anyone (a launch page, a re-executor) recomputes and compares — the
    ///         REPLAYABLE disclosure. True iff `s` is exactly what was committed.
    function checkSchedule(uint256 launchId, Schedule calldata s) external view returns (bool) {
        return _launches[launchId].scheduleCommit == keccak256(abi.encode(s));
    }

    // ─── (b) Sealed commit → reveal ─────────────────────────────────────────────

    /// @notice Commit a SEALED bid. `sealedHash == H(price‖qty‖salt‖bidder)`; only
    ///         the seal is public during the commit window, so there is no bid to
    ///         observe and no earliest-block edge to win. Escrow `msg.value` (must
    ///         cover the eventual payment). One commitment per address (MVP).
    /// @param proof optional eligibility evidence for a gated launch.
    function commitBid(uint256 launchId, bytes32 sealedHash, bytes calldata proof) external payable {
        Launch storage L = _launches[launchId];
        if (L.phase == Phase.None) revert NoSuchLaunch(launchId);
        if (L.phase != Phase.Commit || block.timestamp >= L.commitEnd) revert NotCommitPhase();

        if (address(L.gate) != address(0) && !L.gate.eligible(launchId, msg.sender, proof)) {
            revert NotEligible(msg.sender);
        }

        Bid storage b = _bids[launchId][msg.sender];
        if (b.committed) revert AlreadyCommitted();

        b.committed = true;
        b.sealedHash = sealedHash;
        b.deposit = msg.value;

        emit BidCommitted(launchId, msg.sender, sealedHash, msg.value);
    }

    /// @notice Reveal a committed bid. The reveal is accepted ONLY in the reveal
    ///         window (revealing during commit reverts — no peek) and ONLY if it
    ///         opens the exact committed seal (`BidMismatch` otherwise — no
    ///         late-switch to a different bid after seeing others). This is the
    ///         `SealedAuction.reveal_binds_committed` / `reveal_requires_reveal_phase`
    ///         guarantee, on-chain.
    function revealBid(uint256 launchId, uint256 price, uint256 qty, bytes32 salt) external {
        Launch storage L = _launches[launchId];
        if (L.phase == Phase.None) revert NoSuchLaunch(launchId);
        // Fail-closed on off-phase reveals: not before commit seals, not after.
        if (block.timestamp < L.commitEnd || block.timestamp >= L.revealEnd) revert NotRevealPhase();
        if (L.phase == Phase.Commit) L.phase = Phase.Reveal;

        Bid storage b = _bids[launchId][msg.sender];
        if (!b.committed) revert NoCommit();
        if (b.revealed) revert AlreadyRevealed();

        // NO LATE-SWITCH: the reveal must open the committed seal exactly.
        if (keccak256(abi.encode(price, qty, salt, msg.sender)) != b.sealedHash) revert BidMismatch();

        // The escrow must cover the bidder's own maximum payment.
        if (b.deposit < price * qty) revert UnderCollateralized(b.deposit, price * qty);

        b.revealed = true;
        b.price = price;
        b.qty = qty;
        _revealedBidders[launchId].push(msg.sender);
        L.revealedCount++;

        emit BidRevealed(launchId, msg.sender, price, qty);
    }

    // ─── (c) Uniform-price clearing ─────────────────────────────────────────────

    /// @notice Compute the UNIFORM clearing price on-chain and award fills.
    ///
    ///         The caller supplies `order`, a claimed descending-by-price ordering
    ///         of the revealed bidders (untrusted search). The contract VERIFIES
    ///         it (translation-validation style):
    ///           - it is a PERMUTATION of all revealed bids (each index exactly
    ///             once) — NO-DROP / NO-INSERT (`Market/Aggregation.lean`); a
    ///             hidden extra allocation cannot be inserted into the cleared book.
    ///           - prices are NON-INCREASING along it — the canonical clearing
    ///             order; a non-uniform / mis-ordered clearing reverts.
    ///         Then a marginal-fill walk fills bids top-down until `saleSupply` is
    ///         exhausted; the LAST filled price is the single uniform clearing
    ///         price every winner pays (`uniform_price_envy_free`).
    ///
    ///         If an attestor is pinned, a real dregg clearing proof must attest
    ///         the computed (saleSupply, clearingPrice, bookCommit) — the PROVED
    ///         rung 2. With no attestor, the launch runs on rung 1 (REPLAYABLE).
    function finalizeClearing(uint256 launchId, uint256[] calldata order, bytes calldata clearingProof)
        external
    {
        Launch storage L = _launches[launchId];
        if (L.phase == Phase.None) revert NoSuchLaunch(launchId);
        if (block.timestamp < L.revealEnd) revert RevealWindowOpen();
        if (L.phase == Phase.Cleared || L.phase == Phase.Finalized) revert NotClearPhase();

        // Permutation-checked descending-sort + marginal-fill walk (kept in a
        // helper to stay under the stack-depth limit).
        (uint256 clearingPrice, uint256 sold, bytes32 bookCommit) =
            _runClearing(launchId, order, L.saleSupply, L.reservePrice);

        // Optional PROVED rung: a real dregg clearing proof must attest the
        // on-chain-computed clearing before it is accepted.
        bool attested = false;
        if (address(L.attestor) != address(0)) {
            if (!L.attestor.attestClearing(launchId, L.saleSupply, clearingPrice, bookCommit, clearingProof)) {
                revert ClearingNotAttested();
            }
            attested = true;
        }

        L.clearingPrice = clearingPrice;
        L.soldQty = sold;
        L.clearingAttested = attested;
        L.phase = Phase.Cleared;

        emit Cleared(launchId, clearingPrice, sold, attested);
    }

    /// Verify `order` is a permutation of the revealed book sorted descending by
    /// price, walk it filling up to `saleSupply` at/above `reservePrice`, and set
    /// each winner's `filled`. Returns (uniform clearing price, total sold, a
    /// commitment to the whole revealed book). Reverts on drop/insert or a
    /// non-descending (non-uniform) order.
    function _runClearing(uint256 launchId, uint256[] calldata order, uint256 saleSupply, uint256 reservePrice)
        private
        returns (uint256 clearingPrice, uint256 sold, bytes32 bookCommit)
    {
        address[] storage revealed = _revealedBidders[launchId];
        _assertPermutation(order, revealed.length);

        uint256 prevPrice = type(uint256).max;
        for (uint256 i = 0; i < order.length; i++) {
            Bid storage b = _bids[launchId][revealed[order[i]]];
            // Sorted descending (the canonical uniform-clearing order).
            if (b.price > prevPrice) revert NotSortedDescending();
            prevPrice = b.price;

            // Fold the whole revealed book into a commitment (rung-2 binding).
            bookCommit = keccak256(abi.encodePacked(bookCommit, revealed[order[i]], b.price, b.qty));

            if (sold < saleSupply && b.price >= reservePrice) {
                uint256 fill = b.qty < saleSupply - sold ? b.qty : saleSupply - sold;
                if (fill > 0) {
                    b.filled = fill;
                    sold += fill;
                    clearingPrice = b.price; // marginal = lowest winning price
                }
            }
        }
    }

    /// The no-drop / no-insert check: `order` must be a permutation of [0,n) —
    /// each index present exactly once. Mirrors `Market/Aggregation.lean`'s
    /// `no_drop` / `no_insert` on the aggregated book.
    function _assertPermutation(uint256[] calldata order, uint256 n) private pure {
        if (order.length != n) revert BadPermutation();
        bool[] memory seen = new bool[](n);
        for (uint256 i = 0; i < n; i++) {
            uint256 idx = order[i];
            if (idx >= n || seen[idx]) revert BadPermutation();
            seen[idx] = true;
        }
    }

    // ─── (d) Non-custodial settlement ───────────────────────────────────────────

    /// @notice Settle one bidder after clearing: every winner pays the SAME
    ///         `clearingPrice` for its `filled` tokens (uniform price), receives
    ///         the tokens, and is refunded `deposit − payment`. A non-winner is
    ///         fully refunded. Permissionless (anyone can settle any bidder).
    function settleBid(uint256 launchId, address bidder) external {
        Launch storage L = _launches[launchId];
        if (L.phase != Phase.Cleared && L.phase != Phase.Finalized) revert NotClearPhase();

        Bid storage b = _bids[launchId][bidder];
        if (!b.revealed || b.settled) revert NothingToSettle();
        b.settled = true;

        uint256 payment = L.clearingPrice * b.filled;
        uint256 refund = b.deposit - payment; // deposit >= price*qty >= clearing*filled

        if (b.filled > 0) {
            L.proceeds += payment;
            L.token.transfer(bidder, b.filled * TOKEN_UNIT);
        }
        if (refund > 0) _sendEth(bidder, refund);

        emit BidSettled(launchId, bidder, b.filled, payment, refund);
    }

    /// @notice Creator withdraws the accumulated raise PROCEEDS (the winners'
    ///         payments), non-custodially. Callable after clearing; settle bidders
    ///         first to realize the full amount.
    function withdrawProceeds(uint256 launchId) external {
        Launch storage L = _launches[launchId];
        if (msg.sender != L.creator) revert NotCreator();
        if (L.phase != Phase.Cleared && L.phase != Phase.Finalized) revert NotClearPhase();
        if (L.proceedsWithdrawn) revert AlreadyDone();
        L.proceedsWithdrawn = true;
        L.phase = Phase.Finalized;
        uint256 amount = L.proceeds;
        if (amount > 0) _sendEth(L.creator, amount);
        emit ProceedsWithdrawn(launchId, L.creator, amount);
    }

    /// @notice Claim the creator's disclosed allocation — ONLY after the disclosed
    ///         vesting cliff (`creatorLockUntil`). Before the cliff this reverts:
    ///         the dev-dump guard (§3, vector A). No LP-withdrawal door exists —
    ///         the raise tokens are pool/holder-owned by settlement.
    function claimCreatorAllocation(uint256 launchId) external {
        Launch storage L = _launches[launchId];
        if (msg.sender != L.creator) revert NotCreator();
        if (block.timestamp < L.creatorLockUntil) revert CreatorLockActive(L.creatorLockUntil);
        if (L.creatorAllocClaimed) revert AlreadyDone();
        L.creatorAllocClaimed = true;
        uint256 amount = L.creatorAllocation * TOKEN_UNIT;
        if (amount > 0) L.token.transfer(L.creator, amount);
        emit CreatorAllocationClaimed(launchId, L.creator, amount);
    }

    // ─── Views ──────────────────────────────────────────────────────────────────

    function phaseOf(uint256 launchId) external view returns (Phase) {
        return _launches[launchId].phase;
    }

    function clearingPriceOf(uint256 launchId) external view returns (uint256) {
        return _launches[launchId].clearingPrice;
    }

    function soldQtyOf(uint256 launchId) external view returns (uint256) {
        return _launches[launchId].soldQty;
    }

    function tokenOf(uint256 launchId) external view returns (address) {
        return address(_launches[launchId].token);
    }

    function scheduleCommitOf(uint256 launchId) external view returns (bytes32) {
        return _launches[launchId].scheduleCommit;
    }

    function clearingAttested(uint256 launchId) external view returns (bool) {
        return _launches[launchId].clearingAttested;
    }

    function revealedCount(uint256 launchId) external view returns (uint256) {
        return _revealedBidders[launchId].length;
    }

    function getBid(uint256 launchId, address bidder)
        external
        view
        returns (bool committed, bool revealed, uint256 price, uint256 qty, uint256 filled, bool settled, uint256 deposit)
    {
        Bid storage b = _bids[launchId][bidder];
        return (b.committed, b.revealed, b.price, b.qty, b.filled, b.settled, b.deposit);
    }

    /// @notice The canonical sealed-hash preimage encoding — a bidder computes its
    ///         seal off-chain identically. `H(price‖qty‖salt‖bidder)`.
    function sealOf(uint256 price, uint256 qty, bytes32 salt, address bidder) external pure returns (bytes32) {
        return keccak256(abi.encode(price, qty, salt, bidder));
    }

    function _sendEth(address to, uint256 amount) private {
        (bool ok,) = payable(to).call{value: amount}("");
        if (!ok) revert TransferFailed();
    }
}
