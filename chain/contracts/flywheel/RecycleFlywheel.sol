// SPDX-License-Identifier: MIT
pragma solidity ^0.8.20;

import {DreggLaunchToken} from "../launchpad/DreggLaunchToken.sol";
import {DreggSolventPool} from "../launchpad/DreggSolventPool.sol";
import {LibClone1167} from "../launchpad/LibClone1167.sol";

/// @title RecycleFlywheel
/// @notice The dregg VERIFIABLE recycle mechanism — the CIRC-style fee-flywheel
///         with every property CIRC leaves "visible/trusted" replaced by one that
///         is enforced-by-contract, and every step left as a prev-hash-chained
///         signed receipt a non-witness re-checks. It is a COMPOSITION of landed,
///         proven launchpad pieces (`docs/reference/CIRC-COMPETITIVE-ANALYSIS.md`
///         §4.2), not new science:
///
///   1. ACCRUE — each fee inflow is recorded WITH a source-receipt hash: provenance
///      is folded into `provenanceRoot`, not an anonymous transfer (§5.2).
///   2. SPLIT — a PURE function of `(accrued, buyBps)` where `buyBps` is a committed
///      constructor input. The finalizer must pass the split it believes correct; a
///      wrong/hidden split REVERTS `SplitMismatch` — the exact `GraduationSeedMismatch`
///      pattern (`DreggLaunchpad.sol:619`). The operator CANNOT deviate; contrast
///      `MockCircFlywheel.setSplitBps`, an owner-key door.
///   3. CLEAR — the "buy" is a SEALED-BID uniform-price batch clearing over sellers'
///      asks, cleared by a permutation-checked ascending sort + marginal-fill walk
///      (the dual of `DreggLaunchpad._runClearing` / `_assertPermutation`,
///      `Market/Aggregation.lean` no-drop/no-insert). There is NO telegraphed swap
///      to sandwich, and the clearing is ORDER-INVARIANT — the §2.1(e) front-run is
///      unconstructable, not mitigated.
///   4. POOL — the bought tokens + the pool-half (+ any unspent budget) seed a
///      `DreggSolventPool`, floor-guarded (`PoolFloorBreached`, rung-6). The seed is
///      the disclosed, checked amount.
///   5. CONSERVE + EMIT — the recycle asserts per-asset `netFlow = 0` on-chain (the
///      on-chain twin of `Market/Priced.lean priced_clearing_keystone`) and emits a
///      prev-hash-chained, operator-SIGNED receipt whose head a non-witness
///      re-derives from public data (`verifyReceipt`).
///
/// ## Honest trust grades (per the analysis §4.3 — do NOT overclaim)
/// - front-run resistance / order-invariance / split-enforcement / floor-guarded
///   pool / conservation check / signed receipt chain: BUILT + on-chain-enforced
///   here (both polarities tested in `test/RecycleFlywheelAB.t.sol`).
/// - The underlying MECHANISM fairness (`uniform_price_no_arbitrage`) and
///   conservation (`priced_clearing_keystone`) are PROVED in Lean; this contract is
///   a faithful REPLAYABLE realization, not itself the Lean statement.
/// - NAMED WELD, unclosed (§4.3.1): the receipt does NOT bind the clearing to an
///   in-circuit price proof — a non-witness re-derives the price from the PUBLIC
///   book (rung-1 replayable), so a corrupt operator can WITHHOLD but cannot
///   MISPRICE; binding the clearing tuple inside a Groth16 statement is future work
///   (PROTOTYPED at the circuit level: `chain/gnark/clearing_snark.go` proves the
///   clearing tuple against this contract's exact book-fold layout; the on-chain
///   verify entry point is the named remaining piece).
/// - `.sol ↔ Lean` correspondence is prose, not mechanized (§4.3.2).
///
/// Single-lifecycle per instance (one recycle), for a clean A/B measurement.
/// Quote currency is native ETH.
contract RecycleFlywheel {
    // ─── Committed public inputs (the disclosed schedule of the recycle) ────────
    DreggLaunchToken public immutable token;
    /// THE COMMITTED SPLIT — bps of the accrued fee routed to the buy leg. Fixed at
    /// construction: a public, unchangeable fact of this recycle. There is NO setter
    /// (the CIRC deviation door is absent by construction).
    uint16 public immutable buyBps;
    /// The operator whose signature attests the receipt head (re-checkable off-chain).
    address public immutable operator;

    uint16 public constant FLOOR_BPS = 2000; // disclosed solvency floor (rung-6)
    uint16 public constant POOL_FEE_BPS = 30; // graduated-pool swap fee

    // ─── Phases ─────────────────────────────────────────────────────────────────
    enum Phase {
        Commit, // 0 — fees accrue + sellers commit sealed asks
        Reveal, // 1 — sellers reveal
        Cleared // 2 — buy cleared, pool seeded, receipt emitted
    }

    // `phase`, the signature v byte, and the pool address share ONE slot (8+8+160
    // bits) — finalize turns three cold SSTOREs into warm writes of a slot the
    // reveal already opened. Public getters are unchanged.
    Phase public phase;
    uint8 private _sigV;
    DreggSolventPool public pool;

    uint64 public immutable commitEnd;
    uint64 public immutable revealEnd;

    // ─── Accrual + provenance ───────────────────────────────────────────────────
    uint256 public accrued; // total fees in (wei)
    // The two counters share a slot (each bounded by the number of txs ever, far
    // under 2^128); getters keep their selectors (return-type width is not part
    // of a selector and decodes identically).
    uint128 public inflowCount; // number of accrue() calls
    uint128 public provenancedCount; // inflows carrying a nonzero source-receipt hash
    bytes32 public provenanceRoot; // fold of (sourceReceiptHash, amount) — the provenance chain

    // ─── Sealed asks (the sell-side of the recycle buy) ─────────────────────────
    // Packed to 3 slots (was 7). The widths are DOCUMENTED RANGE BOUNDS enforced
    // by checked casts at entry (revert `ValueOutOfRange`, never truncate):
    // price < 2^128 wei/token (~3.4e20 ETH/token), qty < 2^96 whole tokens
    // (~7.9e28), escrow < 2^128 base units — all astronomically above any real
    // book. Packing makes reveal (price+qty+flag), the clearing's fill write, and
    // settle's flag write WARM single-slot updates instead of cold 20k SSTOREs.
    struct Ask {
        bytes32 sealedHash; // slot 0: H(price‖qty‖salt‖seller)
        uint128 escrow; // slot 1: tokens escrowed at commit (>= revealed qty)
        uint96 filled; // slot 1: whole tokens taken by the clearing
        bool settled; // slot 1
        uint128 price; // slot 2: wei per whole token (ask), revealed
        uint96 qty; // slot 2: whole tokens offered, revealed
        bool committed; // slot 2
        bool revealed; // slot 2
    }

    mapping(address => Ask) private _asks;
    address[] private _revealedSellers;

    uint256 public constant TOKEN_UNIT = 1e18;

    // ─── Cleared result ─────────────────────────────────────────────────────────
    // Only the PRIMARY cleared facts are stored; everything else in the receipt is
    // a pure function of them + the committed inputs, recomputed by view (identical
    // values, the redundant SSTOREs removed — the receipt stays fully re-derivable,
    // which is its entire point). Price+quantity share a slot: the price is an ask
    // price (already < 2^128 by the reveal bound); the quantity is checked-cast.
    uint128 public uniformPrice; // the single price every filled seller is paid (wei/token)
    uint128 public boughtTokens; // whole tokens the recycle bought
    bytes32 public bookCommit; // fold of the whole revealed book (order-independent content)

    // ─── The receipt (prev-hash-chained, operator-signed, re-checkable) ─────────
    struct Receipt {
        // ACCRUE step
        uint256 accrued;
        bytes32 provenanceRoot;
        uint256 inflowCount;
        // SPLIT step
        uint256 buyHalf;
        uint256 poolHalf;
        uint16 buyBps;
        // CLEAR step
        uint256 uniformPrice;
        uint256 boughtTokens;
        uint256 spentQuote;
        bytes32 bookCommit;
        // POOL step
        uint256 quoteSeed;
        uint256 tokenSeed;
        uint256 floorQuote;
        uint256 floorToken;
        // CONSERVE step (both zero — the netFlow=0 tooth)
        int256 netQuote;
        int256 netToken;
    }

    // The receipt itself is NOT stored: every field is a pure function of public
    // state (see `_liveReceipt`), so storing it would be ~14 redundant SSTOREs.
    // Only the signed chain head + the operator signature (as r‖s‖v) persist.
    bytes32 public receiptHead; // the signed chain head
    bytes32 private _sigR;
    bytes32 private _sigS;
    // (the signature v byte lives packed with `phase` + `pool` above)

    // ─── Events ─────────────────────────────────────────────────────────────────
    event FeeAccrued(address indexed from, uint256 amount, bytes32 sourceReceiptHash, bytes32 provenanceRoot);
    event AskCommitted(address indexed seller, bytes32 sealedHash, uint256 escrow);
    event AskRevealed(address indexed seller, uint256 price, uint256 qty);
    event RecycleCleared(uint256 uniformPrice, uint256 boughtTokens, uint256 spentQuote, bytes32 bookCommit);
    event PoolSeeded(address indexed pool, uint256 quoteSeed, uint256 tokenSeed, uint256 floorQuote, uint256 floorToken);
    event ReceiptEmitted(bytes32 receiptHead);
    event AskSettled(address indexed seller, uint256 filled, uint256 paidQuote, uint256 returnedTokens);

    // ─── Errors ─────────────────────────────────────────────────────────────────
    error NotCommitPhase();
    error NotRevealPhase();
    error NotClearPhase();
    error RevealWindowOpen();
    error AlreadyCommitted();
    error NoCommit();
    error AlreadyRevealed();
    error AskMismatch(); // reveal does not open the seal
    error UnderEscrowed(uint256 escrow, uint256 qty);
    error TransferFromFailed();
    error TransferFailed();
    error BadPermutation();
    error NotSortedAscending();
    /// The disclosed committed split, ENFORCED — a wrong/hidden split reverts.
    /// The CIRC-key deviation is unconstructable (mirror `GraduationSeedMismatch`).
    error SplitMismatch(uint256 correctBuyHalf, uint256 correctPoolHalf);
    /// The per-asset netFlow=0 tooth — a recycle that mints or destroys value reverts.
    error ConservationBroken(int256 netQuote, int256 netToken);
    error BadReceiptSignature();
    error ReceiptHeadMismatch(bytes32 computed);
    error NothingBought();
    error NothingToSettle();
    /// A value exceeds its documented packed-field bound (price < 2^128 wei/token,
    /// qty < 2^96 whole tokens, escrow < 2^128 base units) — refused at entry,
    /// never truncated.
    error ValueOutOfRange();

    /// The one inert `DreggSolventPool` implementation this recycle's pool is an
    /// EIP-1167 clone of — a COMMITTED public input like `token`/`buyBps`
    /// (deployed once per chain, shared with the launchpad; ~41k proxy create
    /// instead of a ~713k per-recycle code deposit).
    address public immutable poolImplementation;

    constructor(
        address token_,
        uint16 buyBps_,
        address operator_,
        uint64 commitDuration,
        uint64 revealDuration,
        address poolImplementation_
    ) {
        require(buyBps_ > 0 && buyBps_ < 10000, "buyBps");
        require(poolImplementation_ != address(0), "poolImpl");
        token = DreggLaunchToken(token_);
        buyBps = buyBps_;
        operator = operator_;
        commitEnd = uint64(block.timestamp) + commitDuration;
        revealEnd = commitEnd + revealDuration;
        phase = Phase.Commit;
        poolImplementation = poolImplementation_;
    }

    // ─── (1) ACCRUE — fee in, WITH provenance ───────────────────────────────────

    /// @notice Accrue a fee inflow tagged with the hash of the receipt of the work
    ///         that produced it (a `TurnReceipt`/game-move/clearing hash). The
    ///         provenance is folded into `provenanceRoot` — a re-checkable chain of
    ///         where the fees came from, the structural answer to CIRC's
    ///         "amount visible, provenance opaque" (§5.2). `sourceReceiptHash == 0`
    ///         is an UNPROVENANCED inflow (counted, but not provenanced) — the mock's
    ///         every inflow is of this kind.
    function accrueFee(bytes32 sourceReceiptHash) external payable {
        if (phase != Phase.Commit || block.timestamp >= commitEnd) revert NotCommitPhase();
        accrued += msg.value;
        unchecked {
            // Each counter increments once per tx — 2^128 is unreachable.
            inflowCount += 1;
            if (sourceReceiptHash != bytes32(0)) provenancedCount += 1;
        }
        provenanceRoot = keccak256(abi.encode(provenanceRoot, sourceReceiptHash, msg.value));
        emit FeeAccrued(msg.sender, msg.value, sourceReceiptHash, provenanceRoot);
    }

    // ─── (2) commit → reveal the sealed asks (the sell-side book) ───────────────

    /// @notice Commit a SEALED ask and escrow the tokens. `sealedHash ==
    ///         H(price‖qty‖salt‖seller)`; nothing about the ask is observable during
    ///         the commit window (no book to front-run), and the tokens are escrowed
    ///         so the clearing can deliver them. Caller must `approve` this contract.
    function commitAsk(bytes32 sealedHash, uint256 tokenEscrow) external {
        if (phase != Phase.Commit || block.timestamp >= commitEnd) revert NotCommitPhase();
        Ask storage a = _asks[msg.sender];
        if (a.committed) revert AlreadyCommitted();
        if (tokenEscrow > type(uint128).max) revert ValueOutOfRange();
        if (!token.transferFrom(msg.sender, address(this), tokenEscrow)) revert TransferFromFailed();
        a.committed = true;
        a.sealedHash = sealedHash;
        a.escrow = uint128(tokenEscrow);
        emit AskCommitted(msg.sender, sealedHash, tokenEscrow);
    }

    /// @notice Reveal a committed ask — only in the reveal window, only opening the
    ///         exact seal (`AskMismatch` otherwise: no late-switch after seeing
    ///         others). Escrow must cover the revealed quantity.
    function revealAsk(uint256 price, uint256 qty, bytes32 salt) external {
        if (block.timestamp < commitEnd || block.timestamp >= revealEnd) revert NotRevealPhase();
        if (phase == Phase.Commit) phase = Phase.Reveal;
        Ask storage a = _asks[msg.sender];
        if (!a.committed) revert NoCommit();
        if (a.revealed) revert AlreadyRevealed();
        if (keccak256(abi.encode(price, qty, salt, msg.sender)) != a.sealedHash) revert AskMismatch();
        // qty is WHOLE tokens; escrow is base units — cover qty·1e18 (mirrors the
        // launchpad's wei-deposit ≥ price·qty check, applied to the token side).
        if (price > type(uint128).max || qty > type(uint96).max) revert ValueOutOfRange();
        if (a.escrow < qty * TOKEN_UNIT) revert UnderEscrowed(a.escrow, qty * TOKEN_UNIT);
        a.revealed = true;
        a.price = uint128(price);
        a.qty = uint96(qty);
        _revealedSellers.push(msg.sender);
        emit AskRevealed(msg.sender, price, qty);
    }

    // ─── (3),(4),(5) FINALIZE — split-check, clear, seed pool, conserve, emit ───

    /// @notice Finalize the recycle. The caller (the operator) supplies:
    ///         - `order`: a claimed ASCENDING-by-price permutation of the revealed
    ///           asks (untrusted search, verified translation-validation style).
    ///         - `claimedBuyHalf`,`claimedPoolHalf`: the split it believes correct —
    ///           a mismatch with the committed `buyBps` reverts `SplitMismatch`.
    ///         - `claimedReceiptHead`,`signature`: the operator's precomputed +
    ///           signed receipt head; the contract recomputes the head from its own
    ///           cleared values and rejects a mismatch or a bad signature.
    function finalizeRecycle(
        uint256[] calldata order,
        uint256 claimedBuyHalf,
        uint256 claimedPoolHalf,
        bytes32 claimedReceiptHead,
        bytes calldata signature
    ) external {
        if (block.timestamp < revealEnd) revert RevealWindowOpen();
        if (phase == Phase.Cleared) revert NotClearPhase();

        // (2) THE COMMITTED SPLIT, ENFORCED — a wrong/hidden split reverts.
        (uint256 correctBuy, uint256 correctPool) = splitOf(accrued);
        if (claimedBuyHalf != correctBuy || claimedPoolHalf != correctPool) {
            revert SplitMismatch(correctBuy, correctPool);
        }

        // (3) THE SEALED-BID UNIFORM-PRICE CLEARING — order-invariant, no swap to
        //     sandwich. (4) SEED the pool. (5a) CONSERVE. (Kept in a helper to stay
        //     under the stack-depth limit.)
        _clearSeedConserve(order, correctBuy, correctPool);

        // (5b) EMIT the prev-hash-chained, operator-signed receipt.
        _emitReceipt(claimedReceiptHead, signature);

        phase = Phase.Cleared;
        emit RecycleCleared(uniformPrice, boughtTokens, uint256(uniformPrice) * boughtTokens, bookCommit);
        emit ReceiptEmitted(receiptHead);
    }

    /// Clear the sealed-ask buy, seed the solvent pool, assert per-asset netFlow=0.
    function _clearSeedConserve(uint256[] calldata order, uint256 correctBuy, uint256 correctPool) private {
        (uint256 uPrice, uint256 bought, uint256 spent, bytes32 bCommit) = _runAskClearing(order, correctBuy);
        if (bought == 0) revert NothingBought();
        // uPrice is an ask price (< 2^128 by the reveal bound); bought is a sum of
        // fills — checked casts, revert on the unreachable overflow.
        if (bought > type(uint128).max) revert ValueOutOfRange();
        uniformPrice = uint128(uPrice);
        boughtTokens = uint128(bought);
        bookCommit = bCommit;

        // (4) SEED THE PROVABLY-SOLVENT POOL with the bought tokens + the pool-half
        //     + any unspent budget (all disclosed, floor-guarded).
        uint256 qSeed = correctPool + (correctBuy - spent); // pool-half + unspent budget
        uint256 tSeed = bought * TOKEN_UNIT; // base units seeded into the pool
        uint256 fQuote = (qSeed * FLOOR_BPS) / 10000;
        uint256 fToken = (tSeed * FLOOR_BPS) / 10000;
        // Clone + fund + seed ATOMICALLY (an un-initialized pool is never
        // observable on-chain); the floor guard is the same rung-6 tooth.
        DreggSolventPool p = DreggSolventPool(LibClone1167.clone(poolImplementation));
        pool = p;
        token.transfer(address(p), tSeed); // tokens taken from filled sellers' escrow
        p.initialize{value: qSeed}(address(token), 0, fQuote, fToken, POOL_FEE_BPS, tSeed);
        emit PoolSeeded(address(p), qSeed, tSeed, fQuote, fToken);

        // (5a) CONSERVATION — per-asset netFlow = 0 (the on-chain twin of
        //      `priced_clearing_keystone`). Quote: accrued = spent(→sellers) +
        //      quoteSeed(→pool). Token: bought·1e18 = tokenSeed(→pool). A bug in the
        //      split/leftover math trips this tooth.
        int256 netQuote = int256(accrued) - int256(spent) - int256(qSeed);
        int256 netToken = int256(bought * TOKEN_UNIT) - int256(tSeed);
        if (netQuote != 0 || netToken != 0) revert ConservationBroken(netQuote, netToken);
    }

    /// The receipt, REBUILT from public state — every field is a pure function of
    /// the stored cleared facts + committed inputs (nothing here is a new claim;
    /// `spentQuote ≡ uniformPrice·boughtTokens` is exact by construction of the
    /// clearing, and the nets are 0 or `finalizeRecycle` reverted). Storing this
    /// struct would be pure redundancy; deriving it keeps the receipt re-checkable
    /// from the SAME public data a non-witness uses.
    function _liveReceipt() internal view returns (Receipt memory r) {
        (uint256 bH, uint256 pH) = splitOf(accrued);
        uint256 uP = uniformPrice;
        uint256 bT = boughtTokens;
        uint256 spent = uP * bT;
        uint256 qS = pH + (bH - spent);
        uint256 tS = bT * TOKEN_UNIT;
        r = Receipt({
            accrued: accrued,
            provenanceRoot: provenanceRoot,
            inflowCount: inflowCount,
            buyHalf: bH,
            poolHalf: pH,
            buyBps: buyBps,
            uniformPrice: uP,
            boughtTokens: bT,
            spentQuote: spent,
            bookCommit: bookCommit,
            quoteSeed: qS,
            tokenSeed: tS,
            floorQuote: (qS * FLOOR_BPS) / 10000,
            floorToken: (tS * FLOOR_BPS) / 10000,
            netQuote: int256(0),
            netToken: int256(0)
        });
    }

    /// Fold the (memory-rebuilt) receipt and require the operator's signed head
    /// matches; persist only the head + signature (r‖s‖v).
    function _emitReceipt(bytes32 claimedReceiptHead, bytes calldata signature) private {
        bytes32 head = _foldReceipt(_liveReceipt());
        if (head != claimedReceiptHead) revert ReceiptHeadMismatch(head);
        if (signature.length != 65) revert BadReceiptSignature();
        bytes32 sigR = bytes32(signature[0:32]);
        bytes32 sigS = bytes32(signature[32:64]);
        uint8 sigV = uint8(signature[64]);
        if (_recover(head, sigV, sigR, sigS) != operator) revert BadReceiptSignature();
        receiptHead = head;
        _sigR = sigR;
        _sigS = sigS;
        _sigV = sigV;
    }

    /// @notice Settle one seller after clearing: a filled seller is paid the UNIFORM
    ///         price for its filled tokens (the filled tokens already seeded the
    ///         pool) and returned any un-filled escrow; an un-filled seller gets its
    ///         whole escrow back. Permissionless.
    function settleAsk(address seller) external {
        if (phase != Phase.Cleared) revert NotClearPhase();
        Ask storage a = _asks[seller];
        if (!a.committed || a.settled) revert NothingToSettle();
        a.settled = true;
        uint256 filled = a.filled;
        uint256 paid = uint256(uniformPrice) * filled; // uniform price, not the seller's ask
        uint256 returned = uint256(a.escrow) - filled * TOKEN_UNIT; // filled tokens went to the pool
        if (paid > 0) _sendEth(seller, paid);
        if (returned > 0) _sendToken(seller, returned);
        emit AskSettled(seller, filled, paid, returned);
    }

    // ─── The clearing (dual of DreggLaunchpad._runClearing) ─────────────────────

    /// Verify `order` is a permutation of the revealed asks sorted ASCENDING by
    /// price, walk it filling tokens at the marginal (uniform) price while the
    /// budget covers the cumulative fill, and set each filled seller's `filled`.
    /// Returns (uniform price, tokens bought, wei spent, a commitment to the whole
    /// revealed book). Reverts on a drop/insert or a non-ascending order.
    ///
    /// Invariant: when ask i takes fill making the cumulative `bought = B` at its
    /// price `p`, `p·B ≤ budget` (fill is capped at `budget/p − bought`). Prices
    /// ascend, so once `bought` reaches `budget/p` no dearer ask can add anything —
    /// the LAST filled ask's price is the single uniform price, and `uniform·bought
    /// ≤ budget`. The result is a function of the book + budget ALONE (order-invariant).
    function _runAskClearing(uint256[] calldata order, uint256 budget)
        private
        returns (uint256 clearingPrice, uint256 bought, uint256 spent, bytes32 bCommit)
    {
        address[] storage revealed = _revealedSellers;
        uint256 n = revealed.length;
        if (order.length != n) revert BadPermutation();
        // The no-drop/no-insert check runs MERGED into the walk (one pass, a bitmap
        // instead of a bool[]) — the checked property is identical: `order` must be
        // a permutation of [0,n).
        uint256[] memory seen = new uint256[]((n >> 8) + 1);

        uint256 prevPrice = 0;
        for (uint256 i = 0; i < n;) {
            _markSeen(seen, order[i], n);

            address seller = revealed[order[i]];
            Ask storage a = _asks[seller];
            uint256 price = a.price;
            uint256 qty = a.qty;
            // Ascending (the canonical uniform-clearing order for a buy-side budget).
            if (price < prevPrice) revert NotSortedAscending();
            prevPrice = price;

            // Same preimage widths as before the packing (uint256-encoded).
            bCommit = keccak256(abi.encodePacked(bCommit, seller, price, qty));

            if (price > 0) {
                uint256 affordable = budget / price; // total tokens if uniform == price
                if (affordable > bought) {
                    unchecked {
                        // affordable > bought ⇒ the subtraction is safe;
                        // fill ≤ qty < 2^96 ⇒ the cast is safe;
                        // bought + fill ≤ affordable ≤ budget ⇒ no overflow.
                        uint256 fill = qty < affordable - bought ? qty : affordable - bought;
                        if (fill > 0) {
                            a.filled = uint96(fill);
                            bought += fill;
                            clearingPrice = price; // marginal = highest filled ask
                        }
                    }
                }
            }
            unchecked {
                ++i;
            }
        }
        spent = clearingPrice * bought; // uniform price × total = wei paid to sellers
    }

    /// @notice A NON-mutating preview of the clearing — the operator runs this to
    ///         learn `(uniformPrice, bought, spent, bookCommit)`, builds the receipt,
    ///         signs it, and submits it to `finalizeRecycle`. Same math as
    ///         `_runAskClearing`, read-only (no fills written). Anyone re-derives the
    ///         clearing from the public revealed book with it.
    function previewClearing(uint256[] calldata order, uint256 budget)
        external
        view
        returns (uint256 clearingPrice, uint256 bought, uint256 spent, bytes32 bCommit)
    {
        address[] storage revealed = _revealedSellers;
        uint256 n = revealed.length;
        if (order.length != n) revert BadPermutation();
        uint256[] memory seen = new uint256[]((n >> 8) + 1);
        uint256 prevPrice = 0;
        for (uint256 i = 0; i < n;) {
            _markSeen(seen, order[i], n);

            address seller = revealed[order[i]];
            Ask storage a = _asks[seller];
            uint256 price = a.price;
            uint256 qty = a.qty;
            if (price < prevPrice) revert NotSortedAscending();
            prevPrice = price;
            bCommit = keccak256(abi.encodePacked(bCommit, seller, price, qty));
            if (price > 0) {
                uint256 affordable = budget / price;
                if (affordable > bought) {
                    unchecked {
                        uint256 fill = qty < affordable - bought ? qty : affordable - bought;
                        if (fill > 0) {
                            bought += fill;
                            clearingPrice = price;
                        }
                    }
                }
            }
            unchecked {
                ++i;
            }
        }
        spent = clearingPrice * bought;
    }

    /// The no-drop/no-insert tooth, one index at a time: `idx` must be in [0,n)
    /// and not yet seen. Same property `_assertPermutation` checked, fused into
    /// the walk (bitmap words instead of a bool[]).
    function _markSeen(uint256[] memory seen, uint256 idx, uint256 n) private pure {
        if (idx >= n) revert BadPermutation();
        uint256 w = seen[idx >> 8];
        uint256 bit = 1 << (idx & 0xff);
        if (w & bit != 0) revert BadPermutation();
        seen[idx >> 8] = w | bit;
    }

    // ─── Split — the committed pure function ────────────────────────────────────

    /// @notice The recycle split — a PURE function of the accrued amount and the
    ///         committed `buyBps`. Anyone re-derives it; the finalizer must pass it
    ///         exactly (`SplitMismatch`).
    function splitOf(uint256 amount) public view returns (uint256 buyLeg, uint256 poolLeg) {
        buyLeg = (amount * buyBps) / 10000;
        poolLeg = amount - buyLeg;
    }

    // ─── Receipt: fold + verify (the re-checkable, verify-only path) ────────────

    /// @notice The receipt chain fold — genesis 0, one keccak per step, prev-hash
    ///         chained. A non-witness reproduces this from public data alone.
    function _foldReceipt(Receipt memory r) internal pure returns (bytes32) {
        bytes32 h = bytes32(0);
        h = keccak256(abi.encode(h, "ACCRUE", r.accrued, r.provenanceRoot, r.inflowCount));
        h = keccak256(abi.encode(h, "SPLIT", r.buyHalf, r.poolHalf, r.buyBps));
        h = keccak256(abi.encode(h, "CLEAR", r.uniformPrice, r.boughtTokens, r.spentQuote, r.bookCommit));
        h = keccak256(abi.encode(h, "POOL", r.quoteSeed, r.tokenSeed, r.floorQuote, r.floorToken));
        h = keccak256(abi.encode(h, "CONSERVE", r.netQuote, r.netToken));
        return h;
    }

    /// @notice Recompute the receipt head from an externally-supplied receipt —
    ///         the pure re-derivation a third party runs on public step data.
    function recomputeReceiptHead(Receipt calldata r) external pure returns (bytes32) {
        return _foldReceipt(r);
    }

    /// @notice VERIFY-ONLY re-check: recompute the head from the stored (public)
    ///         receipt, confirm it equals the emitted head, and confirm the operator
    ///         signed it. A non-witness runs this against public chain data and
    ///         learns the recycle happened exactly as claimed — ex-ante verification,
    ///         not ex-post block-explorer trust. Returns true iff all three hold.
    function verifyReceipt() external view returns (bool) {
        if (phase != Phase.Cleared) return false;
        bytes32 head = _foldReceipt(_liveReceipt());
        if (head != receiptHead) return false;
        return _recover(head, _sigV, _sigR, _sigS) == operator;
    }

    /// @notice The receipt (rebuilt from public state) + head + signature — the
    ///         public re-check bundle. Identical bytes to the pre-optimization
    ///         stored bundle; all-zero before the recycle clears.
    function receiptBundle() external view returns (Receipt memory r, bytes32 head, bytes memory sig) {
        if (phase != Phase.Cleared) {
            return (r, bytes32(0), "");
        }
        return (_liveReceipt(), receiptHead, abi.encodePacked(_sigR, _sigS, _sigV));
    }

    // ─── Views ──────────────────────────────────────────────────────────────────

    // Derived cleared facts — pure functions of the stored primaries + committed
    // inputs, identical to the values previously stored (0 until Cleared, exactly
    // as the storage variables were).

    /// @notice Committed-split buy leg (wei); 0 until the recycle clears.
    function buyHalf() external view returns (uint256) {
        if (phase != Phase.Cleared) return 0;
        (uint256 b,) = splitOf(accrued);
        return b;
    }

    /// @notice Committed-split pool leg (wei); 0 until the recycle clears.
    function poolHalf() external view returns (uint256) {
        if (phase != Phase.Cleared) return 0;
        (, uint256 p) = splitOf(accrued);
        return p;
    }

    /// @notice Wei paid to sellers = uniformPrice × boughtTokens (exact by
    ///         construction of the clearing); 0 until the recycle clears.
    function spentQuote() external view returns (uint256) {
        return uint256(uniformPrice) * boughtTokens;
    }

    /// @notice Wei seeded into the pool = poolHalf + unspent buy budget; 0 until
    ///         the recycle clears.
    function quoteSeed() external view returns (uint256) {
        if (phase != Phase.Cleared) return 0;
        (uint256 b, uint256 p) = splitOf(accrued);
        return p + (b - uint256(uniformPrice) * boughtTokens);
    }

    /// @notice Token base units seeded into the pool; 0 until the recycle clears.
    function tokenSeed() external view returns (uint256) {
        return boughtTokens * TOKEN_UNIT;
    }

    /// @notice Fraction of inflows carrying a verifiable source receipt, in bps.
    ///         (dregg: measurable; the mock's opaque transfers: 0.)
    function provenanceBps() external view returns (uint256) {
        if (inflowCount == 0) return 0;
        return (uint256(provenancedCount) * 10000) / inflowCount;
    }

    function revealedCount() external view returns (uint256) {
        return _revealedSellers.length;
    }

    function getAsk(address seller)
        external
        view
        returns (bool committed, bool revealed, uint256 price, uint256 qty, uint256 filled, bool settled, uint256 escrow)
    {
        Ask storage a = _asks[seller];
        return (a.committed, a.revealed, a.price, a.qty, a.filled, a.settled, a.escrow);
    }

    /// @notice The canonical seal preimage a seller reproduces off-chain.
    function sealOf(uint256 price, uint256 qty, bytes32 salt, address seller) external pure returns (bytes32) {
        return keccak256(abi.encode(price, qty, salt, seller));
    }

    // ─── Internal ─────────────────────────────────────────────────────────────

    /// EIP-191 personal-sign recovery over the 32-byte receipt head.
    function _recover(bytes32 head, uint8 v, bytes32 r, bytes32 s) internal pure returns (address) {
        bytes32 digest = keccak256(abi.encodePacked("\x19Ethereum Signed Message:\n32", head));
        return ecrecover(digest, v, r, s);
    }

    function _sendEth(address to, uint256 amount) private {
        (bool ok,) = payable(to).call{value: amount}("");
        if (!ok) revert TransferFailed();
    }

    function _sendToken(address to, uint256 amount) private {
        if (!token.transfer(to, amount)) revert TransferFailed();
    }
}
