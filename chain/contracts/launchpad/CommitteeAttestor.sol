// SPDX-License-Identifier: MIT
pragma solidity ^0.8.20;

import {IClearingAttestor} from "./IClearingAttestor.sol";

/// @title CommitteeAttestor
/// @notice The v1 `IClearingAttestor` — the PROVED-grade trust anchor the launchpad
///         consumes as a bool. `attestClearing` returns true iff a `threshold`-of-`n`
///         committee has signed the exact clearing tuple
///         `(launchId, saleSupply, clearingPrice, bookCommit)` under this attestor's
///         domain. It checks a COMMITTEE SIGNATURE, never a VK — so it is STABLE
///         across every dregg VK rotation / devnet re-genesis by construction
///         (`PRIVATE-DREGG-PUBLIC-LAUNCHPAD-ARCHITECTURE.md` §3.4, §3.6).
///
/// ## Trust model — HONEST (§3.4, §5)
/// This is TRUST-MINIMIZED, not trustless. What a corrupt QUORUM can and cannot do:
///  - CANNOT over-mint: the token has one hard-capped, one-shot mint door and no
///    other (`DreggLaunchToken.mint`, `AlreadyMinted`/`CapExceeded`/`NotMinter`).
///  - CANNOT drain the graduated pool: every swap reverts below the disclosed floor
///    (`DreggSolventPool.PoolFloorBreached`).
///  - CANNOT charge a bidder above escrow: `settleBid` refunds `deposit - payment`
///    with `deposit >= price*qty >= clearing*filled` (`DreggLaunchpad:405-423`), and
///    a reveal under its own escrow is rejected (`UnderCollateralized`).
///  - CAN, in the SHIELDED grade, misallocate WITHIN those bounds (award the wrong
///    winners / a suboptimal price) — a fairness fault, not a theft. That fault is
///    fraud-PROVABLE: the committee signs `bookCommit`, which binds the exact book,
///    so a clearing inconsistent with that book + the Lean-proved uniform-price
///    mechanism is disprovable on-chain (`challengeAttestation`). A caught committee
///    is SLASHED (`slashed`) — all future `attestClearing` return false, degrading
///    launches to the stall-then-refund backstop (`DreggLaunchpad.reclaimEscrow`),
///    never a theft.
///  - As WIRED to the current (public-grade) `finalizeClearing`, the committee is
///    even weaker: the clearing price is recomputed ON-CHAIN by `_runClearing`, so
///    the committee can only GATE that on-chain result — withholding a signature is
///    a liveness fault (→ refund), not a misallocation. The misallocation surface
///    above is the SHIELDED grade (attestor as sole price source), which is
///    designed-not-built (§5).
///
/// The trustless successor is v2 — a stable-wrap-VK attestor over the epoch registry
/// (`DreggGroth16VerifierUpgradeable` + `IGroth16VerifierRegistry`), NOT this
/// contract — same `IClearingAttestor` seam, hardened trust (§3.5, §3.6). Named, not
/// built here; it additionally needs the clearing-proof pipeline wired (§3.3 weld).
contract CommitteeAttestor is IClearingAttestor {
    /// Domain tag: binds a signature to THIS attestor kind + version, so a signature
    /// cannot be replayed against a different attestor or scheme.
    bytes32 public constant DOMAIN = keccak256("DreggCommitteeAttestor.v1");

    /// The committee members and the quorum size.
    mapping(address => bool) public isSigner;
    address[] public signers;
    uint256 public immutable threshold;

    /// Set true once a committee is proven to have signed a clearing INCONSISTENT
    /// with its own committed book (`challengeAttestation`). A slashed committee can
    /// no longer attest — every `attestClearing` returns false thereafter.
    bool public slashed;

    /// The specific attested digests proven fraudulent (evidence trail).
    mapping(bytes32 => bool) public fraudProven;

    error NoSigners();
    error BadThreshold(uint256 threshold, uint256 n);
    error ZeroSigner();
    error DuplicateSigner(address signer);
    error NotAttested(); // the challenged tuple was never actually attested by a quorum
    error BookCommitMismatch(bytes32 got, bytes32 want); // the supplied book is not the attested book
    error NotFraudulent(); // the attested clearing IS consistent — an honest committee cannot be slashed

    event CommitteeSlashed(bytes32 indexed digest, uint256 indexed launchId, string reason);

    /// A revealed-book entry, in the canonical descending clearing order — the shape
    /// the launchpad folds into `bookCommit` (`DreggLaunchpad._runClearing:373`).
    struct BookEntry {
        address bidder;
        uint256 price;
        uint256 qty;
    }

    /// @param signers_   the committee public keys (EOA addresses).
    /// @param threshold_ the quorum size k (1 <= k <= n). k>=2 makes a single rogue
    ///        signer insufficient to attest.
    constructor(address[] memory signers_, uint256 threshold_) {
        uint256 n = signers_.length;
        if (n == 0) revert NoSigners();
        if (threshold_ == 0 || threshold_ > n) revert BadThreshold(threshold_, n);
        for (uint256 i = 0; i < n; i++) {
            address s = signers_[i];
            if (s == address(0)) revert ZeroSigner();
            if (isSigner[s]) revert DuplicateSigner(s);
            isSigner[s] = true;
            signers.push(s);
        }
        threshold = threshold_;
    }

    function signerCount() external view returns (uint256) {
        return signers.length;
    }

    // ─── The attestor seam (view, per IClearingAttestor) ────────────────────────

    /// @notice The domain-separated digest a committee member signs. Binds chainId +
    ///         this attestor address + the full clearing tuple, so a signature is
    ///         non-replayable across chains, attestors, and tuples.
    function attestationDigest(uint256 launchId, uint256 saleSupply, uint256 clearingPrice, bytes32 bookCommit)
        public
        view
        returns (bytes32)
    {
        return keccak256(abi.encode(DOMAIN, block.chainid, address(this), launchId, saleSupply, clearingPrice, bookCommit));
    }

    /// @notice True iff a `threshold`-of-`n` quorum of the committee signed the exact
    ///         `(launchId, saleSupply, clearingPrice, bookCommit)` tuple. `proof` is
    ///         `abi.encode(bytes[] signatures)`, each a 65-byte `(r,s,v)`, ordered by
    ///         ascending signer address (the dedup discipline). A slashed committee
    ///         attests nothing. Returns false (never reverts) on an insufficient /
    ///         forged / mis-ordered signature set, so the launchpad simply stays in
    ///         its pre-final, refundable state (`ClearingNotAttested`).
    function attestClearing(
        uint256 launchId,
        uint256 saleSupply,
        uint256 clearingPrice,
        bytes32 bookCommit,
        bytes calldata proof
    ) external view returns (bool) {
        if (slashed) return false;
        bytes32 digest = attestationDigest(launchId, saleSupply, clearingPrice, bookCommit);
        return _quorumSigned(digest, proof);
    }

    /// Count distinct committee members whose signatures over `digest` appear in
    /// `proof`, in strictly-ascending signer-address order (so a duplicate signature
    /// from one rogue signer counts at most once), and report whether the quorum is
    /// met. Never reverts — a malformed set simply fails to reach threshold.
    function _quorumSigned(bytes32 digest, bytes calldata proof) private view returns (bool) {
        bytes[] memory sigs;
        // A malformed proof decodes to nothing → not a quorum → false.
        try this.decodeSigs(proof) returns (bytes[] memory decoded) {
            sigs = decoded;
        } catch {
            return false;
        }

        address last = address(0);
        uint256 count = 0;
        for (uint256 i = 0; i < sigs.length; i++) {
            address rec = _recover(digest, sigs[i]);
            if (rec == address(0) || !isSigner[rec]) continue; // forged / non-committee → ignored
            if (rec <= last) continue; // not strictly ascending → dedup / reject a replayed rogue sig
            last = rec;
            count++;
            if (count >= threshold) return true;
        }
        return count >= threshold;
    }

    /// External so `_quorumSigned` can `try/catch` a malformed `abi.decode` without
    /// reverting the whole `attestClearing` (keeping the view honest: forged → false).
    function decodeSigs(bytes calldata proof) external pure returns (bytes[] memory) {
        return abi.decode(proof, (bytes[]));
    }

    /// Recover the signer of a 65-byte `(r,s,v)` ECDSA signature over `digest`.
    /// Returns address(0) on a malformed signature (→ never counts toward a quorum).
    function _recover(bytes32 digest, bytes memory sig) private pure returns (address) {
        if (sig.length != 65) return address(0);
        bytes32 r;
        bytes32 s;
        uint8 v;
        assembly {
            r := mload(add(sig, 0x20))
            s := mload(add(sig, 0x40))
            v := byte(0, mload(add(sig, 0x60)))
        }
        if (v < 27) v += 27;
        if (v != 27 && v != 28) return address(0);
        // Reject the upper-half malleability range (EIP-2).
        if (uint256(s) > 0x7FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF5D576E7357A4501DDFE92F46681B20A0) {
            return address(0);
        }
        return ecrecover(digest, v, r, s);
    }

    // ─── The fraud-proof / challenge hook (§3.4) ────────────────────────────────

    /// @notice CHALLENGE a committee attestation as inconsistent with its own
    ///         committed book. Fully on-chain, stateless, non-repudiable:
    ///
    ///           1. Re-derive the digest and require the committee ACTUALLY signed a
    ///              quorum over `(launchId, saleSupply, clearingPrice, bookCommit)`
    ///              (`proof`) — you cannot challenge what was never attested.
    ///           2. Require the supplied `book` folds (in the given order) to exactly
    ///              `bookCommit` — you cannot frame a committee with a fabricated book.
    ///           3. Run the canonical uniform-price mechanism over that book and
    ///              detect fraud:
    ///                (a) UNCONDITIONAL: the committed order is NOT non-increasing in
    ///                    price — the attested clearing order is non-canonical
    ///                    (`Market/Aggregation.lean` descending discipline). No other
    ///                    input needed; this arm is soundly false-positive-free.
    ///                (b) CONDITIONAL on `reservePrice`: the marginal (lowest-winning)
    ///                    price of the walk to `saleSupply` differs from the signed
    ///                    `clearingPrice` — the attested price is not the fair uniform
    ///                    clearing of the committed book.
    ///
    ///         On proven fraud the committee is SLASHED: `attestClearing` returns
    ///         false forever, so pending/future launches degrade to the timeout-refund
    ///         backstop — a lying committee costs itself the mandate, never the users.
    ///         An HONEST attestation (correct order + correct price) CANNOT be slashed
    ///         (`NotFraudulent`) — no false positives.
    ///
    /// HONEST residual: arm (b) trusts the caller's `reservePrice`. A full integration
    /// reads `reservePrice`/`saleSupply` from the launch's on-chain `scheduleCommit`
    /// so neither can be spoofed to frame an honest committee, and binds this hook
    /// into a `finalize → challenge-window → settle` path so a proven fraud reverts
    /// settlement. That binding + a full succinct fraud-proof verifier is the NAMED
    /// residual (§5); arm (a) is already unconditional here.
    function challengeAttestation(
        uint256 launchId,
        uint256 saleSupply,
        uint256 clearingPrice,
        bytes32 bookCommit,
        uint256 reservePrice,
        bytes calldata proof,
        BookEntry[] calldata book
    ) external {
        // (1) It must have actually been attested by a quorum (the non-repudiable evidence).
        bytes32 digest = attestationDigest(launchId, saleSupply, clearingPrice, bookCommit);
        if (!_quorumSigned(digest, proof)) revert NotAttested();

        // (2) The supplied book must be THE attested book (fold matches bookCommit,
        //     byte-identically to DreggLaunchpad._runClearing:373).
        bytes32 fold;
        for (uint256 i = 0; i < book.length; i++) {
            fold = keccak256(abi.encodePacked(fold, book[i].bidder, book[i].price, book[i].qty));
        }
        if (fold != bookCommit) revert BookCommitMismatch(fold, bookCommit);

        // (3) Run the canonical mechanism over the committed book and detect fraud.
        (bool nonDescending, uint256 marginal) = _replayClearing(book, saleSupply, reservePrice);
        bool priceWrong = marginal != clearingPrice; // arm (b), conditional on reservePrice
        if (!nonDescending && !priceWrong) revert NotFraudulent();

        fraudProven[digest] = true;
        slashed = true;
        emit CommitteeSlashed(digest, launchId, nonDescending ? "non-descending clearing order" : "clearing price mismatch");
    }

    /// The canonical uniform-price walk over the committed book (mirrors
    /// `DreggLaunchpad._runClearing`): returns whether the order is NON-descending
    /// (arm (a)) and the marginal lowest-winning price for `saleSupply`/`reservePrice`.
    function _replayClearing(BookEntry[] calldata book, uint256 saleSupply, uint256 reservePrice)
        private
        pure
        returns (bool nonDescending, uint256 marginal)
    {
        uint256 prevPrice = type(uint256).max;
        uint256 sold = 0;
        for (uint256 i = 0; i < book.length; i++) {
            uint256 p = book[i].price;
            if (p > prevPrice) nonDescending = true; // arm (a): non-canonical order
            prevPrice = p;
            if (sold < saleSupply && p >= reservePrice) {
                uint256 remaining = saleSupply - sold;
                uint256 fill = book[i].qty < remaining ? book[i].qty : remaining;
                if (fill > 0) {
                    sold += fill;
                    marginal = p; // lowest winning price so far
                }
            }
        }
    }
}
