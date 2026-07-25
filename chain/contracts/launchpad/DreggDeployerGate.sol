// SPDX-License-Identifier: MIT
pragma solidity ^0.8.20;

import {IDeployerGate} from "./IDeployerGate.sol";
import {IDreggCredentialGate} from "../IDreggCredentialGate.sol";

/// @title DreggDeployerGate
/// @notice The on-chain deployer-gate: authorizes a launch deployment only if the
///         deployer satisfies a pluggable gate arm. Composes the launchpad's
///         existing anti-scam machinery — the conduct bond, an interview/audit
///         attestor set, and `DreggCredentialGate` (anonymous credentials) for
///         the reveal-nothing private arm.
///
/// The operator enables any subset of arms via `acceptedArms` (a bitmask), so a
/// launchpad can require, e.g., "bond OR passed-interview", "audit only", or
/// "private interview-credential only". A capability is
/// `abi.encode(uint8 arm, bytes armData)`:
///
///   arm 0  BOND               armData: (empty)            — bond >= minBond now.
///   arm 1  INTERVIEW (public)  armData: bytes32 commitment — attester marked it.
///   arm 2  INTERVIEW (private) armData: (bytes32 fedRoot, bytes sp1Proof)
///                                        — DreggCredentialGate proves an
///                                          "interview-passed" credential without
///                                          revealing identity; a nullifier burns
///                                          for sybil-resistance.
///   arm 3  AUDIT               armData: bytes32 reportHash — cleared dregg-audit.
///
/// Fail-closed everywhere: an unknown arm, a disabled arm, an unmet condition, or
/// a malformed capability all return false (the launchpad then reverts).
contract DreggDeployerGate is IDeployerGate {
    // ─── Arm identifiers + accepted-arm bitmask ──────────────────────────────
    uint8 public constant ARM_BOND = 0;
    uint8 public constant ARM_INTERVIEW_PUBLIC = 1;
    uint8 public constant ARM_INTERVIEW_PRIVATE = 2;
    uint8 public constant ARM_AUDIT = 3;

    /// The predicate an anonymous interview credential must prove.
    bytes32 public constant INTERVIEW_PREDICATE = keccak256("interview-passed");

    /// Bitmask of enabled arms: bit `i` set => arm `i` accepted.
    uint8 public acceptedArms;

    // ─── Roles ───────────────────────────────────────────────────────────────
    address public admin;
    /// The interview-verdict oracle (marks passed interviews) — the marquee arm.
    address public attester;
    /// The audit oracle (marks cleared audit reports).
    address public auditor;
    /// The OPERATIONAL fraud-detection / slasher role. It cannot drain a bond in
    /// one call (that was the #11 hole); it TIMELOCKS via `proposeSlash` →
    /// `executeSlash`, vetoable by governance. See the SLASH_DELAY block.
    address public slasher;

    // ─── Bond arm ──────────────────────────────────────────────────────────────
    uint256 public minBond;
    mapping(address => uint256) public bondOf;

    /// Conduct-bond ESCROW window. A bond that BACKS a launch (authorized through
    /// the BOND arm) is locked from withdrawal until this long after that launch
    /// was registered — long enough to cover the launch itself plus a
    /// fraud-challenge period — so a deployer cannot post a bond, register a
    /// launch, and reclaim the bond the next block (a rug with ZERO at stake, the
    /// hole the unconditional `withdrawBond` left open). Slashing stays available
    /// the whole time; only the deployer's OWN `withdrawBond` is gated.
    ///
    /// CONSERVATIVE DEFAULT: 30 days comfortably covers a commit+reveal raise plus
    /// the launchpad's 7-day `REFUND_GRACE` and a challenge margin. A launch whose
    /// disclosed windows exceed this could in principle outlast the timer; a
    /// production deployment that permits very long raises should have the
    /// launchpad signal launch resolution to release the lock precisely.
    uint64 public constant CHALLENGE_WINDOW = 30 days;

    /// The timestamp until which a deployer's bond is escrow-locked (0 = unlocked).
    /// Extended forward each time the deployer backs a fresh launch via the BOND arm.
    mapping(address => uint256) public bondLockedUntil;

    // ─── Slash timelock (#11) ──────────────────────────────────────────────────
    /// The operational `slasher` role can no longer drain a bond in one call
    /// (the #11 hole: `msg.sender == slasher`, any amount, arbitrary recipient, NO
    /// on-chain fraud proof → a compromised slasher key drains every bond). It now
    /// TIMELOCKS: `proposeSlash` stages a slash with `eta = now + SLASH_DELAY`,
    /// `executeSlash` moves the funds only on/after `eta`, and `cancelSlash` lets
    /// governance (`admin`) VETO within the window — so a compromised slasher key
    /// buys nothing but a delay during which governance cancels it and rotates the
    /// key via `setSlasher`. Governance itself retains an immediate `slash` (it is
    /// already the omnipotent root — `setSlasher`/`setAdmin` — so this grants it no
    /// new power; hardening the governance root is the separate admin-timelock item).
    ///
    /// CONSERVATIVE DEFAULT: 2 days mirrors the DreggGroth16VerifierUpgradeable VK
    /// timelock (batch 1) — long enough for governance to notice and veto a rogue
    /// slash, short enough that an honest fraud slash still resolves promptly.
    uint256 public constant SLASH_DELAY = 2 days;

    struct PendingSlash {
        address deployer;
        uint256 amount;
        address recipient;
        uint256 eta;
        bool executed;
        bool cancelled;
    }

    /// Staged slashes by id. `id == 0` is never a real proposal.
    mapping(uint256 => PendingSlash) public pendingSlashes;
    /// Monotone id counter (first real proposal is id 1).
    uint256 public slashCount;

    /// The pinned launchpad. Once set, ONLY it may call `authorizeDeploy` — which
    /// makes the bond escrow non-griefable (an arbitrary caller cannot lock a
    /// bonded deployer's funds by re-authorizing) and, incidentally, closes the
    /// pending-launch nullifier-snipe surface. `address(0)` = unpinned (dev/test).
    address public launchpad;

    // ─── Interview / audit registries ──────────────────────────────────────────
    /// Verdict commitments the attester has marked as passed-and-attested.
    mapping(bytes32 => bool) public interviewPassed;
    /// Audit report hashes the auditor has marked as cleared.
    mapping(bytes32 => bool) public auditCleared;
    /// The launch a cleared audit report is BOUND to (`keccak256(abi.encode(
    /// Schedule))`), set by `attestAuditFor`. `0` = unscoped (the report
    /// authorizes any schedule from a deployer who presents it).
    ///
    /// Scoping is what makes the token-factory compose into CREATE: the factory's
    /// VERIFIED-SAFE artifact proves a property of the TOKEN (a Halmos-proven hard
    /// cap, no rug doors), while the launch's DISCLOSED SCHEDULE (total supply,
    /// creator allocation, vesting cliff) is a separate public input. The auditor —
    /// which read both — attests the PAIR, so an audit cleared for one disclosure
    /// cannot be spent on another (e.g. a 1B-cap artifact reused to launch a
    /// different supply). Without a scope nothing on-chain ties the two.
    mapping(bytes32 => bytes32) public auditScope;

    // ─── Private (ZK) arm ──────────────────────────────────────────────────────
    /// The anonymous-credential verifier for the reveal-nothing interview arm.
    IDreggCredentialGate public credentialGate;
    /// The federation whose members are "interview-passed" credential holders.
    bytes32 public interviewFederationRoot;
    /// Spent presentation nullifiers (one deploy per credential presentation).
    mapping(bytes32 => bool) public usedNullifiers;

    // ─── Events ────────────────────────────────────────────────────────────────
    event DeployAuthorized(address indexed deployer, bytes32 indexed launchParamsHash, uint8 arm);
    event BondPosted(address indexed deployer, uint256 amount, uint256 total);
    event BondSlashed(address indexed deployer, uint256 amount, address indexed recipient);
    event BondWithdrawn(address indexed deployer, uint256 amount);
    /// A slasher-role slash was STAGED behind the timelock (not yet effective).
    event SlashProposed(
        uint256 indexed id, address indexed deployer, uint256 amount, address recipient, uint256 eta
    );
    /// Governance VETOED a staged slash before its `eta`.
    event SlashCancelled(uint256 indexed id);
    /// A bond was escrow-locked (or its lock extended) to back a launch.
    event BondLockExtended(address indexed deployer, uint256 lockedUntil, bytes32 indexed launchParamsHash);
    event LaunchpadSet(address indexed launchpad);
    event InterviewAttested(bytes32 indexed commitment, bool passed);
    event AuditAttested(bytes32 indexed reportHash, bool cleared);
    /// A cleared audit bound to exactly one launch disclosure.
    event AuditScoped(bytes32 indexed reportHash, bytes32 indexed launchParamsHash);
    event AcceptedArmsSet(uint8 mask);

    // ─── Errors ────────────────────────────────────────────────────────────────
    error Unauthorized();
    error InsufficientBond(uint256 have, uint256 need);
    error NothingToWithdraw();
    error TransferFailed();
    error NullifierAlreadyUsed(bytes32 nullifier);
    /// The bond is escrow-locked to back a live launch until `lockedUntil`.
    error BondLocked(uint256 lockedUntil);
    /// A staged slash cannot execute until its timelock `eta` (#11).
    error SlashNotReady(uint256 eta);
    /// A staged slash was already executed or cancelled (#11).
    error SlashAlreadyResolved(uint256 id);
    /// No staged slash with this id (#11).
    error UnknownSlash(uint256 id);

    constructor(address _admin, uint256 _minBond) {
        admin = _admin;
        attester = _admin;
        auditor = _admin;
        slasher = _admin;
        minBond = _minBond;
    }

    modifier onlyAdmin() {
        if (msg.sender != admin) revert Unauthorized();
        _;
    }

    // ─── Operator configuration (pluggable) ──────────────────────────────────
    function setAcceptedArms(uint8 mask) external onlyAdmin {
        acceptedArms = mask;
        emit AcceptedArmsSet(mask);
    }

    function setAttester(address a) external onlyAdmin {
        attester = a;
    }

    function setAuditor(address a) external onlyAdmin {
        auditor = a;
    }

    function setSlasher(address a) external onlyAdmin {
        slasher = a;
    }

    function setMinBond(uint256 v) external onlyAdmin {
        minBond = v;
    }

    function setCredentialGate(IDreggCredentialGate g, bytes32 federationRoot) external onlyAdmin {
        credentialGate = g;
        interviewFederationRoot = federationRoot;
    }

    /// Pin the launchpad that drives `authorizeDeploy`. Once pinned, only it may
    /// call `authorizeDeploy`, so the bond escrow cannot be griefed and the
    /// pending-launch nullifier snipe is closed. Set this on any real deployment.
    function setLaunchpad(address l) external onlyAdmin {
        launchpad = l;
        emit LaunchpadSet(l);
    }

    function armEnabled(uint8 arm) public view returns (bool) {
        return (acceptedArms & uint8(1 << arm)) != 0;
    }

    // ─── (a) Bond arm ─────────────────────────────────────────────────────────
    /// Stake a conduct bond. Slashable by the fraud-proof on a proven rug.
    function postBond() external payable {
        bondOf[msg.sender] += msg.value;
        emit BondPosted(msg.sender, msg.value, bondOf[msg.sender]);
    }

    /// GOVERNANCE-immediate slash (`admin` only). `admin` is the omnipotent root
    /// (it already sets the slasher, min bond, and admin), so an immediate slash
    /// here grants it no power it lacked — it is the emergency/settled-fraud path.
    /// The OPERATIONAL `slasher` role does NOT use this; it timelocks via
    /// `proposeSlash`/`executeSlash` so a compromised slasher key cannot drain
    /// bonds in one shot (#11). Hardening the governance root itself is the
    /// separate admin-timelock item (#14).
    function slash(address deployer, uint256 amount, address recipient) external onlyAdmin {
        _applySlash(deployer, amount, recipient);
    }

    /// Move up to `amount` (capped at the bond balance) of `deployer`'s bond to
    /// `recipient`. Shared by the governance-immediate and timelocked paths.
    function _applySlash(address deployer, uint256 amount, address recipient) internal {
        uint256 bal = bondOf[deployer];
        uint256 take = amount > bal ? bal : amount;
        bondOf[deployer] = bal - take;
        (bool ok,) = recipient.call{value: take}("");
        if (!ok) revert TransferFailed();
        emit BondSlashed(deployer, take, recipient);
    }

    /// The OPERATIONAL slasher STAGES a slash behind the timelock (#11). Returns
    /// the proposal id. It becomes executable at `eta = now + SLASH_DELAY` and
    /// governance can `cancelSlash` it before then.
    function proposeSlash(address deployer, uint256 amount, address recipient)
        external
        returns (uint256 id)
    {
        if (msg.sender != slasher) revert Unauthorized();
        id = ++slashCount;
        pendingSlashes[id] = PendingSlash({
            deployer: deployer,
            amount: amount,
            recipient: recipient,
            eta: block.timestamp + SLASH_DELAY,
            executed: false,
            cancelled: false
        });
        emit SlashProposed(id, deployer, amount, recipient, block.timestamp + SLASH_DELAY);
    }

    /// Execute a staged slash once its timelock has elapsed and it was not vetoed.
    /// Callable by the slasher (the operational role that staged it).
    function executeSlash(uint256 id) external {
        if (msg.sender != slasher) revert Unauthorized();
        PendingSlash storage p = pendingSlashes[id];
        if (p.eta == 0) revert UnknownSlash(id);
        if (p.executed || p.cancelled) revert SlashAlreadyResolved(id);
        if (block.timestamp < p.eta) revert SlashNotReady(p.eta);
        p.executed = true;
        _applySlash(p.deployer, p.amount, p.recipient);
    }

    /// Governance VETO of a staged slash (the compromised-slasher backstop, #11).
    function cancelSlash(uint256 id) external onlyAdmin {
        PendingSlash storage p = pendingSlashes[id];
        if (p.eta == 0) revert UnknownSlash(id);
        if (p.executed || p.cancelled) revert SlashAlreadyResolved(id);
        p.cancelled = true;
        emit SlashCancelled(id);
    }

    /// Withdraw an unslashed bond (a deployer exiting in good standing). Refused
    /// while the bond is escrow-locked backing a live launch (until the launch's
    /// challenge window elapses) — the fix for the rug-with-zero-bond hole: a
    /// deployer can no longer reclaim the bond that gates a launch it just
    /// registered. Slashing remains available against a locked bond.
    function withdrawBond() external {
        uint256 lockedUntil = bondLockedUntil[msg.sender];
        if (block.timestamp < lockedUntil) revert BondLocked(lockedUntil);
        uint256 bal = bondOf[msg.sender];
        if (bal == 0) revert NothingToWithdraw();
        bondOf[msg.sender] = 0;
        (bool ok,) = msg.sender.call{value: bal}("");
        if (!ok) revert TransferFailed();
        emit BondWithdrawn(msg.sender, bal);
    }

    /// Escrow-lock (or extend the lock on) `deployer`'s bond to back a launch for
    /// the challenge window. Never shortens an existing lock.
    function _lockBond(address deployer, bytes32 launchParamsHash) internal {
        uint256 lockedUntil = block.timestamp + CHALLENGE_WINDOW;
        if (lockedUntil > bondLockedUntil[deployer]) {
            bondLockedUntil[deployer] = lockedUntil;
        }
        emit BondLockExtended(deployer, bondLockedUntil[deployer], launchParamsHash);
    }

    // ─── (b) Interview + (c) Audit attestation ────────────────────────────────
    /// The interview-verdict oracle marks a verdict commitment passed-and-attested.
    /// The commitment hides the interview content and the deployer identity — the
    /// gate learns only membership (see the crate's `private` module).
    function attestInterview(bytes32 verdictCommitment, bool passed) external {
        if (msg.sender != attester) revert Unauthorized();
        interviewPassed[verdictCommitment] = passed;
        emit InterviewAttested(verdictCommitment, passed);
    }

    /// The audit oracle marks a report hash as cleared, UNSCOPED — it authorizes
    /// any schedule the presenting deployer registers. Use this only for a
    /// standing deployer-level clearance; the launch-bound form below is what the
    /// token-factory create path uses.
    function attestAudit(bytes32 reportHash, bool cleared) external {
        if (msg.sender != auditor) revert Unauthorized();
        auditCleared[reportHash] = cleared;
        emit AuditAttested(reportHash, cleared);
    }

    /// The audit oracle clears a report AND BINDS it to one launch's disclosed
    /// schedule (`keccak256(abi.encode(Schedule))` — the same hash the launchpad
    /// commits as `scheduleCommit` and scopes the capability to). This is the
    /// token-factory composition: the auditor attests "THIS VERIFIED-SAFE artifact
    /// is the token of THIS disclosure", and the report authorizes nothing else.
    /// Un-clearing (`cleared = false`) also drops the scope.
    function attestAuditFor(bytes32 reportHash, bytes32 launchParamsHash, bool cleared) external {
        if (msg.sender != auditor) revert Unauthorized();
        auditCleared[reportHash] = cleared;
        auditScope[reportHash] = cleared ? launchParamsHash : bytes32(0);
        emit AuditAttested(reportHash, cleared);
        emit AuditScoped(reportHash, cleared ? launchParamsHash : bytes32(0));
    }

    // ─── The authorization gate (the registerLaunch hook) ─────────────────────
    /// @inheritdoc IDeployerGate
    function authorizeDeploy(address deployer, bytes32 launchParamsHash, bytes calldata capability)
        external
        returns (bool)
    {
        // Once a launchpad is pinned, only it may drive authorization. This makes
        // the BOND escrow non-griefable (an arbitrary caller cannot lock a bonded
        // deployer's funds by re-authorizing) and closes the pending-launch
        // nullifier-snipe surface. Unpinned (dev/test) leaves the call open.
        if (launchpad != address(0) && msg.sender != launchpad) revert Unauthorized();

        if (capability.length == 0) return false;
        (uint8 arm, bytes memory armData) = abi.decode(capability, (uint8, bytes));
        if (!armEnabled(arm)) return false;

        if (arm == ARM_BOND) {
            if (bondOf[deployer] < minBond) return false;
            // ESCROW the bond over the launch + challenge window: the deployer
            // cannot withdraw it until the window elapses, so the launch it now
            // backs always has the bond at stake.
            _lockBond(deployer, launchParamsHash);
            emit DeployAuthorized(deployer, launchParamsHash, arm);
            return true;
        }

        if (arm == ARM_INTERVIEW_PUBLIC) {
            bytes32 commitment = abi.decode(armData, (bytes32));
            if (!interviewPassed[commitment]) return false;
            emit DeployAuthorized(deployer, launchParamsHash, arm);
            return true;
        }

        if (arm == ARM_INTERVIEW_PRIVATE) {
            return _authorizePrivateInterview(deployer, launchParamsHash, armData);
        }

        if (arm == ARM_AUDIT) {
            bytes32 reportHash = abi.decode(armData, (bytes32));
            if (!auditCleared[reportHash]) return false;
            // A launch-BOUND report authorizes exactly the disclosure it was
            // cleared for — an audit obtained for one schedule cannot be spent on
            // another. (An unscoped report — `attestAudit` — is deployer-level.)
            bytes32 scope = auditScope[reportHash];
            if (scope != bytes32(0) && scope != launchParamsHash) return false;
            emit DeployAuthorized(deployer, launchParamsHash, arm);
            return true;
        }

        return false; // unknown arm — fail closed.
    }

    /// The reveal-nothing arm: prove an anonymous "interview-passed" credential
    /// via `DreggCredentialGate` (identity hidden), burning a per-deploy nullifier.
    function _authorizePrivateInterview(address deployer, bytes32 launchParamsHash, bytes memory armData)
        private
        returns (bool)
    {
        if (address(credentialGate) == address(0)) return false;
        (bytes32 fedRoot, bytes memory sp1Proof) = abi.decode(armData, (bytes32, bytes));
        if (fedRoot != interviewFederationRoot) return false;

        // Verify the anonymous credential proves the interview-passed predicate.
        if (!credentialGate.verifyCredential(fedRoot, INTERVIEW_PREDICATE, sp1Proof)) {
            return false;
        }

        // Sybil-resistance: burn the presentation nullifier (one deploy per
        // credential presentation). The nullifier is the proof's, unlinkable to
        // the deployer's identity.
        (,,, bytes32 nullifier) = abi.decode(
            _publicValues(sp1Proof), (bool, bytes32, bytes32, bytes32)
        );
        if (usedNullifiers[nullifier]) revert NullifierAlreadyUsed(nullifier);
        usedNullifiers[nullifier] = true;

        emit DeployAuthorized(deployer, launchParamsHash, ARM_INTERVIEW_PRIVATE);
        return true;
    }

    /// Extract the public-values blob from an SP1 proof envelope
    /// (`abi.encode(bytes proofBytes, bytes publicValues)`) — the same layout
    /// `DreggCredentialGate` decodes.
    function _publicValues(bytes memory sp1Proof) private pure returns (bytes memory publicValues) {
        (, publicValues) = abi.decode(sp1Proof, (bytes, bytes));
    }

    // ─── Admin rotation ────────────────────────────────────────────────────────
    function setAdmin(address a) external onlyAdmin {
        admin = a;
    }

    receive() external payable {
        bondOf[msg.sender] += msg.value;
        emit BondPosted(msg.sender, msg.value, bondOf[msg.sender]);
    }
}
