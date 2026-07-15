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
    /// The fraud-proof / slasher authorized to slash bonds on a proven rug.
    address public slasher;

    // ─── Bond arm ──────────────────────────────────────────────────────────────
    uint256 public minBond;
    mapping(address => uint256) public bondOf;

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

    function armEnabled(uint8 arm) public view returns (bool) {
        return (acceptedArms & uint8(1 << arm)) != 0;
    }

    // ─── (a) Bond arm ─────────────────────────────────────────────────────────
    /// Stake a conduct bond. Slashable by the fraud-proof on a proven rug.
    function postBond() external payable {
        bondOf[msg.sender] += msg.value;
        emit BondPosted(msg.sender, msg.value, bondOf[msg.sender]);
    }

    /// Slash a deployer's bond (the fraud-proof / slasher on a proven rug).
    function slash(address deployer, uint256 amount, address recipient) external {
        if (msg.sender != slasher) revert Unauthorized();
        uint256 bal = bondOf[deployer];
        uint256 take = amount > bal ? bal : amount;
        bondOf[deployer] = bal - take;
        (bool ok,) = recipient.call{value: take}("");
        if (!ok) revert TransferFailed();
        emit BondSlashed(deployer, take, recipient);
    }

    /// Withdraw an unslashed bond (a deployer exiting in good standing).
    function withdrawBond() external {
        uint256 bal = bondOf[msg.sender];
        if (bal == 0) revert NothingToWithdraw();
        bondOf[msg.sender] = 0;
        (bool ok,) = msg.sender.call{value: bal}("");
        if (!ok) revert TransferFailed();
        emit BondWithdrawn(msg.sender, bal);
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
        if (capability.length == 0) return false;
        (uint8 arm, bytes memory armData) = abi.decode(capability, (uint8, bytes));
        if (!armEnabled(arm)) return false;

        if (arm == ARM_BOND) {
            if (bondOf[deployer] < minBond) return false;
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
