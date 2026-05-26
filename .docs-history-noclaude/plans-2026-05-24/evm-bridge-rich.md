# Rich EVM Bridge: Solidity Contracts as `dregg` Participants

## Executive Summary

The current EVM bridge (`DreggVault` + `DreggCredentialGate`) treats Ethereum as
a deposit/withdraw endpoint. This design elevates EVM contracts to **first-class
dregg participants**: they can hold sovereign state, route capabilities, register
in the namespace, verify arbitrary Effect VM turns, and emit dregg-bound effects.

The key enabler: SP1 wraps our BabyBear STARK to Groth16/BN254, which EVM can
verify natively. This path is already working for withdrawals. We generalize it
to arbitrary Effect VM proofs, making the EVM verifier as powerful as a dregg node.

---

## Contract Architecture

```
chain/contracts/
  DreggVault.sol              (EXISTS -- deposit/withdraw with SP1 proof)
  DreggCredentialGate.sol     (EXISTS -- gate access with credential proofs)
  IDreggVault.sol             (EXISTS -- vault interface)
  IDreggCredentialGate.sol    (EXISTS -- credential gate interface)
  DreggSovereignCell.sol      (NEW -- EVM-hosted sovereign cell)
  DreggCapRouter.sol          (NEW -- CapTP capability routing on EVM)
  DreggNameRegistry.sol       (NEW -- mirror dregg namespace on EVM)
  DreggDisputeBridge.sol      (NEW -- optimistic bridge with dispute)
  IDreggBridge.sol            (NEW -- unified bridge interface)
```

---

## Current Bridge vs. Rich Bridge

| Dimension | Current | Rich |
|-----------|---------|------|
| EVM role | Escrow endpoint | Full participant |
| State model | Note commitments (vault only) | Arbitrary state commitments per cell |
| Proof scope | "This note is valid" | "This Effect VM turn happened correctly" |
| Capability model | None | Swiss numbers as storage slots, handoff verification |
| Discovery | None | Governed namespace mirrored on-chain |
| Direction | `dregg` -> EVM (withdraw) only | Bidirectional (events -> turns, proofs -> actions) |
| Trust model | SP1 proof per withdrawal | SP1 proof per state transition + optimistic dispute |

---

## 1. DreggSovereignCell: EVM-Hosted Sovereign Cell

### Concept

A sovereign cell on dregg holds committed state and requires proofs for transitions.
A `DreggSovereignCell` on EVM does the same thing -- it stores a `bytes32 stateCommitment`
and only advances state when a valid SP1 proof of Effect VM execution is presented.

From the dregg side, this contract IS a cell. It can be referenced via sturdy refs.
The bridge relay translates dregg turn messages into EVM transactions (and vice versa).

### Design Principles

1. **State commitment**: A single `bytes32` captures the cell's entire state (Poseidon2
   hash of the state tree). The actual state lives off-chain; the contract only validates
   transitions.

2. **Effect VM proof**: Each `transitionState` call includes an SP1 proof attesting that
   the Effect VM correctly executed the turn, producing the new state from the old state.

3. **Effects hash**: The proof also commits to the effects produced by the turn. These
   effects can trigger further on-chain actions (token transfers, contract calls).

4. **Turn sequencing**: A monotonic turn counter prevents replay and ensures ordering.

5. **Owner/guardian**: The cell has a guardian address that can pause/upgrade (governance).

### Solidity Interface

```solidity
// SPDX-License-Identifier: MIT
pragma solidity ^0.8.20;

interface IDreggSovereignCell {
    /// Emitted on successful state transition.
    event StateTransition(
        uint256 indexed turnNumber,
        bytes32 oldCommitment,
        bytes32 newCommitment,
        bytes32 effectsHash
    );

    /// Emitted when the cell processes an effect (e.g., token release, cross-call).
    event EffectExecuted(
        uint256 indexed turnNumber,
        uint8 effectType,
        bytes effectData
    );

    /// Emitted when a sturdy ref is registered for this cell.
    event SturdyRefRegistered(bytes32 indexed swissNumber, address indexed registrant);

    /// Transition the cell's state by providing an SP1 proof of Effect VM execution.
    /// @param newCommitment The new state commitment (output of the proven turn).
    /// @param effectsHash Hash of the effects produced by this turn.
    /// @param effects Encoded effects to execute on-chain after state transition.
    /// @param sp1Proof The SP1-wrapped Groth16 proof of the Effect VM turn.
    function transitionState(
        bytes32 newCommitment,
        bytes32 effectsHash,
        bytes calldata effects,
        bytes calldata sp1Proof
    ) external;

    /// Read the current state commitment.
    function stateCommitment() external view returns (bytes32);

    /// Read the current turn number.
    function turnNumber() external view returns (uint256);

    /// Check if a specific turn has been executed.
    function isTurnExecuted(uint256 turn) external view returns (bool);
}
```

### Implementation Sketch: DreggSovereignCell.sol

```solidity
// SPDX-License-Identifier: MIT
pragma solidity ^0.8.20;

/// @title DreggSovereignCell
/// @notice An EVM contract that acts as a dregg sovereign cell.
///
/// Holds a state commitment and requires SP1 proofs of Effect VM execution to
/// advance state. From dregg's perspective, this IS a cell -- it can be referenced
/// via sturdy refs, it processes turns, and it emits effects.
///
/// The SP1 guest program (effect-vm-turn) verifies:
///   1. The old state commitment matches what this contract holds
///   2. The Effect VM correctly executed the turn (message dispatch, capability checks)
///   3. The new state commitment is the correct result
///   4. The effects hash matches the effects the turn produced
///
/// After proof verification, the contract:
///   1. Updates stateCommitment to newCommitment
///   2. Increments turnNumber
///   3. Executes on-chain effects (token transfers, cross-contract calls)
contract DreggSovereignCell {
    // ─── Immutables ─────────────────────────────────────────────────────
    address public immutable sp1Verifier;
    bytes32 public immutable effectVmVkey;

    // ─── State ──────────────────────────────────────────────────────────
    bytes32 public stateCommitment;
    uint256 public turnNumber;
    address public guardian;

    /// Sturdy ref registry: swiss number -> registered (for CapTP integration).
    mapping(bytes32 => bool) public sturdyRefs;

    /// Turn execution record (for idempotency).
    mapping(uint256 => bool) public executedTurns;

    // ─── Effect Types ───────────────────────────────────────────────────
    uint8 constant EFFECT_TRANSFER_ERC20 = 1;
    uint8 constant EFFECT_TRANSFER_ETH = 2;
    uint8 constant EFFECT_CROSS_CALL = 3;
    uint8 constant EFFECT_EMIT_INTENT = 4;
    uint8 constant EFFECT_REGISTER_SWISS = 5;
    uint8 constant EFFECT_REVOKE_SWISS = 6;

    // ─── Errors ─────────────────────────────────────────────────────────
    error InvalidProof();
    error TurnAlreadyExecuted();
    error EffectsHashMismatch();
    error InvalidEffectType();
    error Unauthorized();
    error EffectExecutionFailed();
    error CommitmentMismatch();

    // ─── Events ─────────────────────────────────────────────────────────
    event StateTransition(
        uint256 indexed turnNumber,
        bytes32 oldCommitment,
        bytes32 newCommitment,
        bytes32 effectsHash
    );
    event EffectExecuted(uint256 indexed turnNumber, uint8 effectType, bytes effectData);
    event SturdyRefRegistered(bytes32 indexed swissNumber, address indexed registrant);
    event SturdyRefRevoked(bytes32 indexed swissNumber);
    event IntentEmitted(uint256 indexed turnNumber, bytes32 intentHash, bytes intentData);

    // ─── Constructor ────────────────────────────────────────────────────
    constructor(
        address _sp1Verifier,
        bytes32 _effectVmVkey,
        bytes32 _initialCommitment,
        address _guardian
    ) {
        sp1Verifier = _sp1Verifier;
        effectVmVkey = _effectVmVkey;
        stateCommitment = _initialCommitment;
        guardian = _guardian;
    }

    // ─── Core State Transition ──────────────────────────────────────────

    /// @notice Execute a turn on this sovereign cell.
    ///
    /// The SP1 proof must attest that the Effect VM correctly transitioned
    /// from `stateCommitment` to `newCommitment` and produced `effectsHash`.
    ///
    /// Public values format from SP1 guest:
    ///   (bool valid, bytes32 oldState, bytes32 newState, bytes32 effectsHash, uint256 turnNum)
    function transitionState(
        bytes32 newCommitment,
        bytes32 effectsHash,
        bytes calldata effects,
        bytes calldata sp1Proof
    ) external {
        uint256 currentTurn = turnNumber;
        if (executedTurns[currentTurn]) revert TurnAlreadyExecuted();

        // Verify the effects hash matches the provided effects.
        if (keccak256(effects) != effectsHash) revert EffectsHashMismatch();

        // Decode and verify the SP1 proof.
        (bytes memory proofBytes, bytes memory publicValues) = abi.decode(
            sp1Proof, (bytes, bytes)
        );

        (bool verifySuccess, ) = sp1Verifier.staticcall(
            abi.encodeWithSignature(
                "verifyProof(bytes32,bytes,bytes)",
                effectVmVkey,
                publicValues,
                proofBytes
            )
        );
        if (!verifySuccess) revert InvalidProof();

        // Decode public values and validate against expected state.
        (
            bool valid,
            bytes32 proofOldState,
            bytes32 proofNewState,
            bytes32 proofEffectsHash,
            uint256 proofTurnNum
        ) = abi.decode(publicValues, (bool, bytes32, bytes32, bytes32, uint256));

        if (!valid) revert InvalidProof();
        if (proofOldState != stateCommitment) revert CommitmentMismatch();
        if (proofNewState != newCommitment) revert CommitmentMismatch();
        if (proofEffectsHash != effectsHash) revert EffectsHashMismatch();
        if (proofTurnNum != currentTurn) revert TurnAlreadyExecuted();

        // State transition is valid. Update state.
        bytes32 oldCommitment = stateCommitment;
        stateCommitment = newCommitment;
        executedTurns[currentTurn] = true;
        turnNumber = currentTurn + 1;

        emit StateTransition(currentTurn, oldCommitment, newCommitment, effectsHash);

        // Execute on-chain effects.
        _executeEffects(currentTurn, effects);
    }

    // ─── Effect Execution ───────────────────────────────────────────────

    /// Process effects produced by the turn. Each effect is:
    ///   [1 byte type][variable-length data]
    function _executeEffects(uint256 turn, bytes calldata effects) internal {
        uint256 offset = 0;
        while (offset < effects.length) {
            uint8 effectType = uint8(effects[offset]);
            offset += 1;

            if (effectType == EFFECT_TRANSFER_ERC20) {
                // [20 bytes token][20 bytes recipient][32 bytes amount]
                address token = address(bytes20(effects[offset:offset+20]));
                offset += 20;
                address recipient = address(bytes20(effects[offset:offset+20]));
                offset += 20;
                uint256 amount = uint256(bytes32(effects[offset:offset+32]));
                offset += 32;

                (bool success, bytes memory data) = token.call(
                    abi.encodeWithSignature("transfer(address,uint256)", recipient, amount)
                );
                if (!success || (data.length > 0 && !abi.decode(data, (bool)))) {
                    revert EffectExecutionFailed();
                }
                emit EffectExecuted(turn, effectType, effects[offset-72:offset]);

            } else if (effectType == EFFECT_TRANSFER_ETH) {
                // [20 bytes recipient][32 bytes amount]
                address recipient = address(bytes20(effects[offset:offset+20]));
                offset += 20;
                uint256 amount = uint256(bytes32(effects[offset:offset+32]));
                offset += 32;

                (bool success, ) = recipient.call{value: amount}("");
                if (!success) revert EffectExecutionFailed();
                emit EffectExecuted(turn, effectType, effects[offset-52:offset]);

            } else if (effectType == EFFECT_CROSS_CALL) {
                // [20 bytes target][32 bytes value][2 bytes data_len][N bytes calldata]
                address target = address(bytes20(effects[offset:offset+20]));
                offset += 20;
                uint256 value = uint256(bytes32(effects[offset:offset+32]));
                offset += 32;
                uint16 dataLen = uint16(bytes2(effects[offset:offset+2]));
                offset += 2;
                bytes calldata callData = effects[offset:offset+dataLen];
                offset += dataLen;

                (bool success, ) = target.call{value: value}(callData);
                if (!success) revert EffectExecutionFailed();
                emit EffectExecuted(turn, effectType, effects[offset-54-dataLen:offset]);

            } else if (effectType == EFFECT_EMIT_INTENT) {
                // [32 bytes intentHash][2 bytes data_len][N bytes intentData]
                bytes32 intentHash = bytes32(effects[offset:offset+32]);
                offset += 32;
                uint16 dataLen = uint16(bytes2(effects[offset:offset+2]));
                offset += 2;
                bytes calldata intentData = effects[offset:offset+dataLen];
                offset += dataLen;

                emit IntentEmitted(turn, intentHash, intentData);

            } else if (effectType == EFFECT_REGISTER_SWISS) {
                // [32 bytes swissNumber]
                bytes32 swiss = bytes32(effects[offset:offset+32]);
                offset += 32;
                sturdyRefs[swiss] = true;
                emit SturdyRefRegistered(swiss, msg.sender);

            } else if (effectType == EFFECT_REVOKE_SWISS) {
                // [32 bytes swissNumber]
                bytes32 swiss = bytes32(effects[offset:offset+32]);
                offset += 32;
                sturdyRefs[swiss] = false;
                emit SturdyRefRevoked(swiss);

            } else {
                revert InvalidEffectType();
            }
        }
    }

    // ─── View ───────────────────────────────────────────────────────────

    function isTurnExecuted(uint256 turn) external view returns (bool) {
        return executedTurns[turn];
    }

    // ─── Guardian ───────────────────────────────────────────────────────

    function setGuardian(address newGuardian) external {
        if (msg.sender != guardian) revert Unauthorized();
        guardian = newGuardian;
    }

    /// Emergency pause: guardian can freeze the cell.
    /// (In production, this would use OpenZeppelin Pausable.)
    bool public paused;
    function setPaused(bool _paused) external {
        if (msg.sender != guardian) revert Unauthorized();
        paused = _paused;
    }

    receive() external payable {}
}
```

### How This Maps to `dregg` Concepts

| `dregg` Concept | EVM Representation |
|---------------|-------------------|
| Cell state | `bytes32 stateCommitment` |
| Turn execution | `transitionState()` with SP1 proof |
| Effect emission | Decoded from `effects` bytes, executed on-chain |
| Sturdy ref | `sturdyRefs[swiss]` mapping |
| Turn ordering | `turnNumber` monotonic counter |
| Cell identity | Contract address (immutable, CREATE2-derivable) |

---

## 2. DreggCapRouter: CapTP on EVM

### Concept

Capabilities in dregg are opaque 32-byte swiss numbers. CapTP uses handoff certificates
to transfer capabilities between parties. On EVM, we can:

1. Store swiss numbers as capability tokens (mapping from address to swiss[])
2. Verify handoff certificates via SP1 (the introducer's signature is proven in STARK)
3. Route messages to target cells by swiss number lookup
4. Manage capability lifecycle (grant, revoke, delegate)

The key insight: from EVM's perspective, a swiss number IS the capability. Possession
of the swiss number (stored in a contract's storage) IS authority. The SP1 proof
of a valid handoff certificate is how you GET that swiss number on-chain.

### Solidity Implementation: DreggCapRouter.sol

```solidity
// SPDX-License-Identifier: MIT
pragma solidity ^0.8.20;

/// @title DreggCapRouter
/// @notice Routes capabilities between EVM contracts and dregg cells.
///
/// Implements CapTP semantics on EVM:
///   - Swiss numbers as capability tokens (32-byte storage slots)
///   - Handoff certificate verification via SP1 proofs
///   - Message routing by capability (swiss -> target contract)
///   - Capability delegation (export swiss to another address/contract)
///
/// The router is the EVM-side CapTP node. It:
///   1. Accepts handoff certificates (proven valid via SP1)
///   2. Stores capabilities for EVM addresses
///   3. Routes invocations from EVM to dregg (via events)
///   4. Routes invocations from dregg to EVM (via proven effects)
contract DreggCapRouter {
    // ─── Immutables ─────────────────────────────────────────────────────
    address public immutable sp1Verifier;
    bytes32 public immutable handoffVkey; // SP1 program that verifies handoff certs

    // ─── State ──────────────────────────────────────────────────────────

    /// Capabilities held by an address: address -> swiss[] (active capabilities).
    mapping(address => bytes32[]) private heldCapabilities;

    /// Reverse lookup: swiss -> holder address (for routing).
    mapping(bytes32 => address) public capabilityHolder;

    /// Swiss -> target info (where does this capability route to?).
    mapping(bytes32 => CapTarget) public capabilityTargets;

    /// Used handoff nonces (replay prevention).
    mapping(bytes32 => bool) public usedHandoffNonces;

    /// Registered DreggSovereignCell contracts (for routing).
    mapping(address => bool) public registeredCells;

    // ─── Types ──────────────────────────────────────────────────────────

    struct CapTarget {
        /// The target type: 0 = dregg cell (off-chain), 1 = EVM contract.
        uint8 targetType;
        /// For EVM targets: the contract address. For dregg: bytes32 cell ID.
        address evmTarget;
        bytes32 dreggCellId;
        /// Permission level granted by this capability.
        uint8 permissionLevel;
        /// Effect mask (which effects can be triggered).
        uint64 allowedEffects;
    }

    // ─── Events ─────────────────────────────────────────────────────────

    /// A handoff was accepted -- a new capability was granted on EVM.
    event HandoffAccepted(
        bytes32 indexed swiss,
        address indexed recipient,
        bytes32 introducerFederation
    );

    /// A capability was invoked (EVM -> dregg direction).
    /// The relay observes this and submits the invocation as a turn on dregg.
    event CapabilityInvoked(
        bytes32 indexed swiss,
        address indexed invoker,
        bytes32 messageHash,
        bytes message
    );

    /// A capability was delegated from one EVM address to another.
    event CapabilityDelegated(
        bytes32 indexed swiss,
        address indexed from,
        address indexed to
    );

    /// A capability was revoked (dropped).
    event CapabilityRevoked(bytes32 indexed swiss, address indexed holder);

    // ─── Errors ─────────────────────────────────────────────────────────
    error InvalidHandoffProof();
    error HandoffNonceReused();
    error CapabilityNotHeld();
    error NotCapabilityHolder();
    error CellNotRegistered();
    error Unauthorized();

    // ─── Constructor ────────────────────────────────────────────────────
    constructor(address _sp1Verifier, bytes32 _handoffVkey) {
        sp1Verifier = _sp1Verifier;
        handoffVkey = _handoffVkey;
    }

    // ─── Handoff Acceptance ─────────────────────────────────────────────

    /// @notice Accept a handoff certificate, granting a capability to msg.sender.
    ///
    /// The SP1 proof verifies:
    ///   1. The introducer's Ed25519 signature on the certificate is valid
    ///   2. The recipient public key matches (binds to msg.sender via ecrecover or mapping)
    ///   3. The certificate is not expired
    ///   4. The swiss number is well-formed
    ///
    /// Public values from SP1 guest:
    ///   (bool valid, bytes32 swiss, bytes32 recipientPkHash, bytes32 nonce,
    ///    bytes32 introducerFed, uint8 permLevel, uint64 effectMask,
    ///    bytes32 targetCellId, uint8 targetType)
    ///
    /// @param sp1Proof The SP1-wrapped Groth16 proof of handoff certificate validity.
    /// @param evmTarget If the target is an EVM contract, its address. Otherwise address(0).
    function acceptHandoff(
        bytes calldata sp1Proof,
        address evmTarget
    ) external {
        (bytes memory proofBytes, bytes memory publicValues) = abi.decode(
            sp1Proof, (bytes, bytes)
        );

        // Verify via SP1 gateway.
        (bool verifySuccess, ) = sp1Verifier.staticcall(
            abi.encodeWithSignature(
                "verifyProof(bytes32,bytes,bytes)",
                handoffVkey,
                publicValues,
                proofBytes
            )
        );
        if (!verifySuccess) revert InvalidHandoffProof();

        // Decode public values.
        (
            bool valid,
            bytes32 swiss,
            bytes32 recipientPkHash,
            bytes32 nonce,
            bytes32 introducerFed,
            uint8 permLevel,
            uint64 effectMask,
            bytes32 targetCellId,
            uint8 targetType
        ) = abi.decode(publicValues, (bool, bytes32, bytes32, bytes32, bytes32, uint8, uint64, bytes32, uint8));

        if (!valid) revert InvalidHandoffProof();

        // Replay prevention.
        if (usedHandoffNonces[nonce]) revert HandoffNonceReused();
        usedHandoffNonces[nonce] = true;

        // Bind to msg.sender (the recipient proves they own the pk via the SP1 proof).
        // The SP1 guest checks that recipientPkHash matches a known binding to msg.sender.
        // (Alternative: require ecrecover proof in the SP1 guest.)

        // Store the capability.
        heldCapabilities[msg.sender].push(swiss);
        capabilityHolder[swiss] = msg.sender;
        capabilityTargets[swiss] = CapTarget({
            targetType: targetType,
            evmTarget: evmTarget,
            dreggCellId: targetCellId,
            permissionLevel: permLevel,
            allowedEffects: effectMask
        });

        emit HandoffAccepted(swiss, msg.sender, introducerFed);
    }

    // ─── Capability Invocation ──────────────────────────────────────────

    /// @notice Invoke a capability (send a message to the target cell/contract).
    ///
    /// If the target is an EVM contract (targetType == 1):
    ///   Routes the message directly to the target contract.
    ///
    /// If the target is a dregg cell (targetType == 0):
    ///   Emits a CapabilityInvoked event. The relay observes this and submits
    ///   the message as a turn on the dregg side.
    ///
    /// @param swiss The capability being exercised.
    /// @param message The message to deliver to the target.
    function invoke(bytes32 swiss, bytes calldata message) external {
        if (capabilityHolder[swiss] != msg.sender) revert NotCapabilityHolder();

        CapTarget memory target = capabilityTargets[swiss];

        if (target.targetType == 1 && target.evmTarget != address(0)) {
            // Direct EVM routing: call the target contract.
            // The target contract should check that msg.sender == address(this)
            // and that the swiss number is valid for the operation.
            (bool success, ) = target.evmTarget.call(
                abi.encodeWithSignature(
                    "handleCapMessage(bytes32,address,bytes)",
                    swiss,
                    msg.sender,
                    message
                )
            );
            if (!success) revert EffectExecutionFailed();
        } else {
            // Dregg routing: emit event for relay to observe.
            bytes32 messageHash = keccak256(message);
            emit CapabilityInvoked(swiss, msg.sender, messageHash, message);
        }
    }

    // ─── Capability Delegation ──────────────────────────────────────────

    /// @notice Delegate a capability to another EVM address.
    /// This is the EVM equivalent of ExportSturdyRef in CapTP.
    function delegate(bytes32 swiss, address to) external {
        if (capabilityHolder[swiss] != msg.sender) revert NotCapabilityHolder();

        // Transfer ownership.
        capabilityHolder[swiss] = to;
        heldCapabilities[to].push(swiss);
        _removeFromHeld(msg.sender, swiss);

        emit CapabilityDelegated(swiss, msg.sender, to);
    }

    /// @notice Revoke/drop a capability.
    function revoke(bytes32 swiss) external {
        if (capabilityHolder[swiss] != msg.sender) revert NotCapabilityHolder();

        capabilityHolder[swiss] = address(0);
        _removeFromHeld(msg.sender, swiss);
        delete capabilityTargets[swiss];

        emit CapabilityRevoked(swiss, msg.sender);
    }

    // ─── Cell Registration ──────────────────────────────────────────────

    /// Register an EVM DreggSovereignCell as a routable target.
    function registerCell(address cell) external {
        // In production: governance-gated.
        registeredCells[cell] = true;
    }

    // ─── View ───────────────────────────────────────────────────────────

    function getCapabilities(address holder) external view returns (bytes32[] memory) {
        return heldCapabilities[holder];
    }

    function hasCapability(address holder, bytes32 swiss) external view returns (bool) {
        return capabilityHolder[swiss] == holder;
    }

    // ─── Internal ───────────────────────────────────────────────────────

    error EffectExecutionFailed();

    function _removeFromHeld(address holder, bytes32 swiss) internal {
        bytes32[] storage caps = heldCapabilities[holder];
        for (uint256 i = 0; i < caps.length; i++) {
            if (caps[i] == swiss) {
                caps[i] = caps[caps.length - 1];
                caps.pop();
                return;
            }
        }
    }
}
```

---

## 3. DreggNameRegistry: Namespace on EVM

### Concept

`dregg`'s governed namespace (`/bridges/evm/uniswap-pool`) can be mirrored on EVM so that:
- EVM contracts can discover dregg services
- `dregg` can discover EVM contracts registered via the bridge
- Cross-chain resolution: a dregg path resolves to an EVM address

### Design

```solidity
// SPDX-License-Identifier: MIT
pragma solidity ^0.8.20;

/// @title DreggNameRegistry
/// @notice Mirrors the dregg governed namespace on EVM.
///
/// Registration is governance-gated (only approved operators can register names).
/// Resolution is permissionless (anyone can look up a name).
///
/// Names are paths like "/bridges/evm/uniswap-pool" mapped to:
///   - An EVM contract address (for EVM-native targets)
///   - A bytes32 cell ID (for dregg-native targets)
///   - A swiss number (for capability-gated targets)
///
/// The registry is updated via SP1 proofs of dregg governance decisions.
/// When dregg governance mounts a new service at a path, a relay submits
/// the proof to this contract, which updates the on-chain registry.
contract DreggNameRegistry {
    address public immutable sp1Verifier;
    bytes32 public immutable governanceVkey; // SP1 program proving governance decisions

    struct NameEntry {
        address evmAddress;      // EVM contract address (if EVM target)
        bytes32 dreggCellId;     // Dregg cell ID (if dregg target)
        bytes32 swissNumber;     // Swiss number for capability-gated access
        uint8 entryType;         // 0=dregg, 1=evm, 2=hybrid
        string serviceKind;      // "bridge", "oracle", "defi", etc.
        uint256 registeredAt;    // Block number of registration
        bool active;             // Whether the entry is currently live
    }

    /// Path hash -> NameEntry.
    mapping(bytes32 => NameEntry) public entries;

    /// Governance operator addresses.
    mapping(address => bool) public operators;

    /// Event: a name was registered or updated.
    event NameRegistered(
        bytes32 indexed pathHash,
        string path,
        address evmAddress,
        bytes32 dreggCellId,
        string serviceKind
    );

    event NameDeregistered(bytes32 indexed pathHash, string path);

    error Unauthorized();
    error InvalidGovernanceProof();
    error NameNotFound();

    constructor(address _sp1Verifier, bytes32 _governanceVkey, address initialOperator) {
        sp1Verifier = _sp1Verifier;
        governanceVkey = _governanceVkey;
        operators[initialOperator] = true;
    }

    /// Register a name via governance proof.
    /// The SP1 proof attests that dregg governance approved this registration.
    function registerWithProof(
        string calldata path,
        address evmAddress,
        bytes32 dreggCellId,
        bytes32 swissNumber,
        uint8 entryType,
        string calldata serviceKind,
        bytes calldata sp1Proof
    ) external {
        // Verify governance decision proof.
        (bytes memory proofBytes, bytes memory publicValues) = abi.decode(
            sp1Proof, (bytes, bytes)
        );

        (bool verifySuccess, ) = sp1Verifier.staticcall(
            abi.encodeWithSignature(
                "verifyProof(bytes32,bytes,bytes)",
                governanceVkey,
                publicValues,
                proofBytes
            )
        );
        if (!verifySuccess) revert InvalidGovernanceProof();

        bytes32 pathHash = keccak256(bytes(path));
        entries[pathHash] = NameEntry({
            evmAddress: evmAddress,
            dreggCellId: dreggCellId,
            swissNumber: swissNumber,
            entryType: entryType,
            serviceKind: serviceKind,
            registeredAt: block.number,
            active: true
        });

        emit NameRegistered(pathHash, path, evmAddress, dreggCellId, serviceKind);
    }

    /// Resolve a name (permissionless).
    function resolve(string calldata path) external view returns (NameEntry memory) {
        bytes32 pathHash = keccak256(bytes(path));
        NameEntry memory entry = entries[pathHash];
        if (!entry.active) revert NameNotFound();
        return entry;
    }

    /// Resolve by hash (cheaper, for contracts that precompute the hash).
    function resolveByHash(bytes32 pathHash) external view returns (NameEntry memory) {
        NameEntry memory entry = entries[pathHash];
        if (!entry.active) revert NameNotFound();
        return entry;
    }
}
```

---

## 4. DreggDisputeBridge: Optimistic Bridge with Dispute

### Concept

Same model as the Midnight bridge (see `plans/midnight-bridge-production.md`) but for EVM:
- Relay posts dregg state claims to EVM with a bond
- Challenge window allows anyone to dispute with an SP1 fraud proof
- If unchallenged: claim finalizes and EVM actions execute
- If challenged and fraud proven: relay is slashed

### Interface

```solidity
// SPDX-License-Identifier: MIT
pragma solidity ^0.8.20;

interface IDreggDisputeBridge {
    enum ClaimStatus { Pending, Challenged, Finalized, Slashed }

    struct BridgeClaim {
        bytes32 dreggStateRoot;    // The dregg state this claim is about
        bytes32 actionHash;        // What EVM action should execute on finality
        address relay;             // Who submitted the claim
        uint256 bond;              // ETH bonded by the relay
        uint256 submittedAt;       // Block number of submission
        uint256 disputeDeadline;   // Block number when dispute window closes
        ClaimStatus status;
    }

    event ClaimSubmitted(bytes32 indexed claimId, address indexed relay, bytes32 dreggStateRoot);
    event ClaimChallenged(bytes32 indexed claimId, address indexed challenger);
    event ClaimFinalized(bytes32 indexed claimId);
    event ClaimSlashed(bytes32 indexed claimId, address indexed challenger, uint256 slashAmount);

    /// Submit a bridge claim with a bond.
    function submitClaim(
        bytes32 dreggStateRoot,
        bytes32 actionHash,
        bytes calldata federationAttestation
    ) external payable;

    /// Challenge a claim by providing an SP1 fraud proof.
    function challengeClaim(
        bytes32 claimId,
        bytes calldata sp1FraudProof
    ) external payable;

    /// Finalize a claim after the dispute window passes.
    function finalizeClaim(bytes32 claimId) external;

    /// Execute the action associated with a finalized claim.
    function executeAction(bytes32 claimId, bytes calldata actionData) external;
}
```

---

## 5. IDreggBridge: Unified Bridge Interface

```solidity
// SPDX-License-Identifier: MIT
pragma solidity ^0.8.20;

/// @title IDreggBridge
/// @notice Unified interface for all dregg bridge operations on EVM.
///
/// Aggregates: sovereign cells, capability routing, namespace, and disputes.
interface IDreggBridge {
    /// Submit a proven state transition to a sovereign cell.
    function submitTransition(
        address cell,
        bytes32 newCommitment,
        bytes32 effectsHash,
        bytes calldata effects,
        bytes calldata sp1Proof
    ) external;

    /// Accept a handoff certificate (grant capability on EVM).
    function acceptHandoff(bytes calldata sp1Proof, address evmTarget) external;

    /// Invoke a capability (route message to target).
    function invokeCapability(bytes32 swiss, bytes calldata message) external;

    /// Resolve a name from the dregg namespace.
    function resolveName(string calldata path) external view returns (address evmAddress, bytes32 cellId);

    /// Submit a bridge claim (optimistic).
    function submitClaim(bytes32 stateRoot, bytes32 actionHash) external payable;

    /// Check claim status.
    function claimStatus(bytes32 claimId) external view returns (uint8);
}
```

---

## 6. SP1 Proof Integration Points

### Which SP1 Guest Programs Are Needed

| Guest Program | What It Proves | EVM Consumer |
|---------------|---------------|--------------|
| `effect-vm-turn` | Effect VM correctly executed a turn | DreggSovereignCell |
| `handoff-verify` | Handoff certificate has valid Ed25519 signature | DreggCapRouter |
| `governance-decision` | `dregg` governance approved a namespace registration | DreggNameRegistry |
| `withdrawal` | Note is valid and unspent (existing) | DreggVault |
| `credential` | Anonymous credential is valid (existing) | DreggCredentialGate |
| `fraud-proof` | A relay's claim is inconsistent with dregg state | DreggDisputeBridge |
| `datalog-eval` | A Datalog query is derivable from committed state | Any contract (generic) |

### SP1 Program Public Values Format

All SP1 programs commit their results as ABI-encoded `publicValues`. The EVM verifier
checks `verifyProof(vkey, publicValues, proofBytes)` and then decodes `publicValues`
to extract the proven statement.

```
effect-vm-turn:
  (bool valid, bytes32 oldState, bytes32 newState, bytes32 effectsHash, uint256 turnNum)

handoff-verify:
  (bool valid, bytes32 swiss, bytes32 recipientPkHash, bytes32 nonce,
   bytes32 introducerFed, uint8 permLevel, uint64 effectMask,
   bytes32 targetCellId, uint8 targetType)

governance-decision:
  (bool valid, bytes32 pathHash, bytes32 decisionHash, uint256 epoch)

fraud-proof:
  (bool fraudulent, bytes32 claimedStateRoot, bytes32 actualStateRoot, bytes32 claimId)
```

### SP1 Pipeline: BabyBear STARK -> Groth16/BN254 -> EVM

```
1. Dregg computes a turn (Effect VM execution)
2. SP1 guest re-executes the turn inside RISC-V zkVM
3. SP1 produces a STARK proof of correct execution
4. SP1 compresses the STARK via recursion
5. SP1 wraps to Groth16 over BN254 (~1-2 KB proof)
6. Groth16 proof submitted to EVM
7. SP1 Verifier Gateway (deterministic CREATE2 address) verifies
8. EVM contract reads public values and acts accordingly
```

---

## 7. Message Flows

### Flow A: `dregg` -> EVM (Proven State Transition)

```
1. Dregg cell executes a turn that affects EVM state
2. Effect VM produces: (newState, effects[])
3. SP1 proves the turn: STARK -> Groth16
4. Relay submits to DreggSovereignCell.transitionState():
   - newCommitment (new state hash)
   - effectsHash (keccak256 of effects)
   - effects (encoded on-chain actions)
   - sp1Proof (Groth16 proof bytes + public values)
5. Contract verifies proof, updates state, executes effects
6. Effects may include: token transfers, cross-contract calls, swiss registration
```

### Flow B: EVM -> `dregg` (Event Observation)

```
1. EVM contract emits an event (e.g., CapabilityInvoked, IntentEmitted)
2. Relay/watcher observes the event via Ethereum RPC
3. Relay submits the event as a turn on dregg:
   - Include Ethereum storage proof (state proof against block hash)
   - Dregg verifies the proof (trustless if block hash is trusted)
   - Turn executes on dregg side
4. Result flows back via Flow A if needed
```

### Flow C: Handoff Certificate Crossing the Bridge

```
1. Dregg introducer creates HandoffCertificate (Ed25519 signed)
2. SP1 proves the signature is valid (Ed25519 in RISC-V)
3. Groth16 proof submitted to DreggCapRouter.acceptHandoff()
4. Contract verifies proof, stores capability for msg.sender
5. msg.sender can now invoke() the capability:
   - If target is EVM: direct contract call
   - If target is dregg: event emitted, relay delivers to dregg
```

### Flow D: Namespace Resolution

```
1. Dregg governance approves: mount "/bridges/evm/uniswap-pool" -> 0x1234...
2. SP1 proves the governance decision
3. Relay submits to DreggNameRegistry.registerWithProof()
4. Any EVM contract can resolve("/bridges/evm/uniswap-pool") -> 0x1234...
5. Cross-chain composability: Uniswap pool accessible via dregg namespace
```

### Flow E: Optimistic Claim with Dispute

```
1. Relay posts claim: "dregg state S implies EVM action A"
   - Includes: federation attestation, bond (ETH)
   - DreggDisputeBridge records claim, starts dispute window
2. Dispute window (configurable: 7 days for L1, 1 hour for L2):
   - Any watcher can challenge by submitting SP1 fraud proof
   - Fraud proof: "state S does NOT imply action A" (STARK proven)
3a. If unchallenged: finalize after window, execute action
3b. If challenged + fraud proven: relay slashed, challenger rewarded
3c. If challenged + fraud NOT proven: challenger slashed (anti-grief)
```

---

## 8. Example: DeFi Protocol Using `dregg` Capabilities

### Scenario: Uniswap Pool with Anonymous Credential Gating

A Uniswap V4 hook contract gates LP access behind dregg anonymous credentials:
"Only users with a valid KYC credential from a trusted federation can add liquidity."

```solidity
contract DreggGatedUniswapHook {
    DreggCapRouter public immutable capRouter;
    DreggCredentialGate public immutable credentialGate;
    bytes32 public immutable requiredFederation;
    bytes32 public immutable kycPredicate; // keccak256("kyc_status == approved")

    /// Before adding liquidity, verify the user has a dregg capability
    /// AND a valid KYC credential.
    function beforeAddLiquidity(address sender, ...) external {
        // Check 1: sender holds a capability for this pool (via CapRouter)
        bytes32 poolSwiss = getPoolCapability();
        require(
            capRouter.hasCapability(sender, poolSwiss),
            "No pool capability"
        );

        // Check 2: sender has proven KYC credential (via CredentialGate)
        // (The credential proof was submitted in a prior transaction)
        require(
            credentialGate.isNullifierUsed(
                computePoolNullifier(sender, poolSwiss)
            ),
            "KYC credential not presented"
        );
    }
}
```

### How the user gets access:

```
1. User obtains KYC credential from dregg federation (off-chain)
2. User gets handoff certificate for the pool capability (from pool operator)
3. User submits handoff proof to DreggCapRouter.acceptHandoff()
   -> Now has poolSwiss capability on EVM
4. User submits KYC credential proof to DreggCredentialGate.verifyCredential()
   -> Nullifier recorded (sybil resistance)
5. User adds liquidity to Uniswap -- hook verifies both checks
```

### Privacy Properties

- Pool operator does NOT learn the user's identity (anonymous credential)
- Other LPs do NOT learn who the user is (capability is just a bytes32)
- The federation does NOT learn which pool the user accessed (unlinkable)
- The chain sees: "address 0xABC has capability X and credential Y" but cannot
  link these to any off-chain identity

---

## 9. Comparison with Midnight Bridge

| Dimension | Midnight Bridge | EVM Bridge |
|-----------|----------------|-----------|
| Chain model | UTXO + Compact lang | Account + Solidity |
| Proof target | BLS12-381 (blocked) -> Optimistic | BN254 (working via SP1) |
| Current status | Level 1.5 (optimistic) | Level 1 (vault+credentials) -> Level 2 (this plan) |
| CapTP transport | Substrate RPC + observer | Events + relay + SP1 proofs |
| Namespace | Governed, proven via DFA | Mirrored on-chain via governance proofs |
| Dispute | dregg-side dispute framework | EVM-side dispute contract |
| Sovereign cells | N/A (Midnight has own model) | DreggSovereignCell (this plan) |
| Value transfer | Bond-based optimistic | Existing DreggVault (working) |

The EVM bridge has a STRUCTURAL ADVANTAGE over Midnight: SP1 natively outputs BN254/Groth16,
which EVM can verify directly. No curve conversion needed. This means Level 2 (proof-carrying)
is achievable NOW on EVM, while Midnight is stuck at Level 1.5 until BLS12-381 wrapping works.

---

## 10. Deployment Strategy

### Phase 1: Sovereign Cell (2 weeks)

- Deploy `DreggSovereignCell` with effect-vm-turn SP1 program
- Single cell holding state; relay submits proven turns
- Effects: ERC-20 transfer only (simplest effect type)
- Test: end-to-end state transition with real SP1 proof

### Phase 2: Capability Routing (2 weeks)

- Deploy `DreggCapRouter` with handoff-verify SP1 program
- Test: cross-bridge handoff (dregg -> EVM capability grant)
- Integrate with existing `DreggSovereignCell` for routing

### Phase 3: Namespace + Dispute (3 weeks)

- Deploy `DreggNameRegistry` with governance SP1 program
- Deploy `DreggDisputeBridge` with fraud-proof SP1 program
- Wire existing `DreggVault` as the bonding escrow
- Test: full optimistic bridge claim lifecycle

### Phase 4: DeFi Integration (4 weeks)

- Uniswap V4 hook example (credential-gated LP)
- Aave borrowing with dregg credit score (anonymous proof of creditworthiness)
- Cross-chain atomic swaps via sovereign cell effects

---

## 11. Gas Cost Estimates

| Operation | Estimated Gas | Notes |
|-----------|--------------|-------|
| SP1 Groth16 verification | ~250K | Via SP1 Verifier Gateway |
| transitionState (no effects) | ~300K | Proof verify + state update |
| transitionState (1 ERC-20 transfer) | ~350K | + token transfer |
| acceptHandoff | ~300K | Proof verify + storage writes |
| invoke (dregg target) | ~50K | Event emission only |
| invoke (EVM target) | ~100K+ | Depends on target contract |
| registerWithProof | ~350K | Proof verify + string storage |
| submitClaim | ~100K | State write + bond accounting |
| challengeClaim | ~300K | Proof verify + slash logic |

Total for a dregg turn executing on EVM with one effect: ~350K gas.
At 30 gwei base fee on Ethereum L1: ~$3-5 per turn.
On Base L2: ~$0.01 per turn.

---

## 12. Security Considerations

### SP1 Program Correctness

The security of the entire bridge reduces to: "Are the SP1 guest programs correct?"
If the effect-vm-turn guest faithfully re-executes dregg's Effect VM logic, then
the EVM contract cannot be tricked into an invalid state transition.

Key properties that must hold:
- Effect VM determinism: same inputs always produce same outputs
- State commitment binding: stateCommitment uniquely identifies the state
- Effect completeness: all effects produced by the turn are included in effectsHash
- Turn sequencing: turnNumber prevents replay and ensures ordering

### Relay Trust Model

- For sovereign cells: TRUSTLESS (SP1 proof required for every transition)
- For namespace: Semi-trusted (governance proof required, but governance is off-chain)
- For disputes: 1-of-N honest watcher (same as Midnight bridge)
- For EVM->dregg direction: relay trust for liveness, Ethereum state proofs for safety

### Capability Security

Swiss numbers are the capability. If a swiss number leaks (stored on-chain in a
mapping), does that break security?

NO: the swiss number alone is insufficient. To INVOKE a capability, you must be
the `capabilityHolder[swiss]`. The holder is set during `acceptHandoff()` which
requires an SP1 proof. You cannot become the holder without a valid handoff proof.

The on-chain swiss number is like a "live reference" -- it identifies the capability
but does not confer authority. Authority comes from being the holder in the mapping.
This mirrors CapTP's semantics where having a reference != having authority (you
need to be in the capability's facet).

### Reentrancy

`DreggSovereignCell._executeEffects()` makes external calls (EFFECT_CROSS_CALL).
Reentrancy is mitigated by:
1. State is already updated before effects execute (checks-effects-interactions)
2. Turn counter prevents re-execution of the same turn
3. Guardian can pause if anomalous behavior detected

Production deployment should use OpenZeppelin's ReentrancyGuard on `transitionState`.
