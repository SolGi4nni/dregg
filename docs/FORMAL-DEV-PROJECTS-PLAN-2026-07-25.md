# Formal Dev-Projects Plan — Cross-Chain Verification & Circuits — 2026-07-25

Three interlocking dev-projects to turn the deployed cross-chain verifiers from TRUSTED into PROOF targets.
The formal-assurance audit (docs/FORMAL-ASSURANCE-LIGHTCLIENT-CIRCUITS-2026-07-25.md) found the deployed
assurance bottoms out at (a) hand-transcribed Rust==Lean, (b) named crypto assumptions, (c) an unbuilt
Groth16 pairing model + an FRI extraction wire the repo proves its discharges can't yet supply. Each project
closes one side; they interlock.

## THE INTERLOCK (one goal, three faces)
- **LC twin-deletion** closes the RUST side — delete the re-authored Rust LC verifier, route through a Lean
  @[export] the decision is DEFINITIONALLY equal to.
- **BN254 pairing model** closes the PROOF side — build the missing Groth16/BN254 soundness proof + discharge
  the SettlementVerifier25Refines residual.
- **HOL4/Verifereum** closes the BYTECODE side — ∀-input proofs over real compiled bytecode (and provides the
  EVM semantics the pairing-model's deployed-verifier tie needs).

## PROJECT 1 — Light-Client Twin-Deletion  ✅ ETH SLICE LANDED
The Lean LC no-forgery theorems were proven over a Lean RE-AUTHORING of the Rust (no translation validation).
ember's insight: that re-authoring is a TWIN → apply the twin-deletion method. @[export] the verification
LOGIC (quorum count / ≥2/3 threshold / branch-depth); keep the crypto PRIMITIVES (BLS/Ed25519/keccak) as
named verified-FFI carriers; DELETE the Rust `&&` decision composition.
- ✅ **ETH: DONE** (`94d52c7877`) — LightClientEthGate.lean, `ethVerifyDecision_refines := rfl` AXIOM-FREE
  (re-verified via lake build), @[export] dregg_eth_lc_verify, fail-closed Rust route bridge_lc_ffi.rs.
  The deployed decision IS the proven object.
- ⏭ **Tendermint** — same method, stake-weighted (export summed voting-power ≥2/3 + next_validators overlap;
  Ed25519 batch = carrier). Identical export shape.
- ⏭ **MPT** — treat alloy-trie EIP-1186 verify as the keccak carrier; export the account/storage BINDING
  logic (RLP extraction + slot-key derivation + terminal-value equality).
- ⏭ **ETH wiring landing** (mechanical, swarm-build): build.rs check-cfg + archive_exports probe + splice
  target; lean_init.c extern + _str shim; lib.rs mod; eth-lightclient calls verified_eth_lc_verify authoritative
  fail-closed + deletes the Rust composition (= the same landing that wires the deployed ConsensusProven relayer).
- Crypto carriers (honest): SHA-256/keccak → HACL*/EverCrypt (F*-verified); BLS12-381 → blst (audited
  ETH-client reference + Galois SAW proofs; a full verified pairing does not exist — the honest frontier).

## PROJECT 2 — BN254/Groth16 Pairing Model + SettlementVerifier25Refines  (DEEP, FOUNDATIONAL)
Finding: NO Lean model of the Groth16 pairing exists (millerLoop/finalExp/Fp12/G1G2/pairingCheck = zero .lean).
What EXISTS in metatheory/Market/: an abstract-oracle verifier + a real 25-lane ABI codec + a genuine Lean
model of the WRAPPED R1CS CIRCUIT (BN254-scalar gadgets, KAT-tied to chain/gnark/*.go) — a strong SCAFFOLD,
not a pairing proof. The soundness residual SettlementVerifier25Refines (ProtocolAssurance.lean:872, accept ⟹
∃ DrexClearing) is tightly stated + OPEN.
- Step 1: **Build the BN254 pairing model** — e(·,·) over Fq/Fq2/Fp12, the 4-pairing Groth16 check + the
  gnark Pedersen-PoK 2-pairing, matching DreggGroth16Verifier25.verifyProof step-for-step. Mathlib has the
  field towers, not the BN254 pairing — genuinely does not exist (unlike the FRI floor's proofs-on-disk).
- Step 2: **Discharge SettlementVerifier25Refines** — instantiate the oracle with the model + prove the
  stateLanes codec faithful. The single highest-value named hole.
- Step 3: tie the deployed verifiers (Solidity precompile / arkworks / alt_bn128) — needs a real EVM/Rust
  semantics → Verifereum (Project 3) for the Solidity leg; else KAT/differential.
- Step 4: model the VK + prove deployed-VK ↔ emitted-circuit correspondence.

## PROJECT 3 — HOL4/Verifereum Bytecode Proofs  (REAL, READY, one URGENT prereq)
Verifereum (~/dev/verifereum, separate repo) = a production HOL4 EVM semantics (Osaka, ~complete EEST, frame +
gas-monotonicity + a separation-logic program logic). Proves ∀-input properties over REAL forge-compiled
bytecode (deploy tx run in-logic). Two dregg contracts proven clean (DreggLaunchToken refinement +
anti-rug logical core; DreggProofAttestor + the bind-latch anti-swap SPEC_bind_oneshot_reverts); one theory
(whole-contract SPEC_mint) OOM-STALLED; the clearing T1-T6 are NOT bytecode-proven (docs outrun proof).
- 🚨 **URGENT PREREQ: the dregg proof corpus is UNTRACKED in git** (5 dregg*Script.sml + evmSpecAutomation in
  ~/dev/verifereum/examples/) — one `git clean` from gone. COMMIT FIRST (ember's repo).
- ⭐ **Near-term win: DreggVault no-double-withdraw** — clone the bind-latch proof (identical one-shot shape) →
  a ∀-input bytecode theorem turning the audit's informal CEI+nullifier claim into proof. Highest assurance/effort.
- Then #10 unlocked bond (REFUTE current + VERIFY the fix, both-directions), #1 settable-VK slot-immobility
  (frame theorems), #13 credential binding (partial). #4 fee-on-transfer needs SPEC_Call (the external-call
  frontier — new capability). Keep proofs door-scoped from the post-ABI JUMPDEST (SPEC_mint whole-contract OOM'd).

## RECOMMENDED ORDER (value × tractability)
1. **Commit the Verifereum corpus NOW** (durability emergency, trivial, ember's repo).
2. **Finish LC twin-deletion** (Tendermint + MPT + the ETH wiring landing) — tractable, on-brand, closes the
   most surface; ETH already proves the method works axiom-clean.
3. **DreggVault Verifereum latch** — near-term bytecode gold-standard, clones a done proof.
4. **BN254 pairing model + SettlementVerifier25Refines** — deep + foundational; unblocks the whole Groth16
   soundness story + Project 2 steps 2-4. Do after 1-3 (biggest effort, but the highest ceiling).
