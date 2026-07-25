# Formal-Assurance Map — Light Clients & Circuits (Lean theories) — 2026-07-25

VERDICT: **SOUND-WITH-NAMED-FLOORS for the light-client no-forgery layer; THIN-to-VACUOUS for the
deployed-circuit + on-chain-verifier layer.** The architecture + floor-naming are EXEMPLARY (the iterative/
labeled-floor method done well, WITH self-adversarial vacuity guards) — but the deployed cross-chain assurance
is trusted-Rust / trusted-Solidity END-TO-END: every no-forgery/unfoolability theorem bottoms out at (a)
hand-transcribed Rust==Lean, (b) named crypto-library assumptions, (c) an FRI extraction wire the repo has
PROVEN its current discharges cannot supply.

## Discovery map (HAS a Lean theory vs trusted-Rust/Solidity-only)
- ETH beacon/sync-committee (BLS 2/3-of-512): YES — metatheory/Dregg2/Bridge/LightClientEth.lean (1002 lines).
  Proven over a Lean RE-AUTHORING of the Rust verifier's rules; NO formal Rust↔Lean tie.
- Tendermint (>2/3 Ed25519): YES — LightClientTendermint.lean. Same posture.
- EIP-1186/MPT inclusion (keccak): YES — LightClientMpt.lean. Same posture.
- Solana Tower-BFT/stake-weighted: **NO consensus theory.** ProofOfHoldings.lean's Solana instance is a
  `True`-instance (ProofOfHoldingsGeneric.lean:47); finality = assumed oracle. TRUSTED.
- dregg's OWN consensus LC (hybrid Ed25519+ML-DSA): YES — Crypto/LightClientSoundness.lean — STRONGEST: soundness
  reduced to SchnorrDLHard ∨ MSISHard (honest floor). (This is dregg's own, not a foreign chain.)
- On-chain Groth16/BN254 verifier (DreggSettlement): **NONE outside Market** — trusted-Solidity, no Lean tie.
  (SettlementSoundness.lean is capability-liveness, NOT the pairing verifier.)
- FRI/STARK apex (deployed verifyBatch): YES — CircuitSoundness.lean + StarkSoundReduction + DeployedProximity +
  AirSoundness + CorrelatedAgreement/. Conditional over explicitly-named floors; deployed verifier OPAQUE
  (KAT-validated leaves); discharge attempts PROVEN VACUOUS (below).

## Key findings (theorem | floor | vacuous/missing | deployed-gap)
- ETH `eth_no_forgery` (LightClientEth.lean:554): REAL, non-vacuous — quorum count (342 accept/341 reject)
  genuinely discriminates; floors blsSound/hashPairCR/uChunkInj are VISIBLE STRUCTURE FIELDS (not laundered
  def-hard). BUT the verify RULES are a Lean transcription of the Rust (no translation validation); the BLS
  discharge is only a TOY modelLeaf (∀ pk, pk=7); production BLS = trusted blst.
- Tendermint/MPT: same shape — real threshold/branch-binding proven, toy leaves labeled toy, rules transcribed,
  crypto trusted.
- Solana ProofOfHoldings: VACUOUS for consensus content — the stake-weighted ≥2/3 bank-hash verification is NOT
  formalized (Solana Holds := Unit, a True-instance). No stake-weight/Ed25519 theorem at all.
- dregg own LC `accepting_forged_history_breaks_floor` (LightClientSoundness.lean:173): REAL + SHARP — accepting
  a forged history ⟹ breaks DL or MSIS (deleted a prior HashCR export proven FALSE at deployed params).
- FRI apex `lightclient_unfoolable` (CircuitSoundness.lean:570): #assert_axioms-clean, single-transition,
  freshness/replay OUT OF SCOPE; premise verifyBatch=accept runs against an OPAQUE KAT-validated verifier;
  StarkSound carrier is "NOT provable in Lean" — REDUCED (not laundered — explicit hypothesis, teeth show
  load-bearing) to one FRI research lemma (DeployedTraceExtract) + one Rust refinement (DeployedRefines).
- `air_sound` (AirSoundness.lean:187): near-TAUTOLOGICAL over an abstract applyEff (the AIR is DEFINED as
  row.post = applyEff eff pre → not tied to the emitted circuit — the witness-gen perimeter).
- `accept_soundness_deployed` (DeployedProximitySoundness.lean:123): REAL <2^-31 bound BUT only for the
  single-layer |L|=16 query sampler (radius 7, 38 queries), NOT the multi-layer/batched deployed verifyBatch.
- **SELF-ADVERSARIAL HONESTY** (PremiseInhabitability.lean:425 + FriLdtExtractDeployed.lean:298):
  THREE landed extraction bundles (E1/E2/E3) are PROVEN to make verifyBatch REJECT EVERYTHING for all inputs →
  any apex resting on them is VACUOUSLY true. Confirms the deployed FRI extraction is NOT soundly discharged;
  StarkSound remains a genuine OPEN floor. (The discipline working — the repo proves its own discharges vacuous.)

## Top 5 formal-assurance priorities (these are DEEP research/formalization campaigns, not bug-fixes)
1. Discharge or honestly-floor the FRI extraction wire (DeployedTraceExtract) — the single load-bearing research
   residual: transport the PROVEN abstract-oracle proximity onto MainAirAccept over the deployed VmTrace. Connects
   to the FRI correlated-agreement campaign. Until then the apex is conditional-OR-vacuous.
2. Close the deployed-verifier translation gap (DeployedRefines) — the whole cross-chain surface (+ the STARK) is
   Rust hand-transcribed into Lean; NO object proves verify_batch/eth-lightclient COMPUTES the Lean verifier.
   The "proven-over-re-authored-spec, not proven-over-emitted" gap. Connects to the witness-gen perimeter.
3. The on-chain BN254/Groth16 settlement verifier has NO Lean model — highest-value UNMODELED TCB (trusted-Solidity
   + dev-ceremony trusted setup).
4. Solana LC is trusted, not verified — no stake-weighted consensus theorem; an un-instantiated ForeignLightClient
   slot if Solana is a live settlement source.
5. Ground the crypto carriers beyond toy leaves — a VERIFIED BLS/SHA/keccak (EverCrypt-style) removes the last
   trusted-crypto step for the LC no-forgery theorems.

## The honest resolution (describe-at-current-resolution)
The light-client no-forgery theorems ARE real conditional refinements over honestly-named, visible carriers with
both-polarity falsifiers — but proven over a Lean re-authoring of the Rust, so the deployed Rust LCs are TRUSTED
to match, and Solana isn't even in the set. The FRI/STARK apex is honestly conditional and its deployed discharge
is PROVABLY not yet live (the repo's own vacuity guards). The on-chain BN254 verifier is entirely trusted-Solidity.
Net: exemplary discipline + labeled floors; deployed cross-chain assurance is trusted-Rust/Solidity end-to-end.
See [[project-fri-correlated-agreement-formalization]], [[project-witness-gen-assurance-perimeter]],
[[project-fri-soundness-reality]], [[project-circuit-soundness-apex]].
