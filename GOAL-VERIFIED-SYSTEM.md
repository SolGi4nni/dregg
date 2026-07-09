<!-- ⚑ MULTIPLE /goal lanes run here — see GOALS-INDEX.md. This is the VERIFIED-SYSTEM campaign lane ONLY. -->

# CAMPAIGN — THE VERIFIED SYSTEM (kernel → crypto → protocol → code, one connected proof)

The crypto-to-protocol-soundness tree is closed to the lattice/DL/hash floor + the leanc toolchain
(HORIZONLOG 07-09). This campaign takes it to **completion**: parameter-level security claims, the last
hypothesis discharged, every deployed primitive extracted, the protocol climbed, the impls widened, and the
two capability systems welded.

## Completion criteria (the campaign is DONE when ALL hold)
1. A **parameter-level theorem**: at the deployed params (ML-DSA-65, ML-KEM-768, committee n), the system has
   **λ ≥ 120 bits** against a quantum adversary making ≤ q queries. (Lattice-estimator input is a labeled
   NUMERIC assumption, honestly named — the only non-proof input.) The first pass gave λ=79 because our
   reductions were LOOSE, not our constructions: `sigBitsR=(msisBits−log2q)/2` is the FORKING square-root and
   `o2hBitsR=msgEntropyBits/2−…` is the O2H square-root. **P1-TIGHT** kills both by formalizing the tight
   literature: lossy-identification (AFLT12) / KLS18's QROM Dilithium proof (tight from decision-MLWE, the
   proof FIPS 204 itself cites) and the double-sided O2H (BHHHP19 / HHM22) for the FO transform over Kyber's
   deterministic T-transform. Expected λ ≈ 140–150.
2. **CircuitSound is a THEOREM**, not a hypothesis → `turn_sound` rests on the floor alone.
3. **Every deployed crypto primitive is a proved Lean object** (leanc-native): ML-DSA sign+verify, ML-KEM,
   X25519, HKDF/SHA-256. `Fips203Correct`/`X25519Correct`/`HkdfCorrect`/`DualPRF` all discharged.
4. **The protocol layer is proven end-to-end**: full BFT liveness (view-change), blocklace equivocation +
   dissemination safety, light-client whole-history soundness, the effect-VM's real step semantics.
5. **Every deployed impl is model-connected** (VRF, beacon, threshold signer, wire-AKE) — like dregg-pq.
6. **The CAP WELD**: one theorem where the capability held in the seL4 kernel IS the capability provable in
   the protocol (hardware-enforced ↔ cryptographically attenuable).
7. Whole tree green; nothing laundered; final trusted base = lattice/DL/hash floor + leanc + the labeled
   lattice-estimate + seL4's own (cited) proofs. NOTHING else.

## Phases + units (deps noted)

### P0 — FOUNDATIONS (unblock P1/P2; do first)
- **0a** Concrete-security framework: negligible functions, a PPT/step-bound machine model, advantage
  functions `Adv : params → ℝ`. Upgrade UC's `≈` from Prop-equality to negligible-ensemble-distance,
  retiring the last modelling note. → unblocks P1.
- **0b** The `-- PRIMITIVE:` digest-binding seam (`Circuit.lean:256`): prove the prover's CR-hash digest binds
  to `chainOk` — reduce to `HashCR`. → unblocks P2.

### P1 — CONCRETE SECURITY (needs 0a)  [the claim]
- **1a** Per-reduction advantage accounting, unified (forking ε²/q_H · FO terms · O2H 2√(q·Pfind) · UC session
  factor · combiner · protocol games · adaptive's zero loss).
- **1b** End-to-end composition: one advantage bound from the deployed parameters.
- **1c** Lattice hardness interface: MSIS/MLWE bit-security at ML-DSA-65 / ML-KEM-768 (estimator input as a
  LABELED numeric assumption; cite the estimator + params).
- **1d** THE THEOREM: ≥ X bits vs a q-query quantum adversary at the deployed params.

### P2 — DISCHARGE CircuitSound (needs 0b)  [the last hypothesis]
- **2a** AIR soundness: the constraint system ⟹ the execution trace is the VM's.
- **2b** FRI soundness — formalize the literature (BBHR18 / DEEP-FRI / the tight bounds). NOT a frontier.
- **2c** Compose: the STARK verifier is sound ⟹ `CircuitSound` is a theorem ⟹ `turn_sound` floor-only.

### P3 — EXTRACTIONS (independent)  [shrink the TCB to nothing]
- **3a** FIPS-204 **sign** (rejection sampling) → leanc-native; `Fips204Correct` fully discharged.
- **3b** FIPS-203 / ML-KEM → leanc-native; `Fips203Correct` discharged.
- **3c** X25519 + HKDF/SHA-256 → leanc-native; `X25519Correct`/`HkdfCorrect` discharged, `DualPRF` REDUCED to
  HKDF's PRF security (not assumed).

### P4 — CLIMBS (protocol; 4d needs P2)
- **4a** Full BFT liveness: view-change / leader rotation until an honest leader (we proved only the
  honest-proposer case).
- **4b** Blocklace equivocation detection + cordial-dissemination safety.
- **4c** Light-client whole-history soundness (the universal fold).
- **4d** The effect-VM's real step semantics + the receipt's exact content (abstract `turn_sound` made concrete).

### P5 — WIDENS (code refinement; independent)
- **5a** crypto-xmvrf VRF → the abstract VRF model (DreggPqRefinement pattern).
- **5b** crypto-hashrand beacon → the beacon model.
- **5c** The deployed threshold signer → the Hermine/TS-UF-0 model.
- **5d** The wire handshake as a proper AKE game (session-key security, channel binding).

### P6 — CAP WELD (the vista; needs CapabilityChain [done] + a seL4 cap model)
- **6a** Model seL4/firmament's capability system (derivation, revocation, the verified kernel invariants —
  cite seL4's own proofs as the hardware-enforced base).
- **6b** Weld: an OS capability ↔ a cryptographic attenuation-chain capability (the same lattice, the same
  no-amplification law).
- **6c** THE THEOREM: the capability you hold in the kernel is the capability you can prove in the protocol.

## Discipline (unchanged, non-negotiable)
CLOSE by formalizing the literature — no smuggling (a labeled hypothesis dressed as closure), NO giving up
("too hard" for a published result). Load-bearing #guard teeth (both-truth) on every theorem. WHOLE-TREE green
(`lake build Dregg2`; `cargo build/test`). Main loop wires `Dregg2.lean` imports; lanes never touch it, other
lanes' files, or Cargo.lock. Scale with ultracode/Workflow. Sign Co-Authored-By: Claude Opus 4.8.

## Next 3 moves
1. Fire wave 1: **0a** (concrete-security framework), **0b** (digest-binding → HashCR), **3a** (ML-DSA sign
   extraction), **5a** (VRF refinement) — the independent/unblocking units.
2. Integrate each (wire imports, whole-tree green, commit); then wave 2: P1 (needs 0a), P2 (needs 0b), 3b/3c.
3. Then P4 climbs + P5 widens + P6 cap weld; HORIZONLOG + memory the final trusted base.

## Done-log (newest last)
- (start) campaign planned; wave 1 firing.
- ✅ WAVE 1 (all 4, whole-tree green 4500 jobs): 0a 71b25c1d4 concrete-security framework (Negl/PPT/Adv) +
  UC's two modelling notes RETIRED · 0b b533bef74 the last `-- PRIMITIVE:` digest-binding seam → THEOREM on
  HashCR · 3a a52eea5f1 FIPS-204 SIGN extracted to leanc-native, Fips204Correct now a THEOREM (both
  directions; 591 C facets via leanc, dregg-pq 9/9) · 5a 7f2cd66c3 deployed XM-VRF refines the abstract VRF,
  uniqueness reduced to HashCR.
- ✅ WAVE 2 (all 6, whole-tree green): P1 3f45ef062 λ=79 (⚠ loose reductions → P1-TIGHT firing) · 3b 3d65cb122
  ML-KEM extracted (Fips203Correct discharged) · 3c 13281a768 X25519Correct a THEOREM + HkdfCorrect + DualPRF
  reduced · 5b 04f30baa5 beacon → HashCR.
- ✅✅ **CRITERION #2 ACHIEVED** — P2 complete: 2a 73b099d43 AIR soundness · 2b 15ae7114c FRI soundness
  (BBHR18 key lemma proved, error ≤ 1/|F|) · 2c 80835f90f `circuit_sound` is a THEOREM (residual HashCR
  alone) ⇒ `turn_sound_unconditional`: a valid receipt ⟹ correct authorized evolution under (DL∨MSIS)∧HashCR.
- ✅ WAVE 3 (all 6, whole-tree green 4513): 4a 9a35d3a44 BFT liveness w/ view-change · 4b cf2694df9 blocklace
  equivocation detector (sound+complete) + dissemination · 4c 52040c675 light-client soundness (a forged
  history BREAKS the floor) · 5c a8e4d6658 threshold-signer refined (live vs staged path stated honestly) ·
  5d 5b04c0dad wire handshake as an AKE game.
- ✅✅ **CRITERION #6 ACHIEVED** — 8479e55fd THE CAP WELD: capMap is an order embedding that preserves AND
  reflects, so the seL4 rights lattice and the protocol attenuation lattice are the SAME lattice. The
  capability you hold in the kernel IS the one you can prove in the protocol.
- ✅ **CRITERION #5 ACHIEVED** (5a VRF · 5b beacon · 5c threshold signer · 5d wire-AKE — every deployed impl
  model-connected). **CRITERION #3** essentially achieved (ML-DSA both directions, ML-KEM, X25519, HKDF all
  leanc-native; DualPRF reduced).
- ✅✅ **CRITERION #4 ACHIEVED** — 4d 508cb014e `turn_sound_real`: the soundness theorem is about the DEPLOYED
  effect-VM (RealEffect mirrors turn/src/action.rs, all six LinearityClass colors; stepGate_iff_real bridges
  the AIR gate to the real step; RealReceipt mirrors TurnReceipt). Residual exactly (DL∨MSIS) ∧ HashCR.
- **SIX OF SEVEN CRITERIA BANKED**: #2 CircuitSound-is-a-theorem · #3 every primitive leanc-native · #4
  protocol end-to-end on the real VM · #5 every impl model-connected · #6 THE CAP WELD · #7 whole tree green
  (4514 jobs), nothing laundered.
- ✅✅✅ **CRITERION #1 ACHIEVED — λ = 149 BITS** (d349cacfc; derived-not-asserted via the DAG inversion
  0be716c0d). Tight reductions: 099f54d74 lossy identification (+93), 56ef72184 double-sided O2H (+45).
  `system_security_at_least_120 : 120 ≤ 149` by decide; 29-bit margin; stress budget 121.
- 🏁 **ALL SEVEN CRITERIA HOLD — CAMPAIGN DONE.** Whole tree green (4518 jobs). Final trusted base: the
  lattice/DL/hash floor + the leanc toolchain + ONE labeled lattice-estimate + seL4's cited proofs.
  HORIZONLOG 4479b11a7; memory project-verified-system.
- (superseded) LAST ONE: criterion #1 — λ ≥ 120. P1-TIGHT (wh5extheb) is killing the forking square root (KLS18 lossy
  identification) and the O2H square root (BHHHP19 double-sided). Then recompute λ in ParameterSecurity and
  hold it to the bar; if short, diagnose the dominant term and tighten THAT.
- (superseded) WAVE 2 firing: P1 parameter-level theorem · 2a AIR soundness · 2b FRI soundness (BBHR18/DEEP-FRI) ·
  3b ML-KEM extraction · 3c X25519+HKDF extraction (DualPRF reduced) · 5b beacon refinement.
