# dregg2/metatheory — Coverage + Lean-Rebuild Roadmap — 2026-07-26

The strategic map for ember's "escape the buggy architecture" direction: what Lean already IS the implementation
vs a shadow model, and the ordered path to route the rest through proven Lean @[export]s (delete the Rust twin).

## Classification (the crux is the FAIL-MODE + PROOF-CONTENT, not just A/B/C)
- **A-hard** — routed AND hard fail-closed: no Rust twin on any path; export absent ⇒ refuse. (Twin-deletion end state.)
- **A-soft** — routed BUT fail-OPEN to a live Rust twin when the export/oracle is absent; held out of a --release
  build only by the build-gate (DREGG_REQUIRE_VERIFIED_EXPORTS PANICs a release lacking an export), NOT by the
  runtime. The twin is alive on wasm/zkVM/dev/opt-out.
- **A-latent** — seam+export exist, fail-closed, but NO deployed decision calls them yet.
- **B** — Lean models it beside the Rust; the deployed decision is the Rust twin (rebuild candidate: proof exists,
  wiring doesn't). **B-dead** — export built+build-gated but ZERO deployed callers.
- **C** — pure Rust, no Lean object.
- PROOF-CONTENT (orthogonal): REFINED (proven =/↔ the committed AIR / a real floor) · DIFFERENTIAL (#guard/KAT
  byte-parity, no ∀) · CALCULATOR (numbers no adversary theorem backs).

## Coverage summary
- EXECUTOR: apply/authorize/conservation = **A-soft REFINED** (producer mode installs the Lean post-state via
  execFullForestG; conservation → @[export] dregg_cross_cell_conserves, decision_conserves_iff_air_boundary to the
  COMMITTED AIR — the strongest; BUT fail-OPEN to unverified_rust_conservation_fallback / BlockConservation when the
  oracle is absent). Constraint admission = **A-hard(release) DIFFERENTIAL** (DeployedConstraint.lean has 0 theorems
  — #guard parity only). RecordKernel = model REFINED.
- CapTP: handoff = **A-hard REFINED** (clean; handoff_concrete_attenuation grantedPerm≤heldPerm). drop/pipeline =
  **A-soft** (fail-OPEN to Rust GC/FIFO via gate()?-None). revocation = **C** (pure-Rust swiss table).
- PERSISTENCE: recover=replay = **B** (recover_eq_replay proven, NO @[export], recovery is pure Rust). WAL = **B**
  (wal_crash_recovery_sound, no export). content-root = **B-dead** (export built, zero callers).
- CONSENSUS: finality quorum = **A-hard REFINED** (quorum_no_conflict); τ-order = **A-hard(startup)**; coord 2PC =
  **A-hard(release)**; coord causal-order + shared-budget = **A-latent** (registered, NEVER called);
  Safety/Settlement/Epistemic keystones = **B** (pure metatheory, gate nothing deployed).
- cell-crypto: ML-DSA/ML-KEM verify/sign/decaps = **A-hard DIFFERENTIAL** (KAT native_decide on ≤10 vectors, ∀
  deferred to *CoreSpec, keygen refinement OPEN); ML-KEM keygen = **A-soft FAIL-OPEN** (WARNS + proceeds — the one
  PQ core that fails open); Pedersen/Schnorr/Bulletproof = **B** (undischarged DLog carriers; the Bulletproof Lean
  model is a DIFFERENT construction than deployed dalek); OT/X25519/HKDF = **C** (toy/unmodeled).
- Already-mapped: cross-chain LC verifiers (ETH/MPT/TM) = **A-hard REFINED** (the gold standard — hard fail-closed,
  ethVerifyDecision_refines rfl over verifyFinalizedUpdate); Circuit AIR emit = A REFINED; FRI apex = **A-form
  CALCULATOR** (no adversary object, undischarged FRI floor); shielded note-tree root = A but the pool value-holding
  is not deployed; credentials = B.

## ORDERED REBUILD ROADMAP (value × tractability)
**Tier 0 — flip A-soft → A-hard (proof already routes; just close the fallback; cheapest; retires live drift):**
1. **Conservation fail-close** (HIGHEST) — startup hard-fail when register_conservation_oracle() is false (mirror
   lib.rs:1704's process::exit(1)); DELETE BlockConservation from the native path (atomic.rs:445). The asset-inflation
   boundary that drifted once (the executor #1 + cell-crypto F1 holes THIS session both live here). [= the executor
   fix lane's #2, in flight.]
2. **CapTP drop + pipeline fail-close** — replace gc.rs:82 / pipeline.rs:63 None-fallbacks with export-or-refuse
   (handoff already did this). One line per site.
3. **Constraint gate off debug_assertions** so debug builds don't silently run the Rust twin.
**Tier 1 — wire A-latent → A (proof+seam exist, no caller):** 4. Coord causal-order + shared-budget (route a node
decision through the proven gates). 5. storage_content_root dead export → live.
**Tier 2 — B → A (author the export, proof partly exists):** 6. Persistence recover=replay/WAL (author @[export
dregg_recover], route state.rs/commit_log.rs — durability is the weakest axis, 100% Rust today despite the theorems
on disk). 7. Constraint proof content (author admits↔spec — currently 0 theorems, a name-is-a-claim risk).
**Tier 3 — discharge thin proof on routed gates:** 8. PQ ∀-refinement + ML-KEM keygen fail-close. 9. FRI adversary
object (its own standing campaign).
**Tier 4 — C → B/A (build the model):** classical crypto binding (Pedersen/Schnorr/Bulletproof — verify-the-circuit,
not re-derive dalek), OT, X25519/HKDF (arguably library-boundary, lowest priority).

## VERDICT
dregg2/metatheory IS the live implementation for the value- and authority-bearing decision surface of a native
--release node (build-gated + two startup process::exit(1) checks — NOT shadow for a correctly-built node: executor
apply+authorize+conservation, the constraint gate, the 3 cross-chain LC verifiers, CapTP handoff, consensus
finality, coord 2PC, AIR emission, shielded note-tree root, PQ cores). A genuine move past the 07-23 twin-deletion
PLAN — conservation, the twin that had NO export then, now routes through dregg_cross_cell_conserves.
BUT not uniformly, on 3 axes: (1) FAIL-MODE — much of the routed surface is A-SOFT (conservation, apply, capTP
drop/pipeline, ML-KEM-keygen), a live Rust twin held out of a release by the BUILD-gate not the runtime, plus 2
A-latent coord gates. **HONEST CORRECTION: "11/11 twins deleted" is optimistic — the twins are DEMOTED +
BUILD-GATED, not deleted from the code.** (2) PROOF-CONTENT — routing ≠ proof: the constraint gate (0 theorems), the
PQ cores (KAT on ≤10 vectors, ∀ OPEN), the FRI ledger (a bit-calculator, no adversary object) route through
proof-free objects (the "a name is a claim" register). (3) WHOLE SHADOW SUBSYSTEMS — persistence/durability is
pure Rust (theorems exist, nothing routes), classical cell-crypto is B, credentials B.
ONE-LINE: the SPINE (turn authority + conservation, cross-chain verification, consensus finality, PQ signatures)
has crossed from shadow model INTO the implementation and is structurally guarded; the frontier is (a) hardening
A-soft → fail-closed so the Rust twins can actually be DELETED, (b) giving the routed-but-thinly-proven gates
(constraint/PQ/FRI) real refinements, (c) pulling durability out of pure Rust — the last core subsystem with zero
deployed Lean linkage despite the proofs on disk. See [[project-twin-deletion-campaign]] (correct the "11/11
deleted"), [[project-lean-must-be-the-implementation]], [[project-dregg2-coverage-map]].
