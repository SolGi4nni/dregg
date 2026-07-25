# fhegg / FHE-Market Stack — Discovery + Forward Scope — 2026-07-25

VERDICT: **PARTIAL, leaning "advanced PoC"** — a real, proven-at-spec-level FHE clearing kernel that is NOT
yet a wired, distributed, malicious-secure product. NOT scaffold (the FHE + threshold decrypt + smudging + MPC
crossing genuinely RUN, oracle-/Lean-anchored); NOT spec-only (real fhe.rs BFV + tfhe-rs; a passing e2e
dark-clearing test ~4.8s); NOT near-ready (nothing wired into a live UX; the committee is single-process;
malicious security + the ZK floor open; the live DrEX clear is regression-broken).

## WHAT'S REAL (unusually mature for its stage)
- FHE scheme REAL: default BFV via fhe.rs (Lepoint pure-Rust BGV/BFV) + opt-in TFHE via tfhe-rs (Zama, tfhe-integer).
  fhe_clear (lib.rs:316) encrypts unary order increments, folds with FheUint32::sum, computes argmax_p min(D,S)
  homomorphically, decrypts ONLY (p*,V*). Oracle-anchored (bfv_lean_oracle/bfv_mul_oracle). Honest limit: a
  measured PoC envelope; ct×ct multiply is depth-1 with a tight t≈2^20 wrap budget.
- Threshold BFV decrypt REAL + strongest-built: n-of-n, party-owned custody (collective s=Σsᵢ NEVER constructed),
  its OWN smudging noise (doesn't trust fhe.rs's TODO-flagged share noise) PROVEN in metatheory/Bfv/Smudging.lean
  (deployed_smudge_hides sd≤2^-48 vs the 2^32 fold; deployed_smudged_decrypt_exact 16 parties; teeth
  deployed_smudge_floor_leaks a 2^15 smudge leaks totally). Fails closed on short/dup/under-smudged share sets.
- Output-boundary MPC crossing REAL (semi-honest GMW/Beaver argmax); attestation quorum REAL (ed25519+ML-DSA).
- Lean corpus (metatheory/Market/, 89 files ~37k lines, green): Clearing.lean (clearing_fair/conserves/mint_refused),
  FhEggClearing.lean (demand_perm/supply_perm permutation-invariance, clearedBatch_conserves/uniform, clearedVolume_
  optimal), MpcClearingSecurity.lean (perfect_hiding, full_collusion_breaks_hiding, reveal_only), RevealNothing.lean
  (View≈Sim∘Q — the privacy crux). Non-vacuous (no sorry/axiom, both-polarity teeth). FhEggRustDenotation.lean ties
  the Rust decrypted observable to the Lean argmax — but ONLY the plaintext/decrypted semantics (the tfhe-rs
  ciphertext-eval correctness + AggregatesFitU32 stay NAMED residuals).

## ⚡ ACTIONABLE REGRESSION (from our own twin-deletion campaign) — /clear FIXED, other consumers still dark
The DrEX /clear ring-settle was REGRESSION-BROKEN: the clear-book CLI never installed an IntentVerifiedGate, so
the twin-deletion fail-closed REFUSED every clearing book INCL the demo, with a message that blamed the ring
("verified settlement rejected the ring: …FFI unavailable"). Note the fail-closed itself is CORRECT and stays:
an unverified in-process Rust fold must not decide a settlement. What over-reached was the APP, not the gate.
FIXED: the CLI is exec-lean/src/bin/drex_clear.rs (NOT intent/src/bin/ — it was moved into dregg-exec-lean, the
crate that owns the gate impl, because FFI-free dregg-intent cannot depend on exec-lean without a cycle), and its
main calls dregg_exec_lean::register_distributed_gates(). A missing core now names the BUILD/ENVIRONMENT instead
of the book, and exec-lean/tests/drex_clear_gate.rs pins both poles.
STILL UNREGISTERED (same fail-closed, no gate reachable — each settles a ring with no gate installed):
perf/src/bin/orchestration_demo.rs (a BIN that .expect()s the settle → panics; already deps dregg-exec-lean, so
it is a one-line fix), starbridge-apps/tussle, starbridge-apps/sealed-auction (both only MENTION
register_distributed_gates() in doc comments — neither calls it, and neither deps exec-lean), app-framework
(ring_trade / service_promise / agent_coordination) and every app on it (discord-bot, dreggnet-market), plus the
public intent lib entries fulfillment.rs::execute_fulfillment_flow_verified* / trustless.rs / drex_routing.rs.

## FORWARD — top 5 things we NEED (ranked)
① [BLOCKS LAUNCH] **A real distributed MPC/threshold runtime.** Today every party is a THREAD in one process +
  a SIMULATED Beaver dealer (threshold_committee.rs: "one process holding all n shares is one compromise away
  from all"). Semi-honest, not malicious. NEED: network DKG, authenticated transport (the ed25519/ML-DSA/X25519
  material exists in mpc_party/transport.rs, not a deployed runtime), t-of-n availability (Shamir quorum.rs exists,
  not the deployed committee), real inter-party OT/HE preprocessing (not the dealer). THE largest gap; the DARK
  tier IS the MPC. (See the MPC scope doc.)
② [BLOCKS LAUNCH] **Wire the real clearing into a live path + fix two hard stops:** the DrEX /clear gate regression
  (above); the Cert-F STARK wrap UNREACHABLE for live orders (hardcoded epsilon=0.5 in fhegg_clear.rs:235 can't
  match the 2-program registry — make registration dynamic); the proven private-book relation called only from
  test code (call prepare_private_clearing_zk from the production worker). No real crypto touches a user surface.
③ [BLOCKS LAUNCH] **Malicious-secure computation-integrity proof over the encrypted clearing.** attestation.rs
  binds + checks reveal-only SHAPE but does NOT prove (p*,V*) is the correct clearing of the encrypted inputs
  (ComputationIntegrityEvidence::BindingOnly can never pass verify_full). Need the Cert-F STARK live so a
  malicious clearer/solver is CAUGHT (verify-not-find). Today BindingOnly is a self-assertion.
④ [HARDENING] **Discharge the HidingFriPcs statistical-ZK floor** — the deployed reveal_law is a NAMED struct
  field (RESEARCH-grade), not a theorem; discharging it makes reveal-nothing UNconditional (the assurance capstone).
⑤ [HARDENING] **PQ value-commitment cutover** (Pedersen/Ristretto DLog binding is Shor-broken — privacy is
  quantum-safe, BINDING is not; Option A Poseidon2 hash-commitment + fully-in-AIR STARK conservation is mostly
  built) + **ct×ct depth/noise theory** (multiply noise is measured not proven; metatheory/Bfv/Noise.lean covers
  addition only) — required before any private-QUADRATIC clearing (AMM invariant, option payoff) beyond additive
  uniform-price.

## HOW fhegg DEPENDS ON MPC (the shared floor)
fhegg's no-viewer (DARK/Tier-0) guarantee IS an MPC property — remove MPC and it's a fast BFV aggregator some
single key-holder decrypts (the omniscient-viewer failure). Three layers: (1) threshold BFV decrypt (threshold.rs
+ quorum.rs, soundness on Bfv/Smudging), (2) the output-boundary MPC argmax crossing (mpc.rs + mpc_party/,
reveal-only enforced cryptographically), (3) the attestation quorum. Satisfied ONLY in-process today. The
production MPC obligations (network DKG, authenticated transport, t-of-n availability, real OT/HE preprocessing,
malicious security) are NEED ① and gate the entire DARK tier. Interlocks with the dark-pool + MPC scope docs.
Roadmap: docs/deos/{SHIELDED-DREX-ASSURANCE-ROADMAP,DREX-TIER-STATUS-2026-07-24}.md.
