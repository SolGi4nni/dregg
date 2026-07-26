# MPC + Threshold-Crypto Stack — Discovery + Forward Scope — 2026-07-25

VERDICT: **more real MPC than a skim suggests, less deployable MPC than the surface implies.** Nearly every
primitive is genuine cryptographic code — real BFV threshold FHE, real Chou-Orlandi OT, real Yao garbling, real
JF-DKG, real TLSNotary 2PC. What is MISSING everywhere is the SAME two things: (1) DISTRIBUTED no-single-viewer
custody (committees are real objects but run IN ONE PROCESS — a "simulated ceremony"/"shared dealer"), and (2)
MALICIOUS security (everything is semi-honest with trusted preprocessing). **No single MPC primitive is missing —
an operational PERIMETER is missing around MPC that already computes correctly in a test harness.**

## By primitive (real / grade)
- THRESHOLD SIGS: the DEPLOYED quorum (federation/src/frost.rs:169 HybridVotes) is a MULTISIG (count of distinct
  ed25519+ML-DSA sigs), NOT a t-of-n threshold sig (ThresholdSignerRefinement.lean:34). Real threshold sigs exist:
  FROST VERIFY real/final (verify_frost_quorum RFC8032), FROST SIGN test-only (trusted FrostTestDealer, omits
  RFC9591 binding factors — "NOT for live concurrent signing"); hints BLS real (subset-dependent, right for certs);
  the BLS randomness beacon (beacon.rs) genuinely t-of-n-unbiasable. crypto-hermine/tanuki/traccoon = PRE-AUDIT
  references (toy challenge hash, splitmix64 not CSPRNG, non-constant-time; default-off, "must never sign live").
- DKG: the STRONGEST part — real JF-DKG (GJKR Feldman commitments + complaints + QUAL + resharing, dkg.rs) + a
  real slashable DKG SERVICE (node/src/dkg_service.rs) + fhegg bivariate-VSS DKG (threshold/quorum.rs). Gaps: transport
  modeled (PrivateShare "PLACEHOLDER for a ciphertext"), agreement assumed via blocklace, malicious range-proofs absent.
- GARBLED + OT: REAL Chou-Orlandi OT (cell-crypto/src/oblivious_transfer.rs, cofactor checks) + REAL Yao garbling
  (circuit/src/garbled.rs, Poseidon2 hash) + a REAL 2PC sealed-bid auction (demo-agent) — BUT single predicate (>=),
  2-party, output decoded BY THE GARBLER, semi-honest, and the integrity STARK is RETIRED (privacy holds,
  integrity vs a malicious evaluator does NOT).
- FHE + THRESHOLD DECRYPT — TWO distinct schemes (do not conflate):
  1. federation/src/threshold_decrypt.rs = the TURN-PRIVACY prototype, WEAK: GF(256) Shamir of a SYMMETRIC key that
     RECONSTRUCTS the full key in one place (threshold KEY-reconstruction, not partial decryption), TRUSTED DEALER.
     Used LIVE by intent/src/trustless.rs + sdk/src/council_seal.rs. Lean (Distributed/ThresholdDecrypt.lean) faithfully
     proves t-privacy + fail-closed + tamper-detect — but of a trusted-dealer key-reconstruction scheme.
  2. fhegg_fhe::threshold = the REAL threshold FHE (real BFV/tfhe backend; real n-of-n retained ternary shares,
     s=Σsᵢ never constructed; partial_decrypt with smudging >= 80 bits Lean-pinned Bfv/Smudging.lean; real t-of-n
     crash-tolerant Shamir quorum; proven teeth: an n-1 forging coalition recovers garbage). GAP: custody is
     SINGLE-PROCESS (threshold_committee.rs:16 "one process holding all n shares is one compromise away";
     dark_pool_offering.rs "a SHARED DEALER... can decrypt the book unilaterally... a SIMULATED ceremony").
  3. output-boundary MPC crossing (fhegg boundary.rs + mpc.rs) = real GMW/Beaver argmax revealing only p*/V*,
     semi-honest, in-process, simulated triples.
- MPC-TLS/zkTLS: REAL TLSNotary 2PC (feature-gated tlsn-live, vendored tlsn + mpz crates, separate notary,
  cert-pinning, live-host paths) — BUT default is a SELF-SIGNED FIXTURE ("NO PROVENANCE"), and the wired
  deos-hermes agent path uses the fixture by default. deco-prove is NOT DECO 3-party (a STARK over an
  already-disclosed transcript). Hardening/deployment story, not a missing primitive; not on the market's critical path.

## The 3 private-market paths + the shared blocker
- PATH 1 (Penumbra/Shutter): threshold-decrypt committee (dark_pool_offering/oracle_pit). Needs fhegg combine
  (real) + MISSING distributed custody + authenticated transport + malicious DKG.
- PATH 2 (FHE + output-MPC): fhegg BFV fold + boolean-MPC crossing. Needs fhegg threshold + GMW (real) + MISSING
  distributed custody + malicious security.
- PATH 3 (ZK shielded notes, "decrypts NOTHING"): Market/ShieldedClearing.lean over shielded commitments. Needs
  STARK/FRI hiding (BUILT) + NO COMMITTEE + MISSING: inherits the UNDISCHARGED FRI/STARK soundness floor.
- The Dark Bazaar family (private_clearing/certified_clearing/fhegg_settlement) does NO threshold decryption — a
  PLAINTEXT sealed auction (one process sees every bid) wrapped in ZK + signing quorums. Tier-1 operator-visible.

## ⚡ THE STRATEGIC FORK (the headline)
ember's own DREX-DESIGN.md §1: EVERY DEX is stuck on a trusted party — Penumbra/Shutter on a threshold COMMITTEE
(Path 1), CoW/dYdX on a solver/proposer. Two of three in-tree paths carry the committee (Path 1 directly; Path 2
needs it to decrypt the aggregate). **ONLY PATH 3 structurally ELIMINATES the decryption committee** ("decrypts
nothing" over shielded commitments) — at the cost of the undischarged FRI/STARK floor. So the real fork is:
**build the honest distributed threshold committee (Paths 1/2, MPC-heavy) OR discharge the FRI floor and lean on
Path 3 (ZK-heavy, NO MPC decryption).** MPC is the shared floor under Paths 1&2; it is AVOIDABLE on Path 3.
→ This ties the session's FRI-correlated-agreement work directly to product strategy: discharging the FRI floor
yields a COMMITTEE-FREE private DEX that structurally beats every competitor. See
[[project-fri-correlated-agreement-formalization]], [[project-fri-soundness-reality]].

## Top 5 MPC NEEDS (ranked)
1. [BLOCKS-LAUNCH, shared Paths 1+2] Distributed threshold-decryption committee — turn the single-process
   simulated ceremony into n independently-hosted custodians with authenticated transport. OPS + protocol wiring
   around FINISHED crypto (fhegg_fhe::threshold), not new cryptography.
2. [BLOCKS-LAUNCH] Malicious-secure DKG for the FHE committee — lattice range proofs (ternary/CBD shortness) +
   complaint ARBITRATION (fhegg/hermine DKGs are detection-only; port the federation JF-DKG QUAL/slash skeleton).
3. [BLOCKS-LAUNCH] Retire the trusted-dealer GF(256) turn-privacy scheme (federation/src/threshold_decrypt.rs, used
   live by intent/src/trustless.rs) — replace with the real fhegg asymmetric path or the Path-3 decrypt-nothing approach.
4. [HARDENING] Malicious security for the 2PC/MPC compute (authenticated garbling / cut-and-choose, real
   correlated-randomness gen, malicious OT extension) — the retired garbling-integrity STARK is the first tell.
5. [HARDENING] A publicly-deployed independently-pinned MPC-TLS notary (the real 2PC works; the default fixture
   is the gap). Load-bearing only for the web-fact/oracle leg, NOT market clearing.

Files first: fhegg-fhe/src/threshold.rs + threshold/quorum.rs (the real committee to distribute),
dreggnet-market/src/threshold_committee.rs:16 (the custody gap), docs/deos/OUTPUT-BOUNDARY-MPC.md (the
semi-honest→malicious frontier), metatheory/Market/ShieldedClearing.lean (the committee-free Path 3).
