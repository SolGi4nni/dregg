<!-- ⚑ This repo runs MULTIPLE /goal lanes — see GOALS-INDEX.md. This is the PQ (no-prequantum) lane ONLY.
     Edit only THIS file; never clobber another lane's trail or files. -->

# GOAL — NO PRE-QUANTUM: leave no classical-only load-bearing crypto standing

Every security-critical **signature** → hybrid (ed25519 ∧ ML-DSA-65, verify BOTH, PQ key ENROLLED+PINNED,
never self-carried). Every security-critical **key-exchange** → hybrid KEM (X25519 + ML-KEM). Per the
07-09 pre-quantum audit.

## Guardrails
- ENROLL+PIN the PQ key to the committee/identity roster (GAP #0 was a self-carried-key hole).
- ADVERSARIAL TEST per surface: forge classical + attacker's OWN PQ key + valid sig under it → REJECTED.
- NO named-carrier laundering (reduce to MLWE/MSIS/hash-CR or flag). HYBRID not PQ-only. DON'T OVERCLAIM.
- HYGIENE: commit only my files; NEVER the paused lanes' files (circuit/committed_threshold, circuit-prove,
  sdk/full_turn_proof, sdk/privacy, rotation/turn-src, federation dkg_ceremony, crypto-hermine) or Cargo.lock.

## ✅ CORE DONE — every named signature surface hybrid + transport hybrid-KEM + deps consolidated
- 04ba2901d  GAP #0  finality re-verifiers PIN the enrolled ML-DSA roster (+ adversarial test) — the load-bearing fix
- 78c1d2081  GAP #1  blocklace lib::Block signing (enrolled+pinned creator)
- a840498bf  GAP #1b LIVE finality::Block signing (the consensus wire block)
- 1868c2180  GAP #2 + HNDL  CapTP handoff hybrid + transport X25519+ML-KEM-768 (X-Wing combiner)
- 526ff41d1  GAP #3  dregg-auth biscuit/credential chain (rooted at enrolled hybrid key)
- d7baf652c  GAP #4  cell-crypto capability proof
- 149c78013  GAP #5  token revocation-root attestation
- d83921917  GAP #6  wire peer authentication
- 2b60ec9ae  wasm light-client roster arity (fail-closed, real fix flagged)
- 77f125197  dregg-pq consolidation: 4 crates migrated, pre-release `kem` pin dropped, one audit surface
- a0136958f  de-launder beacon HonestSlotCR→hash-CR + label VRF/beacon abstract carriers
- d53b54b52 / 367742dd8  de-launder Hint-MLWE→MLWE + DKG→lossiness+Shamir (pre-goal)

## ⚑ FLAGGED-OPEN (honest — not done)
- **NEEDS-EMBER — identity binding.** The capability/handoff/peer/block ML-DSA keys are enrolled OUT-OF-BAND;
  the identities (CellId, FederationId, participant-id) are ed25519-only and don't CRYPTOGRAPHICALLY commit
  to the ML-DSA key. Full closure = hybrid identity `Id = H(ed25519_pk ‖ ml_dsa_pk)` (or the id struct carries
  both) — a tree-wide `dregg-types` change. Flagged by GAP #2/#4/#6/#1. **Ember decision: do the H(ed25519‖ml_dsa) identity, or keep out-of-band enrollment?**
  - GAP #4 (cell-crypto capability proof) is the TEMPLATE where the id-commitment DID land: `CellId` is a hybrid
    id (`derive_hybrid_raw`), the holder self-carries its ML-DSA key, and `verify` gates it with
    `CellId::verify_committed_ml_dsa` — a self-supplied key not committed by the identity is REJECTED, no roster.
  - GAP #6 (wire peer-auth) CANNOT reuse that pattern as-is: the wire `participant_key` is the RAW ed25519 pubkey
    — it is fed straight into `PublicKey::verify` as the ed25519 verifying key (`wire/src/server.rs` ~1912), and
    the constitution / `federation_id` are keyed on ed25519 committee pubkeys (`node/src/genesis.rs` — `committee_
    pubkeys.push(PublicKey(ed))`, `derive_federation_id_with_epoch`). So `participant_key` cannot simultaneously
    BE `H(ed‖ml)` and be used as an ed25519 key. Applying the id-commitment needs the constitution to be re-based
    on hybrid ids (add a separate ed25519 field to `PeerAuthResponse`, make `is_participant`/`federation_id`
    consume the hybrid id) — a node/genesis + federation change, OUT of the wire-only scope. The raw material
    already exists: genesis publishes `hybrid_id = hybrid_id_commitment(ed, ml_dsa)` per validator, unused by wire.
  - MEANWHILE the enrolled roster (GAP #6, `d83921917`) is the SOUND binding and is KEPT UNTOUCHED:
    `ParticipantSource::ml_dsa_pubkey_for` pins the peer's ML-DSA key to its ed25519 identity; the PQ half is
    verified against that enrolled key (never a self-carried pubkey), fail-CLOSED on a missing half. No id-commitment
    was faked onto an ed25519-only id.
- **finality::Block NODE enforcement** (WIRED in source; node re-verify blocked by an UNRELATED dep break):
  Done — (a) `node/src/blocklace_sync.rs`: enroll every committee member's ML-DSA key into the finality
  Blocklace's `pq_roster` from `pq_committee`, at the single post-restore build site (~2255, covers restored /
  fresh / error laces) AND across committee rotation in `apply_committee_change` (rotated-in validators stay
  acceptable); (b) `node/src/catchup.rs:267` (the sole live wire ingest, `handle_push`→`apply_with_buffering`):
  `receive_block` → `receive_block_pinned`, with the match made exhaustive+fail-closed over the new PQ error
  variants (UnsignedPq / BadPqSignature / UnenrolledCreator all dropped, never buffered); (c) a node
  integration-style test (`pinned_ingest_finalizes_honest_and_refuses_forged_pq`) + the existing catchup
  buffering tests updated to enroll. NOTE: the circuit E0609 break has CLEARED (circuit compiles); the node
  re-verify is now blocked instead by 3 type-inference errors in `dregg-blocklace` itself
  (`addressing.rs:130`, `pq.rs:128`, `lib.rs:126` — `.as_ref()` ambiguity from a new `hybrid_array` `AsRef`
  impl pulled in by an out-of-lane Cargo.lock/Cargo.toml dep bump). Outside this lane; do NOT touch blocklace/
  or Cargo.lock. The source changes are precise per the recipe and compile once that dep break clears.
- **wire authority-sig** (GAP #5): wire/server.rs revocation-authority sig needs the same hybrid (coord GAP #6).
- **remaining fips204→dregg-pq migrations**: turn, federation, blocklace, lightclient, wasm (deferred — hot).
- **wasm boundary**: needs an ml_dsa_committee_hex_csv config param + JS callers supplying the enrolled roster.
- **Hermine concurrent TS-UF-0 game** (de-laundering residual, NOT a signature surface): genuinely open;
  masking carrier is reduced to MLWE, but the full oracle+corruption+forking game is unclosed. Honestly flagged.

## Next: FRONTIER (drive as far as honestly lands — flag-don't-fake)
Tanuki (2-round) + TRaccoon (3-round) reference impls (cited-proven benchmark for Hermine); HashRand beacon;
XM-VRF sortition (uniqueness!). Plus the identity-binding once ember decides.

## Done-log detail: see the git log (SECURITY (pq GAP #N) commits) — each carries its enroll+pin+adversarial evidence.
