# Credentials / Anonymous-Credential Audit — 2026-07-26

VERDICT: **HAS-A-FORGERY-HOLE (critical) — the core presentation proof is never cryptographically verified.**
The named "emitted facts_root PI + weld" predicate residual is real + correctly FAIL-CLOSED (a side room). The
FRONT DOOR is open: dregg_credentials::verify() runs NO STARK verifier. MITIGATING (lowers immediate blast, not
API soundness): current external callers route AROUND credentials::verify — discord uses
dregg_sdk::privacy::verify_predicate_unlinkable, the identity service refuses, nameservice uses the executor's
BlindedSet verifier. But verify() is the crate's documented re-exported canonical verifier (lib.rs:35,86).

## Findings
- **F1 CRIT — verify() never verifies the STARK.** verification.rs:143-366 verify_inner calls NO bridge verifier
  (verify_proof_complete/verify_presentation never appear in the crate); it matches the prover-controlled
  proof.verification field + is_valid() (bridge/present.rs:335 checks only real_stark_proof.is_some() &&
  verification==Valid, NEVER running the STARK). Zero-secret attack: make your own IssuerKeys, issue yourself a
  credential with any attributes, present it, set proof.federation_root/revealed_facts_commitment to what the
  verifier expects → verify() returns Ok. The real_stark_proof can be a copy from an unrelated presentation.
  FIX (Rust, the sound path EXISTS): route verify() through dregg_bridge::present::verify_proof_complete
  (present.rs:2214 — runs verify_wire_typed STARK verification) against an EXTERNAL trusted fed root + action +
  freshness. STRUCTURAL: Presentation is not Deserialize + there's no WirePresentation->Presentation path, so
  verify() can only run on a locally-constructed Presentation (prover==verifier in-process, the LocalOnly model
  the crate claims to reject) — the wire-decode path must be added too.
- **F2 HIGH — federation membership bound to proof.federation_root (a pub field), not the STARK PI**
  (verification.rs:328; contrast verify_proof_complete:2244 which binds to PI_ROOT_4ARY), and only checked when
  expected_federation_root is Some. Same fix as F1.
- **F3 HIGH — issuer HMAC minting secret embedded in every credential.** issuance.rs:205 copies issuer.root_key
  into Credential.root_key; present_impl REQUIRES it (MacaroonToken::mint(credential.root_key)). So holder==issuer
  — any holder mints arbitrary credentials (any attributes/holder_id), indistinguishable even to a SOUND verifier.
  Contradicts the crate's own issuance.rs:21 "holder receives only a derived subkey" / :42 "Never share this."
  → unforgeability is VOID even with a perfect verifier. FIX (design+Rust): presentation must not need the issuer
  minting secret; holder holds a derived/encoded token only.
- **F4 HIGH (named residual, fail-closed, NOT a live hole)** — the expected_predicates loop returns
  PredicateProofInvalid UNCONDITIONALLY (verification.rs:313), so cross-credential predicate forgery cannot occur
  (closed by REFUSAL, not binding). The 2b92286895 state_root binding is NOT the live decider (correction to any
  "it's live" reading — verify_predicate_proof_third_party is never called). The residual (expose facts_root as a
  presentation-STARK PI + weld to a credential-committed attr-facts tree) is real + STILL OPEN (Lean/AIR).
- **F5 MED — test vacuity**: cross_credential_predicate_forgery_rejected passes via the blanket fail-close +
  matching_predicate_proof_accepted was inverted to .is_err() → no test distinguishes a working predicate
  verifier from a deleted one; no test exercises F1 with a forged/garbage real_stark_proof. FIX: add a falsifier
  (verification=Valid + foreign/garbage real_stark_proof → refusal); restore both predicate polarities when F4 lands.
- **F6 MED — unlinkability leak**: BridgeFactAttestation ships state_root = final_state_root in the clear, and
  final_state_root is DETERMINISTIC per credential (present.rs:401 "enables linkage") → a passive observer links
  two anonymous shows. Latent under F4's fail-close, but the linkable material still travels the wire. FIX: rerandomize/omit.
- **F7 MED-HIGH — no nullifier / no replay protection / no freshness**: verify() binds no verifier context + never
  checks proof age → infinitely replayable. FIX: bind a verifier challenge/context + freshness (mostly free via
  verify_proof_complete); a spent-context set if single-use required.
- **F8 MED (latent under F1) — 30-bit disclosure narrowing** (presentation.rs:504 & ((1<<30)-1)): once F1 lands,
  disclosure integrity rests on a 30-bit collision bound (~2^30 to swap a disclosed value; attr_symbol shares the
  space → name collisions). The felt-width class. FIX: hash to full-width/multi-limb.
- **F9 LOW (info)** — bridge/present.rs:426 AUDIT[P3] predicts F1 exactly ("a path that checks
  proof.verification==Valid without re-running the STARK could short-circuit"). The field is pub + not serde-skip.

## Top 5 + status
1. F1 route verify() through verify_proof_complete (closes F1 + most of F2 + much of F7). Nothing else matters until this lands.
2. F3 get the issuer minting secret out of the credential (holder==issuer voids unforgeability even with a sound verifier).
3. F2 bind membership to the STARK PIs unconditionally (falls out of F1).
4. F7 replay protection (challenge/context + freshness).
5. F5+F4 restore meaningful predicate tests alongside the Lean facts_root AIR (both polarities in one commit).

Predicate-forgery status: closed by unconditional REFUSAL (fail-closed), not a live binding; the state_root
third-party binding is a MODEL result (AttestedFactsRootModel.lean) not wired to the emitted descriptor; the
facts_root PI + attr-facts weld is the still-open named residual. CAMPAIGN CORRECTION: the predicate residual is
NOT the principal open forgery surface — F1 (verify never verifies) sits ABOVE it and is exploitable with zero
secrets via the public API.
