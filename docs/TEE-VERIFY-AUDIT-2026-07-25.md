# TEE Attestation-Verify Crypto Audit — 2026-07-25

VERDICT: **the TEE root-of-trust is SOUND — NO universal-forgery hole.** All three verifiers (Nitro/COSE,
SNP, TDX/DCAP) derive the trust anchor from a PINNED embedded constant (never the document), verify the
vendor signature OVER the actual attested payload with the leaf/VCEK/QE key chaining to that pinned root, and
check measurement/report_data against EXTERNALLY-supplied expected values (a pinned measurement + a
ledger-committed slot). No x==x / sig-over-self / read-off-the-same-doc anywhere. The binding weld
(cell/src/tee_attest.rs:200-268) is the real authorization gate: measurement==commitment, report_data==input_
commitment(slot), tcb_ok, fail-closed with no verifier. Third class/subsystem this campaign found largely-sound
(after arithmetic + fail-open) — the crypto/trust floor is solid; the real work is deployed-surface DoS + edge-cases.

SOUND (confirmed, do not re-audit): root pinning (Nitro cabundle[0] byte-identical to embedded AWS root;
SNP ARK/ASK/VCEK chain from embedded AMD KDS; TDX pinned Intel SGX Root CA + dcap-qvl re-anchor); alg pinning
(Nitro ES384 hardcoded, no alg header read → no alg:none; SNP sig_algo==1 ECDSA-P384); fail-closed defaults
(no verifier ⇒ reject); the measurement/report_data binding; agent-platform landed-slot join (report_data off
the FINALIZED ledger, not the proof); chutes-e2ee gate (fresh nonce, pubkey from discovery not the blob).

SCOPE CORRECTIONS: sandstorm-bridge/serve do NOT depend on tee-verify (separate anchor: owner ed25519 over
(grain_cell_id‖data_root) + Merkle inclusion vs heap-root). attested-dm does NOT (game-internal replay-check,
red herring). discord-bot DOES (chutes-tee → dcap-qvl, sound).

## FINDINGS (all policy-strength / defense-in-depth — NOT auth bypasses)
- **F1 (MEDIUM, fix first) — SNP tcb_ok FAIL-OPEN default.** snp.rs:255,262-266 + meets() snp.rs:107-113:
  `min_tcb` defaults to TcbVersion::default() = all-zeros, and `meets()` returns true when every field >= min,
  so `reported_tcb.meets(&zeros)` is ALWAYS true → tcb_ok=true for ANY TCB. A genuine but DOWN-LEVEL /
  vulnerable-microcode SNP chip is accepted; the weld's `if !claims.tcb_ok` gate (cell/src/tee_attest.rs:260)
  never fires unless the operator remembers `.with_min_tcb(...)`. FIX: make min_tcb non-defaultable (require
  at construction) or default to a sane per-product floor, matching TDX's strict {"UpToDate"} posture.
  (VERIFICATION NOTE: tee-verify → dregg-cell → dregg-circuit, so this fix is currently circuit-churn-blocked
  like the rest; verify on persvati once the descriptor golden lands.)
- F2 (LOW-MED) — VCEK cert TCB not cross-checked vs body reported_tcb (snp.rs:342, snp_chain.rs:224); an
  extracted OLD VCEK key can sign a forged high reported_tcb (contingent on F1 fixed + a key extraction).
  Fix: assert VCEK cert TCB extension >= body reported_tcb.
- F3 (LOW) — cert CA constraints / keyUsage / pathlen SKIPPED (Nitro lib.rs:227, SNP snp_chain.rs:235); not
  exploitable today (pinned root + vendor won't issue a CA-capable leaf) but standard X.509 hardening absent.
  TDX unaffected (dcap-qvl enforces). Fix: enforce CA:TRUE + keyCertSign + pathlen on non-leaves.
- F4 (LOW-MED) — SNP VCEK revocation (AMD KDS CRL) not checked; a revoked VCEK still verifies. TDX checks
  PCK+root CRLs. Fix: check the AMD KDS CRL.
- F5 (LOW advisory) — the verify_report trait returns TeeReportClaims WITHOUT measurement/report_data
  enforcement (sound only because every current consumer checks downstream); a future blind consumer would
  accept a wrong-enclave/replayed quote. Fix: document "claims unauthenticated until measurement AND
  report_data checked", or a single verify_bound(...) entry point.
- F6 (LOW) — Nitro freshness is a 1-hour wall-clock window + the nonce field is parsed-and-IGNORED
  (#[allow(dead_code)]); real anti-replay is the report_data==committed-slot binding (sound when per-turn
  fresh). without_freshness() + a REUSED commitment reopens replay.

## Dispatch: F1 first (the one real-property-off-by-default), then the F2-F4 defense-in-depth cluster, then F5
API-contract hardening. All circuit-churn-blocked for verification (tee-verify → cell → circuit); flush with the
other staged batches when the descriptor golden lands.
