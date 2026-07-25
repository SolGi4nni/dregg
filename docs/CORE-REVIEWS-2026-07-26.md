# Core-Subsystem Adversarial Reviews — 2026-07-26

Four read-only reviews of the deepest core (capability, executor, persistence, crypto) — the surfaces everything
rests on, not focus-audited before. THE THROUGH-LINE: the two most serious findings are the SAME class — a
CONSERVATION gate that binds VALUE but not ASSET, at two sites — a cross-asset inflation vector; plus a live
capability-introducer forgery. All being fixed. All are DRIFTED RUST TWINS (hand-mirrored from Lean, not
@[export]-routed) — so the fixes weld the Rust to the Lean, and the deeper move (the wholesome regime) is routing
the decision through the Lean @[export].

## EXECUTOR CORE (HAS-A-CONSERVATION-HOLE)
- **#1 HIGH — Effect::Transfer cross-asset teleport.** apply.rs apply_transfer moves scalar balance between cells
  of DIFFERENT token_ids with NO same-asset guard and NEVER feeds the per-asset conservation accumulator
  (asset_deltas is fed only by action.balance_change). Transfer{from: cheap-asset-X, to: valuable-asset-Y} inflates
  Σbal[Y] from nothing. Diverges from the Lean kernel recTransferAsset (single-column move). FIX (dispatched): the
  from.token_id()==to.token_id() guard. Latent if the ledger is single-asset, but definitively missing.
- #2 MED — conservation oracle fallback not fail-closed on a NATIVE no-oracle node (silently runs the
  BlockConservation twin that drifted into the asset-blind bug once). FIX: fail-closed on native absence.
- #3 MED — post-Phase-1 rejections mutate fee/nonce but return an empty delta → the nonce advance can be dropped
  → replay. FIX: carry the fee/nonce mutation on Rejected.
- SOUND: authorization EXHAUSTIVE (no catch-all — a new Effect can't default-allow), mint/burn/note proof-bound,
  replay/nonce, symbolic-mode gate-equivalence. LEAN STATUS: per-asset conservation is Lean-gated ONLY when the
  oracle is installed; authorize/cap-tooth is a DRIFTED RUST TWIN (not @[export]-routed) — a rebuild candidate.

## cell-crypto SUBSTRATE (SOUND primitive + a deployed committed-conservation hole)
- **F1 HIGH — committed-mode cross-asset inflation (the twin of executor #1).** finalize.rs
  check_committed_conservation collects value commitments IGNORING the cleartext asset_type + runs one
  verify_conservation over commit(v,r). Spend asset-A note + create equal-value asset-B note → passes → cross-asset
  theft. The primitive SHIPS the fix (commit_hidden_asset/verify_asset_conservation); the wiring dropped the asset
  grouping. FIX (dispatched, finalize.rs): group committed legs by asset_type.
- F2 MED — OT malicious-model gaps sold as robust: receiver never validates A (a malicious sender learns the
  choice bit), is_small_order misses mixed-order, the KDF omits the (A,B) transcript. FIX (dispatched): torsion
  checks both sides + transcript binding + honest semi-honest disclosure.
- SOUND (confirmed): weak-Fiat-Shamir correctly AVOIDED (all sigma families bind the full statement), 64-bit range
  correct, NUMS generators, clean domain separation (20 labels), no blinding/nonce reuse. F3 DLog binding is the
  honestly-named Shor floor (live in the TCB, cutover named). F4/F5/F6 low (disclosed experimental / recipient-note
  comment drift / contributory-DH).

## captp / OBJECT-CAPABILITY (HAS-A-CAP-FORGERY/AMPLIFICATION HOLE)
- **F-1 HIGH — introducer impersonation on the LIVE classical path.** validate_handoff verifies the introducer sig
  against a WIRE-SUPPLIED introducer_pk never bound to cert.introducer → a presenter sets introducer=<trusted
  federation>, signs with their own key, impersonates it. The hybrid validator binds id↔pk; the wire calls the
  classical one. FIX (dispatched): bind pk to id / route through the hybrid.
- **F-2 MED-HIGH — Custom auth folded to 64 bits before the verified gate** (undermines the twin-deletion's
  non-amplification for the Custom dimension — the "injective fold" comment is false). FIX (dispatched): injective
  full-width Custom encoding.
- F-3/F-4/F-5 MED — publish discards SendCap.recipient + unauth subscribe (recipient-confinement break); unbounded
  unauth wait table (metadata oracle + DoS); no revocation of an issued live-ref. SOUND: token crypto, the
  AuthRequired lattice polarity, the fail-closed .unwrap_or(false) default (no fail-open).

## PERSISTENCE / DURABILITY (SOUND core + optional-path hole)
- SOUND: the finalized-turn store is ONE fsync'd redb txn (receipt+ledger+consensus-state+nullifiers welded),
  recovery with a fail-closed convergence gate, executor_consensus_state atomic rollback, redb 2-phase + checksums,
  WAL, PG-mirror non-trust posture.
- F1 HIGH but CONFINED to the optional pg-mirror-live feature (NOT default): direct-PG (receipt, ledger, nonce) not
  one txn + never finalized (a local fork). FIX: route PG through the consensus weld / don't ship as a write path.
- F2 MED (dispatched) — swallowed block-persist error → self-equivocation window (fail-closed persist). F3 (dispatched)
  — convergence gate skippable on read-error (fail-closed at non-zero cursor). F5 (dispatched) — unbounded
  receipt/realm logs → O(n) boot (compaction/MMR-head-skip). F4 solo-node rollback (documented, federation is the defense).

## METATHEORY-REBUILD IMPLICATION (ember's wholesome-regime direction)
The two conservation holes + the cap-tooth are DRIFTED RUST TWINS — Rust re-derivations of proven Lean gates, not
@[export] invocations. The immediate fixes WELD the Rust to the Lean (the Transfer guard = recTransferAsset; the
committed grouping = verify_asset_conservation). The DEEPER move: route per-asset conservation + the authorize
cap-tooth through the Lean @[export] (conservesFFI + stateStep/authorizedB), fail-closed, deleting the twin — so
these holes become STRUCTURALLY impossible, not patched. That is the top rebuild candidate the metatheory map is
scoping. See [[project-twin-deletion-campaign]], [[project-lean-must-be-the-implementation]].
