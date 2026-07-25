# Flaw-Hunt Backlog — 2026-07-22 (3 adversarial lanes, seeded by the overlay spawn_blocking bug)

The crowd-stream close bug (6d0e024f19: a Lean call from an unregistered spawn_blocking thread
silently refused the turn) was a CANARY. Three adversarial lanes hunted its class + the binding
surface + the turn-signing core. Verdict: the CORE IS SOUND (verify_strict malleability-closed;
every Lean-gate bridge fails CLOSED; no FFI ABI/arity mismatch; the game-spine head-check; monotone
signed counter; domain-separated seeds) — but there are real edges, and the dangerous ones are in
the NODE, not the frontends.

## 🔴 CLASS: Lean FFI from an UNREGISTERED thread — the overlay bug's ARMED twins in the node
Lean registers only the thread that first calls init (lean_initialize_thread; the ONLY correct
caller is orb/dataplane). A Lean call from a tokio spawn_blocking pool thread is unregistered →
under full-Lean it silently refuses/downgrades. The node is the binary that ARMS the reality-gate
(register_constraint_oracle only at node/src/lib.rs:617), so its spawn_blocking sites are live:
- CRIT node/src/blocklace_sync.rs:6680 — AUTHORITATIVE finalized-turn execution (produce_via_lean ->
  shadow_exec_full_forest_auth + the armed constraint oracle) on spawn_blocking. Overlay bug's twin
  on the COMMIT path. Full-Lean node would silently fail authoritative turns.
- CRIT :5617 — FNSP-v3 finalized-turn execute() (the global oracle fires inside execute() regardless
  of the Rust producer fence) on spawn_blocking.
- HIGH :1549 + :1708 — the VERIFIED finality/projection gates on spawn_blocking; a failing
  unregistered-thread call is timeout+mapped to None -> SILENTLY DOWNGRADES every finality decision
  to the unverified Rust order. The "verified" gate becomes DECORATIVE with no surfaced error.
- MED discord-bot spawn_blocking fleet (descent/offering/verify_chain/export_nft/proof_verify/
  tournament/dashboard/fiction) + off-thread PQ try_sign: LATENT — safe TODAY because the bot/web
  DON'T arm the Lean cores; become the CRIT class the instant a FULL-LEAN build arms one.
  >> DIRECT CONSEQUENCE: the full-Lean bot REDEPLOY would EXPOSE this class in the bot. The redeploy
     needs the class fix (or these sites on a registered thread) FIRST, not just a seed re-gen.
CLASS FIX (proposed): (1) a Lean-registered owner thread (orb's single-owner job-loop pattern; the
HostThread channel generalizes) for every service crossing a Lean seam; (2) expose
lean_initialize_thread + a thread-local "registered" flag, and make every shadow_* entry
debug-assert / hard-refuse-loudly when called off a registered thread — converting silent
refusal/downgrade into a visible, testable failure; (3) a grep-lint (spawn_blocking/thread::spawn
bodies reaching dregg_lean_ffi::/*_oracle/*_gate) in the full-Lean CI. TERRITORY: node + the FFI
layer = co-tenant/security-critical; FLAG + propose, do not unilaterally rewrite node execution.

## 🔴 A FRI SOUNDNESS GATE IS DARK — a binding deleted by an unrelated commit
circuit-prove/tests/{fri_params_soundness_budget,fri_regrid_post_s2_measure}.rs import
dregg_lean_ffi::{FriKnobs,FriLedger,fri_ledger,fri_ledger_available} — an API DELETED by commit
0f2802a0ca (titled "ML-KEM keygen now dispatches the VERIFIED core" — collateral, unrelated). Zero
definition sites remain; the Lean @[export] dregg_fri_ledger SURVIVES (orphaned). So
dregg-circuit-prove won't compile and the FRI-KNOB-DRIFT PIN GATE (deployed FRI knobs vs the
Lean-owned ledger — the sole guard against silent soundness-budget drift) is DARK. "Green hides a
red umbrella": the ML-KEM commit didn't rebuild the FRI-test crate. FIX: restore the fri_ledger
wrapper + FriKnobs/FriLedger + the dregg_fri_ledger_str C bridge + the build.rs probe/cfg from
0f2802a0ca^ (the Lean export is still live). TERRITORY: co-tenant FRI/felt-width -> FLAG.

CORRECTED + STILL OPEN 2026-07-25 (lane AC). Two corrections and one measurement.
(1) It was TWO commits, 17 hours apart, neither of which mentions FRI — so "restore from
0f2802a0ca^" recovers only half of it. 7ebe7b7d4b (07-20 05:08, "no-silent-fallback: two gates
make unaudited PQ substitution IMPOSSIBLE") rewrote dregg-lean-ffi/build.rs (476 lines) and
dropped the `dregg_fri_ledger` archive probe, its `cargo::rustc-check-cfg` declaration AND its
`cargo:rustc-cfg` emission; 0f2802a0ca (07-20 21:53) then deleted the Rust API and lean_init.c's
`dregg_fri_ledger_str` shim. Stage 1 alone had already stopped the gate working; stage 2 turned a
loud failure into an unresolved import that only a `--all-targets` build can see.
(2) The Lean side is confirmed live AND inside the FFI boundary closure: `@[export]
dregg_fri_ledger` (metatheory/Dregg2/Circuit/FriLedger.lean:380), imported by
metatheory/Dregg2/FFI.lean:31 — so the symbol IS in today's archive. Only the Rust half is gone.
(3) MEASURED, not assumed: no knob drifted while the gate was dark. All 7 shipped configs' deployed
consts still equal the Lean literals the test transcribes (IR2 6/19/16/3/0/4, PROD + ZK 3/38/16/3/0/4,
OUTER + GPU 3/38/16/1/0/4, RECURSION 3/38/14/1/0/4, INNER 19 queries / arity 1). That is a hand
reading with a shelf life, not a gate. The two targets are now enumerated in
`.github/dark-targets.txt`, so any THIRD target going dark is a CI failure rather than an annotation.

## 🟠 RESUME FORGES SIGNED PROVENANCE — a signed turn is NOT re-verifiable after restart  [FIXING]
LoggedMove persists (action, actor, 1-byte trust tag) but NO signature; decode_log maps "s" ->
Signed{pubkey=actor} straight from the store string; resume re-drives (action,actor) and adopts the
log verbatim, never re-verifying. Anyone who can write the unauthenticated FileResumeStore forges a
"verified-signer" turn no key ever signed. advance_signed's whole promise (actor = a verified KEY,
not a label) is FALSE for resumed turns. FIX IN PROGRESS (a fix-lane): persist pubkey/counter/
signature; re-run verify_signed on resume before honoring Signed; fail-closed on a Signed line whose
sig is absent/wrong; old lines stay Asserted. TERRITORY: mine (dreggnet-offerings).

## 🟡 MED provenance edges (turn-signing lane) — real, worth a pass
- Legacy advance_signed has NO epoch/incarnation in signing_message + close() forgets the floor ->
  reopen a caller-chosen same-id session after close/restart re-lands a captured counter=0 envelope.
  The GAME route is immune (GameSessionBinding + check_expected_head); the LEGACY signed route
  inherited none of it. FIX: bind a host-incarnation into signing_message (as the game spine does).
- Signed collapses CUSTODIAL (server signs as anyone via seed_for) and USER-HELD into one grade; a
  Signed receipt can't say which. FIX: carry Signed::Custodial vs Signed::UserHeld through log+receipt.
- No domain tag between asserted labels (blake3(user), 64-hex) and signed pubkeys (64-hex); executor
  gates on bare DreggIdentity. Web practically safe (needs a blake3 preimage). FIX: domain-tag the
  spaces or gate on Attribution not bare identity.
- LOW: "Verified turn" shown identically for asserted + signed (player_turn_receipt.rs); webauth PoP
  optional (documented bearer model, per-replica single-use).

## What PASSED (do not re-chase)
verify_strict rejects non-canonical S (malleability-closed); all ~18 Lean-gate string bridges are
fail-CLOSED with symmetric _present()/not() fallbacks and correct probe->cfg->export name chains;
no-copy direct FFI boundary arity/ABI all match (Int->boxed Obj handled); AgentRuntime churn SETTLED
(next_agent_turn_nonce + spawn_sub_agent_scoped_seeded defined, callers resolve); the reality-gate
Rust-twin fallback is fail-CLOSED (constraints still evaluated; the equivalence to the proven admits
is a labeled seam, not fail-open).
