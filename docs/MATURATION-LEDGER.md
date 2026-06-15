# The Maturation Ledger — toys to productionize

*A code-grounded census of where dregg ships scaffolding that needs to mature into its
full form. Synthesized 2026-06-15 from six parallel domain scans (proving/circuit ·
consensus/network · executor/data-plane · apps · surfaces/SDKs · desktop/deos/seL4),
each reading the cited lines (not grepping). Organized by **coherent theme**, not by
scanner, because the highest-leverage findings cluster.*

This is a *maturation* map, not a bug list: most entries are honestly-scaffolded
("named seam") code whose production form is known. The job is to drive each to its full
form, coherently — not to paper over it.

> Calibration discipline (the lamesauce lesson): a finding is only listed if a scanner
> READ the line. Severity is the main loop's, after checking whether the code is on a
> live path. Where "needs live-path verification" is noted, treat as a candidate, not a
> confirmed hole.

---

## THEME 1 — The privacy / confidential-value layer is demo-grade across the board

The single most coherent cluster: every surface that promises *privacy* (hidden amounts,
encrypted notes, selective disclosure) currently ships a labelled placeholder. Core turn
authorization is **Ed25519 and real** — this theme is strictly the privacy feature.

- **Schnorr value-commitment uses a placeholder curve** — `circuit/src/schnorr_curve.rs:41-100`:
  `CURVE_B=3, GENERATOR=(1,2)`, group order is composite `2013191319 = 3·331·2027383`
  (31-bit). The doc itself says "production MUST verify #E has prime order." Used by
  `cell/src/value_commitment.rs` (the Pedersen/Schnorr excess signature) and exported to
  `wasm/src/lib.rs`. **Live path = confidential value, NOT core auth** (turns are Ed25519).
  MATURE: Schoof/SEA over BabyBear^8 for a prime-order group; regen generator+order; audit
  scalar arithmetic. (~L)
- **The in-STARK Schnorr AIR is vacuous** — `circuit/src/schnorr_air.rs:182-198`:
  `verify_schnorr_via_trace` checks only `scalar_bit ∈ {0,1}` per row — no curve addition,
  no slope witness, no `s·G + e·pk == R`. Any bit-valid trace passes. (The off-AIR
  `schnorr_verify` does the real check; the *in-circuit* one does not.) MATURE: implement
  the missing constraints (trace already computes the values). (~M)
- **MCP `dregg_private_transfer` is a labelled fake** — `node/src/mcp.rs:4846-4874`:
  `encrypted_note: vec![]`, `value: 0`, `range_proof: None`. Produces a committed turn with
  ZERO ZK — amount not hidden, recipient can't decrypt, no spend path. MATURE: wire the real
  `committed_turn.rs` NoteCreate path. (~L)
- **SDK NoteCreate "encryption" is a placeholder** — `sdk/src/committed_turn.rs:206-210`:
  `encrypted_note = [recipient || nonce]`, not ECIES; recipient has no key to decrypt. The
  range proof + commitment math IS real; the encryption is not. MATURE: HPKE/ECIES to the
  recipient's X25519 stealth key (infra in `cipherclerk.rs`). (~M)
- **EncryptedTurn STARK validity proof is carried but never verified** —
  `turn/src/encrypted.rs:291,453`: `verify_metadata` says "does NOT verify the STARK proof";
  `proof_bytes` always empty; `InvalidValidityProof` is dead. The ordering path
  (`order_by_conflict.rs`) calls only `verify_metadata` → **a fee-DoS hole**: fake encrypted
  blobs consume ordering slots. MATURE: call the verifier on `proof_bytes` before
  `order_batch`. (~M, ~S for the fail-closed gate)
- **discord-bot selective disclosure returns a null proof** —
  `discord-bot/src/commands/identity.rs:302-308`: `cryptographic_proof: null`,
  "not implemented." MATURE: call the SDK's `prove_predicate_unlinkable` (circuit exists in
  `sdk/src/privacy.rs:413`). (~M)
- **Privacy module is Rust-SDK-only** — none of `authorize_anonymously / create_private_note
  / prove_predicate_unlinkable / prove_not_revoked` are bound in sdk-py / sdk-ts / CLI.

**Theme verdict:** the cryptographic *cores* (range proofs, commitment math, the
`prove_predicate_unlinkable` circuit) are largely real; the *wiring* (real encryption, real
in-circuit verification, prime-order curve, cross-SDK bindings) is the gap. One coherent
"make privacy real" campaign closes most of it.

---

## THEME 2 — The verified-Lean shadow path is lossy on the harder auth shapes

The executor's Lean inversion is structurally sound and well-fenced, but the wire-marshal
drops information for the non-trivial authorization shapes — so for those, the Lean kernel
sees a weaker turn than Rust does. Most are "root-gap" (Lean falls back to Rust, which still
enforces), but each is a place where the verified kernel is NOT yet the authority.

- **`DelegationMode::ParentsOwn` / `Inherit` — typed, EMITTED in production, silently neutered** —
  `turn/src/executor/execute_tree.rs:456` + collapsed to None at `execute_tree.rs:1031`; set
  by `eventual.rs` in every bilateral-schedule turn (`:514,1197,1314,…`). Callers can't tell
  "denied: parent lacks cap" from "denied: unimplemented." MATURE: implement the ParentsOwn
  chain-walk (like `walk_delegation_chain_for_capability`) OR remove the variant + fail-closed
  at the type. (~M) **[highest-leverage in this theme — it's live]**
- **`Refusal`'s `proof_witness_index` is discarded** — `turn/src/executor/apply.rs:1840`:
  `let _ = proof_witness_index;` — the non-action attestation's witness is never resolved, so
  any index passes. Both Rust and Lean admit Refusal with a fabricated/empty witness. MATURE:
  resolve `action.witness_blobs[index]`, reject on miss. (~M)
- **Marshal flattens the call-forest to a linear null-cap list** —
  `turn/src/lean_shadow.rs:1491` (`parent_cap: Cap::Null, keep: vec![]`): multi-level
  delegation turns lose the parent→child cap handoff before Lean sees them. MATURE:
  recursively build `WChild` from the real `CallTree` edges. (~L) (single-root turns unaffected)
- **Caveats are always `vec![]` on the wire** — `lean_shadow.rs:1491`: the Lean caveat gate
  trivially passes; caveats are not Lean-verified on the producer path. MATURE: add a caveats
  field to `CallTree::action` + marshal them. (~L)
- **Biscuit/macaroon caveat-discharges are dropped** — `dregg-lean-ffi/src/marshal.rs:343-354`:
  `auth_biscuit_issuer` / `auth_cell_macaroon` drop the `encoded`/`discharges` blobs (sig:0,
  proof:0); Lean checks the WHO-leg (issuer key) but not the caveat chain. MATURE: carry the
  discharge blobs across the wire. (~M)
- **Bearer-cap auth collapses to a u64** — `marshal.rs:304-310`: the full delegation sig
  becomes a bool+u64; Lean can't reproduce the Rust bearer-auth check. MATURE: carry the full
  sig bytes (hash to a Digest). (~M)
- **`marshal.rs` is `#[allow(dead_code)]` whole-module** — `marshal.rs:54`: a newly-added
  unreachable arm is never linted; conformance tests are the only enforcement.
- **No `TurnExecutor→WireState` extractor** — `marshal.rs:38` (self-labelled P0): callers must
  supply pre-state externally or get a stale-state admit (fail-open on stale pre-state). Today
  routed through `lean_shadow::build_pre_ledger`. MATURE: implement `Ledger→WireState`. (~M)

**Theme verdict:** the gap is "the Lean kernel is authoritative for the simple shapes and
falls back to Rust for the hard ones." Closing it = the verified kernel becomes the authority
for delegation/caveats/bearer too (the ARGUS direction).

---

## THEME 3 — The deos glass: authority is real, pixels & durability are not

"Boot it and it's real" needs four closures. The authority discipline (cap gates, membrane,
rehydration, deploy assurance) is genuinely implemented and tested; what's missing is the
output side.

- **servo `glow_gl_api` is `unimplemented!()`** — `servo-render/src/webview.rs:137`; the whole
  real-page render (`render_url_to_frame`) is gated behind `libservo`, behind the multi-GB
  mozjs/SpiderMonkey build. MATURE: wire glow over swgl + clear the mozjs build. (~M/L)
  (the cap-gated `WebViewDelegate` IS written; this is the last mile to real page pixels)
- **The seL4 executor-PD seat does no verified compute** — `sel4/dregg-pd/executor-stub/src/main.rs`:
  holds caps, writes `0xE0`, returns — no `execFullForestG`. MATURE: cross-compile the Lean
  runtime to `aarch64-sel4-microkit` + wire `dregg-lean-ffi`. (~L) (the embeddable-runtime
  spike already refuted the "blocker" — see EMBEDDABLE-LEAN-RUNTIME.md)
- **The persist-PD writes nothing durable** — `sel4/dregg-pd/persist-stub/src/main.rs`: reads
  the sentinel, acks, does nothing. MATURE: `redb` over a block cap. (~M)
- **The compositor framebuffer is a 256-byte authority witness** —
  `sel4/dregg-firmament/src/compositor_pd.rs:443`: `FRAMEBUFFER_TILES=256`, `Vec<u8>` one byte
  per tile — proves *which regions were admitted*, carries no pixels/scanout. MATURE: connect
  servo-render's `RgbaFrame` to real tiles + a scanned-out framebuffer. (~L, the F1/F2 frontier)
- **The deploy receipt is a zeroed shape** — `dregg-deploy/src/apply.rs:277`:
  `pre/post_state_hash, computrons, timestamp` all zero — the auditable chain is a skeleton,
  not a live receipt. MATURE: wire to a live executor response at submit. (~M)
- **Playground ring-trades / marketplace are pure-JS sims** —
  `site/playground/sections/{ring-trades,marketplace}.js`: the headline "atomic multi-party
  settlement" demos never touch the wasm executor (`_wasm` unused). MATURE: route through the
  in-memory runtime's `executeTurn`. (~M/L)
- **The Linux strictly-headless display seams** (just-landed Linux render works on a GPU
  session): Xvfb lacks DRI3 (no presentation); weston-headless has no `wl_seat` (gpui unwraps
  None → panic). gpui's own gaps, not starbridge's.

---

## THEME 4 — The apps silo: a clean ladder, not holes

Zero of 22 apps mount a `DeosApp` in shipped `src/`, but the *floors* are mostly real and
Lean-proven — the gap is a thin compositional skin. This is the crosswiring ember already has
a lane on.

- **Promote (one move away — green deos re-expression already in `tests/`):**
  `supply-chain-provenance` (507-line reexpress, 9/9 green), `subscription` (366-line, green,
  mislocated in app-framework/tests), `swarm-orchestration` (505-line reexpress).
- **The keystone:** `nameservice` — nothing in the web-of-cells is reacquirable *by name* until
  it stores a real sturdyref (today `RESOLVE_TARGET_SLOT` = `blake3(uri)`, not a reacquirable
  ref). Every other app's `DeosApp::announce` targets it.
- **Retire (dangling stubs, inventory-lying):** `gallery` (manifest-only, legacy path gone),
  `compute-exchange` (manifest-only, 8 P0s in deleted source), `demo-agent` examples
  (`AuthRequired::None` ×22, `Authorization::Unchecked`, println-as-proof — covered by the real
  deos apps).
- **One-reexpress-away (~S each):** bounty-board (the canonical 4-state cap∧state demo),
  privacy-voting, tool-access-delegation (+ fix `Immutable`→`WriteOnce` doc drift), sealed-auction
  (on-ledger commit board kills the in-process BTreeMap front-running), storage-gateway-mandate
  & compartment-workflow-mandate (also not mounted at node startup — DEVNET gap),
  governed-namespace, polis (wrap the proven core), agent-provenance.
- **Already good (don't touch):** escrow-market, identity, polis-core.

---

## THEME 5 — Surface completeness & SDK parity

- **CLI `cap export` emits a literal placeholder** — `cli/src/commands/cap.rs:88,113`:
  `placeholder-for-cli-export` / `dregg://local/…/placeholder-see-sdk-for-real-bearer`, printed
  as "Exported." Capability handoff from the shell is broken. MATURE: plumb `captp_client::export_cap`. (~M)
- **Predictable sturdyref nonce** — `sdk/src/names.rs:667` (`swiss: [0u8;32]`) — flagged by TWO
  scanners (surfaces + executor). A zero swiss is guessable/collides; the security of a sturdyref
  IS the unguessable swiss. MATURE: derive from CSRNG/HKDF(identity, cell, nonce). (~S) **[verify
  reachability from live export, then fix — small + security-relevant]**
- **MCP unrevokable caps + credential stub** — `node/src/mcp.rs:2169` (revocation registry not
  wired — caps die only by expiry) + `:7242` (credential proof defaults to
  `dregg-mcp-credential-stub-v1`). MATURE: wire `store.is_revoked` into `enforce_tool_cap`;
  require a real proof. (~S each)
- **TreeKEM is an `unimplemented!()` panic** — `sdk/src/channels.rs:362` — flagged by TWO
  scanners. Live path is `SenderKeys` (O(n) fan-out); TreeKEM is the named successor for groups
  >~5. MATURE: at minimum fail-closed (Result not panic); real impl = the MLS ratchet tree. (~L)
- **`SiloClient` has zero tests** — `sdk/src/client.rs:70` — flagged by TWO scanners; the primary
  TCP capability path (Welcome→Turn→Receipt) is untested. Directly affects the Pug handoff bar.
- **Parity gaps:** privacy / polis-governance-write / FlashWell-FlashRing exist ONLY in the Rust
  SDK; `TurnBuilder.reveal` and a clean light-client read surface are Rust-only. (Python/CLI/MCP blank.)
- **MCP intent epoch hardcoded `0`** — `sdk/src/cipherclerk.rs:6226`; encrypted intents carry a
  stale epoch. MATURE: thread the live network epoch. (~S)

---

## THEME 6 — Proving-stack "not-yet-real-recursion" + commit/fold correctness

- **IVC is a hash-chain, not in-circuit recursion** — `circuit/src/ivc.rs:30` +
  `plonky3_recursion.rs:1`: aggregates by hashing public inputs; `verify_recursive` still needs
  all N inner proofs (no O(1)). The REAL recursive fold (`ivc_turn_chain.rs`) exists and is
  tested. MATURE: redirect remaining `prove_ivc()` callers to the real fold; retire the hash-chain
  path. (~M)
- **`temporal_predicate_p3` is a hard `Err` stub** — `circuit/src/temporal_predicate_air.rs:55`;
  `Clone` panics. MATURE: port to the DSL temporal AIR. (~M/L)
- **commit/fold rule-prefix not enforced** — `circuit/src/commit/state.rs:155`
  (`is_rule_field_element` always false → `rules_only()` empty) + `commit/fold.rs:123` (accepts
  any non-zero predicate as rule-prefixed → a malicious fold can inject fabricated capabilities).
  MATURE: a tag bit / symbol-table lookup (fixes both). (~S/M)
- **cap-root revocation uses a zero padding leaf** — `circuit/src/cap_root.rs:478`; verify the
  non-amp AIR treats zero-leaf correctly (ARGUS linchpin). (~S, verify first)
- **EffectVm net-delta magnitude range-check deferred** — `circuit/src/effect_vm/air.rs:1593`:
  defended executor-side, not in-circuit. MATURE: the 15+15-bit decomposition (same shape as the
  implemented W9-RANGECHECK). (~S)

---

## THEME 7 — Consolidation debt (finish the cutovers)

- **C7-residue:** `perf/`, `tests/`, `demo/`, `preflight/` import deleted v1 symbols
  (`effect_vm::{EffectVmAir,generate_effect_vm_trace}`, `joint_turn_aggregation::{prove_joint_turn,…}`,
  `effect_vm_p3_full_air`) → `cargo check --workspace` is RED on these 4 crates (the node build is
  unaffected). The C7 cutover integrated the cone but left the non-cone test/bench/demo consumers.
  MATURE: rewire each to the rotated IR-v2 path, OR recursion-gate, OR retire dead legacy benches. (~M)
- **Deprecated-but-live `MerklePoseidon2StarkAir`** — `circuit/src/poseidon2_air.rs:347`; superseded
  by the DSL circuit, still reachable. MATURE: delete after confirming no callers. (~S)
- **`federation-mode` defaults to `solo`** — `node/src/main.rs:168`; a footgun (the N3 runbook passes
  `full` explicitly). + `solo_consensus.is_solo` can read true while n>1 → `/status` misreports the
  mode. MATURE: default to `full` when peers are configured; reconcile `is_solo` with the blocklace
  participant count. (~S)

---

## N=3 readiness (from the consensus scan — operational, not maturation)

The federation logic is implemented and correct. N=3 finalizes IF all 3 stay up AND all run
`--federation-mode full`. Watch: the 15s mesh-connect timeout (self-heals ~1 cadence), checkpoint-
bootstrap is a no-op (don't restart-fast-forward), `supermajority(3)=3` (zero fault tolerance —
expected). Judge by **height advancing**, not the `/status` mode string. These are tracked for the
live run, not maturation items.

---

## Recommended sequencing (main loop's read)

1. **Verify-then-fix the small security-relevant ones** (~S, high trust-impact): swiss-nonce,
   Refusal-witness, MCP revocation+credential-stub, commit/fold rule-prefix. Each is a bounded,
   real closure.
2. **One "make privacy real" campaign** (Theme 1) — the most coherent cluster; the cores are real,
   the wiring isn't.
3. **The apps ladder** (Theme 4) — promote 3, retire 3, ship nameservice — already has a lane.
4. **The Lean-shadow auth-shape closures** (Theme 2) — makes the verified kernel authoritative for
   delegation/caveats (ARGUS).
5. **The deos glass** (Theme 3) — the days-to-weeks servo + seL4 push.
6. **Finish the cutovers** (Theme 7) — green workspace for the tag.
