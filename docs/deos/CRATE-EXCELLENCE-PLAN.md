# Crate Excellence — the honest picture, the cross-cutting patterns, the standard, the plan

**Method:** careful-reading assessments (not grep, not `cargo metadata`, not a green check). Each reader
opened the accept path, ran probes where a claim was checkable, and recorded what the code does versus what
the code says it does.

**Scope of the evidence backing this report.** Six crates are read to completion or near it: `dregg-circuit`,
`dregg-circuit-prove`, `dregg-turn`, `dregg-cell`, `dregg-node`, `dregg-sdk` (partial — strengths only).
Together they are the core-protocol + verification spine and ~250k lines. Every finding below is anchored to a
file:line a reader actually opened. The patterns generalize *by construction* — they are the shape of how this
tree is written — but the per-crate table names only what is read. Nothing here is extrapolated to an unread
crate.

---

## 1. The honest picture

| grade | count | crates |
|---|---|---|
| excellent | **0** | — |
| good | **6** | circuit, circuit-prove, turn, cell, node, sdk |
| adequate | 0 | — |
| poor | 0 | — |

**Zero crates are excellent. The spine of the system grades `good`.** That is the finding, and softening it
would waste the reading.

`good` here is not a participation trophy — it means something specific and it means the same thing six times:

- The **architecture is right.** "Rust authors no constraints; Lean authors, Rust interprets" is a genuinely
  correct central abstraction, and `verify_vm_descriptor2` really does rebuild the AIRs from the descriptor
  alone. The prove/verify crate split is real and enforced (`cargo tree -p dregg-circuit` is recursion-free).
  The injected-verifier seams in `cell` really do fail closed. `TurnChainError` and `turn/src/error.rs` are
  error design other projects should steal.
- The **honesty apparatus is unusually strong** — strong enough that most of this report is written *out of the
  crates' own self-reports.* `effect_vm_descriptors.rs:20-27` pre-empts its own FP-tautology hole in its own
  words. `fri_params_soundness_budget.rs` states that the capacity conjecture is **refuted** and that its own
  gate is an engineering margin, not a proof. `producer_descriptor_coverage_gate.rs` tallies its own
  **43 Uncovered** rows and fails the build on an unclassified one. `lib.rs` in `cell` and `turn` open by
  declaring themselves LEGACY and not the source of truth. This is the iterative/approximative method working.
- And the **gap between the two is where excellence is lost.** The ledgers name real holes that nobody burns
  down. The teeth are written and then never armed. The deep modules are scrupulous and the front doors are
  stale. The apparatus that finds the gap is better than the discipline that closes it.

Three findings are not "gaps" — they are live defects, and they are stated first because grade-averaging hides
them:

1. **`cell/src/program/eval.rs:2557` is a wire-reachable panic.** `SimpleStateConstraint::Not(Not(c))` panics in
   `lift_simple`. The reader *proved* it with three probes: direct eval panics; a 42-byte postcard payload
   decodes clean and *then* panics (so an attacker-supplied cell program remotely crashes any node that
   evaluates it); and the public safe builder `implies()` constructs the panicking shape with **no adversary at
   all**. 30+ crates depend on `dregg-cell`. This is a node-crash DoS.
2. **`turn/src/verify.rs:245` `verify_receipt_chain_with_keys` is fail-open.** It verifies signatures only on
   receipts that have them (`if let Some(ref sig_bytes)`). Strip the signature; the chain still verifies under
   the function whose name promises key-checking. No test catches this because it would not fail. This is the
   federation-exit path `lightclient/`, `wire/` and the seL4 verifier PD sit on.
3. **`cell`'s `test-stubs` firewall is defeated by the workspace's own build graph.** `tests/Cargo.toml:38`
   enables `dregg-cell/test-stubs` as a **normal** `[dependencies]` entry, and `dregg-tests` is in both
   `members` and `default-members`. Verified empirically: `cargo tree -p dregg-node -p dregg-tests -e features
   -i dregg-cell` prints `feature "test-stubs"`. A root `cargo build --release` arms `StubVerifier`'s
   accept-anything path inside the production node binary. Only reachable if a host calls `with_stubs()`, so it
   is a defeated defense-in-depth layer rather than a live forge — but `cell/Cargo.toml`'s stated guarantee
   ("production builds never set it", "structurally impossible") **is false as packaged.**

One more, on the record: **`cell/tests/offchain_root_forge_closed.rs` is RED at HEAD.** 2 of 3 tests fail their
setup precondition — the pinned birthday-search collision constants went stale when `compute_heap_root` /
`compute_fields_root` changed underneath them. The crate's gold-standard adversarial test (real collision pairs,
proving the wide 8-felt encoding separates states the old lane-0 projection collided) is providing zero
protection on the heap and fields planes right now.

---

## 2. ⚑ THE CROSS-CUTTING PATTERNS

This is the product. These are not six crates' six problems; they are one body's habits, showing up six times.

### ⚑ P1 — The tooth that cannot bite (the dominant pattern)

We write negative tests prolifically and adversarially-*named*. A large fraction of them cannot fail for the
reason they claim. Four distinct mechanisms, all live:

**(a) Structural presence standing in for behaviour.** The test asserts a gate-*shaped* subtree is in the
constraint list, not that the interpreter enforces it.
`cap_delegation_nonamp_descriptor.rs::genuine_nonamp_carries_anti_amplify_teeth` pattern-matches the descriptor
AST for `Mul(Var(granted), Add(Const(1), Mul(Const(-1), Var(held))))` on each of 8 mask bits. No amplifying
witness is ever constructed; no prover is ever asked to refuse one. The doc claims "the interpreted circuit
ENFORCES `granted ⊑ held` bitwise — on every delegation effect." The behavioural twin exists 200 lines away
(`ir2_amplified_submask_refuses`) and is exactly what is missing here.

**(b) The undiscriminating reject.** `match catch_unwind(..) { Err(_) => {}, Ok(Err(_)) => {}, Ok(Ok(_)) =>
panic!("...is OPEN") }` — **any** panic or **any** error counts as a correct refusal. **36 sites in `circuit`**
(`descriptor_ir2.rs:6333, 6362, 6502, 6565, 6658, 6738, 6823`, …), **161 sites in `circuit-prove`**. A stray
`.unwrap()` introduced in trace assembly keeps every one of them green while proving nothing about the
constraint system. A tooth that cannot distinguish *"rejected the forgery"* from *"crashed"* is measuring the
wrong thing.

**(c) The fallback IS the expected answer.** `node/src/coord_gate.rs:150` —
`lean_gate_decides_unanimous_scenarios`, the **only** test of the verified 2PC gate — calls
`authoritative_decision(Decision::Commit, Some("y=3;n=0;N=3;t=3"))` and asserts `Commit`. The function's `Err`
branch returns `rust_decision`, i.e. the value passed in. The test passes identically whether
`verified_2pc_decide` works, is broken, returns garbage, or is **absent**. The differential is defeated because
the fallback is the assertion. Its sibling `falls_back_to_rust_when_no_wire` asserts `f(x, None) == x` where the
function's second statement is `let Some(wire) = wire else { return rust_decision; }` — literal P → P.

**(d) The tooth that is written, adversarial, correct — and never runs.** All 8 `*_binding_deployed_tooth.rs`
files in `circuit-prove` are `#[ignore]`-gated (17 of 24 tests; custom/hatchery/membership/sovereign are **100%
ignored**). CI runs `cargo test --workspace` (`ci.yml:55`), which never runs ignored tests. Nothing in
`.github/workflows/` or `scripts/test-gauntlet.sh` passes `--ignored` — verified. In `node`, every load-bearing
verified-gate test self-skips on an archive-less build (`finality_gate.rs:313/413/506/634`, `coord_gate.rs:153`,
`finalization_votes.rs:929`, `tests/lean_producer_mode.rs:202/223/244` all `eprintln!("SKIP"); return`), and no
scheduled job sets a hard mode. `consensus_under_failure.rs` is `#[ignore]` *and* launches every node with
`DREGG_LEAN_PRODUCER=0`, so the verified producer — documented as THE SWAP, on by default in production — is
never exercised under real cross-node fault injection.

> **"Expensive" must mean "runs nightly", not "runs never."** These teeth are minutes-long real recursion
> folds; they belong on the gauntlet box. Today they are documentation.

**(e) The identity gate.** `node/src/blocklace_sync.rs:1000` calls
`admitted_participants(&raw_participants, &raw_participants)` — seeds == candidates, and `AdmissionRegistry`
admits every seed by construction. The F-4 strand-admission filter **provably cannot drop anything.**
`vouch_threshold=1` and `min_bond=1` are inert (the module doc concedes "no vouches/bonds fed"). The divergence
warning at `:1004-1011` is unreachable dead code. Its test (`strand_admission_gate.rs:127`) passes
`candidates ⊋ participants` — a configuration the live call site never produces. It tests a code path that does
not exist in production, and it is labelled "the live F-4 closure."

**Why P1 is the top pattern:** each mechanism produces a green suite, a confident doc-comment, and zero
assurance. And they compound — (b) exists partly *because* (P3) the error surface is stringly-typed, so a test
literally **cannot** assert *why* a reject fired.

### ⚑ P2 — The name that outlives its referent (front-door inversion)

**The deepest modules are the most honest and the most-read text is the least accurate.** This is an inversion,
and it is systematic.

- `circuit/src/lib.rs:33` — the Trust Model, the first paragraph any auditor reads — claims "negligible
  soundness error (2^{-128} for STARK)". The crate's **own gate** says capacity 130 is refuted (Crites–Stewart,
  eprint 2025/2046, disprove the conjecture by reduction; Kambiré, arXiv 2604.09724, gives a prime-field
  counterexample) and the standing columns are per-fold 109 at the deployed arity 8 (~112.6 is the arity-2
  figure, and both are claims at 96.9% farness, not at the Johnson radius FRI operates at) / Johnson QUERY
  column 73 / commit-phase `ε_C` 71, composing under ethSTARK eq. (20) to ~70. The honest text already exists
  at `descriptor_ir2.rs:5416-5425`; it just never reached the top of the file. Same header: a documented `mock`
  feature that **does not exist** in Cargo.toml, and three intra-doc links to a `stark` module that **does not
  exist**.
- `circuit-prove/src/custom_proof_bind.rs` — a 51-line module doc describing `verify_proof_bind` in present
  tense with a rustdoc link and a `## The soundness property` section. `grep -rn 'fn verify_proof_bind' .`
  matches **nothing**; it was deleted in `dd038c08e`. The stale claim propagated to **5 sites** that mislead
  readers about the live architecture (`turn/src/turn.rs:554`, `turn/src/executor/proof_verify.rs:238`,
  `joint_turn_aggregation.rs:587`, `custom_leaf_adapter.rs:983`, `sdk/tests/wide_completeness_ledger.rs:341`).
  `sdk/tests/wide_completeness_ledger.rs:1239` documents the stark-kill **correctly** — the true state is known
  and was simply never propagated back to the module that owns the name.
- `cell/src/program/types.rs:594` — the canonical case, because **the false doc caused the bug.** It states
  "Double-negation: `Not(Not(c))` is *not* representable because the inner is unboxed... the type system shapes
  against it." The declaration on the very next line is `Not(Box<SimpleStateConstraint>)` — the stated reason is
  exactly what *makes* it representable. The reasoning is backwards, the belief suppressed the test, and the
  panic shipped.
- `turn/src/executor/mod.rs:938-945` and `:1315-1319` claim `require_validity_proof` is "FAIL-CLOSED... rejects
  EVERY encrypted turn". **Falsified by the crate's own passing test** (`tests.rs:9515`
  `encrypted_turn_accepts_authenticated_when_gated`). `verify.rs:259-261` says the executor signs "the canonical
  narrow message... not the full `receipt_hash()`" — v3 signs exactly the full `receipt_hash`. An operator reads
  these docs to choose a security posture.
- `cap_delegation_nonamp_descriptor.rs:35` — "The sdk authority-binding routes cap-graph rows to it by name."
  **False.** Grepping the workspace for the routed name returns zero hits outside the defining module. Both cap
  descriptors are dead code, `lib.rs:165-181` calls them "the ARGUS linchpin", and **the good descriptor is dead
  while the opaque-digest one is deployed.**
- `cell/src/predicate.rs:849-855` — `with_stubs()` claims each stub accepts "only when the proof bytes are not
  empty AND have the kind's documented length-prefix shape." The code (`:1411-1420`) performs **no shape check
  whatsoever.** On the exact type whose accept path is the soundness gate.
- Names that lie by themselves: `turn/src/encrypted.rs:409` **`verify_stark()` verifies no STARK** — it checks
  an Ed25519 signature and an agent binding. The type is `TurnValidityProof`; the field is `proof_bytes`. The
  unnamed consequence: `conflict_set` is submitter-declared, unverified, and drives `order_encrypted_turns`, so
  a malicious submitter can declare a false conflict set, influence ordering, and pass `verify_stark`.
  `ProofBindError` is a `pub enum` with 5 variants, a hand-written `Display`, an `Error` impl, and **zero
  construction sites** — while two live doc-comments cite `ProofBindError::UnknownProgram` as a fail-closed
  mechanism that fires.

**The signature of P2:** the code was fixed, refactored, or superseded, and the *name* stayed. Nothing enforces
that a deleted item cannot be documented as live, so the doc becomes the last surviving witness to an
architecture that no longer exists.

### ⚑ P3 — Stringly-typed boundaries, and fail-open at the seams

**The numbers:** `circuit` — **181** `Result<_, String>` vs **9** typed error enums, and all 9 live in
peripheral modules (xmss, block_conservation, …) while `verify_vm_descriptor2` / `parse_vm_descriptor2` /
`prove_vm_descriptor2` all return `Result<(), String>`. `circuit-prove` — **140** vs 74, the entire leaf-adapter
layer and all of `gpu_backend`. `node/src/api.rs` — bare axum `StatusCode` across ~100 endpoints;
`.map_err(|_| StatusCode::BAD_REQUEST)` discards the cause entirely, so the client gets an empty 400 *and the
node loses the error for its own logs.*

**The cost is not aesthetic, it is threefold:**

1. **A consumer cannot separate a deploy bug from an adversary.** `lightclient/` gets an opaque `String` for both
   "the descriptor is malformed" (page someone) and "the proof is invalid" (quietly reject). These are opposite
   operational responses.
2. **The good error design is swallowed from below.** `TurnChainError` is excellent — 10 fail-closed variants,
   each naming the adversary it stops (`ChainBreak{index, expected_old_root, found_old_root}`,
   `MissingWideAnchor{index}`, `VkFingerprintMismatch`). Then it re-swallows the layer beneath into
   `RecursionFailed{reason: String}`. So the security-relevant distinction — **`BindingUnsat` (the connect
   conflicted: a forged claim, the tooth firing)** vs **`ProverFailed` (FRI/OOM/shape: an operational fault)** —
   is destroyed at exactly the boundary that needs it.
3. **It is the upstream cause of P1(b).** You cannot write `assert!(matches!(e, LeafError::BindingUnsat{..}))`
   when the variant does not exist. So 197 reject sites settle for `Err(_) => {}`.

**And the seams default open:**
- `node`'s `coord_gate` / `finality_gate` / `strand_admission` all **fall back to the unverified Rust sibling**
  when the archive lacks the export, distinguished only by log level — `coord_gate` logs its fallback at
  `debug!` "to avoid spamming a fallback build". A node silently running three unverified gates is one missing
  symbol away, and the loudest signal for the 2PC gate is a debug line.
- `circuit-prove/tests/gpu_babybear_merkle_e2e.rs:59` and `:169` — `let Some(gpu) = require_gpu() else {
  eprintln!("no GPU adapter — skipping"); return; }`. Reports **`ok`** having verified nothing, while its module
  doc declares "PARITY IS LOAD-BEARING... a fast wrong tree is worthless. Parity is asserted before any timing is
  reported." The crate's own correct pattern is 40 lines away (`gpu_backend.rs:4624` asserts `adapter_available()`
  **and** that the GPU path was taken, so it cannot degenerate into a CPU-vs-CPU tautology).
- `node/src/api.rs:4453/4510` — `let _ = s.store.set_config("passphrase_hash", ...)` under a comment reading
  "Persist... so they survive restarts." A failed write returns `success: true`; the node reboots with no
  passphrase and the next loopback caller sets a fresh one.
- `turn`'s `LedgerJournal::rollback` is infallible and best-effort: it swallows every missing cell
  (`if let Some(c) = ledger.get_mut(&cell)`), panics on a poisoned mutex (`verify.rs:515-524`), and panics on a
  violated fixed-slot invariant (`:433`) — **inside the path whose entire job is recovering from failure.**
  Atomicity is the crate's central claim and its recovery path is its least defended code.

### P4 — The abstraction exists in the domain and not in the type system

`circuit-prove`: **zero traits in 37,543 lines** (`grep -rn '^pub trait|^trait ' src/` → nothing). Yet ~20
`*_leaf_adapter` modules implement a manifestly uniform contract — `prove_X_leaf(witness, pis, config) ->
Result<RecursionOutput<..>, String>` plus `prove_X_leaf_with_claim` exposing an `X_CLAIM_LEN`-felt claim the
binding node `connect`s. `membership_leaf_adapter.rs:197` and `presentation_leaf_adapter.rs:178` differ only in
error strings. `lib.rs` is 43 flat `pub mod` and exactly **one** `pub use` — no facade, no seam.

**The direct, measurable cost is ragged validation.** Counting `public_inputs.len() !=` per adapter:
sovereign/membership/hatchery/factory/caveat_admission/bridge validate **both** entry points;
zkoracle/solvency/shielded_spend/note_spend/deco validate **one of two**; presentation/dsl/custom/
blinded_membership validate **neither**. `prove_membership_leaf` opens with an explicit length check;
`prove_presentation_leaf` passes the slice straight to the prover. It is fail-closed **by accident** (a wrong
length dies deeper in `prove_vm_descriptor2_for_config`) — fail-closed at the wrong layer, surfacing an opaque
deep string instead of a clean boundary error, inconsistent for no stated reason. Adding a leaf is ~500 lines of
copy-paste the compiler checks nothing about.

The same shape in `cell`: the Not-depth invariant is enforced **nowhere** — not by the type, not by a validation
pass (there is no `fn validate` anywhere in `src/program/`), not by a smart constructor. `Not(Box<..>)` is a
public tuple variant. The invariant lives only in a comment, and the comment is false.

**Contrast — the pattern done right, in this same tree:** `sdk`'s `raw` module seal. `Authorization::Unchecked`
is spelled in exactly ONE constructor (`raw::unsigned_action`), quarantined behind a module whose docs enumerate
the three sanctioned uses, and deliberately omitted from the root re-export. `TurnBuilder` holds `effects`
private and `sign()` is the only exit. **On the headline surface an unauthorized act is inexpressible.** That is
what P4 asks for everywhere else. The minted `handler-floors` pattern (a forgotten gate is a *type error*) is
the same idea and it is already ours.

### P5 — The god object, and its receipt

`NodeStateInner` is **127 pub fields behind one `Arc<RwLock>`** — cipherclerk, ledger, store, coord budgets,
routing table, prove pool, accumulators, gossip handle, committee history. **The architecture already handed us
the receipt:** the crate's own comment documents the live n=4 stall, where `poll_finalized_blocks` had to
snapshot-and-clone the whole lace because holding `lace.read()` across the O(history) FFI starved the block
producer's `lace.write()` and froze `dag_height`. The clone is a workaround; the lock granularity is the bug.

`turn`: 68k lines, 50+ top-level `pub mod`. `economics.rs` (EpochMinter), `fast_path.rs` (lock tables),
`aggregate_bilateral_prover.rs` (2,070 lines of prover), `reactive.rs`, `umem.rs` (2,656) are things a
call-forest transaction model *depends on or emits*, not things it **is**. `executor/` alone is 21k across 11
files, `apply.rs` at 4,610. `src/tests.rs` is **11,998 lines** — the largest file in the crate by 2.5×, and it
compiles into the crate. The Cargo.toml shows real thought about the verify/prover split (the recursion-free
wasm/seL4 floor), but that discipline is expressed **in features, not in module boundaries.**

Nothing here is *wrong*. The abstraction boundary has simply not been paid for. **And it is deliberately the
lowest-priority pattern** — see §4.

### P6 — The self-report is better than the burndown

Our best apparatus produces ledgers nobody drains:
- **43 Uncovered** producer-equals-descriptor rows (32 Covered / 8 Partial / 43 Uncovered). Roughly **half** of
  deployed descriptor members have no prove+verify roundtrip against the registry descriptor they ship under —
  on the V3-live registry, which is what a light client verifies against **today**. This is the exact class that
  already bit once: the gate's own header cites `be732a9dd`, where 7 wide members laid their AFTER carrier chain
  at a stale base and verify failed on **honest** turns — "a class the drift gate CANNOT see."
- The FRI gate covers **3 of 5** deployed knobs. `IR2_FRI_MAX_LOG_ARITY` and `IR2_FRI_LOG_FINAL_POLY_LEN` are
  ungated and can drift silently — and the surviving ~112.6-bit bound is explicitly **structure-specific** ("the
  deployed dim-2 constant-fold recursion code", "at our fixed r = 2, n = 64"). So the only numeric gate enforces
  a margin on the arithmetic the same file calls **refuted**, and enforces **nothing** on the structural
  parameters the surviving bound actually depends on.
- Two authority traits (`IssuerRootAuthority`, `FinalizedRootAuthority`) have **no production implementation
  anywhere in the tree** — only cell's own in-memory `Static*` doubles. Their rustdocs say "Production hosts that
  read issuer roots from on-chain slots install their own authority." No such host exists. So BlindedSet
  membership and ObservedFieldEquals are fail-closed-in-practice, i.e. non-functional. Honest and safe — but the
  docs imply a built path that is not built.
- `node/src/turn_proving.rs:3-4` opens "This module makes the public claim — every committed state transition is
  proven — TRUE for the running node." Seventy lines later the honest capacity note concedes that beyond 14
  nullifiers (`TREE_DEPTH=4`) the spend turn commits with **no freshness-bound proof**. The headline is not
  qualified where it is made; the caveat is downstream of it.

**The named-seam law is satisfied and the closure lane is not running.** A named seam is not a hole — but a seam
named 3 months ago with no lane is drifting toward one.

### P7 — Diagnostics registered as tests

`circuit-prove/src/gpu_backend.rs:4544` `dump_hash_wgsl` — a `#[test]` with **zero assertions** that writes
generated WGSL to a hardcoded `/tmp/hash.wgsl` on **every CI run** and eprintlns. `:4555` `compile_wgsl_from_env`
— `let Ok(file) = std::env::var("WGSL_FILE") else { eprintln!("skipping"); return; }`; WGSL_FILE is unset in CI,
so it always trivially passes without executing its body. Both are honestly comment-labelled DIAGNOSTIC (they
bisect a live RADV compiler SIGSEGV) — so the intent is clean — but they are `#[test]`, so they inflate the count
and report `ok` while proving nothing. They are debug tools.

Relatedly: `gpu_backend.rs` contains **zero** `#[ignore]` attributes, yet three of its tests assert
`adapter_available()` unconditionally. Under `cargo test --workspace` these hard-fail on any GPU-less runner —
or pass **hollowly** against lavapipe/SwiftShader, measuring nothing they claim to measure. The suite's red/green
is a function of undeclared host hardware. The GPU lane is neither honestly skipped nor honestly required.

### What we do NOT have (recorded so it is not re-litigated)

Readers hunted specifically for these and found **zero** hits:
- `assert!(true)`, `assert_eq!(1,1)`, P → P shapes, mock-testing-the-mock across `circuit`'s src/ and tests/.
- `todo!()` / `unimplemented!()` in 37.5k lines of `circuit-prove`; **zero** `todo!`/`unimplemented!`/`FIXME` in
  the whole of `cell`.
- Unlabelled placeholders. Every placeholder found is labelled, and several are labelled *better than the
  standard asks*: `shielded_ring_clearing_air.rs:106` names its endpoint boundary and states exactly what it
  cannot do ("cannot by itself instantiate `ShieldedRingDescriptorRefines`... the N-leg generalization is named
  not built"). `journal.rs:122-129` carries "NAMED SEAM (UMEM-PRIMITIVE §2, Stage A)". `shadow.rs:86-96` names
  the verified kernel's fixed placeholder fee cells and exactly why the reconstituted ledger diverges.
  `NotYetWiredVerifier` names the **exact missing upstream module per kind** so an operator can diagnose which
  wiring they forgot. `node`'s crypto-core installs carry an explicit ⚠ HONEST SCOPE block admitting the ML-DSA
  **sign** install wires only the scalar core and does **not** remove fips204 from the sign TCB — the opposite
  of laundering.

**Read that carefully: `unlabelled placeholders` is not one of our patterns.** Our vacuity is never a fake
assertion and never a dressed-up stub. It is **structural presence standing in for behaviour**, and **a name
outliving its referent**. Those are subtler and they survive code review, which is why they are the top two
patterns and why the standard below targets them specifically.

---

## 3. ⚑ THE STANDARD — what EXCELLENT means for a dregg crate

Hold a crate against these. Each gate is checkable, has a stated falsifier, and names the real anti-pattern it
exists to kill. **A crate is EXCELLENT when all nine pass. `good` is any crate that gets the architecture right
and fails some of them — which is currently all of them.**

### S1 — Every load-bearing tooth has an adversary, and the adversary is *constructed*

- For each security claim, a test **builds a specific forged witness** and requires refusal.
- It **re-asserts the honest pole first**: `assert!(!rejects(&desc, &trace, &pis), "honest witness must be
  accepted — else the canary is vacuous")` **before** asserting the tampered reject. This is not optional; it is
  the thing that makes the negative non-vacuous.
- It asserts **why** it rejected — `assert!(matches!(e, LeafError::BindingUnsat{..}))` — not that something went
  wrong.
- ✗ Fails if: the test pattern-matches an AST for gate *presence* (P1a); accepts any `Err(_)` or any panic
  (P1b); asserts a value the fallback path also returns (P1c); passes an input shape the live call site cannot
  produce (P1e); asserts `HashSet::contains` on a hand-constructed struct (this tests the standard library).
- ✓ **Reference implementations, in-tree:** `ir2_amplified_submask_refuses`;
  `every_forged_commitment_lane_is_rejected_by_the_fold` (forges each of 8 lanes **independently**, `k in 0..8`
  — which is precisely what makes the second squeeze block load-bearing, because a node binding only the first 4
  would accept `k in 4..8`); the whole `*_emit_gate` canary family;
  `cap_witness_path_not_reaching_prestate_root_is_rejected`;
  `signature_rejects_tampered_{was_encrypted,effects_hash,finality,computrons}`;
  `proptest_receipt_chain_integrity` (removes each interior receipt and requires failure, plus a swap-breaks
  companion).

### S2 — Every tooth bites in automation, on a named schedule

- No load-bearing test is `#[ignore]`d without a **scheduled lane that runs it** (`--ignored` on the
  gauntlet/nightly box). "Expensive" means "runs nightly", never "runs never".
- No test silently skips. A skip is either an **explicit honest skip** (`#[ignore]`, so the runner reports it as
  skipped) or a **hard requirement** (`assert!(adapter_available())`). Never `eprintln!("skipping"); return;`
  inside a running test — a green that means nothing is worse than a red.
- Environment-conditional behaviour is **declared**, and a hard mode exists that turns every skip into a panic
  (`DREGG_TEST_REQUIRE_LEAN=1`, mirroring the `DREGG_REQUIRE_LEAN` build gate that already exists).
- ✗ Fails if: the crate's central claim is asserted only by tests no scheduled job executes; the suite's
  red/green depends on undeclared host hardware; a fault-injection lane disables the production default it is
  supposed to exercise (`DREGG_LEAN_PRODUCER=0`).

### S3 — Errors are typed at every boundary a consumer crosses

- Public entry points return an **enum**, not `String`. The mandatory distinction: **an adversary** (reject
  quietly — `ProofInvalid`, `BindingUnsat`) vs **a deploy/operational fault** (page someone —
  `MalformedDescriptor`, `TableShapeMismatch`, `ProverFailed`). A consumer that cannot separate these cannot
  operate.
- Variants carry **structured triage payload**, not a formatted sentence.
- A typed error at the top **must not swallow a stringly layer beneath it**. `RecursionFailed{reason: String}`
  under a 10-variant enum is the enum failing.
- No `panic!`/`unwrap`/`expect` on any path reachable from decoded wire bytes or from a public API taking
  untrusted input. Prover-side can't-happens still return `Result` (`fill_chip_lanes`).
- ✓ **Reference implementations, in-tree:** `TurnChainError` — 10 variants, each fail-closed with diagnostic
  payload, each doc-comment **naming the adversary it stops**; `turn/src/error.rs` — ~90 typed variants,
  stranger-legible `Display`, and a `refusal_class()` projection for security counters that depends on no metrics
  facade. `DelegationModeUnimplemented` is deliberately distinct from `DelegationDenied` so a caller can tell
  "mode confers nothing" from "authority was evaluated and found wanting." **That is design, not enum-padding —
  it is the bar.**

### S4 — Fail-closed is structural, and fail-open is in the *name*

- The default is refusal. A missing verifier, a missing archive symbol, an absent signature → **reject**.
- If a lenient variant must exist, the leniency is in the identifier: `verify_receipt_chain_with_optional_keys`,
  not `..._with_keys`. The strict variant exists and is the one the exit path calls.
- A degraded gate is **loud**. Falling back to an unverified sibling is `error!`/`warn!`, never `debug!`.
- A feature that arms a permissive path is **structurally unable** to reach a production build — enforced by
  `compile_error!` and a pinned `cargo tree` assertion in CI, not by a Cargo.toml comment.
- ✓ **Reference implementation, in-tree:** `CredentialSetMembershipVerifier` holds two independent
  `Option<Arc<dyn ..>>` and rejects unless **both** are installed; the `with_adjacency` rustdoc correctly states
  it *still* fails closed on the issuer-root step. The gate rejects; it does not merely claim to.
  Also: `canonical_revocation_root_for_set` returns `Err(RevocationCapacityExceeded)` rather than silently
  truncating past `TREE_DEPTH` — **explicitly choosing to lose the proof rather than lose soundness.**

### S5 — Docs claim exactly what the code does — checked at the front door first

- **The front door is audited first, not last.** `lib.rs:1-110` and every module header is the most-read text in
  the crate and must be the most accurate. Today the ordering is inverted.
- Every number in a doc is **derived from the code that computes it** or is pinned by a test. A soundness figure
  that contradicts the crate's own gate is a defect of the same severity as a wrong constraint.
- Every named function/type in a doc **exists**. `#![deny(rustdoc::broken_intra_doc_links)]` is on, so a deleted
  item can never again be documented as live.
- A function's name states what it verifies. `verify_stark` verifies a STARK or it is renamed.
- **When a claim is deleted from the code, it is deleted from every doc that cites it** — grep the workspace for
  the name, not just the module.
- ✗ Fails if: a doc's stated *reasoning* is backwards (`types.rs:594`); a doc describes a plan that already
  landed or an engine that was deleted; a rustdoc claims a check (`length-prefix shape`) the body does not
  perform; a headline claim is qualified 70 lines downstream of where it is made.

### S6 — The abstraction is in the type system, not in the copy-paste

- If N modules share a shape, that shape is a **trait with provided methods**, and the validation every instance
  needs happens **once, in the trait, for everyone**.
- A forgotten gate is a **type error**, not a code-review miss (the minted `handler-floors` pattern).
- An invariant stated in a comment is enforced by a type, a smart constructor, or a validation pass. **A comment
  is not an enforcement mechanism** — and `cell`'s `Not(Not)` panic is the proof: the comment was not just
  unenforcing, it was *false*, and the belief it created suppressed the test that would have caught it.
- The public surface makes the wrong thing **inexpressible** rather than merely discouraged.
- ✓ **Reference implementation, in-tree:** `sdk`'s `raw` module seal (see P4).

### S7 — Placeholders are labelled with their *resolution*, not just their existence

We already pass this. Hold the line:
- Every placeholder names **what it is**, **what it cannot do**, **the exact missing upstream**, and **the lane
  that closes it** — and per standing practice that lane enters HORIZONLOG in the same breath.
- Honest scope blocks state what a change **does not** buy (the ML-DSA sign install's ⚠ HONEST SCOPE).
- A conditional proof of an architecture over a labelled placeholder floor **is real work** and is framed as
  scheduled sharpening on a chosen trajectory — never as a defect.
- ✗ Fails if: the label is accurate but its lane has not run in months (P6 — a named seam with no lane is
  drifting toward a hole); a rustdoc implies a production path ("production hosts install their own authority")
  that is not built anywhere in the tree.

### S8 — Every floor is stated at its real resolution, and someone has tried to prove it false

- Security figures are stated **per column, each labeled with what it is a claim about** — never as one
  headline: `per-fold 109` at the deployed arity 8 (`~112.6` is arity 2; both at 96.9% farness, not the
  operating Johnson radius) / `73` Johnson QUERY column (the `m → ∞` idealisation, which DROPS BCIKS20's
  `ε_C`) / `71` commit-phase `ε_C` at the `2^12` fixture (it BINDS) / `~70` the ethSTARK eq. (20) composite /
  `130` refuted-capacity drift baseline. Stated at the front door, not only in the gate.
- Every knob the bound depends on is **pinned by a gate**. If the surviving bound is structure-specific (dim-2
  constant-fold, r=2, n=64), the **structural** knobs are gated, not just the arithmetic ones.
- The non-vacuity test for a gate **perturbs the deployed constants and requires a red** — it does not evaluate
  the formula on a synthetic point. (`budget_gate_reds_a_degraded_config` asserts `conjectured_bits(1,20,0) <
  128`, i.e. that 20 < 128. It never invokes the gate it is named for, and would pass if that gate's `assert!`
  were **deleted outright**. Ironic in the crate's best file on floor honesty.)
- ✓ **Reference implementation, in-tree:** `fri_params_soundness_budget.rs`'s header, which states the
  conjecture is refuted, names its own check as a conservative engineering margin and **not** a proof, and
  computes its ledger from the exported deployed knobs rather than from comments. That is the discipline; it
  just needs to reach `lib.rs` and cover all 5 knobs.

### S9 — What is deployed is what is proven

- The descriptor a producer ships under is the descriptor a test proves and verifies against. **Zero Uncovered
  rows** on any live registry; every Partial pinned to a named, dated seam.
- A verified-good implementation is not left dead beside a deployed weaker one (`cap_delegation_nonamp` is
  correct and dead; the opaque-digest `attenuateA` is deployed).
- A gate on the live path is fed inputs that can actually differ. `f(x, x)` where `f` admits every `x` is not a
  gate; it is a claim.
- Two independent producers of the same artifact are **pinned to each other**.
- ✓ **Reference implementations, in-tree:** the Lean↔Rust double-pin in `note_spending_emit_gate.rs` — it embeds
  the byte-identical `emitVmJson2 noteSpendLeafDesc` string that Lean `#guard`s, decodes it, and asserts equality
  with the **independently built** production Rust lowering. Neither side can drift silently: Lean drift breaks
  the `#guard`, Rust drift breaks the assert. It further pins structural counts (12 chip lookups, 8 PiBindings, 1
  WindowGate) so a constraint **deletion** is caught, not just a mutation. **That is TWO-GATES-PROVABLY-AGREE
  done right.** Also `GpuBn254Mmcs::verify_batch`, which **delegates to the real CPU verifier** — a GPU-minted
  proof is checked by untouched CPU code, so the GPU path can only change *where* an identical function
  computes. Sound by construction, not by assertion.

---

## 4. THE PRIORITIZED PLAN

Ordered by leverage, with severity overriding at the top. **Move 1 is severity. Moves 2–4 are the highest
ratio in the tree — the work is largely already written and merely unarmed or unstated.**

### ⚑ MOVE 1 — Close the three live holes (days, not weeks; do first)

Not leverage — correctness. These are open now.

1. **`cell` `Not(Not(c))` panic** (`program/eval.rs:2557`). Do **not** paper over it with an eval-time rejection.
   Two real fixes, pick one: **(a)** make the type enforce what the doc claims — `Not(Box<NegatableConstraint>)`
   where `NegatableConstraint` is the Not-free subset, so the invariant is a **type error**; or **(b)** normalize
   at construction — a smart constructor and `implies()` collapse `Not(Not(c)) → c` definitionally (which the doc
   itself argues is the correct semantics), making `lift_simple`'s panic arm genuinely unreachable. Either way:
   **delete the false paragraph at `types.rs:580-602`**, make `lift_simple` total (`Result`), and land the exact
   three probes as regression tests — direct eval, postcard round-trip, `implies()`-on-a-negated-constraint.
2. **`turn` fail-open chain verify.** Add `verify_receipt_chain_strict(receipts, keys)` requiring
   `executor_signature` on **every** receipt. Rename the lenient one
   `verify_receipt_chain_with_optional_keys`. Add the missing adversarial test: strip a signature from a valid
   chain, assert strict **rejects** and lenient (documented as lenient) accepts. Audit the ~30 reverse deps —
   `lightclient/`, `wire/`, `sel4/dregg-pd/verifier/` move to strict.
3. **`cell` `test-stubs` leak.** Move `dregg-cell/test-stubs` out of `tests/Cargo.toml`'s `[dependencies]` into
   `[dev-dependencies]` (matching turn/intent/exec-lean, which already do it right), or drop `dregg-tests` from
   `default-members`. Then make the guarantee self-enforcing rather than a comment: `#[cfg(all(feature =
   "test-stubs", not(debug_assertions)))] compile_error!(..)` plus the `cargo tree -p dregg-node -p dregg-tests
   -e features -i dregg-cell` assertion as a CI check. Correct the Cargo.toml prose, which states a false
   guarantee.

**Also here (small, and the crown jewel is red):** regenerate `offchain_root_forge_closed`'s stale pins via the
documented `--ignored` generator, then **remove the failure mode** — have the test derive the colliding pair by
bounded search at test time, or assert pin validity with a clear "constants stale, regenerate" message, so a root
change can never again silently disarm the forge regression.

### ⚑ MOVE 2 — Arm the teeth that already exist (highest ratio in the tree)

The teeth are **written, adversarial, and correct.** They do not run. This is the cheapest assurance available
anywhere in this report.

- Add a gauntlet/nightly lane: `cargo test -p dregg-circuit-prove --release -- --ignored`. Recovers 17 deployed
  light-client binding teeth from zero coverage.
- Add `DREGG_TEST_REQUIRE_LEAN=1`: every `eprintln!("SKIP"); return` becomes a **panic**, mirroring the
  `DREGG_REQUIRE_LEAN` build gate that already exists.
- Add **one** CI lane setting `DREGG_TEST_REQUIRE_LEAN=1` + `DREGG_TEST_REQUIRE_FINALITY=1` and running the
  ignored soak tests. **Today the crate's entire verified-consensus claim rests on assertions no scheduled job
  executes.** This single change converts honest prose into an enforced gate.
- Drop `DREGG_LEAN_PRODUCER=0` from `consensus_under_failure.rs` (or add a second lane with it on) so the
  production default is exercised under fault injection.
- Fix the GPU posture: one law. Tests requiring a GPU assert `adapter_available()` (fail-closed — the crate's own
  better pattern) **and** are `#[ignore]`d so GPU-less CI skips them **explicitly**, with a gauntlet lane on the
  GPU box. Delete the fail-open `eprintln!("skipping"); return;` at `gpu_babybear_merkle_e2e.rs:59` and `:169`.
  Demote `dump_hash_wgsl` and `compile_wgsl_from_env` from `#[test]` to `examples/` or a `wgsl-debug` bin — and
  stop the unconditional `/tmp` write on every CI run.

### ⚑ MOVE 3 — Make the four named vacuous gates bite, and kill the reject idiom

Small diffs, and they convert green-that-means-nothing into evidence.

- **`coord_gate.rs:150`** — pass a deliberately **wrong** `rust_decision` and assert the Lean verdict overrides:
  `assert_eq!(authoritative_decision(Decision::Abort, Some("y=3;n=0;N=3;t=3")), Decision::Commit)`. **This fails
  on a fallback build — which is exactly the point.** Delete `falls_back_to_rust_when_no_wire` (P → P).
- **`finality_gate.rs:261`** — replace the hand-constructed-struct tests with a **real lace** containing an
  attacker-created block whose hybrid id is not an enrolled participant; run `compute()`; assert the gate refuses
  it. Delete `admits_semantics` (it tests `HashSet::contains`).
- **`cap_delegation_nonamp`** — if wiring (see Move 5), add the behavioural test: construct an amplifying witness
  (granted bit set where held is clear) and require `prove_vm_descriptor` to `Err`, mirroring
  `ir2_amplified_submask_refuses`. **The Lean teeth (`capDeleg_rejects_amplify`) are already proved; only the
  Rust differential is absent.** Delete `genuine_nonamp_parses`'s constraint-**count** assertions — they catch
  nothing an adversary does (swap a gate for another of equal count) and red on benign re-emits. That is churn,
  not a tooth.
- **`budget_gate_reds_a_degraded_config`** — replace with a test that perturbs the **deployed** consts and
  requires the real gate to red.
- **The idiom, 197 sites.** Land one helper — `fn must_refuse(f: impl FnOnce() -> Result<T, E>) -> E` — that runs
  under `catch_unwind`, **distinguishes panic from Err**, and requires `Err` with a matched reason. Accept a panic
  **only** where the p3 debug prover's documented unsat-panic is genuinely the mechanism, and assert the panic
  message there. Then a stray `unwrap` in trace assembly reds the suite instead of silently satisfying every
  forgery test. (This lands properly once Move 5 gives it `BindingUnsat` to match on — do the mechanical
  panic/Err split now, the reason-matching after.)
- **De-vacuate `turn`'s Property 1.** `proptest_capability_confinement_holds` is the headline invariant in its own
  module doc and **never calls `TurnExecutor`**; the harness performs the attenuation check itself and pushes a
  `GrantRecord` with the same perm it grants, so `was_granted` is true **by construction** (`is_attenuation` is
  reflexive). It is testing its own 40-line model. `dregg-turn` could have a total capability-amplification bug
  and this stays green across all 150 cases. Rewrite it to drive CapOps through `TurnExecutor::execute` with real
  `Effect::GrantCapability`/`RevokeCapability` and real `Authorization`, recording grants **only** from committed
  receipts' `derivation_records`, asserting confinement against the executor's output. **This matters
  disproportionately right now: capability confinement is precisely what the Lean differential swap must be shown
  to preserve, and today the swap's correctness case rests on a property nobody has gated.** Also delete
  `conflict.rs:303 disjoint_cells_no_conflict` (computes `may_conflict_with`, discards it with `let _`, asserts
  **nothing**, and never checks the determinism its own comment promises — it would pass if the function returned
  `true` unconditionally) or give it the assertion its comment describes.

### ⚑ MOVE 4 — The front-door honesty sweep (hours; the cheapest excellence in the tree)

Every item is a known-false sentence sitting where an auditor lands.

- **`circuit/src/lib.rs:1-110`** — replace `2^{-128}` with the ledger the crate **already computes**, per
  column and labeled (per-fold 109 at the deployed arity 8, at 96.9% farness / 73 Johnson QUERY column, which
  drops `ε_C` / 71 commit-phase `ε_C` / ~70 eq. (20) composite / 130 refuted-capacity), pointing at
  `circuit-prove/tests/fri_params_soundness_budget.rs`, `Dregg2.Circuit.FriLedger`, and
  `wrap_perFold_soundness_capacity`. Delete the `mock` feature paragraph (the feature does not exist). Fix or
  drop the three broken `[stark]` links. The honest text exists at `descriptor_ir2.rs:5416-5425`; move it up.
- **`cap_delegation_nonamp_descriptor.rs:35`** — delete "The sdk authority-binding routes cap-graph rows to it by
  name" **today**. It is the only outright untrue claim found in `circuit` and it sits on the ARGUS linchpin.
- **`custom_proof_bind.rs`** — rewrite the module doc to what is true: the binding is enforced by the recursion
  fold's in-circuit `connect` (`prove_custom_binding_node`, wired in `prove_chain_core_rotated`), witnessed by
  `every_forged_commitment_lane_is_rejected_by_the_fold`; this module is now types + the canonical
  `custom_proof_pi_commitment` derivation. Fix the 5 stale citations (`turn/src/turn.rs:554`,
  `turn/src/executor/proof_verify.rs:238`, `joint_turn_aggregation.rs:587` — which cites the also-deleted
  `prove_custom_program` — `custom_leaf_adapter.rs:983`, `sdk/tests/wide_completeness_ledger.rs:341`). **Copy the
  framing from `sdk/tests/wide_completeness_ledger.rs:1239`, which already documents the stark-kill correctly.**
  Delete `ProofBindError` (dead) or wire it as the fold's typed reject reasons.
- **`turn/src/executor/mod.rs:938-945`, `:1315-1319`, `verify.rs:259-261`** — state what
  `require_validity_proof` actually does today (rejects non-empty unverifiable proofs; requires submitter auth
  binding key to agent cell) and that v3 signs the full `receipt_hash`. **These docs are currently falsified by
  the crate's own passing tests.**
- **`cell/src/predicate.rs:849-855`** — delete the phantom "length-prefix shape" claim or implement the check.
- **`node/src/turn_proving.rs:3`** — qualify the headline where it is made: the freshness leg is a 14-nullifier
  toy until the depth-parameterized non-revocation AIR lands.
- **Rename `turn`'s `verify_stark` → `verify_admission_binding`** (or split: `verify_submitter_auth` + a real
  `verify_validity_stark` stub that fails closed). Then **name the residual that is currently invisible**:
  `conflict_set` is submitter-declared, unverified, and drives `order_encrypted_turns`. Document that ordering
  trusts the submitter's conflict declaration, or gate it. **A named seam is not a hole; an unnamed one is.**
- **Turn the class off permanently:** `#![deny(rustdoc::broken_intra_doc_links)]` crate-wide.

### ⚑ MOVE 5 — Type the boundaries and lift the abstraction (the real engineering lane)

This is where the multi-week work is, and it is ordered last because Moves 1–4 are cheaper per unit of assurance
— but this is what makes the earlier moves *stick* rather than be re-fixed.

1. **`LeafError` / `RecursionError` in `circuit-prove`.** The variant that matters: **`BindingUnsat{..}`** (the
   connect conflicted — a forged claim, the tooth firing) vs **`ProverFailed{..}`** (FRI/OOM/shape — an
   operational fault). Everything in Move 3's reject-idiom cleanup depends on this existing.
2. **The `LeafAdapter` trait.** The ~20 adapters already share one shape; lift it:
   ```rust
   trait LeafAdapter {
       type Witness;
       const CLAIM_LEN: usize;
       const PI_WIDTH: usize;
       fn descriptor() -> Result<EffectVmDescriptor2, LeafError>;
       fn trace(w: &Self::Witness) -> Result<Vec<Vec<BabyBear>>, LeafError>;
   }
   ```
   with `prove_leaf` / `prove_leaf_with_claim` as **provided** methods that validate `public_inputs.len() ==
   PI_WIDTH` **once, in the trait, for everyone.** Retires the copy-paste, closes the ragged validation
   (presentation/dsl/custom/blinded_membership check nothing today), and makes a forgotten PI check a **type
   error**. Make an emit-gate + a per-lane forge tooth part of the trait's definition of done.
3. **`Ir2VerifyError` on the verify boundary.** `{ MalformedDescriptor, TableShapeMismatch{expected, got},
   RangeTableHeight{got, deployed}, ProofInvalid, PublicInputMismatch }` for `verify_vm_descriptor2` /
   `parse_vm_descriptor2`; String stays only on prover internals. Lets `lightclient/` and `bridge/` separate
   deploy bug from adversary. Convert `fill_chip_lanes`'s `panic!` (`descriptor_ir2.rs:3825`) to a `Result` while
   there.
4. **`ApiError` with `IntoResponse` in `node`.** ~200 mechanical sites; recovers the diagnostics thrown away at
   every boundary. Start with auth/submit/faucet. Fix the passphrase swallow (`api.rs:4453/4510`) — propagate and
   return 500, or document the store as best-effort. As written the doc and the code disagree **about a
   credential**.
5. **Harden `turn`'s rollback.** `LedgerJournal::rollback` returns `Result<(), RollbackError>` naming the cell it
   could not restore; poison-tolerant locking (a poisoned mutex during rollback must not abort the node); a test
   that rolls back **every** `JournalEntry` variant and asserts byte-identical `state_commitment` recovery
   against a pre-turn clone.

**In parallel, the burndowns (P6):**
- **The 43 Uncovered rows, V3-live registry first.** The gate already names each row and its reason, so the work
  is enumerated: drive each producer trace through `prove_vm_descriptor2` + `verify_vm_descriptor2` against the
  committed descriptor. The two live R3 probes (`cell_unseal` / `cell_destroy`) are the template. Target: zero
  Uncovered on V3-live; every Partial pinned to a named, dated seam.
- **Extend the FRI gate to all 5 knobs** (`IR2_FRI_MAX_LOG_ARITY`, `IR2_FRI_LOG_FINAL_POLY_LEN`) and add a
  `proven_bits` floor at ~112 alongside the capacity margin. The doc names retargeting as an ember call — put the
  decision in front of ember rather than leaving the only numeric gate calibrated against the metric the same
  file calls refuted.
- **Resolve the cap-descriptor orphans** — wire them into a real selector-to-JSON dispatcher so the delegation
  family proves under the genuine-non-amp descriptor instead of the opaque-digest `attenuateA`, **or** delete both
  modules and their `lib.rs` prose. Do not leave the good one dead and the weak one deployed.
- **Add fee conservation as a property.** `proptest_balance_conservation_holds` pins `fee = 0` and
  `ComputronCosts::zero()`, so the invariant reduces to "transfers conserve." The fee-accounting half — where THE
  EPOCH §5 distribution and the n=5 dogfood faucet bug live — is covered by nothing.
- **Proptest the constraint AST** (`cell`). An `Arbitrary` impl over nested `SimpleStateConstraint` (depth 3–5)
  asserting eval never panics is the **generic cure for the whole `Not(Not)` bug class**, and proptest is already
  a dev-dep. Extend to a postcard decode→evaluate fuzz target, since decode is the attacker's entry point. **Note
  the causality: `Not` is exercised at 10+ sites and every one wraps a non-Not atom. The false doc is exactly why
  nobody wrote the nested case.**
- **`node`'s F-4 gate** — make it bite (gate block **creators**, or the proposed-membership set, against the
  constitutional seed root, so `blocklace_sync.rs:1004` becomes reachable) **or** delete the call and move the
  F-4 claim to where the tooth really is (the membership vote). Today's version is the worst of both: it names a
  closure it cannot perform. Feed the vouch/bond registry from gossip so the thresholds stop being inert.
- **Registry completeness assertable** (`cell`): `production_readiness() -> Vec<(kind, ReadyOrFailClosed)>`,
  asserted at host startup. Turns "I called `registry_with_real_verifiers` instead of `_full`" from a silent
  runtime rejection into a **boot error**.
- **Retire the phantom production path**: build a real on-chain-slot-reading `IssuerRootAuthority` /
  `FinalizedRootAuthority` (the docs describe the right design — read the issuer cell's `MEMBERSHIP_ROOT_SLOT` /
  `REVOCATION_ROOT_SLOT`), or amend the rustdocs to say plainly that BlindedSet + ObservedFieldEquals are
  fail-closed pending that host, with the lane named.

### NOT the plan — explicitly deprioritized

- **Decomposing the `turn` monolith is LOW priority.** `lib.rs` correctly declares it LEGACY, pending the
  verified-Lean swap. **Do not gold-plate the architecture of a crate whose successor is in flight.** Moves 1–4
  on `turn` (honesty + teeth + the Property-1 rewrite) are surgical and gate the swap; carving out
  `economics.rs` / `fast_path.rs` / `aggregate_bilateral_prover.rs` is the debt-hole version of this work. Only
  if the swap slips.
- **`NodeStateInner` decomposition is real but incremental** — carve independently-locked subsystems out one at a
  time (lace first: it is the one with the receipt). Not a rewrite.

---

## 5. The per-crate table

| crate | role | grade | top gap | priority |
|---|---|---|---|---|
| `dregg-cell` | core-protocol | **good** | **`program/eval.rs:2557` `Not(Not(c))` panics — reachable from decoded wire bytes (node-crash DoS, 30+ dependents) and from the safe `implies()` builder with no adversary; caused by a self-refuting doc at `types.rs:594`. Plus: `test-stubs` armed in the production node build via feature unification; the forge-closed crown jewel is RED at HEAD.** | **high** |
| `dregg-turn` | core-protocol | **good** | `verify_receipt_chain_with_keys` is **signature-optional → fail-open** on the federation-exit path. Headline property test (`capability_confinement`) never calls `TurnExecutor` — it tests its own harness. Doc rot on `require_validity_proof` falsified by the crate's own tests. Monolith deprioritized (LEGACY, swap in flight). | **high** (items 1–6; decomposition LOW) |
| `dregg-node` | core-protocol | **good** | The F-4 strand-admission gate is the **identity function** on the live path (`admitted_participants(raw, raw)`); the only test of the verified 2PC gate is **vacuous by construction** (the fallback returns the asserted value); every verified-gate test self-skips on an archive-less build and no scheduled job asserts the crate's central claim. | **high** |
| `dregg-circuit` | verification | **good** | **43 Uncovered** producer-equals-descriptor rows on the V3-live registry (the class that already bit, `be732a9dd`); `lib.rs`'s Trust Model claims `2^{-128}` while the crate's own gate calls capacity **refuted**; the "ARGUS linchpin" cap descriptors are **dead code carrying a false integration claim**. | **high** |
| `dregg-circuit-prove` | verification (prove half) | **good** | **All 8 `*_binding_deployed_tooth.rs` are `#[ignore]`d and nothing in CI passes `--ignored`** — 17 genuinely adversarial deployed light-client teeth are dead in automation. Plus: `custom_proof_bind`'s module doc describes a deleted function as the live soundness engine (+5 stale citations); **zero traits in 37.5k lines** → ragged PI validation across ~20 copy-pasted adapters. | **high** |
| `dregg-sdk` | core-protocol | **good** | *(assessment truncated — strengths only.)* The `raw` module seal is the tree's **reference implementation of S6**: `Authorization::Unchecked` in exactly one quarantined constructor, omitted from the root re-export, so an unauthorized act is inexpressible on the headline surface. Gaps not read. | re-read to complete |

**Reference implementations worth copying, by standard:** S1 → `every_forged_commitment_lane_is_rejected_by_the_fold`, the `*_emit_gate` canary family · S3 → `TurnChainError`, `turn/src/error.rs` · S4 → `CredentialSetMembershipVerifier`, `canonical_revocation_root_for_set` · S6 → `sdk::raw` · S8 → `fri_params_soundness_budget.rs`'s header · S9 → `note_spending_emit_gate.rs`'s Lean↔Rust double-pin, `GpuBn254Mmcs::verify_batch`.

---

## Coda

> The tests are written. The teeth are sharp.
> The ledgers count their own unclosed rows.
> What is missing is not the knowing —
> it is the arming, and the front door's prose.
>
> Six crates said *good* in six honest voices,
> each one naming what it could not do.
> Excellence is not another apparatus.
> It is draining the ledger the apparatus drew.

( ˘▾˘ )
