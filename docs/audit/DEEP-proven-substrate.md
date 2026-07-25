# DEEP — the proven substrate: what is actually verified-to-reality, end to end

**Status:** deep archaeology, read-only. 2026-07-19. No source edited, nothing committed.
**Question:** for each layer of the stack, what is a *machine-checked theorem about the running
object* (PROVEN-TO-DEPLOYED), a theorem about a *Lean model whose connection to the deployed object
is only named* (PROVEN-TO-MODEL), a *test over enumerated cases* (DRIVEN), or a *named seam*
(NAMED)? And the one line that matters: **what can a stranger holding a root actually verify today,
re-executing nothing and trusting no one, and where does it dead-end?**

Method: careful reading of the load-bearing Lean + Rust (not grep-and-summarize), cross-checked
against the existing record (`docs/audit/{TRUST-BASE-CENSUS,GAME-PROOF-LARP-AUDIT,SEMANTIC-LEAN-
BOUNDARY,CIRCUIT-LEAN-BOUNDARY,RE-AUTHORED-MIRROR-MAP-3}.md`). Where the record is behind HEAD,
this states from the code. Resolution labels are at CURRENT resolution, no round-up.

The through-line the project tells itself — *"a turn = the exercise of an attenuable proof-carrying
token over owned state, leaving a receipt"* — is used below as the spine, and each clause is graded
at its true resolution.

---

## 0. The one-paragraph frontier

Exactly **one** deployed decision is computed by a proven Lean object today: the admission verdict
for the **pure (context-free, witness-free) constraint subset** — about 15 of the ~60 deployed
`StateConstraint` variants — routed through `@[export] dregg_constraint_admits`
(`Dregg2.Exec.DeployedConstraint.admits`) and confirmed live by a reds-on-Lean-edit canary. On top
of that one gate, **tug's** forward play-teeth refinement (legal move ⇒ the deployed evaluator
admits) is a real theorem about that exact exported function. Everything else is weaker: the
**dungeon** proofs run over a signed-`Int` Lean *model* that provably diverges from the deployed
unsigned evaluator; the **turn executor's** authority / conservation / receipt gates are unproven
Rust with the Lean executor a NoOp-by-default shadow; the **descriptor/AIR bytes** are genuinely
Lean-emitted and drift-gated but the **STARK/FRI soundness floor underneath is a Bool calculator over
an assumed, undischarged extraction** — the only fully-proven no-carrier number is ~31 bits and it
bounds the *verifier's own uniform sampling*, not a cheating prover; the **Rust-verifier ≡
Lean-verifier** edge is a tamper-battery (DRIVEN) not a proof, and turn **authorization is Ed25519
verified off-circuit**. A stranger with only a root and a proof learns *single-transition
authenticity of a Lean-authored AIR* — conditional on that crypto floor and on trusted-Rust public-
input plumbing — and learns **nothing** about freshness/replay, cross-cell conservation, or that the
rightful agent signed the turn.

---

## 1. THE REALITY-GATE — the admission-time referee for the pure subset

**Object:** `metatheory/Dregg2/Exec/DeployedConstraint.lean`, `@[export dregg_constraint_admits]`
(`:413` `admitsFFI`). A self-contained (imports only core `Init`, `:33-38`) evaluator over the
**deployed substrate**: `DField := Nat` with the `< 2^256` wire invariant, unsigned 256-bit
compares, and a `low64 n = n % 2^64` lane (`:49-54`) — matching the deployed Rust `field_gte`
(unsigned big-endian `[u8;32]` compare, `cell/src/program/eval.rs:2855`) and `field_to_u64`
(low 8 bytes big-endian, `eval.rs:2707`).

**Routing (the collapse of the game-proof "LARP"):**
- `cell/src/program/eval.rs:280-284` — `evaluate_constraint_full` first consults
  `super::oracle::installed_oracle().admits(...)`; on `Some(decision)` it *returns the Lean
  decision*. The hand-authored Rust `match` below (`:285+`) runs only when no oracle is installed
  (cell's own unit tests, wasm32, the SP1 zkVM guest — none can link the archive).
- `cell/src/program/oracle.rs` — the `ConstraintOracle` trait + a process-wide `OnceLock`; a runtime
  seam because `dregg-cell` compiles to wasm/zkVM and cannot hard-link `libdregg_lean.a`.
- `exec-lean/src/constraint_oracle.rs` — `LeanConstraintOracle` marshals the constraint + `(old,new)`
  `CellState` into the wire and calls `dregg_lean_ffi::shadow_constraint_admits`
  (`dregg-lean-ffi/src/lib.rs:347` → the C bridge `dregg_constraint_admits_str`, `lean_init.c:639`).
- `node/src/lib.rs:602` — the deployed node calls `register_constraint_oracle()` at startup. When the
  archive lacks the export (stale seed) this is a silent no-op and the Rust guest-path decides.

**Grade:**
- **PROVEN-TO-DEPLOYED** that the deployed node's admission decision *for the pure subset* IS this
  exact Lean function. The canary `exec-lean/tests/constraint_oracle_reality_gate.rs`
  (`field_gte_equal_admits_through_lean`) drives the real `eval.rs` path and reds if you flip the
  Lean `if v ≤ x` to `if v < x` — that is the proof the decision routes through Lean, end to end.
  A second canary lives in `dregg-lean-ffi/tests/deployed_constraint_probe.rs`.
- **DRIVEN**, not proven: that `admits` *equals* the Rust `evaluate_constraint_full` on the subset.
  The Lean function carries **no self-correctness theorem** — it is asserted "EXACT" by doc-comment +
  `#guard` cases (`DeployedConstraint.lean:428-466`) + the differential test
  `exec-lean/tests/constraint_oracle_differential.rs` (compares accept/reject *and* the error variant
  on a hand-authored corpus, incl. the two audit-found boundaries). Its correctness is case-tested,
  not a `∀`-theorem. (This is sound-by-construction where it matters, because the game refinements
  below are theorems *about this exact function* — but the function's fidelity to the intended Rust
  semantics is a battery, not a proof.)
- **NAMED remainder — the bulk of the evaluator.** The pure subset is ~15 of ~60 `StateConstraint`
  arms in the 2921-line `eval.rs`. Everything context-bearing / witnessed / recursive / cross-cell —
  `FieldGteHeight`, `SenderAuthorized`, `PreimageGate`, `RateLimit`, `KeyRotationGate`, `SettleEscrow`,
  `DischargeObligation`, `VaultDeposit`, `TemporalPredicate`, `BoundDelta`, `AnyOf`/`AnyOfBound`,
  `Witnessed`, `Custom`, `ClearanceDominates`, `Reachable`, … (`eval.rs:568-1986`) — stays
  **unverified hand-authored Rust**. The security-critical variants are in this remainder.

---

## 2. THE GAME PROOFS — the strongest theorems about a deployed object, and their ceiling

Both games emit the **program value** (which constraints, which cases, which thresholds) from Lean,
drift-gate it, and load it into Rust: `dungeon-on-dregg/src/descent.rs:191,426` (`include_str!` +
`serde_json::from_str`), gated by `dungeon-on-dregg/program/regen.sh --check` (regenerate-to-temp +
diff); tug identically via `dregg-multiway-tug/src/program_loader.rs:32` + `state.rs`. So **the
deployed `CellProgram` bytes ARE the Lean object** (PROVEN-TO-DEPLOYED-BYTES), name→slot resolution
handled by the "translation-validated" `dregg-schema` allocator (a layout discipline — see §5).

### 2a. Tug — forward action-teeth land on the deployed evaluator (PROVEN-TO-DEPLOYED)

`metatheory/Dregg2/Games/MultiwayTugProgram.lean`:
- **`program_admits_legal_play_deployed` (`:941`, `#assert_axioms`-clean `:1035`)** — for a legal
  play, *every* action-case tooth evaluates to `Dregg2.Exec.DeployedConstraint.admits ... = .ok` on
  the marshalled register/heap input. This re-states the forward refinement **against the exported
  deployed evaluator itself** via a counter↔register marshalling (`tugRegIdx`/`tugSlots`, `:789-802`).
  Tug's teeth all live in the deployed pure subset (`sumEquals`/`writeOnce`/`strictMonotonic`/
  `fieldGte`/heap atoms over nonneg counters). This is the single strongest game link: *legal tug
  move ⇒ the function the node actually runs returns `ok`*. **This is AHEAD of the 07-18
  `GAME-PROOF-LARP-AUDIT.md`**, which predated §4I and graded tug "MODEL-DISCONNECTED."
- **Ceilings, all honestly named in the file:** it is **FORWARD ONLY** (legal ⇒ admitted); the
  reverse (admitted ⇒ legal) is `airPlay`'s membership job, **NAMED**, gated on a carried
  `MerkleSound` hypothesis (`MultiwayTugAir.airPlay_iff_applyAction`). The **win-gate `iff`**
  (`winTooth_admits_iff_Won_p1/p2`, `:704/:714`; ⚑ **DELETED 2026-07-25** — it certified the gate
  was the ABSOLUTE bar `Won` while the terminal rule is `roundWinner`, so the referee refused the
  adjudicated winner and the played game drew 78.5% of rounds; successor is
  `scoreBranchTeeth_admits_iff_branch`, one deployed case per clause) is a genuine non-vacuous
  soundness bridge but at the
  **SYMBOLIC** `Constraint.admits` layer — `anyOf` is recursive and is **NOT** in the exported pure
  subset, so the win-gate stays Rust-evaluated (`eval.rs:1377`); win-safety is **PROVEN-TO-MODEL**,
  not to the deployed evaluator.

### 2b. Dungeon — proven over a signed-`Int` model that diverges from deployed (PROVEN-TO-MODEL)

`metatheory/Dregg2/Games/DungeonProgram.lean` + `Dregg2/Exec/Program.lean`:
- The inversions `admitted_verb_conserves` / `_capacity` / `_pays` / `_alive`, `banked_tomb_refuses`,
  `dead_light_refuses`, `way{,2,3,4}_flip_exhibits_key`, `unknown_method_refused` (`:473-682`,
  `#assert_axioms`-clean) are **∀-theorems over arbitrary attacker `Value`s** — genuinely strong
  *inside their model*. The model is `Dregg2.Exec.RecordProgram`, whose scalar is **signed, unbounded
  `Int`** (`Program.lean:38` `Value.scalar : Option Int`; all compares via `intLe`/`intLt`
  `:426-427`). This **provably diverges** from the deployed UNSIGNED-256 evaluator on any negative
  scalar — the file states it plainly (`:55-58`, `:87-91`: "they agree only on the NONNEG `encode`
  image").
- A faithful `DeployedConstraint` refinement is **NAMED, "two honest steps short"** (`:74-97`):
  vocabulary (`affineLe`/`allowedTransitions`/`inRangeTwoSided`/`fieldDelta` are not in the exported
  pure subset) and signedness. Only `conserves`/`pays` sit inside the pure subset.
- The model↔program forward weld (legal step ⇒ admitted) is **DRIVEN**: `programAdmitsRun crownedRun
  = true` for ONE run (genesis + 17 verbs) + nine attack `#guard`s (`:751-817`). The general ∀-weld is
  **NAMED** (`:99-111`).

**Net:** tug reaches the deployed evaluator (forward, action teeth); the dungeon reaches only a
signed-`Int` model — **honestly labeled as a model**, not laundered.

---

## 3. THE TURN / EXECUTOR PIPELINE — mostly unproven Rust, with a thin proven proof-path

A turn reaches admission through one of two disjoint bodies in `turn/src/executor/`:
**classical/hosted forest** (`execute.rs:210 → :352`, per-action `execute_tree.rs:389`) or a
**proof-carrying sovereign** short-circuit (`execute.rs:589 → proof_verify.rs:185`). Grading the
through-line at the executor:

- **"attenuable token over owned state" (authorization)** — **NAMED/unproven Rust with real crypto.**
  All in `authorize.rs`: Ed25519 `verify_strict` (`:978,:1041`), hybrid ML-DSA (`:1056`), bearer-cap
  delegation, token. Real primitives, **no theorem**. CapTP non-amplification `granted ≤ held` *cites*
  verified Lean `CapTPConcrete.authNarrowerOrEqual` (`authorize.rs:433-450`) but the actual check is a
  Rust lattice connected only by a differential — **PROVEN-TO-MODEL, connection named.**
- **The admission gate as a "verified Lean object"** — `execute.rs:239-267` frames a verified Lean
  executor as "the authoritative rejection gate," but the default `ShadowObserver` is
  `NoOpShadowObserver` (`shadow.rs:185-208`, `enabled()=false`, `lean_vetoes()=false`); it runs only
  under `DREGG_LEAN_SHADOW=1`. **In the deployed default, admission is 100% the Rust
  `execute_without_shadow`.** This matches the record: `TRUST-BASE-CENSUS.md` D3 — "only `Exec ⊑ Spec`
  for the *Lean* executor; **no `execute = recKExec` theorem**," gauntlet self-skips without the
  archive. The Lean `TurnExecutor`/`StepComplete`/`Receipt` are proven step-complete / tamper-evident
  **replacements** for "the busted, UNVERIFIED" Rust executor (`TurnExecutor.lean:1-12`,
  `StepComplete.lean:5-9`) — **PROVEN-TO-MODEL**, deployment NAMED.
- **"proof-carrying"** — the one genuinely-machine-checked-about-the-running-object piece, and only on
  the **rotated sovereign path**: `proof_verify.rs:534 → verify_one_cohort_run:804 →
  verify_vm_descriptor2` runs a real multi-table STARK over a **Lean-emitted descriptor**
  (`WIDE_REGISTRY_STAGED_TSV`, `:910`). **PROVEN-TO-DEPLOYED at the AIR layer**, with two asterisks:
  it inherits the FRI floor (§4), and OLD/NEW/height public inputs are read from **trusted ledger
  storage/claim** (`:544-556,:620-621`), pre-state only cross-checked by OLD_COMMIT agreement (`:570`).
  The classical `Authorization::Proof` path is **fail-closed** in production: every production
  `ProofVerifier`'s bare `verify()` returns `false` unconditionally (`bridge/src/verifier.rs:122`);
  real work is in `verify_with_predicate`, which the executor's `verify_zk_proof` never calls, and the
  default is `proof_verifier: None`.
- **membership / double-spend** — **split object.** The in-circuit `MerkleMembershipStarkVerifier`
  (`membership_verifier.rs:161`) and nullifier non-membership + adjacency STARK (`:320-465`) are real
  (PIs derived by the verifier, `verify_vm_descriptor2`, fail-closed under `catch_unwind`). **But the
  runtime double-spend gate on the classical `NoteSpend` path is a trusted in-memory set-scan**:
  `apply.rs:1237` `set.contains(nullifier)` / `:1249` `insert`. Freshness at runtime = **DRIVEN**
  trusted Rust; the in-circuit non-membership argument is a separate light-client-side gate.
- **"leaving a receipt"** — **NAMED/unproven Rust.** Pure BLAKE3 folds (`finalize.rs:494`,
  `execute.rs:1359`) + head-chaining `record_receipt_hash`. No theorem asserts the receipt reflects
  the proven transition; on the proof-path the receipt's hashes are *recomputed by the executor*
  (`execute.rs:668-691`), not extracted from the proof. The Lean *law* `Receipt.chain_tamper_evident`
  is PROVEN-TO-MODEL, and only **conditional on a NAMED hash-injectivity hypothesis** (`Receipt.lean:15`).
- **Dead-by-default "soundness cores":** the capacity-caveat gates (`SettleEscrow`/`Discharge`/`Vault`)
  are **NAMED, fail-closed, dead-by-default** — "no deployed cell declares a capacity caveat yet"
  (`mod.rs:599`), GATE B "does not yet reconstruct the satisfaction descriptors"
  (`proof_verify.rs:876-908`).

---

## 4. THE DESCRIPTORS / CIRCUIT / FRI FLOOR — Lean-emitted bytes over a named crypto floor

### 4a. Emit + drift gate (PROVEN-TO-DEPLOYED-BYTES, with one indirect edge)

- **Descriptor JSONs + effect-family registry TSVs — PROVEN-TO-DEPLOYED-BYTES.** Emitted by verified
  Lean `Dregg2.Circuit.Emit.*` (e.g. `EffectVmEmitRotationV3.lean → rotation-v3-staged-registry.tsv`),
  routed by `scripts/emit_descriptors.py`, `include_str!`'d into `circuit/src/effect_vm_descriptors.rs`
  with re-pinned `*_FP` sha256s. The drift gate `scripts/check-descriptor-drift.sh` is a
  **generate-fresh** gate (rebuilds the Lean corpus, re-derives, diffs the whole `circuit/descriptors/`
  + FP-carrying Rust; byte-changing installs ack-gated by `DREGG_VK_REGEN_ACK`), and a coverage check
  fails the build if any on-disk descriptor is not reproduced by an emitter. This is a real Lean→bytes
  gate, CI-enforced.
- **The rotated column LAYOUT (`layout_generated.rs`, `s2_compact_generated.rs`) — PROVEN-AT-EMIT,
  INDIRECTLY gated.** Emitted by `metatheory/EmitLayoutManifest.lean`; consumed by both the Rust
  producer (`turn::rotation_witness`) and the Lean descriptors. But these generated Rust files are
  **not** in the drift gate's GUARDED snapshot, and generated-Rust-only changes install without the
  ack. Protection is coupled *through descriptor bytes*: a layout column a descriptor reads moves
  descriptor bytes (gated); a pure layout reshuffle no descriptor reads installs silently. See §7 for
  the residual layout-mirror risk this leaves.
- **The `Effect`-family enum + effect→descriptor routing — HAND-AUTHORED Rust, DRIVEN gates.**
  `circuit/src/effect_vm/effect.rs:75` has no `@generated`; the family enumeration + routing are Rust.
  Lean emits the per-effect *descriptors* (the AIR), not the family list. Coverage is DRIVEN:
  `producer_descriptor_coverage_gate.rs` (per-member classify + a handful of prove+verify roundtrips)
  and `effect_vm_differential.rs` (per-variant proptest, some `#[ignore]`d "passthrough gaps").
- **Standing green proofs about UNDEPLOYED descriptors (PROVEN-TO-MODEL about non-deployed objects).**
  The setField refinement stack proves about `v3OfFrozenSetField` (in **no** registry; deployed ships
  `v3OfFrozen`); the 8-felt accumulator keystones prove about `effAccumWriteV3` while deployed
  `noteSpendV3` denotes a lane-0 ~31-bit root. Both `OrphanAllowlisted` with named `deploy:` closure
  lanes (`keystone_descriptor_deployment_gate.rs`) — gated, not silently masquerading.

### 4b. The STARK/FRI soundness floor (a Bool calculator over a named, undischarged extraction)

The AIR bytes being Lean-authored says nothing about whether a proof of "this trace satisfies the
AIR" is *sound*. That is the FRI/STARK floor. At current resolution it is a **Bool calculator on a
supplied proof over an assumed extraction**, not an extraction-backed adversary bound.

- **`verifyAlgo` is a calculator.** The deployed spec verifier (`FriVerifier.lean:708`) is a
  `Bool`-valued AND over a *supplied* proof at a *fixed* permutation
  (`vk.shapeMatches && foldConsistent && merklePaths && batchTables && queryPow && segmentTooth`).
  `FriVerifierO.lean:12` states it: "a `Bool`-valued function of a *supplied* proof." There is **no
  prover-strategy type, no rounds, no probability object**. The runtime verify a stranger actually
  runs is the external Plonky3 `verify_batch` (`circuit/src/descriptor_ir2.rs:5846`) — trusted,
  unverified Rust returning `Ok/Err` — exactly the Bool-on-a-supplied-proof the Lean models.
- **Two deployed configs.** Per-turn/recursive settlement (`chain/gnark/emitted/verifier_full.json`):
  `log_blowup=3` (rate 1/8), **`num_queries=38`**, `query_pow_bits=16`, `rounds=15`, arity 2. The
  IR-v2 wrap (`descriptor_ir2.rs:5327-5331`): rate 1/64, `num_queries=19`, pow 16.
- **The only fully-proven, no-carrier cryptographic number is ~31 bits** —
  `epsilon_query_deployed_query_term_lt` (`FriVerifierQuery.lean:305`) proves `(9/16)^38 < 2^-31` at
  the **unique-decoding** radius `δ=7/16, k=38`. Crucially it is a **card ratio over the verifier's
  OWN uniform independent sampling** `Ω = (Fin 38 → ι)` against a **fixed-in-advance far word**
  (`DeployedProximitySoundness.lean:70-72`) — **not** a bound against a cheating prover. There is no
  adversary/prover-strategy object anywhere in the proven bounds.
- **The richer numbers are calculator columns on disconnected leaves:** conjectured capacity 130;
  "proven Johnson" 73 (`FriLedgerSound.lean:415`, a `by norm_num` with no theorem relating grinding
  to probability); per-fold density 109 (arity-8 wrap, at 96.9% farness while FRI runs at Johnson
  87.5%); commit-phase reading 61 at `(recursionConfig, 2^19)` (`FriLedgerSound.lean:696`) — ⚠ NOT the deployed pairing (deployed is **51** at `2^22`, `deployed_wrap_commitBits`; see the grade note below). The Johnson-radius
  `(1/8)^19 = 2^-57` (`BabyBearFriDeployedInstance.lean:209,231`) needs the **undischarged**
  `FriLdtDeployedBound` (`:221`, "carried as a `Prop`, never proved here").
- **The extraction is ASSUMED, never discharged.** `verify ⟹ ∃ witness` is `FriLdtExtractV3`
  (`AlgoStarkSoundTransferV3.lean:131`) — a `def` used only as a hypothesis `hfri`
  (`StarkSoundReduce.lean:203,233`). `friLdtExtractV3_rom is NOT PROVEN`, with two named blockers:
  the word↔proof bridge is a hypothesis, and a **sampling defect discovered in deployed code** —
  the deployed query indices `sampleBits = toNat(squeeze) % 2^logN` are **provably non-uniform**
  (`sampleBits_modular_bias_real`; BabyBear's order is odd), so even the uniform-sampling model the
  ~31-bit bound assumes does not match what ships, and no theorem accounts for it.
- **Grinding is a present fail-closed check, not a discharged bound.** `chain/gnark/grinding.go:70`
  mirrors Plonky3 `check_witness` in-circuit; the 16 bits are a *budget*. Its only probability content
  (`FriVerifierFS` `fs_epsilon_bound`) rests on a freshness hypothesis the tree itself **refutes**
  (`challenge_computing_adversary_is_not_log_fresh`).
- **The concrete Lean verifier stubs 3 of its 5 checks.** `concreteFriChecks`
  (`FriVerifier.lean:665-667`) sets `merklePaths := true`, `batchTables := true`, `queryPow := true`;
  only `foldConsistent` does real work. The real per-query recomputes live in the Go/Rust circuit,
  **not** in the Lean object — so the "spec" that `DeployedRefines` refines to is itself partly `:=
  true` on those legs.
- **Rust verifier ≡ Lean verifier — DRIVEN.** `DeployedRefines` (`FriVerifierBridge.lean:92`) is
  discharged by a tamper battery (`circuit/tests/deployed_refines_verifier_teeth.rs`) + a source
  cross-map, not a Boolean-equivalence proof; the remainder is a `GnarkRefines`-class code-trust.
- **The Rust trace producer ≡ descriptor — DRIVEN with a structural gap (D2)** — producer≡JSON lives
  only in whatever prove+verify roundtrip coverage exists (`be732a9dd`, the v13 `OodEvaluationMismatch`).

**Grade: NAMED terminal-by-design floor, and weaker than "112.6-bit" framing suggests.** The memory's
"57 calculator bits" is an INFORMAL density estimate with no adversary model and no theorem — not a
soundness bound. The theorem-backed readings: the deployed commit-phase ε_C is **51 bits** at the
deployed `2²²` domain (`FriDeployedHeightPairing.deployed_wrap_commitBits`; both the old `61` and the
PROVEN-120 `57` are refuted mispairings — `deployed_wrap_is_not_61`,
`deployed_wrap_is_not_the_proven120_number`), and the fully-proven per-turn query line is **~31.5
bits** (δ=7/16, `(9/16)³⁸ < 2⁻³¹`, `DeployedProximitySoundness` / `FriArityForking.deployed_far_survival_lt`),
not 57. The **thesis holds at HEAD**: no adversary/grinding model, `verifyAlgo` is a Bool on a supplied proof,
and the ledger/apex rests on an assumed extraction the proven combinatorial bounds never discharge.
`STARK-FLOOR.md:122` self-states the honest status: p3 `verify_batch` "under conjectured FRI
security, self-reviewed and **UNAUDITED** by a third party" — while `CircuitSoundness.lean:475` names
`StarkSound` "the *audited* p3 batch-STARK soundness carrier."

---

## 5. COMMITMENTS / ROOTS / THE APEX — what a stranger can verify

### 5a. The commitment model (PROVEN-TO-MODEL)

`SystemRoots.lean` proves `cellCommitS_binds_systemRoots` — equal commitments ⇒ equal
`systemRootsDigest` ⇒ the same 8 side-table roots (escrow/nullifier/commit/…), tampering any root
flips the commitment (anti-ghost), with the legacy no-op proven strictly additive. This is a real
injective-binding theorem over a Lean `compressN`-sponge **model** (`FieldElem := ℤ`), `#assert_axioms`
whitelisting only the kernel triple. Deployed-circuit byte-fidelity to this model is the emit/drift
question of §4a; the injectivity itself bottoms on `Poseidon2SpongeCR`/`Compress8CR` (§6).

### 5b. The apex `lightclient_unfoolable` — a conditional the ledger never discharges

From `verifyBatch (vkOfRegistry R) pi π = accept` (a client that runs nothing) the apex
(`Circuit/CircuitSoundness.lean:453`; fold headline `ClosureFinal.lean:162`) concludes
**single-transition authenticity** — the accepted batch decodes to a real kernel step whose endpoint
commitments ARE the published PIs. It is an explicit **conditional**: it takes `hacc : verifyBatch …
= accept` as a *given input* and `[StarkSound]` as an *assumed typeclass* (`StarkSound.extract`,
`CircuitSoundness.lean:482-487`, IS "verify accept ⟹ ∃ Satisfied2 witness"). **It proves nothing
about the FRI verifier's soundness — it assumes it.** `#assert_axioms`-clean, over the carriers
`[StarkSound]`, `Poseidon2SpongeCR`, `CommitSurface` CR, `hrefines`, `WitnessDecodes`.

- **The ledger never touches the apex — confirmed structurally.** The files carrying the proven FRI
  numbers (`FriLedgerSound.lean`, `DeployedProximitySoundness.lean` — the 61/73/109/2^-31 columns) are
  imported **only by `Dregg2.lean`** (the build-all aggregator) — dead leaves. They do not feed the
  apex and do not discharge `StarkSound`/`FriLdtExtractV3`. Cell obligations gate on doc-rungs
  "`verifyBatch accept ⟹ X`" (`cell/src/obligation_standing.rs:99`, `escrow_sealed.rs:83`,
  `vault.rs:105`) — conditional on the assumed floor. (The legacy trusted-signer/bare-hash
  `TurnExecuted` path is retired; commit binds `TurnProven` to a real `verify_vm_descriptor2`,
  `turn/src/conditional.rs:224`.)
- **Freshness is OUT of the apex.** It proves ONE transition at a given `pi.turn`; nothing about
  replay/ordering (`CircuitSoundness.lean:412-435`). Freshness rests on the deployed commitment-chain
  CAS + nonce monotonicity — the **trusted Rust set-scan of §3** (`apply.rs:1237`), not the proof.
- **Per-effect family bottoms on a `WitnessDecodes`-class limb-decode carrier the ledger cannot
  certify** (the ledger root never mentions the trace columns), realized for **honest provers only**;
  the groundings **never compose** into one theorem carrying the minimal floor.

### 5c. `verify_history` and the app-root weld — real proof-verify + a DRIVEN equality

- **`verify_history` verifies a REAL recursive STARK/FRI proof — not re-execution, not a hash-chain.**
  `lightclient/src/lib.rs:189` → `verify_turn_chain_recursive` → `verify_recursive_batch_proof_with_
  config` → `verify_vm_descriptor2` → the Plonky3-fork `verify_batch`. Its doc is explicit: "It does
  not re-execute any turn, re-hash any state, or inspect any per-turn leaf" (`:180-183`); the one
  caveat, in-code (`:45-50`), is that FRI/recursion soundness (`EngineSound.recursive_sound`) is a
  **named assumption** (`RecursiveAggregation.lean:121`, a `structure … : Prop`). The node path
  `tool_compress_history` runs the same teeth. **Distinct** are the `verify_chain` family
  (`turn/src/verify.rs:140`, `dregg-agent/src/receipt.rs:327`) — **hash-chain + Ed25519 only**, "not
  content verification" — and `spween-dregg/src/verify.rs:123 verify_by_replay`, the one path that
  genuinely **re-executes** (trusted-Rust).
- **The app-root weld's actual equality is DRIVEN-to-deployed.** The keystone `published R ==
  committed field[K]` is an **in-circuit equality constraint** `cb.connect(ev[…], cs[…])`
  (`circuit-prove/src/joint_turn_recursive.rs:538-546`), wired on the live turn path
  (`ivc_turn_chain.rs:3119`), used by a real app (`dregg-multiway-tug/src/fold.rs:430` forces
  `PI[offset] == field[7] == winner`) and shown LC-visible through `verify_history`
  (`fold_real_cell.rs:276`, with a canary pinning the refusal to the weld). A disagreeing root ⇒ UNSAT
  ⇒ no verifying proof exists. It is a **constraint, not a Lean theorem and not a host `assert_eq`**.
- **Lean proves only the commitment-backing half (PROVEN-TO-MODEL).** `CustomBindingFromFold.lean:147`
  shows a verifying aggregate forces `∃ q, verify q ∧ piCommit q = f.c` under the named
  `CustomLeafFriFloor` + `Poseidon2SpongeCR` floors — but models "connect" abstractly as
  `leafCommit = c`, **not** the deployed `R == field[K]` octet equality. There is **no machine-checked
  theorem over the emitted object stating `app_root == field[K]`**; the multi-turn weld
  (`EngineSoundOfApex.lean`) leaves the per-leaf endpoint binding a **named** `apexLowers` field,
  realizable only on the transfer arm, and consumes the assumed `[StarkSound]`.

---

## 6. THE LOAD-BEARING UNVERIFIED (floors · trusted-Rust · named bridges)

**Terminal crypto floors (correctly named, `Prop`-carriers not `axiom`s):** the FRI/STARK extraction
`StarkSound` — and beneath it `FriLdtExtractV3`, which is **assumed as a hypothesis and never
discharged** (§4b), with a **discovered non-uniform-sampling defect** (`sampleBits % 2^logN` over
odd-order BabyBear) that no theorem accounts for — plus `Poseidon2SpongeCR`, `CommitSurface`/
`Compress8CR` CR, `FriExtract`, the PortalFloor kernels, `Ed25519EufCma`/`SchnorrDLHard`/BLS
carriers, and the hash-injectivity hypothesis under the receipt chain law. The proven combinatorial
FRI bounds (~31-bit and the 61/73/109/130 columns) are **disconnected leaves** that never discharge
these carriers. The whole metatheory has exactly two `axiom`-keyword decls, both inert demo fixtures;
zero `sorry` (`TRUST-BASE-CENSUS.md` §1).

**Trusted-Rust the running system depends on (no proof):**
- The **entire classical forest executor** — authority, conservation (`excess==0`), fee, receipt —
  is `EXECUTOR-TRUSTED` Rust (`mod.rs:5-32`; no `execute = recKExec` theorem).
- **Runtime freshness / double-spend** = the in-memory nullifier set-scan (`apply.rs:1237`).
- **Public-input plumbing** on the sovereign proof path (OLD/NEW/height from storage/claim).
- The **`verify_batch` ≡ `verifyAlgo`** and **producer ≡ descriptor** edges (DRIVEN batteries/roundtrips).
- **No runtime VK/descriptor attestation** — "VK distribution = git push + client rebuild"
  (`TRUST-BASE-CENSUS.md` D4); a client built against divergent descriptors verifies the wrong circuit.

**Named bridges / seams the record flags:**
- **S5 — turn auth Ed25519 verified OFF-circuit** (`authorize.rs`); only a Schnorr/BabyBear^8
  stepping-stone is in-circuit. A ledgerless client **cannot conclude the rightful agent signed THIS
  turn** — the largest light-client trust surface. terminal-by-design.
- **S3/D5 — `transferCapOpenTB` ~31-bit LC binding** — the sole cap-open key with no wide twin; the
  transfer's `(actor,src,dst)` identity is bound at ~31 bits, below the FRI floor. ATTACK-SURFACE
  (bounded to identity; close = wide-twin grind).
- **S4 — cross-cell Σδ=0 not live-enforced** (`turn_proving.rs`, `conservation: None`) — proven in
  Lean/AIR, deployed path proves per-cell-isolated; a ledgerless client is not shown turn-wide balance.
- The **C0 carrier residual**: every `*_binding_from_fold` rests on `SatXFold.connect`/`hfri`/`hbacks`
  as **assumptions**; "deployed aggregate ≡ fold model" lives in unverified Rust, and the deployed
  per-row AIR alone is **fail-open** (`*BackingAttack.lean` `forged_deployed_accepts`) — only the fold
  *model* rejects (`TRUST-BASE-CENSUS.md` §2).

---

## 7. MIRRORS / LARP STILL STANDING

1. **The `RecordProgram` model evaluator (signed-`Int`) is a parallel-disconnected copy Rust never
   links or calls** — not `@[export]`-ed, not in the FFI splice. The **dungeon** admission-soundness
   proofs run over it, and it provably diverges from the deployed unsigned-256 evaluator on negative
   scalars. It is **honestly labeled a model** (`DungeonProgram.lean:52-72`), not laundered — a
   transparently-scoped parallel model, but the dungeon's "deployed-teeth soundness" does not reach
   the deployed object. (The *pure subset* was re-homed into `DeployedConstraint`, which tug reaches;
   the dungeon has not.)
2. **The rotated LAYOUT mirror** — the app-root weld ("published R == cell real field") and the octet/
   completion-lane placements are the highest-blast-radius hand-encodings; a wrong lane is either a
   silent soundness hole ("a forged winner passes") or a fought-for-hours UNSAT
   (`CIRCUIT-LEAN-BOUNDARY.md` §1.3; the exemplar `fold.rs:384-386 reg("winner")-3` +
   `app_root_pi_offset: 17`, guessed wrong three times). At HEAD `layout_generated.rs` IS emitted from
   Lean and read by the producer, but its drift protection is **indirect** (coupled through descriptor
   bytes, §4a): a layout reshuffle no descriptor reads can install silently, and Lean's
   proven-disjoint `groupTable` projection is **not wired to the emit** (`RotatedLayout.lean:119-121`).
   The specific limb-37/38 REVOKED-ROOT soundness bug physically lived here.
3. **M35 — `sdk-py/python/dregg/pg_workflow.py:135` idempotency key is inert.** The durable-workflow
   crash-resume dedups on raw signed-turn bytes, not the advertised `idempotency_key`; a regenerated
   turn (fresh nonce) re-charges — the exact double-charge the override claims to prevent. Medium,
   false-claim, still standing (`RE-AUTHORED-MIRROR-MAP-3.md` M35). Bounded (re-charge, never lost step).

**Refuted mirror predictions (for the record):** the light-client trust roots are the *most*-defended
surface (all six bridge/chain verifiers carry/delegate to the canonical authority); the Go apex-VK
"mirror" is a fail-closed weak-subjectivity anchor (drift = liveness, not soundness); the setField
written-slot "silent forge" was refuted (the deployed freeze binds — it is a *completeness* seam).

---

## 8. THE STRANGER-CAN-VERIFY-TODAY LINE

A stranger holding a state root and an accepted proof, re-executing nothing and trusting no one,
can conclude — **conditional on the crypto floor (§6) and on trusted-Rust PI plumbing** — that:

> the accepted batch decodes to **one** real kernel transition whose pre/post endpoint commitments
> ARE the published public inputs, over a **Lean-authored AIR** whose bytes are drift-gated to the
> Lean source; and for the **tug** game specifically, that the deployed pure-subset evaluator admits
> exactly the legal-forward play-teeth.

It **dead-ends** immediately after:

- **at the FRI floor** — the stranger runs a **trusted-Rust Plonky3 `verify_batch` Bool calculator**
  on a supplied proof; what its `accept` *means* is a PROVEN-TO-MODEL implication strictly conditional
  on the **assumed, undischarged** `StarkSound`/`FriLdtExtractV3` extraction. The only fully-proven,
  no-carrier number is ~31 bits, and it bounds the *verifier's own uniform sampling* against a fixed
  far word — with the deployed sampling itself provably non-uniform. The richer 61/73/109/130 numbers
  are calculator columns on disconnected leaves; the `verify_batch ≡ verifyAlgo` edge is a tamper
  battery, and `verifyAlgo`'s concrete Lean instance stubs 3 of its 5 checks.
- **at freshness** — the apex is single-transition; replay/ordering rest on a **trusted Rust nullifier
  set-scan**, not the proof. A stranger cannot conclude "this note was unspent."
- **at authorization** — turn auth is **Ed25519 off-circuit**; a stranger cannot conclude "the rightful
  agent signed THIS turn."
- **at cross-cell conservation** — the deployed path proves per-cell-isolated; a stranger is not shown
  turn-wide Σδ=0.
- **at the ~31-bit surfaces** — `transferCapOpenTB` identity and the flat-mem lane-0 twins bind below
  the soundness floor (grindable, bounded to identity).
- **at the executor** — the *classical* forest turn (the common path) is executor-trusted Rust; only
  the *sovereign rotated proof* path carries a real STARK, and even it trusts its PI plumbing.
- **for the dungeon** — the "deployed-teeth soundness" theorems are over a signed-`Int` model, not the
  running evaluator.

**In one sentence:** today a stranger can verify *the authenticity of a single AIR-shaped state
transition, modulo a named FRI assumption and trusted-Rust public inputs* — and that is the whole of
it; everything a real system also needs (freshness, the right signer, cross-cell balance, the
common-path executor, and the dungeon's soundness) is trusted Rust, a named seam, or a model.
