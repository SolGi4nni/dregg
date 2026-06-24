# Executor Completeness Gap Map

> Honest, code-grounded map (2026-06-06) of the distance between the verified Lean
> executor `Dregg2.Exec.FullForestAuth.execFullForestG` (production FFI entry
> `dregg_exec_full_forest_auth`, `Dregg2/Exec/FFI.lean:3324`) and a COMPLETE,
> verifiable-execution Dregg node core.
>
> Read CODE not comments. Every claim cites file:line. Maintainer's correction is
> CONFIRMED: `execFullForestG` computes state transitions over a rich effect set, but
> it does NOT execute full protocol semantics and there is NO prover/verifier wired to it.

---

## 0. What `execFullForestG` actually is (verified facts)

- It is a per-node FAIL-CLOSED gate (`gateOK`, `FullForestAuth.lean:462`) in front of
  `execFullA`, run over a `FullForestG` call-forest, all-or-nothing
  (`execFullForestG`, `FullForestAuth.lean:506`).
- The production FFI entry wraps it as `runGatedForestTurn ctx hdr s0 gforest`
  (`FFI.lean:3339`), which is `Admission.runTurn ctx h s (execFullForestG · forest)`
  (`TurnAdmission.lean:30`) — i.e. a REAL turn prologue (fee-debit + nonce-tick,
  never-rolled-back) THEN the gated forest body.
- The executed action sum `FullActionA` has **~56 constructors**
  (`TurnExecutorFull.lean:3203`–`3260`+): transfers, mint/burn, delegate/revoke/introduce/
  attenuate, setField/setPermissions/setVK/incrementNonce/emitEvent, escrow (plain +
  committed), obligation, note spend/create, bridge lock/finalize/cancel, seal/unseal,
  makeSovereign/refusal/receiptArchive, queue alloc/enqueue/dequeue/resize/atomic/pipeline,
  sturdyref export/enliven/swiss-handoff/drop, cell seal/unseal/destroy, refreshDelegation.
  The wire codec (`FFI.lean §W4`, line 1577) transports **all 51 arms** with typed args.
- The state it operates on, `RecChainedState.kernel : RecordKernelState`
  (`RecordKernel.lean:442`), carries: `accounts, cell, caps, escrows, nullifiers,
  revoked, commitments, bal`. So escrow side-tables, the nullifier set, the revocation
  registry, and the note-commitment set ARE welded into executed state.

So the old "0/51 effects executed; circuit is the only model" memory is OUTDATED — the
effect-execution axis is now substantially real. The gaps are elsewhere.

---

## AXIS A — SEMANTIC COMPLETENESS GAPS

Prioritized; load-bearing first.

### A1. [LOAD-BEARING] The cap-authority leg (`capAuthorityG`) is admit-by-construction over the production wire
- **What:** The gate is `credentialValid && capAuthorityG && caveatsDischarged &&
  revocationGate` (`gateOK`, `FullForestAuth.lean:462`). `capAuthorityG` dispatches the
  rich `authModeAdmits` (`granted ≤ held`, the CapTpDelivered attenuation). But the
  production wire pins every node's `capMode := .unchecked (Guard.all [])` and a fixed
  `baseCapCtx` (`GatedForestCfg.lean:103`–`106`, used by `FFI.lean:3290 mkGAuth`).
  `.unchecked (Guard.all [])` makes `authModeAdmits = true` for ALL inputs.
- **file:line:** `GatedForestCfg.lean:105` (`capMode := .unchecked (Guard.all [])`),
  `FFI.lean:3197`–`3204` (the comment admitting it: "the lift supplies the WHAT/caveat
  legs from ADMITTING defaults… `authModeAdmits = true` for all inputs").
- **Load-bearing?** YES. The WHO leg (credential) and caveat leg DO gate over the wire;
  but the entire `granted ≤ held` cap-attenuation theory — the thing the module advertises
  as "the CapTpDelivered gap dregg1's Rust misses, modeled CORRECT" — is PROVED in Lean but
  NEVER EXERCISED by the production entry. A real node must transport `capMode`/`capCtx`
  per node and route them, or the WHAT leg is decorative at the boundary.

### A2. [LOAD-BEARING] Fee is debited but credited to no one — no fee distribution / treasury / validator payout
- **What:** `commitPrologue` subtracts `fee` from the agent cell and bumps its nonce
  (`prologueCell`, `Admission.lean:216`; `commitPrologue`, `Admission.lean:222`). It edits
  ONLY the agent cell — no validator/treasury/silo credit. The fee is effectively burned.
- **file:line:** `Admission.lean:216`–`225`. `commitPrologue_balance`/`_nonce`
  (`Admission.lean:229`) confirm the only edit is `bal -= fee, nonce += 1` on the agent.
- **Load-bearing?** YES for a real node with an economic model. Total-conservation is
  therefore NOT preserved across the prologue (the fee leaves circulation) — the
  conservation theorems are about the BODY (`execFullForestG` over `eraseG f`), not the
  prologue. Whether burn-vs-distribute is intended is a protocol decision, but right now it
  is a silent burn with no distribution edge.

### A3. [LOAD-BEARING] No consensus / finalization is wired into the executor
- **What:** `Consensus.lean` builds a `NetCell` quorum→Finality.Tier bridge
  (`Consensus.lean` header, theorems `quorum_reaches_bft_tier` etc.), and `World.lean`
  carries the abstract `committedByQuorum`. But NOTHING references `execFullForestG`,
  `RecChainedState`, or `dregg_exec_full_forest_auth` from the consensus modules — it is a
  SEPARATE algebraic layer over its own `NetCell`/`Tier` types.
- **file:line:** `Consensus.lean` (no `execFullForestG`/`RecChainedState` references — grep
  confirms). The header itself states Byzantine quorum-intersection safety and post-GST
  liveness are left as open `…_OPEN` theorems in `World.lean`.
- **Load-bearing?** YES. A real node must: place each committed turn into a block, track
  height/epoch/checkpoint, gather quorum, and only then finalize. `execFullForestG` has no
  block height (the `AdmCtx.blockHeight`/`admissionClock` exists in `Admission.lean:135`–
  `146` for valid-until clamping ONLY), no epoch, no checkpoint, no finalization hook, and
  no DAG/blocklace ordering. The dregg1 memory note (Cordial-Miners DAG + Stingray) is the
  real protocol; none of that orders these turns.

### A4. [LOAD-BEARING] Higher privacy tiers are an unwelded algebraic layer (only nullifier double-spend is welded)
- **What welded:** `noteSpendA`/`noteCreateA` operate on `RecordKernelState.nullifiers` /
  `.commitments` via `execFullA`, and `PrivacyTheorems.lean` proves no-double-spend OVER the
  executed `RecChainedState` (`chainNoteSpend_no_double_spend`, `PrivacyTheorems.lean:84`;
  `nullifier_set_monotone:117`; `nullifier_persists:139`). That IS real and welded.
- **What NOT welded:** `Privacy.lean` and `PrivacyKernel.lean` define a SEPARATE Zcash-style
  algebraic model (`Note`/`Nullifier`/spent-set, `Privacy.lean:315`–`328`, `namespace
  Dregg2.Privacy`) with anonymity, value-commitment hiding, and
  anonymity⊗nullifier-reconciliation theorems — over its OWN types, NOT `RecChainedState`.
  No `RecChainedState`/`execFull*`/`gateOK` references appear in `Privacy.lean`.
- **file:line:** `Privacy.lean:58, 315–328` (own types); `PrivacyTheorems.lean:84`
  (the welded double-spend tooth).
- **Load-bearing?** PARTIAL. Double-spend prevention is enforced by the executor. But the
  ACTUAL hiding (commitments hide value, nullifiers unlinkable, shielded value-balance) is
  NOT enforced over executed state — `noteCreateA cm` just inserts a `Nat` `cm` with no
  range-proof / value-commitment binding in the executor (the binding is a "§8 CryptoPortal"
  Prop-carrier, `RecordKernel.lean:463`). A real shielded node needs the value-commitment
  conservation welded, not just the spent-set.

### A5. [MEDIUM] Caveats are within-cell only; cross-cell (coordinated) caveats fail-closed, not executed
- **What:** A `.coordinated` (tier-3) caveat fail-closes intra-cell (`GatedCaveat.holds`,
  `FullForestAuth.lean:233`: `| .coordinated => false`). It is "routed to `CrossCaveat`" —
  but the production turn entry `execFullForestAuthStep` runs `runGatedForestTurn`, which
  does NOT invoke any `CrossCaveat.jointApplyCaveated`. So a coordinated caveat over the
  production wire is simply a hard reject, never actually discharged across cells.
- **file:line:** `FullForestAuth.lean:233`–`236`; `FFI.lean:3447`–`3449` (the eval admits
  coordinated "fail-closes by routing to CrossCaveat even though its bound trivially holds").
- **Load-bearing?** MEDIUM. Single-machine-correct (fail-closed is safe), but a node that
  needs genuine cross-cell coordinated conditions cannot express them through this entry.

### A6. [MEDIUM] Forest delegation handoff: edges run the cap-attenuation spine, but gated children inherit only the default capCtx
- **What:** `execFullChildrenG` DOES run a real delegation handoff —
  `execFullAGated s sub.auth (delegateAttenA delegator holder t keep)` on the
  `recCDelegateAtten` spine (`FullForestAuth.lean:520`–`528`). This is BETTER than the
  earlier "decorative delegation" memory (that audit was about `execFullChildrenA`/`G`
  discarding edges — the current code routes them onto `delegateAttenA`). The remaining gap
  is A1's: each child's `sub.auth.capMode` is the admitting default over the wire, so the
  attenuation edge runs but `granted ≤ held` is not gated at the boundary.
- **file:line:** `FullForestAuth.lean:520`–`528` (real handoff); `FFI.lean:3301`
  (`liftChildrenG` keeps delegation data but `mkGAuth` supplies admitting `capMode`).
- **Load-bearing?** MEDIUM — the structural handoff is real; the authority refinement on it
  is not exercised at the wire (same root cause as A1).

### A7. [LOW/INFO] Joint / cross-vat / cross-cell forest execution is a separate module, not in the production turn entry
- **What:** `JointCell.lean`, `CrossVatCharter.lean`, `CrossCellForest.lean`,
  `VatBoundary.lean`, `JointCharterBridge.lean` exist as their own modules. The production
  entry `execFullForestAuthStep` runs ONE `DForest` (a single agent's call-forest), not a
  joint/multi-party turn. There is no `JointTurn` over the FFI.
- **file:line:** `FFI.lean:3324`–`3343` (single forest, single agent header).
- **Load-bearing?** LOW for a single-machine n=1 node (per the dregg4 single-machine
  principle memory), but a real multi-vat node needs joint turns at the boundary.

### A8. [INFO] Per-effect semantic divergences from dregg1 (the handler audit findings)
- The handler-executor maps `makeSovereign`/`refusal`/`receiptArchive` onto a GENERIC
  live-gated `stateWriteH` (`HandlerExecutor.lean:166`–`167, 229`–`234`). These are
  flag/lifecycle writes modeled as generic field writes — faithful-enough for state but
  they do NOT carry dregg1's full lifecycle side effects (e.g. sovereign-cell proof-carrying
  enforcement lives in the Rust `execute.rs:222`–`238` `ProofCarryingRequiresSovereign`
  path, which has NO Lean analog).
- `queueAllocate`/enqueue/dequeue have real Lean semantics over a queue side-table, but the
  pipelined/atomic-tx arms are the most likely divergence surface (not audited line-by-line
  here).
- **Load-bearing?** Mostly INFO — the executed state transition is defined; the divergence
  is in lifecycle/proof-carrying obligations that the classical Lean path does not model.

---

## AXIS B — PROVER / VERIFIER INTEGRATION

The target: per turn, executor computes the transition (HAS) → emit witness/descriptor →
run plonky3 prover → attach proof; on receipt, verify incoming proofs → gate.

### State of the world (skeptic's read)

**There is NO "execute → prove" path and NO "verify → accept" path wired to
`execFullForestG`. Not in Lean, not in Rust.** The pieces exist but are disconnected on
three different state models.

#### B1. The Lean circuit covers a TOY micro-core, not the executed forest
- `Circuit.bridge : satisfied kernelCircuit (encode s t s') ↔ fullStepInv s t s'`
  (`Circuit.lean:213`) is over `ChainedState`/`Turn` (the OLD micro-core), NOT
  `RecChainedState`/`FullForestG`.
- `kernelCircuit` is **4 scalar constraints** (`Circuit.lean:136`): `cConservation`
  (totalPost = totalPre), `cAuthority` (authBit = 1), `cChainLink` (chainOk = 1),
  `cObsAdvance` (lenPost = lenPre + 1) — `Circuit.lean:118`–`132`. It does NOT mention
  per-asset balances, escrows, nullifiers, caps, revocation, or any of the ~56 effects.
- `encode` (`Circuit.lean:106`) maps a `ChainedState` to ~5 scalar variables. There is no
  witness generator from `RecChainedState`'s 8-field state-delta.
- **Gap:** the circuit and the executor are over DIFFERENT, incompatible state types. The
  `bridge` is real but proves a 4-gate toy, not the forest transition.

#### B2. `CircuitEmit` emits the toy circuit, not the forest transition
- `EmittedDescriptor`/`emit`/`emit_faithful` (`CircuitEmit.lean` header) serialize
  `Circuit.kernelCircuit` (the 4-gate `ConstraintSystem`) to a wire the Rust
  `circuit_decode.rs` re-parses and fingerprint-checks against a native AIR.
- `CircuitEmit.lean` references `Dregg2.Circuit` / `Circuit.Lookup` / `Crypto.Merkle` —
  NOT `execFullForestG`, `RecChainedState`, or any forest transition.
- **Gap:** the emit path carries the proved-faithful TOY descriptor. Nothing emits a
  descriptor/witness for the actual `execFullForestG` state delta.

#### B3. The Rust executor is proof-AGNOSTIC and does NOT call the Lean FFI on the live path
- `turn/src/executor/execute.rs:957`–`960`: *"We intentionally do NOT prove inside
  `execute` (the executor remains proof-agnostic on the classical path)."*
- The Lean FFI is invoked ONLY as a SHADOW differential, gated on `DREGG_LEAN_SHADOW=1`
  (`execute.rs:55`–`57`, `lean_shadow.rs` header: *"compares Rust commit decisions against
  the verified Lean kernel without affecting `TurnResult`"*). The Rust executor is the real
  executor; Lean is a side-channel oracle. (This matches THE SWAP memory: 0 call-sites call
  the Lean FFI to BE the executor.)
- `dregg-lean-ffi/` is entirely DIFFERENTIAL/cross-validation (`differential.rs`,
  `full_turn_differential.rs`, `circuit_differential.rs`, `state_differential.rs`,
  `marshal_roundtrip.rs`) — none of it proves; it cross-checks codec + Rust reference vs
  the proved Lean semantics. `full_turn_differential.rs:24`–`26` explicitly disclaims:
  agreement does NOT mean either side carries proofs.

#### B4. The ONLY real prove site is the MCP demo path, over a 2–3-effect toy VM
- The canonical prove site is `node/src/mcp.rs::generate_effect_vm_proof`
  (`execute.rs:949`–`950` points to it). It builds an `EffectVmAir` and calls
  `dregg_circuit::stark::try_prove` (`mcp.rs:260`–`262`), then wraps a `WitnessedReceipt`.
- But `project_effects_for_mcp` (`mcp.rs:277`–`304`) only maps **Transfer, SetField,
  IncrementNonce→NoOp** and DROPS every other effect (`_ => {}`, `mcp.rs:300`). So the prove
  path covers ~2 effect kinds of the ~56, and is an MCP-tool demo, not the turn executor.
- `circuit/src/plonky3_prover.rs:611 prove_plonky3` is a real plonky3 STARK prover, and many
  per-feature AIRs exist (`note_spending_air`, `effect_vm_p3_air`, `bridge_action_air`,
  `lean_descriptor_air`, etc.). They are real circuits but each is a feature-specific island;
  none is driven by `execFullForestG`'s output.

#### B5. The verify-and-accept path exists in Rust but is per-feature, not per-turn-transition
- `proof_verify.rs` has rich verifiers: `verify_and_commit_proof:27`,
  `verify_sovereign_witness_stark:531`, `verify_proof_carrying_turn_bundle:656`,
  `verify_effect_binding_proofs:847`, `verify_bilateral_bundle:1457`,
  `verify_bundle_with_stark:1663`. These verify SPECIFIC proof-carrying bundles
  (sovereign cells, effect-binding, bilateral) — NOT "verify the STARK that this turn's
  whole-state transition was computed correctly." There is no `verify(turn_transition_proof)`
  gating admission of an incoming turn's full delta.

### The concrete path to "execute → prove / verify → accept"

What EXISTS:
- A real plonky3 STARK prover (`plonky3_prover.rs:611`) + many AIRs.
- A faithful Lean→Rust descriptor emit + fingerprint binding for the TOY circuit
  (`CircuitEmit` + `circuit_decode.rs`).
- A `WitnessedReceipt` carrier (`turn/src/witnessed_receipt.rs`) ready to hold
  trace+PI+proof.
- Per-feature verifiers in `proof_verify.rs`.

What is MISSING (the wiring, in order):
1. **A real transition circuit over `RecordKernelState`.** Replace the 4-gate toy
   `kernelCircuit` with constraints over the executed 8-field state delta (per-asset bal
   conservation, escrow/nullifier/commitment/revoked set updates, cap-graph edges). This is
   the single biggest missing piece — the circuit must speak the executor's state language.
2. **A witness generator from `execFullForestG`'s delta.** Given `s, gforest, s'`, emit the
   trace/assignment the new circuit verifies. Today `encode` (`Circuit.lean:106`) only
   handles the toy `ChainedState`.
3. **Descriptor → AIR → prove.** Route the new descriptor through the EXISTING
   `CircuitEmit` → `circuit_decode.rs` fingerprint binding → `plonky3_prover.rs:611`.
   The fingerprint discipline already exists; it just points at the toy AIR.
4. **proof → verify → gate.** On receipt, verify the transition proof and make it a
   PRECONDITION of admission (a 5th leg beside `gateOK`/`Admission.admissible`), analogous to
   the existing `verify_and_commit_proof` but over the whole-turn transition.
5. **Make the Rust executor call it (or make Lean the executor).** Either the Rust executor
   proves on commit (remove the "proof-agnostic" stance, `execute.rs:957`) or the SWAP lands
   (FFI the gated Lean executor in to BE the executor) and the prove hook hangs off that.

---

## VERDICT — how far is `execFullForestG` from a real verifiable-execution node core?

**Effect-execution: ~70% of the way (much further than older notes claim).** It executes a
~56-constructor effect set over a real 8-field kernel state with escrows, nullifiers,
commitments, and a revocation registry, gated by a real fail-closed credential portal +
caveats + revocation + a real never-rolled-back fee/nonce prologue, with conservation /
non-amplification / attestation / no-double-spend PROVED. This is a genuine state-transition
engine.

**Protocol semantics: ~40%.** The cap-authority leg is admit-by-construction at the wire
(A1); fees are burned with no distribution (A2); there is NO consensus/finalization/
block/epoch/checkpoint wiring (A3); shielded value-hiding is unwelded (A4); cross-cell and
joint turns are not in the production entry (A5/A7).

**Prover/verifier: ~5%, and DISCONNECTED.** There is no execute→prove or verify→accept path
for the actual transition. The Lean circuit is a 4-gate toy over a different state type; the
real prover is an MCP-demo over 2–3 effects; the Rust executor is deliberately proof-agnostic
and only shadows Lean. The "verifiable" in "verifiable-execution" is NOT realized.

**Net: `execFullForestG` is a strong, proof-carrying STATE-TRANSITION CORE, but it is not yet
a verifiable-execution NODE.** It lacks (a) a prover that attests its own transitions, (b) a
verifier that gates on incoming transition proofs, and (c) consensus/finalization to order
turns. The crown-jewel "circuit ⟺ protocol" soundness is absent for the forest transition —
the proved bridge is over the abandoned micro-core.

---

## HIGHEST-LEVERAGE NEXT BUILDS

1. **Transition circuit over `RecordKernelState` + witness generator from `execFullForestG`.**
   (B1+B2 root cause.) Without a circuit that speaks the executor's state, nothing downstream
   can prove the real transition. This is THE crown-jewel beachhead per the
   conservation-≠-correctness memory: a full-state commitment (`recStateCommit` injective +
   authenticated root) so the witness pins ALL 8 state fields, with an anti-ghost tooth
   (tamper a 3rd cell/caps/nullifier ⇒ UNSAT). Start with ONE effect end-to-end (transfer),
   then the per-asset conservation gate, on the REAL state type — not the toy.

2. **Exercise the cap-authority leg at the wire (A1).** Transport `capMode`/`capCtx` per node
   through the codec and route them into `capAuthorityG` so the PROVED `authModeAdmits`
   (`granted ≤ held`) actually gates. Cheapest high-value fix; the theory is already proved,
   it is purely a codec + lift change in `GatedForestCfg.mkAuth`/`FFI.liftForestG`.

3. **Decide + wire fee distribution (A2).** Even a single treasury-credit edge in
   `commitPrologue` closes the silent-burn gap and restores a stated conservation invariant
   across the prologue.

4. **A verify→accept leg.** Add a transition-proof verification as a precondition beside
   `Admission.admissible` (reuse the `proof_verify.rs` discipline), so incoming turns are
   gated on a proof of correct execution — the receipt side of #1.

5. **Weld shielded value-conservation (A4).** Bind `noteCreateA`'s commitment to a value via
   the §8 range-proof portal so the commitment set carries value, making shielded balance a
   conserved quantity over executed state (not just a spent-set anti-replay).

(Consensus/finalization, A3, is the largest piece but is gated on the proof-system decision
in the reorientation memory — pickles vs plonky3-recursion — so it should follow #1, not
precede it.)
