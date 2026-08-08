# Rust-only logic census — what to Lean-ground next

A TCB-shrinking census. The question: *what logic is implemented ONLY in Rust (no Lean
spec/proof) where a bug could break SOUNDNESS — i.e. cause a light-client / verifier to
**falsely accept** something untrue?* That set, and only that set, is the answer to "what
should we Lean-ground next." Everything else is named honestly and set aside.

This is a point-in-time census (2026-06-26) verified against code at HEAD. Where a claim is
"audited / differential / pinned" rather than "proven," it says so. Read the code at the cited
`file:line`; memories and prose drift, the code is the state.

## The classification

Applied to each Rust-only piece:

- **SOUNDNESS-CRITICAL (in the TCB)** — a Rust bug → a **false accept** (the light client /
  verifier accepts something untrue). MUST be Lean-grounded. *These are the answer.*
- **FAILS-CLOSED (liveness / completeness)** — a Rust bug → fails-closed / can't-prove /
  rejects-honest. By STARK soundness or commitment re-binding, a bad witness or wrong
  selection just won't verify. Name them; lower priority; not TCB.
- **OUT-OF-SCOPE** — stores, UI, networking, dev tooling, and the executor/federation-side
  surfaces the light client never trusts. Not soundness.

A fourth label that recurs below: **TERMINAL CRYPTO FLOOR** — a named, by-design assumption
(Poseidon2 collision-resistance, FRI/STARK soundness). Not a reducible Rust-only gap and not
the answer; called out so it isn't mistaken for one.

---

## The census

### 1. The deployed Rust executor — `turn/src/executor/{execute.rs,apply.rs,atomic.rs}`

**What it is.** The sole entry for ledger mutation: `TurnExecutor::execute`
(`turn/src/executor/execute.rs:210`), dispatching to `apply_effect`
(`turn/src/executor/apply.rs:27`) and ~33 per-effect arms (`apply_transfer:380`,
`apply_mint:2765`, `apply_burn:2547`, `apply_note_spend:917`, `apply_grant_capability:485`, …).
These decide whether a turn commits and produce the exact bytes the committed `.root()`
reflects. The code's own comments name the stakes: *"the sole entry point for all ledger state
mutations… If compromised: arbitrary state changes bypass authorization, preconditions, and fee
metering"* (`execute.rs:203`).

**Lean-status.** **NO `TurnExecutor::execute = recKExec` theorem exists.** The Rust executor is
not specified in Lean; only the *Lean* executor is, and it is proven `Exec ⊑ Spec`
(`docs/reference/lean-kernel.md:164`, `metatheory/Dregg2/Spec/ExecRefinement.lean`). The Rust↔Lean link is
**audited + differential parity**, not proven equality — stated outright at
`docs/RUST-LEAN-EXECUTOR-PARITY.md:20`. Evidence: the rejection-parity audit
(`exec-lean/tests/rejection_parity.rs`, hard-fails only the dangerous Rust-accepts-Lean-rejects
direction; aligned six under-enforcements) and the differential gauntlet
(`exec-lean/tests/rust_lean_parity_gauntlet.rs`, 17 effects byte-identical incl. `.root()`,
0 silent divergence over a corpus). Both self-skip when the Lean archive is unlinked.

**The SWAP factor (load-bearing).** There is a deployed
runtime inversion that makes the **verified Lean executor authoritative**, default-ON on native
builds: `produce_via_lean` (`exec-lean/src/lean_apply.rs:1402`) drives the turn through
`recKExec` via FFI and installs the Lean post-state + commit verdict *unconditionally*, demoting
Rust to a checked reference; a disagreement surfaces as `LeanAuthoritative { rust_agreed: false }`.
Gated by `lean_producer_env_enabled()` (`sdk/src/runtime.rs:35`, `node/src/state.rs:39`),
default `true` unless `DREGG_LEAN_PRODUCER` is off. The parity doc states the same inversion up
front (`docs/RUST-LEAN-EXECUTOR-PARITY.md:12`): on native builds the verified Lean executor is
the authoritative producer by default (`default = ["exec-lean"]`; opt out with
`DREGG_LEAN_PRODUCER=0`), with Rust as the differential cross-check and the wasm/zkvm producer.

But Rust is still load-bearing where the swap can't reach:
1. **wasm / zkvm builds** (`feature = "no-lean-link"`): the archive isn't linked,
   `lean_producer_env_enabled()` is hard-`false` (`sdk/src/runtime.rs:49`). The SDKs that
   compile to wasm run **pure Rust**.
2. **The uncovered partition.** The Lean producer is authoritative only on a ~21-effect
   root-agreeing covered set (`exec-lean/src/lean_shadow.rs`); turns that are unmappable or
   touch a root-gap effect (notably **Mint / BridgeMint**) fall back to the Rust path
   (`ProducerOutcome::Fallback`, `lean_apply.rs:1411`). There Rust is authoritative.

**Class: SOUNDNESS-CRITICAL (in TCB) — wherever Rust is authoritative.** An under-enforced gate
is fail-*open*: Rust commits a turn the kernel would refuse, the `.root()` is accepted as
genuine → false accept. Not fails-closed, not out-of-scope. The mitigating control
(rejection-parity hard-fail) is a *test-time* corpus gate, not a runtime or proof guarantee.

**To Lean-ground.** Two routes, either removes Rust from the TCB:
- **Route A (momentum, no new theorem):** close the swap to totality — bring every effect
  (Mint/BridgeMint…) into the root-agreeing covered set, and solve the link-weight/platform
  story so the Lean archive rides wasm/zkvm. Then `produce_via_lean` is authoritative everywhere
  and inherits the proven `Exec ⊑ Spec`.
- **Route B (the named open):** formally specify `TurnExecutor::execute` in Lean and prove
  `execute = recKExec` (`docs/RUST-LEAN-EXECUTOR-PARITY.md:108`). Structurally hard; lets the
  Rust path carry soundness without running Lean in production.

---

### 2. The state-commitment computation — `cell/src/commitment.rs`, `cell/src/state.rs`, `circuit/src/heap_root.rs`

**What it is.** The hashing that produces the root a light client / STARK verifier checks.
- Whole-cell canonical commitment (BLAKE3, kernel face): `compute_canonical_state_commitment`
  (`cell/src/commitment.rs:204`); felt-packing for the STARK public input
  `canonical_to_babybear_pi` (`cell/src/commitment.rs:635`, 8 BabyBear felts at ~30 bits each).
- Rotated Poseidon2 commitment (circuit / light-client face): `compute_rotated_pre_limbs`
  (`cell/src/commitment.rs`), the chained `wireCommit` (`cell/src/commitment.rs`) — now the v11
  8-felt `node8` geometry (~124-bit faithful; `docs/reference/faithful-commitment.md`, v9→v10→v11).
- Sorted-Poseidon2 leaf roots: `compute_heap_root` (`cell/src/state.rs:409`),
  `compute_fields_root` (`cell/src/state.rs:470`), `compute_canonical_capability_root`
  (`cell/src/commitment.rs:595`). The heap tree sorts leaves
  (`circuit/src/heap_root.rs:161`, `leaves.sort_by_key(|l| l.addr.as_u32())`) then folds a
  padded binary Poseidon2 Merkle (`CanonicalHeapTree::new`, `circuit/src/heap_root.rs:157`).
- Whole-ledger root: `Ledger::root()` (`cell/src/ledger.rs:777`).

**Lean-status.** The commitment *binding* is **Lean-modeled and proven** —
`recStateCommit_binds_kernel` (`metatheory/Dregg2/Circuit/StateCommit.lean:603`,
`#assert_axioms`-clean): equal full-state roots ⟹ equal whole `RecordKernelState`. But it binds
the **model**, conditional on abstract injectivity carriers (`cmb`/`CH`/`RH` collision-hardness).
It does **NOT** prove the deployed Rust `compute_canonical_state_commitment` /
`CanonicalHeapTree::root` / `canonical_to_babybear_pi` / v11 `wireCommit` *equal* `recStateCommit`.
That Rust↔model equality is established by **differential + KAT tests** over concrete values
(`circuit/tests/effect_vm_commit_lean_differential.rs` — explicitly "byte-identity of the
COMMITMENT HASH TREE against an independent Lean-limb re-fold, NOT executor agreement";
`heap_root_cell_circuit_differential.rs`; `poseidon2_cell_circuit_kat.rs`). There is also a
**structural gap**: Lean `Heap.root` is a sponge over a sorted leaf list; the Rust impl is a
binary Merkle tree with sentinels + empty-subtree padding — the model proves order-canonicity of
an *abstraction*, not the literal tree fold. The **sort** is modeled in Lean only as a
*predicate* (`sortedKeys`), not as the `sort_by_key` algorithm.

**Class: SOUNDNESS-CRITICAL.** The root these functions produce is exactly what the verifier
checks, and the whole unfoolability argument routes through `recStateCommit_binds_kernel` — sound
only if the Rust hashing computes the same function as the bound model. A bug in limb order /
nesting, the felt-packing, the sort comparator (signed-vs-unsigned, or a non-total tie-break
across `as_u32`-truncated addrs), or the sentinel/padding/dedup logic yields a root the verifier
accepts that does not correspond to the genuine kernel state → false accept. A malleable
commitment is an *acceptance* failure, not a rejection. (Note: the ~30-bit-per-limb packing in
`canonical_to_babybear_pi` is the "~124-bit faithful commit" floor that sits *under* every other
guarantee — measure it against FRI's ~130-bit soundness, per
`feedback-dont-launder-a-load-bearing-insecurity`.)

**To Lean-ground.** A refinement / verified-extraction proof that each deployed Rust commitment
function computes *exactly* `recStateCommit` / `Heap.root`; model the sort algorithm (prove
`sort_by_key(addr.as_u32())` realizes the canonical order and `addr.as_u32` is a total injective
key); reconcile the binary-Merkle vs sponge structural gap; and reconcile the BLAKE3 vs Poseidon2
faces. (The abstract CR carriers themselves are the terminal floor — §4.)

---

### 3. The wire codec — `wire/src/codec.rs`, `circuit-prove/src/ivc_turn_chain.rs`, verifier JSON

**What it is.** Postcard binary framing (`wire/src/codec.rs:79`/`:97`) and the verify-sufficient
proof envelope `WholeChainProofBytes` (`circuit-prove/src/ivc_turn_chain.rs:1357`, `from_postcard`
`:1417`); plus serde_json bundles on the verifier CLI side (`verifier/src/rotated_replay.rs:175`,
`verifier/src/bilateral_pair.rs:188`). The descriptor JSON parser is `parse_vm_descriptor2`
(`circuit/src/descriptor_ir2.rs`).

**Lean-status.** **Rust-only — no Lean model of postcard or serde_json.** What *is* Lean-anchored
is the descriptor JSON *emit* side (`emitVmJson2` / `EffectVmEmitRotationV3.lean`, FP-pinned at
`circuit/src/effect_vm_descriptors.rs:822`); the Rust *parser* that consumes it is unmodeled. So
emit ∈ Lean, parse ∈ Rust-only. Validation is fuzz/differential round-trip + FP pins
(`redteam/tests/wire_codec_fuzz.rs`), which per `feedback-byte-identity-differential-is-not-faithfulness`
proves drift-detection, NOT parse-faithfulness.

**Class: FAILS-CLOSED (architecturally), with one flag.** A verifier-side misparse **cannot**
false-accept on the light-client / STARK path, because every decoded soundness-relevant field is
**re-bound to a cryptographic commitment that is independently verified**: the whole-chain
envelope checks decoded publics against the in-circuit segment (`exposed != expected → reject`,
`ivc_turn_chain.rs:2898`; VK is the caller's anchor, never read from the envelope, `:2860`);
rotated legs are selector-bound to the FP-pinned descriptor with `vk_hash` re-derived
(`rotated_replay.rs:208`); receipt PI is checked-against-expected, not merely deserialized
(`verifier/src/lib.rs:420`). A misparse yields wrong felts that fail the equality → reject. The
residual proof-blob deserialization reduces to the standard FRI/STARK floor. **The one flag:** the
serde_json bilateral/aggregated bundles (`verifier/src/bilateral_pair.rs:188`) **re-run the
executor over decoded structures** rather than checking a STARK commitment — a misparse there
yields a verdict about a *different object*; worth watching if those bundles ever gate
state-acceptance.

**To Lean-ground.** Defense-in-depth, not a gap closure. Highest value: a Lean grammar for
`parse_vm_descriptor2` with `parse ∘ emitVmJson2 = id` (closes the loop on the one codec whose
content is already Lean-authored). Lower: a postcard field-projection-faithfulness model for the
load-bearing types.

---

### 4. Poseidon2 permutation + Merkle / cap-tree / nullifier-tree — `circuit/src/{poseidon2,merkle_types,cap_root,heap_root,non_membership}.rs`

**What it is.** A hand-rolled width-16 BabyBear Poseidon2 (`Poseidon2State::permute`,
`circuit/src/poseidon2.rs:215`, constants transcribed from `p3-baby-bear`), plus the trees:
4-ary Poseidon2 Merkle (`circuit/src/merkle_types.rs:13`, depth 16), the cap-reshape tree
(`CanonicalCapTree`, `circuit/src/cap_root.rs:279`; `compute_capability_root:647`,
`membership_witness:746`), the heap tree (`circuit/src/heap_root.rs`), and in-circuit nullifier
non-membership (`circuit/src/non_membership.rs`, `circuit/src/adjacency_witness.rs`).

**Lean-status.** The Poseidon2 permutation is an **ABSTRACT CARRIER**: `compress`/`compressN` are
uninterpreted with only a `collisionHard : Prop` law (`metatheory/Dregg2/Crypto/Primitives.lean`),
discharged at the real params via the named hypothesis `Poseidon2SpongeCR`
(`metatheory/Dregg2/Circuit/Poseidon2Binding.lean`). The real round constants are not evaluated in Lean; they live
as `rc_source: BABYBEAR_POSEIDON2_RC_16` consumed by the Rust prover. The sponge→permutation CR
reduction IS done (`Crypto/SpongeReduction.lean`, `#assert_axioms`-clean), shrinking the
irreducible primitive to "one fixed-width permutation is collision-resistant." The **trees are
MODELED**: cap-tree (`metatheory/Dregg2/Circuit/DeployedCapTree.lean`, `DeployedCapOpen.lean`, `CapRootBridge.lean`),
heap tree (`Substrate/Heap.lean`, `MapMerkleRoot.lean`), sorted non-membership
(`SortedTreeNonMembership.lean`) — with declared Rust twins and proven membership/non-amplification
gates. Permutation conformance to the audited Plonky3 reference is pinned byte-for-byte by KAT
(`poseidon2.rs:972`, cross-check vs `default_babybear_poseidon2_16`).

**Class: TERMINAL CRYPTO FLOOR (permutation) + already-modeled (trees).** Poseidon2's
collision-resistance is the named assumption, peer of FRI soundness — not a reducible Rust-only
gap and not the answer. The only Rust-bug surface (wrong constant / round / MDS) is the
conformance KAT's job, and it's pinned. The tree *construction / membership / non-membership*
logic — where a Rust bug could otherwise pass an invalid opening — all has Lean twins. **No
dregg-specific Rust-only soundness logic gap found in this subsystem.** (`cell/src/nullifier_set.rs`
is a separate BLAKE3 Rust-only set with no Lean model, but it is **OUT-OF-SCOPE**: executor /
federation / wasm side, the light client never trusts it.)

**To Lean-ground.** Not worth further grounding the permutation (proving Poseidon2's own security
argument is what nobody does in-prover; the conformance KAT already discharges the only Rust bug
surface). The terminal residual — one fixed-width-permutation `CompressionCR` — is the carrier,
not a TODO.

---

### 5. Verifier orchestration glue — `sdk/src/full_turn_proof.rs`, `turn/src/executor/proof_verify.rs`, `lightclient/src/lib.rs`

**What it is.** The Rust logic that picks *which descriptor/VK a proof verifies against*: the
rotated cutover (`verify_effect_vm_rotated_with_cutover`, `sdk/src/full_turn_proof.rs:4312`),
cohort-run splitting (`split_into_cohort_runs`, `sdk/src/full_turn_proof.rs:3802` +
`turn/src/executor/proof_verify.rs:45`), descriptor resolution by name
(`circuit/src/effect_vm_descriptors.rs`), the leg-chain adjacency checks
(`proof_verify.rs:631-657`, `full_turn_proof.rs:5062-5184`), the recursion driver
(`circuit-prove/src/ivc_turn_chain.rs`), and the light-client driver (`lightclient/src/lib.rs:183`).

**Lean-status.** Rust-only **glue**, but the *bindings it enforces* are grounded: every rotated
proof is descriptor-bound by Fiat-Shamir, so a wrong descriptor selection diverges the transcript
→ FRI fails → reject. The chain-binding soundness lives **in-circuit** (`TurnChainBindingAir`,
Lean `binding_sound` / `light_client_verifies_whole_history`); the light-client driver is a thin
embodiment of `light_client_verifies_whole_history`.

**Class: mostly FAILS-CLOSED — with ONE soundness-critical exception.** Cohort splitting (leg
count + adjacency checked, `proof_verify.rs:631-657`), name→JSON resolution (FS-bound), leg chaining
(anchors trusted-pinned, forged after-state UNSAT), and the aggregation fold (reorder/drop/insert
is UNSAT in-circuit; the host-side admission gate is *documented as NOT the soundness boundary*,
`lightclient/src/lib.rs:27`, with tamper tests confirming) all **fail closed**. The exception:

**The authority-floor deny-list — `is_forbidden_plain_cap_descriptor`
(`sdk/src/full_turn_proof.rs:4203`) + `is_forbidden_authority_only_cap_write_descriptor`
(`:4162`), used at the cutover `:4469`.** A "plain" cap descriptor (e.g.
`introduceVmDescriptor2R24`, `revokeVmDescriptor2R24`, `attenuateVmDescriptor2R24`,
`grantCapVmDescriptor2R24`) is a valid AIR with **no in-circuit cap-membership crown** — a
producer who never held the capability can produce a proof that genuinely verifies under it. The
deny-list is the verifier's floor against laundering that authority into a light-client proof,
and its two legs sit at different resolutions:

- **The list-completeness leg is mechanically enforced.** The test
  `authority_deny_list_is_complete_over_deployed_registry` (`:6153`) enumerates EVERY descriptor
  in EVERY deployed registry against a typed `DescriptorAuthorityClass` classification (`:4227`)
  and fails on any unclassified authority-shaped descriptor or any `LaundersAuthority` descriptor
  the deny-list misses — a new authority-bearing descriptor cannot enter the registry without
  either a classification or a red gate. This is a test-time completeness gate, not a runtime
  check, but the "hand-maintained census with nothing checking it" description no longer holds.
- **The write-bearing cap effects no longer ride the deny-list alone.** The cap-open write
  wrappers genuinely prove + light-client-verify the cap-tree write in-circuit ("THE TOOTH IS
  ON", `:4153-4163`), and the authority-only wrappers are light-client-REJECTED — so for those
  effects the barrier is a real in-circuit constraint, with the deny-list as the routing gate.

**Class: SOUNDNESS-CRITICAL (false-accept if the classification itself misjudges a
descriptor).** The residual is the deeper leg: the *classification* (`DescriptorAuthorityClass`)
is Rust judgment, and there is no Lean totality theorem behind it.

**To Lean-ground.** Make crown-presence a **structural** property the verifier reads off the
parsed descriptor (presence of the `capOpenConstraintsEff` op-set / a typed
`carries_authority_crown` flag emitted by Lean), and prove `∀ desc, authority_bearing(desc) →
has_crown(desc)`, so a misclassification is impossible by construction rather than caught by an
enumeration test. (The companion `cap_open_key_has_wide_twin` heuristic at `:2706` uses
`key.contains("TB")` / `name.contains("CapOpen")` string-matching — not a wrong-descriptor
accept, but commitment-width-fragile glue worth replacing with the registry membership it
mirrors.)

---

### 6. Blocklace consensus / finality / equivocation — `blocklace/`, `node/src/{blocklace_sync,finality_gate,equivocation_court_service}.rs`

**What it is.** The DAG (`blocklace/src/finality.rs`), the consensus ordering rule
(`supermajority_threshold(n)=2n/3+1`, `blocklace/src/ordering.rs:237`; `tau` / wave-ratification),
equivocation detection (paper Def 4.2 incomparability, `finality.rs:828`), and the node glue:
`poll_finalized_blocks` executes via the identity-keyed `ExecutionCursor`
(`node/src/blocklace_sync.rs:1360`, `node/src/execution_cursor.rs`); the live `VerifiedFinality` FFI gate (default-ON, re-runs the
Lean rule, `node/src/finality_gate.rs:60`); slashing as a real conserving executor `Transfer`
(`node/src/equivocation_court_service.rs`).

**Lean-status.** **More modeled than assumed.** The finality rule is executably modeled
(`Distributed/BlocklaceFinality.lean`: `tauOrder`, with `tauOrder_deterministic`,
≤1-anchor-per-wave, and the executor connection `tau_drives_verified_run`, `#assert_axioms`-clean,
golden-vector-matched to Rust `tau`); the gate is proven equivalent to it
(`Distributed/FinalityGate.lean: gate_admits_iff_verified_finalizes`); the finalized client has
`light_client_accepts_finalized_history` (`Distributed/FinalizedLightClient.lean`). Equivocation
is `Authority/Blocklace.lean` Def 4.2. **`SettlementSoundness.lean` does NOT cover the finality
rule** — it models authority-at-the-tip (caps + revocation, `settlement_soundness:153`) with the
tip *assumed*; it extends unfoolability along the revocation axis, not the consensus axis.

**The crux — two TCBs.** The light client has two entry points with different TCBs:
- **Property A ("accept ⟹ genuine state transition," the headline unfoolability).**
  `verify_history` (`lightclient/src/lib.rs:183`) verifies one recursive STARK aggregate and
  **re-witnesses no blocklace**. A forged `(old_root,new_root)` has no satisfying leaf; a
  double-spend is caught by in-circuit nullifier/balance + chain adjacency, regardless of what
  order/fork consensus picked. **Consensus is OUTSIDE this TCB** — a finality/equivocation/ordering
  bug cannot false-accept an *invalid* transition. (Matches the prompt's hypothesis: a
  bad-but-valid fork ≠ a false accept of an invalid transition.)
- **Property B ("accept ⟹ this root is the BFT-FINALIZED canonical root").** The code names the
  gap (`lightclient/src/lib.rs:247`): an equivocating prover can fold a valid aggregate over a fork
  the network never finalized. A wallet/bridge must additionally check leg 3 — `FinalityCert` +
  `verify_finalized_history` (`:393`). **Consensus IS in this TCB.**

**Class: OUT-OF-SCOPE for invalid-transition acceptance (Property A, fully circuit-enforced);
SOUNDNESS-CRITICAL for finalized-canonicity (Property B), with precise Rust-only gaps.** For a
value-bearing client, a Property-B break (settle on a non-finalized fork) is economically a
soundness break. The Property-B gaps:
- **Gap B1 — index slicing REFUTED (against the old coverage-τ); the identity cursor is the
  deployed closure; the residual is its proof.** `metatheory/Dregg2/Consensus/TauPrefixMonotone.lean`
  proves prefix monotonicity under `ClosedExtension` + `ChainExtends` (the former three-field
  `FinalizedRegionStable` is deleted; its honest-laggard counterexample is RETRACTED as a fact
  about CM — it refuted a τ that had deviated from CM Def. 6, and the CM-faithful anchor-closure
  τ is prefix-stable on the same trace). Historically, under the deviated coverage-τ a late
  validator's blocks passed every `insert` check yet `xsort`ed into the middle of the
  already-executed prefix — under a bare `executed_up_to` index the node re-executed one block
  and **skipped a finalized honest turn forever** (the FinalityGate admits by `(creator,seq)`
  membership, not position, so it didn't catch it). The deployed code does not slice by index:
  `poll_finalized_blocks` runs the "TAU-PREFIX-MONOTONE CLOSURE (identity cursor, not an
  index)" — `cursor.pending(&ordered)` set-difference plus `cursor.mark_executed(block_id)`
  (`node/src/blocklace_sync.rs:1360-1468`), boot-restored (`:2101`) and durably persisted
  (`persist_executed_block_ids`). `node/src/execution_cursor.rs`'s own header ("# The closure")
  states the cursor must not assume prefix stability: executed blocks are tracked
  by `BlockId` identity, so a mid-prefix insertion executes late exactly once and nothing already
  executed is re-served; the prefix-shift event surfaces as observability (loud log +
  `dregg_tau_prefix_shifts_total`; the Lean-side runtime mirror `stableCheck` was deleted as
  never-called). **The residual is the Rust↔Lean bridge:** no Lean theorem yet connects the
  deployed identity cursor to the corrected `tau_finalized_prefix_monotone`.
- **Gap B2 — `FinalityCert` signature verification — CLOSED since this census.** As written in
  2026-06-26 the cert checked signer COUNT over bare pubkeys, with no Ed25519 verification. That
  is now fixed: `FinalityCert` carries the Ed25519 signatures, and `distinct_signers`
  (`lightclient/src/lib.rs`) counts a validator toward the quorum **only when its signature
  `verify_strict`s over `finality_signing_message(finalized_root, participant_count)`** — a forged
  or unbound (wrong-root) signature is not counted. The committee-anchored path
  `distinct_committee_signers` / `has_committee_quorum` further binds the quorum to the client's
  TRUSTED committee (defeating the mint-fresh-keys attack), and the production
  `verify_finalized_history` uses that committee-anchored path. The Rust gate now discharges the
  signature/binding legs of the Lean `CertValid`, not merely `CertQuorum` (the count). **No longer
  an open soundness gap.**
- **Gap B3 — `xsort` tie-break is differential-only** (the OPEN-CM-XSORT residual): the Lean
  `(round,id)` linearization is a golden-vector-matched projection of the Rust `xsort`, not a
  proof.

The equivocation court (slash) is **not** a separate soundness surface — slashing executes as a
verified conserving executor turn; a detection bug is a fairness/liveness concern, not an
invalid-transition accept.

**To Lean-ground.** B1: prove the deployed identity cursor realizes the corrected
`tau_finalized_prefix_monotone` (the code-side closure is landed; the Rust↔Lean bridge theorem is
the open piece). B2: CLOSED (bullet above) — the deployed check already verifies the hybrid
ed25519 + ML-DSA-65 votes against the trusted committee; no code work remains on this leg.
B3: prove Rust `xsort` ≡ the Lean linearization.

---

## Ranked — what to Lean-ground next

Ordered by TCB-importance × tractability. The genuinely **soundness-critical Rust-only** set, with
the already-modeled and fails-closed candidates demoted (they are named, not ranked).

### Tier 1 — soundness-critical, Rust-only, and reachable

1. **The authority-floor deny-list — the structural/Lean leg** (`is_forbidden_plain_cap_descriptor`,
   `sdk/src/full_turn_proof.rs:4203`). The census's original near-term step — a registry-vs-list
   completeness diff — is DONE and mechanized: `authority_deny_list_is_complete_over_deployed_registry`
   (`:6153`) enumerates every deployed-registry descriptor against `DescriptorAuthorityClass` and
   red-gates any unclassified authority-shaped descriptor, and the write-bearing cap-open wrappers
   now prove the cap-tree write in-circuit (§5). What remains is the deeper leg: replace the name
   match + Rust classification with a **structural** crown-presence check read off the parsed
   descriptor + the Lean theorem `authority_bearing(desc) → has_crown(desc)`, so a
   misclassification is impossible by construction. Tractable because the per-descriptor crown
   semantics are *already* Lean-modeled; what's missing is the totality/structural-resolution step.

2. **The finalized-prefix cursor's Rust↔Lean bridge** (Gap B1, `node/src/blocklace_sync.rs`). The
   index-slicing design was *refuted* unsound under honest lag by `TauPrefixMonotone.lean` — a
   finalized honest turn could be skipped. The identity-keyed advance is **deployed** (§6):
   `poll_finalized_blocks` executes via `cursor.pending(&ordered)` set-difference with
   `cursor.mark_executed(block_id)` by `BlockId` identity (`node/src/blocklace_sync.rs:1393,1408,1468`),
   boot-restored via `ExecutionCursor::restore` (`:2101`) and durably persisted
   (`persist_executed_block_ids`), with the `stableCheck` observability signal (loud log +
   `dregg_tau_prefix_shifts_total`). The remaining work is the Rust↔Lean bridge theorem
   connecting the deployed identity cursor to the corrected `tau_finalized_prefix_monotone`.
   Tractable because the Lean side is done.

   *(Gap B2 — `FinalityCert` signature verification — is now CLOSED, see §6; it was the #2 near-term
   fix in the 2026-06-26 census and has since landed the Ed25519 `verify_strict` + committee-anchored
   quorum.)*

### Tier 2 — soundness-critical, Rust-only, but a larger proof effort

4. **The Rust commitment computation ≡ `recStateCommit`** (`cell/src/commitment.rs:204`/`:635`,
   `circuit/src/heap_root.rs:157`). The *binding* is proven over the model; the *deployed Rust
   computation of it* is linked only by differential + KAT. This is the floor that sits **under**
   every other guarantee, so it ranks high on importance — but lower on tractability: it wants a
   real refinement/extraction proof (Rust function = Lean model), modeling the `sort_by_key`
   algorithm (not just a sortedness predicate), and reconciling the binary-Merkle-vs-sponge and
   BLAKE3-vs-Poseidon2 structural gaps. Big, foundational, and the one whose differential coverage
   should be widened in the meantime.

5. **The Rust executor ≡ `recKExec`, or close the swap to totality**
   (`turn/src/executor/apply.rs:27`). Soundness-critical wherever Rust is authoritative
   (wasm/zkvm SDKs + the uncovered Mint/BridgeMint partition). Two routes: **Route A** (extend the
   `produce_via_lean` covered set to every effect and ride the Lean archive on wasm/zkvm — inherits
   the proven `Exec ⊑ Spec`, has momentum) is more tractable than **Route B** (the full
   `execute = recKExec` theorem — the structurally hard named open). Ranked below the commitment
   because the live swap already removes Rust from the TCB on the native covered set; the residual
   is the wasm/zkvm + uncovered-effect tail.

### Tier 3 — defense-in-depth (Rust-only, but fails-closed today)

6. **`xsort` ≡ Lean linearization** (Gap B3) and **descriptor parser `parse ∘ emitVmJson2 = id`**
   (§3). Both fails-closed today (xsort feeds Property B ordering already gated above; the parser
   is commitment-re-bound). Worth doing for completeness — the parser is especially clean since the
   emit side is already Lean — but neither is a current false-accept vector.

---

## Already-modeled or fails-closed (named, not the answer)

- **The state-commitment *binding*** — Lean-proven (`recStateCommit_binds_kernel`,
  `#assert_axioms`-clean). The gap is the Rust-impl-equals-model step (Tier 2 #4), not the binding.
- **The Merkle / cap-tree / heap-tree / nullifier non-membership construction** — Lean-modeled
  with Rust twins (cap-reshape crown, `Substrate/Heap.lean`, `SortedTreeNonMembership.lean`). No
  Rust-only gap.
- **Poseidon2 collision-resistance + FRI/STARK soundness** — TERMINAL CRYPTO FLOOR (named
  assumptions); the permutation conformance is KAT-pinned to Plonky3. Not a Rust-only logic gap;
  not the answer.
- **The wire codec** (postcard / serde_json) — Rust-only, but architecturally fails-closed:
  decoded fields are commitment-re-bound, so a misparse rejects rather than false-accepts. Flag:
  the serde_json executor-rerun verifier bundles (`verifier/src/bilateral_pair.rs:188`).
- **Most verifier orchestration** (cohort split, name→JSON resolution, leg chaining, aggregation
  fold, light-client driver) — Rust glue but fails-closed: proofs are Fiat-Shamir-bound to their
  descriptor, anchors are trusted-pinned, in-circuit constraints make reorder/forge UNSAT. The one
  exception is the authority deny-list's classification leg (Tier 1 #1; its list-completeness leg
  is mechanically gated).
- **Blocklace consensus for Property A** — OUT-OF-SCOPE: invalid-transition acceptance is fully
  circuit-enforced; consensus picks *which valid fork*, not *whether a transition is valid*.
- **`cell/src/nullifier_set.rs`** (BLAKE3, Rust-only, unmodeled) — OUT-OF-SCOPE for the light
  client; a separate executor/federation/wasm trust surface worth tracking on its own, not here.

## The honest one-liner

The genuinely soundness-critical, Rust-only, and not-yet-Lean-grounded set (as of this census,
since narrowed) is **two glue/check gaps, each partially closed** (the authority-floor
deny-list — its list-completeness leg is now mechanically gated by the registry-enumeration test
and the write wrappers prove the cap write in-circuit, leaving the structural crown-presence +
Lean totality theorem; the finalized-prefix cursor — the identity-keyed advance is deployed,
leaving the Rust↔Lean bridge theorem to `tau_finalized_prefix_monotone`) plus **two foundational refinement proofs**
(Rust-commitment ≡ model; Rust-executor ≡ `recKExec` / swap-totality) — the third original glue
gap, the `FinalityCert` signature check, is CLOSED (Ed25519 `verify_strict` + committee-anchored
quorum). The remaining deny-list and cursor legs are the high-leverage near-term work — small,
sharp, and each already has its Lean counterpart waiting. The two refinements are the deep
TCB-shrink. Everything else is already modeled, fails-closed, or the standard crypto floor. ( ◕‿◕ )
