# UMEM Cross-Review - Codex Source Review

> **Point-in-time review artifact (~2026-06-24).** Companion to `docs/deos/UMEM-CROSS-REVIEW.md`. Line numbers below have drifted against HEAD but the cited symbols and the substantive seam analysis still hold. One dated detail: this review argues over a *five*-constructor `Domain` enum; a sixth constructor `working` has since been added (`metatheory/Dregg2/Crypto/UniversalMemory.lean:87-94`, the umem realization of `UDomain::Working` at `turn/src/umem.rs:118`) — which partially answers §1 / Open-Questions-#3 (the transient scratch domain rides the same one memcheck trace and publishes no committed boundary), though the deeper ask (generalize to an arbitrary/injective tag manifest) is still open.

Scope: second review of `docs/deos/UMEM-CROSS-REVIEW.md` against the current Rust and Lean source, with no code edits.

Local checks run:

- `cd metatheory && lake env lean Dregg2/Crypto/UniversalMemory.lean`
  - reported: `#assert_namespace_axioms Dregg2.Crypto.UniversalMemory: 25 theorems pinned kernel-clean`
- `cd metatheory && lake env lean Dregg2/Exec/UniversalBridge.lean`
  - completed successfully

## Verdict

The central idea is sound in the narrow formal sense already landed: a single Blum memory argument over a tagged address space can cover multiple logical memory planes, and the init-boundary root-binding theorem is real and axiom-clean.

The brief overstates the integration boundary in several places. The current circuit realizes committed-state binding for the cross-cell-read use case by per-cell `MapOp::Read` openings against a public root, not by recomputing and pinning a whole universal boundary image. That per-cell subset proof is enough for "this peer field is the committed value under this published root." It is not enough for "the entire `UMemBoundaryWitness` init image equals committed pre-state, with no extra or missing cells."

The second major overstatement is the executor bridge. Rust has a broad executable witness lane, and Lean has clean agreement theorems for a compressed subset. But the current source does not prove the full live executor projection over all state planes/effects. Treat it as a strong prototype plus partial formal bridge, not yet a completed refinement theorem.

## Soundness Claims

### 1. Universal memory and tag isolation are real, but finite/tag-manifest scoped

The Lean universal address space is explicitly `Domain x key`, where `Domain` is the five-constructor enum `registers | heap | caps | nullifiers | index` (`metatheory/Dregg2/Crypto/UniversalMemory.lean:75-86`). The core projection lemmas are real:

- `consistentFrom_filter` says consistency restricts to an arbitrary address class (`UniversalMemory.lean:114-142`).
- `consistentFrom_strip` says a single-domain trace can shed the tag and become a standalone memory trace (`UniversalMemory.lean:150-190`).
- `universal_memory_sound` welds `MemCheck`, `Disciplined`, `Nodup`, and closure into whole-trace consistency plus per-domain consistency (`UniversalMemory.lean:192-213`).

That supports the "tag isolation" story. It does not by itself prove an unbounded "parametric primitive" with arbitrary future collections. For that, the proof shape should be generalized from the finite `Domain` enum to an injective tag/collection manifest, or the IR must bind every new domain/collection code to a semantic manifest. The AIR currently checks the domain as a byte/nibble (`circuit/src/descriptor_ir2.rs:2768-2770`, `2833-2857`) and the source comments say "new state components are new codes, never new tables"; that is plausible, but the semantic code-to-collection registry is still source/comment-level rather than a theorem.

Cleaner formulation: prove `universal_memory_sound` over an arbitrary tag type with decidable equality, plus a concrete manifest theorem saying the deployed tag encoding is injective and every tag has exactly one declared semantic collection.

### 2. The init-boundary keystone exists and is stated correctly

The two named keystone theorems are present and pinned:

- `boundary_init_root_derived` (`UniversalMemory.lean:463-468`) is the init-side mirror of `boundary_root_derived`. Given a sorted committed heap `h`, a sorted declared address list `as`, and semantic equality
  `Heap.get h a = if a in as then init a else none`,
  it proves the committed heap root equals the root of `boundaryCells init as`.
- `boundary_init_root_bound` (`UniversalMemory.lean:475-479`) says equal roots imply equal heaps under `Poseidon2SpongeCR`, via `Heap.root_injective`.
- Both are included in the axiom pins (`UniversalMemory.lean:781-782`) and the namespace check is pinned at `UniversalMemory.lean:787`.

This is the right statement for the whole-image theorem. It is not a per-row membership theorem. Its hypothesis `hsem` is whole-image equality over the declared list plus absence outside the list (`UniversalMemory.lean:463-467`). The injectivity tooth then upgrades equal roots to equal heaps (`UniversalMemory.lean:470-479`).

The source-level integration is narrower than the brief's phrasing. `descriptor_ir2.rs` says the universal boundary image is witness-supplied, and that init is bound to committed pre-state per-cell by `MapOp::Read` openings, while the "whole-IMAGE equality" and in-circuit sorted-Poseidon2 fold are a named tail (`circuit/src/descriptor_ir2.rs:94-106`). I found `DescriptorIR2.satisfied2U_init_root` as a design label in comments, not as a named theorem/constraint symbol.

So: the Lean keystone is real; the current IR usage is per opened cell, not a whole-image boundary root pin.

### 3. Cross-cell read is sound with per-cell membership, not whole-image equality

For the primitive "cell A proves it read field f from peer cell B under B's published field root," whole-image equality is not required. A PI-bound root plus membership opening of `(field, value)` is enough, assuming the public root is itself authenticated as B's committed field-plane root.

The test descriptor is exactly that shape:

- root column pinned to public input (`circuit/tests/effect_vm_umem_real_turn.rs:478-493`);
- one `MapOp::Read` with `new_root = root` (`effect_vm_umem_real_turn.rs:494-502`);
- the map witness preflight rejects absent keys, wrong values, and read root changes (`circuit/src/descriptor_ir2.rs:3925-3945`);
- teeth cover honest proof, forged root, forged value, and PI mismatch (`effect_vm_umem_real_turn.rs:576-683`).

The comments state the soundness scope accurately: per touched init/read cell by per-cell membership is a faithful subset view, and whole-image/no-extra-cells is a named tail (`effect_vm_umem_real_turn.rs:443-449`).

What is missing is the integrated theorem that connects this circuit fact to the program-level `ObservedFieldEquals` carrier. The Lean program theorem assumes a `TurnCtx` already contains an authenticated observed value (`metatheory/Dregg2/Exec/Program.lean:1569-1599`). Rust currently builds a host `FinalizedRootAuthority` from the shared ledger (`turn/src/executor/execute_tree.rs:106-170`) and passes it into the witness bundle (`execute_tree.rs:940-954`). The cell evaluator then fails closed without that host authority and checks the observed value (`cell/src/program/eval.rs:1767-1826`). That is a good executor path, but it is not yet a single circuit/Lean theorem saying "the `MapOp::Read` proof populates exactly this `TurnCtx.observedFields` triple."

## Seven-Item Lean Frontier

### 1. Whole-image boundary equality

Correct obligation, and it is stricter than the cross-cell-read need. The Lean semantic root theorem is already there (`UniversalMemory.lean:463-479`), but the circuit still needs an in-circuit boundary root fold or an equivalent binding that covers the entire `UMemBoundaryWitness` image. The current AIR enforces boundary sortedness, option canonicality, init/final participation in the Blum balance, and address closure (`descriptor_ir2.rs:2833-2927`), and the trace builder replays the final image (`descriptor_ir2.rs:3624-3758`). It does not compute a whole boundary root.

Cleaner split:

- `MembershipSound`: per-cell committed membership under a public root. This is enough for cross-cell reads.
- `BoundaryImageSound`: the entire declared boundary image equals a committed heap, including no extra cells. This needs the root fold and `boundary_init_root_bound`.

Tractability: medium. The Lean statement is done; the remaining work is mostly AIR/witness/public-input plumbing.

### 2. Per-cell umem

The proof technology is tractable because `consistentFrom_filter` already works for arbitrary address classes, not just enum domains (`UniversalMemory.lean:118-142`). A per-cell heap can be formulated as a predicate over `(domain, collection, cell, key)` or as a tag refinement inside `key`.

The harder part is not the memory argument; it is the semantic projection and commitment surface. Rust projects a broad state table (`turn/src/umem.rs:32-60`, `379-398`) but explicitly does not project derived roots like `CellState.fields_root`, the ledger Merkle root, or metering state (`turn/src/umem.rs:62-75`). A per-cell theorem must state exactly which cell state is reconstructed from the umem projection and which roots are derived views.

Cleaner formulation: prove `project_cell`/`reify_cell` as a partial isomorphism for the committed subset, then prove derived commitments from that subset, rather than trying to prove literal equality to the full runtime `Cell` object.

### 3. Per-handoff Blum-trace witness

Harder than the brief implies. Rust's `emit_trace` does check `fold(pre, ops) == post` and discipline (`turn/src/umem.rs:721-741`), but it can synthesize trailing writes for pre/post differences not named by the journal (`turn/src/umem.rs:692-719`). The real-turn test asserts `synthesized == 0` for its lane (`circuit/tests/effect_vm_umem_real_turn.rs:167-170`), which is the right gate for a "journal produced every write" claim.

The Lean/Rust obligation should be split:

- `FoldAgreement`: `fold(pre, ops) = post` for the emitted trace. This exists as executable Rust and partial Lean bridge.
- `JournalCoverage`: every op is justified by a journal entry or by a named allowed synthetic surface.
- `NoSynthesized` for proof modes that claim the trace is fully journal-derived.

Without that split, a handoff proof can prove memory consistency while still relying on synthesized state differences whose executor-cause theorem has not been established.

### 4. `reify_cell`

This is harder than "dropped fields are functions." The projection intentionally omits derived commitments and operational metadata (`turn/src/umem.rs:62-75`). The right theorem is not `reify(project(cell)) = cell` for the full runtime struct.

Cleaner formulation:

- `project(reify(p)) = p` for canonical projected cells.
- `commit(reify(p)) = derived_root(p)` for the committed state subset.
- Explicit non-theorems for runtime-only fields: per-window metering, lazy caches, derived roots, and host-local proof caches.

Tractability: medium if the target is the committed subset; high risk if stated as full runtime equality.

### 5. Mid-forest yield point

This is more than a memory checkpoint. A prefix of a forest execution can certainly be represented by a umem fold:

`fold(pre, prefix_ops) = snapshot`.

But a resumable proof also needs continuation conditions: same authorization context, nonces/nullifiers not double-consumed, rollback semantics for fail-closed branches, and a receipt/commitment shape that says the prefix is passable state rather than a committed final turn. The memory proof is necessary but not sufficient.

Cleaner formulation: define a `YieldCertificate` with pre-root, prefix-root, next-program-counter/continuation descriptor, consumed-linear resources, and allowed continuation authority. Then prove prefix fold and suffix composition separately.

Tractability: medium-high, but mostly outside `UniversalMemory.lean`.

### 6. Promise-hole-as-nullifier

This needs narrowing. The landed guarded-hole source is explicit: the weak guarded hole is safe because the shape is eager and only the value is lazy; the strong hole with undetermined delta/lazy shape is deliberately inexpressible (`metatheory/Dregg2/Exec/GuardedHole.lean:1-18`, `33-63`).

So "promise hole is a nullifier" is sound only for a one-shot fill of an already-shaped obligation. It is not sound as a general "defer arbitrary transition shape and later spend the hole" primitive. The nullifier analogy should be: resolution consumes a unique pending obligation and installs a value/effect whose shape was already committed. If the shape is not committed up front, the memory/nullifier machinery does not save the construction.

Cleaner formulation: `PromiseHole` has an eager `(target, field/effect kind, guard, continuation id)` plus a nullifier key. Resolution proves non-membership/freshness, inserts the nullifier, and performs exactly that eager shape.

### 7. Deep-interior runtime checkpoint

This is not a single Lean obligation yet; it is an interface design. If a deep runtime checkpoint is replayable, umem can be the state witness. If it is service-backed, the proof should bind an opaque service checkpoint digest plus whatever attestation/replay contract that service claims.

The open question in the brief is real: the receipt or descriptor should commit a semantics bit such as `ReplayableDeterministic` vs `ServiceCheckpoint`. Otherwise a verifier may accidentally apply replay theorems to an opaque service snapshot.

Tractability: high as an interface split, lower as a universal proof because service semantics are intentionally external.

## Open Questions

### Is "umem as a parametric primitive" sound by tag isolation?

Partially. The formal tag-isolation theorem is good for disjoint address classes and finite domains (`UniversalMemory.lean:118-213`). Scaling it to a parametric primitive needs one of:

- a generalized theorem over arbitrary tag types;
- or a manifest theorem tying deployed numeric tags/collection ids to semantics.

The gap is not in the memory check. The gap is in tag/collection registry binding and in saying which boundary root each tag instance commits to.

### Is ed25519 -> ML-DSA proof-shape preserving?

Only at the abstract Prop-portal level.

The Lean receipt predicate is opaque: `Ed25519ReceiptVerifies` is a named `Prop`, not an AIR gate (`metatheory/Dregg2/Crypto/DualSchemeAuthority.lean:123-125`). The dual-scheme proof derives the proven-mode forcing without any ed25519 premise (`DualSchemeAuthority.lean:299-310`) and the file is clean-pinned (`DualSchemeAuthority.lean:352-361`). If ML-DSA replaces the opaque receipt predicate with the same abstract shape, the Lean proof skeleton can survive.

That does not mean the system swap is one-line or end-to-end proof-preserving. Rust has ed25519 in multiple authorization carriers: ordinary action signatures (`turn/src/action.rs:216-217`), CapTP delivery signatures (`turn/src/action.rs:251-257`), stealth authorization (`turn/src/action.rs:394-410`), Biscuit issuer keys (`turn/src/action.rs:449-454`), and signed delegations (`turn/src/action.rs:520-524`). The in-circuit turn-auth source also states the deployed signature is ed25519 off-circuit and the in-circuit proving path is BabyBear^8 Schnorr, with Ed25519 AIR or rebinding as the named remaining gap (`circuit/src/turn_auth_signature_air.rs:1-41`).

So: proof-shape preserving for the abstract off-circuit receipt predicate; not yet proof-shape preserving for the deployed wire formats, account identities, token issuers, signature sizes, key commitments, and light-client-visible authorization path.

### What is missing?

The highest-value missing pieces I see:

1. A whole-boundary root-fold AIR, or an equivalent public-root binding, for `UMemBoundaryWitness` as a whole image.
2. An integrated theorem from `MapOp::Read` membership proof to `ObservedFieldEquals`/`TurnCtx.observedFields`.
3. A tag/collection manifest theorem for parametric umems beyond the fixed five-domain Lean enum.
4. Codec injectivity and production lowering for every projected `UKey`/`UVal` plane. The first real-turn proof uses dense per-proof relabeling and names production codecs as remaining work (`circuit/tests/effect_vm_umem_real_turn.rs:21-31`).
5. A full live executor refinement theorem. `turn/src/umem.rs` says the live proving path is untouched (`turn/src/umem.rs:26-28`), and Lean asserts agreement for `gwrite`, `move`, and `create` (`metatheory/Dregg2/Exec/UniversalBridge.lean:481`, `587`, `727`, `1110-1112`) but not for every Rust effect/state surface.
6. A theorem or hard gate around synthesized writes in `emit_trace`.
7. A precise semantics split for replayable checkpoints versus service checkpoints.

## Overstated Claims

1. "The init binding is lifted to IR as a complete boundary binding."

   The Lean theorem is complete, but the source says current IR binding is per declared init cell by map reads and that whole-image equality rides the universal-map rotation (`descriptor_ir2.rs:94-106`).

2. "Cross-cell read needs whole-image equality."

   It does not. For the cross-cell-read primitive, per-cell membership under a published root is enough. Whole-image equality is needed for stronger claims about the full boundary image.

3. "Cross-cell read is already a universal-memory primitive."

   The proved circuit leg is a `MapOp::Read` descriptor with no `UMemOp` table (`effect_vm_umem_real_turn.rs:478-507`). It is the right committed-membership primitive, but not yet an integrated umem boundary theorem.

4. "The executor bridge is fully proved."

   Rust projects broadly and checks fold agreement (`turn/src/umem.rs:379-398`, `721-741`), but it can synthesize writes (`turn/src/umem.rs:692-719`). Lean's asserted agreement theorems cover `gwrite`, `move`, and `create` (`UniversalBridge.lean:1110-1112`). `moveAssetTrace` has a disciplined theorem (`UniversalBridge.lean:250`, `276-277`, `1108`), but I did not find a corresponding `moveAsset_is_memory_program` agreement theorem.

5. "Per-proof dense relabeling is production lowering."

   The test is honest that dense injection preserves the memory-consistency statement and that production address/value codecs remain the rotation's realization step (`effect_vm_umem_real_turn.rs:21-31`). Claims about production committed-state proofs should keep that qualifier.

6. "ed25519 -> ML-DSA is just a carrier swap."

   It is a carrier swap only for the opaque Lean receipt predicate. The deployed Rust and light-client authorization surface contains multiple ed25519-shaped carriers and an explicit in-circuit signature gap (`turn/src/action.rs:216-217`, `251-257`, `394-410`, `449-454`, `520-524`; `circuit/src/turn_auth_signature_air.rs:25-41`).

## Bottom Line

The architect's main direction is right: universal memory can be the general witnessed primitive, and the keystone boundary-init theorem is real. The safe next phrasing is:

> UMEM currently proves a tagged-memory interior plus per-cell committed membership at the edge. Whole-image boundary commitment, full executor refinement, parametric tag manifests, and integrated cross-cell-read context population are the remaining proof/integration frontier.

That phrasing preserves the real breakthrough without implying the source has already welded every boundary the design names.
