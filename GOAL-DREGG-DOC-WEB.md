# GOAL — dregg document + web layer, real end-to-end (on the proven Lean foundation)

*A /goal lane (this repo runs concurrent /goal sessions; this is the doc+web lane's trail).
Spec: docs/DREGG-DOCUMENT-FOUNDATION.md · memory: project-document-foundation.md*

## The goal
Make the dregg document + web layer real end-to-end on the proven Lean foundation: the deployed
dregg-doc / <dregg-doc> CALL the exported DocCore (native via libdregg_lean.a, tab via wasm-Lean) —
no Rust shadow. Close every named seam (Element-grammar injectivity in Lean; the real content-
addressed netlayer; aggregate the doc modules into Dregg2.lean when the PQ lane clears it). Then the
rich layer emergent from authoring real docs: Peritext marks, DOM-schema editing, a keyed reconciler
→ a person authors a verifiable document in a browser, a stranger checks the whole receipt chain.
Disciplines: read proofs adversarially against their name; name seams + never let a name inflate;
fail-closed; carriers only at the crypto floor; verify on the real tree; commit path-specific.
ON-DISK-FORMAT CUTOVER + any deployed-behavior flip = ember-gated.

## FOUNDATION — DONE (7/7, all on main, each verified adversarially)
- F1 dc23286b4 · composed merge = product of pushouts; boundary at ConflictAt level
- F2 08d255113 · Poseidon2 commit (real decoder) + conflict-as-state soundness [seam: Element grammar cited-to-Rust]
- F3 97db0a91d · anchored verifier — live include() hole closed; anti-forge INVOKES CR
- F4a 703bef7a4 · DocCore Init-only reaches the tab (verified on emitted C, 677KB); refines := rfl
- COLL_EMBEDS 2eb11fbc0 · embed pointer bound; Name = indirection-not-resolution
- web-embed b52fade6c · <dregg-embed>/<dregg-transclude>, recursive shadow membranes, darkening withholds bytes
- P a2b126215 · full labelled patch category — conflict = a MISSING pushout (categorical necessity)

## CURRENT THRUST — cutover + closures (3 lanes, re-issued after a process-exit killed them)
- F4b · deployed commitment cutover (dregg-doc → @[export] DocCore via FFI). Ember-gated on the FORMAT FLIP:
  agent maps blast radius + does it if clean, else STOPS with a plan. NOT a silent Rust-twin.
- F2-closure · Element-grammar injectivity in Lean (close F2's cited-to-Rust seam)
- netlayer · real content-addressed resolver (WebOfCells+Membrane+verify_anchored) so <dregg-*> hit a live node

## NEXT 3 MOVES (my pick)
1. Land the 3 current lanes (verify adversarially, commit path-specific).
2. Aggregate the 6 Deos doc modules into Dregg2.lean — WHEN the PQ lane stops churning it.
3. Rich layer kickoff: Peritext mergeable marks (within-cell), the first real authored document.

## DONE-LOG
- 2026-07-09 foundation 7/7 landed + verified + memory'd; specs written (FOUNDATION/WEB/QUIET-UPGRADE).

## ⚠ SCOPE CORRECTION (F4b Step-0, verified on tree) — F2/F4a targeted the WRONG commit
The DEPLOYED document commitment is `substrate_commit` (sorted-Poseidon2 heap-Merkle root, dregg-doc/
src/substrate.rs::compute_heap_root) — bindings_doc.rs: `heap_root == substrate_commit(published)`.
Its INJECTIVITY is ALREADY PROVEN via Storage/BucketCommitment.lean (contentRoot_injective, no-ghost),
same Poseidon2SpongeCR carrier. BUT F2 (DocCommit) + F4a (DocCore) proved the LINEAR-SPONGE scheme
(`commit::commit`, DefaultHasher default, ZERO external consumers) — a PARALLEL, NON-DEPLOYED commit.
So the earlier "F4a = proven core reaches the tab, no shadow" was INFLATED (integrator-scope-compress):
the tab's real commit is substrate_commit, which DocCore does NOT prove. F2/F4a are real Lean proofs of
a scheme that isn't deployed.
REAL CLOSURE (Path A — additive, NO format flip, so main-loop's call not ember-gated): prove the
conflict-as-state-soundness COROLLARY for the DEPLOYED substrate_commit (equal heap-root ⟹ equal conflict
alternatives, from contentRoot_injective + to_heap_map faithfulness), and relabel the toy commit::commit
as a non-security content-address. F2/F4a's linear sponge KEPT (honest parallel; could become the deployed
default if commit::commit is ever un-toy'd) but its deployment-relevance corrected. Firing Path A now.
- done-log: F4b Step-0 finding verified; Path A chosen (additive); F2/F4a scope corrected in-trail.

## 🔥 DELETING THE DUPLICATION (ember: "delete the bullshit toys, stop duplicating")
Verified: the DEPLOYED document commitment is `substrate_commit` (dregg-doc/src/substrate.rs, the
sorted-Poseidon2 heap-root via cell::compute_heap_root), and it is ALREADY PROVEN in Lean via the umem
heap-root keystones (Dregg2/Substrate/Heap.lean, Crypto/UniversalMemory.lean::boundary_root_derived,
Crypto/PerCellUmem.lean::percell_boundary_root_derived — scheme-pinned to the deployed circuit::heap_root,
AssuranceCase.lean:1043). So:
- ⚠ RETRACT F2 (08d255113 DocCommit) + F4a (703bef7a4 DocCore/DocProofs) + the ElementGrammar closure:
  they proved a PARALLEL linear-sponge commit (`commit::commit`, DefaultHasher default, ZERO external
  consumers, test-only) — a TOY duplication, NOT the deployed commit. DELETED the 4 Lean modules.
- The `commit::commit` toy (DefaultHasher, commit.rs) is being DELETED too; the anti-forge tests re-point
  to the real substrate_commit.
- KEPT (real, deployed): F1 (DocMergeComposed — the merge), F3 (AnchoredQuote — the quote verifier),
  P (PatchCategory — the algebra), COLL_EMBEDS (binds the embed pointer in the REAL substrate_commit).
- The wasm-Lean RECIPE (F4a §4: Init-only @[export] reaches wasm) is KEPT as knowledge (spec §4 + memory);
  the specific DocCore module was a toy instance. The DEPLOYED substrate_commit reaches wasm as Rust
  (bindings_doc.rs), gauntlet-bound to the proven heap-root keystones.
- ONE commit now: substrate_commit. done-log: 4 toy Lean modules deleted; Rust toy commit deletion firing.
