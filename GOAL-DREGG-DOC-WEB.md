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
