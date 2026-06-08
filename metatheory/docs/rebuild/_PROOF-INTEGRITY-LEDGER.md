# Proof-Integrity Ledger — severity-ranked

Synthesized 2026-06-08 from the audit + adversarial-verification rounds (R0/R1/R2/R3 +
two independent VERIFY passes per region). Every cited line below was re-checked against
source by reading theorem **bodies**, not grep counts. Build was GREEN at synthesis
(`lake build` Dregg2+Metatheory, ~3828 jobs, no `sorry`/`sorryAx`; the audited soundness
keystones are `#assert_axioms`-pinned and elaborated, so a stray axiom would have failed
the build).

The bar (from MEMORY): **builds = LOW, meaningful spec = MID, l4v = HIGH.** A labeled
vacuity is still BROKEN. FATAL = a *load-bearing* guarantee that is secretly trivial/false.

---

## FATAL — load-bearing guarantee secretly trivial or false

**None.** The adversarial rounds tried to refute the keystones and could not. Specifically:

- `effect2_circuit_full_sound` (`Circuit/EffectCommit2.lean:387`) is **non-vacuous**: real
  `RestFrameDecodes2`/`logHashInjective`/`GuardDecodes2` hypotheses, a genuine 4-conjunct
  full-state apex (`:216`), three real anti-ghost contrapositive teeth (`:441/:451/:461`).
- The `:=True` / `binds := trivial` / `restFrame := True` markers flagged in earlier waves
  live on the **Wire/emission carriers** (e.g. `balanceAEWire`, `Circuit/Inst/balanceA.lean:213`),
  which `effectCircuit2` (`EffectCommit2.lean:317`) reads only via `guardGates` — they are
  genuinely **off the soundness path**. The soundness theorem `balanceA_full_sound`
  (`:199`) carries the REAL `Function.Injective D` / `RestIffNoBal` / `logHashInjective`.
- `mint_circuit_refines_exec` and the `EffectRefinement.lean` triangle descend to the
  genuine `execFullA` (`:154/:192`), `#assert_axioms`-clean.
- ConcreteKernel's four theorems and the abstract keystone they invoke
  (`recTransfer_balanceSum_conserve`, `RecordKernel.lean:670`) are real cancellation proofs.
- The distributed/CapTP crypto seams (`SignatureKernel.unforgeable`, `signed`-bit,
  `SessionUnforgeable`) are genuine named hypotheses, **witnessed FALSE** somewhere
  (`instSignatureForge_not_unforgeable`), never `:=True`.

So nothing in the crown jewels is *secretly false*. What follows are real coverage gaps
and prose overclaims — every one is a place where the **docstring/headline promises more
than the theorems deliver**. Treat them as FATAL-adjacent honesty debt: under the project
bar, a doc that names a theorem which does not exist is "vapor," and vapor is broken.

### F1 — GC §1↔§2 bridge is VAPOR: `gcDropTotal` does not exist (FIXED here)
- **Claims:** `Exec/CapTPGCConcrete.lean:30-31` docstring — "§2's table is the abstraction
  of the per-holder refcounts whose SUM is the swiss entry's `refcount` field, and
  `gcDropTotal` is shown to track that field's decrement."
- **Why weak:** `gcDropTotal` appears **only in that doc comment** — no `def`, no `theorem`.
  §1 (refcount-positivity over the real `execFullA … swissDropA` swiss-table `refcount`
  field) and §2 (the executable `processDrop` per-holder session table modeling `gc.rs`)
  are **two disconnected models**. There is no theorem linking §2's per-holder SUM to §1's
  swiss-entry field. Each half is independently sound; the "the SUM is the swiss entry's
  refcount" connection is asserted in prose and never proven.
- **Fix:** either (a) prove the bridge `swissEntry.refcount = Σ holders, holder.total_refs`
  and a `gcDropTotal`-tracks-decrement lemma, or (b) make the prose honest. Done here via
  (b): the docstring now states the two models are **independently sound but unbridged**,
  removing the phantom-theorem claim. The real bridge is logged as MID-1 to actually prove.
- **Ownership:** `CapTPGCConcrete.lean` — task #61 is **completed**; no in-progress task
  touches GC. **SAFE-TO-FIX-NOW.** ✅ doc fix applied in this commit.

### F2 — per-asset conservation keystone has ZERO concrete refinement square (doc clarified here)
- **Claims:** `Exec/ConcreteKernel.lean:7` docstring cites `recKExecAsset_conserves_per_asset`
  as one of the soundness lemmas the refinement layer preserves; MEMORY flags per-asset
  conservation (`recTotalAsset` for EVERY asset, never one aggregate scalar) as the **real**
  conserved measure.
- **Why weak:** `concreteTransferAsset` **does not exist** (`grep` across `Dregg2/` = NONE).
  The only concrete ops are `concreteTransfer` (`:134`, single implicit asset) and
  `concreteWriteField` (`:144`). The genuine multi-asset keystone
  `recKExecAsset_conserves_per_asset` (`RecordKernel.lean:801`, over `recKExecAsset` at
  `:756`) has **no commuting square** at the concrete layer — `concreteTransfer_conserves`
  (`:222`) only transfers the **aggregate** `recTotal` conservation, not the per-asset one.
  The concrete layer's conserved measure is therefore the *weaker* aggregate scalar that
  MEMORY explicitly warns against treating as "conservation."
- **Fix:** add `concreteTransferAsset` refining `recKExecAsset` + its commuting square, then
  derive `concreteTransfer_conserves_per_asset` from `recKExecAsset_conserves_per_asset` via
  the square. This is real l4v work (a new `def` + a `getD_insert` square + a corollary),
  not a doc edit. Logged as MID-2. The docstring is corrected here to stop implying the
  per-asset keystone is preserved at the concrete layer when only the aggregate is.
- **Ownership:** `ConcreteKernel.lean` — task #14 (l4v data refinement, node basis) is
  **pending, not in_progress**; no running workflow owns this file. The *theorem* fix is
  SAFE-TO-FIX-NOW but is genuine proof work; the *doc honesty* fix is applied here. ✅

---

## MID — real weakness, not soundness-fatal

### MID-1 — GC bridge theorem (the real fix behind F1)
- **What:** prove `swissEntry.refcount = Σ_{holders} holder.total_refs` and a
  `processDrop`-decrement-tracks-`swissDropA` lemma, welding §2 to §1.
- **Why MID not FATAL:** both halves are independently sound and `#assert_axioms`-clean; the
  Byzantine session tooth (`byzantine_node_different_session_cannot_drop_others_refs`) and
  the refcount-positivity teeth genuinely bite. Only the *unification* is missing.
- **Fix:** as above. **SAFE-TO-FIX-NOW** (GC file unowned).

### MID-2 — `concreteTransferAsset` refinement square (the real fix behind F2)
- **What:** the per-asset concrete op + square + corollary (see F2).
- **Why MID:** the abstract per-asset keystone is fully proven; only the concrete *mirror*
  is absent, so node-grade execution cannot yet *carry* per-asset conservation — but the
  guarantee is not false, just not refined down. **SAFE-TO-FIX-NOW** (`ConcreteKernel.lean`
  unowned; pending task #14).

### MID-3 — ConsentLace "equivocation repels settlement" is a weaker lookalike
- **Claims:** `Exec/CapTPConsentLace.lean:333-339` `equivocating_party_blocks_settlement` —
  headline "a byzantine consenter is repelled."
- **Why weak:** the block is driven **entirely** by the hypothesis
  `hReject : partySignedConsent B p digest = false`; the equivocation premise `hfork` feeds
  **only** the `Equivocator` detection tag (`:338`), not the block. The witness
  `fork9approve` (`:466`) discharges `hReject` by setting the approve branch `signed := false`
  — i.e. only an **unsigned** fork is repelled. A party that signs a *valid* approve AND a
  conflicting revoke (a genuine **signed** equivocation) has `partySignedConsent = true` and
  **would settle**. The missing theorem is "signed-equivocation ⇒ consent not counted."
- **Fix:** prove `consentForks ∧ partySignedConsent ⇒ ¬settle` (the validator must DROP a
  detected signed equivocator's consent, not merely tag it), then re-witness with a signed
  fork. Until then the docstring should read "an *unsigned* fork is repelled; signed
  equivocation is DETECTED (tagged) but its settlement-blocking is the validator's policy
  hypothesis, not a theorem."
- **Why MID not FATAL:** the soundness lemma `settle_requires_signed_authorship` it leans on
  is real, the detection (`consent_equivocation_detectable`) is real, and the property is
  true as stated *given* `hReject`. It is an overclaimed headline, not a false theorem.
- **Ownership:** `CapTPConsentLace.lean` — task #61 **completed**; no in-progress task. The
  doc-narrowing is safe; the new theorem is real proof work. SAFE-TO-FIX-NOW but deferred
  (proof, not in scope of this path-limited commit).

### MID-4 — three disjoint state commitments, NO cross-binding theorem
- **Claims:** the crown-jewel triangle implies one authenticated state object.
- **Why weak:** there are **three** distinct commitments and **no Lean theorem equates any
  two**: `recStateCommit` (`Circuit/StateCommit.lean:196`, `cmb`/`compress`),
  `cellCommit` (`Exec/RecordCommit.lean:79`, BLAKE3 `compressN` over `fields_root`,
  `cell/src/commitment.rs` v3), and the EffectVm descriptor `state_commit`
  (`Circuit/Emit/EffectVmEmitTransfer.lean:133-155`, Poseidon2 H4-of-H4 over a strict
  SUBSET `{bal_lo,bal_hi,nonce,field[0..7],cap_root}`). `grep` for any theorem relating
  `recStateCommit` and `cellCommit` is empty; the `commit_eq_commitOf` matches are
  intra-circuit (the H4 chain proving itself), not a bridge to the executor commitment.
  So the witness pins the post-state under *one* commitment, but soundness vs the *running*
  cell commitment (BLAKE3) is unproven, and the EffectVm subset omits ~most fields.
- **Fix:** prove a cross-binding lemma `recStateCommit s = f(cellCommit s)` (or that both
  are injective images of the same `RecordKernelState` projection) and widen the EffectVm
  subset, or document the subset as the authenticated boundary with an injectivity portal.
- **Ownership:** `StateCommit.lean`, `RecordCommit.lean`, and the `Circuit/Emit/*` files are
  owned by **in-progress** tasks #36/#37/#41/#53/#62/#63/#64 (and several Emit files are
  dirty in the working tree right now). **MUST-WAIT.** Do not touch.

---

## WARTs — cosmetic / candidly-documented narrowness

- **W-A — refinement covers 2 of ~30 effects.** `concreteTransfer`/`concreteWriteField` are
  the only concrete ops; the Neutral/Monotonic/Terminal family (`Exec/EffectsState.lean:19-37`)
  and `recKDelegateAtten`/nullifier/revocation/escrow/queue have no concrete twin. This is
  candidly the validation scope of a beachhead refinement layer, not a hidden gap. Widen as
  node-grade execution demands it (task #14). Unowned, low priority.
- **W-B — anti-ghost `restFrame := True` in some Witness `#guard`s.** `rhConcrete`
  (e.g. NoteSpendWitness `:50-52`, `CreateEscrowWitness:110`) is a weighted field-count that
  collapses cell/caps/bal — deliberately non-injective, so the rest-frame gate is decorative
  *in those witnesses*. The keystone `refP2` (`refP2_injOn`, PROVED on `BoundedBy` lists) IS
  genuinely injective and distinguishes cons/drop/reorder/rights-swap; the toothful witnesses
  use it. Document which witnesses use the sponge vs the real fold. Witness files; check
  ownership before editing.
- **W-C — `hole_circuit_step := fullActionStep` tautology.** The generic-hole fallback's
  `circuit ⊑ spec` reduces to `fullActionStep ⊑ fullActionStep`. Per the comment the live
  arm is "now a REAL composite step" and this fallback is dead/unused. Delete the dead arm to
  remove the lookalike. Circuit-owned — MUST-WAIT.
- **W-D — boundDelta fail-OPEN / clearanceGe wiring.** `Authority/.../Program.lean` ~280/347.
  Per task #55/#56/#57 this is **live work being closed** by a running workflow (the silent
  `true` fail-OPEN hole). Known-and-being-addressed, NOT a novel finding. **MUST-WAIT** — do
  not race the workflow writing this file.

---

## Honest one-line verdict

The crown jewels are **SOUND**: ConcreteKernel's refinement squares, the `*_full_sound`
keystones, and the distributed/CapTP safety teeth are all genuine, non-vacuous, and
`#assert_axioms`-clean — nothing load-bearing is secretly trivial or false. What is broken
is **reach, not truth**: two docstrings promised theorems that don't exist (GC `gcDropTotal`
bridge F1, per-asset concrete square F2 — both now corrected), the per-asset keystone and
the cell-commitment cross-binding (MID-2, MID-4) are proven abstractly but not refined to
the running surface, and one distributed headline ("equivocation repels settlement", MID-3)
is true only for *unsigned* forks. The jewels are real; they just don't yet cover as much
ground as their prose claims.

( ◕‿◕ ) the proofs hold — it's the captions that overreached.
