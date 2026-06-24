# Proof-Integrity Ledger — severity-ranked

Synthesized 2026-06-08 from the audit + adversarial-verification rounds (R0/R1/R2/R3 +
two independent VERIFY passes per region). Every cited line below was re-checked against
source by reading theorem **bodies**, not grep counts. Build was GREEN at synthesis
(`lake build` Dregg2+Metatheory, ~3828 jobs; the audited soundness
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
  and a `gcDropTotal`-tracks-decrement lemma, or (b) make the prose honest. SUPERSEDED by
  option (a): the bridge is now a real set of kernel-clean theorems (see MID-1, RESOLVED
  2026-06-08). `gcDropTotal` is no longer vapor — it is `bridge_processDrop_tracks_refcount`.
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

### MID-1 — GC bridge theorem (the real fix behind F1) — RESOLVED 2026-06-08
- **What:** prove `swissEntry.refcount = Σ_{holders} holder.total_refs` and a
  `processDrop`-decrement-tracks-`swissDropA` lemma, welding §2 to §1.
- **Why MID not FATAL:** both halves are independently sound and `#assert_axioms`-clean; the
  Byzantine session tooth (`byzantine_node_different_session_cannot_drop_others_refs`) and
  the refcount-positivity teeth genuinely bite. Only the *unification* was missing.
- **Fix (DONE):** `Exec/CapTPGCConcrete.lean` §2.5 now PROVES the bridge as real theorems
  (kernel-clean, subset `{propext, Classical.choice, Quot.sound}`):
  - `SwissHoldersCoherent refc t := refc = totalRefs t` — the swiss-entry scalar IS the
    per-holder sum (not an aggregate standing in for a per-holder fact: a full equality the
    joint step preserves). NON-VACUOUS: `coherent_demo` (TRUE), `not_coherent_demo` (FALSE on
    `3 ≠ 2`); `NoDupFeds` witnessed admit/reject (`nodup_demo` / `not_nodup_dup`).
  - `decHolder_pred_total` — under the `HashMap` key-uniqueness invariant `NoDupFeds`, an
    accepting per-holder drop lowers `totalRefs` by EXACTLY one (the unit-exact decrement;
    helper lemmas `decHolderMap_not_mem` / `decHolderFilter_not_mem` / `totalRefs_pos_of_findHolder`).
  - `processDrop_accept_table` + `bridge_processDrop_tracks_refcount` — §2's REAL `gc.rs`
    verdict function `processDrop` accept-path post-table sums to the DECREMENTED §1 scalar
    `refc - 1` (`gcDropTotal` made real: per-holder drop tracks the scalar `swissDropK` writes).
  - `swissDropK_writes_scalar_pred` — §1's verified GC arm writes exactly `refcount - 1` on the
    `> 1` branch; `bridge_last_ref_iff` — §2's `canRevoke` (sum hits 0) ⟺ §1's GC-at-zero
    (scalar hits 0): they reclaim EXACTLY together.
  - `bridge_swiss_refcount_eq_holders_sum` — the end-to-end weld over BOTH real functions: under
    coherence + key-uniqueness + an accepting matched-session drop, the POST swiss entry that
    `swissDropK` commits has `refcount` equal to the POST holder-table sum.
  - `#assert_axioms` tripwires added for all 12 new declarations.

### MID-2 — `concreteTransferAsset` refinement square (the real fix behind F2) — **RESOLVED**
- **What:** the per-asset concrete op + square + corollary (see F2).
- **Why MID:** the abstract per-asset keystone is fully proven; only the concrete *mirror*
  was absent, so node-grade execution could not yet *carry* per-asset conservation — but the
  guarantee was not false, just not refined down.
- **FIX LANDED** (`Dregg2/Exec/ConcreteKernel.lean` §5b/§5c): `concreteTransferAsset`
  (the `balMap : Std.HashMap (CellId × AssetId) ℤ`-backed, fail-closed twin of the abstract
  `recKExecAsset`, RecordKernel.lean:756) + the `Option`-level commuting square
  `toAbstract_concreteTransferAsset` (gate matches via `toAbstract_caps/accounts/bal`; ledger
  half `toAbstract_balMap_transferAsset` collapses the product-key `getD_insert`s to the
  abstract `recTransferBal`) + the PROOF-TRANSFER corollary
  `concreteTransferAsset_conserves_per_asset` carrying `recTotalAsset _ b` FOR EVERY asset `b`
  down through the square from the abstract keystone `recKExecAsset_conserves_per_asset`
  (RecordKernel.lean:801), with ZERO HashMap reasoning redone. Plus
  `concreteTransferAsset_no_cross_asset_leak` (cross-asset non-laundering at node grade).
  Build green (919 jobs); all four new theorems `#assert_axioms`-clean
  (`{propext, Classical.choice, Quot.sound}`). Non-vacuity witnessed BOTH ways
  in §6b (`demoAssetCS`/`demoAssetTurn`): a genuine commit moving asset 0 (100→70, 5→35) with
  asset 1 untouched, AND two fail-closed rejects (over-amount ⇒ `none`, unauthorized actor ⇒
  `none`). Task #14.

### MID-3 — ConsentLace "equivocation repels settlement" is a weaker lookalike — **RESOLVED 2026-06-08**
- **Claims (original):** `Exec/CapTPConsentLace.lean:333-339` `equivocating_party_blocks_settlement` —
  headline "a byzantine consenter is repelled."
- **Why weak (original):** the block was driven **entirely** by the hypothesis
  `hReject : partySignedConsent B p digest = false`; the equivocation premise `hfork` fed
  **only** the `Equivocator` detection tag, not the block. The witness `fork9approve` discharged
  `hReject` by setting the approve branch `signed := false` — i.e. only an **unsigned** fork was
  repelled. A party that signs a *valid* approve AND a conflicting revoke (a genuine **signed**
  equivocation) has `partySignedConsent = true` and **would settle**. The missing theorem was
  "signed-equivocation ⇒ consent not counted."
- **FIX LANDED** (`Dregg2/Exec/CapTPConsentLace.lean` §7.5 + §9.0): the strengthened settlement
  validator now DROPS a detected signed equivocator's consent — the exclusion is part of the gate,
  not a downstream policy hypothesis. New, all `#assert_axioms`-clean (subset
  `{propext, Classical.choice, Quot.sound}`; axioms verified via `#print axioms`):
  - `isRevokeFor` / `partySignedRevoke` — the signed-revoke twin of `isApprovalFor`.
  - `equivocatesSigned B p digest := partySignedConsent && partySignedRevoke` — the DECIDABLE
    signed-fork detector (`p` signed BOTH a valid approve AND a valid revoke over the same digest;
    **both** signatures verifying — NOT an unsigned accident).
  - `consentCounted B p digest := partySignedConsent && !equivocatesSigned` — the REAL per-party
    gate: a signed equivocator's consent does NOT count. `laceSettleExcl` gates on the n-ary
    `consentLaceCompleteExcl` over `consentCounted`.
  - `signed_equivocator_consent_not_counted` — a flagged signed equivocator has `consentCounted = false`.
  - **`settle_excludes_signed_equivocator`** — THE real keystone: a required party that signed both
    a valid approve AND a conflicting revoke has `laceSettleExcl = some k` (UNCHANGED, nothing
    commits). Driven by the equivocation ITSELF (via `signed_equivocator_consent_not_counted`), not
    by `hReject`. An equivocating party CANNOT cause a settlement to commit with their consent counted.
  - `equivocatesSigned_sound` — the detector flags a GENUINE fork: two present, signed, self-authored,
    same-digest blocks acking the conflicting approve/revoke markers (never an arbitrary drop).
  - `demo_signed_consent_equivocation` / `signedFork_no_precedes` / `demo_signed_fork_detected` —
    the signed fork is a real `Blocklace.Equivocator` (incomparable pair), so the exclusion rests on
    the same byzantine-repelling keystone as the unsigned case, now on a **fully-signed** fork.
- **Non-vacuity witnessed BOTH ways** (§9.0 / §9.0b): an equivocator-EXCLUDED settlement
  (`demoLaceSignedFork`: 9 signs approve id 102 + conflicting revoke id 105, both valid — the WEAK
  `laceSettle` is `#guard`'d to settle behind it, the STRENGTHENED `laceSettleExcl` freezes the
  batch to `some demoState`) AND an honest-settles case (`demoLaceAllSigned`: all three sign clean
  approves, none equivocate, `laceSettleExcl.isSome = true` — the gate does not over-block, caps
  preserved). The weaker `equivocating_party_blocks_settlement` is retained as the detection-tagging
  lemma it always was; the module docstring point 5 now states the real property.
- **Ownership:** `CapTPConsentLace.lean` — task #61 **completed**; no in-progress task. FIXED here.

### MID-4 — three disjoint state commitments, NO cross-binding theorem — **PARTIALLY RESOLVED; EffectVm-subset widening RESIDUAL (owned/MUST-WAIT)**
- **Status:** the cross-binding theorem itself is now LANDED in
  `Dregg2/Circuit/CommitmentCrossBind.lean` (built green this wave, 13 `#assert_axioms` tripwires):
  `stateCommit_binds_cellCommit` ("THE CROWN" — equal circuit
  full-state roots force equal canonical `cellCommit` per touched cell, under a hash-CR portal
  `LeafIsCellCommit`), its executor-side twin `setFieldCommit_binds_cellCommit`,
  `crossbind_circuit_exec_same_state` (circuit ⟺ executor agree on the SAME `RecordKernelState`),
  and `all_three_agree_on_eq_state` (the packaged "ONE object" fact). Non-vacuity witnessed BOTH
  ways: `chC_is_cellCommit` (a realizable injective Horner/positional cell-commit SATISFIES the
  leaf-bridge, TRUE) and `chC_bad` (a value-DROPPING leaf `CH c v := 0` FAILS it, FALSE). So the
  "three disjoint commitments, NO theorem relating any two" finding is addressed: the weld exists,
  gated honestly on a named hash collision-resistance portal (the §8 crypto seam, witnessed false on
  a collapsing carrier — not `:=True`).
- **RESIDUAL (still owned / MUST-WAIT):** widening the EffectVm descriptor `state_commit` subset
  `{bal_lo,bal_hi,nonce,field[0..7],cap_root}` to the full field set lives in `Circuit/Emit/*`,
  owned by in-progress tasks #36/#37/#41/#53/#62/#63/#64 and explicitly off-limits to this
  path-limited commit. That widening is the remaining MID-4 work, for the owning circuit workflow.
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
`#assert_axioms`-clean — nothing load-bearing is secretly trivial or false.

**Wave close (2026-06-08): MID-1, MID-2, MID-3 RESOLVED; MID-4 PARTIALLY RESOLVED (residual
owned).** The GC §1↔§2 bridge is real (MID-1, `bridge_swiss_refcount_eq_holders_sum`); the
per-asset concrete refinement square carries `recTotalAsset` for EVERY asset down to node grade
(MID-2, `concreteTransferAsset_conserves_per_asset` — NOT an aggregate scalar standing in); the
ConsentLace equivocation headline is now the REAL property (MID-3, `settle_excludes_signed_equivocator`
— a SIGNED equivocator's consent is DROPPED at the gate, witnessed both ways); and the
state-commitment cross-binding theorem is landed (MID-4, `stateCommit_binds_cellCommit` under a
named hash-CR portal), with only the EffectVm-subset widening left as the owned-task residual.
All four wave modules — `ConcreteKernel`, `CapTPGCConcrete`, `CommitmentCrossBind`,
`CapTPConsentLace` — build green and the new keystones are `#assert_axioms`-clean (subset
`{propext, Classical.choice, Quot.sound}`; named crypto hypotheses witnessed FALSE).

The jewels are real and now cover the ground their prose claims, save the one owned residual.

( ◕‿◕ ) the captions caught up to the proofs.
