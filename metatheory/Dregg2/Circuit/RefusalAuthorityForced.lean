/-
# Dregg2.Circuit.RefusalAuthorityForced — refusal's authority change is FORCED IN-CIRCUIT
  via the OPENABLE-fields_root insertion (the #103 ledgerless-authority close, build-half).

## The gap this closes

`refusal`'s authority change is the write of an audit record into the protocol-reserved
`fields_root` key (`REFUSAL_AUDIT_EXT_KEY`):

    post_fields_root = insert(pre_fields_root_map, REFUSAL_AUDIT_KEY → audit)
    audit = blake3_keyed("dregg-refusal-audit-v1",
              offered_action_commitment ++ reason_tag ++ reason_hash)

The deployed `fields_root` (`cell::state::compute_fields_root`) is a sponge over the WHOLE map, so
the post-root depends on every entry — a LEDGERLESS client cannot recompute it, and today the
verifier anchors it OFF-CIRCUIT from the trusted post-cell (`Anchor::RecordDigest`). The
proven `rotateV3WithFieldsRootGate` cannot fix this (it welds `prmCol 0` = the target, not the
post-root). The real fix is an OPENABLE root: model `fields_root` as the SAME sorted-Poseidon2
binary Merkle commitment the capability / heap roots use (`crate::openable_fields_root` Rust-side),
and FORCE the post-root in-circuit as the single-leaf insertion of the public audit at the audit key.

## What this file forces (over the PROVEN gadget interface — no new chip seam)

We reuse the keystone gadget `SortedTreeNonMembership` exactly as `CapTreeUpdate` does. The openable
`fields_root` is a `CapHashScheme`-committed sorted tree; `SpineCommits S8 root spine` is the
realizable spine↔root binding (a HYPOTHESIS the chip discharges, never an axiom), and `MembersAt S
root leaf` is the depth-16 binary-Merkle recompose (the proven `DeployedCapOpen` chip soundness).

The refusal audit is a leaf at the audit key carrying the PUBLIC audit as its value. A verifying
refusal proof supplies:
  * the pre-`fields_root` binding (`SpineCommits S8 preRoot spine`),
  * the audit-key non-membership in the pre-root (`auditKey ∉ keysOf S8 preRoot` — a fresh insert; the
    refusal-re-fires overwrite is the `capUpdateAt` shape, also covered),
  * the post-`fields_root` binding at the INSERTED spine (`SpineCommits S8 postRoot (sortedInsert
    auditKey spine)`) — THE in-circuit insertion-gate output, the SAME recompute the membership open
    realizes, NOT a free post-root column.

We then prove:

  * `refusal_authority_forced_in_circuit` — the post-root's committed key set is EXACTLY the pre-set
    plus the audit key (the audit record genuinely lands), and the audit key is PRESENT after; and
  * `forged_refusal_post_root_absurd` (THE TOOTH) — a "forged" refusal whose post-root does NOT commit
    the audit key (claims `auditKey ∉ keysOf S8 postRoot`) is CONTRADICTORY given the insertion-gate
    binding — UNSAT via the proof ALONE, no executor, no trusted post-cell. Honest refusal
    (the insertion holds) proves the key lands.

## What this does NOT do (the honest seam — named, carried by the live-wire)

This forces the KEY-SET move of the openable `fields_root`. The lift to the deployed sponge
`compute_fields_root` (the cell's CURRENT representation) is the faithful-encoding residual the
live-wire re-points: `cell/src/state.rs` adopts the openable `OpenableFieldsTree` as its `fields_root`
representation, and `EffectVmEmitRotationV3.lean`'s refusal row re-points to this insertion gate
(dropping the `Anchor::RecordDigest`). We do NOT fake that representation change here; this is the
in-circuit FORCING layer the re-point consumes.

## Axiom hygiene

`#assert_axioms` ⊆ {propext, Classical.choice, Quot.sound} + the realizable `CapHashScheme` /
`SpineCommits` carriers inherited from `DeployedCapTree` / `SortedTreeNonMembership` (the SAME
single-permutation-call `Compress1CR` floor #4 the commitment tower carries; the spine↔root binding,
a HYPOTHESIS). NEW file; imports read-only.
-/
import Dregg2.Circuit.CapTreeUpdate

namespace Dregg2.Circuit.RefusalAuthorityForced

open Dregg2.Circuit.DeployedCapTree (CapLeaf CapHashScheme Cap8Scheme Digest8)
open Dregg2.Circuit.SortedTreeNonMembership
  (keyOf SpineCommits keysOf keysOf_eq_spine sortedInsert mem_sortedInsert update_sound)
open Dregg2.Circuit.CapTreeUpdate (capInsert_sound capUpdateAt_sound capUpdateAt_present)

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## §1 — the FRESH-key refusal: the audit record lands, FORCED by the insertion gate. -/

/-- **`refusal_authority_forced_in_circuit` — THE FORCED KEY-SET MOVE.** A verifying refusal proof
binds: the pre-`fields_root` commits `spine`; the audit key is FRESH in the pre-root (the audit slot
was empty); and the post-`fields_root` commits `sortedInsert auditKey spine` (the in-circuit
insertion-gate recompute). Then the post-root's committed key set is EXACTLY the pre-set plus the
audit key — the refusal audit GENUINELY landed, derived in-circuit from `(preRoot + auditKey)`, with
NO trusted post-cell. A thin specialization of the proven `capInsert_sound`. -/
theorem refusal_authority_forced_in_circuit (S8 : Cap8Scheme)
    (preRoot postRoot : Digest8) (auditKey : ℤ) (spine : List ℤ)
    (hpre : SpineCommits S8 preRoot spine)
    (hfresh : auditKey ∉ keysOf S8 preRoot)
    (hpost : SpineCommits S8 postRoot (sortedInsert auditKey spine)) :
    ∀ y, y ∈ keysOf S8 postRoot ↔ (y = auditKey ∨ y ∈ keysOf S8 preRoot) :=
  capInsert_sound S8 preRoot postRoot auditKey spine hpre hfresh hpost

/-- **`refusal_audit_present_after`** — corollary: after a verifying refusal the audit key is PRESENT
in the post-`fields_root` (the audit record is genuinely committed, derived in-circuit). -/
theorem refusal_audit_present_after (S8 : Cap8Scheme)
    (preRoot postRoot : Digest8) (auditKey : ℤ) (spine : List ℤ)
    (hpre : SpineCommits S8 preRoot spine)
    (hfresh : auditKey ∉ keysOf S8 preRoot)
    (hpost : SpineCommits S8 postRoot (sortedInsert auditKey spine)) :
    auditKey ∈ keysOf S8 postRoot :=
  (refusal_authority_forced_in_circuit S8 preRoot postRoot auditKey spine hpre hfresh hpost
    auditKey).mpr (Or.inl rfl)

/-! ## §2 — THE TOOTH: a forged refusal whose post-root does NOT commit the audit is UNSAT. -/

/-- **`forged_refusal_post_root_absurd` — THE RAZOR (UNSAT via the proof ALONE).** A "forged" refusal
that publishes the genuine insertion-gate binding (the post-root commits `sortedInsert auditKey
spine`) yet claims the audit key is ABSENT from the post-root (`auditKey ∉ keysOf S8 postRoot`) is
CONTRADICTORY: the insertion gate FORCES `auditKey ∈ keysOf S8 postRoot`. So no satisfying assignment
publishes a post-`fields_root` that lacks the audit — there is NOTHING for a trusted post-cell to
anchor; the proof binds it. (NO executor, NO trusted post-cell.) -/
theorem forged_refusal_post_root_absurd (S8 : Cap8Scheme)
    (preRoot postRoot : Digest8) (auditKey : ℤ) (spine : List ℤ)
    (hpre : SpineCommits S8 preRoot spine)
    (hfresh : auditKey ∉ keysOf S8 preRoot)
    (hpost : SpineCommits S8 postRoot (sortedInsert auditKey spine))
    (hforged : auditKey ∉ keysOf S8 postRoot) : False :=
  hforged (refusal_audit_present_after S8 preRoot postRoot auditKey spine hpre hfresh hpost)

/-! ## §3 — the OVERWRITE (refusal re-fires): the audit slot is updated in place; the key set is
preserved and the audit key stays present. The `capUpdateAt` shape. -/

/-- **`refusal_overwrite_preserves_keys`** — a refusal that re-fires (the audit key was ALREADY
present) updates the audit slot's VALUE in place: the post-root commits the SAME spine (the leaf
value moved, the key set did not). The committed key set is unchanged and the audit key stays
present. The leaf-VALUE move (old audit → new audit) is the named faithful-encoding residual the
membership open carries; this forces the SET preservation. -/
theorem refusal_overwrite_preserves_keys (S8 : Cap8Scheme)
    (preRoot postRoot : Digest8) (auditKey : ℤ) (spine : List ℤ)
    (hpre : SpineCommits S8 preRoot spine)
    (hpresent : auditKey ∈ keysOf S8 preRoot)
    (hpost : SpineCommits S8 postRoot spine) :
    (∀ y, y ∈ keysOf S8 postRoot ↔ y ∈ keysOf S8 preRoot) ∧ auditKey ∈ keysOf S8 postRoot :=
  ⟨capUpdateAt_sound S8 preRoot postRoot auditKey spine hpre hpresent hpost,
   capUpdateAt_present S8 preRoot postRoot auditKey spine hpre hpresent hpost⟩

/-! ## §4 — non-vacuity: the forcing is LOAD-BEARING (the audit key MOVES into the committed set).

Over a concrete spine, the FRESH insert genuinely adds the audit key (the set grows); re-inserting
yields the audit key in the inserted spine. A `:= True` / identity stub would break these `#guard`s
(the audit key would not appear). -/

private def demoSpine : List ℤ := [10, 20, 30]
private def auditKey : ℤ := 25  -- a fresh key strictly between two present keys

-- The insertion genuinely ADDS the audit key to the spine (the committed set grows):
#guard sortedInsert auditKey demoSpine == [10, 20, 25, 30]
-- ...and the audit key is now a member of the inserted spine (the forcing is real):
#guard (decide (auditKey ∈ sortedInsert auditKey demoSpine)) == true
-- ...while it was ABSENT before (the move is observable, not a no-op):
#guard (decide (auditKey ∈ demoSpine)) == false

/-! ## §5 — Axiom hygiene. -/

#assert_axioms refusal_authority_forced_in_circuit
#assert_axioms refusal_audit_present_after
#assert_axioms forged_refusal_post_root_absurd
#assert_axioms refusal_overwrite_preserves_keys

end Dregg2.Circuit.RefusalAuthorityForced
