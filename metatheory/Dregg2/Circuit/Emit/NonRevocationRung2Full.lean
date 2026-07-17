/-
# Dregg2.Circuit.Emit.NonRevocationRung2Full — the RUNG-2 **FULL discharge** for the emitted
non-revocation descriptor (`nonRevocationDesc`, the `revocation` family), now that the lower-bound fix
is IN the descriptor: the residual is discharged by the emitted circuit, and the pre-fix bug is retained
as a machine-checked historical witness.

## What Rung 2 left, and how the deployed fix makes it FULL

`NonRevocationRung2.lean` discharges Rung 1's `FieldCanonicalDiffs` residual (`0 ≤ DIFF_L ∧ 0 ≤ DIFF_R`)
from the carrier `DiffLowerRangeSound` (the diff wires themselves lie in `[0, 2^30)`). Before the fix
that carrier had to be RE-ASSUMED. The deployed `nonRevocationDesc` now carries two DIRECT range lookups
`.lookup ⟨range, [.var DIFF_L]⟩` / `.lookup ⟨range, [.var DIFF_R]⟩`, so `Satisfied2` forces
`[DIFF_L], [DIFF_R] ∈ tf.range`; `RangeTableSound` on those columns discharges `DiffLowerRangeSound`
UNCONDITIONALLY (Rung 2's `sat_forces_lowerRange`). `nonRevocation_full_discharge` therefore concludes
`NonMember spine x` from `Satisfied2` + only the STANDARD crypto carriers (`ChipTableSound` Poseidon2-CR,
`RangeTableSound`) — no re-assumed residual. `emitfix_yields_lowerRange` (kept) states the discharge at
the membership level; `fixTrace_lower` / `emitfixed_conclusion_fires` witness it is inhabited and fires
(`200 ∉ [100,300]`).

## The closed bug (historical witness) + why the fix was the honest closure

The gap the fix closed: the OLD 12-constraint descriptor (`nonRevocationDescPreFix`, in Rung 2)
range-checked only the range-WIRES `RL = HALF_P_MINUS_1 − DIFF_L` / `RR`, never `DIFF_L`/`DIFF_R`
themselves. Over ℤ the single `RL ∈ [0, 2^30)` lookup bounded `DIFF_L ∈ [−2^26, HALF_P_MINUS_1]`
(`satisfied_admits_negative_window`, `window_width`), so `DIFF_L ≥ 0` — i.e. `x > L` — was un-forced,
admitting a revoked-item freshness forgery. Two reasons that gap could not be crypto/anchor-discharged
(and so REQUIRED the emit-fix), each still machine-checked here about the PRE-FIX descriptor:

  1. **No commitment bound the diffs.** The descriptor commits only the leaves/root (Poseidon2 chip,
     `hash [hash [L,R], sib]`) and exposes `x` publicly. `DIFF_L` was a free witness column, hashed into
     nothing — no CR carrier could pin it. `prefix_carriers_do_not_force_nonmembership` re-exports the
     concrete pre-fix member-forgery witnessing this.

  2. **The DFA-style reference-object anchor is CIRCULAR here.** `bracketing_anchor_alone_forces_nonmember`
     shows a genuine bracketing anchor (`lo < x < hi`, adjacent, sorted) yields `NonMember spine x` with
     the trace UNUSED — the conclusion is over the PUBLIC `(spine, x)` the anchor already shares, so an
     anchor-conditioned "discharge" is P→P; and on the member-forgery NO anchor exists
     (`member_has_no_bracketing_anchor`). `reference_anchor_route_is_circular` packages both halves. So
     the residual had to be closed by the DIRECT diff range lookups — the deployed fix, not an anchor.

## Axiom hygiene
`#assert_axioms` ⊆ {propext, Classical.choice, Quot.sound}. Poseidon2 CR rides only as the NAMED
`ChipTableSound`; the range argument only as the NAMED `RangeTableSound`; `sorted_gap_excludes` is
unconditional combinatorics. The member-forgery / honest witnesses are REUSED from Rung 2 (no re-proof
of `Satisfied2`), referenced through their public theorems. NEW file; all imports read-only.
-/
import Dregg2.Circuit.Emit.NonRevocationRung2

namespace Dregg2.Circuit.Emit.NonRevocationRung2Full

open Dregg2.Circuit (Assignment)
open Dregg2.Circuit.DescriptorIR2 (Satisfied2 VmTrace envAt ChipTableSound Table TableId)
open Dregg2.Circuit.Emit.NonRevocationEmit
open Dregg2.Circuit.Emit.NonRevocationRefine
open Dregg2.Circuit.Emit.NonRevocationRung2
open Dregg2.Crypto.NonMembership (Sorted Adjacent NonMember sorted_gap_excludes)

set_option autoImplicit false

/-! ## §1 — THE DEPLOYED FIX CLOSES THE GAP (the two direct diff range lookups).

`nonRevocationDesc` carries `.lookup ⟨range, [.var DIFF_L]⟩` / `.lookup ⟨range, [.var DIFF_R]⟩`. Under
`Satisfied2` those lookups put `[DIFF_L]`, `[DIFF_R]` into the looked-up range table (exactly the `range0`
extraction Rung 1 runs on `RL`/`RR`). Against `RangeTableSound` this yields `DiffLowerRangeSound`
UNCONDITIONALLY — no re-assumed residual. This is the machine-checked statement that the emit change
makes Rung 2 FULL. -/

/-- **`emitfix_yields_lowerRange`** — with the two diff range memberships (which the descriptor's direct
lookups supply under `Satisfied2`) in hand, `RangeTableSound` discharges the named `DiffLowerRangeSound`
carrier directly (via `range_lookup_sound`, the Rung-1 range lever). No re-assumption. -/
theorem emitfix_yields_lowerRange {t : VmTrace}
    (hRange : RangeTableSound ORDERING_BITS (t.tf .range))
    (hDiffL : [(envAt t 0).loc DIFF_L] ∈ t.tf .range)
    (hDiffR : [(envAt t 0).loc DIFF_R] ∈ t.tf .range) :
    DiffLowerRangeSound t :=
  ⟨range_lookup_sound hRange _ hDiffL, range_lookup_sound hRange _ hDiffR⟩

/-- **`nonRevocation_full_discharge` — THE FULL DISCHARGE (the emit-fix is now IN the descriptor).**
The lower-bound fix's two range lookups are present in the deployed `nonRevocationDesc`, so a `Satisfied2`
active-row-0 window against the two STANDARD carriers (`ChipTableSound` Poseidon2-CR, `RangeTableSound`)
forces the genuine non-membership `NonMember spine x` — with NO `FieldCanonicalDiffs` /
`DiffLowerRangeSound` re-assumed. The descriptor's own diff range lookups supply `[DIFF_L], [DIFF_R] ∈
tf.range` (Rung 2's `sat_forces_lowerRange`), so `nonRevocation_rung2` is now unconditional. The residual
is DISCHARGED by the emitted circuit, not re-named. -/
theorem nonRevocation_full_discharge {hash : List ℤ → ℤ} {t : VmTrace} {minit : ℤ → ℤ}
    {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ}
    (hlen : 0 < t.rows.length)
    (hsat : Satisfied2 hash nonRevocationDesc minit mfin maddrs t)
    (hChip : ChipTableSound hash (t.tf .poseidon2))
    (hRange : RangeTableSound ORDERING_BITS (t.tf .range))
    (hcanon : NonRevCanon t)
    (spine : List ℤ) (hsorted : Sorted spine)
    (hadj : Adjacent spine ((envAt t 0).loc LEAF_L) ((envAt t 0).loc LEAF_R)) :
    NonMember spine ((envAt t 0).loc X) :=
  nonRevocation_rung2 hlen hsat hChip hRange hcanon spine hsorted hadj

#assert_axioms emitfix_yields_lowerRange
#assert_axioms nonRevocation_full_discharge

/-! ## §2 — Non-vacuity of the closure: the emit-fix carrier is genuinely inhabited.

A minimal one-row trace with the honest diffs `DIFF_L = DIFF_R = 99` and a range table containing `[99]`
(what the descriptor's direct diff lookups range-check). `emitfix_yields_lowerRange` fires on it:
`DiffLowerRangeSound` is realizable — not an empty antecedent. (The full conclusion firing end-to-end is
`honest_rung2_fires` from Rung 2: `NonMember [100,300] 200`.) -/

private def fixRange : List (List ℤ) := [[99]]

private def fixRow : Assignment := fun c => if c = DIFF_L then 99 else if c = DIFF_R then 99 else 0

private def fixTrace : VmTrace :=
  { rows := [fixRow], pub := fun _ => 0
    tf := fun tid => match tid with
      | .range => fixRange
      | _ => [] }

private theorem fixTrace_rangeSound : RangeTableSound ORDERING_BITS (fixTrace.tf .range) := by
  intro r hr
  simp only [fixTrace, fixRange, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl
  exact ⟨99, rfl, by decide, by decide⟩

/-- The carrier `DiffLowerRangeSound` is inhabited: derived from `RangeTableSound` and the two range
memberships the descriptor's diff lookups supply. So `nonRevocation_full_discharge` is over a satisfiable
hypothesis set. -/
theorem fixTrace_lower : DiffLowerRangeSound fixTrace := by
  have eL : (envAt fixTrace 0).loc DIFF_L = 99 := rfl
  have eR : (envAt fixTrace 0).loc DIFF_R = 99 := rfl
  have hL : [(envAt fixTrace 0).loc DIFF_L] ∈ fixTrace.tf .range := by
    rw [eL]; show [(99 : ℤ)] ∈ fixRange; simp [fixRange]
  have hR : [(envAt fixTrace 0).loc DIFF_R] ∈ fixTrace.tf .range := by
    rw [eR]; show [(99 : ℤ)] ∈ fixRange; simp [fixRange]
  exact emitfix_yields_lowerRange fixTrace_rangeSound hL hR

/-- The FULL conclusion is achievably true (not vacuous): the emit-fixed discharge's endpoint is the
genuine non-membership `200 ∉ [100,300]`, witnessed by Rung 2's end-to-end honest fire. -/
theorem emitfixed_conclusion_fires : NonMember ([100, 300] : List ℤ) 200 := honest_rung2_fires

#assert_axioms fixTrace_lower
#assert_axioms emitfixed_conclusion_fires

/-! ## §3 — The PRE-FIX carriers did NOT force non-membership (the closed bug, historical witness).

As emitted BEFORE the fix (`nonRevocationDescPreFix`, no diff range lookups), `Satisfied2` + the standard
carriers did NOT force non-membership: a revoked (present) item forged freshness through the `2^26`
negative window. Re-exported from Rung 2's `prefix_carriers_admitted_forgery` as a clean existential — no
re-proof of `Satisfied2`. The DEPLOYED fixed descriptor rejects this forgery (`fixed_forbids_the_forgery`);
this theorem is retained as a TRUE record that the bug was real. -/

/-- **`prefix_carriers_do_not_force_nonmembership`** — there is a trace on which the PRE-FIX descriptor's
`Satisfied2` + `ChipTableSound` + `RangeTableSound` all hold, the committed spine is sorted with the
bracketing leaves adjacent, yet the queried item is a genuine MEMBER (`¬ NonMember`) and the residual
`FieldCanonicalDiffs` is violated. So NO theorem concluding `NonMember` from the PRE-FIX carriers alone
could exist — the exact hole the lower-bound fix closes. -/
theorem prefix_carriers_do_not_force_nonmembership :
    ∃ (hash : List ℤ → ℤ) (t : VmTrace) (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ)
      (spine : List ℤ),
      Satisfied2 hash nonRevocationDescPreFix minit mfin maddrs t
      ∧ ChipTableSound hash (t.tf .poseidon2)
      ∧ RangeTableSound ORDERING_BITS (t.tf .range)
      ∧ Sorted spine
      ∧ Adjacent spine ((envAt t 0).loc LEAF_L) ((envAt t 0).loc LEAF_R)
      ∧ (envAt t 0).loc X ∈ spine
      ∧ ¬ NonMember spine ((envAt t 0).loc X)
      ∧ ¬ FieldCanonicalDiffs t :=
  ⟨_, _, _, _, _, _, prefix_carriers_admitted_forgery⟩

#assert_axioms prefix_carriers_do_not_force_nonmembership

/-! ## §4 — Why the DFA-style reference-object anchor is CIRCULAR for this family.

The DFA template discharges `hterm` by anchoring to a genuine reference RUN whose route-commitment
matches the public one: the CR binding transfers the run's genuine last transition onto `t`, and the
conclusion `final = classify(t.input)` is about `t`'s OWN read input — the circuit does real work.

Here the security conclusion `NonMember spine x` is over the PUBLIC `(spine, x)` any anchor already
shares, so a genuine bracketing anchor implies it with the trace UNUSED (P→P), and on the member-forgery
no anchor exists at all. Hence there is no non-circular reference-object discharge for `revocation`. -/

/-- **`bracketing_anchor_alone_forces_nonmember` — THE CIRCULARITY WITNESS.** A genuine bracketing
anchor (`lo < x < hi`, `lo`/`hi` adjacent in the sorted spine) yields the FULL security conclusion
`NonMember spine x` via `sorted_gap_excludes` alone — no `Satisfied2`, no trace, no CR. So conditioning
a "discharge" on such an anchor is P→P: the circuit is inert. (In DFA the analogous conclusion is about
`t`'s own read input and must be bridged from the anchor by the route-commitment CR — not inert.) -/
theorem bracketing_anchor_alone_forces_nonmember
    (spine : List ℤ) (lo hi x : ℤ)
    (hsorted : Sorted spine) (hadj : Adjacent spine lo hi)
    (hlo : lo < x) (hhi : x < hi) :
    NonMember spine x :=
  ⟨hsorted, sorted_gap_excludes spine lo hi x hsorted hadj hlo hhi⟩

/-- On a MEMBER, no genuine bracketing anchor exists — so the anchor premise is exactly the conclusion
`x ∉ spine`, i.e. assuming an anchor is assuming non-membership. Contrapositive of the circularity
witness. -/
theorem member_has_no_bracketing_anchor (spine : List ℤ) (x : ℤ) (hmem : x ∈ spine) :
    ¬ ∃ lo hi : ℤ, Sorted spine ∧ Adjacent spine lo hi ∧ lo < x ∧ x < hi := by
  rintro ⟨lo, hi, hsorted, hadj, hlo, hhi⟩
  exact (bracketing_anchor_alone_forces_nonmember spine lo hi x hsorted hadj hlo hhi).2 hmem

/-- **`reference_anchor_route_is_circular` — WHY THE PRE-FIX GAP WAS CLOSED BY THE EMIT-FIX, NOT AN
ANCHOR.** (a) The anchor ALONE forces the conclusion (a reference-object "discharge" does no circuit
work — P→P where true); AND (b) on the PRE-FIX member-forgery, `Satisfied2` + both standard carriers held
with the spine sorted and the leaves adjacent, yet NO bracketing anchor existed (the conclusion was
false). So a reference-object discharge was either circular (a) or unavailable (b) — never a load-bearing
bridge. That is why `revocation`'s residual had to be closed by the DIRECT diff range lookups (the
lower-bound fix, now in the descriptor: `nonRevocation_full_discharge`), not anchored away like DFA's
`hterm`. -/
theorem reference_anchor_route_is_circular :
    (∀ (spine : List ℤ) (lo hi x : ℤ),
        Sorted spine → Adjacent spine lo hi → lo < x → x < hi → NonMember spine x)
    ∧ (∃ (hash : List ℤ → ℤ) (t : VmTrace) (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ)
         (spine : List ℤ),
         Satisfied2 hash nonRevocationDescPreFix minit mfin maddrs t
         ∧ ChipTableSound hash (t.tf .poseidon2)
         ∧ RangeTableSound ORDERING_BITS (t.tf .range)
         ∧ Sorted spine
         ∧ Adjacent spine ((envAt t 0).loc LEAF_L) ((envAt t 0).loc LEAF_R)
         ∧ ¬ ∃ lo hi : ℤ, Sorted spine ∧ Adjacent spine lo hi
              ∧ lo < (envAt t 0).loc X ∧ (envAt t 0).loc X < hi) := by
  refine ⟨fun spine lo hi x hs ha hl hh =>
    bracketing_anchor_alone_forces_nonmember spine lo hi x hs ha hl hh, ?_⟩
  obtain ⟨hash, t, minit, mfin, maddrs, spine, hsat, hChip, hRange, hsorted, hadj, hmem, _, _⟩ :=
    prefix_carriers_do_not_force_nonmembership
  exact ⟨hash, t, minit, mfin, maddrs, spine, hsat, hChip, hRange, hsorted, hadj,
    member_has_no_bracketing_anchor spine ((envAt t 0).loc X) hmem⟩

/-- Non-vacuity of §4 (TRUE half): the anchor implication is not empty — it fires on the honest
bracketing to prove `200 ∉ [100,300]`. -/
theorem bracketing_anchor_fires : NonMember ([100, 300] : List ℤ) 200 :=
  bracketing_anchor_alone_forces_nonmember [100, 300] 100 300 200
    (by simp [Sorted, List.pairwise_cons]) ⟨[], [], rfl⟩ (by norm_num) (by norm_num)

#assert_axioms bracketing_anchor_alone_forces_nonmember
#assert_axioms member_has_no_bracketing_anchor
#assert_axioms reference_anchor_route_is_circular
#assert_axioms bracketing_anchor_fires

end Dregg2.Circuit.Emit.NonRevocationRung2Full
