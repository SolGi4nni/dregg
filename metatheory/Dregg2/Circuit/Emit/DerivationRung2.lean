/-
# Dregg2.Circuit.Emit.DerivationRung2 — the Rung-2 no-forgery layer for the Datalog DERIVATION AIR.

## What this file IS (and how the fix closes the body↔membership-leaf gap)

`DerivationRefine.lean` (Rung-1) proves the SAT_IMPLIES_SEM direction against the *head* chain:
a `Satisfied2` derivation trace publishes a conclusion that IS the genuine `hash_fact` of the head
(the C4 chip ∘ C6 pin crown), under the named `ChipTableSound` carrier. That leg is genuinely
enforced in-circuit.

The *body* chain is not authenticated by an in-circuit Merkle lookup. No constraint proves
`bodyHash i` (cols 1..8) IS a member of the committed root `pi[0]`:

* C2 (`DerivationEmit.lean:214`) forces only `flag_i · (hash_i · inv_i − 1) = 0` — nonzero-when-used.
  Over the ℤ field model this makes `bodyHash i` any UNIT (`±1`), authenticating nothing.
* C5 (`:226`) pins the SEPARATE decorative `bodyRoot i` column (cols 31..38) to `pi[0]` — but that
  column is never linked to `bodyHash i`. It authenticates the root against itself, not the fact.

So the descriptor ALONE still accepts a fabricated body fact — this file keeps the concrete
accepted-but-non-genuine witness (`der_accepts_fabricated_body_fact`) and PROVES it `Satisfied2`.

**The fix (held forgery #3).** Rather than add an in-circuit Merkle tooth (a shared-file layout
change), the deployed descriptor now EXPORTS body atom 0's fact hash as the public input `pi[5]`
(the new C6b pin + boundary, `DerivationEmit.lean:c6b`). `der_body_fact_exported` proves the binding:
every `Satisfied2` trace has `bodyHash 0 = pi[5]` on row 0. The fabricated hash the descriptor
accepts is therefore FORCED into a bound public handle. The full-turn verifier binds that handle to
the c-list membership leg's authenticated leaf (`membership.leaf_hash == derivation.pi[5]`), so a
forger who publishes `pi[5] = -1` must ALSO exhibit a membership proof for `-1` — which they do not
hold. `der_accepts_fabricated_body_fact` now publishes `pi[5] = -1` to stay accepted, exactly
witnessing that the residual (the missing in-circuit Merkle tooth) is closed at the COMPOSITION.

## The honest closure (a NAMED carrier, now DISCHARGEABLE via the export)

The genuine body-fact membership relation still enters as the NAMED carrier `BodyMembershipSound`,
the body-fact analog of `ChipTableSound`. The fix's payoff is `der_carrier_slot0_discharged_by_pi`:
the slot-0 conjunct of the carrier — undischarged by any in-circuit lookup — now FOLLOWS from a single
external fact about the exported PI (`DbMember pi[0] pi[5]`, what the membership leg proves), because
C6b binds `bodyHash 0 = pi[5]`. The AUDIT FIX (§5, `DerivationEmit.lean:c6c`) extends this to the
FURTHER body atoms: `bodyHash i = pi[5 + i]` for all eight slots, so `der_carrier_further_discharged`
composition-discharges slots 1..7 exactly as slot 0. A fully in-circuit Merkle tooth over the body
slots remains a layout change for a later rung, but every body-fact hash is now a BOUND public handle
(no longer a free witness), which is what the composition needs.

The carrier is proven LOAD-BEARING, not vacuous: it ACCEPTS the honest witness
(`honest_satisfies_membership`) and REJECTS the fabricated one (`forge_violates_membership`) — so it
is exactly the missing authentication, and the `bodyFactsMembers` conjunct of the full relation comes
WHOLLY from the carrier (the descriptor contributes zero to it — `der_authentic_needs_carrier`).

## Axiom hygiene

`#assert_axioms` ⊆ {propext, Classical.choice, Quot.sound}. The concrete `Satisfied2` witness is
decided; the membership carrier enters ONLY as a named hypothesis. NEW file; imports read-only.
-/
import Dregg2.Circuit.Emit.DerivationRefine

namespace Dregg2.Circuit.Emit.DerivationRung2

open Dregg2.Circuit (Assignment)
open Dregg2.Exec.CircuitEmit (EmittedExpr)
open Dregg2.Circuit.Emit.EffectVmEmit (VmConstraint VmRowEnv)
open Dregg2.Circuit.DescriptorIR2
open Dregg2.Circuit.Emit.DerivationEmit
open Dregg2.Circuit.Emit.DerivationRefine

set_option autoImplicit false
set_option maxRecDepth 8000

/-! ## §1 — The accepted-cheat-witness: a FABRICATED body fact the descriptor accepts.

`waForge` is the honest witness `wa` (`DerivationRefine.lean:381`) with ONE change: the active
body-fact hash `bodyHash 0` is flipped from the honest `1` to the fabricated unit `-1`, with its C2
inverse `bodyInv 0 = -1` (so `(-1)·(-1) = 1` keeps C2 nonzero-when-used satisfied). Every other
column — the head, the derived hash, the comparators, the substitution selectors — is byte-identical
to `wa`, so the C4 chip and C6/boundary pins fire identically. -/

/-- The forged row: `wa` with `bodyHash 0 = -1` (a fabricated non-member) and its matching inverse. -/
def waForge : Assignment := fun v =>
  if v = bodyFlag 0 then 1
  else if v = bodyHash 0 then (-1)
  else if v = bodyInv 0 then (-1)
  else 0

/-- The forged trace: two rows of `waForge`. Its chip table is REUSED from the honest witness
(`witTf`) — legitimate because the C4 fact-site tuple reads only head/derived/lane columns, all of
which are `0` in BOTH `wa` and `waForge`, so the evaluated tuples coincide.

`pub 5 = -1` publishes the FABRICATED body-fact hash at the C6b export slot (so the forge is still
`Satisfied2` — see below). This is the crux of the fix: the fabricated hash the descriptor accepts is
now FORCED into a BOUND public input `pi[5]`, which the full-turn verifier cross-checks against the
membership leg's authenticated leaf. A forger cannot both publish `pi[5] = -1` AND exhibit a c-list
membership proof for `-1` (they do not hold it) — so the composition rejects, even though the
derivation descriptor alone (lacking an in-circuit Merkle tooth) still accepts. -/
def forgeTrace : VmTrace :=
  { rows := [waForge, waForge], pub := fun i => if i = 5 then (-1) else 0, tf := witTf }

theorem forgeMemLog : memLog derivationDesc forgeTrace = [] := by
  simp [memLog, witMemOps]

theorem forgeMapLog : mapLog derivationDesc forgeTrace = [] := by
  simp [mapLog, witMapOps]

/-- **`der_accepts_fabricated_body_fact` — THE accepted-cheat-witness (the residual the descriptor
alone still cannot close).** The forged trace, whose active body fact `bodyHash 0 = -1` is NOT the
honest committed fact `1`, is in the deployed accept-set `Satisfied2 derivationDesc`: every one of the
393 gate/pin constraints holds on both rows (decided — C2 rides the fabricated `(-1)·(-1) = 1`
inverse; the NEW C6b pin `bodyHash 0 = pi[5]` holds because the forge publishes `pi[5] = -1`), the
lone C4 lookup finds its genuine chip row (head unchanged), and the (empty) memory legs balance. The
descriptor CANNOT tell the fabricated body fact from the honest one — BUT the fabricated hash is now
forced into the bound public input `pi[5]` (C6b), where the full-turn verifier binds it to the
membership leg's authenticated leaf. The in-circuit Merkle tooth is still absent; the closure is at
the composition, via the export this fix adds. -/
theorem der_accepts_fabricated_body_fact :
    Satisfied2 (fun _ => (0 : ℤ)) derivationDesc (fun _ => 0) (fun _ => (0, 0)) [] forgeTrace := by
  refine
    { rowConstraints := ?_
      rowHashes := ?_
      rowRanges := ?_
      memAddrsNodup := ?_
      memClosed := ?_
      memDisciplined := ?_
      memBalanced := ?_
      memTableFaithful := ?_
      mapTableFaithful := ?_ }
  · exact witRowConstraints (by decide)
  · intro i _; exact True.intro
  · intro i _ r hr; exact absurd hr List.not_mem_nil
  · exact List.nodup_nil
  · intro op hop; rw [forgeMemLog] at hop; exact absurd hop List.not_mem_nil
  · rw [forgeMemLog]; decide
  · rw [forgeMemLog]; decide
  · rw [forgeMemLog]; rfl
  · rw [forgeMapLog]; rfl

/-- **The honest witness and the forge publish the SAME conclusion from DIFFERENT body facts — and
now the difference SURFACES in a bound public input.** Both `witTrace` and `forgeTrace` are
`Satisfied2` with the same published conclusion (`pi[1] = 0`) — yet their active body-fact hashes
differ (`1` vs `-1`), AND after the C6b export that difference is no longer invisible: it is forced
into `pi[5]` (`witTrace.pub 5 = 1 ≠ -1 = forgeTrace.pub 5`). Before the fix the descriptor bound the
body-fact content to nothing; now it binds it to the exported `pi[5]`, the handle the full-turn
verifier ties to the membership leg. -/
theorem der_two_facts_same_conclusion :
    Satisfied2 (fun _ => (0 : ℤ)) derivationDesc (fun _ => 0) (fun _ => (0, 0)) [] witTrace
    ∧ Satisfied2 (fun _ => (0 : ℤ)) derivationDesc (fun _ => 0) (fun _ => (0, 0)) [] forgeTrace
    ∧ witTrace.pub 1 = forgeTrace.pub 1
    ∧ (envAt witTrace 0).loc (bodyHash 0) ≠ (envAt forgeTrace 0).loc (bodyHash 0)
    ∧ witTrace.pub 5 ≠ forgeTrace.pub 5 :=
  ⟨witTrace_satisfies, der_accepts_fabricated_body_fact, by decide, by decide, by decide⟩

/-! ## §2 — The NAMED body-membership carrier (the honest closure of the leg). -/

/-- The abstract committed-database membership relation: `DbMember root x` says fact-hash `x` is a
member of the database committed by Merkle root `root`. In the deployed system this is the depth-D
binary Merkle set under the Poseidon2-CR hash committed by `pi[0]`. -/
abbrev DbMembership := ℤ → ℤ → Prop

/-- **`BodyMembershipSound DbMember env`** — the body-fact analog of `ChipTableSound`: every ACTIVE
body slot's fact-hash is a genuine member of the committed root `pi[0]`. This is the carrier the
in-circuit membership tooth WOULD discharge; it is currently UNDISCHARGED (no body-membership lookup
exists in the 371-col layout), which is the P0 bug — see the file header. -/
def BodyMembershipSound (DbMember : DbMembership) (env : VmRowEnv) : Prop :=
  ∀ i, i < MAX_BODY_ATOMS → env.loc (bodyFlag i) = 1 → DbMember (env.pub 0) (env.loc (bodyHash i))

/-- **`DerivationStepAuthentic`** — the FULL genuine relation: the Rung-1 `DerivationStepValid` PLUS
the body-fact membership conjunct the descriptor omits. A row is an authentic derivation step iff its
head is the genuine hash-fact (Rung-1) AND each active body fact is a committed member (the carrier).
-/
structure DerivationStepAuthentic (hash : List ℤ → ℤ) (DbMember : DbMembership) (env : VmRowEnv)
    : Prop extends DerivationStepValid hash env where
  /-- The MISSING leg: each active body fact is authenticated against the committed root `pi[0]`.
  Its content comes WHOLLY from the `BodyMembershipSound` carrier — the descriptor contributes
  nothing to it (`der_authentic_needs_carrier`). -/
  bodyFactsMembers : ∀ i, i < MAX_BODY_ATOMS →
    env.loc (bodyFlag i) = 1 → DbMember (env.pub 0) (env.loc (bodyHash i))

/-- **`derivation_sat_imp_authentic` — the no-forgery theorem, honest about its carrier.** A
`Satisfied2` derivation trace (height ≥ 2, sound chip table) that ADDITIONALLY carries the named
`BodyMembershipSound` witnesses the FULL authentic relation on row 0. The head leg rides Rung-1
(`derivation_sat_imp_valid`); the body-membership leg rides the carrier verbatim — no crypto axiom,
the Merkle-CR carrier stays a named hypothesis exactly as `ChipTableSound` does. -/
theorem derivation_sat_imp_authentic {hash : List ℤ → ℤ} {DbMember : DbMembership}
    {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
    (hSound : ChipTableSound hash (t.tf .poseidon2))
    (hMem : BodyMembershipSound DbMember (envAt t 0))
    (hlen : 2 ≤ t.rows.length)
    (hsat : Satisfied2 hash derivationDesc minit mfin maddrs t)
    (hcanon : DerivationCanon t) :
    DerivationStepAuthentic hash DbMember (envAt t 0) :=
  { derivation_sat_imp_valid hSound hlen hsat hcanon with bodyFactsMembers := hMem }

/-! ## §2b — The C6b export: the descriptor now BINDS body atom 0's fact hash to `pi[5]`, and that
export DISCHARGES the slot-0 membership carrier from a single external fact. -/

/-- **`der_body_fact_exported` — the fix's in-circuit tooth.** Any `Satisfied2` derivation trace
(height ≥ 2) has `bodyHash 0 = pi[5]` on row 0: the new C6b pin, extracted exactly like the C6
conclusion pin (`der_pi0` on `lift_c6b`). Body atom 0's fact hash is no longer a free witness — it is
forced equal to the bound public input `pi[5]`, the handle the full-turn verifier ties to the
membership leg's authenticated leaf. -/
theorem der_body_fact_exported {hash : List ℤ → ℤ} {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat}
    {maddrs : List ℤ} {t : VmTrace}
    (hlen : 2 ≤ t.rows.length)
    (hsat : Satisfied2 hash derivationDesc minit mfin maddrs t) :
    (envAt t 0).loc (bodyHash 0) ≡ t.pub 5 [ZMOD 2013265921] :=
  der_pi0 hlen hsat (lift_c6b (by simp [c6b, pin]))

/-- **`der_carrier_slot0_discharged_by_pi` — the composition-level discharge of the P0 leg.** The
slot-0 `BodyMembershipSound` conjunct — undischarged by any in-circuit Merkle lookup — now FOLLOWS from
a single external membership fact about the exported PI: if the committed root `pi[0]` contains `pi[5]`
(exactly what the c-list membership leg proves), then it contains body atom 0's fact hash, because C6b
binds the two equal. For the deployed authorization rule `Allow(?0) :- capability(?0)` (a SINGLE body
atom, slot 0), this is the WHOLE carrier — the gap is closed at the composition by the PI export plus
the membership leg. (Multi-atom rules: the further atoms are now exported too by C6c —
`der_carrier_further_discharged` — so ALL body slots are composition-discharged.) -/
theorem der_carrier_slot0_discharged_by_pi {DbMember : DbMembership} {hash : List ℤ → ℤ}
    {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
    (hlen : 2 ≤ t.rows.length)
    (hsat : Satisfied2 hash derivationDesc minit mfin maddrs t)
    -- the deployed membership relation is Merkle set-membership over the Poseidon2 field-hash, so it
    -- respects field congruence in the leaf argument (a leaf and its residue are the SAME field cell).
    (hResp : ∀ a b : ℤ, a ≡ b [ZMOD 2013265921] → DbMember (t.pub 0) a → DbMember (t.pub 0) b)
    (hpi : DbMember (t.pub 0) (t.pub 5)) :
    DbMember ((envAt t 0).pub 0) ((envAt t 0).loc (bodyHash 0)) := by
  show DbMember (t.pub 0) ((envAt t 0).loc (bodyHash 0))
  exact hResp (t.pub 5) ((envAt t 0).loc (bodyHash 0)) (der_body_fact_exported hlen hsat).symm hpi

/-! ## §3 — The carrier is LOAD-BEARING (non-vacuous): it discriminates honest from forged. -/

/-- The honest membership predicate for these witnesses: the committed database (root `0`) contains
exactly the honest body fact `1` (and not the fabricated `-1`). A concrete instance witnessing that
the carrier is a genuine, satisfiable, DISCRIMINATING predicate. -/
def honestMember : DbMembership := fun _root x => x = 1

/-- **`honest_satisfies_membership`** — the carrier ACCEPTS the honest witness: `wa`'s active body
fact `1` is a member. So `derivation_sat_imp_authentic`'s carrier hypothesis is genuinely inhabited
by the honest trace (with the honest membership relation). -/
theorem honest_satisfies_membership :
    BodyMembershipSound honestMember (envAt witTrace 0) := by
  intro i hi
  -- only slot 0 is active on `wa` (its body-fact hash is the honest member `1`); slots 1..7 have a
  -- zeroed flag, so the flag premise is vacuously false. Each concrete slot decides.
  simp only [MAX_BODY_ATOMS] at hi
  interval_cases i <;> simp only [honestMember] <;> decide

/-- **`forge_violates_membership` — THE regression pole: the forge is REJECTED by the carrier.** The
fabricated trace does NOT satisfy `BodyMembershipSound honestMember`: its active body fact `-1` is not
a member. So the carrier is EXACTLY the tooth that separates the honest witness (accepted) from the
forge (rejected) — a non-vacuous, load-bearing hypothesis, not a laundered tautology. Since the
descriptor accepts the forge anyway (`der_accepts_fabricated_body_fact`), the descriptor ALONE cannot
supply this rejection: it needs the (undischarged) in-circuit membership tooth. -/
theorem forge_violates_membership :
    ¬ BodyMembershipSound honestMember (envAt forgeTrace 0) := by
  intro h
  have hflag : (envAt forgeTrace 0).loc (bodyFlag 0) = 1 := by
    simp [envAt, forgeTrace, waForge, bodyFlag, BODY_MEMBERSHIP_START, BODY_HASH_START]
  have hmem := h 0 (by decide) hflag
  -- `honestMember _ (-1)` unfolds to `(-1 : ℤ) = 1`, false.
  simp only [honestMember, envAt, forgeTrace, bodyHash, BODY_HASH_START] at hmem
  exact absurd hmem (by decide)

/-- **`der_authentic_needs_carrier`** — the descriptor does NOT imply the authentic relation.
`forgeTrace` is `Satisfied2` (chip-sound, height 2) yet is NOT `DerivationStepAuthentic` under the
honest membership relation — precisely because its `bodyFactsMembers` leg fails
(`forge_violates_membership`). So the `bodyFactsMembers` conjunct is contributed WHOLLY by the
carrier: the P0 hole, stated as an impossibility for the descriptor alone. -/
theorem der_authentic_needs_carrier :
    ¬ DerivationStepAuthentic (fun _ => (0 : ℤ)) honestMember (envAt forgeTrace 0) := by
  intro h
  exact forge_violates_membership h.bodyFactsMembers

/-! ## §4 — Non-vacuity of the authentic relation itself: it HOLDS on the honest witness. -/

/-- **`witTrace_authentic` — the bridge FIRES end-to-end WITH the body leg.** The honest witness,
fed the sound chip table (`witTf_chipSound`) AND the honest membership carrier
(`honest_satisfies_membership`), witnesses the FULL `DerivationStepAuthentic` on row 0 — a real
accepting trace maps to the real semantic conclusion, body-fact membership now included. So the
authentic relation is satisfiable (not a constant-false conclusion), and the whole
`derivation_sat_imp_authentic` chain is non-vacuous. -/
theorem witTrace_authentic :
    DerivationStepAuthentic (fun _ => (0 : ℤ)) honestMember (envAt witTrace 0) :=
  derivation_sat_imp_authentic witTf_chipSound honest_satisfies_membership (by decide)
    witTrace_satisfies witTrace_canon

/-! ## §5 — THE AUDIT REGRESSION: the C6c export closes the MULTI-ATOM body-fact forgery.

The audit confirmed that `bodyHash 1..7` (cols 2..8) — the FURTHER body atoms of a multi-atom rule —
were bound ONLY by C2 (nonzero-when-used), never to a committed member: C6b exported only slot 0. A
forger could therefore activate a further body slot with an arbitrary fabricated fact hash and have
the descriptor ACCEPT it. The C6c fix (`DerivationEmit.lean:c6c`) exports every further body-fact hash
as its own public input (`bodyHash i == pi[5 + i]`), so the fabricated hash is forced into a bound
handle the full-turn verifier binds to that atom's membership leaf. This section:

* proves the NEW in-circuit tooth (`der_body_facts_further_exported`): each further body hash is now
  pinned to its export;
* exhibits the REGRESSION (`der_rejects_unexported_body_fact`): a forge that activates slot 1 with a
  fabricated `bodyHash 1 = -1` but publishes a genuine member `pi[6] = 0` is now `¬ Satisfied2` — the
  slot-1 export pin bites (before the fix this exact trace was accepted);
* shows the forge is otherwise-valid (`forge_slot1_exported_satisfies`): the SAME fabricated hash stays
  accepted ONLY when the prover also publishes it at `pi[6] = -1`, exactly the C6b residual now
  extended to the further atoms (accepted-but-disclosed, so the membership leg rejects at composition);
* shows an HONEST multi-atom derivation (slots 0 AND 1 active, both facts genuine members published at
  their exports) still `Satisfied2`s (`honestBody2_satisfies`) — the pins are non-vacuous, accepting
  honest derivations while rejecting the forge. -/

/-- Membership lift for the new C6c family: each further-atom export pin is a descriptor constraint. -/
theorem lift_c6c {x} (hx : x ∈ c6c) : x ∈ derivationDesc.constraints := by
  show x ∈ derivationConstraints
  simp only [derivationConstraints, List.append_assoc, List.mem_append]; tauto

/-- **`der_body_facts_further_exported` — the fix's in-circuit tooth for the further atoms.** Any
`Satisfied2` derivation trace (height ≥ 2) has `bodyHash (j+1) = pi[6 + j]` on row 0 for every further
body slot `j+1` (slots 1..7): the new C6c pins, extracted exactly like the C6b slot-0 export. Each
further body-fact hash is no longer a free witness — it is forced equal to its bound public input, the
handle the full-turn verifier ties to that atom's membership leaf. -/
theorem der_body_facts_further_exported {hash : List ℤ → ℤ} {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat}
    {maddrs : List ℤ} {t : VmTrace}
    (hlen : 2 ≤ t.rows.length)
    (hsat : Satisfied2 hash derivationDesc minit mfin maddrs t) :
    ∀ j, j < MAX_BODY_ATOMS - 1 →
      (envAt t 0).loc (bodyHash (j + 1)) ≡ t.pub (6 + j) [ZMOD 2013265921] := by
  intro j hj
  exact der_pi0 hlen hsat (lift_c6c (List.mem_map.mpr ⟨j, List.mem_range.mpr hj, rfl⟩))

/-- **`der_carrier_further_discharged` — the further atoms' membership carrier is now dischargeable
from the exports.** For each further body slot `j+1`, a single external membership fact about its
export (`DbMember pi[0] pi[6+j]`, what that atom's c-list membership leg proves) discharges the slot's
`BodyMembershipSound` obligation, because C6c binds `bodyHash (j+1) = pi[6+j]`. Together with
`der_carrier_slot0_discharged_by_pi` (slot 0, via C6b) the WHOLE 8-slot carrier is now composition-
discharged — the audit forgery is closed for every body atom, not just slot 0. -/
theorem der_carrier_further_discharged {DbMember : DbMembership} {hash : List ℤ → ℤ}
    {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
    (hlen : 2 ≤ t.rows.length)
    (hsat : Satisfied2 hash derivationDesc minit mfin maddrs t)
    -- as in slot 0: the deployed Merkle-over-field membership respects field congruence in the leaf.
    (hResp : ∀ a b : ℤ, a ≡ b [ZMOD 2013265921] → DbMember (t.pub 0) a → DbMember (t.pub 0) b)
    (hpi : ∀ j, j < MAX_BODY_ATOMS - 1 → DbMember (t.pub 0) (t.pub (6 + j))) :
    ∀ j, j < MAX_BODY_ATOMS - 1 → DbMember (t.pub 0) ((envAt t 0).loc (bodyHash (j + 1))) := by
  intro j hj
  exact hResp (t.pub (6 + j)) ((envAt t 0).loc (bodyHash (j + 1)))
    (der_body_facts_further_exported hlen hsat j hj).symm (hpi j hj)

/-- The regression forge: a FURTHER body atom (slot 1) is activated with a FABRICATED fact hash
`bodyHash 1 = -1` (a non-member the prover does not hold), its C2 inverse `bodyInv 1 = -1` keeping the
nonzero-when-used check satisfied. Slot 0 is left inactive. Before the C6c fix, `bodyHash 1` was bound
ONLY by C2 — so this trace authenticated the fabricated further-atom fact against NOTHING. -/
def waForgeBody1 : Assignment := fun v =>
  if v = bodyFlag 1 then 1
  else if v = bodyHash 1 then (-1)
  else if v = bodyInv 1 then (-1)
  else 0

/-- The forge that tries to HIDE the fabricated further-atom fact: it carries `bodyHash 1 = -1`
internally while publishing a genuine member (`pi[6] = 0`) at the slot-1 export. Its chip table is
reused from the honest witness (`witTf`) — legitimate because the C4 fact-site tuple reads only
head/derived/lane columns, all `0` in `waForgeBody1` exactly as in `wa`. -/
def forgeUnexportedTrace : VmTrace :=
  { rows := [waForgeBody1, waForgeBody1], pub := fun _ => 0, tf := witTf }

/-- **`der_rejects_unexported_body_fact` — THE AUDIT REGRESSION.** With the C6c fix the fabricated
further-atom fact can no longer hide: the slot-1 export pin forces `bodyHash 1 = pi[6]`. This forge
carries `bodyHash 1 = -1` yet publishes the genuine member `pi[6] = 0`, so the pin is VIOLATED and the
trace is REJECTED — `¬ Satisfied2`. Before the fix this exact trace (a further body atom with an
arbitrary fabricated hash) was `Satisfied2`; the new pin is exactly the tooth that now rejects it. -/
theorem der_rejects_unexported_body_fact :
    ¬ Satisfied2 (fun _ => (0 : ℤ)) derivationDesc (fun _ => 0) (fun _ => (0, 0)) []
        forgeUnexportedTrace := by
  intro h
  have hpin := der_body_facts_further_exported (t := forgeUnexportedTrace) (by decide) h 0 (by decide)
  -- hpin : (envAt forgeUnexportedTrace 0).loc (bodyHash 1) = forgeUnexportedTrace.pub 6, i.e. -1 = 0
  exact absurd hpin (by decide)

theorem forgeUnexpMemLog : memLog derivationDesc forgeUnexportedTrace = [] := by
  simp [memLog, witMemOps]

/-- The forge that stays ACCEPTED by DISCLOSING the fabricated fact: the SAME `waForgeBody1` rows, but
`pi[6] = -1` publishes the fabricated further-atom hash at its export. -/
def forgeSlot1ExportedTrace : VmTrace :=
  { rows := [waForgeBody1, waForgeBody1], pub := fun i => if i = 6 then (-1) else 0, tf := witTf }

theorem forgeExpMemLog : memLog derivationDesc forgeSlot1ExportedTrace = [] := by
  simp [memLog, witMemOps]
theorem forgeExpMapLog : mapLog derivationDesc forgeSlot1ExportedTrace = [] := by
  simp [mapLog, witMapOps]

/-- **`forge_slot1_exported_satisfies` — the forge is OTHERWISE-VALID; only the export forces
disclosure.** The fabricated further-atom trace is `Satisfied2` when — and only when — the prover also
publishes the fabricated hash at its export (`pi[6] = -1`): every gate/pin holds, the C4 lookup finds
its (unchanged) chip row. So the slot-1 export pin is the SOLE tooth standing between the forge and
acceptance (`der_rejects_unexported_body_fact` shows it bites the moment the export disagrees). The
descriptor still lacks an in-circuit Merkle tooth; the closure is at the composition — a forger who
publishes `pi[6] = -1` must exhibit a membership proof for `-1`, which they do not hold. -/
theorem forge_slot1_exported_satisfies :
    Satisfied2 (fun _ => (0 : ℤ)) derivationDesc (fun _ => 0) (fun _ => (0, 0)) []
        forgeSlot1ExportedTrace := by
  refine
    { rowConstraints := ?_, rowHashes := ?_, rowRanges := ?_, memAddrsNodup := ?_, memClosed := ?_,
      memDisciplined := ?_, memBalanced := ?_, memTableFaithful := ?_, mapTableFaithful := ?_ }
  · exact witRowConstraints (by decide)
  · intro i _; exact True.intro
  · intro i _ r hr; exact absurd hr List.not_mem_nil
  · exact List.nodup_nil
  · intro op hop; rw [forgeExpMemLog] at hop; exact absurd hop List.not_mem_nil
  · rw [forgeExpMemLog]; decide
  · rw [forgeExpMemLog]; decide
  · rw [forgeExpMemLog]; rfl
  · rw [forgeExpMapLog]; rfl

/-- The HONEST multi-atom witness: BOTH body slots 0 and 1 active, each carrying a genuine fact hash
`1` with its inverse, published at its export (`pi[5] = pi[6] = 1`). Generalizes `wa` (slot 0 only) to
a two-atom rule. Its chip table is `witTf` (head/derived/lane columns are `0`, as in `wa`). -/
def waHonest2 : Assignment := fun v =>
  if v = bodyFlag 0 then 1 else if v = bodyHash 0 then 1 else if v = bodyInv 0 then 1
  else if v = bodyFlag 1 then 1 else if v = bodyHash 1 then 1 else if v = bodyInv 1 then 1
  else 0

def honestBody2Trace : VmTrace :=
  { rows := [waHonest2, waHonest2]
  , pub := fun i => if i = 5 then 1 else if i = 6 then 1 else 0, tf := witTf }

theorem honest2MemLog : memLog derivationDesc honestBody2Trace = [] := by
  simp [memLog, witMemOps]
theorem honest2MapLog : mapLog derivationDesc honestBody2Trace = [] := by
  simp [mapLog, witMapOps]

/-- **`honestBody2_satisfies` — an honest TWO-ATOM derivation still `Satisfied2`s (non-vacuity of the
C6c pins).** With both body slots active and each fact hash equal to its published export
(`bodyHash i = pi[5 + i] = 1`), every constraint — including the eight body-fact export pins — holds
on both rows, and the C4 lookup finds its chip row. So the C6c fix does not reject honest derivations;
the export pins accept the honest witness exactly as they reject the forge. -/
theorem honestBody2_satisfies :
    Satisfied2 (fun _ => (0 : ℤ)) derivationDesc (fun _ => 0) (fun _ => (0, 0)) []
        honestBody2Trace := by
  refine
    { rowConstraints := ?_, rowHashes := ?_, rowRanges := ?_, memAddrsNodup := ?_, memClosed := ?_,
      memDisciplined := ?_, memBalanced := ?_, memTableFaithful := ?_, mapTableFaithful := ?_ }
  · exact witRowConstraints (by decide)
  · intro i _; exact True.intro
  · intro i _ r hr; exact absurd hr List.not_mem_nil
  · exact List.nodup_nil
  · intro op hop; rw [honest2MemLog] at hop; exact absurd hop List.not_mem_nil
  · rw [honest2MemLog]; decide
  · rw [honest2MemLog]; decide
  · rw [honest2MemLog]; rfl
  · rw [honest2MapLog]; rfl

/-- **`der_regression_summary`** — the audit fix, stated as one proposition: the honest two-atom
derivation is ACCEPTED, the fabricated-and-hidden further-atom forge is REJECTED, and the fabricated
forge stays accepted ONLY once it DISCLOSES the fabricated hash at its export (where the membership leg
then rejects it). The three legs are exactly the accept/reject poles the C6c export installs. -/
theorem der_regression_summary :
    Satisfied2 (fun _ => (0 : ℤ)) derivationDesc (fun _ => 0) (fun _ => (0, 0)) [] honestBody2Trace
    ∧ ¬ Satisfied2 (fun _ => (0 : ℤ)) derivationDesc (fun _ => 0) (fun _ => (0, 0)) []
          forgeUnexportedTrace
    ∧ Satisfied2 (fun _ => (0 : ℤ)) derivationDesc (fun _ => 0) (fun _ => (0, 0)) []
          forgeSlot1ExportedTrace :=
  ⟨honestBody2_satisfies, der_rejects_unexported_body_fact, forge_slot1_exported_satisfies⟩

#assert_axioms lift_c6c
#assert_axioms der_body_facts_further_exported
#assert_axioms der_carrier_further_discharged
#assert_axioms der_rejects_unexported_body_fact
#assert_axioms forge_slot1_exported_satisfies
#assert_axioms honestBody2_satisfies
#assert_axioms der_regression_summary

#assert_axioms der_accepts_fabricated_body_fact
#assert_axioms der_two_facts_same_conclusion
#assert_axioms der_body_fact_exported
#assert_axioms der_carrier_slot0_discharged_by_pi
#assert_axioms derivation_sat_imp_authentic
#assert_axioms honest_satisfies_membership
#assert_axioms forge_violates_membership
#assert_axioms der_authentic_needs_carrier
#assert_axioms witTrace_authentic

end Dregg2.Circuit.Emit.DerivationRung2
