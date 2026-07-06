# Adversarial Meta-Review — the `governed_holds` unification

**Scope.** `metatheory/Metatheory/Adversary/{Schema,Model,Instances}.lean` @ main HEAD.
**Method.** Read the Lean *statements + proof terms* and every deployed theorem each
`holds` field delegates to; built the real tree (`lake build Metatheory.Adversary.Instances`
→ *Build completed successfully (3153 jobs)*, exit 0). Prior: **distrust** — trying to show
vacuity/laundering, not to confirm.

**Bottom line.** No instance is vacuous and no fold is laundered: every fold packages the
*exact* deployed hypotheses into `accept` and the *exact, full* deployed conclusion into
`invariant` — I checked each conclusion against the deployed theorem and found **no dropped
or weakened content**. What does not survive the distrust prior is the *rhetoric*: the
"unification" is a near-contentless shape-identity, the "one adversary" fusion is cosmetic,
the anti-vacuity apparatus witnesses the wrong direction, and the rung-5 DECO/UC instance is
rung-4 in a heavier coat. Verdicts below: mostly **GENUINE (but thin)**, with **four
OVERCLAIMED** framings, one of them sharp.

---

## A. The schema itself — `GovernedProperty` / `governed_holds`

`GovernedProperty run accept invariant := ∀ c, accept (run c) → invariant (run c)`
`governed_holds D c h := D.holds c h`   (Schema.lean:82-84)

- **Is it a real predicate?** Yes. `broken_dynamics_not_governed` (Schema.lean:222) exhibits
  a tuple `(Bool, id, True, ·=true)` for which `GovernedProperty` is **false** (`id false`
  is accepted, violates `= true`). So `GovernedDynamics.holds` is a genuine constraint — not
  every tuple lifts to an instance. The "it is not a `P → P`" claim is **earned** at the
  *type* level.

- **But `governed_holds` proves nothing.** It is definitionally the projection `D.holds`.
  All security content lives in the `holds` fields, which are *imported deployed theorems*,
  never re-proven here. This is honest (the files say "the two `holds` fields ARE the deployed
  proofs") and normal for a factoring lemma — but it means the **"unification"** is the
  observation that safety theorems share the shape `∀ c, admissible → good`. That shape is
  nearly universal (every conditional invariant fits it). Calling non-domination and
  unfoolability "the SAME theorem" (Schema.lean:37) is a **shape-identity, not a
  content-identity** — the two are discharged by completely disjoint proofs. **Verdict:
  GENUINE but near-contentless; the "one theorem" phrasing OVERCLAIMS.**

- **The negative witness is a Bool toy.** `broken_dynamics_not_governed` /
  `broken_holds_field_empty` operate on `(Bool, id, …)`, which resembles *none* of the real
  instances (attack #3). They defend only the *abstract schema*'s falsifiability; they say
  nothing about whether `circuitDynamics`, `assuranceApexDynamics`, etc. are non-vacuous.
  That work is delegated to the per-instance `*_bites` teeth + the deployed files — see §C.

---

## B. The systemic anti-vacuity gap — the teeth point the wrong way

Attack #1's real vacuity risk for `∀ c, accept c → invariant c` is **`accept`
unsatisfiable** (`∄ c. accept c` ⟹ the statement is vacuously true and the invariant is
never delivered).

Every schema-level anti-vacuity witness in these files proves the **opposite** direction:
- `*_accept_bites` proves `∃ c, ¬accept c` (accept rejects *something* — accept ≠ `True`);
- `*_invariant_bites` proves `∃ c, ¬invariant c` (invariant ≠ `True`).

Neither establishes `∃ c, accept c` (satisfiability). So the unification layer does **not**
rule out the precise vacuity attack #1 names. Where satisfiability *is* grounded, it lives in
the **deployed** files and is **not surfaced through the schema**:
- settlement: `demo_settles_when_live` / `deployedSettle_nonvacuous.1` (SettlementSoundness.lean:356,434) — a real cap **settles**. Instances.lean's `settlement_accept_bites` uses only the `.2` reject side.
- carriers: `honest_companion_fires` / `honestSat` (e.g. CustomBindingFromFold.lean:224-238) — `SatCustomFold` **is** satisfied by an honest fold. `customCarrier_bites` uses only `forged_unsat`.

For **circuit, whole-history, apex, attestation** there is *no* satisfiability witness at any
layer visible here — `accept` satisfiability rests on named realizability floors
(`WitnessDecodes`, `EngineSound`) whose achievability is a deployed-apex concern (tracked in
the circuit-soundness lane), not closed in this unification. **This is not laundering — it is
inherited from the deployed theorems — but the anti-vacuity apparatus advertises a
non-vacuity it does not actually deliver for the folded instances.** Verdict on the apparatus:
**OVERCLAIMED** (proves accept/invariant are non-`True`, gestures at "the schema BITES", but
leaves the satisfiability hole open for the hard instances).

---

## C. Per-instance verdicts (fold faithfulness verified against the deployed theorem)

| Instance | accept | invariant vs deployed conclusion | Verdict |
|---|---|---|---|
| `polisDynamics` | `True` | `∀n, safe (traj …)` = `polis_safety` concl., verbatim | **GENUINE** (accept=True trivially sat) |
| `circuitDynamics` | `verifyBatch=accept ∧ WitnessDecodes` = the two deployed hyps `hacc`,`hwitdec` | the full `∃ pre post, StateDecode ∧ kstep ∧ preBinds ∧ postBinds` = `lightclient_unfoolable` concl., verbatim (CircuitSoundness.lean:461) | **GENUINE**; sat inherited-unwitnessed |
| `settlementDynamics` | `S T log held tip ac` = deployed hyp | `LiveAtTip …` = `settlement_soundness` concl., verbatim | **GENUINE** (deployed sat witness exists) |
| `wholeHistoryDynamics` | `EngineSound ∧ verify root=true ∧ genesis=expected` = deployed hyps `es`,`hroot`,`hanchor` | `AnchoredAttests` = `light_client_verifies_anchored_history` concl., verbatim (RecursiveAggregation.lean:250) | **GENUINE** fold; sat rests on `EngineSound` floor |
| 8× `*CarrierDynamics` | `Sat*Fold` = deployed hyp `hsat` | `(∃ q verifying, piCommit=…) ∧ (VK determinacy)` = `*_binding_from_fold` concl., verbatim (CustomBindingFromFold.lean:155) | **GENUINE** (deployed both-polarity teeth: `honest_companion_fires` + `forged_unsat`) |
| `attestationDynamics` | `KD.verify=true` | `decoAuthenticated` = `AttRealizes` consequent = `deco_attestation_realizes` concl. | **GENUINE** (`attestation_invariant_bites`: invariant false at forge kernel) |
| `assuranceApexDynamics` | 7 conjuncts = the turn-specific hyps of `deployed_system_secure` (`hrun`,`hcov`,`hspend`,`es`,`hroot`,`hgen`,`hstruct`) | the full A∧B∧c1∧c2∧D∧E1∧E2 7-conjunction = `deployed_system_secure` concl., verbatim (AssuranceCase.lean:909-922) | **GENUINE** fold; **joint** accept satisfiability unwitnessed |
| `attestationUCDynamics` | `KD.verify=true` (**identical to rung-4**) | `decoAuthenticated` (**byte-identical to rung-4**) | **OVERCLAIMED** — see §D |

**On the three "folded-into-accept" seams flagged in the prompt** (circuit `WitnessDecodes`,
whole-history `EngineSound`, apex `hcov`/`EngineSound`/`KernelGenesisPin`/`SeamStruct`): each
folded predicate is an **explicit hypothesis of the deployed theorem** (verified by reading
`lightclient_unfoolable`, `light_client_verifies_anchored_history`, `deployed_system_secure`
signatures) — **not invented to make the fit work**. The fold cannot gut the invariant,
because the `holds` field is typed to produce the *full* deployed conclusion and won't
elaborate otherwise (the build confirms it does). So the fold is **faithful**: content moved
into `accept` is exactly the deployed precondition; the invariant retains the entire deployed
payload. **No laundering found in the folds.**

---

## D. The sharp find — rung-5 DECO/UC is rung-4 in a coat

`attestationUCDynamics` (Instances.lean:594) is billed as "the rung-5 STRENGTHENING… the
summit ABOVE rung-4 unforgeability." At the schema level it is **not** a strengthening:

1. Its `accept` and `invariant` are **byte-identical** to `attestationDynamics` (both
   `KD.verify=true` → `decoAuthenticated`).
2. Its `holds` routes through `(decoUC_realization_of_discharge …).soundness`, and
   `DecoUCRealization.soundness := deco_attestation_realizes …` (DecoUC.lean:208) — the
   **same proof term** as rung-4. So `deco_attestation_uc_via_schema` and
   `deco_attestation_via_schema` prove the *identical* proposition by the *identical*
   underlying lemma.
3. The extra UC apparatus is discharged trivially in the shipped companion
   `deco_attestation_uc_realizes` (Instances.lean:624): the five computational carriers
   (`stark_zk`, `handshake_sim`, `simulator_ppt`, `negligible_advantage`, `composes`) are
   instantiated with **`True … trivial`**.
4. `UCRealizesFAtt = AttRealizes ∧ (∀ stmt w₁ w₂, decoDisclosedView stmt w₁ = decoDisclosedView
   stmt w₂)`. But `decoDisclosedView stmt _w := stmt` (DecoUC.lean:116), so the "perfect-ZK
   simulator fragment" conjunct is literally **`stmt = stmt`**, proved `rfl`. It carries **no
   zero-knowledge content** — the disclosed view is witness-free by *definition*, not by any
   simulator argument.

So the Lean-provable core of the "UC realization summit" reduces to **rung-4 soundness ∧ a
`stmt = stmt` tautology**, with the genuinely-computational UC content filled by `True`. This
is exactly the shape ember suspected: *looks stronger than it is.* Not vacuous (soundness is
real and load-bearing), but the **rung-5 elevation is cosmetic at the level of provable
content** and the ZK conjunct is definitionally trivial. **Verdict: OVERCLAIMED.** (Root cause
is in the deployed `DecoUC.lean` framing; the schema instance faithfully packages it and
inherits the overclaim.)

---

## E. The payoff theorems

- `unfoolability_via_schema`, `settlement_soundness_via_schema`, `whole_history_via_schema`,
  the 8 `*_backing_via_schema`, `deployed_system_secure_via_schema`: each conclusion is the
  **actual deployed guarantee, verbatim** (checked term-by-term). Attack #4 (weakened
  restatement) **does not land** — nothing is dropped. **GENUINE.**

- `adversary_governed_uniformly`, `non_domination_and_unfoolability`, `assurance_case_governed`:
  faithful **conjunctions** of the deployed guarantees, each conjunct discharged by its real
  proof. But the celebrated "one adversary `A`, same `∀ A`" is **cosmetic**: `A`'s fields
  (`opCtrl`, `forgedPI`, `forgedProof`) are mutually independent, so
  `∀ A, P(A.opCtrl) ∧ Q(A.forgedPI, A.forgedProof)` is **logically equivalent** to
  `(∀ ctrl, P ctrl) ∧ (∀ pi π, Q pi π)`. Bundling two independent universals into one
  universal-over-a-product adds **no logical strength**. Moreover `assurance_case_governed`
  never consumes `A.netCtrl`, `A.committee`, `A.corrupt`, `A.byzBound` (the Byzantine leg is a
  *separate* theorem `byzantine_leg_cannot_uphold_false`) — the "one object" is a bag the
  marquee projects a few fields from. **Content GENUINE; the "profound fusion / same ∀
  adversary" framing (Model.lean:38) is OVERCLAIMED.**

---

## F. Summary of findings (distrust prior, honestly reported)

**No vacuous instance. No laundered fold.** Folds faithfully package deployed hypotheses into
`accept` and the *complete* deployed conclusion into `invariant`; the tree builds green; every
`via_schema` conclusion equals its deployed guarantee verbatim. The unification *does* what it
literally says.

**Four overclaims** (framing, not soundness):
1. **`governed_holds` is a trivial projection** and the "unification" is a near-universal
   shape-identity — "non-domination ≡ unfoolability, ONE theorem" oversells a common shape,
   not shared content. (§A)
2. **The anti-vacuity apparatus witnesses the wrong direction** — `accept ≠ True` and
   `invariant ≠ True`, never `accept` **satisfiable**; for circuit/whole-history/apex/
   attestation the satisfiability hole attack #1 names is left open (inherited from the
   deployed realizability floors). (§B)
3. **Rung-5 DECO/UC = rung-4 in a coat** — identical invariant, same underlying proof,
   `True`-filled computational carriers, and a definitionally-trivial (`stmt = stmt`) ZK
   conjunct. The sharpest "looks stronger than it is." (§D)
4. **The "one adversary" fusion is cosmetic** — a Cartesian bundling of independent
   universals with no added strength; several bundled fields go unused by the marquee. (§E)

**What would raise each to fully-earned "genuine":** (2) add `∃ c, accept c` satisfiability
witnesses at the schema level for the folded instances (or cite the deployed completeness
lemmas through the instances, as settlement/carriers already can); (3) either give the rung-5
instance an invariant that *actually* carries the UC/ZK content beyond soundness, or stop
calling it a summit above rung-4; (4) drop the "profound same-∀" rhetoric or give the
adversary fields a genuine cross-constraint that a product-of-quantifiers could not express.
