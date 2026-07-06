# Adversarial meta-review — the marquee theorem STATEMENTS (not the names, not the reports)

**Prior: DISTRUST.** ember's suspicion (correct and load-bearing): it is *suspicious* that the proof
attempts keep finding no flaws — clean green can hide a hollow rung. This lane read each marquee
theorem's ACTUAL Lean statement + proof term, exhibited vacuity where it exists, compared the code to
the agent reports, ran the WHOLE tree (`lake build Dregg2` + the relevant `cargo`), and independently
`#print axioms`-checked the cleanliness claim rather than trusting `#assert_axioms`.

Repo `/Users/ember/dev/breadstuffs` @ `main` HEAD `b201f7d76`. Read-only on the reviewed code.

## What ground truth actually says (ran, not self-reported)

- **`lake build Dregg2` → `Build completed successfully (4265 jobs)`**, exit 0, zero `error:`/`sorry`
  in the log. The full umbrella is green — no per-file-green-hides-red-downstream trap here.
- **Independent `#print axioms`** on five marquees (not via `#assert_axioms`):
  - `governed_holds` — *does not depend on any axioms* (it is a pure structure projection).
  - `assurance_case_governed`, `deco_attestation_uc_realizes`, `sealedescrow_no_theft` — `[propext,
    Classical.choice, Quot.sound]` only.
  - `DecoUC.decoUC_realizes` — *does not depend on any axioms*.
  So the axiom-cleanliness claim is REAL: no `sorryAx` sneaks in, no stray axiom the assert misses.
  The `#assert_axioms` machinery (`Dregg2/Tactics.lean:39`) genuinely calls `Lean.collectAxioms` and
  rejects anything outside the 3-name allow-list — `sorryAx` would fail the build. **Important, and
  honestly documented (`Tactics.lean:147`): the discipline only sees `axiom`-keyword decls. Carriers
  that enter as HYPOTHESES or `Prop`-typeclass fields (`StarkSound`, `DeployedRefines`, the DECO §8
  crypto floors, the DecoUC computational carriers) are NOT axioms and NOT flagged.** "Axiom-clean"
  means "no `sorry`, no extra axioms" — it does NOT mean "no assumptions." That is the correct reading
  and the files are uniform about it.
- **`cargo test -p dregg-circuit deployed_cohort_bytes_carry_the_refuse` → 1 passed.** The gentian Rust
  weld genuinely lands the refuse gates into the committed registry bytes (all 36 cohort rows).

## The table

| theorem | statement matches name? | non-vacuous? | report over-claimed? | whole-tree build clean? |
|---|---|---|---|---|
| `governed_holds` (Adversary/Schema:82) | **Schema, not a security thm** — it is `D.holds c h`, a struct projection; *no axioms*. Honestly labeled as "the unified consumer." | Trivial itself; content lives in the instances. Anti-vacuity present: `broken_dynamics_not_governed` shows `GovernedProperty` is a real (falsifiable) predicate. | No — file states outright the `holds` fields ARE the deployed proofs. | ✅ |
| `assurance_case_governed` (Adversary/Instances:755) | **A unification, not new security** — conjunction of 4 pre-existing theorems each re-expressed as `governed_holds Dᵢ`. Matches the "one lemma, N instances" claim. | Non-vacuous *iff* the 4 underlying theorems are; `settlement_accept_bites`/`wholeHistory_invariant_bites` witness two of them bite. Adds no new security content. | No (as unification). Would be over-claim only if read as *independent* security. | ✅ |
| `deco_attestation_unforgeable` (Crypto/DecoUnforgeable:219) | **YES.** Genuine game+reduction: a forged attestation ⟹ concrete ed25519 `SigForgery` ∨ HMAC `MacForgery`, under standard floors. | **YES, both poles.** `attestation_fires` (real attestation verifies) + `Forge.attestation_bites_is_sig_forgery` (concrete forgery extracted when carrier stripped). | No. | ✅ |
| `deco_attestation_uc_realizes` (Crypto/Instances:624) + `DecoUC.decoUC_realizes` | **OVERCLAIMED.** "rung-5 UC-realization summit above rung-4" — but the shipped Lean delta over rung-4 is a *tautological* conjunct. See §1. | **The distinctive (ZK/UC) content is VACUOUS.** `UCRealizesFAtt`'s 2nd conjunct is `stmt = stmt` (def-constant view); computational carriers passed `True`/`trivial`. Only the *soundness* conjunct (inherited rung-4) is non-vacuous. | **YES — a real overclaim.** The docstrings sell the perfect-ZK fragment as "a real constraint, not a vacuous rfl" with `decoLeaky_no_simulator` teeth — but those teeth target `decoLeakyView`, a function *never wired into* `UCRealizesFAtt`; the conjunct actually shipped IS the vacuous rfl. | ✅ |
| `sealedescrow_no_theft` (Deos/SealedEscrow:753) | **YES** at the model level — per-leg conservation ∧ no-free-lunch over the reachable `Ledger`/`Op` system. | **YES, both poles.** `honest_swap_reachable`/`honest_reclaim_reachable` FIRE; `halfopen_theft_unreachable`/`phantom_extraction_unreachable` BITE. | No — but note it is a **model-level** economic invariant; this file does not prove the deployed escrow executor *refines* this `Op` model. | ✅ |
| `declared_{escrow,discharge,vault}_unsat_deployed` (Deos/BareCohortFloorRefuseDeployed) | **YES** for the welded descriptor — a satisfying witness of `gentianDeployedBareRefuse d` on a cell whose *committed* manifest declares the tag ⟹ `False` (decode forces `fc=1`, refuse gate forces `fc=0`), under `Poseidon2SpongeCR`. | **YES.** Both decode poles bite (`#guard tagBitZ declared==1 / absent==0`); the refuse is inert for non-declaring cells, so the descriptor is not universally-unsat. | No — "deployed" rests on the Rust weld; `deployed_cohort_bytes_carry_the_refuse` (cargo, PASS) shows the committed bytes carry it. **Note the `V3_STAGED_REGISTRY` naming (§2).** | ✅ (+ cargo PASS) |
| `anchored_attests_rejects_fabricated_genesis` (Circuit/RecursiveAggregation:270) | **Near-tautological projection** — `hne anch.genesis_anchored` : `(a≠b)→(a=b)→False`. The real anti-ghost content is `AggregateAttests.genesis_pinned` (ties public `genesisRoot` to the first step's `oldRoot`) + the client-side `genesis_anchored` check. | Non-vacuous via the pin; the headline theorem itself is definitional. `AnchoredAttests` IS constructible honestly (`light_client_verifies_anchored_history`). | Mild — the "GENESIS ANTI-GHOST TOOTH" framing overstates a field-projection; the substance is one layer down (`genesis_pinned`). | ✅ |
| `deployed_rejects_tampered_quotient` / `DeployedRefines` (Circuit/FriVerifierBridge) | **YES.** Genuine contrapositive tooth: deployed-verifier-refines-algo (`DeployedRefines`) + the proven `verifyAlgo_full_rejects_tampered_quotient` ⟹ a tampered-quotient batch cannot be accepted, *with no appeal to the crypto floor*. | **YES** — the tamper hypothesis `constraintEval ≠ vanishing·quotient` is a real condition; the tooth bites the deployed verdict. | No. `DeployedRefines` (Rust==spec) is a plainly-labeled carried residual — "the SOLE remaining code-trust." Honest. | ✅ |
| `zkOracle_sound` (Crypto/ZkOracle:77) | **YES** as a *composition* — authentic (`decoAuthenticated` via `deco_attestation_realizes`) ∧ well-formed (`cfg_verify_sound`) ∧ injection-free. | Legs 1–2 non-vacuous (real reductions + `Demo`/`Json` witnesses). **Leg 3 caveat:** `InjectionFree field` is a *decidable side-condition passed as hypothesis and restated verbatim in the conclusion* — not derived from a proof object (teeth: `malicious_not_injection_free`). | No, but note leg 3 is assumed-and-restated. | ✅ |

## §1 — THE HOLLOW RUNG: `deco_attestation_uc_realizes` (the one ember suspected exists)

This is the marquee whose green is genuinely misleading. Reading the actual definitions:

```lean
-- DecoUC.lean:116
def decoDisclosedView {Dg} (stmt : Statement Dg) (_w : CircuitIR Dg) : Statement Dg := stmt  -- IGNORES w
-- DecoUC.lean:159
def UCRealizesFAtt verify Auth : Prop :=
  AttRealizes verify Auth
  ∧ (∀ stmt w₁ w₂, decoDisclosedView stmt w₁ = decoDisclosedView stmt w₂)
```

Because `decoDisclosedView` is *defined* to discard the witness, the second conjunct unfolds to
`∀ stmt w₁ w₂, stmt = stmt` — provable by `rfl` for **any** `verify`/`Auth`, including a forgeable
oracle. Hence `UCRealizesFAtt verify Auth` is logically **equal to** `AttRealizes verify Auth` (the
rung-4 soundness). The proof term confirms it: `decoUC_realizes := fun r => ⟨r.soundness, r.zk_disclosed⟩`
with `zk_disclosed := fun _ _ _ => rfl`.

The genuinely-computational UC pieces (`stark_zk`, `handshake_sim`, `simulator_ppt`,
`negligible_advantage`, `composes`) exist only as `Prop` *fields* of the `DecoUCRealization` structure,
and the marquee `deco_attestation_uc_realizes` (Instances.lean:629) fills every one with `True` /
`trivial`:

```lean
decoUC_realization SK MK … True True True True True trivial trivial trivial trivial trivial
```

So the `≈_c` core has **no Lean content** in the headline. The falsification lemma proves the point
against itself: `forge_not_ucRealizes` is `rintro ⟨hsound, _⟩; exact Forge.forge_not_realizes hsound` —
it **discards** the ZK conjunct and derives the contradiction from soundness alone. The ZK conjunct
carries zero falsifiable content.

**The precise overclaim:** the DecoUC module header (§2) and the `UCRealizesFAtt` docstring present the
perfect-ZK fragment as non-vacuous — "`decoLeaky_no_simulator` is the TEETH … the perfect-ZK fragment
is a real constraint, not a vacuous `rfl`." But `decoLeaky_no_simulator` is a statement about
`decoLeakyView (:= w.sessionKey)` — a DIFFERENT function that is **never wired into** `UCRealizesFAtt`.
The conjunct actually shipped in the load-bearing proposition IS the vacuous `rfl`. Rung 5 is, in Lean,
rung-4 soundness ∧ a tautology, dressed as "the summit above rung-4."

**This corroborates a prior independent lane** (`docs/audit/META-REVIEW-GATE-AND-DECOUC.md` §2.2), which
found the same `rfl`-vacuous conjunct. Two adversarial reads reaching this independently is the strongest
signal in this review that the finding is real, not a misreading. The module's *long-form prose* is
otherwise honest that the computational layer is CARRIED (never faked as an `axiom`); the defect is
localized to (a) the ZK conjunct's vacuity and (b) the "non-vacuous perfect-ZK teeth" claim pointing at
an unused function. **Fix owed:** either wire a load-bearing view function into `UCRealizesFAtt` (one that
`decoLeaky_no_simulator` actually refutes), or downgrade the docstrings/manifest so rung 5 is counted as
"soundness restated + computational core CARRIED," not a distinct proven summit.

## §2 — The "STAGED" registry: verify the flip is live, not shelved

The gentian anti-launder is sound at the Lean level and the Rust `deployed_cohort_bytes_carry_the_refuse`
test PASSES against the committed `V3_STAGED_REGISTRY_TSV`. The residual question is naming: the registry
is `…_STAGED_…`, and the project's own record flags a *deliberately-gated VK epoch* (commit the welded VK,
then flip the deployed default). The Lean theorems are about `gentianDeployedBareRefuse d` and the Rust
test asserts the *staged* TSV bytes carry the refuse. Whether "staged" == "the live-keyed default the
apex `Rfix` and the shipped light client actually verify against" is a deployment-plumbing fact this lane
did not fully trace end-to-end. It is NOT a Lean vacuity — it is a *staged-vs-live-default* calibration to
confirm before the "deployed" adjective is unconditional. (The file header claims `Rfix` re-keys over the
same `v3RegistryCapOpenDep`; that identity is the thing to spot-check on the live VK path.) A minor
consistency nit: the Rust module header cites caveat cols `291/298/305/312` while the deployed v13 geometry
uses `643/650/657/664` (`caveat_tag_col` under `GRAD_ROT_WIDTH`) — the two are different geometries; the
`#guard ebDep 0 == 643` pins the deployed one, so this is a stale comment, not a live mismatch.

## The honest meta-verdict — how trustworthy is the session's green?

**Largely trustworthy, with ONE genuinely hollow marquee and a cluster of honestly-labeled trivialities
whose NAMES out-run their content.** Concretely:

- The **axiom hygiene is real** (independently reconfirmed: no `sorryAx`, no stray axioms), the **whole
  tree builds green** (4265 jobs, not per-file), and the **Rust weld genuinely hits committed bytes**.
  Ground-truth green is not faked.
- The **crypto/economic reductions that DO the work are solid**: `deco_attestation_unforgeable` (real
  reduction, real forgery teeth), `sealedescrow_no_theft` (real reachability invariant, both-pole teeth),
  `declared_*_unsat_deployed` (real unsat + both decode poles), `deployed_rejects_tampered_quotient`
  (real algorithm tooth out of the TCB), `zkOracle_sound` (honest 3-leg composition).
- ember's suspicion is **VINDICATED at `deco_attestation_uc_realizes`**: its distinctive rung-5 content is
  a definitional tautology plus `True`/`trivial`-discharged carriers, and its advertised non-vacuity teeth
  point at a function not used by the shipped proposition. This is the real overclaim.
- A **second, softer pattern** worth naming so it does not compound: several marquees are
  *projections/unifications honestly labeled as such* — `governed_holds` (a field projection, *no
  axioms*), `assurance_case_governed` (a re-expression of 4 prior theorems), and
  `anchored_attests_rejects_fabricated_genesis` (a field-equation contradiction). None is *false* or
  *vacuous*, but each carries a security-sounding NAME while its content is definitional; the substance
  lives one layer down (the instances' `holds`, `AggregateAttests.genesis_pinned`). Read as unifications
  they are fine; cited as standalone security guarantees they would mislead.

### Ranking

- **TRUSTWORTHY** (statement matches name, both-pole non-vacuous, no overclaim):
  `deco_attestation_unforgeable`, `sealedescrow_no_theft`, `declared_{escrow,discharge,vault}_unsat_deployed`,
  `deployed_rejects_tampered_quotient` / `DeployedRefines`, `zkOracle_sound` (with the leg-3 side-condition note).
- **TRUSTWORTHY-BUT-TRIVIAL** (sound + honestly labeled, but the NAME over-suggests independent security;
  content is definitional/inherited): `governed_holds`, `assurance_case_governed`,
  `anchored_attests_rejects_fabricated_genesis`.
- **OVERCLAIMED**: `deco_attestation_uc_realizes` — rung-5 "UC-realization summit" is, in Lean, rung-4
  soundness ∧ a `rfl`-vacuous conjunct, with the computational UC carriers `True`/`trivial`; the perfect-ZK
  "teeth" refute an unused function. (Not *false* and not *sorry*-tainted — the soundness leg is real —
  but the delta it advertises over rung 4 is not there.)
- **VACUOUS / NEEDS-REWORK**: none is fully vacuous; the ONE vacuous *sub-claim* is the ZK conjunct of
  `UCRealizesFAtt` (§1), which needs a load-bearing view function or a docstring/manifest downgrade.

**Bottom line:** the session's green holds where it matters (the reductions, the invariants, the deployed
bytes, the axiom floor), and the review earned that by reading statements + building the whole tree rather
than trusting reports. The one place the green is hollow is exactly the newest, grandest-named rung
(DECO-UC rung 5) — which is where a distrustful prior should have looked first, and where a prior lane and
this one independently agree.
