# Polis theorem stack

The "fair playground for superintelligences" constitution, as a kernel-clean Lean artifact:
the dregg ⋈ svenvs ⋈ Lacan synthesis made theorem-bearing against the real dregg substrate.
Verified where verified, red where red — no charisma filling the gap.

## Reproduce

```
cd metatheory
lake build Polis.Polis Polis.DreggPolis Polis.PolisNonConfusion
```

(Mathlib is cached at `~/src/mathlib4`; ~3174 jobs; exit 0.) The Polis theory is its own `lean_lib`
(`name = "Polis"`, `globs = ["Polis.+"]`) and a **CI-enforced `defaultTarget`** in `lakefile.toml`
(`defaultTargets = ["Dregg2", "Metatheory", "Polis"]`) — it builds on every `lake build`. The
qualified theorem names are unchanged from when it lived under `Metatheory.*`; only the module path
moved (`Metatheory.PolisX` → `Polis.PolisX`).

## Axiom budget

Every keystone is `#assert_axioms` / `#print axioms` within:

```
{propext, Classical.choice, Quot.sound}
```

Several depend on **no axioms at all** (`envelope_least_restrictive`,
`structural_requires_proof`, `disjoint_floors_no_polis`, `dregg_shared_floor_inhabited`).

## Proven (`Polis.Polis` · `Polis.DreggPolis` · `Polis.PolisNonConfusion`)

| Property | Theorem |
|---|---|
| **Verify the cage, not the animal** — enforcement cannot psychometrically classify the inhabitant (∀ ctrl) | `polis_safety` |
| Least-restrictive envelope — every bar load-bearing | `envelope_least_restrictive`, `override_only_unsafe`, `maxpol_envelope_safe` |
| **Structural means theorem-bearing** — no clause is `structural` without a proof | `structural_requires_proof` |
| **Legitimacy as non-regression** — self-amending, but no declared minimum may be legally weakened | `amendment_stream_nonregression`, `regressive_amendment_inert` |
| **Empty meet is schism** — the polis edge is the empty intersection of *exported* floors | `disjoint_floors_no_polis` |
| Candidate model non-vacuous (kills "beautiful but empty") | `dregg_shared_floor_inhabited` |
| Disclosure law = a real deployed theorem ("proves the same while reveals less") | `minimalBoundary_carries_real_theorem` (← `EpistemicDial.accepts_invariant_under_dial`) |
| Authority floor on the deployed l4v `Auth` enum | `dreggReal_polis_safety` |
| Authority = the real `Auth`-camera substance discipline | pins of `production_step_fpu`, `unauthorized_amplification_not_production` |
| Non-confusion family (shadow ≠ resource), deployed | pins of `transclusion_no_amplify`, `execFullForestG_no_amplify`, `noteSpendFresh_rejects_double`† |
| Foundational anti-Mythos floor (no forged history) | pin of `unfoolability_guarantee` |
| **certificate ↛ capability** (dereliction guard) | pins of `transclusion_grants_no_unheld_authority`, `transclusion_is_observed_finalized_read` |
| **observation ↛ resolution** (one resolver, many observers) | pins of `Await.{one_shot_is_static, commit_resumes_once, rollback_discards_continuation, runtime_guard_is_double_spend, four_faces_unify}` |
| executor-coupled `gateOK` authority floor | pin of `Exec.AuthModes.captp_granted_le_held` (+ camera `Fpu`) |
| real KERI human floor (cannot lose identity) | pins of `PreRotation.rotChain_pinned_by_commitments`, `ResharingChain.{reshare_forward_jump, secret_value_survives}` |
| **Politician — exit foreclosure** | `CaptureBar`, `rExitForeclosureBar`, `dreggReal_envelope_no_foreclosure` |
| **Politician — flow/policy capture** (decidable Büchi game) | `flowCaptureBar` over `≤ᶠ`, sound+complete by `FlowRefine.decideRefines_iff` (`PolisFlowRefine`) |
| **Politician — disclosure ratchet** | `DiscloseAt.{accepts_invariant_under_dial, accepts_preserved_down, leak_mono}` |
| **Politician — grade laundering** | `Finality.{no_downgrade, Tier.rank_injective, conservation_tier_independent}`, `World.world_no_downgrade` |
| **Politician — clerk monopoly** | `FullForestAuthPortal.{proof_arm_sound, custom_arm_sound, unchecked_arm_rejects}` (validity depends on the proof, not the prover) |
| **Politician — hole rent** | `ConditionalTurn.condTurn_atomic` + `Await` one-shot (`PolisPolitician`) |

† `noteSpendFresh_rejects_double` lives in the `PolisNonConfusionCircuit` sidecar (pulls the
circuit-emit tree); builds when that tree is green.

## The interleaved-multi-agent hyperproperty — FRAMEWORK BUILT (gpt5.5's design reply)

The deep object is no longer "open research" — its full construction is built, green, decidable,
`∀`-opaque, with models (`docs/POLIS-HYPERPROPERTY-FRONTIER.md` + gpt5.5's 5-file plan):

| axis | file | what's proven |
|---|---|---|
| unification (heterogeneous → one trace) | `Polis.CaptureBar.pullback`, `PolisTrace` | bars transport along public projections; `multiAgentExitFloor` / `politicianFloor` compose over subjects ∧ shapes |
| option-space (`∀`-opaque) | `PolisViability` | `viableWithinB` = B's bounded **public winning game** (∃-move/∀-response), decidable; `viabilityBar` |
| relational domination (2-safety) | `PolisSelfCompose` | `Dominated` = viable-without ∧ ¬viable-with on the counterfactual product; `dominationBar`, decidable |
| monotone composition | `PolisHyperBars` | `NoWeaken.or_mono` + `amendment_stream_nonregression_hyper` — the floor is monotone-amendable |
| graded composition (quantale) | `PolisGrade` + `PolisGradeProduct` | max-plus/tropical quantale + the product `tier×rent×burden`; `graded_amendment_nonregression` |
| shared carrier | `PolisCrossCell` | `Monitorable` + `violation_has_finite_witness`; polis-floor ∥ circuit-soundness kept **separate** |
| causal counterfactual | `PolisErase` | `eraseAgent` = the maximal A-independent subconfig (causally closed); `_subset`/`_no_A`/`_maximal` |

**The deployment wiring is now DONE** (gpt5.5's architecture call + scout `w6meqdgol` + bind-wave
`w35gr3opx`) — the framework runs on the **deployed** substrate, not toys:

| deployed binding | file | bound to |
|---|---|---|
| causal counterfactual on the blocklace | `PolisEraseBlocklace` | `eraseAuthor` on `Blocklace.{Block.creator, precedes}` (axiom-free; non-vacuity on the deployed `demoLace`) |
| recovery floor as a real bounded game | `PolisRecoveryFloor` | `recoverableNow`/`recoveryArena` on the live `PreRotation.rotateStep` (a `#guard` caught a real bug) |
| shared adversary-stream carrier | `PolisStreamCarrier` | `CoinductiveAdversary.obsStream`; `circuitSoundnessProp` ∥ `polisFloorProp` with `not_identified` **proving** they differ |

The **one** genuine frontier left: a `Monitorable` witness for the real *temporal* polis floor over the
deployed `Obs` (the safety/bounded-liveness bad-prefix predicate — connect to `FlowRefine.decideRefines`
/ the Büchi game). Per gpt5.5's headline, we claim **bounded/public/decidable** domination, never "full
unbounded politics" — *decidable gentleness is bounded gentleness*. (The executor-camera refinement of
`held ⊆ bound` is a tightening, not a hole: the shadow *is* the real `fits`, camera `Fpu` pinned.)

## The grounding insight (`~/dev/svenvs`)

svenvs resolves the protected-remainder paradox **for enforcement, not epistemology**: the
inhabitant is the `∀`-quantified term the proof never reasons about, so the shadow is
real-but-**inert** (no place in the enforcement function to put it). The same `∀`-blindness
that protects the remainder makes the politician ungovernable-by-interior → **govern
trace-shape, not motive**. `disjoint_homes_make_floor_empty` is legitimacy as a kernel fact:
the polis exists only where *exported* floors (never interiors/souls) have a non-empty meet.

> Not a proof of justice — a checked floor against forgery, psychometric enforcement,
> amendment capture, exit foreclosure, and empty-meet coercion, with the remaining political
> frontier named instead of faked.
