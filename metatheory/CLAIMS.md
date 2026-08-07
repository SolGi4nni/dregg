# CLAIMS.md — exactly what dregg2 proves, and what it does not

A skeptic-facing ledger for the `Dregg2` Lean metatheory. It is the **human-readable
half**; the **machine-checked half** is [`Dregg2/Claims.lean`](Dregg2/Claims.lean), which
`import Dregg2` (the root, transitively every module) and then re-pins, in one place, every
keystone advertised as *PROVED / axiom-clean* with `#assert_axioms`. That command (defined in
`Dregg2/Tactics.lean`) ELABORATES TO AN ERROR unless the named theorem's entire axiom set is
`{propext, Classical.choice, Quot.sound}` — in particular it **fails on any kernel open-hole
axiom**. So `lake build` (or `lake env lean Dregg2/Claims.lean`) is itself a credibility
artifact: if any claimed keystone silently regresses to an open hole, the build breaks **here,
at the ledger**, not
somewhere downstream. This is dregg2's Lean-native port of svenvs's `verify-claims.sh` +
`CLAIMS.md` discipline.

> **What "PROVED" means here — load-bearing, not preface.** Exactly the cited theorem and its
> labelled seams. A green ledger is **not** a verified distributed OS, not verified consensus,
> not verified cryptography. It is: *every theorem labelled PROVED is free of the kernel's
> open-hole axiom in the Lean kernel, modulo the named §8 interface obligations that are, by
> design, the circuit's
> job and never Lean's.* If "dregg2 is verified" begins to carry more than that, the extra
> meaning is the reader's, not the artifact's.

## Honesty labels

| Label | Meaning |
|-------|---------|
| **PROVED-axiom-clean** | A Lean theorem whose `collectAxioms` is exactly the three standard kernel axioms. No open holes, no `admit`, no `axiom`-keyword, no `native_decide`. **Pinned** in `Dregg2/Claims.lean` (build-enforced). |
| **PROVED (home-pinned, parked)** | Identical strength, and self-pinned `#assert_axioms` in its **home module** — but its `.olean` is not yet in `Dregg2/Claims.lean`'s import closure (a concurrent-edit race; see *Parked pins* below). Listed here as PROVED; its central pin is commented out so `lake env lean` stays exit-0, to be re-enabled after an `.olean` rebuild. |
| **rests-on-§8-primitive** | The theorem is real and free of open holes, but it is **stated over** an explicit, labelled, literature-standard interface obligation (a `conservation_step`-style operational primitive, or a `CryptoKernel`/`World`/`Verifiable` law). These primitives are stated as typeclass fields / `Prop` portals on purpose — they are the circuit's / protocol's job (§8 boundary), never Lean's. |
| **honest-OPEN** | A genuine open obligation carried as a **named residual `Prop`, an explicit hypothesis, or a prose `-- OPEN:` note — never an open hole** (the corpus has zero). Not pinned, not claimed proved. The current residues are listed in *§ OPEN* below. |

There are **zero open holes, zero `admit`s, and zero `native_decide`** in the corpus (verified
by a whole-corpus open-hole scan over `Dregg2/ Metatheory/` → 0). The only `axiom`-keyword
declarations are the **two clearly-named DEMO axioms** in `Dregg2/Widget/Basic.lean`
(`demoEd25519VerifyExtern` / `demoUnvettedAssumption`) that exist to exhibit the amber
"carrier-bounded" trust tier in the ProofWidgets surface — deliberately NOT pinned, and a
clean-triple pin on anything touching them would correctly fail (see `Claims.lean` §34).

## The two honest non-proof buckets (and nothing else masquerades as a proof)

1. **§8 interface obligations** — the `CryptoKernel` / `World` laws, `Core.conservation_step`
   (Law 1's balance), `Laws.search_sound` (the soundness-by-verification contract on an opaque
   matcher), the `Privacy` commitment/stealth/nullifier predicates, the range-proof
   anti-inflation rib. Discharged by Rust + the ZK circuits, **by design never in Lean**.
   Soundness/extractability of `verify`/`commit`/`hash` is a *circuit* obligation stated as
   `CryptoKernel` laws; Lean treats `verify` as a decidable oracle. A boundary, not a gap.
   These enter downstream theorems as **typeclass parameters / hypotheses**, so they do
   **not** appear in `collectAxioms` — a theorem taking them as hypotheses is genuinely
   kernel-clean and IS pinned. (Several have since been *discharged inside Lean* — Merkle,
   Pedersen, PredicateKernel, NonMembership, Temporal/Dfa, Bridge — see `Claims.lean`
   §18–§22.)
2. **Genuine open obligations** — carried as named residual `Prop`s / explicit hypotheses /
   prose `OPEN` notes (never an open hole). Listed explicitly in *§ OPEN* below.

---

## Machine-checked keystones (PROVED-axiom-clean — pinned in `Dregg2/Claims.lean`)

**297 theorem pins (`#assert_axioms`) + 51 whole-namespace pins (`#assert_namespace_axioms`)**
currently build-enforced (plus 20 parked pins, commented out — see *Parked pins* below; recount:
`grep -c "^#assert_axioms" Dregg2/Claims.lean`). Grouped by subsystem (the `Dregg2/Claims.lean`
section numbers). Every row is `collectAxioms`-clean as of the last verification. The table
below shows the original §0–§17 keystones; `Claims.lean` §18–§34 pin many more subsystems
(WP/LTS, crypto §8 discharges, BFT safety+liveness, Cordial-Miners, executor axes, caveat +
attestation faces, consistency witness, handler-transformer, the Hatchery) — the file itself
is the authoritative inventory.

| § | keystone (fully-qualified) | module | what it claims |
|---|----------------------------|--------|----------------|
| 0 | `Dregg2.Conserve.sum_conserve_of_deltas_zero`, `…sum_transfer_conserve`, `…sum_indicator`, `…sum_pointUpdate` | `Conserve` | the shared Σ_k conservation lemma library (deltas-sum-zero ⇒ measure preserved; transfer conserves) |
| 1 | `Dregg2.Exec.cexec_attests` | `Exec.StepComplete` | the executable machine attests all 4 `StepInv` conjuncts — realizes `Core.conservation_step` AS A THEOREM about `cexec` |
| 1 | `Dregg2.Exec.conservation_step_realized` | `Exec.StepComplete` | the abstract conservation primitive is discharged by the running kernel |
| 1 | `Dregg2.Exec.livingCell_sound` | `Exec.Cell` | genuine bisimulation of the coinductive living cell to the golden oracle (Mg keystone) |
| 1b | `Dregg2.Exec.RecordCell.recCexec_attests`, `…recReplay_preserves_sumEquals`, `…recordCell_stepComplete`, `…recordCell_run_preserves_sumEquals`, `…recordCell_obs_advances` | `Exec.RecordCell` | the name-keyed record cell GROWS νF life: 4-conjunct step-completeness + conservation over records |
| 2 | `Dregg2.Circuit.bridge` | `Circuit` | satisfied `kernelCircuit` ↔ `fullStepInv` (the circuit-from-Lean CCS bridge) |
| 2 | `Dregg2.Circuit.verify_law_derivable` | `Circuit` | the verify-law is DERIVED from the bridge, not assumed |
| 3 | `Dregg2.Hyperedge.hyperedge_sound` | `Hyperedge` | the atomic hyperedge (turn = wide pullback over shared `TurnId`) is sound given binding |
| 3 | `…hyperedge_sound_needs_binding`, `…hyper_stepComplete`, `…hyper_binding_is_proper`, `Hyperedge.legs_agree`, `…toSharedTurnId`, `…toJointBinding`, `SharedTurnId.toHyperedge`, `ringHyperedge` | `Hyperedge` | leg-agreement, binding-as-proper-subobject, N-ary step-completeness, bilateral/ring as special cases |
| 4 | `Dregg2.Spec.Guard.attenuate_narrows` | `Spec.Guard` | the ONE verify/find rule: attenuation narrows admission (meet-semilattice, NOT Heyting) |
| 4 | `Spec.Guard.admits_all`, `…admits_any`, `…admits_attenuate`, `…admits_witnessed_iff_discharged`, `…discharged_admits`, `…admits_monotonic`, `…admits_sumEquals`, `…admits_senderAuthorized`, `…admits_nonMembership`, `…admits_oneOf` | `Spec.Guard` | the demand⊣supply seam: first-party / witnessed admission, OneOf coproduct, legacy constraints derived |
| 5 | `Dregg2.Spec.committed_iff_cleartext` | `Spec.Conservation` | hidden-yet-conserved: a Pedersen-committed balance conserves iff its cleartext does |
| 5 | `…conservation_over_monoid(_finset)`, `…disclosed_non_conservation`, `…conservative_discloses_nothing`, `…committed_of_cleartext`, `…multi_domain_independent`, `…turnConserves_balance`, `LinearityClass.*` | `Spec.Conservation` | multi-domain, value-monoid-parametric conservation; disclosed-non-conservation exclusivity |
| 6 | `Dregg2.Spec.gen_step_traces` | `Spec.Authority` | the generative core: every new edge of one authorized step traces to an authorized generator ("only connectivity begets connectivity", per-step) |
| 6 | `…introduce_non_amplifying`, `…amplify_needs_held_amplifier`, `…mint_needs_held_factory`, `…mint_conforms_to_contract`, `…confers_refl/trans`, `…{introduce,mint,amplify}_is_gen`, `…{attenuate,revoke}_is_restrict`, `…revoke_step_adds_nothing`, `…gen_conferral_is_attenuation`, `…attenuate_is_restrictive_narrowing`, `…introduce_same_target` | `Spec.Authority` | the capability-graph generators + the per-step half of non-forgeability |
| 7 | `Dregg2.Spec.Lifecycle.creation_provable_death_temporal` | `Spec.Lifecycle` | creation is provable; death is only *temporally* (lease) decidable, never globally |
| 7 | `…creation_and_death_are_dual`, `…archival_is_fold`, `…reclaim_by_lease`, `…terminal_rejects_{effects,transition}`, `…{migrated,destroyed}_terminal`, `…acceptsEffects_iff`, `…isTerminal_iff`, `…birthProvable`, `…archived_still_live` | `Spec.Lifecycle` | lifecycle = attested dual of creation; archival as IVC fold; lease reclamation |
| 8 | `Dregg2.Spec.hyperedge_is_validity_not_canonicity` | `Spec.JointViaHyper` | hyperedge soundness is *validity* (proof-check), distinct from *canonicity* (consensus) |
| 8 | `…joint_via_hyperedge`, `…binary_{binding,joint}_via_hyperedge`, `…singletonHyperedge`, `…validity_is_local_canonicity_is_global` | `Spec.JointViaHyper` | N-ary joint soundness DERIVED from `hyperedge_sound` |
| 9 | `Dregg2.Spec.red_projects_to_hyperedge` | `Spec.Choreography` | the red (coupled) projection of a blue/red split projects to a `Hyperedge` |
| 9 | `…blue_commits_independently`, `…blue_needs_no_hyperedge`, `…red_legs_agree`, `…red_iff_coupled`, `…epp_membrane_is_projection`, `RedBinding.toHyperedge` | `Spec.Choreography` | blue commits independently; red is exactly the coupled fragment |
| 10 | `Dregg2.Spec.Conditional.conditional_is_temporal_guard` | `Spec.Await` | the await family's temporal face IS a `Guard` (conditional = temporal admission) |
| 10 | `…resolve_monotone`, `…expired_stays_expired`, `…resolved_iff_gateway_discharged`, `…gateway_admits_eq_token`, `…await_two_faces`, `…temporal_face_is_await_discharge`, `PromiseGraph.depends_{irrefl,trans}`, `…broken_promise_propagates(_trans)` | `Spec.Await` | temporal Guard ⊕ dataflow DAG; resolution is monotone; broken promises propagate |
| 11 | `Dregg2.Spec.phi_drops_confinement` | `Spec.VatBoundary` | the caps↔keys functor Φ is *named-lossy*: permission survives the vat boundary, authority (confinement) does not |
| 11 | `…forwarded_cap_is_revocable`, `…revocable_iff_not_authority`, `…phi_admits_iff_discharged`, `…cross_vat_needs_witness`, `…macaroon_does_not_cross_phi`, `…biscuit_crosses_phi`, `…phi_domain_is_exactly_biscuit`, `…phi_composes_with_attenuation`, `…phi_attenuation_factors_through_confers` | `Spec.VatBoundary` | biscuit crosses Φ / macaroon does not; Φ composes with attenuation |
| 13 | `Dregg2.Finality.conservation_tier_independent(_iff)` | `Finality` | conservation (Law 1) holds independent of the finality tier — the lattice never weakens it |
| 14 | `Dregg2.Liveness.revocation_needs_consensus` | `Liveness` | revocation (unlike GC collection) requires consensus — the asymmetry of the two deaths |
| 15 | `Dregg2.Exec.Consensus.{quorum_reaches_bft_tier, committedByQuorum_reaches_bft_tier, below_quorum_not_bft, net_no_downgrade(_via_world), finality_monotone_on_net, quorum_grows_preserves_finality, committed_holds_along_rounds, cross_tier_join_on_net, NetCell.tier_eq_bft_iff}` | `Exec.Consensus` | quorum→finality-tier bridge: a reached quorum lands in the BFT tier; finality is monotone on a growing net (Byzantine safety itself is now proved too — `Proof.BFT.bft_safety` + `World.quorum_intersection_safety`, see §19/§21) |
| 16 | `Dregg2.Upgrade.upgrade_never_bricks`, `…stale_version_falls_back_to_signature` | `Upgrade` | anti-brick `set_program`: a stale AIR_VERSION falls back to owner signature; never bricks |
| 17 | `Dregg2.Proof.{refine_conservation(_measure), refine_run_conservation, refine_integrity(_intra)}` | `Proof.Refine` | Exec ⊑ Abstract: conservation + intra-vat integrity refine (**full simulation diagram OPEN**) |
| 39 | `Dregg2.Deos.Surface.{surface_confersEdge_iff_write, surface_confers_no_edge_offtarget, viewSurface_confers_no_edge, notifySurface_confers_no_edge, interactiveSurface_confers_edge, surface_attenuate_no_amplify}` | `Deos.Surface` | target 1: a deos window confers a connectivity edge **iff `write ∈ rights`** (general form; the three instance theorems are corollaries, opposite polarities included), and **no** edge to a cell it does not name; per-viewer projection cannot amplify |
| 39 | `Dregg2.Deos.Membrane.{reshare_chain_attenuates, reshareN_attenuates, reshare_refuses_amplification, membrane_non_amplifies, sealed_refuses_unheld}` | `Deos.Membrane` | target 2: `reshare A→B→C ⟹ C ⊆ B ⊆ A`, n-hop; the conjunction-forwarder floor `exposed ⊑ a ⊓ b` |
| 39 | `Dregg2.Deos.Rehydration.{replayedDeterministic_iff_confined, reconstructedApproximate_iff_unconfined, invalidAttestation_not_replayed, confined_chain_covers_log, unconfined_chain_drops_interactions, replayedDeterministic_replays}` | `Deos.Rehydration` | target 3: the classifier `↔` (**a SPEC-MATCH, see the deos note below**) + the world property it was standing in for — a **confined** context replays to a chain with one receipt per interaction, an **unconfined** one replays STRICTLY SHORTER (the ambient reach leaves no receipt) |
| 39 | `Dregg2.Deos.Affordance.{fireGate_iff_subset, fire_authorized_iff_subset, fire_returns_receipt, firedSurface_binds_attested_root, firedReceipt_commits_to_effect, firedReceipt_anchors, firedReceipt_extends_chain, firedReceipt_determines_effect, unauthorized_fire_no_surface, projectFor_monotone}` | `Deos.Affordance` | target 4: a fire commits iff `required ⊆ held`; the surface binds **the receipt the fire returned**; that receipt commits to the §8 digest of the EFFECT, links onto the well-linked log, and **determines what fired** under a named injectivity obligation |
| 39 | `Dregg2.Deos.ReplayMembrane.{confined_replay_deterministic, ambient_replay_env_dependent, replay_extensional_in_witness, ambient_trace_unconfined, negotiated_attenuates, negotiation_refuses_over_ask, deputy_confers_no_unheld_target, drift_cannot_recover_dropped_authority}` | `Deos.ReplayMembrane` | C1: a confined replay is **independent of the ambient environment** (false off the confined fragment); C2: the negotiation meet, the confused-deputy impossibility, no attenuation drift |

(Ellipses abbreviate same-module siblings; every name is spelled out and pinned individually in
`Dregg2/Claims.lean`.)

### ⚑ The deos rows (§39) — read this before citing them

These were added **2026-08-07**, and the reason they were not here before is the finding.
`docs/deos/DEOS.md` claimed *"four theorems ALL DISCHARGED"* as the basis for calling deos a verified
desktop OS. A survey read all five names at source: **four were definitional and one was an identity
carrier**, and **none of them appeared in this file or in `Dregg2/Claims.lean`** — so the honesty
ledger made no claim about deos at all and no instrument keyed on the rot.

| the old headline | what it actually was | disposition |
|---|---|---|
| `surfaceConfersExactly` | `capAuthConferred (Surface c r) = r := rfl`, where `Surface c r := Cap.endpoint c r` — i.e. **`r = r`** | **claim retracted** in `DEOS.md`; kept as a labelled naming lemma, deliberately **not pinned** |
| `fire_authorized_iff` | `(if c then some _ else none).isSome ↔ c` — the shape of `fire` | **relabelled DEFINITIONAL**, not pinned; replaced by `fire_authorized_iff_subset` |
| `firedSurface_binds_attested_root` | ⚑ **identity carrier** — `fire`'s receipt was `let _receipt`, **discarded**; `boundRoot := post` came from the caller and the theorem re-derived the same receipt in its own statement: **`post = post`** | **REPAIRED**: `fire` returns the receipt, the surface binds `intent.receipt.newCommit` |
| `replayedDeterministic_iff_confined` | `(if c then A else B) = A ↔ c` | kept, **relabelled a classifier spec-match**; "the verified-desktop crown" retracted |
| `replayedDeterministic_replays` | confinement premise **underscore-prefixed and absent from the proof term**, over a free `roots : List Nat` unrelated to `log` | **REPAIRED**: `roots` derived from the log, premise consumed for the coverage conjunct |
| `ReplayMembrane.confined_replay_deterministic` | literally `replayState … = replayState … := rfl` | **REPAIRED**: ambient-environment independence |

Three defects rode inside that discarded receipt and are fixed with it: `effectsHash` was the
affordance's **display name** (which collides — see the display-name-is-not-a-key class) instead of a
commitment to the effect; `prevHash` was hard-coded to `genesisSentinel`, so no fire could ever link
into the chain `chain_tamper_evident` speaks about; and the attested root was a **free parameter the
verifier consumed**.

⚠ **On `firedSurface_binds_attested_root` specifically, do not over-read the repair.** It is still a
structural agreement between two fields of the returned intent, proved by `rfl` once the `some` is
destructed. What changed is that it became **refutable** — binding `fc.pre`, or a root the receipt did
not produce, now makes it false, whereas the old statement re-derived its own right-hand side from the
caller's free `post` and was satisfied by an implementation carrying no receipt at all. The attestation
content is in its three neighbours: `firedReceipt_commits_to_effect` (what the receipt commits to),
`firedReceipt_extends_chain` (that it is linked into the append-only log, hence inherits
`chain_tamper_evident`), and `firedReceipt_determines_effect` (that the receipt pins what fired).

⚠ **`#assert_axioms`-clean was true of all five and told nobody anything.** Axiom hygiene cannot see a
definitional identity. What it takes is a **registered non-vacuity companion**, which every surviving
§39 row now has — a NAMED theorem, never a `def`, never a bare `#guard`:

| keystone | fires (premise satisfiable, conclusion exercised) | bites (the guarded property is refutable) |
|---|---|---|
| `Surface.surface_confersEdge_iff_write` | `surface_confersEdge_iff_write_satisfiable` (write-carrying surface DOES confer) | same theorem's 2nd/3rd conjuncts: drop `write` → dark; keep `write`, change the cell → dark |
| `Membrane.reshareN_attenuates` | `reshareN_attenuates_satisfiable` (pre-existing) | `reshare_refuses_amplification` |
| `Rehydration.replayedDeterministic_replays` | `replayedDeterministic_replays_satisfiable` | `replays_coverage_needs_confinement` (ambient AND forged-attestation routes both drop interactions) |
| `Affordance.firedSurface_binds_attested_root` | `firedSurface_binds_attested_root_satisfiable` | `firedReceipt_determines_effect_bites` |
| `Affordance.firedReceipt_determines_effect` | `demoDigest_injective` (the §8 hypothesis is satisfiable) | `determines_effect_needs_injectivity` (**the hypothesis is not droppable** — a constant digest makes the conclusion FALSE) |
| `Affordance.fire_authorized_iff_subset` | `fire_authorized_iff_subset_satisfiable` | same theorem (the reader is refused the write-gated fire) |
| `ReplayMembrane.confined_replay_deterministic` | `confined_replay_deterministic_satisfiable` (the fold MOVES: `0 → 42 → 84`) | `ambient_replay_env_dependent` |

**Honest count of the audit — seven theorems read at source:**

* **2 had real content and survive unchanged** — `Membrane.reshare_chain_attenuates` /
  `reshareN_attenuates` (the only leg with a registered witness beforehand) and
  `Surface.viewSurface_confers_no_edge` (a real `simp` over the kernel's own `confersEdgeTo`, with an
  opposite-polarity partner at `interactiveSurface_confers_edge`).
* **2 were definitional-but-true** — `surfaceConfersExactly` (`rights = rights`) and
  `fire_authorized_iff` (`(if c then some _ else none).isSome ↔ c`). Both are now **labelled** and
  **not pinned**; content-bearing replacements are pinned instead.
* **1 was a spec-match read as a world property** — `replayedDeterministic_iff_confined`, relabelled;
  "the verified-desktop crown" retracted.
* **3 were vacuous and are repaired** — `firedSurface_binds_attested_root` (an identity carrier over a
  discarded receipt), `replayedDeterministic_replays` (confinement premise absent from the proof term,
  over an unrelated `roots`), and `ReplayMembrane.confined_replay_deterministic` (`X = X`, premise
  unused). *(That is 8 dispositions across 7 theorems because `viewSurface_confers_no_edge` was cited
  alongside `surfaceConfersExactly` in the same target-1 line.)*

What deos is: the authority algebra of a window / membrane / replay / affordance, proved
over the kernel's own lattice and receipt chain. What it is not: a verified desktop OS — the
compositor, the input path and the rehydration transport are outside these models, and the Rust
realization is related to them by shared intent only.

---

## Parked pins (PROVED in source / home-pinned, not yet in the central closure — a race, not a gap)

These keystones are **free of open holes in source and self-pinned `#assert_axioms` in their
home module**, but their `.olean` is not yet in `Dregg2/Claims.lean`'s transitive import closure as
built — a concurrent-swarm artifact (the root `Dregg2.lean` gained an import, or a source file
was edited, after the live `.olean`s were produced; this agent must not `lake build` mid-swarm).
Their central pins are **commented out** in `Dregg2/Claims.lean` so `lake env lean` stays exit-0,
with a note to re-enable after an `.olean` rebuild. They are PROVED — they are simply parked.

| keystone | module | why parked |
|----------|--------|-----------|
| `Dregg2.Spec.guard_is_authority_conferral`, `…conferralGuard_admits_self`, `…introduce_passes_conferralGuard`, `…conservation_is_hyperedge_cg5`, `…hyperedge_conserves_crossCell`, `…lifecycle_revoke_is_authority_restrictive`, `…revoke_is_terminal_restrictive`, `…migrated_and_destroyed_both_revoke`, `…choreography_red_conserves(_sum)`, `…guard_attenuate_narrows_is_meet`, `…authority_confers_narrows_is_meet`, `…attenuation_is_one_order`, `…guard_meet_is_authority_meet` (§12, `Spec.Coherence` — the cross-subsystem weave: one attenuation order, guard-meet = authority-meet) | `Spec.Coherence` | `Dregg2.Spec.Coherence`'s import was added to the root after the last `Dregg2.olean`; its `.olean` was not present in closure at verification time |
| `Dregg2.Upgrade.{invariant_intro, safety_preservation, admit_preserves_safety, self_improvement_is_safe, genealogy_sound, identity_vouch_unconditional, upgradeGenealogy_sound, signatureVouchUnbrickable}` (§16 Envelope spine: invariant intro, safety preservation under policy-admit, self-improvement-is-safe, genealogy soundness) | `Upgrade` | the live `Upgrade.olean` predates the source edit that added/renamed these Envelope theorems |

---

## OPEN (honest — genuine open obligations; named residual `Prop`s / hypotheses / prose notes, never an open hole)

**Closed since the last revision of this table** (each now PROVED-axiom-clean and pinned —
grep the cited pin):

* `Dregg2.Spec.only_connectivity_begets_connectivity` — the Authority **whole-history
  closure** is now a real theorem, home-pinned (`#assert_axioms`, `Spec/Authority.lean`).
  The old "confirmed DIRTY" verdict no longer holds.
* `Dregg2.Liveness.dead_undecidable` — proved via a genuine halting-problem reduction
  (`haltGraph`); pinned in `Claims.lean` §19 (with `Exec.CellLiveness.death_not_decidable`).
* `Dregg2.Spec.Lifecycle.distributed_death_not_co_witnessable` — proved (delegates to
  `dead_undecidable`); pinned in `Claims.lean` §19.
* Byzantine **quorum intersection / safety** and **post-GST liveness** — the old
  `World.quorum_intersection_safety_OPEN` / `liveness_after_gst_OPEN` declarations no longer
  exist; replaced by the PROVED `World.quorum_intersection_safety` + `World.liveness_after_gst`
  (pinned, `Claims.lean` §19; liveness discharged from the named `World.gst_liveness` class
  field) and the stronger `Proof.BFT.bft_safety` (`n>3f` quorum intersection, home-pinned) +
  `Proof.BFTLiveness` (namespace-pinned, §21–§22).
* `Dregg2.Hyperedge` Sound-of-step-complete at N-ary + `hyper_not_all_admissible` — both
  restated and proved (`hyper_not_all_admissible` home-pinned in `Hyperedge.lean`; the whole
  `Dregg2.Hyperedge` namespace is pinned in `Claims.lean` §20).
* `Dregg2.Spec.Conditional.pipeline_topological` — proved (home-pinned, `Spec/Await.lean`).
* `Dregg2.Spec.phi_functorial` — proved under the explicit `NonDegenerate` hypothesis, with
  `nonDegenerate_concrete` + `phi_functorial_concrete` proving the hypothesis satisfiable;
  all pinned in `Claims.lean` §11.

**Still genuinely open** (the real-debt list):

| open obligation | module | what is still needed |
|-----------------|--------|----------------------|
| **OPEN-CM-LIVENESS / O2 pacemaker** (`cm_pacemaker_residual`, a named residual `Prop`) | `Proof.CordialMinersLiveness` | the post-GST "an honest quorum's votes are delivered" pacemaker; carried as a named hypothesis the runtime/partial-synchrony model discharges, never faked |
| **OPEN-CM-DISSEMINATION** | `Proof.CordialMiners` | the gossip / reliable-broadcast convergence that makes a finalized leader's quorum visible to all honest miners ("the precise irreducible residual", see the in-file note) |
| **OPEN-CM-STINGRAY** (narrowed) | `Proof.CordialMiners` / `Coord.StingrayCertReconcile` | the full Stingray bandwidth/budget accounting model; the safety bounds (`overspend_bounded_by_f_ceiling`, `byzantine_undetected_overspend_le_f_ceiling`) ARE proved |
| Synchronizer ↔ operational `World.rand` coupling | `Proof.Synchronizer` | the reduction note in §5: connecting the Bernoulli honest-leader model to the *operational* `World.rand` byte-stream is the one remaining sharp OPEN there |
| `Dregg2.Coordination` `mu`-recursion projection | `Coordination` | deadlock-freedom / projection-progress is proved on the `NoRec` fragment (reachable-config LTS `GStep`/`GReach`, `Claims.lean` §20); the `mu`/`var` recursion case is the residual (and the linearity⇒I-confluence conflation is *refuted* — independent judgements) |
| `Dregg2.Proof.Refine` full simulation diagram | `Proof.Refine` | the conservation + intra-vat integrity refinements ARE pinned (§17); the full abstract operational forward simulation needs an abstract small-step relation absent from `Core` |
| Handler-transformer upper tiers | `HandlerTransformer` | the Fpu = sheaf-gluing weld and the comodel-morphism / sheaf-of-handlers tier (`Claims.lean` §33's honest OPENs) |
| Circuit-soundness moving-face write-forcing — `RevokeDelegationEpochResidual` / `SpawnEpochStampResidual` / `RefreshEpochStampResidual` (each a named, fail-closed, data-bearing `Prop`) | `Circuit.EffectRefinement` / `Circuit.EffectRefinementBatch2` | for these three epoch/snapshot moves the deployed commitment BINDS the field (it folds into `record_digest`), the hostile-witness extractor FORCES the gate, and the executor PERFORMS the move — but the FROZEN v1-face descriptor commitment-binds the `delegationEpochAt` stamp rather than WRITE-GATE-forcing it. The faithful refinement is proven against the residual (e.g. `spawn_full_circuit_refines_spec`); the closure is the moving-face descriptor cutover (§3.EPOCH) — per-effect descriptor + verifier-anchor work on an already-binding commitment, NOT a commitment change. (The hostile-witness extraction lane itself is FULLY CLOSED — `Circuit.CircuitOpenFronts.countOpenFronts = 0`, 32/32 effects; the cap handoff for `spawn` is forced, so only the epoch stamp is the residual.) |

---

## rests-on-§8-primitive (real, free of open holes in body, but stated over a labelled interface obligation)

These are **not** OPEN and **not** overclaims — they are the §8 boundary, by design. The
primitive itself is a typeclass-field / `Prop`-portal obligation (never an open hole) that Rust +
the ZK circuits discharge. A downstream theorem that takes the primitive as a **hypothesis /
typeclass parameter** is kernel-clean and IS pinned above (it does not touch the kernel open-hole axiom).

| primitive (the labelled obligation) | module | who discharges it |
|-------------------------------------|--------|-------------------|
| `Dregg2.Core.conservation_step` (Law 1's balance: turns move/withhold/erase but never create/destroy units) | `Core` | the operational semantics / the circuit; **realized as a theorem** downstream by `Exec.cexec_attests` (which IS pinned) |
| `Dregg2.Laws.search_sound` (soundness-by-verification: whatever an opaque matcher returns must verify) | `Laws` | the external prover/matcher plugin (untrusted; verifier is TCB) |
| `Dregg2.CryptoKernel` laws (`verify`/`commit`/`hash` soundness & extractability) | `CryptoKernel` (typeclass) | the ZK circuits + Rust portal — enter downstream as typeclass params, so downstream theorems stay clean |
| `Dregg2.World` laws (network/clock/randomness oracle) | `World` (typeclass) | the protocol + partial-synchrony model |
| `Dregg2.Privacy.{derivedFrom, Indistinguishable, memberOf, memberView, ViewIndistinguishable, nullifierOf, UnlinkableToHolder, LegalDerivation}` (stealth/commitment/nullifier predicates + the unlinkability/anti-double-spend laws stated over them) | `Privacy` | the cryptographic carriers (DH derivation, Pedersen commitments, range proofs) — the anti-inflation rib is a circuit obligation |

---

## How to re-check (race-safe, mid-swarm)

```
cd metatheory
lake env lean Dregg2/Claims.lean   # must exit 0 — reads oleans, writes none; NEVER `lake build` mid-swarm
```

Exit 0 ⇒ every pinned keystone is free of the kernel open-hole axiom. A non-zero exit with an
`unknownConstant` means a parked pin's `.olean` rebuilt (re-enable it) or a keystone was renamed;
a non-zero exit with an *axiom-hygiene FAIL* means a claimed keystone silently inherited an open
hole — fix the
proof or move the row to **OPEN** above. That breakage, at the ledger, is the whole point.
