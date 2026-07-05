# The Elevated-Assurance Program — raising dregg to a genuine UC treatment

> ember: *"step up our level of assurance and proof engineering by a lot."*

This is the ordered, grounded program to move dregg from **refinement + partial
security-properties + an unwired UC shelf + assumed floors** to a **genuine UC-security
treatment**: explicit adversary model, whole-system (multi-turn / concurrent / adversarial)
composition, and machine-checked proof-engineering rigor.

Every "CURRENT" claim is grounded at `file:line` against HEAD (`db466dcd9`), verified
against the code, not just the survey. The baseline is `docs/audit/SECURITY-PROPERTY-MAP.md`
(the fresh security-property survey) cross-checked with `docs/audit/TRUST-BASE-CENSUS.md`
(the adversarial trust-floor census) and `docs/audit/TIER3.md`. All Lean paths are under
`metatheory/`.

**Design-only. This doc commits nothing but itself. It plans; it does not implement.**

---

## 0. Where we are — one honest paragraph

dregg today proves a **refinement backbone** (`descriptorRefines` / `BindingFromFold` /
`lightclient_unfoolable`, `Circuit/CircuitSoundness.lean:453`) and a real set of
**security-properties** (authority non-amplification `IsNonAmplifying`
`Exec/EffectsAuthority.lean:197`; conservation `reachable_total_zero`
`Exec/ReachableConservation.lean:49`; freshness `AssuranceCase.lean:581`; vault
no-dilution `Deos/Vault.lean:175`; settlement soundness `SettlementSoundness.lean:153`).
It has a **UC/crypto shelf** (`Metatheory/Open/PerfectUC.lean`) that closes only the
**perfect/statistical** fragment for **deterministic** ideals, wired **only** to the
selective-disclosure functionality (`realπ_realizes_idealF`, `PerfectUC.lean:448`). It
**lacks**: a computational UC theorem (explicitly OPEN, `PerfectUC.lean:502` + module
header), an **explicit adversary model** applied to the deployed guarantees, **whole-system
composition** (the apex `deployed_system_secure` is ONE turn, `AssuranceCase.lean:886`),
DECO-as-UC (unforgeability ASSUMED, `Crypto/Deco.lean:315`), SealedEscrow no-theft
(`Deos/SealedEscrow.lean` has replay + gate-binding but no economic invariant), and the
capacities' **pure-light-client** in-AIR witness (STAGED, `Deos/CapacitySatisfaction.lean:46-54`).

The target below is not "prove more of the same." It is to **re-cast the guarantees we have
as ideal-functionality realizations against an explicit adversary, compose them over the
whole execution, and make the assurance case a machine-checked whole with a stated
completeness argument.** Crucially, most of the target is **reachable from named existing
ingredients** — the refinements ARE the correctness legs of the realization proofs; what is
missing is the simulator, the environment quantification, and the composition wiring.

---

## Pillar 1 — THE UC TREATMENT (the marquee)

### 1a. The ideal functionalities dregg should UC-realize

dregg already *models* each of these abstractly; the program is to NAME them as ideal
functionalities `F` in one `Metatheory/UC/` frame and prove the deployed system realizes them.

| Ideal `F` | What it does by fiat | What already models it (reuse) |
|---|---|---|
| **`F_turn`** | An ideal capability-machine that, given an authorized request, applies the kernel step by fiat and returns a receipt; refuses unauthorized/unfresh requests. | The kernel semantics `interp` / `recKExec` + the five `AssuranceCase` guarantees ARE the properties `F_turn` should have. `deployed_system_secure` (`AssuranceCase.lean:886`) is its one-turn realization statement in disguise. |
| **`F_capability`** | Attenuable authority: a principal can delegate only a `⊆` of what it holds; no grant amplifies. | `IsNonAmplifying` (`EffectsAuthority.lean:197`); the kernel-level chain result `Membrane.reshareN_attenuates` (`Deos/Membrane.lean:122`); the cap-lattice `attenuate_subset`. This is the closest to a ready-made `F` — the property is already ∀-quantified over the kernel. |
| **`F_payment`** | Money-in: a payment of `≥ amountCents` was genuinely authenticated (DECO/fiat) or bridged, exactly once, unforgeably. | `deco_authenticates_payment` (`Crypto/Deco.lean:315`) is the *correctness leg*; bridge `BackedAt` (`BridgeBindingFromFold.lean:200`) is the mint-linkage leg. Neither is UC yet; both name their crypto floor. |
| **`F_ledger`** | Conservation + the committed forest: total value is invariant, the published root binds the whole post-state. | `reachable_total_zero` (`ReachableConservation.lean:49`) + `integrity_guarantee` whole-turn binding (`AssuranceCase.lean:412/486`) + the whole-history fold `light_client_verifies_whole_history` (`Circuit/RecursiveAggregation.lean:206`). |
| **`F_disclosure`** (already done, the template) | Selective field disclosure: the environment learns only public fields. | `realπ_realizes_idealF` (`PerfectUC.lean:448`) — **this is the one wired realization** and the pattern every other `F` should copy. |

**Reuse insight (the load-bearing one):** the realization of `F_disclosure` is the *shape*
of every other realization. Copy it: define `F`, define the real protocol `π` as the
deployed construct's behaviour, prove `π ⊑ F` (perfect) or `π ≈ F` (computational).

### 1b. The realization proofs — what it takes to prove the DEPLOYED system UC-realizes each `F`

For each `F`, a UC realization needs **(i)** a real protocol `π` (the deployed construct),
**(ii)** a simulator `S` producing the ideal-world view, **(iii)** indistinguishability of
`view_Z(π)` and `view_Z(S ∘ F)` for all environments `Z`.

- **The correctness legs already exist.** For `F_turn`/`F_ledger`, `deployed_system_secure`
  and the refinements (`descriptorRefines_complete`, `DescriptorRefinesComplete.lean:88`) give
  exactly "an accepting run corresponds to a genuine kernel step" — that is the *soundness half*
  a simulator needs (it can decode an accepting proof to the ideal action). For `F_capability`,
  `reshareN_attenuates` gives the ideal's refusal condition directly.
- **What is MISSING is the simulator + environment quantification.** Today the theorems are
  stated over a *fixed* accepted object, not over "for all `Z`, the ensembles are
  indistinguishable." The program: for each `F`, construct `S` that, given `F`'s ideal
  transcript, produces a real-world-looking view (it must *simulate proofs* — this is where
  the zero-knowledge / simulation-soundness of the STARK enters as a floor, `StarkSound`
  `Circuit/CircuitSoundness.lean:382`), and quantify over `Z`.

### 1c. `perfectUC_composition` as the composition backbone, and the gap to COMPUTATIONAL UC

`perfectUC_composition : π ⊑ F → (ρ ▷ π) ⊑ (ρ ▷ F)` (`PerfectUC.lean`, the `theorem`
verified in-file, `#assert_axioms`-clean) is a **real composition theorem** and IS reusable
as the composition backbone — but **only in the perfect collapse** where `≈` is `=` and `Z`'s
view is a *function*, not a probability ensemble. It is genuinely non-vacuous (teeth:
`leaky_fails_to_realize` `PerfectUC.lean`, the leak context reshapes information).

**The gap to the computational theorem is explicit and named** (`PerfectUC.lean:502`, module
header lines 58-65): it needs (i) an interactive-machine / probabilistic execution model
(`view_Z` a probability ensemble), (ii) a simulator witnessing *negligible* advantage `≈`
(not `=`), (iii) a hybrid argument over `ρ`. That is a **probabilistic-process-calculus
module of its own** — the single biggest new piece of the whole program.

**Ordered pieces for Pillar 1:**
1. `Metatheory/UC/Model.lean` — a computational execution model: PPT machines as a resource
   bound, ensembles indexed by security parameter `λ`, `≈` as negligible advantage. This is
   the greenfield core. *Reuse:* the `System`/`Context` structure of `PerfectUC.lean` is the
   deterministic skeleton to generalize; keep `⊑` as the `λ→∞` perfect specialization so the
   existing wired `F_disclosure` result survives as the perfect corner.
2. `Metatheory/UC/Composition.lean` — the computational composition theorem
   (`compUC_composition`) via a hybrid argument. *Reuse:* `perfectUC_composition` is the base
   case (advantage 0); the hybrid is the inductive step over `ρ`.
3. `Metatheory/UC/FCapability.lean`, `FTurn.lean`, `FLedger.lean`, `FPayment.lean` — the four
   realizations, each copying the `Disclosure` section of `PerfectUC.lean`. *Reuse:* the named
   correctness leg per row of the table in §1a is the soundness half of each simulator.
4. Wire the STARK's simulation-soundness/ZK as the floor the simulator rests on (a new Prop
   carrier `StarkZK` alongside `StarkSound`, `CircuitSoundness.lean:382`), correctly named
   terminal-by-design.

**Size:** LARGE. Piece 1 (the model) is 2-4 weeks of design-heavy Lean. Pieces 3 are ~1 week
each *given* the model (they copy a proven template). This is the marquee and the tail — do it
after the cheap-and-foundational pillars (2, 4) land, because they de-risk it.

---

## Pillar 2 — THE ADVERSARY MODEL (cheap, foundational — do FIRST)

### CURRENT
The current guarantees have an **implicit** adversary. `lightclient_unfoolable`
(`CircuitSoundness.lean:453`) proves "accept ⟹ genuine step" — the adversary is the
*prover*, but it is never named as a universally-quantified object; the forge-rejection teeth
(`amplifying_grant_rejected`, `forged_deployed_accepts` in the `*BackingAttack` files) each
assume a *specific* forger. **However — dregg already has the right object built:**
`Metatheory/KeyLeak.lean` (`key_leak_contained`, `:202`) instantiates the adversary as an
**opaque, universally-quantified controller** `ctrl : State → Action` and proves containment
is literally `Metatheory.Polis.polis_safety` (`Polis/Polis.lean:102`) with the attacker as
the ∀-quantified controller — *"verify the cage, not the animal."* This is the reusable
adversary-model kernel; it is currently applied only to key-leak, not to the crypto apex.

### TARGET
One `Metatheory/Adversary/` frame defining the explicit adversary class as a Lean object, and
each guarantee re-stated *against* it (`lightclient_unfoolable` → `unfoolable_against_A`).

### Ordered pieces
1. `Metatheory/Adversary/Model.lean` — the adversary class as a structure: **(a)** a PPT
   network adversary (schedules/drops/reorders messages), **(b)** a Byzantine node coalition
   `f < n/3`, **(c)** a malicious prover (chooses any proof/witness). *Reuse:* the opaque
   `ctrl : State → Action` of `KeyLeak.lean`/`polis_safety` IS the network+prover adversary
   already — generalize it from key-holding to full message/proof scheduling. The `f < n/3`
   coalition is a new parameter but the Byzantine-majority impossibility is already sketched
   abstractly in `Metatheory/Disputation.lean` (`byzantine_majority_cannot_uphold:79`) —
   metabolize it onto the deployed committee.
2. Make the forger **explicit and universal**: today each `*BackingAttack.lean` names a
   specific forged `VmRowEnv`. Re-state the teeth as "∀ adversary `A`, `A` cannot produce an
   accepting-yet-unbacked object" — the reduction to `StarkSound`/`Poseidon2SpongeCR` is
   already the content; the change is quantifying over `A` and reducing its success to breaking
   a named floor.
3. `unfoolable_against_A` — restate `lightclient_unfoolable` as "∀ PPT `A`, `Pr[A fools the
   light client] ≤ negl`," reducing to `StarkSound` + `CommitSurface` CR. *Reuse:* the existing
   `lightclient_unfoolable` body is the ε=0 core; the wrapper is the reduction.

### Size
SMALL-MEDIUM and high-leverage. The adversary *object* is ~1 week (the `KeyLeak`/`polis_safety`
pattern is the template). Re-stating each apex against it is mechanical once the object exists —
but it becomes *fully* meaningful only once Pillar 1's computational `≈` exists (piece 3's
"negl" needs the ensemble model). Land pieces 1-2 first as scaffolding; piece 3 lands with
Pillar 1.

---

## Pillar 3 — WHOLE-SYSTEM COMPOSITION (multi-turn / concurrent / adversarial)

### CURRENT
`deployed_system_secure` (`AssuranceCase.lean:886`) is a genuine composed theorem but over
**ONE deployed turn** (one committed forest `execFullForestG s f = some s'`, one noteSpend,
one published aggregate). The **multi-turn ingredients already exist**:
`light_client_verifies_whole_history` (`Circuit/RecursiveAggregation.lean:206`) proves the
published final root is the genuine fold of the *whole history* with the chain-bound tooth
`new_root[i] == old_root[i+1]` (`HistoryAggregation.ChainBound`), and `settlement_soundness`
(`SettlementSoundness.lean:153`) gives the temporal/revocation dimension. **Known residual:**
the fold's `genesis_root` is **prover-chosen and unanchored** (`RecursiveAggregation.lean:194`
+ deployed `lightclient/src/lib.rs:540`, per `TIER3.md`) — a prefix-completeness gap
(interior omission/injection are CLOSED).

### TARGET
`whole_execution_secure` — the five guarantees hold over an **arbitrary multi-turn,
concurrent, adversarial** execution, not one turn.

### Ordered pieces
1. **Anchor `genesis_root`** — close the `TIER3` residual: bind the fold's start to a committed
   genesis (a committee-anchored or hardcoded genesis root), turning `light_client_verifies_
   whole_history` from "some prefix" into "the whole chain from genesis." *Reuse:*
   `anchored_history_starts_at_genesis` (`RecursiveAggregation.lean:258`) already exists as the
   anchored variant — the gap is wiring the deployed verify API to demand it.
2. **Two routes to the whole-execution theorem, pick per Pillar-1 timing:**
   - **(a) via UC composition (preferred, rides Pillar 1):** once `F_turn` is realized and
     `compUC_composition` exists, the whole execution is `F_turn` composed with itself under
     the network context `ρ` — the composition theorem gives whole-system security for free.
     This is the clean route and the reason Pillar 3 *rides* Pillar 1.
   - **(b) direct inductive/coinductive theorem (fallback, no Pillar 1 needed):** an induction
     over the chain lifting the one-turn `deployed_system_secure` to the fold, using
     `ChainBound` as the inductive glue and `settlement_soundness` for the revocation dimension.
     *Reuse:* `light_client_verifies_whole_history`'s structure IS this induction for the
     E-leg; extend the same fold to A/B/C/D.
3. **Concurrency:** model interleaved turns as the event-structure / branch-and-stitch object
   already formalized — `SettlementSoundness` + the distributed-time-travel semantics
   (`docs/deos/DISTRIBUTED-TIMETRAVEL-SEMANTICS.md`, `stitch_pair`) give the concurrent-merge
   soundness. The program: state "concurrent turns that stitch preserve the five guarantees" as
   a corollary of settlement soundness over the config lattice.

### Size
MEDIUM. Piece 1 (anchor genesis) is small and independently valuable — do it early regardless
of Pillar 1. Piece 2(b) is a MEDIUM induction; 2(a) is "free" but gated on Pillar 1. Piece 3
reuses existing distributed proofs.

---

## Pillar 4 — PROOF-ENGINEERING RIGOR (cheap, foundational — do FIRST alongside Pillar 2)

### 4a. Minimize + machine-characterize the TCB

**CURRENT:** The floor is honestly named and `axiom`-free — carriers enter as `Prop`
typeclasses, never `axiom` keywords (`TRUST-BASE-CENSUS.md §1`; only two inert demo `axiom`s
exist, `Widget/Basic.lean:298-299`). The named floor: `StarkSound`
(`CircuitSoundness.lean:382`), `Poseidon2SpongeCR` (`Poseidon2Binding.lean:169`),
`Compress8CR` (`DeployedCapTree.lean:630`), `Ed25519EufCma` (`Crypto/Ed25519Reduction.lean:18`),
HMAC/AEAD/DLog (PortalFloor kernels), `PostGSTProgress`. Two "soft spots" already discharged:
`DeployedFaithful{,Eff,8}` is PROVEN in-tree (`deployedFaithfulEff_canonical`,
`DeployedCapTree.lean:551`), `DeployedRefines` is battery-checked
(`circuit/tests/deployed_refines_verifier_teeth.rs`).

**TARGET:** every floor carrier reduces to a **NAMED standard assumption with the reduction
stated**, and the dregg-specific-parked residuals are hunted to zero.

**Ordered pieces:**
1. `docs/reference/TCB.md` (a machine-linked TCB manifest) — one row per carrier: the standard
   assumption it equals (EUF-CMA / collision-resistance / FRI-soundness / DLog), the reduction
   theorem name, and whether it is standard vs dregg-specific. *Reuse:* `TRUST-BASE-CENSUS.md §1`
   is 90% of this already — promote it to a maintained, gate-linked artifact.
2. Hunt the `DeployedFaithful`/`R4` pattern for remaining parked dregg-properties: the census
   names one standing follow-up — `ExerciseHoldFaithful` (`RotatedKernelRefinementExerciseAuth.lean:89`)
   is the identical residual class, NOT yet discharged with the canonical pattern. Discharge it
   with `exerciseHoldFaithful_canonical` (drop-in of the `canonicalLeafAt` proof). Sweep for any
   other carried `hfaith`-style field over a free leaf/assignment.
3. State the FRI/STARK floor as the **specified** `AlgoStarkSound` + `DeployedRefines` chain
   (`starkSound_of_verifyAlgo`, `FriVerifierBridge.lean:106`) everywhere, so the terminal
   assumption is the *standard* "SNARK of a fixed verifier circuit is sound," not an ad-hoc bit.

**Size:** SMALL. Mostly promotion of the existing census + one Lean discharge (piece 2).

### 4b. Non-vacuity as a meta-theorem (the gate)

**CURRENT:** Non-vacuity is **spot-checked**: `#assert_axioms`/`#assert_namespace_axioms`
(`Dregg2/Claims.lean`, enforced by `scripts/axiom-hygiene-guard.sh` in CI) catch `sorry`/axiom
holes corpus-wide; per-keystone `*_satisfiable` + `*_teeth` witnesses (the `KeystoneAudit*`
files) prove each pinned keystone is true AND discriminating; `scripts/mutation-canary.sh`
empirically maps load-bearing vs decorative proofs by mutating the implementation. But there is
**no gate that every security-property theorem HAS a biting non-vacuity tooth** — it is
per-keystone discipline, not a meta-check.

**TARGET:** a lint/meta-gate: **every load-bearing security-property theorem is proven true AND
falsifiable-when-the-guard-breaks**, enforced in CI like the drift gate.

**Ordered pieces:**
1. A `@[security_property]` attribute + a registry (mirror `@[load_bearing_keystone]`,
   `AssuranceCase.lean`) tagging every security-property apex.
2. A meta-check (extend `Claims.lean` + a new `scripts/nonvacuity-gate.sh`) that fails CI if a
   `@[security_property]` decl lacks a paired `*_teeth` (a proof the property FAILS when its
   guard is broken — the `amplifying_grant_rejected` / `dilution_rejected` / `replay_rejected`
   shape). *Reuse:* the pattern already exists per-keystone; the gate makes it *total*.
3. Fold `mutation-canary.sh` into CI as the empirical backstop for the executor-side properties
   (today it is run-on-demand for supply/burn; generalize its mutation matrix to every
   security-property's implementation and assert the expected RED).

**Size:** SMALL-MEDIUM. High leverage — it converts "we spot-checked non-vacuity" into "the
build refuses a vacuous security property." Do this early; it protects every later pillar.

### 4c. Pin the "modulo a small explicit set of assumptions" hand-waves

**CURRENT:** `AssuranceCase.lean` and the apex variants carry prose like "modulo the §8 floor"
and name boundary seams (`AssuranceCase.lean:946+`: prover partition, `ShadowHostCtx`, producer
coverage). The `TRUST-BASE-CENSUS §3` enumerates S1-S9 named seams. These are honest but prose.

**TARGET:** every hand-wave pins to a **named Lean assumption or a named deployment seam with a
tracked closure lane** — no free-floating "modulo."

**Ordered pieces:**
1. Convert each prose "modulo X" in `AssuranceCase.lean` into a named hypothesis argument of the
   theorem (so `#assert_axioms` sees it) OR a row in `TCB.md` (4a) with a closure status.
2. The `A-4` daylight from the census (`TRUST-BASE-CENSUS §4`: the groundings
   algo-out-of-TCB / family-proven / witness-realized live in *separate* weld modules, never one
   final theorem) — build the **single final apex** that carries the minimal floor in one
   `#assert_axioms`, so an auditor reads the true trust base off one pin. This is the "assurance
   case as a machine-checked whole" deliverable.

**Size:** MEDIUM. Piece 2 (the single composed apex) is the valuable one and pairs naturally
with Pillar 3's whole-execution theorem.

### 4d. The assurance case as a machine-checked whole + a completeness argument

**CURRENT:** Five guarantees, conjoined at `deployed_system_secure` (`AssuranceCase.lean:886`).
There is **no coverage meta-theorem** stating the conjunction A∧B∧C∧D∧E *covers* the threat
model — the completeness of the guarantee set vs the adversary is argued in prose.

**TARGET:** a **coverage meta-theorem**: the five guarantees (once each is against the explicit
adversary of Pillar 2) imply the negation of every attack in a stated threat-model enumeration.

**Ordered pieces:**
1. Enumerate the threat model as a Lean sum type (message forge / replay / amplify / mint-forge
   / double-spend / equivocate / steal-from-escrow / dilute-vault …). *Reuse:* the
   `*BackingAttack.lean` files + `docs/deos/AGENT-CONFINEMENT-REDTEAM.md` + the census refutation
   targets R1-R8 are the enumeration.
2. `threat_model_covered` — a theorem: for each attack constructor, one of the five (adversary-
   indexed) guarantees rules it out; and dually, an attack NOT covered would be a `sorry`-visible
   hole. *Reuse:* each guarantee's teeth already refute one attack class — the meta-theorem is
   the case-split asserting the enumeration is exhausted.

**Size:** MEDIUM, and it is the capstone — it lands last, after Pillars 1-2 make the guarantees
adversary-indexed.

---

## Pillar 5 — CLOSE THE SECURITY-PROPERTY GAPS as UC instances

Frame each remaining gap as an **ideal-functionality realization**, not a bespoke lemma — this
is what makes them "raise the bar" rather than patch it.

| Gap | CURRENT (file:line) | Frame as | Ordered pieces + reuse | Size |
|---|---|---|---|---|
| **DECO-as-UC** | `deco_authenticates_payment` (`Crypto/Deco.lean:315`) is a soundness refinement; unforgeability ASSUMED (ed25519 EUF-CMA + HMAC + Web-PKI/Stripe); PerfectUC NOT wired to DECO. | `F_payment` realization (Pillar 1a). | Define `F_payment`; prove the deployed DECO verifier realizes it, with the simulator resting on `Ed25519EufCma` + `Poseidon2SpongeCR` (already the named floor). The correctness leg (`deco_authenticates_payment`) is the simulator's soundness half. | MEDIUM (rides Pillar 1) |
| **SealedEscrow no-theft** | `Deos/SealedEscrow.lean`: replay (`:257`) + gate-forcing (`:361`) + root-binding, but **NO** economic "funds cannot be stolen / value conserved across settle" invariant. | An `F_escrow` where the ideal releases funds only to the entitled party, value-conserving. | Prove the **standalone economic invariant** first (the missing `settle_conserves` / `no_theft` over the kernel `settle` fn, the analog of Vault's `deposit_no_dilution` `Deos/Vault.lean:175` and Lease's `remaining_plus_drawn_conserved` `Deos/PrepaidLease.lean:396`) — this is a self-contained property proof, no UC needed. THEN lift to `F_escrow`. | SMALL (the invariant) + MEDIUM (the lift) |
| **Capacity pure-LC witness** (gentian — **actively closing this session**) | Vault/escrow/obligation safety hold over pure math / executor / an **off-AIR** gate predicate whose VK is explicitly unchanged; the in-AIR weld is STAGED (`Deos/CapacitySatisfaction.lean:46-54`, `circuit/src/effect_vm/satisfaction_weld.rs`). | Each capacity invariant as a property a **pure light client** (not a re-executor) witnesses. | Emit the satisfaction weld into a committed VK + flip the live path (the gentian flag-day — note it is partially closing NOW). *Reuse:* the completeness core `omission_caught_under_binding` (`Deos/ConstraintBinding.lean:151`) and `carrier_omission_impossible` (`Deos/CapacityCarrier.lean:106`) are already proven ∀-universal; the gap is deployment, not proof. | MEDIUM (VK epoch, ember-gated) |

---

## RANKED ROADMAP — highest assurance-per-effort first

The ordering principle: **cheap-and-foundational scaffolding first** (it de-risks and is reused
by everything after), the **deep marquee** (computational UC) in the middle, the **capstone**
(whole-system + coverage) last because it rides the marquee.

**Tier 0 — cheap, foundational, do immediately (weeks, not months; high leverage):**
1. **Pillar 4b — the non-vacuity meta-gate.** Convert per-keystone teeth into a CI gate. Protects
   every later theorem from vacuity. (SMALL-MEDIUM)
2. **Pillar 4a — the TCB manifest + discharge `ExerciseHoldFaithful`.** Promote the census to a
   maintained gate-linked artifact; hunt the last parked dregg-property. (SMALL)
3. **Pillar 2 pieces 1-2 — the adversary object.** Generalize the `KeyLeak`/`polis_safety` opaque
   controller to the full network+prover+Byzantine adversary; make the forger explicit+universal.
   (SMALL-MEDIUM)
4. **Pillar 3 piece 1 — anchor `genesis_root`.** Close the one known whole-history completeness
   residual; independently valuable. (SMALL)
5. **Pillar 5 — SealedEscrow economic no-theft invariant.** A self-contained property proof
   (Vault/Lease template), no UC needed. (SMALL)

**Tier 1 — the deep marquee (the level-up):**
6. **Pillar 1 pieces 1-2 — the computational UC model + composition theorem.** The greenfield
   probabilistic-process-calculus core; `PerfectUC.lean` is the deterministic skeleton to
   generalize, its `F_disclosure` result the perfect corner that must survive. (LARGE)
7. **Pillar 1 piece 3 — the four realizations** `F_capability`/`F_turn`/`F_ledger`/`F_payment`,
   each copying the proven `Disclosure` template. `F_capability` first (closest to ready — the
   property is already ∀-over-the-kernel). (MEDIUM each, given #6)
8. **Pillar 2 piece 3 + Pillar 5 DECO/capacity** — restate the apex against the adversary with
   `negl` advantage; realize `F_payment` (DECO) and flip the capacity weld. (MEDIUM, rides #6)

**Tier 2 — the capstone:**
9. **Pillar 3 piece 2(a) — `whole_execution_secure` via UC composition.** Whole-system security
   as `F_turn` composed under the network context — "free" once #6 lands. (MEDIUM)
   - *Fallback if #6 slips:* Pillar 3 piece 2(b), the direct inductive lift of
     `deployed_system_secure` over the `ChainBound` fold — MEDIUM, no UC dependency.
10. **Pillar 4c-4d — the single composed apex + the coverage meta-theorem.** One `#assert_axioms`
    carrying the minimal floor (closes the `A-4` daylight); `threat_model_covered` proving the
    guarantee set exhausts the enumerated threat model. The assurance case as a machine-checked
    whole. (MEDIUM)

**The through-line:** Tier 0 makes the existing guarantees *rigorous and adversary-explicit*
cheaply. Tier 1 builds the *one genuinely new deep object* — computational UC — and recasts the
guarantees as realizations. Tier 2 *composes* them over the whole adversarial execution and
proves the set *complete*. Every target is reachable from a named existing ingredient: the
refinements are the correctness legs, `PerfectUC` is the composition skeleton, `KeyLeak`/
`polis_safety` is the adversary object, `RecursiveAggregation` is the multi-turn fold, and the
`KeystoneAudit`/drift/`mutation-canary` infrastructure is the rigor gate to generalize.

---

## Appendix — the reuse map (what named thing seeds each new piece)

| New piece | Seeded by (file:line) |
|---|---|
| Computational UC model | `PerfectUC.lean` `System`/`Context`/`⊑` skeleton; `perfectUC_composition` as ε=0 base |
| `F_disclosure` (done — the template) | `realπ_realizes_idealF` (`PerfectUC.lean:448`) |
| `F_capability` realization | `IsNonAmplifying` (`EffectsAuthority.lean:197`), `reshareN_attenuates` (`Deos/Membrane.lean:122`) |
| `F_turn` / `F_ledger` correctness legs | `deployed_system_secure` (`AssuranceCase.lean:886`), `descriptorRefines_complete` (`DescriptorRefinesComplete.lean:88`) |
| `F_payment` correctness leg | `deco_authenticates_payment` (`Crypto/Deco.lean:315`), bridge `BackedAt` (`BridgeBindingFromFold.lean:200`) |
| Adversary object | `key_leak_contained` (`KeyLeak.lean:202`) = `polis_safety` (`Polis/Polis.lean:102`), opaque `ctrl : State → Action` |
| Byzantine `f<n/3` leg | `byzantine_majority_cannot_uphold` (`Disputation.lean:79`) |
| Whole-execution fold | `light_client_verifies_whole_history` (`RecursiveAggregation.lean:206`), `anchored_history_starts_at_genesis` (`:258`) |
| Temporal/revocation dimension | `settlement_soundness` (`SettlementSoundness.lean:153`), `deployedSettle` (`:289`) |
| Non-vacuity gate | `KeystoneAudit*` `*_satisfiable`/`*_teeth`; `Claims.lean` `#assert_axioms`; `axiom-hygiene-guard.sh`; `mutation-canary.sh` |
| TCB manifest | `TRUST-BASE-CENSUS.md §1`; `starkSound_of_verifyAlgo` (`FriVerifierBridge.lean:106`) |
| `ExerciseHoldFaithful` discharge | `deployedFaithfulEff_canonical` (`DeployedCapTree.lean:551`) pattern |
| SealedEscrow no-theft | `deposit_no_dilution` (`Vault.lean:175`), `remaining_plus_drawn_conserved` (`PrepaidLease.lean:396`) |
| Capacity pure-LC weld | `omission_caught_under_binding` (`ConstraintBinding.lean:151`), `CapacitySatisfaction.lean:46-54` (STAGED) |
| Threat-model enumeration | the `*BackingAttack.lean` refutations; `AGENT-CONFINEMENT-REDTEAM.md`; census R1-R8 |
