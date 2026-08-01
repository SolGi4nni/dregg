/-
# Dregg2.Verify.RestFrameFiniteSupportSuccessor — F1: the finite-support SUCCESSOR of
`RestHashIffFrame`, STATED, checked SATISFIABLE / REFUTABLE / NOT PROVABLE, and one downstream
consumer RE-DERIVED through it. De-risking the fork; NOT the 234-position port.

⚑ Substrate, said plainly: this is LEAN-AUTHORED metatheory over `Dregg2.Circuit.StateCommit`'s
commitment surface — `RestHashIffFrame` is a `Prop`-valued hypothesis carried by soundness/binding
THEOREMS about an AIR the Lean side emits (`StateCommit.emittedState`); nothing here is a Rust AIR,
a hand-written `Builder` gadget, or an `air_accepts` predicate, and nothing here touches `circuit/`,
`turn/`, `cell/`, `node/`, or `sdk/`.

## The wound this file responds to

`Circuit.RestFrameCardinalityFloor.restHashIffFrame_false_by_cardinality` (07-27) proves
`RestHashIffFrame RH` UNSATISFIABLE for every `RH : RecordKernelState → ℤ`, at every width, by
Cantor: `bal : CellId → AssetId → ℤ` — and, by the identical argument, EIGHT more per-cell/per-label
side-tables (`caps`, `slotCaveats`, `lifecycle`, `deathCert`, `delegate`, `delegations`,
`delegationEpoch`, `delegationEpochAt`, `heaps`; see `Verify.InjSpelledFloors`'s
`uncountable_bal`/`uncountable_caps`/`uncountable_cellNat`/… instances) — is a function space over
an INFINITE index, and no countable-codomain hash separates it. `Verify.ApexPremiseVacuity` shows
this alone leaves `AssuranceCase.deployed_system_secure`/`unfoolability_guarantee`'s CRITICAL-3
(conservation-from-verification) half unreachable at ANY parameters, not merely deployed ones.

The named repair, in both files' own words, is to digest the FINITE support actually touched — the
`accounts : Finset CellId` rows — never the whole function. Full adoption is 234 binder positions
across 85 modules PLUS `CircuitSoundness.CommitSurface`'s field: a commitment-epoch flag day ember
has not authorized. This file does NOT do that port. It states the successor obligation, checks it
against the tree's own floor doctrine (a floor must be SATISFIABLE and REFUTABLE but NOT PROVABLE),
and re-derives one real consumer through it — then prices what the full port would cost.

## The discovery this file is built on: the repair machinery already exists, just unconnected

`Dregg2.Circuit.FinKernelState` (LIVE — imported transitively at the `Dregg2.lean` root) already
remodels every function-valued `RecordKernelState` field as a sorted-nodup finite map
(`FinKernelState`, `denote : FinKernelState → RecordKernelState`, `denote_injective` PROVED
UNCONDITIONALLY — no crypto hypothesis at all). `Dregg2.Circuit.FinFrameHash` (also LIVE) builds a
concrete rest-hash `RH_fin` and proves `restHashIffFrame_of_fin` — `RestHashIffFrame`'s EXACT
18-conjunct body, quantified over the `denote`-image rather than all of `RecordKernelState`. Neither
file is named as "the F1 repair", and NEITHER is wired to `RestFrameCardinalityFloor` /
`ApexPremiseVacuity` (no cross-reference either way) — this file makes that connection explicit,
restates the obligation as a standalone `Prop` (so it can be discussed and reasoned about
independent of one sponge choice, and so a consumer theorem can carry it as an ordinary hypothesis,
the same way it carries `RestHashIffFrame` today), and runs the floor-doctrine checks the existing
files never ran (satisfiable / refutable / not provable — `ApexPremiseVacuity` checked exactly this
for the OTHER four commitment-floor legs but, having just proved `RestHashIffFrame` dead at every
parameter, had no occasion to check its replacement).

`Dregg2.Circuit.FinBindsKernel` — which builds the FULL kernel-recovery keystone
(`recStateCommit_binds_kernel_fin`) on top of `FinFrameHash` — is marked HISTORICAL / "retired from
the apex" in its own header, for an UNRELATED reason: it discharges `Poseidon2SpongeCR sponge` as
the SOLE residual for the whole state, and `Poseidon2SpongeCR` (bounded-hash injectivity) is ITSELF
refuted at deployed BabyBear width by the SAME pigeonhole argument that refutes `compressInjective`
(`ApexPremiseVacuity`'s LEGS 1-4) — a WIDTH problem, not the DOMAIN/cardinality problem this file
answers. `restHashIffFrame_fin`/`restHashIffFrame_of_fin` are themselves already grandfathered on
`Verify.FloorRatchetBaseline` for exactly that width reason. Using them here at the UNBOUNDED
reference sponge (`Poseidon2Binding.Reference.refSponge`, genuinely `Poseidon2SpongeCR` by
`refSponge_CR`, NOT BabyBear-bounded — the same abstract-but-not-deployed pole
`ApexPremiseVacuity §3.2`'s `pairCompress` occupies for `compressInjective`) is the correct, honest
witness for THIS file's question — is the DOMAIN obstruction repairable at all — and answers it
unconditionally (no carried hypothesis survives in the theorems below; `refSponge_CR` is a closed
proof, not a binder). The width obstruction is separate, already named, and not this file's job.

No `sorry`, no `axiom`, no `native_decide`. No `FloorRatchetBaseline` row is added: nothing below
carries a hypothesis this tree proves false — `restHashIffFrameFin_satisfiable` is a CLOSED,
unconditional theorem (the only "floor" is `refSponge_CR`, already discharged).
-/
import Dregg2.Circuit.FinBindsKernel
import Dregg2.Circuit.StateCommit
import Dregg2.Circuit.RestFrameCardinalityFloor

namespace Dregg2.Verify.RestFrameFiniteSupportSuccessor

open Dregg2.Exec (CellId AssetId Value RecordKernelState Turn)
open Dregg2.Circuit.FinKernelState (FinKernelState denote finInit)
open Dregg2.Circuit.FinFrameHash (RH_fin restHashIffFrame_of_fin rootedInit
  denote_carries_nullifierRoot)
open Dregg2.Circuit.FinBindsKernel (RH_fin_separates_root)
open Dregg2.Circuit.Poseidon2Binding
open Dregg2.Circuit.StateCommit (satisfiedS encodeS stateCircuit cSRestFrame srestframe_iff
  RestHashIffFrame)

set_option autoImplicit false

/-! ## §1 — the successor obligation, ADOPTED (no longer declared here).

⚑ **MOVED 2026-07-31.** `FiniteRepresentable` and `RestHashIffFrameFin` were DECLARED in this file
when it was a de-risking study. They are now the LIVE obligation — `StateCommit.recStateCommit_binds_kernel`
and `CircuitSoundness.CommitSurface.restFrame` both take them — so they had to move BELOW
`StateCommit` in the import graph, and they live in `Dregg2.Circuit.RestFrameFin`. This file's copies
are DELETED rather than kept in sync: two shapes that agree today are two shapes that will disagree
later, and a duplicated `RestHashIffFrameFin` is precisely the kind of pair that would silently
diverge from the one the apex actually carries.

`RestFrameFin` also carries the piece this file could only assert in prose: an `AccountsWF` kernel
that is NOT `FiniteRepresentable` (`not_finiteRepresentable_of_lifecycle_ne_zero`), so the domain
restriction is a machine-checked fact rather than a claim about `balFam`. -/

open Dregg2.Circuit.RestFrameFin (FiniteRepresentable RestHashIffFrameFin
  finiteRepresentable_of_denote not_finiteRepresentable_of_lifecycle_ne_zero)

/-- The genuine-weakening weld (`RestHashIffFrame → RestHashIffFrameFin`) now lives beside the full
carrier, as `StateCommit.restHashIffFrameFin_of_full`; re-pinned here so this file's ladder still
reads top-to-bottom. -/
theorem finFrame_of_full (RH : RecordKernelState → ℤ) (hFull : RestHashIffFrame RH) :
    RestHashIffFrameFin RH :=
  Dregg2.Circuit.StateCommit.restHashIffFrameFin_of_full RH hFull

/-! ## §2 — SATISFIABLE, unconditionally. -/

/-- **SATISFIABLE.** `RH_fin refSponge` — `FinFrameHash`'s rest-hash at the UNBOUNDED reference
sponge (genuinely `Poseidon2SpongeCR` by `refSponge_CR`, the abstract-but-not-deployed pole) —
satisfies `RestHashIffFrameFin` with NO CARRIED HYPOTHESIS: `refSponge_CR` is a closed proof, so
this theorem's own type binds nothing. This is exactly the theorem `RestHashIffFrame` could never
have (`restHashIffFrame_false_by_cardinality` refutes EVERY `RH`, full stop): the obstruction was
the DOMAIN, and restricting it to `FiniteRepresentable` pairs is enough, on its own, with no other
change. -/
theorem restHashIffFrameFin_satisfiable :
    RestHashIffFrameFin (RH_fin Reference.refSponge) := by
  rintro k k' ⟨f, rfl⟩ ⟨f', rfl⟩
  exact restHashIffFrame_of_fin Reference.refSponge Reference.refSponge_CR f f'

/-- **CONCRETE EXHIBIT — not the trivial diagonal.** Two DISTINCT reachable states
(`rootedInit`/`finInit`, differing only in the nullifier-accumulator root) get DISTINCT rest hashes:
the biconditional's forward direction genuinely fires on an instance, the same pair
`restHashIffFrameFin_refutable` below reuses to show the negative pole. (Reuses
`FinBindsKernel.RH_fin_separates_root`, itself built from `restHashIffFrame_of_fin`.) -/
theorem restHashIffFrameFin_fires :
    RH_fin Reference.refSponge (denote rootedInit) ≠ RH_fin Reference.refSponge (denote finInit) :=
  RH_fin_separates_root

/-! ## §3 — REFUTABLE, hence NOT PROVABLE: the obligation genuinely discriminates among rest-hashes.

A floor that held for every `RH` would carry no content (the same disease `ApexPremiseVacuity §5`
diagnoses in the tree's satisfiability-companion schema). The constant rest-hash — the laziest
possible candidate — fails `RestHashIffFrameFin`, at the SAME reachable pair §2 used to show the
positive pole, so satisfiability and refutability are about the same two states, not ones each
picked to make its own proof easy. -/

/-- **REFUTABLE.** `fun _ => 0` cannot possibly separate `rootedInit` from `finInit` (both hash to
`0`), yet the two states genuinely differ in `nullifierRoot` — so the forward direction of the
biconditional fails, at a pair BOTH sides of which are `FiniteRepresentable`. -/
theorem restHashIffFrameFin_refutable :
    ¬ RestHashIffFrameFin (fun _ : RecordKernelState => (0 : ℤ)) := by
  intro h
  obtain ⟨_hAcc, _hCaps, _hBal, _hNul, _hRev, _hCom, _hSC, _hFac, _hLif, _hDC, _hDel, _hDgs, _hDE,
    _hDEA, _hHeaps, hNR, _hRR, _hCR⟩ :=
    (h (denote rootedInit) (denote finInit)
        (finiteRepresentable_of_denote rootedInit) (finiteRepresentable_of_denote finInit)).mp rfl
  have h0 : (denote finInit).nullifierRoot 0 = (denote rootedInit).nullifierRoot 0 :=
    congrFun hNR 0
  rw [denote_carries_nullifierRoot] at h0
  rw [show (denote finInit).nullifierRoot 0 = 0 from rfl] at h0
  exact absurd h0 (by decide)

/-- **NOT PROVABLE.** Since SOME `RH` fails `RestHashIffFrameFin` (the previous theorem), it is not
a schema true of every rest-hash outright — a genuine floor, discriminating between choices of `RH`,
not a tautology in a floor's clothing. Together with §2, `RestHashIffFrameFin` clears all three
checks the tree's own doctrine demands: SATISFIABLE, REFUTABLE, NOT PROVABLE. -/
theorem restHashIffFrameFin_not_provable :
    ¬ ∀ RH : RecordKernelState → ℤ, RestHashIffFrameFin RH :=
  fun h => restHashIffFrameFin_refutable (h (fun _ => 0))

/-! ## §4 — ONE DOWNSTREAM CONSUMER, RE-DERIVED.

`StateCommit.stateCircuit_rejects_field_tamper` is the smallest real theorem in the tree carrying
`RestHashIffFrame` as a hypothesis (a single conjunct extracted — `nullifiers` — to contradict a
tamper). Re-derived here, same proof shape, through `RestHashIffFrameFin` plus the two
`FiniteRepresentable` witnesses instead of the unsatisfiable full carrier: the ladder demonstrated,
not asserted. -/

/-- **Re-derivation of `StateCommit.stateCircuit_rejects_field_tamper`, over finite representatives.**
Any witness whose post-state changes a non-`cell` component (here `nullifiers`) still makes
`satisfiedS` UNSATISFIABLE — the rest-frame gate forces `RH (denote f) = RH (denote f')`, and
`RestHashIffFrameFin.→` (now genuinely APPLICABLE, since `denote f`/`denote f'` are
`FiniteRepresentable` BY CONSTRUCTION) forces the nullifier sets equal — contradiction. Same
conclusion, same tamper, same gate; the only change is which floor the middle step rests on. -/
theorem stateCircuit_rejects_field_tamper_fin
    (CH : CellId → Value → ℤ) (RH : RecordKernelState → ℤ)
    (cmb compress : ℤ → ℤ → ℤ) (compressN : List ℤ → ℤ)
    (hRestFin : RestHashIffFrameFin RH)
    (f : FinKernelState) (t : Turn) (f' : FinKernelState)
    (hfield : (denote f').nullifiers ≠ (denote f).nullifiers) :
    ¬ satisfiedS cmb compress
        (encodeS CH RH cmb compress compressN (denote f) t (denote f')) := by
  rintro ⟨hsat, _⟩
  have hrestgate : cSRestFrame.holds
      (encodeS CH RH cmb compress compressN (denote f) t (denote f')) :=
    hsat cSRestFrame (by unfold stateCircuit; simp)
  have hRHeq : RH (denote f) = RH (denote f') :=
    (srestframe_iff CH RH cmb compress compressN (denote f) t (denote f')).mp hrestgate
  have hframe18 := (hRestFin (denote f) (denote f')
      (finiteRepresentable_of_denote f) (finiteRepresentable_of_denote f')).mp hRHeq
  obtain ⟨_, _, _, hNul, _⟩ := hframe18
  exact hfield hNul

/-- **The re-derivation actually FIRES on a concrete instance** (not merely well-typed): the
Poseidon2 toy portal from `StateCommit`'s own `#guard` section (`chConcrete`/`rhConcrete`/…) rejects
the same nullifier-tamper the original theorem was built to catch, now routed through
`RestHashIffFrameFin (RH_fin Reference.refSponge)` — a DIFFERENT rest-hash than `StateCommit`'s toy
`rhConcrete`, chosen because it is the one this file actually proved the successor for. -/
example (t : Turn) (f f' : FinKernelState)
    (hfield : (denote f').nullifiers ≠ (denote f).nullifiers) :
    ¬ satisfiedS Dregg2.Circuit.StateCommit.cmbConcrete Dregg2.Circuit.StateCommit.compressConcrete
        (encodeS Dregg2.Circuit.StateCommit.chConcrete (RH_fin Reference.refSponge)
          Dregg2.Circuit.StateCommit.cmbConcrete Dregg2.Circuit.StateCommit.compressConcrete
          Dregg2.Circuit.StateCommit.compressNConcrete (denote f) t (denote f')) :=
  stateCircuit_rejects_field_tamper_fin Dregg2.Circuit.StateCommit.chConcrete
    (RH_fin Reference.refSponge) Dregg2.Circuit.StateCommit.cmbConcrete
    Dregg2.Circuit.StateCommit.compressConcrete Dregg2.Circuit.StateCommit.compressNConcrete
    restHashIffFrameFin_satisfiable f t f' hfield

/-! ## §5 — PRICING THE PORT (measured, not guessed).

**What `CommitSurface` becomes.** `CircuitSoundness.CommitSurface`'s fifth field
(`restFrame : RestHashIffFrame RH`) becomes `restFrame : RestHashIffFrameFin RH` — ONE line. The
`FiniteRepresentable k`/`FiniteRepresentable k'` obligations do NOT belong in `CommitSurface` itself
(it is a bundle of FUNCTIONS, not of states) — they belong exactly where `AccountsWF k`/`AccountsWF
k'` already sit today, as sibling per-call hypotheses on every consumer theorem
(`recStateCommit_binds_kernel`, `transfer_circuit_full_sound`, `root_tooth_pins_kernel`,
`finalized_commit_binds_revoked`, …). `CommitSurface` becomes constructible for the FIRST TIME in
its fifth field alone — `apexCommitFloor_unsatisfiable` dies — but remains uninhabited overall: its
other four fields (`cmbInj`/`compInj`/`compNInj`/`leafInj`) are refuted at deployed BabyBear width by
an INDEPENDENT pigeonhole argument (`ApexPremiseVacuity` LEGS 1-4,
`apexCommitFloorSansRest_false_at_babyBear`), and that repair (a keyed collision-resistance advantage
bound, `HashFloorHonesty`/`StateCommitFloorRegrounded`/`Poseidon2KeyedBridge`/
`thread_advantage_bound` — already live machinery) is a SEPARATE campaign this port does not touch.
Landing F1 alone retires ONE of the apex's five vacuity causes, not all five.

**Binder-position count, measured today (not the header's 07-27 snapshot):** a plain grep for
`RestHashIffFrame` finds 447 mentions across 108 files, of which ~232 are binder-shaped
(`hRest : RestHashIffFrame RH` or `RestHashIffFrame S.RH`) — consistent with the header's "234
across 85 modules" (files vs. "modules" is a coarser unit than a raw file count, and a handful of
files are doc-only mentions). SAMPLED across `Distributed/HistoryAggregation.lean`,
`Circuit/SettlementSoundness.lean`, `Circuit/CouncilCommit.lean`: the dominant shape is a theorem
over `∀`-arbitrary `(k k' : RecordKernelState)` (or a field of one, e.g. `s.post.kernel`) that
ALREADY carries `AccountsWF k`/`AccountsWF k'` beside `hRest` — i.e. the exact slot the two new
hypotheses drop into. For these (the large majority sampled), the port is MECHANICAL: widen the
binder list, thread `FiniteRepresentable` to the one or two call sites that apply `hRest`/
`recStateCommit_binds_kernel`. No new proof content per site.

**⚑ A second family the header's count does NOT include.** `Circuit/EffectCommit2.lean` names 13
sibling predicates — `RestIffNoBal`, `RestIffNoCaps`, `RestIffNoNullifiers`, `RestIffNoCommitments`,
`RestIffNoDelegations`, `RestIffNoLifecycle`, `RestIffNoLifecycleDeathCert`, `RestIffNoCellHeaps`,
`RestIffNoCapsEpoch`, `RestIffNoFactoryTouched`, `RestIffNoAccountsBalBorn`, `RestIffNoBalEscrows`,
`RestIffNoSpawnTouched` — each `RestHashIffFrame`'s body with ONE (or two) touched fields omitted,
used by the ~17-25 per-effect files under `Circuit/Inst/*.lean`/`Circuit/Witness/*.lean` for effects
that legitimately change one non-`cell` component. Every one of these STILL demands full-function
equality on the OTHER eight-or-nine function-space fields, so EVERY one is unsatisfiable by the
identical Cantor argument (a different indicator family, same cardinality obstruction) — this file's
successor pattern generalizes to each of them (drop the same field's line from
`FinFrameHash.serializeRestFin`/`restBody_iff_restAgree`), but that is 13 MORE small, mechanical,
NOT-YET-WRITTEN files, not a byproduct of porting the 234.

**The genuinely NON-mechanical cost: `FinKernelState`'s own honesty gate.**
`FiniteRepresentable k` is usable at a call site only once `k` is PROVEN reachable — and
`FinKernelState.denote_surjective_on_reachable` proves that ONLY given `hpres : ∀ e f, denote
(finStep e f) = recStep e (denote f)`, an EXPLICIT hypothesis `FinKernelState.lean`'s own header
assigns to "lane R3" and which is NOT discharged for any effect today. Concretely this needs, per
real effect handler (~17-25 of them, one per `Circuit/Inst/*.lean` file): (1) a `finStep` — the
finite-map-level step (a `SortedMap`/`CanonMap` insert/update) — and (2) a proof it commutes with the
real kernel step. That is genuinely NEW proof engineering, comparable in size to each effect's
existing soundness proof (order ~50-150 lines each), so roughly 1000-3000 lines total — NOT
mechanical, and it is the part that turns "the successor is satisfiable in the abstract" (this file)
into "the successor is satisfiable AT THE STATES THE 234 THEOREMS ARE ACTUALLY APPLIED TO".

**Summed price, in three buckets:**
1. ~230 mechanical binder-list widenings + threading (RestHashIffFrame sites) — low effort, no new
   math, contingent on (3) TO APPLY AT REAL STATES (but see §5b: not to LAND).
2. ~13 new small files generalizing the same pattern to the `RestIffNo*` family — mechanical but
   unwritten, contingent on (3) in the same sense.
3. ~17-25 per-effect `hpres` proofs (`FinKernelState`'s undischarged honesty gate) — genuine new
   engineering, the load-bearing cost, and a PREREQUISITE for (1) and (2) to apply to any REAL
   (post-genesis) state rather than only to the abstract witnesses this file exhibits.
Independent of all three: the width-bound legs (1-4) remain refuted at deployed BabyBear parameters
regardless, so even a completed port does not revive `deployed_system_secure`/
`unfoolability_guarantee` on its own.

## §5b — ⚑ THE PRICING ABOVE WAS CORRECT AND WAS READ WRONG. Measured 2026-07-31.

The three buckets are real and none of them is retracted. But the sentence a reader takes away —
*"~230 binder positions, 13 uncounted siblings, and 17-25 handler commuting squares"* — was quoted as
the cost of **RE-INHABITING `CommitSurface`**, and it is not. It is the cost of porting EVERY
`RestHashIffFrame` consumer in the tree, which is a different and much larger job.

**What re-inhabiting the bundle actually took, measured by doing it:**

  * ONE field-type change (`restFrame`), exactly as §5 predicted;
  * `StateCommit.recStateCommit_binds_kernel` rewritten IN PLACE (`hRest` weakened, `hfin`/`hfin'`
    added beside `hwf`/`hwf'`), and the same two hypotheses threaded to the ~9 declarations that
    apply it or `CommitSurface.commit_binds` — `CircuitSoundness` (3), `StateCommitReduce` (6),
    `CrossTurnFreshness` (the `TurnChain.finrep` field + 5), `Freshness` (4),
    `CommitFaithfulRegrounded` (7 — a SECOND bundle, ported in the same pass),
    `HistoryAggregation` (`SeamStruct` + 3), `CouncilCommit` (3), `Market.WideCommitBoundary` (2);
  * ZERO of bucket (3). No `hpres`, no `finStep`, no per-effect commuting square.

**Why bucket (3) is not a prerequisite for landing.** `hpres` is what would let a call site DISCHARGE
`FiniteRepresentable k` for an executor-reached `k`. Landing the successor only requires that the
hypothesis be STATEABLE and the surface CONSTRUCTIBLE — and `restHashIffFrameFin_satisfiable` above
is a CLOSED theorem, so the surface is constructible today (§6). Bucket (3) is the cost of making the
uniqueness half apply to a RUNNING chain, which is exactly where it now sits and is named.

⚠ **So the honest sequencing is the reverse of the one the pricing implied.** Doing (3) first would
have been 1000-3000 lines of per-effect proof feeding an obligation nothing yet consumed. Landing the
cutover first makes (3) the ONLY thing between a constructed reference surface and a deployed claim
about a live chain — a named, single, load-bearing residual instead of a diffuse one.
-/

/-! ## §6 — ★ THE CONSTRUCTED INHABITANT: `CommitSurface` has a value, for the first time.

`Verify.ApexPremiseVacuity.apexCommitFloor_unsatisfiable` refutes the apex's five-field bundle at
EVERY parameter, and `CircuitSoundness.CommitSurface` carried the same five as FIELDS — so it had no
inhabitant, so every theorem quantified over one was vacuous and (worse) UNREFUTABLE:
`(S : CommitSurface) → ¬ P S` is true for free.

That is no longer the case. The five fields are now discharged by CLOSED proofs at the reference
sponge — four from `Poseidon2SpongeCR Reference.refSponge` (`refSponge_CR`, itself closed) and the
fifth from `restHashIffFrameFin_satisfiable` above. Nothing below carries a hypothesis.

⚑ **WHY THESE ARE `example`s AND NOT NAMED THEOREMS.** A declaration whose TYPE mentions
`CommitSurface` is a `#floor_ratchet` `bundle-user` carrier and the gate hard-errors on any new one —
CORRECTLY, because the bundle's four injectivity fields are still refuted at DEPLOYED BabyBear width.
Naming these would be claiming a deployed object; they are reference-pole objects. This is the same
discipline `TurnDecodeChainLogBundleCutoverCheck` §1/§5 adopted, for the same reason. The build
elaborating them IS the check. -/

section Inhabitant

open Dregg2.Circuit.CircuitSoundness (CommitSurface StateDecode PublishedCommit
  stateDecode_pre_faithful)
open Dregg2.Circuit.FinBindsKernel (CH_fin CH_fin_injective finInit_accountsWF)
open Dregg2.Circuit.Freshness (spongeCompress spongeCompress_inj)
open Dregg2.Circuit.StateCommit (AccountsWF recStateCommit)
open Dregg2.Circuit.Poseidon2Binding (compressNInjective_of_poseidon2CR)
open Dregg2.Exec (RecChainedState)

/-- ★ **A CLOSED INHABITANT OF `CommitSurface`.** Every field is discharged; no hypothesis is
carried. `cmb`/`compress` are 2-element sponges over the reference sponge, `compressN` IS it, `CH` is
`CH_fin`, `RH` is `RH_fin` — and `restFrame` is `restHashIffFrameFin_satisfiable`, the field that had
no possible value before today.

⚠ **REFERENCE POLE, NOT DEPLOYED.** `Reference.refSponge` is `Encodable.encode`, which is genuinely
injective and genuinely NOT BabyBear-bounded. A BabyBear-bounded inhabitant is IMPOSSIBLE and always
was — `ApexPremiseVacuity.apexCommitFloorSansRest_false_at_babyBear` refutes the four injectivity
fields at deployed width by pigeonhole, independent of anything in this file. What changed is the
KIND of impossibility: from "no inhabitant at any parameter, by cardinality, unrepairable by
widening" to "no inhabitant at deployed width, by pigeonhole, repaired by the keyed-CR
advantage-bound campaign". -/
noncomputable example : CommitSurface where
  CH        := CH_fin Reference.refSponge
  RH        := RH_fin Reference.refSponge
  cmb       := spongeCompress Reference.refSponge
  compress  := spongeCompress Reference.refSponge
  compressN := Reference.refSponge
  cmbInj    := spongeCompress_inj Reference.refSponge Reference.refSponge_CR
  compInj   := spongeCompress_inj Reference.refSponge Reference.refSponge_CR
  compNInj  := compressNInjective_of_poseidon2CR Reference.refSponge_CR
  leafInj   := CH_fin_injective Reference.refSponge Reference.refSponge_CR
  restFrame := restHashIffFrameFin_satisfiable

/-- **★ UNIQUENESS FIRES, AND IT BITES.** Over the constructed surface, a forged pre-state that
claims the SAME published root as `denote finInit` is REFUSED. This is `stateDecode_pre_faithful`
applied at a real instance — the theorem that was unrefutable-and-vacuous yesterday, doing work.

The two `FiniteRepresentable` hypotheses are supplied honestly: `denote finInit` by construction,
the forgery by assumption (a forger who cannot produce a finitely-supported state is outside the
claim, which is exactly what §5b names as the remaining residual). Stated over an ARBITRARY
`S : CommitSurface` on purpose — the surface above is what makes that quantifier non-empty, and the
refusal itself needs no property of `S` beyond the bundle it already carries. -/
example (S : CommitSurface) (t : Turn) (forged : RecChainedState)
    (hwf : AccountsWF forged.kernel) (hfin : FiniteRepresentable forged.kernel)
    (hne : forged.kernel ≠ denote finInit)
    (hclaim : S.commit forged.kernel t = S.commit (denote finInit) t) : False := by
  have hdec₁ : StateDecode S ⟨S.commit (denote finInit) t, S.commit (denote finInit) t, t⟩
      ⟨denote finInit, []⟩ ⟨denote finInit, []⟩ :=
    ⟨rfl, rfl, finInit_accountsWF, finInit_accountsWF⟩
  have hdec₂ : StateDecode S ⟨S.commit (denote finInit) t, S.commit (denote finInit) t, t⟩
      forged forged :=
    ⟨hclaim.symm, hclaim.symm, hwf, hwf⟩
  exact hne (stateDecode_pre_faithful S _ (finiteRepresentable_of_denote finInit) hfin
    hdec₁ hdec₂).symm

/-! ### ⚑ THE `FiniteRepresentable` HYPOTHESES ARE LOAD-BEARING — the binding is FALSE without them.

A narrowed theorem whose narrowing does no work would be the same disease one level down. It does
work: at the constructed surface there are TWO DISTINCT `AccountsWF` kernels with the SAME root.
Both stamp every cell's `lifecycle` non-zero, so both are outside `FiniteRepresentable`
(`RestFrameFin.not_finiteRepresentable_of_lifecycle_ne_zero`), and `RH_fin` sends every non-image
state to `0` — so the rest-hash cannot separate them and the cell digests agree by construction. -/

/-- Every cell stamped `lifecycle = 1`; `accounts = ∅` and every cell the default, so `AccountsWF`. -/
def lifeAll : RecordKernelState where
  accounts  := ∅
  cell      := fun _ => default
  caps      := fun _ => []
  lifecycle := fun _ => 1

/-- The same, with cell `0` stamped `2` instead — DISTINCT from `lifeAll`, same `accounts`/`cell`. -/
def lifeAll' : RecordKernelState where
  accounts  := ∅
  cell      := fun _ => default
  caps      := fun _ => []
  lifecycle := fun c => if c = 0 then 2 else 1

theorem lifeAll_wf : AccountsWF lifeAll := fun _ _ => rfl
theorem lifeAll'_wf : AccountsWF lifeAll' := fun _ _ => rfl

theorem lifeAll_ne : lifeAll ≠ lifeAll' := by
  intro h
  have := congrFun (congrArg RecordKernelState.lifecycle h) 0
  simp [lifeAll, lifeAll'] at this

theorem lifeAll_not_finrep : ¬ FiniteRepresentable lifeAll :=
  not_finiteRepresentable_of_lifecycle_ne_zero lifeAll (fun c => by
    show (1 : Nat) ≠ 0
    decide)

theorem lifeAll'_not_finrep : ¬ FiniteRepresentable lifeAll' :=
  not_finiteRepresentable_of_lifecycle_ne_zero lifeAll' (fun c => by
    show (if c = 0 then 2 else 1) ≠ 0
    split <;> decide)

/-- Both states are off the `denote` image, so the reference rest-hash collapses them to `0`. -/
theorem RH_fin_lifeAll_eq :
    RH_fin Reference.refSponge lifeAll = RH_fin Reference.refSponge lifeAll' := by
  have h1 : ¬ ∃ f : FinKernelState, denote f = lifeAll := lifeAll_not_finrep
  have h2 : ¬ ∃ f : FinKernelState, denote f = lifeAll' := lifeAll'_not_finrep
  unfold RH_fin
  rw [dif_neg h1, dif_neg h2]

/-- **⚑ THE LOAD-BEARING TOOTH.** At the constructed surface's own primitives, two DISTINCT
`AccountsWF` kernels share a full-state root. So `recStateCommit_binds_kernel` / `commit_binds`
WITHOUT their `FiniteRepresentable` hypotheses would be FALSE — the narrowing is not decoration, and
the theorem it produced is not the old one with extra ink. -/
theorem finrep_load_bearing (t : Turn) :
    lifeAll ≠ lifeAll' ∧
      Dregg2.Circuit.StateCommit.recStateCommit (CH_fin Reference.refSponge)
          (RH_fin Reference.refSponge)
          (spongeCompress Reference.refSponge) (spongeCompress Reference.refSponge)
          Reference.refSponge lifeAll t
        = Dregg2.Circuit.StateCommit.recStateCommit (CH_fin Reference.refSponge)
          (RH_fin Reference.refSponge)
          (spongeCompress Reference.refSponge) (spongeCompress Reference.refSponge)
          Reference.refSponge lifeAll' t := by
  refine ⟨lifeAll_ne, ?_⟩
  show Dregg2.Circuit.StateCommit.recStateCommit _ _ _ _ _ _ _
     = Dregg2.Circuit.StateCommit.recStateCommit _ _ _ _ _ _ _
  unfold Dregg2.Circuit.StateCommit.recStateCommit
  rw [RH_fin_lifeAll_eq]
  rfl

end Inhabitant
#assert_axioms finFrame_of_full
#assert_axioms restHashIffFrameFin_satisfiable
#assert_axioms restHashIffFrameFin_fires
#assert_axioms restHashIffFrameFin_refutable
#assert_axioms restHashIffFrameFin_not_provable
#assert_axioms stateCircuit_rejects_field_tamper_fin
#assert_axioms lifeAll_not_finrep
#assert_axioms lifeAll'_not_finrep
#assert_axioms finrep_load_bearing

end Dregg2.Verify.RestFrameFiniteSupportSuccessor
