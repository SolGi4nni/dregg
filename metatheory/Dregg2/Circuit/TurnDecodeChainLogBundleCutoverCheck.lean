/-
# `Dregg2.Circuit.TurnDecodeChainLogBundleCutoverCheck` — the SEMANTIC TEETH of the intra-turn
receipt-log bundle cutover.

`CircuitSoundness.TurnDecodeChainLog` carried a REFUTED FLOOR as a FIELD — `hLog : logHashInjective
LH` — which made it UNINHABITABLE at deployed BabyBear parameters and every theorem over it VACUOUS.
`StateCommitFloorRegrounded.logHashInjective_false_babyBear` refutes injectivity for every receipt-chain
accumulator landing in one bounded felt: `List Turn` GROWS without bound and the digest is a single
field element, so pigeonhole forces a collision. A deployed prover could therefore never build the
bundle, and `turnDecodeChainLog_seam_log_derived` / `_seam_full_derived` / `_rejects_forged_log` — the
theorems that say the published turn-chain BINDS the intermediate receipt log, i.e. the dregg
through-line "a turn leaves a VERIFIABLE receipt" at the composition seam — said nothing about the
deployed system.

This is the shape the sibling bundle cutovers used (`Circuit/CapHashBundleCutoverCheck` on
`DeployedCapTree.CapHashScheme`), applied to the log seam. The design decision for the whole bundle
family — DELETE the floor field, never swap in a `noColl` FIELD (a field is fixed for the life of the
value and has no argument position, so it could only quantify over a set chosen in advance: empty and
carrying nothing, or non-trivial and uninhabitable again) — is recorded at `Dregg2.Shielded.RealCrypto`
§2.0. Consumers get the OPPOSITE treatment precisely because a theorem HAS arguments: the three carry
`NoLogSeamColl` at exactly the adjacencies the deleted field was fed.

* **§1 THE FIELD IS GONE, STRUCTURALLY** — the bundle is built from its DATA fields alone by an
  anonymous constructor, and the construction is TOTAL (every `hash`/`S`/`LH`/`c`, no emptiness
  hypothesis, no injectivity). A resurrected Prop field — the floor, OR a `noColl` field standing in
  for it — fails to elaborate here.
* **§2 THE CUTOVER TYPE PINS** — each cured theorem's type is pinned by KERNEL DEFEQ
  (`example : ⟨independently written type⟩ := @original`). A silent weakening, a dropped hypothesis or
  a floor resurrection goes RED.
* **§3 NOTHING WAS WEAKENED** — carried by the pre-existing grandfathered bridge
  `LogCommitRegrounded.noLogColl_of_inj` composed with the FLOOR-FREE lift
  `CircuitSoundness.noLogSeamColl_of_forall`. Mints NO new `…_of_injective` restatement: each would be
  a fresh declaration on a refuted floor, which is the accrual this campaign exists to stop.
* **§4 THE SIDE CONDITION IS LOAD-BEARING** — the per-adjacency step the ported theorems perform is
  FALSE without it, not merely unproved, and the equivocation event is REACHABLE at a degenerate
  accumulator.
* **§5 THE ACCEPTANCE TEST** — the bundle is INHABITED at `deployedTurnLogHash`, a BabyBear-reduced
  receipt-chain accumulator whose `logHashInjective` this module REFUTES. A green build proves nothing
  here; the inhabitant does.
* **§6 THE FLOOR IS UNREACHABLE** — `#assert_not_depends_on` on the bundle and all three cured
  theorems, with an `#assert_depends_on` POSITIVE CONTROL on §3's bridge so the rejectors are not
  vacuous.
* **§7 THE NAMED RESIDUAL** — what this cutover does NOT close, stated at its own resolution rather
  than left for the next reader to discover.

No `sorry`, no `axiom`, no `native_decide`.
-/
import Dregg2.Circuit.CircuitSoundness
import Dregg2.Circuit.StateCommitFloorRegrounded
import Dregg2.Circuit.RestFrameCardinalityFloor
import Dregg2.Tactics

namespace Dregg2.Circuit.TurnDecodeChainLogBundleCutoverCheck

open Dregg2.Exec (Turn RecChainedState)
open Dregg2.Circuit.StateCommit (logHashInjective)
open Dregg2.Circuit.LogCommitRegrounded (LogColl)
open Dregg2.Circuit.CircuitSoundness
  (CommitSurface DecodedStep TurnDecodeChain TurnDecodeChainLog NoLogSeamColl
   turnDecodeChainLog_seam_log_derived turnDecodeChainLog_seam_full_derived
   turnDecodeChainLog_rejects_forged_log)

set_option autoImplicit false

/-! ## §1 — THE FIELD IS GONE, STRUCTURALLY, AND THE BUNDLE IS INHABITED TOTALLY.

The bundle is constructed from its four DATA fields alone by an anonymous constructor: if any Prop
field came back — the refuted floor, or a `noColl` field standing in for it — the arity would change
and this would no longer elaborate.

And the construction is TOTAL: it inhabits the bundle for EVERY `hash`, `S`, `LH` and decoded chain
`c` — no emptiness hypothesis, no injectivity, no restriction on the accumulator. It IS the honest
prover's chained-root: publish the true log digest at each boundary (`logPubPre d = LH d.pre.log`,
`logPubPost d = LH d.post.log`), whereupon each step's `LogDecode` holds by `rfl` and the published log
seam is the chain's own threaded `seam` pushed through `LH`. That an honest prover can always produce
this datum is exactly what `hLog : logHashInjective LH` made impossible at deployed width. -/

/-- ⚑ **THE INHABITANT — the honest prover's log column, at an ARBITRARY accumulator.**

⚑ **WHY AN `example` AND NOT A `def`** — the honest cost, stated rather than hidden. Any NAMED
declaration of this type is a `bundle-user` of `S : CommitSurface`, which still carries FOUR refuted
floors as FIELDS, so `#floor_ratchet` gates it. MEASURED: it did, on the first attempt at this cutover
(`bundle-user`, `floor: CircuitSoundness.CommitSurface`), and it was RIGHT to — a named inhabitant
would have been a NEW declaration that is still vacuous through the OTHER bundle. Grandfathering it
would have been a baseline RAISE taken in order to record a win, which is precisely the accrual the
gate exists to stop. So the construction is elaborated and kernel-checked here and stays unnamed until
`CommitSurface` is drained; that residual is §7. -/
example (hash : List ℤ → ℤ) (S : CommitSurface) (LH : List Turn → ℤ)
    {start fin : RecChainedState} (c : TurnDecodeChain hash S start fin) :
    TurnDecodeChainLog hash S LH c :=
  ⟨ fun d => LH d.pre.log
  , fun d => LH d.post.log
  , fun _ _ => ⟨rfl, rfl⟩
  , List.IsChain.imp (fun _ _ h => congrArg (fun s : RecChainedState => LH s.log) h) c.seam ⟩

/-! ## §2 — THE CUTOVER TYPE PINS (kernel defeq, re-proved every build). -/

/-- ⚙ CUTOVER CHECK — `turnDecodeChainLog_seam_log_derived`: same conclusion (the per-adjacency log
continuity of the decoded chain), the `hLog` field replaced by a PER-INSTANCE `NoLogSeamColl` at
exactly the adjacencies the deleted field was fed. -/
example :
    ∀ (hash : List ℤ → ℤ) (S : CommitSurface) (LH : List Turn → ℤ)
      (start fin : RecChainedState) (c : TurnDecodeChain hash S start fin),
      TurnDecodeChainLog hash S LH c →
      NoLogSeamColl LH (fun d : DecodedStep S => d.post.log)
        (fun d : DecodedStep S => d.pre.log) c.steps →
      List.IsChain (fun a b => a.post.log = b.pre.log) c.steps :=
  @turnDecodeChainLog_seam_log_derived

/-- ⚙ CUTOVER CHECK — `turnDecodeChainLog_seam_full_derived`: the FULL-state seam (kernel ⊕ log) over
the same per-instance condition. -/
example :
    ∀ (hash : List ℤ → ℤ) (S : CommitSurface) (LH : List Turn → ℤ)
      (start fin : RecChainedState) (c : TurnDecodeChain hash S start fin),
      TurnDecodeChainLog hash S LH c →
      NoLogSeamColl LH (fun d : DecodedStep S => d.post.log)
        (fun d : DecodedStep S => d.pre.log) c.steps →
      List.IsChain (fun a b => a.post = b.pre) c.steps :=
  @turnDecodeChainLog_seam_full_derived

/-- ⚙ CUTOVER CHECK — `turnDecodeChainLog_rejects_forged_log`: the forged-intermediate-log rejection,
same `False` conclusion, same forge premise, the floor field replaced by the per-instance condition. -/
example :
    ∀ (hash : List ℤ → ℤ) (S : CommitSurface) (LH : List Turn → ℤ)
      (start fin : RecChainedState) (c : TurnDecodeChain hash S start fin),
      TurnDecodeChainLog hash S LH c →
      NoLogSeamColl LH (fun d : DecodedStep S => d.post.log)
        (fun d : DecodedStep S => d.pre.log) c.steps →
      ∀ (i : Nat) (hi : i + 1 < c.steps.length),
        (c.steps[i]'(by omega)).post.log ≠ (c.steps[i+1]'hi).pre.log → False :=
  @turnDecodeChainLog_rejects_forged_log

/-! ## §3 — NOTHING WAS WEAKENED — and the proof of that costs ZERO new floor carriers.

The old bundle carried the floor as a field, so the old theorems' content is exactly "…given that
field". The machine-checked statement that nothing was lost is therefore the composition

    CircuitSoundness.noLogSeamColl_of_forall (fun _ _ => LogCommitRegrounded.noLogColl_of_inj hLog)
      : NoLogSeamColl LH postLog preLog steps

— the deleted field's own type IMPLIES the new side condition at EVERY pair, hence at every adjacency
of every chain. Drop it into the `hno` slot of any of the three and each recovers its verbatim
pre-cutover statement. `noLogColl_of_inj` ALREADY EXISTS in the tree (minted for the endpoint cutover),
it is grandfathered in `FloorRatchetBaseline`, and `noLogSeamColl_of_forall` — the one step from "at
every pair" to "at every adjacency" — carries NO floor hypothesis at all, so the whole recovery route
adds not one carrier.

⚑ WHY THIS SECTION MINTS NOTHING FURTHER. A per-theorem `…_of_injective` restatement would be a new
declaration whose type takes a hypothesis this tree PROVES FALSE at deployed BabyBear parameters — a
new VACUOUS declaration, precisely the accrual `#floor_ratchet` was built to stop, and a
vacuity-removal lane does not get to be the thing it is removing. HONEST COST, stated rather than
hidden: the three one-step compositions are not themselves elaborated anywhere, so this section is a
pointer plus an argument; §6's positive control pins that the bridge it points at genuinely reaches
the floor. -/

/-! ## §4 — THE SIDE CONDITION IS LOAD-BEARING (dropping it is FALSE, not merely unproved).

At each adjacency the ported theorems perform exactly one step: from `LH a.post.log = LH b.pre.log`
conclude `a.post.log = b.pre.log`. With the per-instance hypothesis DELETED that step is refuted. -/

/-- The degenerate accumulator: every receipt chain to one digest — the pole the 8-felt rule in
`LogCommitRegrounded`'s header names as a BREAK. -/
def constTurnLogHash : List Turn → ℤ := fun _ => 0

/-- A receipt row. -/
def tA : Turn := { actor := 0, src := 0, dst := 1, amt := 1 }

/-- Its sibling, differing only in `dst`. -/
def tB : Turn := { actor := 0, src := 0, dst := 2, amt := 1 }

/-- The two one-row receipt chains are DISTINCT — read off the `dst` field. (`Turn`'s `DecidableEq`
instance is tactic-built, so `decide` cannot reduce it; the field projection is the honest route.) -/
theorem chain_ne : ([tA] : List Turn) ≠ [tB] := by
  intro h
  have h1 : tA = tB := by simpa using h
  exact absurd (congrArg Turn.dst h1) (by simp [tA, tB])

/-- ⚑ The equivocation event is REACHABLE: at the degenerate accumulator the two distinct chains ARE a
`LogColl`. So `NoLogSeamColl` is a claim a bad instantiation genuinely violates — a hypothesis, not a
hedge. -/
theorem logColl_reachable : LogColl constTurnLogHash [tA] [tB] :=
  ⟨chain_ne, rfl⟩

/-- ⚑ Dropping the side condition would be FALSE: the per-adjacency step the three theorems perform,
stated unconditionally, is refuted at the degenerate accumulator. A "port" that dropped `hno` would not
be a port; it would be refuted here. This is the mutation canary for the bundle. -/
theorem seamStep_unconditional_false :
    ¬ (∀ xs ys : List Turn, constTurnLogHash xs = constTurnLogHash ys → xs = ys) := by
  intro hall
  exact absurd (hall [tA] [tB] rfl) chain_ne

/-! ## §5 — ⚑ THE ACCEPTANCE TEST: the bundle is INHABITED at an accumulator whose own carriers
REFUTE the deleted field.

This is the whole point. Before the cutover no `TurnDecodeChainLog` value existed at ANY deployed
accumulator, so the three theorems' `∀ cl : TurnDecodeChainLog …` surface was vacuous there. -/

/-- **A deployed-width receipt-chain accumulator**: a positional Horner fold over the receipt rows,
REDUCED into the BabyBear field — which is what every real Poseidon2 log hash does. The reduction is
the whole of the deployment fact that matters here: the digest is ONE bounded felt while the chain
grows without bound. -/
def deployedTurnLogHash (xs : List Turn) : ℤ :=
  (xs.foldl (fun acc t => acc * 31 + (t.actor : ℤ) * 7 + (t.src : ℤ) * 5 + (t.dst : ℤ) * 3 + t.amt)
    (xs.length : ℤ)) % 2013265921

/-- The deployed accumulator lands in the BabyBear window, by construction. -/
theorem deployedTurnLogHash_bounded :
    ∀ xs : List Turn, 0 ≤ deployedTurnLogHash xs ∧ deployedTurnLogHash xs < (2013265921 : ℤ) := by
  intro xs
  unfold deployedTurnLogHash
  exact ⟨Int.emod_nonneg _ (by norm_num), Int.emod_lt_of_pos _ (by norm_num)⟩

/-- ⚑ **THE REFUTATION TOOTH — the inhabitant's own accumulator REFUTES the deleted field.** Had
`hLog : logHashInjective LH` survived, the §5 inhabitant below could not have been built: the field's
type is FALSE at every BabyBear-bounded receipt-chain accumulator, so the bundle was uninhabitable at
deployed parameters and its whole `∀ cl`-surface vacuous there. The very function this tooth refutes
now INHABITS the structure. -/
theorem deployedTurnLogHash_not_logHashInjective : ¬ logHashInjective deployedTurnLogHash :=
  Dregg2.Circuit.StateCommitFloorRegrounded.logHashInjective_false_babyBear _
    deployedTurnLogHash_bounded

/-- ⚑ **THE INHABITANT AT DEPLOYED PARAMETERS** — the honest prover's chained-root over the
BabyBear-reduced accumulator the tooth above REFUTES. Unnamed for the reason given in §1. -/
example (hash : List ℤ → ℤ) (S : CommitSurface) {start fin : RecChainedState}
    (c : TurnDecodeChain hash S start fin) :
    TurnDecodeChainLog hash S deployedTurnLogHash c :=
  ⟨ fun d => deployedTurnLogHash d.pre.log
  , fun d => deployedTurnLogHash d.post.log
  , fun _ _ => ⟨rfl, rfl⟩
  , List.IsChain.imp
      (fun _ _ h => congrArg (fun s : RecChainedState => deployedTurnLogHash s.log) h) c.seam ⟩

/-- ⚑ THE TOOTH FIRES AT THE INHABITANT — the log-seam derivation, INSTANTIATED at the deployed
accumulator and the honest chained-root. This is the operation the pre-cutover `∀ cl :
TurnDecodeChainLog …` form could never actually be performed for at any deployed `LH`. -/
example (hash : List ℤ → ℤ) (S : CommitSurface) {start fin : RecChainedState}
    (c : TurnDecodeChain hash S start fin)
    (hno : NoLogSeamColl deployedTurnLogHash (fun d : DecodedStep S => d.post.log)
      (fun d : DecodedStep S => d.pre.log) c.steps) :
    List.IsChain (fun a b => a.post.log = b.pre.log) c.steps :=
  turnDecodeChainLog_seam_log_derived hash S deployedTurnLogHash
    ⟨ fun d => deployedTurnLogHash d.pre.log
    , fun d => deployedTurnLogHash d.post.log
    , fun _ _ => ⟨rfl, rfl⟩
    , List.IsChain.imp
        (fun _ _ h => congrArg (fun s : RecChainedState => deployedTurnLogHash s.log) h) c.seam ⟩
    hno

/-! ## §6 — THE FLOOR IS UNREACHABLE from the bundle and from the cured theorems. -/

#assert_axioms deployedTurnLogHash_not_logHashInjective
#assert_axioms seamStep_unconditional_false
#assert_axioms logColl_reachable

#assert_not_depends_on Dregg2.Circuit.CircuitSoundness.TurnDecodeChainLog
  [Dregg2.Circuit.StateCommit.logHashInjective]
#assert_not_depends_on Dregg2.Circuit.CircuitSoundness.NoLogSeamColl
  [Dregg2.Circuit.StateCommit.logHashInjective]
#assert_not_depends_on Dregg2.Circuit.CircuitSoundness.turnDecodeChainLog_seam_log_derived
  [Dregg2.Circuit.StateCommit.logHashInjective]
#assert_not_depends_on Dregg2.Circuit.CircuitSoundness.turnDecodeChainLog_seam_full_derived
  [Dregg2.Circuit.StateCommit.logHashInjective]
#assert_not_depends_on Dregg2.Circuit.CircuitSoundness.turnDecodeChainLog_rejects_forged_log
  [Dregg2.Circuit.StateCommit.logHashInjective]

/-! POSITIVE CONTROL for the five rejectors above: a rejector alone cannot detect its own blindness,
so pin that the grandfathered bridge §3 routes the recovery through DOES reach the floor. If the walk
ever stops seeing proof terms this line reds while the rejectors would silently pass. -/
#assert_depends_on Dregg2.Circuit.LogCommitRegrounded.noLogColl_of_inj
  [Dregg2.Circuit.StateCommit.logHashInjective]

/-! ## §7 — ⚑ THE NAMED RESIDUAL: what this cutover does NOT close.

Stated here rather than left for the next reader to rediscover, because the gate's output already
proves it and a silent residual is how a "drained" bundle stays vacuous through a different floor.

1. **`CircuitSoundness.CommitSurface` is the remaining obstruction, and it is BIGGER than it looks.**
   Every `TurnDecodeChainLog` mentions `S : CommitSurface`, which carries four refuted floors as
   FIELDS (`cmbInj`/`compInj : compressInjective`, `compNInj : compressNInjective`, `leafInj :
   cellLeafInjective`). So a NAMED inhabitant of the log bundle is still a `bundle-user` carrier —
   `#floor_ratchet` says so, which is why §1 and §5 elaborate their inhabitants as `example`s. What
   this cutover bought is exact and it is not nothing: the LOG dimension no longer forces an
   impossible claim, the three seam theorems are out of `logHashInjective`'s proof closure, and the
   bundle's own data is realizable by an honest prover at any accumulator.

2. **Draining `CommitSurface`'s four gated floors would NOT by itself re-inhabit it — and that is now
   a THEOREM, not a caution.** Its FIFTH field `restFrame : RestHashIffFrame RH` is invisible to BOTH
   instruments, and `RestFrameCardinalityFloor.restHashIffFrame_false_by_cardinality` proves it FALSE
   for EVERY `RH : RecordKernelState → ℤ` at EVERY width — by Cantor, because two of the components
   the rest-hash must separate are FUNCTION SPACES (`bal : CellId → AssetId → ℤ`,
   `Caps = Label → List Cap`, all three indices `ℕ`), so the domain has size at least `2 ^ ℵ₀` while
   `ℤ` is countable. That is STRICTLY stronger than every gated floor in the campaign, which are false
   only at deployed BabyBear width; widening the digest — the repair for the CR floors — does nothing
   here, and there is no instance to be per-instance at. The `example` below discharges the
   consequence: `CommitSurface` has NO inhabitant, so this cutover's `∀ S`-quantified inhabitants are
   still vacuous through `S`, exactly as §1 says. Anyone porting `CommitSurface` must shed `restFrame`
   in the SAME pass as the four; the structural repair is the one that class always wants and
   `Verify/InjSpelledFloors` already names — digest the FINITE support actually touched (the
   `accounts : Finset CellId` rows), never the whole function. -/

/-- ⚑ **`CommitSurface` HAS NO INHABITANT AT ALL** — one application of the cardinality refutation to
the surface's own `restFrame` field. So the residual named above is not a suspicion: every theorem in
this tree quantified over a `CommitSurface` is vacuous today, and the `∀ S`-shaped inhabitants of §1
and §5 are honest about exactly that. Unnamed for the same reason as those: a NAMED declaration whose
type mentions `CommitSurface` is a `bundle-user` carrier and `#floor_ratchet` gates it. -/
example (S : CommitSurface) : False :=
  Dregg2.Circuit.RestFrameCardinalityFloor.restHashIffFrame_false_by_cardinality S.RH S.restFrame

/-! (end §7) -/

end Dregg2.Circuit.TurnDecodeChainLogBundleCutoverCheck
