/-
# free_conclusion_canary.lean — THE FREE-CONCLUSION GATE, CAUGHT IN THE ACT OF BITING.

A gate that has never been seen to fail is not a gate; it is a green light with no bulb. This file
is a DELIBERATE VIOLATION, and it is deliberately built to pass EVERY instrument that already
exists, so that the one new red is attributable.

    cd metatheory && lake env lean scripts/free_conclusion_canary.lean

**EXPECTED: EXIT=1**, with `⚑ FREE-CONCLUSION RATCHET: 2 registered keystone(s) …` naming
`free_conclusion_canary_violation_KS` and `free_conclusion_canary_bare_violation_KS`, and naming
NEITHER `control_free_conclusion_canary_ported_KS` NOR
`control_free_conclusion_canary_refutation_KS`. A ZERO exit means the gate has gone blind and every
guarantee in `Dregg2/Verify/FreeConclusionRatchet.lean` is void; naming only ONE violation means
one of the two rules has, which reads identically to a healthy run if you only check the exit code.

## What each half of this file is for

**§2 — THE VIOLATION.** A theorem whose conclusion is `OrBreak (SpongeCollision hash) (xs = ys)`,
registered as a `@[load_bearing_keystone]` with a REAL satisfiability witness and REAL teeth. Its
proof term is the confession: it is `OrBreak.broke (spongeCollision_of_fieldBounded hb)` — the good
branch is never touched, because at a field-bounded sponge it does not have to be. This is the exact
shape of `HistoryAggregation.verified_history_conserves_orBreak` and
`RecursiveAggregation.conserves_from_verification_orBreak`, both of which were REGISTERED KEYSTONES,
one of them documented as "the headline CRITICAL-3 closure".

**§3 — `#keystone_audit` PASSES IT, AND THAT IS THE POINT.** The canary runs the OLD lint on the
violation first and it reports PASS. Not because the companions are fake — they are genuine and
axiom-clean — but because neither of its two checks is about the conclusion's information content.
That is the gap this gate closes, demonstrated in-band rather than asserted in a docstring.

**§4 — THE CONTROL.** The same claim, PORTED: a per-instance residual `SpongeColl hash xs ys` at the
NAMED pair, also registered as a keystone. The gate must NOT name it. Without this half the canary
would pass for the wrong reason — a classifier that flags every disjunction reds here too, and reds
the whole campaign's repair with it.

**§2b — THE BARE PAIR (2026-08-02).** The same demonstration for the rule that closed the
bare-conclusion blind spot, and it is a PAIR because the two declarations are indistinguishable by
their conclusions: `free_conclusion_canary_bare_violation_KS` (`SpongeColl … → SpongeCollision hash`,
a bridge that loses the pair) must be named, and `control_free_conclusion_canary_refutation_KS`
(`FieldBounded hash → SpongeCollision hash`, the pigeonhole refutation that ARMS the gate) must not
— though both are registered keystones and both conclude the same free event.

**§2c — THE BARE RULE'S OWN INVERSION.** §2b shows the rule bites; §2c shows it cannot be disarmed
quietly, by handing `selfTest` a witness set with every bare pattern stripped and requiring it to
REFUSE. A derived rule that derives nothing flags nothing and looks exactly like a clean tree.

## Why a standalone file, and not a temporary edit to the tree

Both reasons are the ones `scripts/floor_ratchet_canary.lean` records, and both still hold.

1. **It is swarm-safe.** Nothing here touches a tracked module, so the canary is safe to run at any
   time, concurrently, by anyone. Injecting a violation by editing a module and reverting is a
   mutation of a tree several agents share.

2. **It exercises the subtle half of the gate.** The violating declaration elaborates in THIS file,
   so it has no module index in the environment. `FreeConclusionRatchet.deriveWitnesses` deliberately
   counts an index-less constant as OURS (the same decision `FloorRatchet.ourNames` makes and for the
   same reason), and `keystoneExt` picks up an attribute applied here exactly as it picks up one
   applied in a module. A gate that could not see the file it is standing in would go green here.

## The import list, and what it is NOT

The `KeystoneAudit*` imports below exist ONLY to clear the gate's fail-closed scale bar
(`FreeConclusionRatchet.minKeystones`): a check that runs against a fraction of the corpus reports a
low number, which is indistinguishable from a clean tree, so it refuses instead. CORPUS COVERAGE is
not this file's job — it belongs to `Dregg2/Verify/FreeConclusionGate.lean` and to the invocation in
the root, both of which import every audit module there is.

⚠ Three audit modules (`KeystoneAuditSystemRoots`, `KeystoneAuditArgusReceipt`,
`KeystoneAuditTerminalAdapters`, 7 keystones between them) are NOT listed, and not because they were
chosen away: they are unbuildable at HEAD today through `Dregg2/Circuit/CircuitCompletenessNonVacuityReal.lean`,
which fails a `rfl` at :421 and leaks `sorryAx` into four declarations. That red is unmodified in the
working tree, predates this work, and has nothing to do with this gate. When it clears, add them here.
-/
import Dregg2.Verify.FreeConclusionRatchet
import Dregg2.Verify.FreeConclusionSpecimens
import Dregg2.Circuit.SpongeCollisionShirk
import Dregg2.Circuit.StateCommitReduceRaw
import Dregg2.Circuit.CircuitSoundness
import Dregg2.Verify.KeystoneAuditNonAmp
import Dregg2.Verify.KeystoneAuditAuthModes
import Dregg2.Verify.KeystoneAuditIntegrity
import Dregg2.Verify.KeystoneAuditFreshness
import Dregg2.Verify.KeystoneAuditUnfoolability
import Dregg2.Verify.KeystoneAuditSupply
import Dregg2.Verify.KeystoneAuditConservation
import Dregg2.Verify.KeystoneAuditTransport
import Dregg2.Verify.KeystoneAuditRunnable

open Dregg2.Circuit.CollisionReduce (SpongeCollision OrBreak)
open Dregg2.Circuit.SpongeCollisionShirk
  (FieldBounded SpongeColl spongeCollision_of_fieldBounded headHash headHash_fieldBounded list01_ne)

/-! ## §2 — THE VIOLATION. -/

/-- **THE VIOLATION.** A perfectly true, perfectly USELESS theorem: its conclusion is a disjunction
whose break branch `SpongeCollisionShirk.spongeCollision_of_fieldBounded` supplies at every
deployed-shaped sponge, so the dichotomy is literally `True`
(`orBreak_spongeCollision_iff_True`) and the good branch `xs = ys` is unreachable from the
statement. The proof term says so: `OrBreak.broke` never looks at the good branch. -/
theorem free_conclusion_canary_violation
    (hash : List ℤ → ℤ) (hb : FieldBounded hash) (xs ys : List ℤ)
    (_h : hash xs = hash ys) :
    OrBreak (SpongeCollision hash) (xs = ys) :=
  OrBreak.broke (spongeCollision_of_fieldBounded hb)

/-- A GENUINE satisfiability witness: the hypotheses hold at a concrete deployed-shaped sponge and
the conclusion fires there. Nothing fake about it, which is exactly why `#keystone_audit` passes. -/
theorem free_conclusion_canary_violation_satisfiable :
    OrBreak (SpongeCollision headHash) (([0] : List ℤ) = [0]) :=
  free_conclusion_canary_violation headHash headHash_fieldBounded [0] [0] rfl

/-- GENUINE teeth: a hostile instance really is refuted, unconditionally and axiom-cleanly.

⚑ Note what the teeth are ABOUT. `#keystone_audit`'s CHECK 2 verifies that a named companion exists
and is axiom-clean; it never checks that the companion refutes THE KEYSTONE'S OWN conclusion — and
it could not, since at a field-bounded sponge that conclusion is `True` and has no refutation. So a
free-disjunct keystone can always be fitted with real teeth pointing somewhere else. That is not a
hypothetical: `KeystoneAuditUnfoolability` (7) carried `tooth_rejects_broken_order`, which concludes
`¬ ChainBound` — a different predicate entirely — and passed. -/
theorem free_conclusion_canary_violation_teeth :
    ¬ (∀ (hash : List ℤ → ℤ) (xs ys : List ℤ), hash xs = hash ys → xs = ys) :=
  fun h => list01_ne (h (fun _ => (0 : ℤ)) [0] [1] rfl)

@[load_bearing_keystone
    satisfiable := free_conclusion_canary_violation_satisfiable
    teeth := free_conclusion_canary_violation_teeth]
def free_conclusion_canary_violation_KS := @free_conclusion_canary_violation

/-! ## §2b — THE BARE VIOLATION, AND ITS TWIN THAT MUST STAY CLEAN.

⚑ **THE PAIR THIS HALF EXISTS FOR.** `free_conclusion_canary_bare_violation` and
`control_free_conclusion_canary_refutation` have the SAME SHAPE — `∀ …, Hyp → SpongeCollision hash`,
no disjunction anywhere — and the SAME conclusion, at the same free break event. One must be named
by the gate and the other must not, and no rule keyed on the shape of the conclusion can tell them
apart. That is why the bare rule is keyed on the HYPOTHESIS instead: `hb : FieldBounded hash` is
what the freeness proof itself carries, `hc : SpongeColl hash xs ys` is not.

Until 2026-08-02 the gate read BOTH of these clean — `#free_conclusion_probe
Dregg2.Circuit.CommitFaithfulRegrounded.stateBreak_faithful_reduces` came back "no free disjunct
found" though its conclusion is proved free ten lines above it in its own file — and the limit was
written up as possibly terminal. It was not. -/

/-- **THE BARE VIOLATION.** Its conclusion IS the free break event, undisjoined: this is the
`_toGlobal` / `_toSponge` shape the tree really contains
(`Distributed.HistoryAggregation.ChainLogColl.toSponge`,
`Circuit.CommitFaithfulRegrounded.stateBreak_faithful_reduces`). The proof term is the confession
again — `hc` is never looked at, because at a field-bounded sponge it does not have to be. -/
theorem free_conclusion_canary_bare_violation
    (hash : List ℤ → ℤ) (hb : FieldBounded hash) (xs ys : List ℤ)
    (_hc : SpongeColl hash xs ys) :
    SpongeCollision hash :=
  spongeCollision_of_fieldBounded hb

/-- `fun _ => 0` is field-bounded, and it is the sponge both bare companions are stated at. -/
theorem canary_zeroHash_fieldBounded : FieldBounded (fun _ => (0 : ℤ)) :=
  fun _ => ⟨le_refl 0, by norm_num⟩

/-- A GENUINE satisfiability witness for the bare violation: both hypotheses hold at a concrete
sponge (`SpongeColl (fun _ => 0) [0] [1]` is `SpongeCollisionShirk.spongeColl_refutable`) and the
conclusion fires there. -/
theorem free_conclusion_canary_bare_violation_satisfiable :
    SpongeCollision (fun _ => (0 : ℤ)) :=
  free_conclusion_canary_bare_violation (fun _ => (0 : ℤ)) canary_zeroHash_fieldBounded [0] [1]
    ⟨list01_ne, rfl⟩

/-- GENUINE teeth, and pointing somewhere else — exactly as §2's do, for the same reason: at a
field-bounded sponge the bare conclusion is `True` and has no refutation to point at. -/
theorem free_conclusion_canary_bare_violation_teeth :
    ¬ SpongeColl headHash [0] [1] :=
  Dregg2.Circuit.SpongeCollisionShirk.noSpongeColl_satisfiable

@[load_bearing_keystone
    satisfiable := free_conclusion_canary_bare_violation_satisfiable
    teeth := free_conclusion_canary_bare_violation_teeth]
def free_conclusion_canary_bare_violation_KS := @free_conclusion_canary_bare_violation

/-- **THE REFUTATION CONTROL — the pigeonhole fact, REGISTERED AS A KEYSTONE.** Same conclusion as
the bare violation, same absence of a disjunction; its only `Prop` hypothesis is the one the
freeness proof needs. The gate must NOT name it. A bare rule that did would make writing the
refutation a build error — and the refutation is what ARMS this gate, so the gate would be
disarming itself. Registered as a keystone deliberately: "it is not tagged" is not the reason it is
clean, and pinning it here means the exemption is exercised in the corpus the gate actually
scans. -/
theorem control_free_conclusion_canary_refutation
    (hash : List ℤ → ℤ) (hb : FieldBounded hash) :
    SpongeCollision hash :=
  spongeCollision_of_fieldBounded hb

/-- The refutation control's satisfiability witness. -/
theorem control_free_conclusion_canary_refutation_satisfiable :
    SpongeCollision (fun _ => (0 : ℤ)) :=
  control_free_conclusion_canary_refutation (fun _ => (0 : ℤ)) canary_zeroHash_fieldBounded

/-- The refutation control's teeth, and note WHAT they are about: the HYPOTHESIS. `FieldBounded` is
two-valued — a function whose outputs leave the BabyBear range is refused — so this keystone's
premise is a real condition on the sponge rather than something every function satisfies. That is
also the whole content of the exemption the gate grants this declaration: the hypothesis is the one
doing the work, which is exactly what the bare violation's `hc` provably is not. -/
theorem control_free_conclusion_canary_refutation_teeth :
    ¬ FieldBounded (fun _ => (-1 : ℤ)) := by
  intro h
  have h0 := (h []).1
  norm_num at h0

@[load_bearing_keystone
    satisfiable := control_free_conclusion_canary_refutation_satisfiable
    teeth := control_free_conclusion_canary_refutation_teeth]
def control_free_conclusion_canary_refutation_KS := @control_free_conclusion_canary_refutation

/-! ## §2c — THE BARE RULE'S OWN INVERSION, IN BAND.

§2b proves the bare rule BITES. This proves it CANNOT BE DISARMED QUIETLY, which is the other half
and the one that is invisible from a green build: the bare pattern is DERIVED (`barePatternOf` reads
`?P ∨ B` off a freeness witness and hands back `B`), so any edit to that derivation — a spelling
change in a break event, a reducibility change under `whnfR`, a stricter guard — can stop producing
it, and a rule that produces no patterns flags nothing and looks exactly like a clean tree.

So the derivation is checked against a DELIBERATELY DISARMED witness set here: `selfTest` must
REFUSE it, and refuse it with the bare-pattern message rather than incidentally. This is the same
discipline as the canary itself, one level down — the fail-closed check gets its own canary. -/

open Lean Elab Command Meta Dregg2.Verify.FreeConclusionRatchet in
run_cmd liftTermElabM do
  let ws ← deriveWitnesses
  let disarmed := ws.map (fun w => { w with bareHeads := #[] })
  let bite ←
    try
      selfTest disarmed
      pure none
    catch e => pure (some (← e.toMessageData.toString))
  match bite with
  | none =>
    throwError "BARE-RULE DISARM CONTROL FAILED: `selfTest` ACCEPTED a witness set with every bare \
      pattern stripped. `bareSentinelWitnesses` is supposed to make that a hard error — with it \
      broken, deleting the bare rule's derivation would leave every gate in this repo green and \
      every `_toGlobal` keystone unscanned."
  | some msg =>
    if (msg.splitOn "no longer arms a BARE pattern").length ≤ 1 then
      throwError "BARE-RULE DISARM CONTROL FAILED: `selfTest` refused the disarmed witness set, but \
        for some OTHER reason:\n{msg}\nThe bare-pattern sentinel check did not fire, so it is not \
        what is holding the rule in place and it would not notice the rule going dark."
    else
      logInfo "bare-rule disarm control: BITES (a witness set with no bare patterns is REFUSED by \
        `bareSentinelWitnesses`, with the bare-pattern message)."

/-! ## §4 — THE CONTROL: the same claim, PORTED. The gate must NOT name this one. -/

/-- **THE CONTROL.** The landed repair shape: the residual is `SpongeColl hash xs ys`, a collision
AT THE NAMED PAIR, so pigeonhole does not supply it and no `_iff_True` witness for it exists.
Structurally this is the same `∨` with the same symbols; it is the OTHER one. If the gate reds here
too, it is flagging the campaign's own repair and porting has become a build error. -/
theorem control_free_conclusion_canary_ported
    (hash : List ℤ → ℤ) (xs ys : List ℤ) (h : hash xs = hash ys) :
    xs = ys ∨ SpongeColl hash xs ys := by
  by_cases hne : xs = ys
  · exact Or.inl hne
  · exact Or.inr ⟨hne, h⟩

/-- The control's satisfiability witness: it fires at a real pair of a real deployed-shaped sponge,
through the GOOD branch (`headHash [0] = headHash [0]`, so `xs = ys` genuinely holds). -/
theorem control_free_conclusion_canary_ported_satisfiable :
    ([0] : List ℤ) = [0] ∨ SpongeColl headHash [0] [0] :=
  control_free_conclusion_canary_ported headHash [0] [0] rfl

/-- The control's teeth, and they are teeth the free form provably cannot have: the residual really
FIRES at a broken hash (`SpongeColl (fun _ => 0) [0] [1]`), so it is two-valued rather than
`True` — `SpongeCollisionShirk.noSpongeColl_satisfiable` is the other pole, at `headHash`. -/
theorem control_free_conclusion_canary_ported_teeth : SpongeColl (fun _ => (0 : ℤ)) [0] [1] :=
  ⟨list01_ne, rfl⟩

@[load_bearing_keystone
    satisfiable := control_free_conclusion_canary_ported_satisfiable
    teeth := control_free_conclusion_canary_ported_teeth]
def control_free_conclusion_canary_ported_KS := @control_free_conclusion_canary_ported

/-! ## §3 — THE OLD LINT, RUN ON ALL FOUR. Every one must PASS: that is the gap, in the act.

`#keystone_audit` THROWS on failure, so a red here would mean the canary's companions are not
genuine and the demonstration is worthless. All four are expected to log PASS — including the BARE
violation, which carries a real satisfiability witness and real teeth and is still worth nothing. -/

#keystone_audit free_conclusion_canary_violation_KS
#keystone_audit control_free_conclusion_canary_ported_KS
#keystone_audit free_conclusion_canary_bare_violation_KS
#keystone_audit control_free_conclusion_canary_refutation_KS

/-! ## §5 — THE NEW GATE. EXPECTED: THROW, naming BOTH violations and NEITHER control. -/

#free_conclusion_ratchet
