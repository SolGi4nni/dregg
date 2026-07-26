/-
# Dregg2.Circuit.LogCommitCutoverCheck — the SEMANTIC teeth of the `logHashInjective` cutover.

The `logHashInjective` endpoints were cut over IN PLACE (same names, same conclusions, the refuted
∀-injectivity binder replaced by a per-instance `¬ LogCommitRegrounded.LogColl` at the EXACT pair the
old proof fed the floor). This module is what makes that cutover a BUILD-TIME invariant rather than a
claim, with two independent teeth per theorem:

  1. **`example : ⟨the intended S3 type⟩ := @original`** — an INDEPENDENTLY WRITTEN statement of what
     each cut-over theorem is now supposed to say, accepted only by KERNEL DEFEQ against the actual
     declaration. A silent weakening, a dropped hypothesis, a binder reorder, or a floor-binder
     resurrection turns the build RED here. (These are hand-written, not printed from the declaration
     — a tooth transcribed from its own subject would only prove the printer is deterministic.)
  2. **`#assert_not_depends_on … [logHashInjective]`** — the refuted floor is UNREACHABLE from the
     cut-over theorem's proof. This is the pin that a "port" which quietly re-introduced the floor via
     a helper could not survive.

  3. **`example : ⟨the OLD statement⟩ := ⟨new⟩ (noLogColl_of_inj hLog)`** — NO STRENGTH LOST: the
     pre-cutover statement is still derivable, through the bridge. Together with (1) this is the
     campaign's bar in both directions — the new hypothesis is IMPLIED BY the old one (so each ported
     theorem is logically STRONGER), and the conclusions are unchanged.

Endpoints pinned: the v1 generic pair (`EffectCommit`), the v2/dual/triple/quad/quint pairs
(`EffectCommit2`…`EffectCommit5`), the concrete `SetFieldCommit` pair, and the two log-seam theorems
in `CircuitSoundness`. `CommitmentCrossBind.setFieldCommit_binds_all` is deliberately NOT here: it is
a multi-floor site under live co-tenant edit (the `cellLeafInjective` lane), and cutting it over in
this transaction would have meant committing someone else's in-flight work.
-/
import Dregg2.Circuit.EffectCommit
import Dregg2.Circuit.EffectCommit2
import Dregg2.Circuit.EffectCommit2Dual
import Dregg2.Circuit.EffectCommit3
import Dregg2.Circuit.EffectCommit4
import Dregg2.Circuit.EffectCommit5
import Dregg2.Circuit.SetFieldCommit
import Dregg2.Circuit.CircuitSoundness
import Dregg2.Circuit.LogCommitRegrounded
import Dregg2.Circuit.WitnessExtract
import Dregg2.Circuit.WitnessExtractDual
import Dregg2.Circuit.WitnessExtract3
import Dregg2.Circuit.WitnessExtract5
import Dregg2.Circuit.WitnessExtractPerEffect
import Dregg2.Tactics

namespace Dregg2.Circuit.LogCommitCutoverCheck

open Dregg2.Circuit.StateCommit
open Dregg2.Circuit.LogCommitRegrounded (LogColl noLogColl_of_inj)
open Dregg2.Exec

set_option autoImplicit false

/-! ## §1 — the v1 generic pair (`Circuit/EffectCommit`). -/

section V1
open Dregg2.Circuit.EffectCommit

/-- ⚙ CUTOVER CHECK — `effect_circuit_full_sound` carries the per-instance log side condition and NO
`logHashInjective`; kernel defeq, re-proved every build. -/
example : ∀ (St Args : Type) (S : CommitSurface) (E : EffectSpec St Args),
    compressNInjective S.compressN → cellLeafInjective S.CH → RestHashIffFrame S.RH →
    GuardDecodes E → ∀ (pre : St) (args : Args) (post : St),
    AccountsWF (E.view.toKernel pre) → AccountsWF (E.view.toKernel post) →
    ¬ LogColl S.LH (E.view.getLog post) (E.postLog pre args) →
    satisfiedE S E (encodeE S E pre args post) →
    E.apex pre args post :=
  @effect_circuit_full_sound

/-- NO STRENGTH LOST — the pre-cutover statement of `effect_circuit_full_sound`, re-derived through
the `noLogColl_of_inj` bridge. -/
example {St Args : Type} (S : CommitSurface) (E : EffectSpec St Args)
    (hN : compressNInjective S.compressN) (hL : cellLeafInjective S.CH)
    (hRest : RestHashIffFrame S.RH) (hLog : logHashInjective S.LH) (hGuard : GuardDecodes E)
    (pre : St) (args : Args) (post : St)
    (hwf : AccountsWF (E.view.toKernel pre)) (hwf' : AccountsWF (E.view.toKernel post))
    (h : satisfiedE S E (encodeE S E pre args post)) :
    E.apex pre args post :=
  effect_circuit_full_sound S E hN hL hRest hGuard pre args post hwf hwf'
    (noLogColl_of_inj hLog) h

/-- ⚙ CUTOVER CHECK — `effectCircuit_rejects_log_forge`. -/
example : ∀ (St Args : Type) (S : CommitSurface) (E : EffectSpec St Args)
    (pre : St) (args : Args) (post : St),
    ¬ LogColl S.LH (E.view.getLog post) (E.postLog pre args) →
    E.view.getLog post ≠ E.postLog pre args →
    ¬ satisfiedE S E (encodeE S E pre args post) :=
  @effectCircuit_rejects_log_forge

/-- NO STRENGTH LOST — `effectCircuit_rejects_log_forge`, old statement. -/
example {St Args : Type} (S : CommitSurface) (E : EffectSpec St Args)
    (hLog : logHashInjective S.LH) (pre : St) (args : Args) (post : St)
    (htamper : E.view.getLog post ≠ E.postLog pre args) :
    ¬ satisfiedE S E (encodeE S E pre args post) :=
  effectCircuit_rejects_log_forge S E pre args post (noLogColl_of_inj hLog) htamper

end V1

#assert_axioms Dregg2.Circuit.EffectCommit.effect_circuit_full_sound
#assert_not_depends_on Dregg2.Circuit.EffectCommit.effect_circuit_full_sound
  [Dregg2.Circuit.StateCommit.logHashInjective]
#assert_axioms Dregg2.Circuit.EffectCommit.effectCircuit_rejects_log_forge
#assert_not_depends_on Dregg2.Circuit.EffectCommit.effectCircuit_rejects_log_forge
  [Dregg2.Circuit.StateCommit.logHashInjective]

/-! ## §2 — the v2 generic pair (`Circuit/EffectCommit2`). -/

section V2
open Dregg2.Circuit.EffectCommit2

/-- ⚙ CUTOVER CHECK — `effect2_circuit_full_sound` (the v2 crown jewel). -/
example : ∀ (St Args : Type) (S : Surface2) (E : EffectSpec2 St Args),
    RestFrameDecodes2 S E → GuardDecodes2 E → ∀ (pre : St) (args : Args) (post : St),
    ¬ LogColl S.LH (E.view.getLog post) (E.postLog pre args) →
    satisfiedE2 S E (encodeE2 S E pre args post) →
    E.apex pre args post :=
  @effect2_circuit_full_sound

/-- NO STRENGTH LOST — `effect2_circuit_full_sound`, old statement. -/
example {St Args : Type} (S : Surface2) (E : EffectSpec2 St Args)
    (hRestF : RestFrameDecodes2 S E) (hLog : logHashInjective S.LH) (hGuard : GuardDecodes2 E)
    (pre : St) (args : Args) (post : St)
    (h : satisfiedE2 S E (encodeE2 S E pre args post)) :
    E.apex pre args post :=
  effect2_circuit_full_sound S E hRestF hGuard pre args post (noLogColl_of_inj hLog) h

/-- ⚙ CUTOVER CHECK — `effectCircuit2_rejects_log_forge`. -/
example : ∀ (St Args : Type) (S : Surface2) (E : EffectSpec2 St Args)
    (pre : St) (args : Args) (post : St),
    E.view.getLog post ≠ E.postLog pre args →
    ¬ LogColl S.LH (E.view.getLog post) (E.postLog pre args) →
    ¬ satisfiedE2 S E (encodeE2 S E pre args post) :=
  @effectCircuit2_rejects_log_forge

end V2

#assert_axioms Dregg2.Circuit.EffectCommit2.effect2_circuit_full_sound
#assert_not_depends_on Dregg2.Circuit.EffectCommit2.effect2_circuit_full_sound
  [Dregg2.Circuit.StateCommit.logHashInjective]
#assert_axioms Dregg2.Circuit.EffectCommit2.effectCircuit2_rejects_log_forge
#assert_not_depends_on Dregg2.Circuit.EffectCommit2.effectCircuit2_rejects_log_forge
  [Dregg2.Circuit.StateCommit.logHashInjective]

/-! ## §3 — the DUAL pair (`Circuit/EffectCommit2Dual`). -/

section V2Dual
open Dregg2.Circuit.EffectCommit2Dual

/-- ⚙ CUTOVER CHECK — `effect2dual_circuit_full_sound`. -/
example : ∀ (St Args : Type) (S : Dregg2.Circuit.EffectCommit2.Surface2)
    (E : EffectSpec2Dual St Args),
    RestFrameDecodes2Dual S E → GuardDecodes2Dual E → ∀ (pre : St) (args : Args) (post : St),
    ¬ LogColl S.LH (E.view.getLog post) (E.postLog pre args) →
    satisfiedE2Dual S E (encodeE2Dual S E pre args post) →
    E.apex pre args post :=
  @effect2dual_circuit_full_sound

/-- ⚙ CUTOVER CHECK — `effectCircuit2Dual_rejects_log_forge`. -/
example : ∀ (St Args : Type) (S : Dregg2.Circuit.EffectCommit2.Surface2)
    (E : EffectSpec2Dual St Args) (pre : St) (args : Args) (post : St),
    E.view.getLog post ≠ E.postLog pre args →
    ¬ LogColl S.LH (E.view.getLog post) (E.postLog pre args) →
    ¬ satisfiedE2Dual S E (encodeE2Dual S E pre args post) :=
  @effectCircuit2Dual_rejects_log_forge

end V2Dual

#assert_axioms Dregg2.Circuit.EffectCommit2Dual.effect2dual_circuit_full_sound
#assert_not_depends_on Dregg2.Circuit.EffectCommit2Dual.effect2dual_circuit_full_sound
  [Dregg2.Circuit.StateCommit.logHashInjective]
#assert_axioms Dregg2.Circuit.EffectCommit2Dual.effectCircuit2Dual_rejects_log_forge
#assert_not_depends_on Dregg2.Circuit.EffectCommit2Dual.effectCircuit2Dual_rejects_log_forge
  [Dregg2.Circuit.StateCommit.logHashInjective]

/-! ## §4 — the TRIPLE pair (`Circuit/EffectCommit3`). -/

section V2Triple
open Dregg2.Circuit.EffectCommit3

/-- ⚙ CUTOVER CHECK — `effect2triple_circuit_full_sound`. -/
example : ∀ (St Args : Type) (S : Dregg2.Circuit.EffectCommit2.Surface2)
    (E : EffectSpec2Triple St Args),
    RestFrameDecodes2Triple S E → GuardDecodes2Triple E → ∀ (pre : St) (args : Args) (post : St),
    ¬ LogColl S.LH (E.view.getLog post) (E.postLog pre args) →
    satisfiedE2Triple S E (encodeE2Triple S E pre args post) →
    E.apex pre args post :=
  @effect2triple_circuit_full_sound

/-- ⚙ CUTOVER CHECK — `effectCircuit2Triple_rejects_log_forge`. -/
example : ∀ (St Args : Type) (S : Dregg2.Circuit.EffectCommit2.Surface2)
    (E : EffectSpec2Triple St Args) (pre : St) (args : Args) (post : St),
    E.view.getLog post ≠ E.postLog pre args →
    ¬ LogColl S.LH (E.view.getLog post) (E.postLog pre args) →
    ¬ satisfiedE2Triple S E (encodeE2Triple S E pre args post) :=
  @effectCircuit2Triple_rejects_log_forge

end V2Triple

#assert_axioms Dregg2.Circuit.EffectCommit3.effect2triple_circuit_full_sound
#assert_not_depends_on Dregg2.Circuit.EffectCommit3.effect2triple_circuit_full_sound
  [Dregg2.Circuit.StateCommit.logHashInjective]
#assert_axioms Dregg2.Circuit.EffectCommit3.effectCircuit2Triple_rejects_log_forge
#assert_not_depends_on Dregg2.Circuit.EffectCommit3.effectCircuit2Triple_rejects_log_forge
  [Dregg2.Circuit.StateCommit.logHashInjective]

/-! ## §5 — the QUAD pair (`Circuit/EffectCommit4`). -/

section V2Quad
open Dregg2.Circuit.EffectCommit4

/-- ⚙ CUTOVER CHECK — `effect2quad_circuit_full_sound`. -/
example : ∀ (St Args : Type) (S : Dregg2.Circuit.EffectCommit2.Surface2)
    (E : EffectSpec2Quad St Args),
    RestFrameDecodes2Quad S E → GuardDecodes2Quad E → ∀ (pre : St) (args : Args) (post : St),
    ¬ LogColl S.LH (E.view.getLog post) (E.postLog pre args) →
    satisfiedE2Quad S E (encodeE2Quad S E pre args post) →
    E.apex pre args post :=
  @effect2quad_circuit_full_sound

/-- ⚙ CUTOVER CHECK — `effectCircuit2Quad_rejects_log_forge`. -/
example : ∀ (St Args : Type) (S : Dregg2.Circuit.EffectCommit2.Surface2)
    (E : EffectSpec2Quad St Args) (pre : St) (args : Args) (post : St),
    E.view.getLog post ≠ E.postLog pre args →
    ¬ LogColl S.LH (E.view.getLog post) (E.postLog pre args) →
    ¬ satisfiedE2Quad S E (encodeE2Quad S E pre args post) :=
  @effectCircuit2Quad_rejects_log_forge

end V2Quad

#assert_axioms Dregg2.Circuit.EffectCommit4.effect2quad_circuit_full_sound
#assert_not_depends_on Dregg2.Circuit.EffectCommit4.effect2quad_circuit_full_sound
  [Dregg2.Circuit.StateCommit.logHashInjective]
#assert_axioms Dregg2.Circuit.EffectCommit4.effectCircuit2Quad_rejects_log_forge
#assert_not_depends_on Dregg2.Circuit.EffectCommit4.effectCircuit2Quad_rejects_log_forge
  [Dregg2.Circuit.StateCommit.logHashInjective]

/-! ## §6 — the QUINT pair (`Circuit/EffectCommit5`). -/

section V2Quint
open Dregg2.Circuit.EffectCommit5

/-- ⚙ CUTOVER CHECK — `effect2quint_circuit_full_sound`. -/
example : ∀ (St Args : Type) (S : Dregg2.Circuit.EffectCommit2.Surface2)
    (E : EffectSpec2Quint St Args),
    RestFrameDecodes2Quint S E → GuardDecodes2Quint E → ∀ (pre : St) (args : Args) (post : St),
    ¬ LogColl S.LH (E.view.getLog post) (E.postLog pre args) →
    satisfiedE2Quint S E (encodeE2Quint S E pre args post) →
    E.apex pre args post :=
  @effect2quint_circuit_full_sound

/-- ⚙ CUTOVER CHECK — `effectCircuit2Quint_rejects_log_forge`. -/
example : ∀ (St Args : Type) (S : Dregg2.Circuit.EffectCommit2.Surface2)
    (E : EffectSpec2Quint St Args) (pre : St) (args : Args) (post : St),
    E.view.getLog post ≠ E.postLog pre args →
    ¬ LogColl S.LH (E.view.getLog post) (E.postLog pre args) →
    ¬ satisfiedE2Quint S E (encodeE2Quint S E pre args post) :=
  @effectCircuit2Quint_rejects_log_forge

end V2Quint

#assert_axioms Dregg2.Circuit.EffectCommit5.effect2quint_circuit_full_sound
#assert_not_depends_on Dregg2.Circuit.EffectCommit5.effect2quint_circuit_full_sound
  [Dregg2.Circuit.StateCommit.logHashInjective]
#assert_axioms Dregg2.Circuit.EffectCommit5.effectCircuit2Quint_rejects_log_forge
#assert_not_depends_on Dregg2.Circuit.EffectCommit5.effectCircuit2Quint_rejects_log_forge
  [Dregg2.Circuit.StateCommit.logHashInjective]

/-! ## §7 — the CONCRETE `setFieldA` pair (`Circuit/SetFieldCommit`). -/

section SF
open Dregg2.Circuit.SetFieldCommit
open Dregg2.Circuit.Spec.CellStateField

/-- ⚙ CUTOVER CHECK — `setfield_circuit_full_sound`. -/
example : ∀ (CH : CellId → Value → ℤ) (RH : RecordKernelState → ℤ) (cmb : ℤ → ℤ → ℤ)
    (compressN : List ℤ → ℤ) (LH : List Turn → ℤ),
    compressNInjective compressN → cellLeafInjective CH → RestHashIffFrame RH →
    ∀ (s : RecChainedState) (actor cell : CellId) (f : FieldName) (v : Int) (s' : RecChainedState),
    Dregg2.Exec.EffectsState.reservedField f = false →
    AccountsWF s.kernel → AccountsWF s'.kernel →
    ¬ LogColl LH s'.log ({ actor := actor, src := cell, dst := cell, amt := 0 } :: s.log) →
    satisfiedSF cmb (encodeSF CH RH cmb compressN LH s actor cell f v s') →
    SetFieldSpec s actor cell f v s' :=
  @setfield_circuit_full_sound

/-- ⚙ CUTOVER CHECK — `setFieldCircuit_rejects_log_forge`. -/
example : ∀ (CH : CellId → Value → ℤ) (RH : RecordKernelState → ℤ) (cmb : ℤ → ℤ → ℤ)
    (compressN : List ℤ → ℤ) (LH : List Turn → ℤ)
    (s : RecChainedState) (actor cell : CellId) (f : FieldName) (v : Int) (s' : RecChainedState),
    s'.log ≠ { actor := actor, src := cell, dst := cell, amt := 0 } :: s.log →
    ¬ LogColl LH s'.log ({ actor := actor, src := cell, dst := cell, amt := 0 } :: s.log) →
    ¬ satisfiedSF cmb (encodeSF CH RH cmb compressN LH s actor cell f v s') :=
  @setFieldCircuit_rejects_log_forge

end SF

#assert_axioms Dregg2.Circuit.SetFieldCommit.setfield_circuit_full_sound
#assert_not_depends_on Dregg2.Circuit.SetFieldCommit.setfield_circuit_full_sound
  [Dregg2.Circuit.StateCommit.logHashInjective]
#assert_axioms Dregg2.Circuit.SetFieldCommit.setFieldCircuit_rejects_log_forge
#assert_not_depends_on Dregg2.Circuit.SetFieldCommit.setFieldCircuit_rejects_log_forge
  [Dregg2.Circuit.StateCommit.logHashInjective]

/-! ## §8 — the LOG-SEAM pair (`Circuit/CircuitSoundness`). -/

section CS
open Dregg2.Circuit.CircuitSoundness

/-- ⚙ CUTOVER CHECK — `logDecode_faithful`. -/
example : ∀ (LH : List Turn → ℤ) (p q : ℤ) (pre post pre' post' : RecChainedState),
    ¬ LogColl LH pre.log pre'.log →
    LogDecode LH p q pre post → LogDecode LH p q pre' post' →
    pre.log = pre'.log :=
  @logDecode_faithful

/-- NO STRENGTH LOST — `logDecode_faithful`, old statement. -/
example (LH : List Turn → ℤ) (hLog : logHashInjective LH)
    {p q : ℤ} {pre post pre' post' : RecChainedState}
    (h : LogDecode LH p q pre post) (h' : LogDecode LH p q pre' post') :
    pre.log = pre'.log :=
  logDecode_faithful LH (noLogColl_of_inj hLog) h h'

/-- ⚙ CUTOVER CHECK — `logDecodeChain_frame_continuous`. -/
example : ∀ (LH : List Turn → ℤ) (a b : RecChainedState) (ap aq bp bq : ℤ)
    (a' b' : RecChainedState),
    ¬ LogColl LH a'.log b.log →
    LogDecode LH ap aq a a' → LogDecode LH bp bq b b' → aq = bp →
    a'.log = b.log :=
  @logDecodeChain_frame_continuous

/-- NO STRENGTH LOST — `logDecodeChain_frame_continuous`, old statement. -/
example (LH : List Turn → ℤ) (hLog : logHashInjective LH)
    {a b : RecChainedState} {ap aq bp bq : ℤ} {a' b' : RecChainedState}
    (hda : LogDecode LH ap aq a a') (hdb : LogDecode LH bp bq b b')
    (hseam : aq = bp) :
    a'.log = b.log :=
  logDecodeChain_frame_continuous LH (noLogColl_of_inj hLog) hda hdb hseam

end CS

#assert_axioms Dregg2.Circuit.CircuitSoundness.logDecode_faithful
#assert_not_depends_on Dregg2.Circuit.CircuitSoundness.logDecode_faithful
  [Dregg2.Circuit.StateCommit.logHashInjective]
#assert_axioms Dregg2.Circuit.CircuitSoundness.logDecodeChain_frame_continuous
#assert_not_depends_on Dregg2.Circuit.CircuitSoundness.logDecodeChain_frame_continuous
  [Dregg2.Circuit.StateCommit.logHashInjective]

/-! ## §7 — the ADVERSARIAL-WITNESS EXTRACTORS (`Circuit/WitnessExtract{,Dual,3,5}`), cut over 07-25.

The four generic extractors and their log-forgery teeth are the hostile-witness layer ABOVE the
`effect2*_circuit_full_sound` crown jewels §2-§5 already carry per-instance: an ARBITRARY assignment
that satisfies the effect circuit and is PI-bound forces the whole apex. Each took
`logHashInjective S.LH` purely to hand `noLogColl_of_inj hLog` to the crown jewel underneath — the
floor was a PASS-THROUGH, never consumed here, so its removal is a statement rewrite with no proof
content lost, and the per-instance pair is the one the layer below already names.

That pass-through is exactly why they mattered: `logHashInjective LH` is FALSE at deployed BabyBear
(`StateCommitFloorRegrounded.logHashInjective_false_babyBear` — a hash into a bounded field cannot be
injective on `List Turn`), so every extraction theorem taking it — including all 28 per-effect
instantiations in `WitnessExtractPerEffect` and the per-effect entries in `WitnessExtract{Dual,3,5}`
and `TurnEmit` — said NOTHING about the deployed prover. "A satisfying trace forces the spec" is the
whole hostile-witness claim; under a false hypothesis it was vacuous. -/

section Extractors
open Dregg2.Circuit.EffectCommit2 (Surface2 EffectSpec2 satisfiedE2 emittedEffect2)
open Dregg2.Circuit.WitnessExtract
open Dregg2.Exec.CircuitEmit (satisfiedEmitted)

/-- ⚙ CUTOVER CHECK — `effect2_extract`, THE single-component adversarial extractor. -/
example : ∀ (St Args : Type) (S : Surface2) (E : EffectSpec2 St Args),
    EffectCommit2.RestFrameDecodes2 S E → EffectCommit2.GuardDecodes2 E →
    ∀ (pre : St) (args : Args) (post : St) (a : Assignment),
    ¬ LogColl S.LH (E.view.getLog post) (E.postLog pre args) →
    satisfiedE2 S E a → PIBindsDigests S E pre args post a →
    E.apex pre args post :=
  @effect2_extract

/-- NO STRENGTH LOST — `effect2_extract`'s pre-cutover statement, through the bridge. -/
example {St Args : Type} (S : Surface2) (E : EffectSpec2 St Args)
    (hRestF : EffectCommit2.RestFrameDecodes2 S E) (hLog : logHashInjective S.LH)
    (hGuard : EffectCommit2.GuardDecodes2 E)
    (pre : St) (args : Args) (post : St) (a : Assignment)
    (hsat : satisfiedE2 S E a) (hPI : PIBindsDigests S E pre args post a) :
    E.apex pre args post :=
  effect2_extract S E hRestF hGuard pre args post a (noLogColl_of_inj hLog) hsat hPI

/-- ⚙ CUTOVER CHECK — `effect2_extract_emitted` (the same, against the Rust-prover wire form). -/
example : ∀ (St Args : Type) (S : Surface2) (E : EffectSpec2 St Args),
    EffectCommit2.RestFrameDecodes2 S E → EffectCommit2.GuardDecodes2 E →
    ∀ (name : String) (pre : St) (args : Args) (post : St) (a : Assignment),
    ¬ LogColl S.LH (E.view.getLog post) (E.postLog pre args) →
    satisfiedEmitted (emittedEffect2 name E) a → PIBindsDigests S E pre args post a →
    E.apex pre args post :=
  @effect2_extract_emitted

/-- ⚙ CUTOVER CHECK — `effect2_extract_rejects_log_forge` (the anti-ghost log tooth). -/
example : ∀ (St Args : Type) (S : Surface2) (E : EffectSpec2 St Args)
    (pre : St) (args : Args) (post : St) (a : Assignment),
    ¬ LogColl S.LH (E.view.getLog post) (E.postLog pre args) →
    PIBindsDigests S E pre args post a →
    E.view.getLog post ≠ E.postLog pre args →
    ¬ satisfiedE2 S E a :=
  @effect2_extract_rejects_log_forge

/-- NO STRENGTH LOST — the log-forgery tooth's pre-cutover statement. -/
example {St Args : Type} (S : Surface2) (E : EffectSpec2 St Args) (hLog : logHashInjective S.LH)
    (pre : St) (args : Args) (post : St) (a : Assignment)
    (hPI : PIBindsDigests S E pre args post a)
    (htamper : E.view.getLog post ≠ E.postLog pre args) :
    ¬ satisfiedE2 S E a :=
  effect2_extract_rejects_log_forge S E pre args post a (noLogColl_of_inj hLog) hPI htamper

end Extractors

section ExtractorsDual
open Dregg2.Circuit.EffectCommit2 (Surface2)
open Dregg2.Circuit.EffectCommit2Dual (EffectSpec2Dual satisfiedE2Dual)
open Dregg2.Circuit.WitnessExtractDual

/-- ⚙ CUTOVER CHECK — `effect2dual_extract`. -/
example : ∀ (St Args : Type) (S : Surface2) (E : EffectSpec2Dual St Args),
    EffectCommit2Dual.RestFrameDecodes2Dual S E → EffectCommit2Dual.GuardDecodes2Dual E →
    ∀ (pre : St) (args : Args) (post : St) (a : Assignment),
    ¬ LogColl S.LH (E.view.getLog post) (E.postLog pre args) →
    satisfiedE2Dual S E a → PIBindsDigestsDual S E pre args post a →
    E.apex pre args post :=
  @effect2dual_extract

/-- NO STRENGTH LOST — `effect2dual_extract`, old statement. -/
example {St Args : Type} (S : Surface2) (E : EffectSpec2Dual St Args)
    (hRestF : EffectCommit2Dual.RestFrameDecodes2Dual S E) (hLog : logHashInjective S.LH)
    (hGuard : EffectCommit2Dual.GuardDecodes2Dual E)
    (pre : St) (args : Args) (post : St) (a : Assignment)
    (hsat : satisfiedE2Dual S E a) (hPI : PIBindsDigestsDual S E pre args post a) :
    E.apex pre args post :=
  effect2dual_extract S E hRestF hGuard pre args post a (noLogColl_of_inj hLog) hsat hPI

/-- ⚙ CUTOVER CHECK — `effect2dual_extract_rejects_log_forge`. -/
example : ∀ (St Args : Type) (S : Surface2) (E : EffectSpec2Dual St Args)
    (pre : St) (args : Args) (post : St) (a : Assignment),
    ¬ LogColl S.LH (E.view.getLog post) (E.postLog pre args) →
    PIBindsDigestsDual S E pre args post a →
    E.view.getLog post ≠ E.postLog pre args →
    ¬ satisfiedE2Dual S E a :=
  @effect2dual_extract_rejects_log_forge

end ExtractorsDual

section ExtractorsTriple
open Dregg2.Circuit.EffectCommit2 (Surface2)
open Dregg2.Circuit.EffectCommit3 (EffectSpec2Triple satisfiedE2Triple)
open Dregg2.Circuit.WitnessExtract3

/-- ⚙ CUTOVER CHECK — `effect2triple_extract`. -/
example : ∀ (St Args : Type) (S : Surface2) (E : EffectSpec2Triple St Args),
    EffectCommit3.RestFrameDecodes2Triple S E → EffectCommit3.GuardDecodes2Triple E →
    ∀ (pre : St) (args : Args) (post : St) (a : Assignment),
    ¬ LogColl S.LH (E.view.getLog post) (E.postLog pre args) →
    satisfiedE2Triple S E a → PIBindsDigestsTriple S E pre args post a →
    E.apex pre args post :=
  @effect2triple_extract

/-- ⚙ CUTOVER CHECK — `effect2triple_extract_rejects_log_forge`. -/
example : ∀ (St Args : Type) (S : Surface2) (E : EffectSpec2Triple St Args)
    (pre : St) (args : Args) (post : St) (a : Assignment),
    ¬ LogColl S.LH (E.view.getLog post) (E.postLog pre args) →
    PIBindsDigestsTriple S E pre args post a →
    E.view.getLog post ≠ E.postLog pre args →
    ¬ satisfiedE2Triple S E a :=
  @effect2triple_extract_rejects_log_forge

end ExtractorsTriple

section ExtractorsQuint
open Dregg2.Circuit.EffectCommit2 (Surface2)
open Dregg2.Circuit.EffectCommit5 (EffectSpec2Quint satisfiedE2Quint)
open Dregg2.Circuit.WitnessExtract5

/-- ⚙ CUTOVER CHECK — `effect2quint_extract`. -/
example : ∀ (St Args : Type) (S : Surface2) (E : EffectSpec2Quint St Args),
    EffectCommit5.RestFrameDecodes2Quint S E → EffectCommit5.GuardDecodes2Quint E →
    ∀ (pre : St) (args : Args) (post : St) (a : Assignment),
    ¬ LogColl S.LH (E.view.getLog post) (E.postLog pre args) →
    satisfiedE2Quint S E a → PIBindsDigestsQuint S E pre args post a →
    E.apex pre args post :=
  @effect2quint_extract

/-- ⚙ CUTOVER CHECK — `effect2quint_extract_rejects_log_forge`. -/
example : ∀ (St Args : Type) (S : Surface2) (E : EffectSpec2Quint St Args)
    (pre : St) (args : Args) (post : St) (a : Assignment),
    ¬ LogColl S.LH (E.view.getLog post) (E.postLog pre args) →
    PIBindsDigestsQuint S E pre args post a →
    E.view.getLog post ≠ E.postLog pre args →
    ¬ satisfiedE2Quint S E a :=
  @effect2quint_extract_rejects_log_forge

end ExtractorsQuint

#assert_axioms Dregg2.Circuit.WitnessExtract.effect2_extract
#assert_not_depends_on Dregg2.Circuit.WitnessExtract.effect2_extract
  [Dregg2.Circuit.StateCommit.logHashInjective]
#assert_axioms Dregg2.Circuit.WitnessExtract.effect2_extract_emitted
#assert_not_depends_on Dregg2.Circuit.WitnessExtract.effect2_extract_emitted
  [Dregg2.Circuit.StateCommit.logHashInjective]
#assert_axioms Dregg2.Circuit.WitnessExtract.effect2_extract_rejects_log_forge
#assert_not_depends_on Dregg2.Circuit.WitnessExtract.effect2_extract_rejects_log_forge
  [Dregg2.Circuit.StateCommit.logHashInjective]
#assert_axioms Dregg2.Circuit.WitnessExtractDual.effect2dual_extract
#assert_not_depends_on Dregg2.Circuit.WitnessExtractDual.effect2dual_extract
  [Dregg2.Circuit.StateCommit.logHashInjective]
#assert_axioms Dregg2.Circuit.WitnessExtract3.effect2triple_extract
#assert_not_depends_on Dregg2.Circuit.WitnessExtract3.effect2triple_extract
  [Dregg2.Circuit.StateCommit.logHashInjective]
#assert_axioms Dregg2.Circuit.WitnessExtract5.effect2quint_extract
#assert_not_depends_on Dregg2.Circuit.WitnessExtract5.effect2quint_extract
  [Dregg2.Circuit.StateCommit.logHashInjective]

/-- ⚙ ONE PER-EFFECT INSTANTIATION, PINNED. The 28 `WitnessExtractPerEffect` entries and the
`TurnEmit` mint pair are mechanical retargets of the generics above, so one is checked here in full
to pin the SHAPE the whole family now has: the side condition is `¬ LogColl` at THIS effect's own
`(claimed post-log, spec-predicted post-log)` pair, and nothing quantifies over all log pairs. -/
example : ∀ (S : Dregg2.Circuit.EffectCommit2.Surface2)
    (D : (Dregg2.Exec.CellId → Dregg2.Exec.AssetId → ℤ) → ℤ) (hD : Function.Injective D),
    Dregg2.Circuit.EffectCommit2.RestIffNoBal S.RH →
    ∀ (s : Dregg2.Exec.RecChainedState) (args : Dregg2.Circuit.Inst.Transfer.BalanceArgs)
      (s' : Dregg2.Exec.RecChainedState) (a : Assignment),
    ¬ LogColl S.LH ((Dregg2.Circuit.Inst.Transfer.balanceE D hD).view.getLog s')
        ((Dregg2.Circuit.Inst.Transfer.balanceE D hD).postLog s args) →
    Dregg2.Circuit.EffectCommit2.satisfiedE2 S (Dregg2.Circuit.Inst.Transfer.balanceE D hD) a →
    Dregg2.Circuit.WitnessExtract.PIBindsDigests S
      (Dregg2.Circuit.Inst.Transfer.balanceE D hD) s args s' a →
    Dregg2.Circuit.Spec.BalanceMovement.BalanceMovementSpec s args.t args.a s' :=
  @Dregg2.Circuit.WitnessExtractPerEffect.transfer_extract

#assert_axioms Dregg2.Circuit.WitnessExtractPerEffect.transfer_extract
#assert_not_depends_on Dregg2.Circuit.WitnessExtractPerEffect.transfer_extract
  [Dregg2.Circuit.StateCommit.logHashInjective]

/-! ## THE BLINDNESS CONTROL (the reason the 16 greens above mean anything).

The `#assert_not_depends_on` pins above are REJECTORS: each passes by finding nothing. A rejector
cannot detect its own blindness, and `Dregg2/Tactics.lean` records the measurement that settles it —
built with `allowOpaque := false` the shared walk MISSED a real semantic dependency while reporting
`scanned = 36`, because a root's TYPE constants are still walked when its VALUE is invisible. Under
that failure every pin above reports CLEAN, vacuously, and this module stays green.

`#assert_depends_on` is the exact dual and shares the same `findForbiddenPath`, so the two go blind
together or not at all. `walkControl`'s statement is `True` — it reaches `logHashInjective` ONLY
through its proof term — so a walk that has stopped opening theorem values cannot report it and the
build fails HERE, loudly, instead of certifying 16 cut-over endpoints on a blind scan.

Tactics.lean states the bar: every module relying on `#assert_not_depends_on` should carry at least
one such control. This module carried 16 pins and none. Do not delete it to get green. -/
theorem walkControl : True := by
  have _h := @Dregg2.Circuit.StateCommit.logHashInjective
  trivial

#assert_axioms Dregg2.Circuit.LogCommitCutoverCheck.walkControl
#assert_depends_on Dregg2.Circuit.LogCommitCutoverCheck.walkControl
  [Dregg2.Circuit.StateCommit.logHashInjective]

end Dregg2.Circuit.LogCommitCutoverCheck
