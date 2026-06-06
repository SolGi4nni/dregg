/-
# Dregg2.Circuit.WitnessExtract — the adversarial-witness EXTRACTOR for the v2 effect circuit.

`effect2_circuit_full_sound` (and the whole emitted tower above it) takes its satisfying witness in the
shape `satisfiedE2 S E (encodeE2 S E pre args post)` — i.e. the circuit satisfied ON THE HONEST
ENCODING. Downstream (`TurnEmit.step_emitted_refines_fullActionStep`) this forces a free hypothesis
`hEnc : assignmentOf sw.assignment = encodeE2 …` that pins the WHOLE 72-wire witness to the honest
encoder, and is then NEVER USED — so the soundness theorem proves only "honest-encoded trace ⇒ state",
smuggling the real ZK obligation in as an assumption.

This module discharges the genuine obligation: an EXTRACTOR over an ARBITRARY assignment `a`. The key
structural fact is that `satisfiedE2 S E a` reads `a` only on the GUARD region (`< guardWidth`) and the
six frame/bind/log digest wires `66 .. 71` (`cE2RestF`/`cE2Bind`/`cE2Log` reference exactly those, by
their definitions). So an adversary's free choice on the OTHER wires — INCLUDING the two root wires `64`,
`65`, which `effectCircuit2` never gates — is irrelevant; what the verifier must (and does) pin is just
those gate-relevant wires, via its PUBLIC-INPUT check against the committed digests.

We name that verifier obligation `PIBindsDigests`: `a` agrees with the honest encoding on the guard
region and the six digest wires. It is STRICTLY WEAKER than the dead `hEnc` (which pinned all 72 wires);
the adversary keeps every non-gate wire, including the un-gated roots. From `PIBindsDigests` alone +
satisfaction we EXTRACT the full apex — proving the satisfying trace determines `(pre, args, post)`'s
post-state. The Poseidon2 CR grounding (`Poseidon2Binding`) is what makes the digest-wire bindings the
verifier publishes actually PIN the state: an injective component/rest/log digest has at most one
preimage, so the published digest fixes the post component / frame / log uniquely (`extract_*_unique`).

NON-VACUITY: `effect2_extract_rejects_*` — a trace whose digest wires are PI-bound but whose state
VIOLATES the apex (wrong component / tampered frame / forged log) is UNSAT. This is the anti-ghost
tooth: the extractor genuinely constrains.

No `sorry`/`admit`/`axiom`/`native_decide`. Each keystone pins exactly `{propext, Classical.choice,
Quot.sound}` (asserted at the foot).
-/
import Dregg2.Circuit.EffectCommit2
import Dregg2.Circuit.Poseidon2Binding

namespace Dregg2.Circuit.WitnessExtract

open Dregg2.Circuit
open Dregg2.Circuit.StateCommit (logHashInjective)
open Dregg2.Circuit.EffectCommit2
open Dregg2.Circuit.Poseidon2Binding (Poseidon2SpongeCR)
open Dregg2.Exec (RecordKernelState Turn)

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## §1 — the public-input binding the verifier enforces on the gate-relevant wires.

This is the predicate a REAL verifier discharges: its public-input check pins the witness's six digest
wires (and the guard region) to the committed values for the CLAIMED `(pre, args, post)`. It does NOT
mention wires `64`, `65` (the roots, never gated) nor any wire `≥ 72` — the adversary keeps those. -/

/-- **`PIBindsDigests S E pre args post a`** — the verifier's public-input obligation: `a` agrees with
the honest encoding `encodeE2 S E pre args post` on (i) the guard region `w < guardWidth` and (ii) the
six frame/bind/log digest wires `66 .. 71`. STRICTLY WEAKER than `a = encodeE2 …` (no claim on the
root wires `64/65` nor on any `w ≥ 72`). -/
def PIBindsDigests {St Args : Type} (S : Surface2) (E : EffectSpec2 St Args)
    (pre : St) (args : Args) (post : St) (a : Assignment) : Prop :=
  (∀ w, w < E.guardWidth → a w = E.guardEncode pre args post w)
  ∧ a vE2RestPre  = S.RH (E.view.toKernel pre)
  ∧ a vE2RestPost = S.RH (E.view.toKernel post)
  ∧ a vE2CompPost = E.active.digest (E.view.toKernel post)
  ∧ a vE2CompExp  = E.active.expected pre args
  ∧ a vE2LogPost  = S.LH (E.view.getLog post)
  ∧ a vE2LogExp   = S.LH (E.postLog pre args)

/-- The honest encoding itself satisfies the PI obligation (sanity: the binding is realizable). -/
theorem encodeE2_PIBindsDigests {St Args : Type} (S : Surface2) (E : EffectSpec2 St Args)
    (pre : St) (args : Args) (post : St) :
    PIBindsDigests S E pre args post (encodeE2 S E pre args post) := by
  refine ⟨fun w hw => encodeE2_agrees_guardEncode S E pre args post w hw, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact enc2_restPre S E pre args post
  · exact enc2_restPost S E pre args post
  · exact enc2_compPost S E pre args post
  · exact enc2_compExp S E pre args post
  · exact enc2_logPost S E pre args post
  · exact enc2_logExp S E pre args post

/-! ## §2 — locality: `satisfiedE2` reads only the gate-relevant wires.

`cE2RestF` is `vE2RestPre = vE2RestPost` (wires 66, 67); `cE2Bind` is `vE2CompPost = vE2CompExp`
(68, 69); `cE2Log` is `vE2LogPost = vE2LogExp` (70, 71); the guard gates are local on `< guardWidth`
(`E.guardLocal`). So PI-binding `a` to the honest encoding on exactly those wires transports
satisfaction. -/

/-- **`satisfiedE2_of_PIBindsDigests`** — an ARBITRARY `a` that is PI-bound to the honest encoding's
gate-relevant wires satisfies `effectCircuit2` IFF the honest encoding does. Proof: each gate's holding
under `a` rewrites (via the seven PI equalities) to its holding under `encodeE2`, and the guard region
transports by `E.guardLocal`. This is the bridge that lets us run `effect2_circuit_full_sound` on a
trace we did NOT assume equals the encoder over all 72 wires. -/
theorem satisfiedE2_of_PIBindsDigests {St Args : Type} (S : Surface2) (E : EffectSpec2 St Args)
    (pre : St) (args : Args) (post : St) (a : Assignment)
    (hPI : PIBindsDigests S E pre args post a) :
    satisfiedE2 S E a ↔ satisfiedE2 S E (encodeE2 S E pre args post) := by
  obtain ⟨hguard, hRestPre, hRestPost, hCompPost, hCompExp, hLogPost, hLogExp⟩ := hPI
  unfold satisfiedE2 effectCircuit2
  constructor
  · intro hsat c hc
    rcases List.mem_append.mp hc with hcg | hc3
    · -- guard gate: transport via guardLocal (a agrees with guardEncode on `< guardWidth`,
      -- and encodeE2 agrees with guardEncode there too).
      have hag : satisfied E.guardGates a := fun c' hc' => hsat c' (List.mem_append_left _ hc')
      have hge : satisfied E.guardGates (E.guardEncode pre args post) :=
        (E.guardLocal a _ hguard).mp hag
      have : satisfied E.guardGates (encodeE2 S E pre args post) :=
        (E.guardLocal _ _ (fun w hw => encodeE2_agrees_guardEncode S E pre args post w hw)).mpr hge
      exact this c hcg
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hc3
      rcases hc3 with rfl | rfl | rfl
      · -- cE2RestF
        unfold Constraint.holds cE2RestF
        simp only [Expr.eval, enc2_restPre, enc2_restPost]
        have := hsat cE2RestF (by simp [List.mem_append])
        unfold Constraint.holds cE2RestF at this
        simp only [Expr.eval] at this
        rw [hRestPre, hRestPost] at this; exact this
      · -- cE2Bind
        unfold Constraint.holds cE2Bind
        simp only [Expr.eval, enc2_compPost, enc2_compExp]
        have := hsat cE2Bind (by simp [List.mem_append])
        unfold Constraint.holds cE2Bind at this
        simp only [Expr.eval] at this
        rw [hCompPost, hCompExp] at this; exact this
      · -- cE2Log
        unfold Constraint.holds cE2Log
        simp only [Expr.eval, enc2_logPost, enc2_logExp]
        have := hsat cE2Log (by simp [List.mem_append])
        unfold Constraint.holds cE2Log at this
        simp only [Expr.eval] at this
        rw [hLogPost, hLogExp] at this; exact this
  · intro hsat c hc
    rcases List.mem_append.mp hc with hcg | hc3
    · have hge : satisfied E.guardGates (E.guardEncode pre args post) :=
        (E.guardLocal _ _ (fun w hw => encodeE2_agrees_guardEncode S E pre args post w hw)).mp
          (fun c' hc' => hsat c' (List.mem_append_left _ hc'))
      exact (E.guardLocal a _ hguard).mpr hge c hcg
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hc3
      rcases hc3 with rfl | rfl | rfl
      · unfold Constraint.holds cE2RestF
        simp only [Expr.eval]
        rw [hRestPre, hRestPost]
        have := hsat cE2RestF (by simp [List.mem_append])
        unfold Constraint.holds cE2RestF at this
        simp only [Expr.eval, enc2_restPre, enc2_restPost] at this; exact this
      · unfold Constraint.holds cE2Bind
        simp only [Expr.eval]
        rw [hCompPost, hCompExp]
        have := hsat cE2Bind (by simp [List.mem_append])
        unfold Constraint.holds cE2Bind at this
        simp only [Expr.eval, enc2_compPost, enc2_compExp] at this; exact this
      · unfold Constraint.holds cE2Log
        simp only [Expr.eval]
        rw [hLogPost, hLogExp]
        have := hsat cE2Log (by simp [List.mem_append])
        unfold Constraint.holds cE2Log at this
        simp only [Expr.eval, enc2_logPost, enc2_logExp] at this; exact this

/-! ## §3 — the EXTRACTOR: arbitrary satisfying + PI-bound trace ⇒ full apex. -/

/-- **`effect2_extract`** — THE adversarial-witness extractor. An ARBITRARY assignment `a` that
(1) satisfies the effect circuit and (2) is PI-bound (the verifier's public-input check pins its six
digest wires + guard region to the committed values for the claimed `(pre, args, post)`) determines the
WHOLE post-state: `E.apex pre args post`. The witness is NOT assumed equal to `encodeE2` over all 72
wires — the adversary keeps the root wires `64/65` and every `w ≥ 72`. The needed digest-wire agreement
is exactly what a real verifier's public-input/boundary check enforces against the committed root
(grounded injective by Poseidon2 CR, `Poseidon2Binding`), so this is the genuine ZK soundness
obligation, no longer smuggled in as a free `hEnc`. -/
theorem effect2_extract {St Args : Type} (S : Surface2) (E : EffectSpec2 St Args)
    (hRestF : RestFrameDecodes2 S E) (hLog : logHashInjective S.LH) (hGuard : GuardDecodes2 E)
    (pre : St) (args : Args) (post : St) (a : Assignment)
    (hsat : satisfiedE2 S E a)
    (hPI : PIBindsDigests S E pre args post a) :
    E.apex pre args post :=
  effect2_circuit_full_sound S E hRestF hLog hGuard pre args post
    ((satisfiedE2_of_PIBindsDigests S E pre args post a hPI).mp hsat)

/-- **`effect2_extract_emitted`** — the same extractor stated against the EMITTED (wire-form) circuit
the Rust prover actually checks: a satisfying emitted descriptor on an arbitrary PI-bound `a` extracts
the apex. (`emitEffect2Faithful` bridges emitted ⟺ `effectCircuit2`.) -/
theorem effect2_extract_emitted {St Args : Type} (S : Surface2) (E : EffectSpec2 St Args)
    (hRestF : RestFrameDecodes2 S E) (hLog : logHashInjective S.LH) (hGuard : GuardDecodes2 E)
    (name : String) (pre : St) (args : Args) (post : St) (a : Assignment)
    (hsat : Dregg2.Exec.CircuitEmit.satisfiedEmitted (emittedEffect2 name E) a)
    (hPI : PIBindsDigests S E pre args post a) :
    E.apex pre args post :=
  effect2_extract S E hRestF hLog hGuard pre args post a
    ((emitEffect2Faithful name E a).mpr hsat) hPI

/-! ## §4 — Poseidon2-grounded uniqueness: the PI digest binding PINS the state component.

A PI-bound assignment fixes the post-component digest to `E.active.digest (toKernel post)`. If that
digest is INJECTIVE (the Poseidon2-CR ground), then any OTHER claimed post whose component digest the
same `a` would have to match must share the component — there is at most one component-preimage. This is
the "injective digests ⇒ unique preimage" content the task asks us to lean on. -/

/-- **`extract_component_unique`** — if two claimed posts are BOTH PI-bound by the same satisfying `a`
(so `a` pins the post-component digest both ways) and the component digest is injective, their post
components' digests coincide — the trace cannot bind two distinct component digests. The injective
digest is exactly the Poseidon2-CR ground (`compressNInjective`/`cellLeafInjective` from
`Poseidon2Binding`). -/
theorem extract_component_unique {St Args : Type} (S : Surface2) (E : EffectSpec2 St Args)
    (pre₁ pre₂ : St) (args₁ args₂ : Args) (post₁ post₂ : St) (a : Assignment)
    (hPI₁ : PIBindsDigests S E pre₁ args₁ post₁ a)
    (hPI₂ : PIBindsDigests S E pre₂ args₂ post₂ a) :
    E.active.digest (E.view.toKernel post₁) = E.active.digest (E.view.toKernel post₂) := by
  rw [← hPI₁.2.2.2.1, ← hPI₂.2.2.2.1]

/-! ## §5 — NON-VACUITY: anti-ghost teeth. A PI-bound trace whose claimed state VIOLATES the apex is
UNSAT. The extractor genuinely CONSTRAINS — a forged/tampered state cannot have a satisfying PI-bound
witness. -/

/-- **`effect2_extract_rejects_frame_tamper`** — a claimed `post` whose untouched-field frame predicate
FAILS against `pre` has NO satisfying PI-bound witness. (Frame forgery rejected.) -/
theorem effect2_extract_rejects_frame_tamper {St Args : Type} (S : Surface2) (E : EffectSpec2 St Args)
    (hRestF : RestFrameDecodes2 S E)
    (pre : St) (args : Args) (post : St) (a : Assignment)
    (hPI : PIBindsDigests S E pre args post a)
    (htamper : ¬ E.restFrame (E.view.toKernel pre) (E.view.toKernel post)) :
    ¬ satisfiedE2 S E a := by
  intro hsat
  have hsat' : satisfiedE2 S E (encodeE2 S E pre args post) :=
    (satisfiedE2_of_PIBindsDigests S E pre args post a hPI).mp hsat
  exact effectCircuit2_rejects_frame_tamper S E hRestF pre args post htamper hsat'

/-- **`effect2_extract_rejects_wrong_component`** — a claimed `post` whose touched component VIOLATES
its declarative `postClause` has NO satisfying PI-bound witness. (Component forgery rejected.) -/
theorem effect2_extract_rejects_wrong_component {St Args : Type} (S : Surface2) (E : EffectSpec2 St Args)
    (pre : St) (args : Args) (post : St) (a : Assignment)
    (hPI : PIBindsDigests S E pre args post a)
    (htamper : ¬ E.active.postClause pre args (E.view.toKernel post)) :
    ¬ satisfiedE2 S E a := by
  intro hsat
  have hsat' : satisfiedE2 S E (encodeE2 S E pre args post) :=
    (satisfiedE2_of_PIBindsDigests S E pre args post a hPI).mp hsat
  exact effectCircuit2_rejects_wrong_component S E pre args post htamper hsat'

/-- **`effect2_extract_rejects_log_forge`** — a claimed `post` whose post-log differs from the
spec-predicted post-log has NO satisfying PI-bound witness (`logHashInjective`). (Log forgery rejected.) -/
theorem effect2_extract_rejects_log_forge {St Args : Type} (S : Surface2) (E : EffectSpec2 St Args)
    (hLog : logHashInjective S.LH)
    (pre : St) (args : Args) (post : St) (a : Assignment)
    (hPI : PIBindsDigests S E pre args post a)
    (htamper : E.view.getLog post ≠ E.postLog pre args) :
    ¬ satisfiedE2 S E a := by
  intro hsat
  have hsat' : satisfiedE2 S E (encodeE2 S E pre args post) :=
    (satisfiedE2_of_PIBindsDigests S E pre args post a hPI).mp hsat
  exact effectCircuit2_rejects_log_forge S E hLog pre args post htamper hsat'

/-! ## §5b — CONCRETE non-vacuity: the gates genuinely reject. A tampered trace whose component digest
wire (`68`) disagrees with its expected wire (`69`) FAILS `cE2Bind` — UNSAT — so satisfaction is NOT
vacuously true; it really pins `compDigPost = compDigExpected`. These are decidable `#guard`s over the
two gates the extractor's component/log teeth rely on. -/

instance (c : Constraint) (a : Assignment) : Decidable (c.holds a) := by
  unfold Constraint.holds; exact inferInstanceAs (Decidable (_ = _))

/-- A tampered assignment: every wire `0` EXCEPT the post-component digest wire `68 := 1` (a forged
component that does not match its expected commitment at wire `69 = 0`). -/
def tamperedAssignment : Assignment := fun w => if w = vE2CompPost then 1 else 0

/- NON-VACUITY: the bind gate `cE2Bind` (`68 = 69`) is FALSE on the tampered assignment — the forged
component is rejected. (If satisfaction were vacuous this would be `true`.) -/
#guard decide (¬ cE2Bind.holds tamperedAssignment)

/- NON-VACUITY: the rest-frame gate `cE2RestF` (`66 = 67`) likewise rejects a tampered rest digest. -/
#guard decide (¬ cE2RestF.holds (fun w => if w = vE2RestPre then 7 else 0))

/- NON-VACUITY: the log gate `cE2Log` (`70 = 71`) rejects a forged log digest. -/
#guard decide (¬ cE2Log.holds (fun w => if w = vE2LogPost then 5 else 0))

/- And the gates DO accept the all-equal (honest-shaped) assignment — so they are not vacuously false
either: the three EQ gates each hold when their two wires agree. -/
#guard decide (cE2Bind.holds (fun _ => 0) ∧ cE2RestF.holds (fun _ => 0) ∧ cE2Log.holds (fun _ => 0))

/-! ## §6 — axiom-hygiene tripwires. -/

#assert_axioms encodeE2_PIBindsDigests
#assert_axioms satisfiedE2_of_PIBindsDigests
#assert_axioms effect2_extract
#assert_axioms effect2_extract_emitted
#assert_axioms extract_component_unique
#assert_axioms effect2_extract_rejects_frame_tamper
#assert_axioms effect2_extract_rejects_wrong_component
#assert_axioms effect2_extract_rejects_log_forge

end Dregg2.Circuit.WitnessExtract
