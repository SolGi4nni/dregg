/-
# Dregg2.Crypto.HandlebarsGuardedWitness — the PROOF-CARRYING SCHEMA INSTANCE.

`Crypto/HandlebarsGuarded.lean` proves generation soundness for GUARD-parametric templates: a hole
carries a `PredRE` guard (a REGULAR LEAF over the infinite `Value` alphabet), and if every hole's
data satisfies ITS OWN guard (`guardedSafe`, decided by the VERIFIED matcher `derives`) the render
lands in the induced language (`guarded_render_mem_language`). `Crypto/HandlebarsWitness.lean`
MATERIALIZES the committed `Tok`-family's generation witness as a leftmost `CfgCompact.Replay` rule
sequence and proves it replays.

This module is the guarded twin — but it does NOT reuse the `Replay` witness, and it is not supposed
to. The guarded grammar is NOT a finite mathlib `ContextFreeGrammar` (the `Value` alphabet is
infinite; each hole is a regular leaf), so there is no leftmost CFG rule sequence to materialize. The
natural certificate here is the **per-hole guard-acceptance record**: for each `GSeg.hole id g` the
pair `(guard g, data d id)` together with the EXECUTABLE matcher run `derives (d id) g` witnessing
that slot admitted its data. Because `derives` is an executable `Bool`, the certificate is checkable
by RE-RUNNING it — no trust. The verifier's replay of the certificate is `guardedVerify`, and an
accepting replay PROVES membership (`guardedWitness_sound`).

This is exactly the CHEAP regular-leaf check of `docs/DESIGN-composed-attestation-architecture.md`:
the witness names, per slot, WHICH regular leaf admitted it — the DFA/regex side of the `regex ⊗ CFG`
substrate, priced per-hole at `derives`, not a pushdown run.

## What is proven (sorry-free)

* `guardedVerify_iff` — the executable per-hole verifier DECIDES `guardedSafe` exactly: re-running
  `derives` on every entry of the honest witness accepts iff every hole's data satisfies its guard.
  The checker the SDK/wasm would call.
* `guardedWitness_sound` — THE KEY THEOREM: an accepting re-check of the certificate
  (`guardedVerify T (guardedWitness T d) = true`) PROVES `render T d ∈ (guardedToGrammar T).language`,
  routed through `guardedVerify_iff` and `guarded_render_mem_language`. The executable derives-replay
  is a SOUND verifier for "template-generated under these guards".
* `Demo` — the two-guard template (`demoT`) with a hole holding `{{`: the honest witness is ACCEPTED
  (`#guard`) and drives `guardedWitness_sound`; a tampered witness whose hole-0 datum violates its
  `noDoubleBraceRE` guard is REJECTED (`#guard`).
-/
import Dregg2.Crypto.HandlebarsGuarded
import Dregg2.Crypto.Deriv.Correctness
import Dregg2.Tactics

namespace Dregg2.Crypto.HandlebarsGuardedWitness

open Dregg2.Exec
open Dregg2.Crypto.Deriv
open Dregg2.Crypto.Deriv.PredRE
open Dregg2.Crypto.HandlebarsGuarded

/-! ## §1 The per-hole certificate — a guard-acceptance record. -/

/-- A **per-hole certificate entry**: the hole's `id`, its `guard` (the regular leaf), and the
`data` placed in the slot. The verifier re-checks the entry by RE-RUNNING `derives data guard` —
the executable matcher decides whether this regular leaf admitted the slot's data. -/
structure HoleEntry where
  id    : Nat
  guard : PredRE
  data  : List Value
  deriving Repr

/-- The per-hole certificate of a segment list: one `HoleEntry` per `GSeg.hole`, carrying its guard
and the rendered slot data. Literals contribute nothing (no guard to check). -/
def holeEntries (d : Nat → List Value) : List GSeg → List HoleEntry
  | []                => []
  | .lit _ :: rest    => holeEntries d rest
  | .hole id g :: rest => ⟨id, g, d id⟩ :: holeEntries d rest

/-- **`guardedWitness T d`** — the certificate the prover puts on the wire: the per-hole list of
`(id, guard, data)` the verifier re-checks by replaying `derives`. -/
def guardedWitness (T : GuardedTemplate) (d : Nat → List Value) : List HoleEntry :=
  holeEntries d T.segments

/-- **`guardedRenderWithProof T d`** — output paired with its per-hole guard-acceptance certificate.
The exact shape a prover emits; the verifier re-runs `guardedVerify` on the second component. -/
def guardedRenderWithProof (T : GuardedTemplate) (d : Nat → List Value) :
    List Value × List HoleEntry :=
  (render T d, guardedWitness T d)

/-- **`guardedVerify T witness`** — the verifier's REPLAY of the certificate: re-run the executable
matcher `derives` on every hole entry. No trust in the prover's claim — the guard-acceptance is
recomputed per slot. (`T` is threaded for signature symmetry with the prover side; the recheck is
entirely determined by the self-describing witness — each entry names its own guard and data.) -/
def guardedVerify (_T : GuardedTemplate) (witness : List HoleEntry) : Bool :=
  witness.all (fun e => derives e.data e.guard)

/-! ## §2 Membership correspondence — the certificate covers exactly the holes. -/

/-- Every hole of the segment list has its entry in the certificate (with the rendered slot data). -/
theorem mem_holeEntries_of_hole (d : Nat → List Value) (id : Nat) (g : PredRE) :
    ∀ segs : List GSeg, GSeg.hole id g ∈ segs →
      (⟨id, g, d id⟩ : HoleEntry) ∈ holeEntries d segs := by
  intro segs
  induction segs with
  | nil => intro h; exact absurd h (by simp)
  | cons seg rest ih =>
      intro h
      rw [List.mem_cons] at h
      cases seg with
      | lit t =>
          rcases h with h | h
          · exact absurd h (by simp)
          · simpa only [holeEntries] using ih h
      | hole id' g' =>
          simp only [holeEntries]
          rcases h with h | h
          · injection h with hid hg; subst hid; subst hg; simp
          · exact List.mem_cons_of_mem _ (ih h)

/-- Conversely, every certificate entry is a genuine hole of the segment list, and its `data` is the
slot's rendered data `d id`. So the certificate neither invents nor drops holes. -/
theorem hole_of_mem_holeEntries (d : Nat → List Value) :
    ∀ (segs : List GSeg) (e : HoleEntry), e ∈ holeEntries d segs →
      GSeg.hole e.id e.guard ∈ segs ∧ e.data = d e.id := by
  intro segs
  induction segs with
  | nil => intro e h; exact absurd h (by simp [holeEntries])
  | cons seg rest ih =>
      intro e h
      cases seg with
      | lit t =>
          simp only [holeEntries] at h
          obtain ⟨hmem, hdata⟩ := ih e h
          exact ⟨List.mem_cons_of_mem _ hmem, hdata⟩
      | hole id' g' =>
          simp only [holeEntries, List.mem_cons] at h
          rcases h with h | h
          · subst h; exact ⟨by simp, rfl⟩
          · obtain ⟨hmem, hdata⟩ := ih e h
            exact ⟨List.mem_cons_of_mem _ hmem, hdata⟩

/-! ## §3 The verifier decides `guardedSafe` exactly. -/

/-- **`guardedVerify_iff`** — the executable per-hole verifier DECIDES `guardedSafe`: replaying
`derives` over the honest certificate accepts iff every hole's data satisfies its own guard. This is
the checker the SDK/wasm calls; its acceptance is EXACTLY the soundness precondition. -/
theorem guardedVerify_iff (T : GuardedTemplate) (d : Nat → List Value) :
    guardedVerify T (guardedWitness T d) = true ↔ guardedSafe T d := by
  simp only [guardedVerify, guardedWitness, guardedSafe, List.all_eq_true]
  constructor
  · intro h id g hmem
    exact h _ (mem_holeEntries_of_hole d id g T.segments hmem)
  · intro h e he
    obtain ⟨hmem, hdata⟩ := hole_of_mem_holeEntries d T.segments e he
    rw [hdata]
    exact h e.id e.guard hmem

/-! ## §4 THE KEY THEOREM — an accepting re-check PROVES membership. -/

/-- **`guardedWitness_sound`** — a SOUND verifier for "template-generated under these guards": if the
verifier's replay of the certificate passes (`guardedVerify T (guardedWitness T d) = true`, i.e. EVERY
per-hole `derives (d id) (guard id)` re-checks), then `guardedSafe T d` holds, hence the render lands
in the induced language `(guardedToGrammar T).language`. The executable per-hole derives-replay is a
sound checker: an accepting re-check of the certificate PROVES membership. -/
theorem guardedWitness_sound (T : GuardedTemplate) (d : Nat → List Value)
    (hv : guardedVerify T (guardedWitness T d) = true) :
    render T d ∈ (guardedToGrammar T).language :=
  guarded_render_mem_language T d ((guardedVerify_iff T d).mp hv)

/-! ## §5 Axiom hygiene. -/

#assert_axioms guardedVerify_iff
#assert_axioms guardedWitness_sound

/-! ## §6 Non-vacuity — the two-guard demo, certified and (tamper-)rejected. -/

namespace Demo

open Dregg2.Crypto.HandlebarsGuarded.Demo

/-- The proof-carrying schema instance for `demoT` filled with `demoD`: the rendered `Value` word
together with its per-hole guard-acceptance certificate. -/
def demoCert : List Value × List HoleEntry := guardedRenderWithProof demoT demoD

/-- The verifier ACCEPTS the honest certificate — proven (not by kernel `decide`, which stalls on the
`String` field-name compare inside `Pred.eval`) by routing the ALREADY-PROVEN `demoD_guardedSafe`
through `guardedVerify_iff`: the executable acceptance and the semantic guard-safety are one fact. -/
theorem demo_verify : guardedVerify demoT (guardedWitness demoT demoD) = true :=
  (guardedVerify_iff demoT demoD).mpr demoD_guardedSafe

/-- **Non-vacuity** — an accepting re-check of the honest certificate PROVES the `{{`-bearing render
lands in the induced language, via `guardedWitness_sound`. (Hole 1 holds a DOUBLE brace, admitted by
its `star any` guard — impossible under the committed `Handlebars.safe` brace-ban.) -/
theorem demo_witness_sound :
    render demoT demoD ∈ (guardedToGrammar demoT).language :=
  guardedWitness_sound demoT demoD demo_verify

/-- A TAMPERED assignment: hole 0's datum is a DOUBLE brace `[{, {]`, which VIOLATES its
`noDoubleBraceRE` guard. Its certificate must be rejected by the executable verifier. -/
def tamperedD : Nat → List Value
  | 0 => [braceVal, braceVal]   -- violates noDoubleBraceRE
  | 1 => [braceVal, braceVal]
  | _ => []

-- The executable verifier ACCEPTS the honest certificate and REJECTS the tampered one (the recheck
-- re-runs `derives` per hole; #guard evaluates the compiled matcher, both polarities pinned).
#guard guardedVerify demoT (guardedWitness demoT demoD) = true       -- honest: accepted
#guard guardedVerify demoT (guardedWitness demoT tamperedD) = false  -- tampered hole 0: rejected

-- The certificate is self-describing: two hole entries, carrying each hole's guard and slot data.
#guard (guardedRenderWithProof demoT demoD).2.length = 2
#guard (guardedWitness demoT demoD).map HoleEntry.id = [0, 1]

#assert_axioms demo_witness_sound

end Demo

/-! ## §7 RESIDUAL — named, not `sorry`-ed.

The certificate proves the GENERATE direction (an accepting re-check ⇒ membership). It says nothing
about parse-uniqueness / the converse (a language member decomposes back to unique per-hole data):
that is the guarded `HandlebarsUniqueness` residual named in `HandlebarsGuarded.lean` §7, which needs
the delimiter-guarded (prefix-free / separated-frame) side-condition — general guards are ambiguous
(two abutting `star any` holes), so a per-hole acceptance certificate neither needs nor supplies it.
As in `HandlebarsWitness.lean` §9, per-hole guards are IN-SLOT: `∈ language` captures in-slot
confinement, not a byte-level cross-junction guarantee. -/

end Dregg2.Crypto.HandlebarsGuardedWitness
