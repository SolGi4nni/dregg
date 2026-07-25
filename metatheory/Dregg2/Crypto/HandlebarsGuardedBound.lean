/-
# Dregg2.Crypto.HandlebarsGuardedBound — the verifier BOUND to the template and the OUTPUT.

`Crypto/HandlebarsGuardedWitness.lean` ships `guardedVerify (_T) (witness) := witness.all (fun e =>
derives e.data e.guard)`. Its `_T` is DISCARDED and no output is ever mentioned, so what it decides is
"every entry's data derives THE ENTRY'S OWN declared guard". Against an HONEST prover that is exactly
`guardedSafe` (`guardedVerify_iff`), and `guardedWitness_sound` is a true theorem — but BOTH sides of
that iff quantify over an honest `d`. There is no statement there about an ARBITRARY prover-supplied
witness, and there cannot be: a witness listing convenient `(guard, data)` pairs — pairs for a
DIFFERENT template, or pairs with no relation to any presented output — satisfies `witness.all` and is
ACCEPTED. §5 exhibits both attacks and proves them.

This module closes that scope hole. `guardedVerifyBound T output witness` is a Bool-valued verifier
that takes the template AND the presented output, and it discharges the statement the old one lacked:

    guardedVerifyBound T output witness = true → ∃ d, guardedSafe T d ∧ render T d = output

for an ARBITRARY `witness` — quantified over the prover's input, with NO honest `d` assumed anywhere.

## What the bound verifier checks (three teeth, each closing one leak)

1. **hole coverage** — `witness.map HoleEntry.id = holeIds T.segments`: the witness names exactly
   `T`'s holes, in `T`'s order. A certificate assembled for a different template is rejected here.
2. **`T`'s guards, not the witness's** — `guardsHold`: for every `GSeg.hole id g ∈ T.segments`, the
   verifier re-runs `derives (witnessAssign witness id) g` where `g` is read off **`T`**. The witness's
   own `guard` field is never consulted; `guardedVerifyBound_guard_irrelevant` PROVES the verdict is a
   function of the `(id, data)` projection alone, so "declare a permissive guard" buys the adversary
   nothing. (A syntactic `guard = T`'s-guard equality test is NOT available: `PredRE` embeds the whole
   `Pred`/`StateConstraint` catalog and carries no `DecidableEq` in-tree — `deriving instance
   DecidableEq for PredRE` fails. Re-running `T`'s guard is strictly stronger than comparing the
   declared one anyway: it does not merely detect a substituted guard, it ignores it.)
3. **binding to the OUTPUT** — `wordBeq (render T (witnessAssign witness)) output`: the witness's data,
   read back as an assignment, must RECONSTRUCT the presented word. This is the tooth the old verifier
   has none of. Decided by the in-tree structural `Value.beq` (`Exec/PredAlgebra.lean`, sound+complete
   via `Value.beq_iff`), lifted to words as `wordBeq` / `wordBeq_iff`.

## What is proven (sorry-free)

* `guardedVerifyBound_sound` — ⚑ THE THEOREM the old verifier lacked, for an ARBITRARY witness:
  acceptance yields guard-satisfying per-hole data whose render IS the presented output. The witness
  is `d`'s only source; the theorem's `d` is the COMPUTABLE `witnessAssign witness`.
* `guardedVerifyBound_mem_language` — the corollary through `guarded_render_mem_language`: an accepted
  `(output, witness)` puts `output` in `(guardedToGrammar T).language`.
* `guardedVerifyBound_complete` — the spec is NOT weakened: the honest prover's own certificate,
  presented with its own render, is accepted iff `guardedSafe T d`. **No side conditions** — not
  `Nodup`, not `Separated`. (Contrast `HandlebarsGuardedParse.parse_exists_distinct_holes`, which
  extracts a `d` from a bare membership PROOF and genuinely needs `(holesOf T).Nodup`. Here the prover
  hands over the data, so nothing has to be recovered by parsing; see §6.)
* `guardedVerifyBound_guard_irrelevant` — the verdict does not read the witness's declared guards.
* §5 `scope_hole_was_real` / `scope_hole_forged_guard` — ⚑ the ADVERSARIAL CANARY as THEOREMS (plus
  the `#guard` Bool evaluations the lane asked for): witnesses that the OLD `guardedVerify` ACCEPTS
  and the new bound verifier REJECTS — one presented next to an output NO assignment can render at
  all, one forging a permissive guard for a strictly-guarded hole. The hole was real; it is closed.

Axiom hygiene: `#assert_all_clean` in §7. New file; it only ADDS to the guarded stack.
-/
import Dregg2.Crypto.HandlebarsGuardedWitness
import Dregg2.Crypto.HandlebarsGuardedParse
import Dregg2.Tactics

namespace Dregg2.Crypto.HandlebarsGuardedBound

open Dregg2.Exec
open Dregg2.Exec.PredAlgebra
open Dregg2.Crypto.Deriv
open Dregg2.Crypto.Deriv.PredRE
open Dregg2.Crypto.HandlebarsGuarded
open Dregg2.Crypto.HandlebarsGuardedWitness
open Dregg2.Crypto.HandlebarsGuardedUniqueness (holeIds holesOf)
open Dregg2.Crypto.HandlebarsGuardedParse (mem_holeIds render_congr)

/-! ## §1 Deciding word equality — the missing tooth's decision procedure.

`Value` derives `Repr` only; there is no `DecidableEq Value` in-tree (`deriving instance DecidableEq
for Value` does not apply — the nested `List (FieldName × Value)`). `Exec/PredAlgebra.lean` already
supplies the structural `Value.beq` together with its soundness+completeness `Value.beq_iff`; we lift
it to words. -/

/-- **`wordBeq u v`** — structural equality of `Value` words, entry-wise `Value.beq`. -/
def wordBeq : List Value → List Value → Bool
  | [],      []      => true
  | a :: as, b :: bs => Value.beq a b && wordBeq as bs
  | _,       _       => false

/-- **`wordBeq_iff`** — the word equality is sound AND complete: it decides propositional equality of
`Value` words exactly. (Soundness is what the bound verifier needs; completeness is what keeps the
honest prover from being rejected.) -/
theorem wordBeq_iff : ∀ u v : List Value, wordBeq u v = true ↔ u = v
  | [],      []      => by simp [wordBeq]
  | [],      _ :: _  => by simp [wordBeq]
  | _ :: _,  []      => by simp [wordBeq]
  | a :: as, b :: bs => by
      simp only [wordBeq, Bool.and_eq_true, List.cons.injEq, Value.beq_iff a b, wordBeq_iff as bs]

/-! ## §2 Reading an assignment OFF the witness, and re-running `T`'s OWN guards. -/

/-- **`witnessAssign witness`** — the hole assignment the witness commits to: hole `i` gets the data
of the FIRST entry naming `i`; an unnamed id gets the empty word. Computable, so the `d` the soundness
theorem produces can be RUN. -/
def witnessAssign : List HoleEntry → Nat → List Value
  | [],       _ => []
  | e :: rest, i => if i = e.id then e.data else witnessAssign rest i

/-- **`guardsHold d segs`** — re-run each hole's guard AS WRITTEN IN THE SEGMENT LIST on `d`'s data.
The guard comes from the TEMPLATE; nothing here reads a prover-declared guard. -/
def guardsHold (d : Nat → List Value) : List GSeg → Bool
  | []                => true
  | .lit _ :: rest    => guardsHold d rest
  | .hole id g :: rest => derives (d id) g && guardsHold d rest

/-- `guardsHold` decides exactly the per-hole obligation of `guardedSafe`. -/
theorem guardsHold_iff (d : Nat → List Value) : ∀ segs : List GSeg,
    guardsHold d segs = true ↔ ∀ id g, GSeg.hole id g ∈ segs → derives (d id) g = true
  | [] => by simp [guardsHold]
  | .lit t :: rest => by
      simp only [guardsHold, guardsHold_iff d rest]
      constructor
      · intro h id g hmem
        rcases List.mem_cons.mp hmem with heq | hin
        · exact absurd heq (by simp)
        · exact h id g hin
      · intro h id g hmem; exact h id g (List.mem_cons_of_mem _ hmem)
  | .hole id0 g0 :: rest => by
      simp only [guardsHold, Bool.and_eq_true, guardsHold_iff d rest]
      constructor
      · rintro ⟨h0, hrest⟩ id g hmem
        rcases List.mem_cons.mp hmem with heq | hin
        · simp only [GSeg.hole.injEq] at heq
          obtain ⟨rfl, rfl⟩ := heq
          exact h0
        · exact hrest id g hin
      · intro h
        exact ⟨h id0 g0 (by simp), fun id g hmem => h id g (List.mem_cons_of_mem _ hmem)⟩

/-! ## §3 THE BOUND VERIFIER. -/

/-- **`guardedVerifyBound T output witness`** — the verifier the stack was missing: it consumes the
TEMPLATE, the PRESENTED OUTPUT, and an ARBITRARY prover-supplied witness, and accepts only when

1. the witness names exactly `T`'s holes in `T`'s order (`holeIds`), and
2. every hole's data satisfies **`T`'s own** guard (re-run by the verified matcher `derives`), and
3. the witness's data, read back as an assignment, RECONSTRUCTS the presented `output`.

Contrast `HandlebarsGuardedWitness.guardedVerify`, which drops (1) and (3) entirely and reads the
guard off the WITNESS rather than off `T` in (2). -/
def guardedVerifyBound (T : GuardedTemplate) (output : List Value)
    (witness : List HoleEntry) : Bool :=
  (witness.map HoleEntry.id == holeIds T.segments)
    && guardsHold (witnessAssign witness) T.segments
    && wordBeq (render T (witnessAssign witness)) output

/-- Tooth 1, extracted: an accepted witness names exactly `T`'s holes, in order. -/
theorem guardedVerifyBound_ids {T : GuardedTemplate} {output : List Value}
    {witness : List HoleEntry} (h : guardedVerifyBound T output witness = true) :
    witness.map HoleEntry.id = holeIds T.segments := by
  simp only [guardedVerifyBound, Bool.and_eq_true, beq_iff_eq] at h
  exact h.1.1

/-- Tooth 2, extracted: the assignment the witness commits to satisfies `T`'s OWN guards. -/
theorem guardedVerifyBound_safe {T : GuardedTemplate} {output : List Value}
    {witness : List HoleEntry} (h : guardedVerifyBound T output witness = true) :
    guardedSafe T (witnessAssign witness) := by
  simp only [guardedVerifyBound, Bool.and_eq_true] at h
  exact (guardsHold_iff _ T.segments).mp h.1.2

/-- Tooth 3, extracted: the assignment the witness commits to RECONSTRUCTS the presented output. -/
theorem guardedVerifyBound_render {T : GuardedTemplate} {output : List Value}
    {witness : List HoleEntry} (h : guardedVerifyBound T output witness = true) :
    render T (witnessAssign witness) = output := by
  simp only [guardedVerifyBound, Bool.and_eq_true] at h
  exact (wordBeq_iff _ _).mp h.2

/-- ⚑ **`guardedVerifyBound_sound`** — THE THEOREM `guardedVerify` DOES NOT HAVE. For an ARBITRARY
prover-supplied `witness` (no honest `d` assumed, nowhere quantified), acceptance PROVES that the
presented `output` is an expansion of `T` under `T`'s own guards: there EXISTS per-hole data, each
piece satisfying its hole's guard as decided by the verified matcher, whose render is exactly
`output`. The `d` is not conjured — it is the computable `witnessAssign witness`.

This is the statement `guardedVerify_iff` cannot make: that iff has an honest `d` on BOTH sides, and
its verifier sees neither `T` nor `output`. -/
theorem guardedVerifyBound_sound (T : GuardedTemplate) (output : List Value)
    (witness : List HoleEntry) (h : guardedVerifyBound T output witness = true) :
    ∃ d : Nat → List Value, guardedSafe T d ∧ render T d = output :=
  ⟨witnessAssign witness, guardedVerifyBound_safe h, guardedVerifyBound_render h⟩

/-- The corollary in the language register: an accepted `(output, witness)` puts `output` in the
template's induced language — now for an ARBITRARY witness, where `guardedWitness_sound` needed the
honest `d`. -/
theorem guardedVerifyBound_mem_language (T : GuardedTemplate) (output : List Value)
    (witness : List HoleEntry) (h : guardedVerifyBound T output witness = true) :
    output ∈ (guardedToGrammar T).language := by
  obtain ⟨d, hsafe, hr⟩ := guardedVerifyBound_sound T output witness h
  exact hr ▸ guarded_render_mem_language T d hsafe

/-- **The declared guards are IGNORED.** The verdict is a function of the witness's `(id, data)`
projection alone, so an adversary's freedom to write whatever `guard` it likes into the certificate
buys it exactly nothing — the check is against `T`'s guards. (This is what replaces an unavailable
syntactic `PredRE` equality test; see the header.) -/
theorem guardedVerifyBound_guard_irrelevant (T : GuardedTemplate) (output : List Value) :
    ∀ w w' : List HoleEntry,
      w.map (fun e => (e.id, e.data)) = w'.map (fun e => (e.id, e.data)) →
      guardedVerifyBound T output w = guardedVerifyBound T output w' := by
  have key : ∀ w w' : List HoleEntry,
      w.map (fun e => (e.id, e.data)) = w'.map (fun e => (e.id, e.data)) →
      w.map HoleEntry.id = w'.map HoleEntry.id ∧ witnessAssign w = witnessAssign w' := by
    intro w
    induction w with
    | nil =>
        intro w' h
        cases w' with
        | nil => exact ⟨rfl, rfl⟩
        | cons e' r' => exact absurd h (by simp)
    | cons e r ih =>
        intro w' h
        cases w' with
        | nil => exact absurd h (by simp)
        | cons e' r' =>
            simp only [List.map_cons, List.cons.injEq, Prod.mk.injEq] at h
            obtain ⟨⟨hid, hdata⟩, hrest⟩ := h
            obtain ⟨hids, hassign⟩ := ih r' hrest
            refine ⟨by simp only [List.map_cons, hid, hids], ?_⟩
            funext i
            simp only [witnessAssign, hid, hdata, hassign]
  intro w w' h
  obtain ⟨hids, hassign⟩ := key w w' h
  simp only [guardedVerifyBound, hids, hassign]

/-! ## §4 COMPLETENESS — the honest prover is still accepted, with NO side conditions. -/

/-- The honest certificate names exactly the template's holes, in order. -/
theorem map_id_guardedWitness (d : Nat → List Value) :
    ∀ segs : List GSeg, (holeEntries d segs).map HoleEntry.id = holeIds segs
  | []                 => rfl
  | .lit _ :: rest     => by
      simpa only [holeEntries, holeIds] using map_id_guardedWitness d rest
  | .hole id g :: rest => by
      simp only [holeEntries, holeIds, List.map_cons]
      rw [map_id_guardedWitness d rest]

/-- Reading the honest certificate back recovers the honest data on every hole the template names. -/
theorem witnessAssign_holeEntries (d : Nat → List Value) :
    ∀ (segs : List GSeg) (i : Nat), i ∈ holeIds segs → witnessAssign (holeEntries d segs) i = d i
  | [], i, hi => absurd hi (by simp [holeIds])
  | .lit _ :: rest, i, hi => by
      simpa only [holeEntries] using
        witnessAssign_holeEntries d rest i (by simpa only [holeIds] using hi)
  | .hole id0 g0 :: rest, i, hi => by
      by_cases hEq : i = id0
      · subst hEq
        simp [holeEntries, witnessAssign]
      · have hi' : i ∈ holeIds rest := by
          simp only [holeIds, List.mem_cons] at hi
          exact hi.resolve_left hEq
        simp only [holeEntries, witnessAssign, if_neg hEq]
        exact witnessAssign_holeEntries d rest i hi'

/-- **`guardedVerifyBound_complete`** — the strengthening does NOT weaken the spec: the honest prover's
own certificate, presented alongside its own render, is accepted EXACTLY when the data is
guard-satisfying. So `guardedVerifyBound` is a drop-in for `guardedVerify` on honest traffic while
being sound on adversarial traffic.

Note the absence of side conditions: no `(holesOf T).Nodup`, no `SeparatedTemplate`. Those are needed
to RECOVER data from a bare output (`HandlebarsGuardedParse`); here the prover supplies the data and
the verifier only has to re-render it. -/
theorem guardedVerifyBound_complete (T : GuardedTemplate) (d : Nat → List Value) :
    guardedVerifyBound T (render T d) (guardedWitness T d) = true ↔ guardedSafe T d := by
  have hagree : ∀ i ∈ holeIds T.segments,
      witnessAssign (guardedWitness T d) i = d i :=
    fun i hi => witnessAssign_holeEntries d T.segments i hi
  have hrender : render T (witnessAssign (guardedWitness T d)) = render T d :=
    render_congr _ d T.segments hagree
  have hids : (guardedWitness T d).map HoleEntry.id = holeIds T.segments :=
    map_id_guardedWitness d T.segments
  simp only [guardedVerifyBound, Bool.and_eq_true, beq_iff_eq, hids, guardsHold_iff,
    wordBeq_iff, hrender, true_and, and_true]
  constructor
  · intro h id g hmem
    rw [← hagree id (mem_holeIds hmem)]
    exact h id g hmem
  · intro h id g hmem
    rw [hagree id (mem_holeIds hmem)]
    exact h id g hmem

/-! ## §5 ⚑ THE ADVERSARIAL CANARY — witnesses the OLD verifier accepts and the NEW one rejects.

Two independent attacks on `guardedVerify`, each proved (not merely `#guard`-ed):

* **§5.1 output-unbinding** — the certificate is HONEST for `demoT`, but it is presented next to an
  output that NO assignment of `demoT` can render (the empty word: every render of `demoT` starts with
  the literal `data`). `guardedVerify` accepts it because it never looks at an output.
* **§5.2 guard forgery** — the certificate declares the PERMISSIVE guard `star any` for hole 0, whose
  TEMPLATE guard is the strict `noDoubleBraceRE`, and fills it with a DOUBLE brace.
  `guardedVerify` accepts it because it reads the guard off the WITNESS.
-/

namespace Canary

open Dregg2.Crypto.HandlebarsGuarded.Demo

/-- The render of `demoT` always begins with the pinned literal `data`. -/
theorem render_demoT (d : Nat → List Value) :
    render demoT d = dataVal :: (d 0 ++ dataVal :: d 1) := by
  simp only [render, demoT, List.flatMap_cons, List.flatMap_nil, renderSeg,
    List.append_nil, List.cons_append, List.nil_append]

/-! ### §5.1 The output-unbinding attack. -/

/-- No assignment of `demoT` — guard-satisfying or otherwise — renders the EMPTY word. -/
theorem no_render_is_nil : ¬ ∃ d : Nat → List Value, guardedSafe demoT d ∧ render demoT d = [] := by
  rintro ⟨d, -, hr⟩
  rw [render_demoT d] at hr
  exact absurd hr (by simp)

/-- ⚑ **`scope_hole_was_real`** — THE CANARY, as a theorem. The OLD `guardedVerify` ACCEPTS the honest
`demoT` certificate; the same certificate presented next to the empty output is REJECTED by
`guardedVerifyBound` — and it MUST be, because nothing renders the empty word. The rejection is
derived FROM `guardedVerifyBound_sound`: if the bound verifier accepted, soundness would hand back an
assignment rendering `[]`, contradicting `no_render_is_nil`. So the hole the old verifier left (accept
a certificate with no relation to the presented output) is closed by construction, not by inspection. -/
theorem scope_hole_was_real :
    ∃ (T : GuardedTemplate) (output : List Value) (witness : List HoleEntry),
      guardedVerify T witness = true ∧
      (¬ ∃ d : Nat → List Value, guardedSafe T d ∧ render T d = output) ∧
      guardedVerifyBound T output witness = false := by
  refine ⟨demoT, [], guardedWitness demoT demoD, Demo.demo_verify, no_render_is_nil, ?_⟩
  cases hb : guardedVerifyBound demoT [] (guardedWitness demoT demoD) with
  | false => rfl
  | true => exact absurd (guardedVerifyBound_sound _ _ _ hb) no_render_is_nil

/-! ### §5.2 The guard-forgery attack. -/

/-- The FORGED certificate: it names `demoT`'s holes `[0, 1]` correctly, but DECLARES the permissive
`star any` guard for hole 0 — whose TEMPLATE guard is the strict `noDoubleBraceRE` — and fills that
hole with a DOUBLE brace, which the template guard forbids. -/
def forgedWitness : List HoleEntry :=
  [ ⟨0, .star PredRE.any, [braceVal, braceVal]⟩,
    ⟨1, .star PredRE.any, [braceVal, braceVal]⟩ ]

/-- The word the forged certificate reconstructs (so the output-binding tooth alone would NOT catch
it — the guard tooth must). -/
def forgedOut : List Value := [dataVal, braceVal, braceVal, dataVal, braceVal, braceVal]

/-- A double brace is REJECTED by the strict template guard — routed through the matcher
characterization, not through kernel `decide`. -/
theorem derives_bb_noDoubleBraceRE : derives [braceVal, braceVal] noDoubleBraceRE = false := by
  have hadj : hasAdjB [braceVal, braceVal] :=
    ⟨[], braceVal, braceVal, [], rfl, leaf_braceP_brace, leaf_braceP_brace⟩
  have := (noDoubleBraceRE_via_matcher [braceVal, braceVal]).not.mpr (by simpa using hadj)
  simpa using this

/-- The OLD verifier ACCEPTS the forgery: every entry's data derives the entry's OWN declared guard,
and `star any` admits everything. -/
theorem forged_old_accepted : guardedVerify demoT forgedWitness = true := by
  simp only [guardedVerify, forgedWitness, List.all_cons, List.all_nil, Bool.and_true]
  exact Bool.and_eq_true _ _ ▸ ⟨derives_star_any _, derives_star_any _⟩

/-- ⚑ The NEW verifier REJECTS the forgery: it re-runs `T`'s OWN hole-0 guard `noDoubleBraceRE` on the
double brace, which fails. The declared `star any` is never read. -/
theorem forged_new_rejected : guardedVerifyBound demoT forgedOut forgedWitness = false := by
  have hassign : witnessAssign forgedWitness 0 = [braceVal, braceVal] := rfl
  have hguards : guardsHold (witnessAssign forgedWitness) demoT.segments = false := by
    simp only [demoT, guardsHold, hassign, derives_bb_noDoubleBraceRE, Bool.false_and]
  simp only [guardedVerifyBound, hguards, Bool.and_false, Bool.false_and]

/-- ⚑ **`scope_hole_forged_guard`** — the second canary as a theorem: a certificate the OLD verifier
accepts, the NEW one rejects, on the GUARD tooth (its data does reconstruct a well-formed word, so the
output tooth alone would let it through). -/
theorem scope_hole_forged_guard :
    ∃ (T : GuardedTemplate) (output : List Value) (witness : List HoleEntry),
      guardedVerify T witness = true ∧ guardedVerifyBound T output witness = false :=
  ⟨demoT, forgedOut, forgedWitness, forged_old_accepted, forged_new_rejected⟩

/-! ### The same split, as COMPILED Bool evaluations.

⚠ LABEL: `#guard` is COMPILED EVALUATION of a `Bool`; it proves NO `Prop`. The propositional content
is §5.1/§5.2 above; these lines pin that the SHIPPED (compiled) verifier agrees with the kernel proofs
— they are the executable readout, not the argument. -/

-- The old verifier accepts BOTH forgeries; the new one rejects both. Same witnesses as above.
#guard guardedVerify demoT (guardedWitness demoT demoD) = true          -- old: accepts (no output!)
#guard guardedVerifyBound demoT [] (guardedWitness demoT demoD) = false -- new: rejects (unbound)
#guard guardedVerify demoT forgedWitness = true                         -- old: accepts (forged guard)
#guard guardedVerifyBound demoT forgedOut forgedWitness = false         -- new: rejects (T's guard)

-- ...and it is precisely the GUARD tooth that rejects the forgery: the other two teeth PASS on it
-- (its ids are `demoT`'s, and its data does reconstruct `forgedOut`), so the rejection cannot be
-- attributed to a coverage or output mismatch.
#guard (forgedWitness.map HoleEntry.id == holeIds demoT.segments) = true
#guard wordBeq (render demoT (witnessAssign forgedWitness)) forgedOut = true
#guard guardsHold (witnessAssign forgedWitness) demoT.segments = false

-- A third leak the coverage tooth closes: a certificate assembled for a DIFFERENT template (holes
-- `[5, 6]`, unrelated to `demoT`'s `[0, 1]`) is accepted by the old verifier, rejected by the new.
def alienWitness : List HoleEntry :=
  [ ⟨5, .star PredRE.any, [dataVal]⟩, ⟨6, .star PredRE.any, [dataVal]⟩ ]

#guard guardedVerify demoT alienWitness = true
#guard guardedVerifyBound demoT [dataVal, dataVal] alienWitness = false

-- And the HONEST traffic still passes the bound verifier (the completeness side, executably).
#guard guardedVerifyBound demoT (render demoT demoD) (guardedWitness demoT demoD) = true

end Canary

/-! ## §6 The honest positive instance — the bound verifier accepts the honest certificate.

Proved through `guardedVerifyBound_complete` and the already-proven `demoD_guardedSafe`, NOT by
kernel `decide` (which stalls on the `String` field-name compare inside `Pred.eval`). -/

namespace Positive

open Dregg2.Crypto.HandlebarsGuarded.Demo

/-- The bound verifier ACCEPTS the honest `(output, witness)` pair. -/
theorem demo_bound_verify :
    guardedVerifyBound demoT (render demoT demoD) (guardedWitness demoT demoD) = true :=
  (guardedVerifyBound_complete demoT demoD).mpr demoD_guardedSafe

/-- ...and the acceptance PROVES membership through the arbitrary-witness route (the witness is
consumed as an arbitrary one; nothing about `demoD` is used past this point). -/
theorem demo_bound_mem_language :
    render demoT demoD ∈ (guardedToGrammar demoT).language :=
  guardedVerifyBound_mem_language demoT _ _ demo_bound_verify

end Positive

/-! ## §7 Axiom hygiene. -/

#assert_all_clean [wordBeq_iff, guardsHold_iff, guardedVerifyBound_sound,
  guardedVerifyBound_mem_language, guardedVerifyBound_complete,
  guardedVerifyBound_guard_irrelevant, Canary.scope_hole_was_real,
  Canary.scope_hole_forged_guard, Positive.demo_bound_verify,
  Positive.demo_bound_mem_language]

/-! ## §8 What this does and does NOT close (stated at the current resolution).

CLOSED. The scope hole named in `HandlebarsGuardedWitness.lean`'s `guardedVerify` docstring: there is
now a verifier whose acceptance, for an ARBITRARY prover-supplied witness, entails
`∃ d, guardedSafe T d ∧ render T d = output` (`guardedVerifyBound_sound`), and the two concrete
attacks the docstring described (a witness for a different template / a witness unrelated to any
output) are exhibited as accepted-by-old, rejected-by-new (§5). Completeness holds with NO side
conditions, so nothing honest is lost.

STILL OPEN (named, not `sorry`-ed):

  -- RESIDUAL (membership decider). `guardedVerifyBound` is a verifier for a PROVER-SUPPLIED witness.
  -- It is NOT a decision procedure for `output ∈ (guardedToGrammar T).language` from `(T, output)`
  -- alone: with no witness in hand, one must SEARCH the span decomposition. That is
  -- `HandlebarsGuardedParse` §8's `RESIDUAL (decidable recognizer)`, and THAT route genuinely needs
  -- `(holesOf T).Nodup` (`parse_exists_distinct_holes`) plus separation for uniqueness. The two
  -- objects answer different questions and neither subsumes the other.

  -- RESIDUAL (uniqueness of the recovered data). Soundness gives SOME `d`; it does not say the
  -- witness's `d` is the only one. On a `SeparatedTemplate` with distinct hole ids,
  -- `HandlebarsGuardedParse.separated_parse_exists_unique` supplies that, and composing it with
  -- `guardedVerifyBound_sound` would say "the accepted witness carries THE data" — a follow-on that
  -- inherits both side conditions, which is why it is not folded in here.

  -- RESIDUAL (no template authentication). `guardedVerifyBound` binds a witness to the `T` the
  -- VERIFIER holds. Which `T` that is remains a question for the layer above (a commitment to the
  -- template); nothing here prevents a verifier from being handed the wrong template.

  -- RESIDUAL (junction breakout, inherited). As everywhere in this family, guards are IN-SLOT:
  -- `∈ language` is in-slot confinement, not a byte-level cross-junction guarantee.
-/

end Dregg2.Crypto.HandlebarsGuardedBound
