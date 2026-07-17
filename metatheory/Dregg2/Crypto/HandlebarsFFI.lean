/-
# Dregg2.Crypto.HandlebarsFFI — the EXPORTED witness surface: Rust CALLS verified Lean, not a mirror.

`HandlebarsWitness.lean` materializes the generation witness (`renderRules T d`) and PROVES it replays
(`renderRules_accepts : safe T d → ReplayAccepts (handlebarsToGrammar T) (renderRules T d) (render T d)`).
`CfgCompact.lean` gives the pushdown `Replay` — but only as a `Prop` inductive, NOT executable. So today a
Rust verifier must RE-AUTHOR the replay check in `zkoracle-prove/src/cfg.rs` and hope its twin agrees. This
module closes that dual-authoring: it exposes the PROVEN Lean objects across the `@[export] String → String`
ABI (the `dregg_grain_r3_verify` / `dregg_holding_grant_weight` / `dregg_blocklace_finalize` precedent), so
Rust calls the verified code instead of mirroring it.

Two exports:

  * `@[export dregg_render_with_proof] renderWithProofWire` — PROVER side. Parses a template+data wire, runs
    the COMPUTABLE `render`/`renderRules` (already computable; `renderRules_accepts` proves the output for
    every `safe` input IS the accepting witness), and serializes `(output-bytes, ruleSequence)` back. The
    materialized object on the wire is exactly the proven one.

  * `@[export dregg_replay_check] replayCheckWire` — VERIFIER side, and the one genuinely NEW thing:
    `replayCheckB` — a COMPUTABLE decider for the `Prop` `Replay`, with `replayCheckB_iff` proving it decides
    `Replay` EXACTLY (soundness AND completeness). `replayCheckB` runs the pushdown as native code via a fuel
    that is provably enough (`= rs.length + input.length`, the exact step count). The verifier now CALLS this
    proven decider rather than trusting a re-authored Rust `verify_cfg_compact`.

Both fail CLOSED: a malformed prover wire → `"ERR"`, a malformed verifier wire → `"0"`.

`#assert_axioms`-clean (⊆ {propext, Classical.choice, Quot.sound}); the C bridge registration
(`dregg-lean-ffi/src/lean_init.c`, `dregg-lean-ffi/src/lib.rs::lean_string_bridge`) is the NEXT phase and is
NOT touched here. Verified with `lake env lean Dregg2/Crypto/HandlebarsFFI.lean`.
-/
import Dregg2.Crypto.Handlebars
import Dregg2.Crypto.HandlebarsWitness
import Dregg2.Crypto.CfgCompact
import Dregg2.Tactics

namespace Dregg2.Crypto.HandlebarsFFI

open Dregg2.Crypto.Handlebars
open Dregg2.Crypto.HandlebarsWitness
open Dregg2.Crypto.CfgCompact

/-! ## §1 The COMPUTABLE replay decider — a fuelled pushdown twin of the `Prop` `Replay`.

`Replay` (`CfgCompact.lean`) is a `Prop` inductive: it says a run EXISTS, but does not RUN. `replayFuel`
is its executable decider. The pushdown is deterministic given the stack top, so a single left-to-right
walk decides acceptance:

  * empty stack  ⇒ ACCEPT iff both the rule list and the input are exhausted (the `Replay.done` shape);
  * a `terminal t` on top ⇒ the next input token must be `t` (the `Replay.term` step);
  * a `nonterminal A` on top ⇒ the next certificate rule `r` must have `r.input = A` and `r ∈ g.rules`,
    and its output is pushed (the `Replay.rule` step).

The run takes EXACTLY `rs.length` rule-steps + `input.length` terminal-steps, so `fuel = rs.length +
input.length` is provably enough (§2). Structural recursion on the `Nat` fuel gives clean definitional
unfolding — the reason we fuel rather than well-found on the (stack-growing) run. Everything by `decide`
so only `[DecidableEq α]` / `[DecidableEq g.NT]` is needed (no `BEq`). -/

variable {α : Type}

/-- The fuelled pushdown decider. `fuel` bounds the number of steps; `= rs.length + input.length` is the
exact requirement (§2 `replayFuel_iff`). Fail-closed: out of fuel with a non-empty stack ⇒ reject. -/
def replayFuel (g : ContextFreeGrammar α) [DecidableEq α] [DecidableEq g.NT] :
    Nat → List (ContextFreeRule α g.NT) → List α → List (Symbol α g.NT) → Bool
  | _, rs, input, [] => rs.isEmpty && input.isEmpty
  | 0, _, _, _ :: _ => false
  | n + 1, rs, input, Symbol.terminal t :: stk =>
      match input with
      | [] => false
      | a :: rest => decide (a = t) && replayFuel g n rs rest stk
  | n + 1, rs, input, Symbol.nonterminal A :: stk =>
      match rs with
      | [] => false
      | r :: rs' =>
          decide (r.input = A) && decide (r ∈ g.rules) && replayFuel g n rs' input (r.output ++ stk)

/-! ## §2 THE CRUX — `replayFuel` decides `Replay` EXACTLY (soundness AND completeness). -/

/-- **`replayFuel_iff`** — the computable decider agrees with the `Prop` machine on the nose, given enough
fuel: `replayFuel g n rs input stk = true ↔ Replay g rs input stk` whenever `rs.length + input.length ≤ n`.
FORWARD (`→`) is the VERIFIER-CRITICAL half: an accepting decision yields a real `Replay` derivation (so a
Rust `verify_cfg_compact` calling this cannot accept a non-member). BACKWARD (`←`) is completeness: every
real replay is decided `true`. Structural induction on the fuel; each step mirrors one `Replay` constructor.
-/
theorem replayFuel_iff (g : ContextFreeGrammar α) [DecidableEq α] [DecidableEq g.NT] :
    ∀ (n : Nat) (rs : List (ContextFreeRule α g.NT)) (input : List α) (stk : List (Symbol α g.NT)),
      rs.length + input.length ≤ n →
      (replayFuel g n rs input stk = true ↔ Replay g rs input stk) := by
  intro n
  induction n with
  | zero =>
    intro rs input stk hle
    have hrs : rs = [] := by
      cases rs with
      | nil => rfl
      | cons r rs'' => exfalso; simp only [List.length_cons] at hle; omega
    subst hrs
    have hin : input = [] := by
      cases input with
      | nil => rfl
      | cons a rest => exfalso; simp only [List.length_nil, List.length_cons] at hle; omega
    subst hin
    cases stk with
    | nil =>
      simp only [replayFuel, List.isEmpty_nil, Bool.and_self]
      exact ⟨fun _ => Replay.done, fun _ => trivial⟩
    | cons s stk' =>
      cases s with
      | terminal t =>
        simp only [replayFuel]
        exact ⟨fun h => absurd h Bool.false_ne_true, fun h => by cases h⟩
      | nonterminal A =>
        simp only [replayFuel]
        exact ⟨fun h => absurd h Bool.false_ne_true, fun h => by cases h⟩
  | succ n ih =>
    intro rs input stk hle
    cases stk with
    | nil =>
      -- Empty stack: ACCEPT iff both lists are exhausted — exactly `Replay.done`.
      cases rs with
      | cons r rs' =>
        simp only [replayFuel, List.isEmpty_cons, Bool.false_and]
        exact ⟨fun h => absurd h Bool.false_ne_true, fun h => by cases h⟩
      | nil =>
        cases input with
        | cons a rest =>
          simp only [replayFuel, List.isEmpty_nil, List.isEmpty_cons, Bool.true_and]
          exact ⟨fun h => absurd h Bool.false_ne_true, fun h => by cases h⟩
        | nil =>
          simp only [replayFuel, List.isEmpty_nil, Bool.and_self]
          exact ⟨fun _ => Replay.done, fun _ => trivial⟩
    | cons s stk' =>
      cases s with
      | terminal t =>
        cases input with
        | nil =>
          simp only [replayFuel]
          exact ⟨fun h => absurd h Bool.false_ne_true, fun h => by cases h⟩
        | cons a rest =>
          have hle' : rs.length + rest.length ≤ n := by
            simp only [List.length_cons] at hle; omega
          have IH := ih rs rest stk' hle'
          simp only [replayFuel, Bool.and_eq_true, decide_eq_true_eq]
          rw [IH]
          constructor
          · rintro ⟨rfl, hp⟩; exact Replay.term _ hp
          · intro h; cases h with | term _ hp => exact ⟨rfl, hp⟩
      | nonterminal A =>
        cases rs with
        | nil =>
          simp only [replayFuel]
          exact ⟨fun h => absurd h Bool.false_ne_true, fun h => by cases h⟩
        | cons r rs' =>
          have hle' : rs'.length + input.length ≤ n := by
            simp only [List.length_cons] at hle; omega
          have IH := ih rs' input (r.output ++ stk') hle'
          simp only [replayFuel, Bool.and_eq_true, decide_eq_true_eq]
          rw [IH]
          constructor
          · rintro ⟨⟨rfl, hmem⟩, hp⟩; exact Replay.rule hmem hp
          · intro h; cases h with | rule hmem hp => exact ⟨⟨rfl, hmem⟩, hp⟩

/-! ## §3 The decider at exact fuel, and its `ReplayAccepts` specialization. -/

/-- **`replayCheckB`** — the fuel-free computable replay decider: fuel it with exactly `rs.length +
input.length`, the provably-sufficient step count. -/
def replayCheckB (g : ContextFreeGrammar α) [DecidableEq α] [DecidableEq g.NT]
    (rs : List (ContextFreeRule α g.NT)) (input : List α) (stk : List (Symbol α g.NT)) : Bool :=
  replayFuel g (rs.length + input.length) rs input stk

/-- **`replayCheckB_iff`** — the headline: `replayCheckB` decides `Replay` EXACTLY. Immediate from
`replayFuel_iff` at `n = rs.length + input.length` (fuel exactly enough). -/
theorem replayCheckB_iff (g : ContextFreeGrammar α) [DecidableEq α] [DecidableEq g.NT]
    (rs : List (ContextFreeRule α g.NT)) (input : List α) (stk : List (Symbol α g.NT)) :
    replayCheckB g rs input stk = true ↔ Replay g rs input stk :=
  replayFuel_iff g (rs.length + input.length) rs input stk (le_refl _)

/-- **`replayCheckAccepts`** — the decider from the INITIAL stack: the executable twin of `ReplayAccepts`. -/
def replayCheckAccepts (g : ContextFreeGrammar α) [DecidableEq α] [DecidableEq g.NT]
    (rs : List (ContextFreeRule α g.NT)) (input : List α) : Bool :=
  replayCheckB g rs input [Symbol.nonterminal g.initial]

/-- `replayCheckAccepts` decides `ReplayAccepts` exactly. So the exported verifier's `"1"`/`"0"` is the
`ReplayAccepts` truth value — and (via `compact_sound`) a `"1"` PROVES language membership. -/
theorem replayCheckAccepts_iff (g : ContextFreeGrammar α) [DecidableEq α] [DecidableEq g.NT]
    (rs : List (ContextFreeRule α g.NT)) (input : List α) :
    replayCheckAccepts g rs input = true ↔ ReplayAccepts g rs input :=
  replayCheckB_iff g rs input [Symbol.nonterminal g.initial]

#assert_axioms replayFuel_iff
#assert_axioms replayCheckB_iff
#assert_axioms replayCheckAccepts_iff

/-- A `"1"` from the decider PROVES injection-free / language membership: `replayCheckAccepts = true`
carries the accepted certificate through `compact_sound` to `input ∈ g.language`. This is why the export
is a verifier, not a heuristic. -/
theorem replayCheckAccepts_sound (g : ContextFreeGrammar α) [DecidableEq α] [DecidableEq g.NT]
    (rs : List (ContextFreeRule α g.NT)) (input : List α)
    (h : replayCheckAccepts g rs input = true) : input ∈ g.language :=
  compact_sound g rs input ((replayCheckAccepts_iff g rs input).mp h)

#assert_axioms replayCheckAccepts_sound

/-! ## §4 The wire alphabet & the handlebars-grammar `DecidableEq` bridge.

`(handlebarsToGrammar T).NT` is definitionally `NT`, so its `DecidableEq` is `NT`'s — register it so
`replayCheckAccepts (handlebarsToGrammar T) …` resolves its instance. -/

instance instDecEqHbNT (T : HandlebarsTemplate) : DecidableEq (handlebarsToGrammar T).NT :=
  (inferInstance : DecidableEq NT)

/-- Drop the first `n` characters, staying in `String` (this Lean's `String.drop` returns a `Slice`). -/
def sdrop (s : String) (n : Nat) : String := String.ofList (s.toList.drop n)

/-- A `Tok` byte on the wire: `brace ↦ 'B'`, `data ↦ 'D'`. -/
def encTok : Tok → Char
  | .brace => 'B'
  | .data => 'D'

/-- Decode one wire byte to a `Tok` (`'B'`/`'D'`); anything else fails. -/
def decTok : Char → Option Tok
  | 'B' => some Tok.brace
  | 'D' => some Tok.data
  | _ => none

/-- A `List Tok` as a `B`/`D` string. -/
def encToks (l : List Tok) : String := String.ofList (l.map encTok)

/-- A `B`/`D` string back to a `List Tok` (empty string ⇒ `[]`); a stray char fails. -/
def decToks (s : String) : Option (List Tok) := s.toList.mapM decTok

/-! ## §5 Nonterminal / symbol / rule (de)serialization.

Nonterminal: `start ↦ "S"`, `safeD h ↦ "D<h>"`, `safeB h ↦ "B<h>"`. Symbol: `terminal brace ↦ "tB"`,
`terminal data ↦ "tD"`, `nonterminal nt ↦ "n<encNT nt>"`. Rule: `"<encNT input>><csv of encSym output>"`.
Rule list: rules joined by `"|"`. -/

def encNT : NT → String
  | .start => "S"
  | .safeD h => "D" ++ toString h
  | .safeB h => "B" ++ toString h

def decNT (s : String) : Option NT :=
  if s = "S" then some NT.start
  else if s.startsWith "D" then (sdrop s 1).toNat?.map NT.safeD
  else if s.startsWith "B" then (sdrop s 1).toNat?.map NT.safeB
  else none

def encSym : Symbol Tok NT → String
  | .terminal .brace => "tB"
  | .terminal .data => "tD"
  | .nonterminal nt => "n" ++ encNT nt

def decSym (s : String) : Option (Symbol Tok NT) :=
  if s = "tB" then some (Symbol.terminal Tok.brace)
  else if s = "tD" then some (Symbol.terminal Tok.data)
  else if s.startsWith "n" then (decNT (sdrop s 1)).map Symbol.nonterminal
  else none

def encSyms (l : List (Symbol Tok NT)) : String := String.intercalate "," (l.map encSym)

def decSyms (s : String) : Option (List (Symbol Tok NT)) :=
  if s = "" then some [] else (s.splitOn ",").mapM decSym

def encRule (r : ContextFreeRule Tok NT) : String := encNT r.input ++ ">" ++ encSyms r.output

def decRule (s : String) : Option (ContextFreeRule Tok NT) :=
  match s.splitOn ">" with
  | [i, o] => do
      let inp ← decNT i
      let out ← decSyms o
      pure ⟨inp, out⟩
  | _ => none

def encRules (l : List (ContextFreeRule Tok NT)) : String := String.intercalate "|" (l.map encRule)

def decRules (s : String) : Option (List (ContextFreeRule Tok NT)) :=
  if s = "" then some [] else (s.splitOn "|").mapM decRule

/-! ## §6 Template (+ data) (de)serialization.

Segments are `;`-separated. A literal segment is `"L<B/D bytes>"`. A hole segment is `"H<id>"` (structure
only) or `"H<id>:<B/D bytes>"` (id together with its per-hole data). The prover wire carries the data; the
verifier wire needs only the structure (the grammar) and ignores any `:data`. -/

/-- Parse one segment chunk, also surfacing the hole's inline data (as a singleton assoc entry). -/
def parseSeg (s : String) : Option (Segment × List (HoleId × List Tok)) :=
  if s.startsWith "L" then
    (decToks (sdrop s 1)).map (fun toks => (Segment.lit toks, []))
  else if s.startsWith "H" then
    match (sdrop s 1).splitOn ":" with
    | [idStr] => idStr.toNat?.map (fun id => (Segment.hole id, []))
    | [idStr, dataStr] => do
        let id ← idStr.toNat?
        let ds ← decToks dataStr
        pure (Segment.hole id, [(id, ds)])
    | _ => none
  else none

def parseSegs (wire : String) : Option (List (Segment × List (HoleId × List Tok))) :=
  (wire.splitOn ";").mapM parseSeg

/-- Prover-side parse: template PLUS the per-hole data function (`d h = []` for an unlisted hole). -/
def parseTemplateData (wire : String) : Option (HandlebarsTemplate × (HoleId → List Tok)) :=
  (parseSegs wire).map (fun parsed =>
    let T : HandlebarsTemplate := ⟨parsed.map Prod.fst⟩
    let assoc : List (HoleId × List Tok) := parsed.flatMap Prod.snd
    let d : HoleId → List Tok := fun h => (assoc.find? (fun p => p.1 = h)).elim [] Prod.snd
    (T, d))

/-- Verifier-side parse: template STRUCTURE only (the grammar). Any inline `:data` is ignored. -/
def parseTemplate (wire : String) : Option HandlebarsTemplate :=
  (parseSegs wire).map (fun parsed => ⟨parsed.map Prod.fst⟩)

/-! ## §7 THE EXPORTS. -/

/-- **`@[export dregg_render_with_proof]`** — PROVER side. Wire: a template-with-inline-data,
`"L<bytes>;H<id>:<bytes>;…"` (segments `;`-separated; a literal `L<B/D>`, a hole `H<id>:<B/D>`).
Runs the computable `render`/`renderRules` (the PROVEN materialized witness — `renderRules_accepts` holds
for every `safe` input) and serializes `"<output B/D bytes>#<rules>"`, rules being `encRules`. Malformed
wire ⇒ `"ERR"` (fail-closed). Runs the verified Lean generation witness as native code — the "Lean is the
runtime" shape shared with `dregg_grain_r3_verify`. -/
@[export dregg_render_with_proof]
def renderWithProofWire (wire : String) : String :=
  match parseTemplateData wire with
  | some (T, d) => encToks (render T d) ++ "#" ++ encRules (renderRules T d)
  | none => "ERR"

/-- **`@[export dregg_replay_check]`** — VERIFIER side. Wire: three space-separated sections
`"<template-structure> <rules> <input bytes>"` — the template (`L…;H…`, grammar structure), the compact
certificate (`encRules`), and the input (`B/D` bytes). Reconstructs `handlebarsToGrammar T`, the rule
sequence and the input, and returns `"1"` iff the PROVEN `replayCheckB` (decides `Replay` exactly, §2)
accepts from the initial stack — i.e. iff `ReplayAccepts`, which `compact_sound` turns into language
membership. Malformed/undecodable wire ⇒ `"0"` (fail-closed). The Rust verifier CALLS this instead of a
re-authored twin. -/
@[export dregg_replay_check]
def replayCheckWire (wire : String) : String :=
  match wire.splitOn " " with
  | [tstr, rstr, istr] =>
      match parseTemplate tstr, decRules rstr, decToks istr with
      | some T, some rs, some input =>
          if replayCheckAccepts (handlebarsToGrammar T) rs input then "1" else "0"
      | _, _, _ => "0"
  | _ => "0"

#assert_axioms renderWithProofWire
#assert_axioms replayCheckWire

/-! ## §8 Non-vacuity — the demo template round-trips, and the decider FIRES on the proven cert. -/

namespace Demo

open Dregg2.Crypto.Handlebars.Demo (greetT greetD greetD_safe)

/-- The proven certificate `renderRules greetT greetD` REPLAYS under the COMPUTABLE decider — the executable
`replayCheckB` agrees with `renderRules_accepts` (`replayCheckAccepts_iff` proves it must). This is the
generation witness, decided by native code. -/
theorem greet_replayCheck_true :
    replayCheckAccepts (handlebarsToGrammar greetT) (renderRules greetT greetD) (render greetT greetD)
      = true :=
  (replayCheckAccepts_iff (handlebarsToGrammar greetT) (renderRules greetT greetD) (render greetT greetD)).mpr
    (renderRules_accepts greetT greetD greetD_safe)

-- The decider actually runs to `true` (`#guard`, not just the theorem): the proven cert is accepted.
#guard replayCheckAccepts (handlebarsToGrammar greetT) (renderRules greetT greetD) (render greetT greetD)

-- Prover export ROUND-TRIPS: parsing the demo template wire recovers greetT/greetD, so the serialized
-- cert equals the serialization of the actual proven objects; and the rendered bytes are `"DDBDD"`.
#guard renderWithProofWire "LD;H0:DBD;LD"
        = encToks (render greetT greetD) ++ "#" ++ encRules (renderRules greetT greetD)
#guard (renderWithProofWire "LD;H0:DBD;LD").startsWith "DDBDD#"

-- Verifier export: the (structure, cert, input) wire built from the encoders ACCEPTS (`"1"`); a wrong input
-- (no brace where the cert emits one) REJECTS (`"0"`); undecodable rules and garbage fail CLOSED (`"0"`).
#guard replayCheckWire
        ("LD;H0;LD " ++ encRules (renderRules greetT greetD) ++ " " ++ encToks (render greetT greetD)) = "1"
#guard replayCheckWire ("LD;H0;LD " ++ encRules (renderRules greetT greetD) ++ " DDDDD") = "0"
#guard replayCheckWire ("LD;H0;LD bad DDBDD") = "0"
#guard replayCheckWire "garbage" = "0"
#guard renderWithProofWire "garbage" = "ERR"

#assert_axioms greet_replayCheck_true

end Demo

end Dregg2.Crypto.HandlebarsFFI
