/-
# Dregg2.Crypto.HandlebarsWitnessTooth — the REAL consistency tooth (content-carrying, and it BITES).

`HandlebarsWitness.materialized_agrees` was RETRACTED at its own docstring: it is `rfl` between two
proofs of the same `Prop`, and Lean 4's definitional proof irrelevance makes that hold for ANY two
proofs of that `Prop` — including garbage. It establishes nothing, and by construction it CANNOT fail.

This module supplies what the retraction names as the real thing. Everything checked here lives in
`Type` or in `Bool`, where equality carries content and a perturbation can — and does — flip it:

  * §2 a DATA equation: `renderRules toothT toothD = toothRules` by `rfl`, where `toothRules` is a
    hand-written literal rule list. `rfl` here forces the recursion (`stateRules`/`segRules`/`flatMap`)
    to compute to a specific list of 7 rules; a wrong rule, a wrong order, a missing closing ε rule all
    break it. Plus the same equation in the deployed WIRE form (`encRules`, a hand-written string).
  * §3 the `Bool` tooth: `replayCheckB`/`replayCheckAccepts` (`HandlebarsFFI`, PROVEN to decide `Replay`
    exactly — `replayCheckB_iff`, sound AND complete) RUNS the materialized rule list against the
    rendered output and returns `true`. Executable, not a `Prop` `rfl`.
  * §4 MUTATION CANARIES — the point. Eight perturbations (drop the start rule, drop the closing rule,
    append a spurious rule, swap two rules, mutate the data, move a byte, retarget the template, feed
    the cert of UNSAFE data) each drive the same decider to `false`. The tooth bites.
  * §5 the FORGERY canary: a well-shaped certificate for an output containing the `{{` breakout, whose
    ONLY defect is that one cited production (`safeB h → brace safeB h`) is not in the grammar. The
    decider rejects it; the same certificate against a grammar EXTENDED by exactly that production is
    ACCEPTED (§5 `leakyGrammar`). So the rejection is attributable to the grammar-membership check, not
    to shape.
  * §6 Prop-level bites (no kernel `decide`): `replay_rules_mem` — every rule cited by an accepted
    replay IS a grammar production — turns the §5 non-membership into a real
    `¬ ReplayAccepts` theorem for the forged injection certificate and for a retargeted template.

Nothing here is edited into `HandlebarsWitness.lean`; the retraction stands as written. The `#guard`s
are EXECUTABLE checks (they prove no `Prop`); the theorems are the `Prop` content, and §6's are the
ones that carry an adversary-relevant statement (a forged certificate is REFUSED).
-/
import Dregg2.Crypto.Handlebars
import Dregg2.Crypto.HandlebarsWitness
import Dregg2.Crypto.HandlebarsFFI
import Dregg2.Crypto.CfgCompact
import Dregg2.Tactics

namespace Dregg2.Crypto.HandlebarsWitnessTooth

open ContextFreeGrammar
open Dregg2.Crypto.Handlebars
open Dregg2.Crypto.HandlebarsWitness
open Dregg2.Crypto.CfgCompact
open Dregg2.Crypto.HandlebarsFFI

/-! ## §0 The retracted shape, shown UNIVERSAL.

Before supplying the replacement, the diagnosis, machine-checked: the retracted equation is an instance
of a statement that holds for ANY two proofs, so it cannot constrain the certificate. -/

/-- **`retracted_shape_is_universal`** — for an ARBITRARY grammar, rule list and input, and ANY two
proofs `p q` of acceptance, the two `compact_sound` outputs are `rfl`-equal. `materialized_agrees` is
this at `p := renderRules_accepts …`, `q := render_mem_language …`; nothing about the materialized
certificate enters. This is a DEMONSTRATION OF VACUITY, not a tooth — it is exactly the shape §2-§6
avoid by working in `Type`/`Bool`. -/
theorem retracted_shape_is_universal {α : Type} (g : ContextFreeGrammar α)
    (rs : List (ContextFreeRule α g.NT)) (input : List α) (p q : ReplayAccepts g rs input) :
    compact_sound g rs input p = compact_sound g rs input q := rfl

#assert_axioms retracted_shape_is_universal

/-! ## §1 A certificate can only cite grammar productions.

The one general lemma this module adds: an accepting `Replay` uses only rules of `g`. Immediate by
induction on the replay (`rule` supplies the head's membership, the tail comes from the IH). It is what
turns "this forged production is not in the grammar" into "this forged certificate is REFUSED", with no
kernel evaluation of the decider. -/

/-- **`replay_rules_mem`** — every rule of a replaying certificate is a production of the grammar. -/
theorem replay_rules_mem {α : Type} {g : ContextFreeGrammar α}
    {rs : List (ContextFreeRule α g.NT)} {input : List α} {stk : List (Symbol α g.NT)}
    (h : Replay g rs input stk) : ∀ r ∈ rs, r ∈ g.rules := by
  induction h with
  | done => intro r hr; simp at hr
  | term _ _ ih => exact ih
  | rule hr _ ih =>
      intro r' hr'
      rcases List.mem_cons.mp hr' with rfl | hmem
      · exact hr
      · exact ih r' hmem

#assert_axioms replay_rules_mem

/-! ## §2 The tooth instance, and the DATA equation.

`toothT` = `"<lit> {{0}} <lit> {{1}}"`, filled with `{x` (a lone interior brace — safe) at hole `0` and
`xx` at hole `1`. Two holes, both recognizer states exercised (`safeD` and, after the brace, `safeB`),
still tiny: 7 rules, 6 tokens. -/

/-- The tooth template: literal, hole `0`, literal, hole `1`. -/
def toothT : HandlebarsTemplate :=
  ⟨[Segment.lit [Tok.data], Segment.hole 0, Segment.lit [Tok.data], Segment.hole 1]⟩

/-- The tooth data: hole `0` ↦ `"{x"` (lone interior brace, SAFE), hole `1` ↦ `"xx"`. -/
def toothD : HoleId → List Tok
  | 0 => [Tok.brace, Tok.data]
  | 1 => [Tok.data, Tok.data]
  | _ => []

/-- Both filled holes carry `NoDoubleBrace` data; every other hole is empty. (Discharged by
constructor disequality, not by a `Decidable`-instance kernel reduction.) -/
theorem toothD_safe : safe toothT toothD := by
  intro h _
  cases h with
  | zero => exact ⟨fun hc => Tok.noConfusion hc.2, trivial⟩
  | succ n =>
      cases n with
      | zero => exact ⟨fun hc => Tok.noConfusion hc.1, trivial⟩
      | succ _ => trivial

/-- **The hand-written rule list** — what the materialized leftmost derivation for `toothT`/`toothD`
MUST be, written out independently of `renderRules`' recursion: the start production, then hole `0`'s
`brace`-then-`data`-then-ε walk (through state `b`), then hole `1`'s two `data` steps and its ε. -/
def toothRules : List (ContextFreeRule Tok NT) :=
  [ ⟨NT.start, [Symbol.terminal Tok.data, Symbol.nonterminal (NT.safeD 0),
                Symbol.terminal Tok.data, Symbol.nonterminal (NT.safeD 1)]⟩,
    ⟨NT.safeD 0, [Symbol.terminal Tok.brace, Symbol.nonterminal (NT.safeB 0)]⟩,
    ⟨NT.safeB 0, [Symbol.terminal Tok.data, Symbol.nonterminal (NT.safeD 0)]⟩,
    ⟨NT.safeD 0, []⟩,
    ⟨NT.safeD 1, [Symbol.terminal Tok.data, Symbol.nonterminal (NT.safeD 1)]⟩,
    ⟨NT.safeD 1, [Symbol.terminal Tok.data, Symbol.nonterminal (NT.safeD 1)]⟩,
    ⟨NT.safeD 1, []⟩ ]

/-- **THE DATA EQUATION** (`Type`-level, content-carrying — unlike the retracted `Prop` `rfl`): the
materialized certificate computed by `renderRules` IS the hand-written list. `rfl` must run
`segRules`/`stateRules`/`flatMap` to seven specific rules in a specific order; any drift in the
recursion (a wrong production, a missing closing ε, a swapped state) makes this fail to typecheck. -/
theorem renderRules_tooth_eq : renderRules toothT toothD = toothRules := rfl

/-- The rendered bytes, likewise as a data equation: `"x{xxx"` — `data brace data data data` after the
leading literal. -/
theorem render_tooth_eq :
    render toothT toothD =
      [Tok.data, Tok.brace, Tok.data, Tok.data, Tok.data, Tok.data] := rfl

#assert_axioms toothD_safe
#assert_axioms renderRules_tooth_eq
#assert_axioms render_tooth_eq

/-- Canary ON THE DATA EQUATION: the same equation against a perturbed list (start rule dropped) is
FALSE — the lengths already differ. So `renderRules_tooth_eq` is not an equation that any list satisfies. -/
theorem renderRules_tooth_ne_tail : renderRules toothT toothD ≠ toothRules.tail := by
  intro h
  have hlen := congrArg List.length h
  rw [renderRules_tooth_eq] at hlen
  simp [toothRules] at hlen

/-- Canary ON THE DATA EQUATION, second form: swapping hole `0`'s two productions gives a DIFFERENT
list (they disagree at index 1: `safeD 0 → brace safeB 0` vs `safeB 0 → data safeD 0`). -/
theorem renderRules_tooth_ne_swapped :
    renderRules toothT toothD ≠
      [ ⟨NT.start, [Symbol.terminal Tok.data, Symbol.nonterminal (NT.safeD 0),
                    Symbol.terminal Tok.data, Symbol.nonterminal (NT.safeD 1)]⟩,
        ⟨NT.safeB 0, [Symbol.terminal Tok.data, Symbol.nonterminal (NT.safeD 0)]⟩,
        ⟨NT.safeD 0, [Symbol.terminal Tok.brace, Symbol.nonterminal (NT.safeB 0)]⟩,
        ⟨NT.safeD 0, []⟩,
        ⟨NT.safeD 1, [Symbol.terminal Tok.data, Symbol.nonterminal (NT.safeD 1)]⟩,
        ⟨NT.safeD 1, [Symbol.terminal Tok.data, Symbol.nonterminal (NT.safeD 1)]⟩,
        ⟨NT.safeD 1, []⟩ ] := by
  intro h
  rw [renderRules_tooth_eq] at h
  simp [toothRules] at h

#assert_axioms renderRules_tooth_ne_tail
#assert_axioms renderRules_tooth_ne_swapped

-- The certificate in the DEPLOYED WIRE FORM equals a hand-written string (an executable check, no
-- `Prop`): every nonterminal, every symbol, every rule boundary, in order.
#guard encToks (render toothT toothD) = "DBDDDD"
#guard encRules (renderRules toothT toothD)
        = "S>tD,nD0,tD,nD1|D0>tB,nB0|B0>tD,nD0|D0>|D1>tD,nD1|D1>tD,nD1|D1>"

-- END TO END through the exported prover (`@[export dregg_render_with_proof]`): the wire in, the
-- rendered bytes and the whole materialized certificate out, against a hand-written expected string.
#guard renderWithProofWire "LD;H0:BD;LD;H1:DD"
        = "DBDDDD#S>tD,nD0,tD,nD1|D0>tB,nB0|B0>tD,nD0|D0>|D1>tD,nD1|D1>tD,nD1|D1>"

/-! ## §3 The `Bool` tooth — the materialized certificate REALLY replays.

`replayCheckAccepts` is `HandlebarsFFI`'s executable decider, PROVEN to decide `ReplayAccepts` exactly
(`replayCheckAccepts_iff`). Running it on `(renderRules toothT toothD, render toothT toothD)` is a
content-carrying check: it walks the pushdown, matching each cited production against the grammar and
each terminal against the next byte. -/

/-- The `Prop` behind the check: the tooth instance's materialized certificate is accepted. -/
theorem tooth_replayAccepts :
    ReplayAccepts (handlebarsToGrammar toothT) (renderRules toothT toothD) (render toothT toothD) :=
  renderRules_accepts toothT toothD toothD_safe

#assert_axioms tooth_replayAccepts

-- The decider RUNS to `true` on the materialized certificate (executable; proves no `Prop`, but it is
-- the same Bool the deployed verifier computes).
#guard replayCheckAccepts (handlebarsToGrammar toothT) (renderRules toothT toothD)
        (render toothT toothD)

-- …and the hand-written list drives it too (the data equation, re-checked through the decider).
#guard replayCheckAccepts (handlebarsToGrammar toothT) toothRules (render toothT toothD)

-- END TO END through the exported verifier (`@[export dregg_replay_check]`): structure, certificate,
-- input bytes — all hand-written wire — ACCEPTS.
#guard replayCheckWire
        ("LD;H0;LD;H1 S>tD,nD0,tD,nD1|D0>tB,nB0|B0>tD,nD0|D0>|D1>tD,nD1|D1>tD,nD1|D1> DBDDDD")
        = "1"

/-! ## §4 MUTATION CANARIES — the tooth bites.

Each perturbation below is fed to the SAME decider that returned `true` above, and each returns
`false`. A check that cannot fail is what was retracted; these fail on demand. -/

/-- Mutant: the start production dropped (the cert no longer opens the derivation). -/
def mutNoStart : List (ContextFreeRule Tok NT) := toothRules.tail

/-- Mutant: the final `safeD 1 → ε` dropped (the derivation never closes). -/
def mutNoClose : List (ContextFreeRule Tok NT) := toothRules.dropLast

/-- Mutant: a spurious extra production appended (rules left unconsumed at accept time). -/
def mutExtra : List (ContextFreeRule Tok NT) := toothRules ++ [⟨NT.safeD 1, []⟩]

/-- Mutant: hole `0`'s two productions swapped (state `b` entered before the brace is emitted). -/
def mutSwapped : List (ContextFreeRule Tok NT) :=
  [ ⟨NT.start, [Symbol.terminal Tok.data, Symbol.nonterminal (NT.safeD 0),
                Symbol.terminal Tok.data, Symbol.nonterminal (NT.safeD 1)]⟩,
    ⟨NT.safeB 0, [Symbol.terminal Tok.data, Symbol.nonterminal (NT.safeD 0)]⟩,
    ⟨NT.safeD 0, [Symbol.terminal Tok.brace, Symbol.nonterminal (NT.safeB 0)]⟩,
    ⟨NT.safeD 0, []⟩,
    ⟨NT.safeD 1, [Symbol.terminal Tok.data, Symbol.nonterminal (NT.safeD 1)]⟩,
    ⟨NT.safeD 1, [Symbol.terminal Tok.data, Symbol.nonterminal (NT.safeD 1)]⟩,
    ⟨NT.safeD 1, []⟩ ]

/-- Mutated data: hole `0` ↦ `"xx"` (the brace gone), hole `1` unchanged. -/
def toothD' : HoleId → List Tok
  | 0 => [Tok.data, Tok.data]
  | 1 => [Tok.data, Tok.data]
  | _ => []

/-- Mutated output: the brace MOVED one byte to the right (same length, same byte multiset). -/
def movedBrace : List Tok :=
  [Tok.data, Tok.data, Tok.brace, Tok.data, Tok.data, Tok.data]

/-- A RETARGETED template: same shape, but hole `0` renamed to hole `2`. Its grammar contains neither
`toothT`'s start production nor hole `0`'s productions. -/
def otherT : HandlebarsTemplate :=
  ⟨[Segment.lit [Tok.data], Segment.hole 2, Segment.lit [Tok.data], Segment.hole 1]⟩

/-- UNSAFE data: hole `0` ↦ `"{{"` — the delimiter breakout `safe` forbids. -/
def unsafeD : HoleId → List Tok
  | 0 => [Tok.brace, Tok.brace]
  | 1 => [Tok.data, Tok.data]
  | _ => []

-- C1 start production dropped ⇒ the initial nonterminal is never expanded.
#guard !replayCheckAccepts (handlebarsToGrammar toothT) mutNoStart (render toothT toothD)
-- C2 closing ε dropped ⇒ the stack never empties.
#guard !replayCheckAccepts (handlebarsToGrammar toothT) mutNoClose (render toothT toothD)
-- C3 spurious extra production ⇒ rules unconsumed when the input runs out.
#guard !replayCheckAccepts (handlebarsToGrammar toothT) mutExtra (render toothT toothD)
-- C4 two productions swapped ⇒ the cited lhs does not match the stack top.
#guard !replayCheckAccepts (handlebarsToGrammar toothT) mutSwapped (render toothT toothD)
-- C5 the certificate is BOUND TO ITS DATA: honest cert, output re-rendered from mutated data.
#guard !replayCheckAccepts (handlebarsToGrammar toothT) (renderRules toothT toothD)
        (render toothT toothD')
-- C6 the certificate is BOUND TO ITS BYTES: one byte moved, same length and multiset.
#guard !replayCheckAccepts (handlebarsToGrammar toothT) (renderRules toothT toothD) movedBrace
-- C7 the certificate is BOUND TO ITS TEMPLATE: verified against a retargeted template's grammar, the
-- cited productions are not that grammar's.
#guard !replayCheckAccepts (handlebarsToGrammar otherT) (renderRules toothT toothD)
        (render toothT toothD)
-- C8 the `safe` hypothesis of `renderRules_accepts` is LOAD-BEARING: with `{{` data the materialized
-- certificate is truncated at the breakout and does NOT replay. Unsafe in ⇒ no witness out.
#guard !replayCheckAccepts (handlebarsToGrammar toothT) (renderRules toothT unsafeD)
        (render toothT unsafeD)

-- The same canaries through the deployed verifier export: wrong bytes, and a retargeted template.
#guard replayCheckWire
        ("LD;H0;LD;H1 S>tD,nD0,tD,nD1|D0>tB,nB0|B0>tD,nD0|D0>|D1>tD,nD1|D1>tD,nD1|D1> DDBDDD")
        = "0"
#guard replayCheckWire
        ("LD;H2;LD;H1 S>tD,nD0,tD,nD1|D0>tB,nB0|B0>tD,nD0|D0>|D1>tD,nD1|D1>tD,nD1|D1> DBDDDD")
        = "0"

/-! ## §5 THE FORGERY CANARY — and what exactly refuses it.

An attacker wants a certificate for an output whose hole content contains the `{{` breakout. The
shape-correct forgery cites `safeB 0 → brace safeB 0` — the ONE production the recognizer deliberately
omits (after a brace, another brace is forbidden). Every other rule in the forged certificate is a real
production, the lhs's all match the stack, and the terminals all match the bytes.

`leakyGrammar` is `toothT`'s grammar EXTENDED by exactly that forged production. Same certificate, same
input: `leakyGrammar` ACCEPTS, `handlebarsToGrammar toothT` REJECTS. The rejection is therefore
attributable to the grammar-membership check on that one rule, and to nothing about shape or length. -/

/-- The output with the breakout: `"x{{xxx"` — hole `0` rendered as `{{`. -/
def injOutput : List Tok := render toothT unsafeD

/-- The forged production the recognizer omits: after a brace, another brace. -/
def forgedRule : ContextFreeRule Tok NT :=
  ⟨NT.safeB 0, [Symbol.terminal Tok.brace, Symbol.nonterminal (NT.safeB 0)]⟩

/-- The shape-correct forged certificate for `injOutput`: identical to an honest run except that its
third rule is `forgedRule`. -/
def forgedInjRules : List (ContextFreeRule Tok NT) :=
  [ ⟨NT.start, [Symbol.terminal Tok.data, Symbol.nonterminal (NT.safeD 0),
                Symbol.terminal Tok.data, Symbol.nonterminal (NT.safeD 1)]⟩,
    ⟨NT.safeD 0, [Symbol.terminal Tok.brace, Symbol.nonterminal (NT.safeB 0)]⟩,
    forgedRule,
    ⟨NT.safeB 0, [Symbol.terminal Tok.data, Symbol.nonterminal (NT.safeD 0)]⟩,
    ⟨NT.safeD 0, []⟩,
    ⟨NT.safeD 1, [Symbol.terminal Tok.data, Symbol.nonterminal (NT.safeD 1)]⟩,
    ⟨NT.safeD 1, []⟩ ]

/-- `toothT`'s grammar with the forged production ADDED — the counterfactual that isolates the cause. -/
def leakyGrammar : ContextFreeGrammar Tok :=
  ⟨NT, NT.start, insert forgedRule (allRules toothT).toFinset⟩

instance : DecidableEq leakyGrammar.NT := (inferInstance : DecidableEq NT)

-- The breakout output is `"DBBDDD"`.
#guard encToks injOutput = "DBBDDD"
-- REJECTED by the real grammar: the forged production is not a production of `toothT`.
#guard !replayCheckAccepts (handlebarsToGrammar toothT) forgedInjRules injOutput
-- ACCEPTED once — and only once — that exact production is added to the grammar. Same certificate,
-- same input: the membership check is what refused it.
#guard replayCheckAccepts leakyGrammar forgedInjRules injOutput

/-! ## §6 Prop-level bite — the forged certificate is REFUSED, as a theorem.

Via §1 (`replay_rules_mem`), non-membership of a single cited production refutes the whole replay. No
kernel evaluation of the decider is involved. -/

/-- The forged production is NOT a production of `toothT`'s grammar. -/
theorem forgedRule_not_mem : forgedRule ∉ (handlebarsToGrammar toothT).rules := by
  show forgedRule ∉ (allRules toothT).toFinset
  rw [List.mem_toFinset]
  simp [allRules, holesOf, holeRules, startRule, startSymbols, segSymbols, toothT, forgedRule]

/-- **The forged certificate is REFUSED** — no `Replay` of `injOutput` uses `forgedInjRules`, because
one of its cited productions is not a production at all. The `{{` output cannot be certified this way. -/
theorem forgedInj_refused :
    ¬ ReplayAccepts (handlebarsToGrammar toothT) forgedInjRules injOutput := fun h =>
  forgedRule_not_mem (replay_rules_mem h forgedRule
    (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)))

/-- `toothT`'s start production is not a production of the RETARGETED template's grammar… -/
theorem toothStart_not_mem_other :
    startRule toothT ∉ (handlebarsToGrammar otherT).rules := by
  show startRule toothT ∉ (allRules otherT).toFinset
  rw [List.mem_toFinset]
  simp [allRules, holesOf, holeRules, startRule, startSymbols, segSymbols, toothT, otherT]

/-- …so `toothT`'s materialized certificate is REFUSED against that template: a certificate is bound to
the template it was rendered from. -/
theorem tooth_cert_refused_by_otherT :
    ¬ ReplayAccepts (handlebarsToGrammar otherT) (renderRules toothT toothD)
      (render toothT toothD) := fun h =>
  toothStart_not_mem_other
    (replay_rules_mem h (startRule toothT) (by rw [renderRules]; exact List.mem_cons_self))

/-- The empty certificate is refused outright (structural inversion: nothing expands the start
nonterminal). -/
theorem tooth_empty_cert_refused :
    ¬ ReplayAccepts (handlebarsToGrammar toothT) [] (render toothT toothD) := by
  intro h
  cases h

#assert_all_clean [retracted_shape_is_universal, replay_rules_mem, toothD_safe, renderRules_tooth_eq, render_tooth_eq,
  renderRules_tooth_ne_tail, renderRules_tooth_ne_swapped, tooth_replayAccepts,
  forgedRule_not_mem, forgedInj_refused, toothStart_not_mem_other, tooth_cert_refused_by_otherT,
  tooth_empty_cert_refused]

/-! ## §7 What this establishes — and what it does not.

ESTABLISHED. (i) The materialized certificate `renderRules toothT toothD` is a specific 7-rule list,
pinned as a `Type`-level equation and as a wire string, and the pin fails under perturbation (§2).
(ii) The PROVEN decider accepts it (§3) and rejects eight perturbations of it (§4). (iii) A forged
certificate for a `{{` output is refused, and the refusal is attributed — by the `leakyGrammar`
counterfactual — to the grammar-membership check on the one omitted production (§5), with the refusal
also stated as a theorem (§6).

NOT ESTABLISHED. The `#guard`s prove no `Prop`; they are executable checks on ONE concrete instance, run
by the interpreter, and they say nothing about all templates. §6's theorems are about these specific
certificates, not about all certificates for `injOutput` — "no certificate at all exists for a `{{`
output" is the parse-uniqueness/round-trip converse, still the named residual of `Handlebars.lean` §9
(and the junction caveat there is untouched: a hole ending in `{` abutting a literal starting with `{`
produces `{{` at the seam and remains in the language). Nothing here touches the FRI/STARK floor the
circuit tie rides on; this is a statement about the CFG certificate object only. -/

end Dregg2.Crypto.HandlebarsWitnessTooth
