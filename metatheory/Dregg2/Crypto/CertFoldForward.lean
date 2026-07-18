/-
# Dregg2.Crypto.CertFoldForward — the substrate PAYS FORWARD: a NEW machine's soundness in one line.

`Chain.lean` proved `Cert.foldSound` once — the generic "walk the chain, accumulate an output,
carry a semantic invariant" induction — and `ReplayAsCert.mrun_imp_replay_via_fold` showed it
RETRO-subsumes the design's named hard induction (`DyckStackRefine.mrun_imp_replay`, a ~37-line
bespoke multi-row `induction … with` over `MRun`). This file demonstrates the FORWARD direction:
a brand-new machine, never seen by the substrate, gets its whole-run soundness for FREE.

The machine: a depth-counter acceptor for balanced brackets (the minimal machine with real
semantic content — one `Nat` of state). A configuration is `(remaining input, current depth)`;
one step consumes the head token, adjusting the depth; the accepting halt is `([], 0)`.

Two whole-run theorems fall out, EACH as a single `Cert.foldSound` application:

    run_closes : Cert Step (input, n) ([], 0) c → Closes n (c.flatMap out)   -- semantic soundness
    run_decode : Cert Step (input, n) ([], 0) c → c.flatMap out = input      -- decode faithfulness

and their composition `accept_sound : accepting run ⇒ Closes n input` — the machine only accepts
genuinely balanced continuations. The refusal pole `cl_no_cert` is powered by the SAME theorem.

## The quantified win

The bespoke route (the shape of `DyckStackRefine.mrun_imp_replay` before the substrate existed):
a hand-rolled `induction` over the run, re-doing the `head?`/`getLast?`/`flatMap` chain
bookkeeping interleaved with the per-step reasoning — ~37 lines THERE, and a structurally
identical ~20+-line induction would be owed HERE for EACH of the two whole-run theorems
(soundness AND decode), ~40+ lines of multi-row assembly.

With the substrate: the bespoke content is ONLY the two per-step lemmas (`step_closes`,
`step_decode` — two `cases` each, ~5 lines apiece), and each whole-run theorem is ONE
`Cert.foldSound` application (a single term, no `induction` keyword in this file at all).
Net: ~40 lines of fragile chain-walking induction per future machine → ~10 lines of local
per-step content. That is the four-rung substrate paying forward: every future rung's hard
induction is already proved.
-/
import Dregg2.Crypto.Chain
import Dregg2.Tactics

namespace Dregg2.Crypto.CertFoldForward

open Dregg2.Crypto
open Dregg2.Crypto.Hypergraph (Cert chain)

/-! ## The new machine — a depth-counter acceptor for balanced brackets. -/

/-- The bracket alphabet: open / close. -/
inductive Par where
  | op : Par
  | cl : Par
deriving DecidableEq, BEq, Repr

/-- A configuration: the remaining input and the current nesting depth. -/
abbrev Cfg := List Par × Nat

/-- **`Step`** — ONE move of the depth-counter machine: consume the head token, adjust the depth.
`cl` at depth `0` has NO step (the machine jams — depth never goes negative), and the accepting
halt is the fixed goal configuration `([], 0)`. -/
inductive Step : Cfg → Cfg → Prop
  | opn {input : List Par} {n : Nat} : Step (Par.op :: input, n) (input, n + 1)
  | cls {input : List Par} {n : Nat} : Step (Par.cl :: input, n + 1) (input, n)

/-- The per-configuration output segment of the fold: the token this configuration is about to
consume (the halt contributes nothing). A certificate's `flatMap out` is the decoded input word. -/
def out : Cfg → List Par
  | (t :: _, _) => [t]
  | ([], _) => []

/-- **`Closes`** — the per-step SEMANTICS: `Closes n w` says the word `w`, read from depth `n`,
legally returns the depth to `0` — never dipping below zero (`cl` requires positive depth) and
ending exactly balanced. `Closes 0 w` is "`w` is a balanced bracket word". -/
inductive Closes : Nat → List Par → Prop
  | nil : Closes 0 []
  | opn {n : Nat} {w : List Par} : Closes (n + 1) w → Closes n (Par.op :: w)
  | cls {n : Nat} {w : List Par} : Closes n w → Closes (n + 1) (Par.cl :: w)

/-! ## The bespoke content — per-step ONLY. Two lemmas, two `cases` each. No induction. -/

/-- ONE step is sound for prepending the consumed token to a closing continuation — the entire
machine-specific SEMANTIC content of the soundness theorem. This is the `hstep` that
`Cert.foldSound` consumes. -/
theorem step_closes (x y : Cfg) (h : Step x y) (rs : List Par)
    (hsem : Closes y.2 rs) : Closes x.2 (out x ++ rs) := by
  cases h with
  | opn => exact Closes.opn hsem
  | cls => exact Closes.cls hsem

/-- ONE step's output segment prepends to the successor's input to give this input — the entire
machine-specific DECODE content: each step consumes exactly the head token, so the accumulated
output reconstructs the input word. -/
theorem step_decode (x y : Cfg) (h : Step x y) (rs : List Par)
    (hsem : rs = y.1) : out x ++ rs = x.1 := by
  cases h with
  | opn => cases hsem; rfl
  | cls => cases hsem; rfl

/-! ## The whole-run theorems — each a SINGLE `Cert.foldSound` application.

The multi-row assembly (`head?`/`getLast?` bookkeeping, chain destructuring, `flatMap`
accumulation) is supplied ENTIRELY by the generic. Compare `DyckStackRefine.mrun_imp_replay`
(lines 1216–1252 there): the same shape hand-rolled is a 37-line `induction` block. -/

/-- **`run_closes`** — whole-run semantic soundness: ANY certificate chain of the machine from
`(input, n)` to the accepting halt folds to `Closes n` of the decoded output. One
`Cert.foldSound` application at `Sem rs cfg := Closes cfg.2 rs`; base case `Closes.nil`. -/
theorem run_closes {c : List Cfg} {input : List Par} {n : Nat}
    (h : Cert Step (input, n) ([], 0) c) : Closes n (c.flatMap out) :=
  Hypergraph.Cert.foldSound out (fun rs cfg => Closes cfg.2 rs) step_closes h Closes.nil

/-- **`run_decode`** — whole-run decode faithfulness: the accumulated output of ANY certificate
chain from `(input, n)` IS the input word. A SECOND `Cert.foldSound` instance over the same
machine at `Sem rs cfg := rs = cfg.1`; base case `rfl`. Two distinct whole-run inductions,
zero `induction` blocks. -/
theorem run_decode {c : List Cfg} {input : List Par} {n : Nat}
    (h : Cert Step (input, n) ([], 0) c) : c.flatMap out = input :=
  Hypergraph.Cert.foldSound out (fun rs cfg => rs = cfg.1) step_decode h rfl

/-- **`accept_sound`** — the headline: an accepting run of the depth-counter machine on `input`
from depth `n` implies `input` genuinely closes depth `n` (at `n = 0`: `input` is balanced).
Composition of the two fold instances. -/
theorem accept_sound {c : List Cfg} {input : List Par} {n : Nat}
    (h : Cert Step (input, n) ([], 0) c) : Closes n input := by
  rw [← run_decode h]
  exact run_closes h

/-- The `ReflTransGen` form, through `Hypergraph.bridge`: reachability of the halt alone implies
the semantics — the machine, the certificate, and the closure all agree. -/
theorem reflTransGen_sound {input : List Par} {n : Nat}
    (h : Relation.ReflTransGen Step (input, n) ([], 0)) : Closes n input := by
  obtain ⟨c, hc⟩ := (Hypergraph.bridge Step (input, n) ([], 0)).mpr h
  exact accept_sound hc

#assert_axioms step_closes
#assert_axioms step_decode
#assert_axioms run_closes
#assert_axioms run_decode
#assert_axioms accept_sound
#assert_axioms reflTransGen_sound

/-! ## Non-vacuity — a genuine accepting chain, a genuine refusal, and the decode checked. -/

/-- The reference word `[[]]` — nesting depth 2, so both step constructors fire twice. -/
def w : List Par := [.op, .op, .cl, .cl]

/-- The explicit machine chain for `w`: five configurations, four real steps. -/
def wChain : List Cfg :=
  [([.op, .op, .cl, .cl], 0), ([.op, .cl, .cl], 1), ([.cl, .cl], 2), ([.cl], 1), ([], 0)]

/-- `wChain` is a genuine certificate: endpoints by `rfl`, every link a real `Step`. -/
theorem w_cert : Cert Step (w, 0) ([], 0) wChain :=
  ⟨rfl, rfl, Step.opn, Step.opn, Step.cls, Step.cls, trivial⟩

/-- The accepting pole, THROUGH the generic fold: `[[]]` is balanced because the machine
accepts it. -/
theorem w_closes : Closes 0 w := accept_sound w_cert

/-- The rejecting pole of the semantics: a bare close is not balanced — no `Closes` constructor
applies at depth 0 to a `cl` head. -/
theorem cl_not_closes : ¬ Closes 0 [Par.cl] := fun h => nomatch h

/-- The rejecting pole of the MACHINE, powered by `accept_sound` itself: no certificate chain can
carry `[cl]` from depth 0 to the halt, else the semantics would hold and it does not. The
soundness theorem is doing real exclusion work, not labeling an empty set. -/
theorem cl_no_cert : ¬ ∃ c, Cert Step ([Par.cl], 0) ([], 0) c :=
  fun ⟨_, hc⟩ => cl_not_closes (accept_sound hc)

-- The decode is computationally real: the concrete chain's accumulated output IS the word.
#guard wChain.flatMap out == w

-- The halt contributes nothing to the decode.
#guard out ([], 0) == ([] : List Par)

#assert_axioms w_cert
#assert_axioms w_closes
#assert_axioms cl_not_closes
#assert_axioms cl_no_cert

end Dregg2.Crypto.CertFoldForward
