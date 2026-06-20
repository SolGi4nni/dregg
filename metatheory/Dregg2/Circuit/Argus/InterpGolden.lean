/-
# Dregg2.Circuit.Argus.InterpGolden — the `decideVm` golden corpus (the R1/R2 transcription pin).

## What this is

`InterpCore.decideVm` is the VERIFIED total reference the Rust descriptor interpreter
(`circuit/src/lean_descriptor_air.rs::EffectVmDescriptorAir::eval`) transcribes. The Rust-side
agreement battery (`tests/effect_vm_descriptor_exhaustive_differential.rs` + the in-crate
differentials) pins the running AIR against a RUST transcription of `decideVm`
(`oracle_decide_vm` / `denote_vm_descriptor`) — but those oracles are themselves hand
transcriptions. THIS module closes the remaining leg of the cascade: it computes `decideVm`'s
verdicts IN LEAN (the verified function itself, no `sorry`, no `native_decide`) over a fixed
corpus of (descriptor, row-window, flags) cases and renders them to a line format the Rust test
`lean_descriptor_air.rs::tests::lean_decide_vm_golden_corpus_agrees` embeds verbatim and
re-decides with its own per-window transcription. A verdict mismatch on any case is a
transcription drift caught at test time. The golden-oracle cascade is then:

    decideVm (Lean, verified)
      ≡ (THIS golden corpus, byte-pinned)        Rust per-window `decide_vm_z`
      ≡ (structural identity, same module)        `oracle_decide_vm` / `denote_vm_descriptor`
      ≡ (exhaustive generated differential)       the running `EffectVmDescriptorAir`

## What the corpus pins (the R1/R2 content)

  * EVERY `VmConstraint` arm — `gate` / `transition` / `boundary .first` / `boundary .last` /
    `piBinding .first` / `piBinding .last` — in BOTH polarities (R1: the boundary arm is real,
    not vacuous: accept-on-row, reject-on-row, AND vacuous-off-row cases are all present).
  * The ROW-DOMAIN flag semantics (R2): the `isFirst`/`isLast` guards are exercised at all four
    flag settings, including the single-row window `isFirst ∧ isLast` (n = 1, the classic
    boundary wrap edge) and the off-row vacuity legs (`boundary`/`piBinding` ACCEPT when their
    flag is off, however broken the cells are). One case pins that `gate`/`transition` are
    VACUOUS at `isLast = true` in `decideVm` — the `when_transition` factoring (gate/transition
    enforced on windows `r < n−1`, not on the last row) lives IN the single-window reference, so
    it faithfully matches the multi-row AIR's domain choice.
  * Every `EmittedExpr` form (`var`/`const` incl. negative/`add`/`mul`, nested), every
    `HashInput` form (`col`/`digest`/`zero`), arity 2 AND 4, the ORDERED digest-accumulator
    chain (site 1 reading site 0's RESOLVED digest), and `VmRange` teeth including the
    `0 ≤ wire` leg only ℤ can see (negative wire ⇒ reject).
  * The descriptor bytes themselves go through `emitVmJson` (the canonical codec
    `EmitRoundtrip.parseVmJson_emitVmJson` proves lossless), so the Rust side re-parses them
    with the production `parse_vm_descriptor` — the same seam the registry carries.

## The hash portal

`decideVm` is parametric in an abstract `hash : List ℤ → ℤ`. The corpus instantiates a TOY
computable fold (`toyHash`, Horner ×31 + 7) on BOTH sides — the golden pins the SITE-WALK
SEMANTICS (binding equation, accumulator order, input resolution), not the Poseidon2 instance;
the Poseidon2 leg is the named CR portal carried where it always was (`Argus` §crypto-floor),
and the Rust differentials run the real permutation. Corpus values are kept ≪ 2^40 so ℤ and the
Rust `i128` transcription agree exactly (no reduction enters on either side).

`main` prints the rendered corpus: regenerate the Rust-embedded bytes with
`lake env lean --run Dregg2/Circuit/Argus/InterpGolden.lean` after any corpus edit.
-/
import Dregg2.Circuit.Argus.InterpCore

namespace Dregg2.Circuit.Argus.InterpGolden

open Dregg2.Circuit.Emit.EffectVmEmit
open Dregg2.Circuit.Argus.InterpCore
open Dregg2.Exec.CircuitEmit (EmittedExpr)

/-! ## §1 — The toy hash portal and finite row environments. -/

/-- The corpus's computable hash instance: a Horner fold (seed 7, radix 31). Injectivity is not
needed — only that accept/reject discriminate — and both sides compute it exactly over small
integers. -/
def toyHash : List ℤ → ℤ :=
  fun xs => xs.foldl (fun a x => a * 31 + x) 7

/-- A finite sparse assignment: listed columns carry their value, everything else 0. -/
def assignOf (l : List (Nat × Int)) : Dregg2.Circuit.Assignment :=
  fun n => ((l.find? (fun p => p.1 == n)).map Prod.snd).getD 0

/-! ## §2 — Golden cases. -/

/-- One golden case: a descriptor, a sparse row window (`loc`/`nxt`), a dense PI vector, and
the window flags. The verdict is NOT stored — it is COMPUTED by `decideVm` (the point). -/
structure GoldenCase where
  name    : String
  desc    : EffectVmDescriptor
  loc     : List (Nat × Int)
  nxt     : List (Nat × Int)
  pubs    : List Int
  isFirst : Bool
  isLast  : Bool

/-- The case's row environment. -/
def GoldenCase.env (c : GoldenCase) : VmRowEnv :=
  { loc := assignOf c.loc, nxt := assignOf c.nxt, pub := fun k => c.pubs.getD k 0 }

/-- The case's verdict — `decideVm` itself, the verified reference. -/
def GoldenCase.verdict (c : GoldenCase) : Bool :=
  decideVm toyHash c.desc c.env c.isFirst c.isLast

/-! ### Builders. -/

private def v (i : Nat) : EmittedExpr := .var i
private def kc (c : Int) : EmittedExpr := .const c
/-- `a − b` in the emitter's canonical shape `a + (−1)·b`. -/
private def sub (a b : EmittedExpr) : EmittedExpr := .add a (.mul (.const (-1)) b)

private def mkDesc (nm : String) (cs : List VmConstraint)
    (hs : List VmHashSite := []) (rs : List VmRange := []) : EffectVmDescriptor :=
  { name := nm, traceWidth := EFFECT_VM_WIDTH, piCount := 4
  , constraints := cs, hashSites := hs, ranges := rs }

private def mkCase (nm : String) (cs : List VmConstraint)
    (loc : List (Nat × Int)) (iF iL : Bool)
    (nxt : List (Nat × Int) := []) (pubs : List Int := [0, 0, 0, 0])
    (hs : List VmHashSite := []) (rs : List VmRange := []) : GoldenCase :=
  { name := nm, desc := mkDesc ("dregg-interpgolden-" ++ nm) cs hs rs
  , loc := loc, nxt := nxt, pubs := pubs, isFirst := iF, isLast := iL }

/-! ### The corpus.

Layout notes: gate cells live in low columns; `transition hi lo` reads `nxt (54+hi)` vs
`loc (76+lo)` (`sbCol`/`saCol`); boundary cells use the aux region 100..103; digest columns
120..122; range wires at 40. Site digests are written with `toyHash` itself so accept cases are
genuine by construction. -/

private def d0 : Int := toyHash [9, 0]
private def d1 : Int := toyHash [d0, 4]

def corpus : List GoldenCase :=
  [ -- gates (unguarded per-row form), every expr constructor, both polarities
    mkCase "gate-eq-accept" [.gate (sub (v 5) (v 6))] [(5, 42), (6, 42)] false false
  , mkCase "gate-eq-reject" [.gate (sub (v 5) (v 6))] [(5, 42), (6, 43)] false false
  , mkCase "gate-const-zero-accept" [.gate (kc 0)] [] false false
  , mkCase "gate-const-neg-reject" [.gate (kc (-3))] [] false false
  , mkCase "gate-mul-zero-accept" [.gate (.mul (v 2) (v 3))] [(2, 0), (3, 7)] false false
  , mkCase "gate-nested-accept" [.gate (sub (.mul (.add (v 2) (v 3)) (v 4)) (v 7))]
      [(2, 3), (3, 4), (4, 10), (7, 70)] false false
  , mkCase "gate-nested-reject" [.gate (sub (.mul (.add (v 2) (v 3)) (v 4)) (v 7))]
      [(2, 3), (3, 4), (4, 10), (7, 71)] false false
    -- transition continuity (guarded at isLast in decideVm — the `when_transition` factoring
    -- lives in the reference: gate/transition are enforced on windows r < n−1, vacuous at isLast)
  , mkCase "transition-accept" [.transition 3 5] [(81, 9)] false false (nxt := [(57, 9)])
  , mkCase "transition-reject" [.transition 3 5] [(81, 8)] false false (nxt := [(57, 9)])
  , mkCase "transition-vacuous-at-last" [.transition 3 5]
      [(81, 8)] false true (nxt := [(57, 9)])
    -- boundary .first (R1): on-row accept/reject + off-row vacuity
  , mkCase "boundary-first-accept-on-row" [.boundary .first (sub (v 100) (v 101))]
      [(100, 5), (101, 5)] true false
  , mkCase "boundary-first-reject-on-row" [.boundary .first (sub (v 100) (v 101))]
      [(100, 5), (101, 6)] true false
  , mkCase "boundary-first-vacuous-off-row" [.boundary .first (sub (v 100) (v 101))]
      [(100, 5), (101, 6)] false false
    -- boundary .last (R1)
  , mkCase "boundary-last-accept-on-row" [.boundary .last (sub (v 102) (v 103))]
      [(102, 8), (103, 8)] false true
  , mkCase "boundary-last-reject-on-row" [.boundary .last (sub (v 102) (v 103))]
      [(102, 8), (103, 9)] false true
  , mkCase "boundary-last-vacuous-off-row" [.boundary .last (sub (v 102) (v 103))]
      [(102, 8), (103, 9)] true false
    -- the single-row window (isFirst ∧ isLast — the n = 1 wrap edge)
  , mkCase "boundary-single-row-both-hold"
      [.boundary .first (sub (v 100) (v 101)), .boundary .last (sub (v 102) (v 103))]
      [(100, 5), (101, 5), (102, 8), (103, 8)] true true
  , mkCase "boundary-single-row-last-broken"
      [.boundary .first (sub (v 100) (v 101)), .boundary .last (sub (v 102) (v 103))]
      [(100, 5), (101, 5), (102, 8), (103, 9)] true true
    -- piBinding .first / .last: on-row accept/reject + off-row vacuity
  , mkCase "pi-first-accept" [.piBinding .first 10 0] [(10, 77)] true false
      (pubs := [77, 0, 0, 0])
  , mkCase "pi-first-reject" [.piBinding .first 10 0] [(10, 77)] true false
      (pubs := [78, 0, 0, 0])
  , mkCase "pi-first-vacuous-off-row" [.piBinding .first 10 0] [(10, 77)] false false
      (pubs := [78, 0, 0, 0])
  , mkCase "pi-last-accept" [.piBinding .last 11 2] [(11, 5)] false true
      (pubs := [0, 0, 5, 0])
  , mkCase "pi-last-reject" [.piBinding .last 11 2] [(11, 5)] false true
      (pubs := [0, 0, 6, 0])
  , mkCase "pi-last-vacuous-off-row" [.piBinding .last 11 2] [(11, 5)] false false
      (pubs := [0, 0, 6, 0])
    -- hash sites: single site, ordered chain, arity 4, both polarities
  , mkCase "site-single-accept" []
      [(30, 9), (120, d0)] false false
      (hs := [{ digestCol := 120, inputs := [.col 30, .zero], arity := 2 }])
  , mkCase "site-single-reject" []
      [(30, 9), (120, d0 + 1)] false false
      (hs := [{ digestCol := 120, inputs := [.col 30, .zero], arity := 2 }])
  , mkCase "site-chain-accept" []
      [(30, 9), (31, 4), (120, d0), (121, d1)] false false
      (hs := [ { digestCol := 120, inputs := [.col 30, .zero], arity := 2 }
             , { digestCol := 121, inputs := [.digest 0, .col 31], arity := 2 } ])
  , mkCase "site-chain-first-corrupt-reject" []
      [(30, 9), (31, 4), (120, d0 + 1), (121, d1)] false false
      (hs := [ { digestCol := 120, inputs := [.col 30, .zero], arity := 2 }
             , { digestCol := 121, inputs := [.digest 0, .col 31], arity := 2 } ])
  , mkCase "site-arity4-accept" []
      [(30, 1), (31, 2), (32, 3), (122, toyHash [1, 2, 0, 3])] false false
      (hs := [{ digestCol := 122, inputs := [.col 30, .col 31, .zero, .col 32], arity := 4 }])
    -- ranges: in-range, over-range, and the negative leg only ℤ can see
  , mkCase "range-accept" [] [(40, 4095)] false false (rs := [{ wire := 40, bits := 12 }])
  , mkCase "range-reject-high" [] [(40, 4096)] false false (rs := [{ wire := 40, bits := 12 }])
  , mkCase "range-reject-negative" [] [(40, -1)] false false (rs := [{ wire := 40, bits := 12 }])
    -- all clauses combined on a single-row window
  , mkCase "combined-accept"
      [ .gate (sub (v 5) (v 6)), .transition 3 5
      , .boundary .first (sub (v 100) (v 101)), .piBinding .last 11 2 ]
      [(5, 42), (6, 42), (81, 9), (100, 5), (101, 5), (11, 5), (30, 9), (120, d0), (40, 4095)]
      true true (nxt := [(57, 9)]) (pubs := [0, 0, 5, 0])
      (hs := [{ digestCol := 120, inputs := [.col 30, .zero], arity := 2 }])
      (rs := [{ wire := 40, bits := 12 }])
  , mkCase "combined-range-violation-reject"
      [ .gate (sub (v 5) (v 6)), .transition 3 5
      , .boundary .first (sub (v 100) (v 101)), .piBinding .last 11 2 ]
      [(5, 42), (6, 42), (81, 9), (100, 5), (101, 5), (11, 5), (30, 9), (120, d0), (40, 4096)]
      true true (nxt := [(57, 9)]) (pubs := [0, 0, 5, 0])
      (hs := [{ digestCol := 120, inputs := [.col 30, .zero], arity := 2 }])
      (rs := [{ wire := 40, bits := 12 }])
    -- the empty descriptor (vacuous-truth structure pin)
  , mkCase "empty-descriptor-accept" [] [] false false
  ]

/-! ## §3 — Rendering (the line format the Rust test embeds verbatim). -/

private def renderPairs (l : List (Nat × Int)) : String :=
  String.intercalate " " (l.map (fun p => s!"{p.1}:{p.2}"))

private def renderInts (l : List Int) : String :=
  String.intercalate " " (l.map toString)

/-- One case, rendered: 7 lines (`CASE`/`DESC`/`LOC`/`NXT`/`PUB`/`FLAGS`/`VERDICT`). The `DESC`
line is the CANONICAL `emitVmJson` bytes (the codec `EmitRoundtrip` proves lossless), re-parsed
on the Rust side by the production `parse_vm_descriptor`. -/
def GoldenCase.render (c : GoldenCase) : String :=
  s!"CASE {c.name}\nDESC {emitVmJson c.desc}\nLOC {renderPairs c.loc}\n" ++
  s!"NXT {renderPairs c.nxt}\nPUB {renderInts c.pubs}\n" ++
  s!"FLAGS {c.isFirst} {c.isLast}\nVERDICT {c.verdict}\n"

/-- The whole rendered corpus (what `main` prints and the Rust golden test embeds). -/
def goldenText : String :=
  String.join (corpus.map GoldenCase.render)

/-! ## §4 — Non-vacuity and edge pins (kernel-checked, no `native_decide`).

The corpus must separate: both verdict polarities occur, and the named R1/R2 edges decide the
way the verified reference says. Each pin evaluates `decideVm` THROUGH `GoldenCase.verdict`. -/

-- both polarities occur (the golden cannot be a constantly-true/false vacuity)
#guard (corpus.map GoldenCase.verdict).contains true
#guard (corpus.map GoldenCase.verdict).contains false
-- R1 edges: the boundary arm accepts on-row, rejects on-row, and is VACUOUS off-row
#guard (corpus.map GoldenCase.verdict) =
  [ true, false, true, false, true, true, false,        -- gates
    true, false, true,                                  -- transitions (incl. vacuous-at-last)
    true, false, true,                                  -- boundary .first
    true, false, true,                                  -- boundary .last
    true, false,                                        -- single-row window
    true, false, true,                                  -- piBinding .first
    true, false, true,                                  -- piBinding .last
    true, false, true, false, true,                     -- hash sites
    true, false, false,                                 -- ranges (incl. negative)
    true, false,                                        -- combined
    true ]                                              -- empty descriptor

end Dregg2.Circuit.Argus.InterpGolden

/-- Regenerate the Rust-embedded golden:
`lake env lean --run Dregg2/Circuit/Argus/InterpGolden.lean`. Namespaced so importing this
module into the `Dregg2` aggregator does not collide with another module's root `main`
(the regen `--run` still resolves the qualified `main`). -/
def Dregg2.Circuit.Argus.InterpGolden.main : IO Unit :=
  IO.println Dregg2.Circuit.Argus.InterpGolden.goldenText
