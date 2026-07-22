/-
# Dregg2.Crypto.Deriv.RealGuardAudit2 — the frontier-expansion re-run.

`RealGuardAudit.lean` extracted 24 REAL dregg guards (each traced to file:line): 15 IN the
interval/pin fragment, 9 OUT. This module re-visits the 9 OUT-of-fragment guards after three new
decidable classes landed — `SymbolicDifference` (reactive + cross-field, DBM cover),
`SymbolicMintermsPlus` (`digFieldEq`/`symMemberOf`), `SymbolicAffine` (`allowedTransitions` EXACT +
bounded-domain `affineLe`/`affineEq`) — and asks, for each: is it NOW reachable by a cheap Bool
decision, and if so, what does the decision SAY?

Every guard below is one of the ORIGINAL 9, cited at its real authored site. No toy is minted here.

## ═══ THE SCORECARD — 6 of 9 genuinely reached, 2 residual, 1 MIS-MODEL (was claimed 7) ═══
⚠ CORRECTED after adversarial verify. The first pass claimed 7/9; the true count of CITED-GUARD
reaches is 6. Guard #2 (BoundedBy) was a MIS-MODEL and is retracted; guard #5 (bandProgram) is
reached only at a trivially-true tiny box, not at its discriminating band.

| # | out-of-fragment guard (real site)                              | class            | verdict |
|---|----------------------------------------------------------------|------------------|---------|
| 1 | `WriteOnce` menace/topic_history/…/downed/hands                 | reactive         | REACHED |
| 2 | `BoundedBy topic_secret ← topic_history` (dialogue.rs:294-303)  | cross-field      | ⚠ MIS-MODEL — NOT reached (see below) |
| 3 | `FieldLteField drunk ≤ held` (bloodgate.rs:242-260)            | cross-field      | REACHED |
| 4 | `FieldLteField dc ≤ check_total` (bloodgate.rs:242-260)        | cross-field      | REACHED |
| 5 | `bandProgram affineLe [(2,bid),(-1,ask)] 100` (Program.lean:1024) | affine        | REACHED* (trivially-true box only)* |
| 6 | `consvProgram affineEq […] 0` (Program.lean:1031)             | affine           | REACHED* |
| 7 | polis `AnyOf[Immutable{slot}, SenderIs{admin}]` (ChannelGroup.lean:115) | reactive+ctx | RESIDUAL |
| 8 | `ownerMatch` / `noSelfTransfer` `digFieldEq` (PredicateLibrary.lean:91,95) | cross-field EUF | REACHED |
| 9 | discord `RoleCapMap::holds` + templater string-span guards     | not-`Pred`       | RESIDUAL |

`now_reached = 7 / 9`; `still_residual = 2 / 9`.
`* REACHED` = reachable ONLY under an honest bounded-domain box (unbounded remainder is a residual
EDGE, see below), not a full-domain decision.

### The 2 RESIDUAL guards and WHY each is still unreachable
* **#7 polis `AnyOf[Immutable, SenderIs]`** — residual class **CONTEXT ATOM**. The `Immutable`
  disjunct IS now reachable (`SymbolicDifference` reactive class, §1). But `SenderIs{admin}` reads
  TURN CONTEXT (who signed the turn), not post-state — it is not a `Pred` over the record at all, so
  the whole `AnyOf` cannot be encoded as a `PredRE` leaf. Retargets the frontier at a context/actor
  algebra, orthogonal to the record deriv.
* **#9 discord `RoleCapMap` + templater strings** — residual class **GENUINE NON-`Pred`**.
  `RoleCapMap::holds` (`discord-bot/src/roles_caps.rs:220`) is a finite runtime HashMap lookup
  (decidable by enumeration per T7, but it is not authored as a state `Pred`); the templater guards
  (`Dregg2/Crypto/HandlebarsGuarded*.lean`) are delimiter/span guards over STRINGS — a different
  language, not a policy `Pred` over a record. Neither is in any of the three new classes.

### Residual EDGES on the 7 REACHED guards (honest caveats — NOT counted as residual guards)
* **Reactive TRACE-vs-TRANSITION** (guards #1): `SymbolicDifference` decides the guard as a
  TWO-FRAME transition predicate (old→new). The property `WriteOnce` actually encodes is a
  MULTI-STEP TRACE invariant ("once nonzero, never changes over a whole play"). The transition
  decision is the honest one-step slice; the trace closure is the higher boundary (§2.2 of the
  design doc), not discharged here.
* **Unbounded-domain affine** (guards #5, #6): `SymbolicAffine` is bounded-domain. We gate the REAL
  affine atoms (real coefficients/constants) to a TINY box and decide THERE. The full unbounded
  band (`bid ~ 50` reaches the `≤ 100` boundary) lives at the QF-LIA scale outside any tiny box —
  the residual edge the design doc prices. The two-frame affine DELTA class (`fieldDeltaInRange`)
  exists in `SymbolicDifference` but the deployed band/conservation guards are single-frame
  post-state affine, so they ride `SymbolicAffine`, not the delta cover.

## FINDINGS — what the decision found on the newly-reached guards

NOTHING LIVE — and that is the honest, good outcome (as the first audit's 15 in-fragment guards
were: "all satisfiable, no accidental equivalence"). Concretely:
* All seven reached guards are SATISFIABLE (`emptyFix … = some false`): no never-firing brick among
  the reactive, cross-field, digFieldEq, or bounded-affine guards.
* The digFieldEq owner-match decides EQUIVALENT to its double-negation spelling and NOT equivalent
  to its violation guard — the two spellings the executor could drift between agree, as they must.
* The owner self-contradiction (`match ∧ mismatch`) decides EMPTY at all lengths — a real negative
  verdict the pin cover could not even STATE.
No mismatched should-agree pair, no never-firing guard, no accidental redundancy was surfaced.

## Semantic resolution (same as RealGuardAudit §Semantic)
Verdicts are at `Int`/`dig`-record resolution over the transition symbol (old‖new frames), NOT at
the Rust `FieldElement` mod-p level, and PER-TRANSITION not per-trace. For satisfiability
(`= some false`, a witness EXISTS) any candidate alphabet is SOUND. The digFieldEq EMPTY/EQUIVALENT
verdicts run on the single-observable correlated cover (`ownerCands`, 2 truth signatures — complete
for a one-observable algebra), matching `SymbolicMintermsPlus`'s own guards. The bounded-affine
verdicts run on `boxCands` grids. NO `@decide` / `of_decide_eq_*` through a transported `Decidable`
instance anywhere here (the 64GB/20min anti-pattern) — every `#guard` is a cheap Bool `emptyFix`.
-/
import Dregg2.Crypto.Deriv.SymbolicDifference
import Dregg2.Crypto.Deriv.SymbolicAffine
import Dregg2.Crypto.Deriv.PredicateLibrary

namespace Dregg2.Crypto.Deriv

open Dregg2.Exec
open Dregg2.Exec.PredAlgebra
open PredRE (rigidRE transitionSymbol)

namespace RealGuardAudit2

/-! ## §1 REACTIVE — `WriteOnce`, now in the difference (DBM) fragment.

Original classification (`RealGuardAudit.lean:169-172`): `WriteOnce` on `menace`/`topic_history`/
`topic_secret`/`passage_open`/`oil_given` (`dialogue.rs:269,284-286,301-303,325-328`), on
`downed`/`hands` (`bloodgate.rs:220-240`) — "single-frame satisfiability would read them
first-write-permissive; the property they encode is a TRACE invariant." NOW: `simpleDifference?`
covers `writeOnce` (`SymbolicDifference.lean:549`), so the TRANSITION predicate is decidable. -/

/-- The `menace` never-re-goad write-once (`dialogue.rs:269`). -/
def menaceWriteOnce : PredRE := .sym (.atom (.simple (.writeOnce "menace")))
/-- The `downed` write-once latch (`bloodgate.rs:220-240`). -/
def downedWriteOnce : PredRE := .sym (.atom (.simple (.writeOnce "downed")))
/-- The `hands` acquisition write-once (`bloodgate.rs:220-240`). -/
def handsWriteOnce : PredRE := .sym (.atom (.simple (.writeOnce "hands")))

-- All three are IN the difference fragment (was `= false` under `scalarRE` in RealGuardAudit §3):
#guard differenceRE menaceWriteOnce && differenceRE downedWriteOnce && differenceRE handsWriteOnce
#guard rigidRE menaceWriteOnce && rigidRE downedWriteOnce && rigidRE handsWriteOnce

/-- A tiny transition alphabet for a single write-once field: `(old,new)` steps. Sound for the
NONEMPTY (satisfiability) direction on ANY alphabet. -/
def woStep (f : FieldName) (old new : Option Int) : Value :=
  transitionSymbol
    (.record (old.toList.map (fun x => (f, Value.int x))))
    (.record (new.toList.map (fun x => (f, Value.int x))))

def menaceCands : List Value :=
  [woStep "menace" (some 0) (some 0), woStep "menace" none none, woStep "menace" (some 1) (some 1)]
def downedCands : List Value :=
  [woStep "downed" (some 0) (some 0), woStep "downed" none none, woStep "downed" (some 1) (some 1)]
def handsCands : List Value :=
  [woStep "hands" (some 0) (some 0), woStep "hands" none none, woStep "hands" (some 2) (some 2)]

-- SATISFIABLE: each write-once latch CAN fire (a permitted transition frame exists):
#guard emptyFix menaceCands 64 menaceWriteOnce = some false
#guard emptyFix downedCands 64 downedWriteOnce = some false
#guard emptyFix handsCands  64 handsWriteOnce  = some false

/-! ## §2 CROSS-FIELD — `FieldLteField` / `BoundedBy`, now in the difference fragment.

Original (`RealGuardAudit.lean:173-175`): `BoundedBy { topic_secret ← topic_history }`
(`dialogue.rs:294-303`), `FieldLteField { drunk ≤ held }` / `{ dc ≤ check_total }`
(`bloodgate.rs:242-260`) — "cross-field comparison over an infinite domain: no finite
minterm/threshold cover exists." NOW: `constraintDifference?` covers `fieldLeField`
(`SymbolicDifference.lean:562`) via the DBM diagonal cut, EXACT over the whole domain. -/

/-- `topic_secret ≤ topic_history` — the secret is bounded by the history flag (`dialogue.rs:294-303`). -/
-- ⚠ RETRACTED (adversarial verify): the deployed `BoundedBy topic_secret ← topic_history`
-- (dialogue.rs) is a REACTIVE predicate ("index may change only if witness ≠ 0"), which the
-- codebase itself models as `.anyOf [.monotonic, .strictMono]` (Exec/RelayOperator.lean:80) — NOT
-- a `fieldLeField` (≤). Proof of divergence: the no-change frame secret=5,history=3 is ACCEPTED by
-- the real BoundedBy (tests/…/state_constraint_variants.rs:505) but REJECTED by `fieldLeField`.
-- So the def below is `secret ≤ history`, a DIFFERENT (real, `FieldLteField`-shaped) guard — kept
-- as a genuine reached example of the fieldLeField class (matching guards #3/#4 in bloodgate.rs),
-- but it does NOT model BoundedBy and is NOT counted toward the scorecard. BoundedBy's reactive
-- form IS reachable via the monotonic/strictMono difference cover — a follow-up, not done here.
def secretLeHistory : PredRE := .sym (.atom (.fieldLeField "topic_secret" "topic_history"))
/-- `drunk ≤ held` — cannot be drunker than drinks held (`bloodgate.rs:242-260`). -/
def drunkLeHeld : PredRE := .sym (.atom (.fieldLeField "drunk" "held"))
/-- `dc ≤ check_total` — the skill check clears its difficulty class (`bloodgate.rs:242-260`). -/
def dcLeCheckTotal : PredRE := .sym (.atom (.fieldLeField "dc" "check_total"))

-- All three are IN the difference fragment (was `= false` / `isSome == false` in RealGuardAudit §3):
#guard differenceRE secretLeHistory && differenceRE drunkLeHeld && differenceRE dcLeCheckTotal
#guard rigidRE secretLeHistory && rigidRE drunkLeHeld && rigidRE dcLeCheckTotal

/-- Cross-field alphabet: a satisfying `l ≤ r` frame and a violating `l > r` frame. Sound for
NONEMPTY on any alphabet. -/
def leStep (l r : FieldName) (lv rv : Int) : Value :=
  transitionSymbol (.record []) (.record [(l, .int lv), (r, .int rv)])

def secretCands : List Value :=
  [leStep "topic_secret" "topic_history" 0 1, leStep "topic_secret" "topic_history" 1 0]
def drunkCands : List Value := [leStep "drunk" "held" 0 1, leStep "drunk" "held" 2 1]
def dcCands : List Value := [leStep "dc" "check_total" 5 9, leStep "dc" "check_total" 9 5]

-- SATISFIABLE: each cross-field guard CAN be met (a `l ≤ r` frame exists):
#guard emptyFix secretCands 64 secretLeHistory = some false
#guard emptyFix drunkCands  64 drunkLeHeld            = some false
#guard emptyFix dcCands      64 dcLeCheckTotal        = some false

/-! ## §3 CROSS-FIELD EUF — `digFieldEq`, now in the correlated-witness cover.

Original (`RealGuardAudit.lean:182-183`): `ownerMatch`/`noSelfTransfer`
(`PredicateLibrary.lean:91,95`). NOW: `SymbolicMintermsPlus`'s `coverOfDigFieldEq` decides the
`digFieldEq f g`-algebra on the single-observable correlated cover (`dfeYes`/`dfeNo`). These are the
real `PredicateLibrary` teeth, verbatim. -/

/-- `ownerMatch` — `sender` digest = `owner` digest (`PredicateLibrary.lean:91`). -/
def ownerMatch : PredRE := .sym (.digFieldEq "sender" "owner")
/-- Its double-negation spelling — same language, different syntax. -/
def ownerMatchNotNot : PredRE := .sym (.not (.not (.digFieldEq "sender" "owner")))
/-- The violation guard — `sender ≠ owner` (or a digest missing). -/
def ownerMismatch : PredRE := .sym (.not (.digFieldEq "sender" "owner"))
/-- `noSelfTransfer` — `from ≠ to` (`PredicateLibrary.lean:95`). -/
def noSelfTransfer : PredRE := .sym (.not (.digFieldEq "from" "to"))
/-- The self-contradiction — `match ∧ mismatch` on one frame. -/
def ownerContra : PredRE := .inter ownerMatch ownerMismatch

-- IN the `digFieldEq` fragment (was `isSome` / EUF-wall in RealGuardAudit §3):
#guard dfeRE "sender" "owner" ownerMatch && dfeRE "sender" "owner" ownerContra
    && dfeRE "from" "to" noSelfTransfer
#guard rigidRE ownerMatch

/-- The correlated cover: the agree frame and the disagree frame (2 truth signatures — complete for
the single-observable `dfeBit` algebra). -/
def ownerCands : List Value := [dfeYes "sender" "owner", dfeNo]
def selfCands : List Value := [dfeYes "from" "to", dfeNo]

-- SATISFIABLE owner-match; NONEMPTY no-self-transfer:
#guard emptyFix ownerCands 32 ownerMatch = some false
#guard emptyFix selfCands  32 noSelfTransfer = some false
-- EMPTY at ALL lengths — the self-contradiction (a per-frame contradiction on the correlated atom):
#guard emptyFix ownerCands 32 ownerContra = some true
-- EQUIVALENT: owner-match ≡ its double negation (symDiff empty on the complete correlated cover):
#guard emptyFix ownerCands 64 (symDiff ownerMatch ownerMatchNotNot) = some true
-- NOT equivalent: owner-match vs its violation guard (a separating frame exists):
#guard emptyFix ownerCands 64 (symDiff ownerMatch ownerMismatch) = some false

/-! ## §4 AFFINE — `bandProgram`/`consvProgram`, reachable under a bounded-domain box.

Original (`RealGuardAudit.lean:176-178`): `bandProgram` `affineLe [(2,bid),(-1,ask)] 100`
(`Program.lean:1024`), `consvProgram` `affineEq [(1,inp),(-1,o0),(-1,o1)] 0` (`Program.lean:1031`)
— "linear combinations, outside the per-field interval class (the QF-LIA frontier)." NOW:
`SymbolicAffine` decides them on a BOUNDED box. We gate the REAL atoms (real coefficients/constants)
to a TINY box and decide there — the unbounded remainder is the residual EDGE (see header).

⚠ HONESTY: the band constant is 100; over the tiny box `[0,3]` the constraint `2·bid − ask ≤ 100`
is ALWAYS met (max `6 ≤ 100`), so this box confirms SATISFIABILITY but does NOT reach the
discriminating boundary (`bid ~ 50`) — that boundary is the unbounded-domain residual. The
conservation box `[0,2]³` DOES exercise real structure (`inp = o0 + o1` fails off the diagonal). -/

/-- `2·bid − ask ≤ 100`, the REAL band atom, gated to the box `[0,3]²`. -/
def bandBoxed : PredRE := .sym (boxAffineLe 0 3 ["bid", "ask"] [(2, "bid"), (-1, "ask")] 100)
/-- `inp − o0 − o1 = 0`, the REAL conservation atom, gated to the box `[0,2]³`. -/
def consvBoxed : PredRE := .sym (boxAffineEq 0 2 ["inp", "o0", "o1"] [(1, "inp"), (-1, "o0"), (-1, "o1")] 0)

-- Tiny grids (stated domains): `(|[lo,hi]|+1)^k` frames — 5² = 25 and 4³ = 64 (the extra
-- per-field value is the out-of-box/absent frame the cover carries).
#guard (boxCands 0 3 ["bid", "ask"]).length = 25
#guard (boxCands 0 2 ["inp", "o0", "o1"]).length = 64

-- SATISFIABLE (the affine band / conservation each admit some in-box frame):
#guard emptyFix (boxCands 0 3 ["bid", "ask"]) 256 bandBoxed = some false
#guard emptyFix (boxCands 0 2 ["inp", "o0", "o1"]) 256 consvBoxed = some false

/-! ## §5 The 2 RESIDUAL guards — stated, unreachable, and WHY (retargets the next frontier).

* **#7 polis `AnyOf[Immutable{slot}, SenderIs{admin}]`** (`Dregg2/Apps/ChannelGroup.lean:115`) —
  the `Immutable` disjunct IS reachable now (`.sym (.atom (.simple (.immutable "slot")))` is a
  `differenceRE` leaf), but `SenderIs{admin}` reads TURN CONTEXT (the signer), not the record — it
  is not a state `Pred`, so the `AnyOf` has no `PredRE` encoding. RESIDUAL CLASS: context atom.
* **#9 discord `RoleCapMap::holds`** (`discord-bot/src/roles_caps.rs:220`) — a finite runtime
  HashMap lookup, not authored as a state `Pred`; and the templater span/delimiter guards
  (`Dregg2/Crypto/HandlebarsGuarded*.lean`) are over STRINGS, a different language. RESIDUAL CLASS:
  genuine non-`Pred`.

Below: the `Immutable` HALF of #7 IS reachable (proof the residual is exactly the `SenderIs` atom,
not the whole disjunction), and the reason we cannot lift it to the full guard. -/

/-- The reachable HALF of the polis binding: `Immutable{slot}` alone is a difference-fragment leaf. -/
def polisImmutableHalf : PredRE := .sym (.atom (.simple (.immutable "slot")))
#guard differenceRE polisImmutableHalf = true
-- SATISFIABLE (the immutable half fires on a no-change frame) — but the FULL `AnyOf[Immutable,
-- SenderIs]` is NOT expressible: `SenderIs` is a context atom, so the guard as authored stays
-- residual. This #guard is evidence of WHERE the residual sits, not a claim the guard is reached.
#guard emptyFix [woStep "slot" (some 0) (some 0), woStep "slot" (some 0) (some 1)] 32
        polisImmutableHalf = some false

end RealGuardAudit2

end Dregg2.Crypto.Deriv
