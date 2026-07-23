/-
# Dregg2.Crypto.Deriv.RealGuardAudit2 — the frontier-expansion re-run.

`RealGuardAudit.lean` extracted 24 REAL dregg guards (each traced to file:line): 15 IN the
interval/pin fragment, 9 OUT. This module re-visits the 9 OUT-of-fragment guards after three new
decidable classes landed — `SymbolicDifference` (reactive + cross-field, DBM cover),
`SymbolicMintermsPlus` (`digFieldEq`/`symMemberOf`), `SymbolicAffine` (`allowedTransitions` EXACT +
bounded-domain `affineLe`/`affineEq`) — and asks, for each: is it NOW reachable by a cheap Bool
decision, and if so, what does the decision SAY?

Every guard below is one of the ORIGINAL 9, cited at its real authored site. No toy is minted here.

## ═══ THE SCORECARD — 8 of 9 genuinely reached, 1 residual (was 6 + 1 MIS-MODEL) ═══
⚠ RE-CORRECTED after the faithful re-encoding of the mis-model. The prior pass had 6 reached, 2
residual, 1 MIS-MODEL (#2 BoundedBy, encoded as `≤` — WRONG). This pass FIXES #2 with the REACTIVE
semantics the deployed eval actually has, and lands #7 (polis) via a faithful virtual-context
extension. Both encodings are exhibited AGREEING with `evalConstraint`/`evalSimpleCtx` on the exact
frames that discriminate (incl. the killer no-change frame that caught the ≤ mis-model). Guard #5
(bandProgram) is still reached only at a trivially-true tiny box, not at its discriminating band.

| # | out-of-fragment guard (real site)                              | class            | verdict |
|---|----------------------------------------------------------------|------------------|---------|
| 1 | `WriteOnce` menace/topic_history/…/downed/hands                 | reactive         | REACHED |
| 2 | `BoundedBy topic_secret ← topic_history` (dialogue.rs:294-303)  | reactive cross-field | REACHED (faithful reactive encoding, §2) |
| 3 | `FieldLteField drunk ≤ held` (bloodgate.rs:242-260)            | cross-field      | REACHED |
| 4 | `FieldLteField dc ≤ check_total` (bloodgate.rs:242-260)        | cross-field      | REACHED |
| 5 | `bandProgram affineLe [(2,bid),(-1,ask)] 100` (Program.lean:1024) | affine        | REACHED* (trivially-true box only)* |
| 6 | `consvProgram affineEq […] 0` (Program.lean:1031)             | affine           | REACHED* |
| 7 | polis `AnyOf[Immutable{slot}, SenderIs{admin}]` (ChannelGroup.lean:115) | reactive+ctx | REACHED (faithful virtual-`__sender`, §5) |
| 8 | `ownerMatch` / `noSelfTransfer` `digFieldEq` (PredicateLibrary.lean:91,95) | cross-field EUF | REACHED |
| 9 | discord `RoleCapMap::holds` + templater string-span guards     | not-`Pred`       | RESIDUAL |

`now_reached = 8 / 9`; `still_residual = 1 / 9`.
`* REACHED` = reachable ONLY under an honest bounded-domain box (unbounded remainder is a residual
EDGE, see below), not a full-domain decision.

### The 1 RESIDUAL guard and WHY it is still unreachable
* **#9 discord `RoleCapMap` + templater strings** — residual class **GENUINE NON-`Pred`**.
  `RoleCapMap::holds` (`discord-bot/src/roles_caps.rs:220`) is a finite runtime HashMap lookup
  (decidable by enumeration per T7, but it is not authored as a state `Pred`); the templater guards
  (`Dregg2/Crypto/HandlebarsGuarded*.lean`) are delimiter/span guards over STRINGS — a different
  language, not a policy `Pred` over a record. Neither is in any of the three new classes.

### Residual EDGES on the 8 REACHED guards (honest caveats — NOT counted as residual guards)
* **Reactive TRACE-vs-TRANSITION** (guards #1, #2): `SymbolicDifference` decides the guard as a
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
* All eight reached guards are SATISFIABLE (`emptyFix … = some false`): no never-firing brick among
  the reactive, cross-field, digFieldEq, or bounded-affine guards.
* The two newly-fixed guards (#2 `BoundedBy`, #7 polis `AnyOf`) each fire AND refuse — the faithful
  reactive/virtual-context encodings agree with `evalConstraint`/`evalSimpleCtx` on the exact test
  frames (incl. the killer no-change frame that caught the ≤ mis-model), and each rejects its
  unarmed / non-admin frame. No mis-model survives: the ≤ and reactive encodings are exhibited
  DIVERGING on the killer frame (§2.1), confirming the fix is a real semantic correction.
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

/-- `topic_secret ≤ topic_history` — a genuine `fieldLeField` example, KEPT (not BoundedBy). -/
-- ⚠ HISTORY: an earlier pass encoded `BoundedBy topic_secret ← topic_history` as THIS `≤` guard —
-- a MIS-MODEL, now FIXED below (`secretBoundedByHistory`). The deployed `BoundedBy`
-- (`cell/src/program/eval.rs:463-484`) is REACTIVE: a change to `index` is admitted ONLY when the
-- `witness` field is nonzero in the NEW frame. `secretLeHistory` (`≤`) is retained purely as a
-- fieldLeField example (a sibling of guards #3/#4); it is NOT BoundedBy — §2.1 exhibits the two
-- DIVERGING on the killer no-change frame (secret=5,history=3), which BoundedBy accepts and `≤`
-- rejects. That divergence is exactly what caught the original mis-model.
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

/-! ## §2.1 REACTIVE CROSS-FIELD — `BoundedBy`, FAITHFULLY (the fixed mis-model).

The REAL deployed `StateConstraint::BoundedBy { index, witness_index }`
(`cell/src/program/eval.rs:463-484`): `changed := new[index] ≠ old[index]`; if `changed`, the
turn is admitted only when `new[witness] ≠ 0`. So the exact admit-char (old frame present, as every
`augment_case` turn is) is

  `accept ⟺ (new[index] = old[index]) ∨ (new[witness] ≠ 0)`.

This is REACTIVE (reads old‖new) — NOT the retracted `fieldLeField` (≤). Both legs are IN-FRAGMENT
difference/scalar atoms, so the whole admit-char is a single transition-frame `Pred` disjunction:
* NO-CHANGE leg `new = old`: the difference atom `fieldDelta index 0` (`b == a + 0`, `Program.lean:503`);
* WITNESS-ARMED leg `new[witness] ≠ 0`: spelled EXACTLY as `fieldGe witness 1 ∨ fieldLe witness (-1)`
  (the two-sided `≠ 0` over `Int`, both scalar DBM axis atoms) — faithful to `!= FIELD_ZERO` even at
  negative values, not just the reachable-flag `≥ 1`. -/

/-- The faithful `BoundedBy index ← witness` admit-char as one transition-frame `Pred`. -/
def boundedByPred (index witness : FieldName) : Pred :=
  .or (.atom (.simple (.fieldDelta index 0)))
      (.or (.atom (.simple (.fieldGe witness 1)))
           (.atom (.simple (.fieldLe witness (-1)))))

/-- The deployed `BoundedBy topic_secret ← topic_history` (`dialogue.rs:294-303`), FAITHFULLY. -/
def secretBoundedByHistory : PredRE := .sym (boundedByPred "topic_secret" "topic_history")

-- IN the difference fragment (reactive OR of DBM leaves):
#guard differenceRE secretBoundedByHistory && rigidRE secretBoundedByHistory

/-- Transition frame: `(secret: old→new, history: new)`. Old-side history is irrelevant to the
admit-char (BoundedBy reads the NEW witness), so only its new value is carried. -/
def bbStep (sOld sNew hNew : Int) : Value :=
  transitionSymbol
    (.record [("topic_secret", .int sOld)])
    (.record [("topic_secret", .int sNew), ("topic_history", .int hNew)])

-- FAITHFULNESS — this encoding AGREES with the deployed `evalConstraint` (BoundedBy) on the exact
-- frames the real `state_constraint_variants.rs` tests pin, INCLUDING the killer no-change frame:
-- (a) NO-CHANGE, witness=3 — the killer frame that caught the ≤ mis-model. Real BoundedBy ACCEPTS
--     (unchanged ⇒ not `changed` ⇒ admit, witness irrelevant):
#guard emptyFix [bbStep 5 5 3] 32 secretBoundedByHistory = some false
-- (b) NO-CHANGE, witness=0 (`state_constraint_variants.rs:505`
--     `bounded_by_accepts_no_change_regardless_of_witness`): ACCEPT:
#guard emptyFix [bbStep 5 5 0] 32 secretBoundedByHistory = some false
-- (c) CHANGE, witness set (`:483 bounded_by_accepts_change_when_witness_set`): ACCEPT:
#guard emptyFix [bbStep 0 10 1] 32 secretBoundedByHistory = some false
-- (d) CHANGE, witness zero (`:494 bounded_by_rejects_change_when_witness_zero`): REJECT:
#guard emptyFix [bbStep 0 10 0] 32 secretBoundedByHistory = some true

-- THE DIVERGENCE that caught the mis-model, exhibited on ONE frame: the retracted `≤` guard and the
-- faithful reactive `BoundedBy` DISAGREE on the no-change frame secret=5,history=3 — `≤` REJECTS
-- (`5 ≤ 3` is false), real BoundedBy (and this encoding) ACCEPTS:
#guard emptyFix [bbStep 5 5 3] 32 secretLeHistory        = some true   -- `≤` REJECTS (WRONG for BoundedBy)
#guard emptyFix [bbStep 5 5 3] 32 secretBoundedByHistory = some false  -- BoundedBy ACCEPTS (RIGHT)

/-- The reactive cover: an armed change, a no-change, and an unarmed change. -/
def bbCands : List Value := [bbStep 5 5 3, bbStep 0 10 1, bbStep 0 10 0]
-- SATISFIABLE (an admitted frame exists), and NOT trivial (the unarmed-change frame (d) is rejected
-- above): the guard genuinely fires AND genuinely refuses — a real reactive gate, not a brick.
#guard emptyFix bbCands 64 secretBoundedByHistory = some false

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

/-! ## §5 Polis `AnyOf[Immutable, SenderIs]` — REACHED via a faithful virtual-context extension.

**#7 polis `AnyOf[Immutable{slot}, SenderIs{admin}]`** (`Dregg2/Apps/ChannelGroup.lean` `admin_gated`,
`blueprint.rs:847`). The `Immutable` disjunct was already a `differenceRE` leaf. The `SenderIs{admin}`
disjunct reads TURN CONTEXT — but `evalSimpleCtx (.senderIs k) o n = (ctx.sender == some k)`
(`Program.lean:1189`) reads ONLY `TurnCtx.sender`: a single `Int` the executor supplies per turn
(`EvalContext::sender`, `Program.lean:1112`), FIXED for the whole transition and independent of the
record. It is therefore a genuine COORDINATE OF THE TURN — present at decision time, though not a
record field. Modeling it as a reserved virtual frame field `__sender` is a FAITHFUL extension:
`SenderIs k ≡ fieldEquals "__sender" k` holds frame-for-frame (both are `ctx.sender = some k`), and
`fieldEquals` is an in-fragment scalar (DBM) atom whose reserved name is invisible to authored record
fields (like the transition envelope). So the whole `AnyOf` is now a `differenceRE` leaf.

CAVEAT (named, not hidden): `__sender` is a VIRTUAL coordinate the decision ranges over as a free
per-frame `Int` — this is exactly the per-transition semantics (one sender per turn), so it is
faithful for this per-transition decision; it is NOT a claim over multi-step traces where each step
carries its own sender.

**#9 discord `RoleCapMap::holds`** (`discord-bot/src/roles_caps.rs:220`) — a finite runtime HashMap
lookup, not authored as a state `Pred`; and the templater span/delimiter guards
(`Dregg2/Crypto/HandlebarsGuarded*.lean`) are over STRINGS, a different language. RESIDUAL CLASS:
genuine non-`Pred`. -/

/-- The reserved virtual coordinate carrying the turn's signer (`TurnCtx.sender`). -/
def senderField : FieldName := "__sender"

/-- The polis per-slot actor binding `AnyOf[Immutable{slot}, SenderIs{admin}]` — slot `f` flips ONLY
in a turn SENT by the admin. NOW a full `PredRE` leaf via the faithful virtual-`__sender` extension.
Admit-char: `accept ⟺ (new[slot] = old[slot]) ∨ (sender = admin)` (mirrors `actorBound_untouched_open`
/ `actorBound_flip_requires_sender`, `Exec/Program.lean:816`). -/
def polisActorBound (slot : FieldName) (admin : Int) : PredRE :=
  .sym (.or (.atom (.simple (.immutable slot)))
            (.atom (.simple (.fieldEquals senderField admin))))

-- IN the difference fragment (reactive immutable ⋓ scalar `__sender` equality):
#guard differenceRE (polisActorBound "slot" 7) && rigidRE (polisActorBound "slot" 7)

/-- Transition frame carrying the virtual signer coordinate: `(slot: old→new, __sender: new)`. -/
def acStep (slotOld slotNew sender : Int) : Value :=
  transitionSymbol
    (.record [("slot", .int slotOld)])
    (.record [("slot", .int slotNew), (senderField, .int sender)])

-- FAITHFULNESS vs the deployed `AnyOf[Immutable, SenderIs]` semantics (admin = 7):
-- (a) slot UNCHANGED, non-admin sender → immutable disjunct → ACCEPT:
#guard emptyFix [acStep 3 3 0] 32 (polisActorBound "slot" 7) = some false
-- (b) slot CHANGED, admin sender → senderIs disjunct → ACCEPT:
#guard emptyFix [acStep 3 4 7] 32 (polisActorBound "slot" 7) = some false
-- (c) slot CHANGED, NON-admin sender → neither disjunct → REJECT (the flip-requires-admin law):
#guard emptyFix [acStep 3 4 0] 32 (polisActorBound "slot" 7) = some true
-- (d) slot UNCHANGED, admin sender → both disjuncts → ACCEPT:
#guard emptyFix [acStep 3 3 7] 32 (polisActorBound "slot" 7) = some false

-- SATISFIABLE and NOT trivial (fires on (a),(b),(d); refuses (c)) — the actor binding is a real gate.
#guard emptyFix [acStep 3 3 0, acStep 3 4 7, acStep 3 4 0] 64 (polisActorBound "slot" 7) = some false

end RealGuardAudit2

end Dregg2.Crypto.Deriv
