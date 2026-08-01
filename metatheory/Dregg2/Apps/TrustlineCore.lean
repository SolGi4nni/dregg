/-
# `Dregg2.Apps.TrustlineCore` — the RUNTIME-CALLABLE trustline DRAW/REPAY/SETTLE decision.

## What this is

`Dregg2/Apps/Trustline.lean` proves the trustline crown: `draw` refuses a replayed digest
(`draw_replay_refused`, and `draw_replay_refused_across_epochs` — a digest committed at step `n` is
refused at EVERY later step, no matter how many settle epochs), refuses an over-line amount
(`over_line_draw_refused`), `repay` refuses over-repayment (`over_repay_refused`), the bilateral
wells conserve (`bilateral_conserved`), and settlement is a conserving move on the hard-asset pair
(`settlePay_conserves_hard`, `settleAll_clears`). 78 theorems, zero `sorry`.

Those `def`s were plain `def`s — not `@[export]`ed — so the spend authority they specify was
re-implemented in Rust roughly sixteen times, none of which was the decision:

  * `coord/src/budget.rs::BudgetSlice::{try_debit, try_debit_fresh, refund, unwind_debit}` — the
    Stingray bounded counter, whose `try_debit` is a plain Rust comparison consulting no gate;
  * `turn/src/budget_gate.rs::BudgetSlice` — a SECOND struct of the same name that carries a
    `debits: Vec<DebitDigest>` field it WRITES AND NEVER CHECKS, i.e. it has no anti-replay leg at
    all, and it is the one that gates live turn execution;
  * `node/src/trustline_service.rs` (2,588 lines) — whose own header calls this module a "twin";
  * `narrator/src/ledger.rs::BudgetLedger` (reserve/true-up = draw/repay), `cell/src/allowance.rs`
    (a per-epoch line), `dregg-agent/src/{budget,meter}.rs`, and a further ~10.

A Rust mirror plus a differential test is NOT a verified implementation — there is no formal
semantics of Rust, so a case-test proves nothing about all inputs.

This module is where `Line`, `draw`, `repay`, `Channel`, `settlePay` and `settleAll` now LIVE, and it
is `@[export dregg_trustline_step]`-ed so Rust CALLS it. `Trustline` imports this module, so every
theorem it proves is a theorem about THESE functions — the ones the C-ABI entry runs. There is no
second model.

## Import discipline

Imports NOTHING beyond core `Init` — no Mathlib. The `@[export]`ed object must be self-contained so
its leanc-emitted `.c` splices into `libdregg_lean.a` without dragging a Mathlib-tactic initializer
closure into the FFI link (same discipline as `Dregg2.Apps.DelegAdmit` /
`Dregg2.Circuit.CrossCellConserveDecision` / `Dregg2.Exec.DeployedConstraint`; see
`dregg-lean-ffi/src/lean_init.c`).

`Trustline.lean` itself imports `Dregg2.Proof.Stingray` (→ `Dregg2.Confluence` →
`Mathlib.Order.Lattice`) and `Dregg2.Tactics` (→ `Mathlib.Tactic.Ring`), so it is Mathlib-tainted
twice over and can never carry the export. The two defs that genuinely need Stingray —
`Line.slice` and `Line.remaining_eq_slice` — STAY THERE; they are proof-side bridges and nothing
computational needs them.

Every construct below is core `Init`: `Nat`, `Int`, `List Nat`, `Option`, `String`, and
`List.Nodup` (which is Lean 4 core at `Init/Data/List/Basic.lean:1401`, NOT Mathlib).
-/

namespace Dregg2.Apps.TrustlineCore

set_option autoImplicit false

/-! ## §1 — The trustline state (the bilateral cell's registers). -/

/-- The bilateral trustline: issuer A extends holder B a line of `ceiling`. Directional — this
record IS the A→B line; a B→A line is a separate trustline with the roles swapped. -/
structure Line where
  /-- The extended line N — the attenuation bound (`Slice.ceiling`). Immutable register. -/
  ceiling : Nat
  /-- Outstanding drawn amount — the shared counter (`Slice.spent`). -/
  drawn : Nat
  /-- Committed draw digests (`BudgetSlice::debits`, `turn/src/budget_gate.rs:29`) — the
  no-double-draw registry. A digest is one-shot FOREVER (repayment does not resurrect it). -/
  draws : List Nat
  /-- The holder's credit balance in the issuer-asset: `+drawn`. -/
  holderAcct : Int
  /-- The issuer's signed well in its own asset: `−drawn` (the issuer-move model — the draw is
  PRODUCTION at the issuer's negative-capable well, never an out-of-thin-air mint). -/
  issuerWell : Int
  deriving Repr, DecidableEq

/-- Remaining undrawn line (`BudgetSlice::remaining`, truncated subtraction = saturating). -/
def Line.remaining (t : Line) : Nat := t.ceiling - t.drawn

/-- **Well-formedness — the reachable-state invariant.** Drawn within the line; the bilateral pair
carries exactly `±drawn`; the digest registry is duplicate-free. -/
def Line.WF (t : Line) : Prop :=
  t.drawn ≤ t.ceiling
    ∧ t.holderAcct = (t.drawn : Int)
    ∧ t.issuerWell = -(t.drawn : Int)
    ∧ t.draws.Nodup

instance (t : Line) : Decidable t.WF := by
  unfold Line.WF; infer_instance

/-! ## §2 — Birth, draw, repay (the ops). -/

/-- **`init` — the BIRTH of the line**: issuer extends a fresh line of `n`. Nothing drawn, no
digests, both wells level. The REAL birth must be funded by a ledger debit at the issuer; this is
the post-birth cell state it installs. -/
def Line.init (n : Nat) : Line :=
  { ceiling := n, drawn := 0, draws := [], holderAcct := 0, issuerWell := 0 }

/-- **`draw` — the holder exercises the line** (`BudgetSlice::try_debit` + digest registration).
Fail-closed twice over: a replayed digest is refused (no-double-draw); an amount beyond the
remaining line is refused (the attenuation bound). On commit: counter up, digest burned, holder
credit up, issuer well down — a MOVE against the issuer's well. -/
def draw (t : Line) (digest amt : Nat) : Option Line :=
  if digest ∈ t.draws then none
  else if amt ≤ t.ceiling - t.drawn then
    some { t with drawn := t.drawn + amt
                , draws := digest :: t.draws
                , holderAcct := t.holderAcct + (amt : Int)
                , issuerWell := t.issuerWell - (amt : Int) }
  else none

/-- **`repay` — the holder restores the line.** Fail-closed: repaying more than is drawn is
refused (over-repayment would MINT credit at the issuer's well). On commit: counter down, holder
credit down, issuer well up — the inverse move. The digest registry is untouched: spent digests
stay burned. -/
def repay (t : Line) (amt : Nat) : Option Line :=
  if amt ≤ t.drawn then
    some { t with drawn := t.drawn - amt
                , holderAcct := t.holderAcct - (amt : Int)
                , issuerWell := t.issuerWell + (amt : Int) }
  else none

/-! ## §3 — Settlement against the hard-asset ledger. -/

/-- A trustline together with the parties' hard-asset balances (the settlement target ledger). -/
structure Channel where
  tl : Line
  /-- Issuer's hard-asset balance (e.g. the devnet payment asset). -/
  issuerHard : Int
  /-- Holder's hard-asset balance. -/
  holderHard : Int
  deriving Repr, DecidableEq

/-- **`settlePay`** — settle `amt` of the outstanding draw: the holder pays `amt` hard asset to
the issuer AND the credit legs unwind by `amt` (a `repay`). Fail-closed via `repay`'s gate. -/
def settlePay (c : Channel) (amt : Nat) : Option Channel :=
  (repay c.tl amt).map fun tl' =>
    { tl := tl', issuerHard := c.issuerHard + (amt : Int), holderHard := c.holderHard - (amt : Int) }

/-- **`settleAll`** — close the line: settle the whole outstanding draw. Total — the full repay
always fires (`drawn ≤ drawn`). -/
def settleAll (c : Channel) : Channel := (settlePay c c.tl.drawn).getD c

/-! ## §3b — THE SETTLED REGISTER: the shape the node actually deploys.

⚑ WHY THIS EXISTS, and why the export dispatches HERE and not on §2.

The deployed trustline cell carries THREE registers — `line`, `drawn` and `settled`
(`node/src/trustline_service.rs:319-321`) — and its repay gate is
`amt ≤ drawn − settled` (`post_trustline_repay`, `trustline_service.rs:1155-1161`), which is
STRICTLY TIGHTER than §2's `amt ≤ drawn`. Settled credit is hard money already paid out and
cannot be repaid back.

So routing the deployed repay onto §2's `repay` would ADMIT every amount in
`(drawn − settled, drawn]` that is refused today — a WEAKENED CHECK on a hard-asset path, which
is the one thing a routing pass may never do. §2 is not wrong; it is a smaller object. The
export therefore dispatches the SETTLED verbs below, and §2 survives as the object they are
built from and the theorems are lifted through.

Likewise `settleS` — not `settlePay` — is the deployed settle: it marches the MONOTONE
redemption register and leaves `drawn` in place. §3's `settlePay`/`settleAll` are the
*pureCredit* axis point (the holder pays the issuer hard value and the credit legs unwind);
the deployed fullReserve close moves escrow → HOLDER, the opposite direction over a different
amount. There is no verb here for that, and none is invented. -/

/-- A trustline with the settlement register: §1's `Line` + `settled` (`TL_SETTLED_SLOT`). -/
structure SLine where
  /-- The underlying line (the §1 registers). -/
  tl : Line
  /-- Cumulative drawn value already redeemed to the holder by epoch settlement. Monotone. -/
  settled : Nat
  deriving Repr, DecidableEq

/-- Outstanding unsettled draw — the deployed repay/settle budget (`drawn − settled`). -/
def SLine.outstanding (s : SLine) : Nat := s.tl.drawn - s.settled

/-- Settled well-formedness: the line is WF and `settled ≤ drawn` (program tooth 4). -/
def SLine.WF (s : SLine) : Prop := s.tl.WF ∧ s.settled ≤ s.tl.drawn

instance (s : SLine) : Decidable s.WF := by
  unfold SLine.WF; infer_instance

/-- Birth of a settled line: fresh line, nothing settled. -/
def SLine.init (n : Nat) : SLine := { tl := Line.init n, settled := 0 }

/-- Draw on the settled line — the §2 gate unchanged (`settled` plays no part in draws:
the deployed remaining is `line − drawn`, `resolve_trustline`). -/
def drawS (s : SLine) (digest amt : Nat) : Option SLine :=
  (draw s.tl digest amt).map fun tl' => { s with tl := tl' }

/-- Repay with the SETTLED FLOOR (the deployed gate, `post_trustline_repay`): fail-closed
beyond the outstanding `drawn − settled`. -/
def repayS (s : SLine) (amt : Nat) : Option SLine :=
  if amt ≤ s.outstanding then (repay s.tl amt).map fun tl' => { s with tl := tl' } else none

/-- **`settleS` — the deployed settle** (`post_trustline_settle`): march `settled` up by the
paid amount; `drawn` and the digest registry untouched. Fail-closed beyond the outstanding draw
(the executor refuses `settled > drawn` — program tooth 4). -/
def settleS (s : SLine) (paid : Nat) : Option SLine :=
  if paid ≤ s.outstanding then some { s with settled := s.settled + paid } else none

/-! ## §4 — the `@[export]` wire codec (Rust → Lean).

Single-line, space-separated token stream. The FULL channel state travels both directions, because
the anti-replay leg is the point: the `draws` registry must be DECIDED here, never summarised into
a Rust-computed "is it fresh" bit.

⚑ IT DISPATCHES THE §3b SETTLED VERBS, NOT §2. The deployed cell carries `settled` and gates
repay on `drawn − settled`; §2 has no such register, so a wire over §2 would ADMIT repays the
node refuses today. See §3b for the full statement. There is deliberately NO verb here for the
fullReserve close (escrow → holder): §3's `settlePay` moves the other way, and inventing a
mapping to make the arm look routed is exactly the drift this file exists to end.

**Request** — `op` then the five settled-line registers, then two op arguments, then the digest
registry as a length-prefixed run:

```
op  ceiling  drawn  settled  holderAcct  issuerWell  a1  a2  n  d1 … dn
```

| `op` | meaning | `a1` | `a2` |
|---|---|---|---|
| `0` | `drawS`   | digest | amount |
| `1` | `repayS`  | amount | (ignored) |
| `2` | `settleS` | paid   | (ignored) |

`ceiling`, `drawn`, `settled`, `a1`, `a2`, `n` and each `dᵢ` are unsigned decimals; `holderAcct`
and `issuerWell` are SIGNED decimals. A digest is an arbitrary-precision `Nat`, so a 32-byte hash
marshals as its full 78-digit decimal with **no truncation** — Rust must not fold it to 64 bits,
or two distinct debits could collide into one burned digest.

**Reply** — the five post-state registers followed by the post-state registry:

```
ceiling  drawn  settled  holderAcct  issuerWell  n  d1 … dn
```

Three outcomes, deliberately distinguishable (the `DelegAdmit` discipline):

  * a state line  — COMMITTED;
  * `"0"`          — REFUSED (the policy said no: replayed digest / over-line / over-repay);
  * `""`           — malformed wire, NO VERDICT (fail-closed; the Rust wrapper turns an empty
                     answer into an `Err`, and every caller REFUSES on `Err`).
-/

/-- Parse an unsigned decimal token. -/
def parseNat? (s : String) : Option Nat := s.toNat?

/-- Parse a signed decimal token (`-…` allowed). -/
def parseInt? (s : String) : Option Int :=
  if s.startsWith "-" then (s.drop 1).toNat?.map (fun n => -(Int.ofNat n))
  else s.toNat?.map Int.ofNat

/-- Split a wire into its non-empty whitespace-separated tokens. -/
def tokens (s : String) : List String :=
  (s.splitOn " ").filter (fun t => t != "")

/-- Parse exactly `n` unsigned decimals off the front, requiring the list to be EXACTLY that long
(a trailing token is a malformation, not slack). -/
def parseDigests (n : Nat) (ts : List String) : Option (List Nat) :=
  match n, ts with
  | 0, [] => some []
  | 0, _ :: _ => none
  | Nat.succ k, t :: rest => match parseNat? t, parseDigests k rest with
    | some d, some ds => some (d :: ds)
    | _, _ => none
  | Nat.succ _, [] => none

/-- Render the post-state: five registers then the length-prefixed digest registry. -/
def renderSLine (s : SLine) : String :=
  let regs :=
    toString s.tl.ceiling ++ " " ++ toString s.tl.drawn ++ " " ++ toString s.settled ++ " "
      ++ toString s.tl.holderAcct ++ " " ++ toString s.tl.issuerWell
  let ds := s.tl.draws.foldl (fun acc d => acc ++ " " ++ toString d) ""
  regs ++ " " ++ toString s.tl.draws.length ++ ds

/-- Parse the request wire into `(op, sline, a1, a2)`; `none` on any malformation. -/
def parseWire (t : String) : Option (Nat × SLine × Nat × Nat) :=
  match tokens t with
  | op :: ceiling :: drawn :: settled :: holderAcct :: issuerWell :: a1 :: a2 :: n :: rest =>
    match parseNat? op, parseNat? ceiling, parseNat? drawn, parseNat? settled,
          parseInt? holderAcct, parseInt? issuerWell,
          parseNat? a1, parseNat? a2, parseNat? n with
    | some op, some ceiling, some drawn, some settled,
      some holderAcct, some issuerWell,
      some a1, some a2, some n =>
        match parseDigests n rest with
        | some ds =>
            some (op,
              { tl := { ceiling := ceiling, drawn := drawn, draws := ds
                      , holderAcct := holderAcct, issuerWell := issuerWell }
              , settled := settled }, a1, a2)
        | none => none
    | _, _, _, _, _, _, _, _, _ => none
  | _ => none

/-- Apply `op` to the settled line. `none` is a REFUSAL (a verdict), distinct from a parse
failure. These are the DEPLOYED verbs — see §3b for why the export does not dispatch §2. -/
def applyOp (op : Nat) (s : SLine) (a1 a2 : Nat) : Option SLine :=
  match op with
  | 0 => drawS s a1 a2
  | 1 => repayS s a1
  | 2 => settleS s a1
  | _ => none

/-- The whole `String → String` decision. Malformed wire ⇒ `""`; refusal ⇒ `"0"`; commit ⇒ the
rendered post-state. An unknown `op` is a malformation, not a refusal — a caller that asks for a
verb we do not have has NOT been told "no", it has been told nothing. -/
def trustlineStepWire (t : String) : String :=
  match parseWire t with
  | none => ""
  | some (op, s, a1, a2) =>
      if op > 2 then ""
      else match applyOp op s a1 a2 with
        | none => "0"
        | some s' => renderSLine s'

/-- **`@[export dregg_trustline_step]`** — the C-ABI entry Rust calls. The trustline draw / repay /
settle verdict AND post-state are COMPUTED HERE; `coord`, `turn`, `node`, `narrator`, `cell` and
`dregg-agent` marshal to this boundary instead of re-deciding the spend authority in Rust. -/
@[export dregg_trustline_step]
def trustlineStepFFI (s : String) : String := trustlineStepWire s

/-! ## §5 — self-tests (`#guard` FAILS the build on regression — teeth, not comments). -/

/-- A demo line: ceiling 100, nothing drawn. -/
def demoLine : Line := Line.init 100

/-- The demo channel: the demo line plus level hard-asset balances. -/
def demoChannel : Channel := { tl := demoLine, issuerHard := 0, holderHard := 0 }

-- DRAW: within the line commits; the boundary is tight; over-line REFUSES.
#guard (draw demoLine 7 40).isSome                     -- 40 ≤ 100 — admitted
#guard (draw demoLine 7 100).isSome                    -- the BOUNDARY draw is admitted (tight)
#guard (draw demoLine 7 101).isNone                    -- 101 > 100 — REFUSED (over-line)
#guard ((draw demoLine 7 40).map (·.drawn)) == some 40 -- the counter moved by exactly the amount
#guard ((draw demoLine 7 40).map (·.holderAcct)) == some (40 : Int)
#guard ((draw demoLine 7 40).map (·.issuerWell)) == some (-40 : Int)

-- ANTI-REPLAY: the same digest twice is REFUSED even when the line has ample room.
#guard (((draw demoLine 7 10).bind (fun t => draw t 7 10))).isNone
#guard (((draw demoLine 7 10).bind (fun t => draw t 8 10))).isSome  -- a FRESH digest still draws

-- REPAY: within the drawn amount commits; over-repay REFUSES (it would MINT at the issuer's well).
#guard ((draw demoLine 7 40).bind (fun t => repay t 40)).isSome
#guard ((draw demoLine 7 40).bind (fun t => repay t 41)).isNone
-- A repay does NOT resurrect the burned digest: the line has room again, the digest still does not.
#guard ((draw demoLine 7 40).bind (fun t => repay t 40) |>.bind (fun t => draw t 7 10)).isNone

-- SETTLE (the §3 pureCredit axis point — NOT the deployed close; see §3b).
#guard (settleAll demoChannel).tl.drawn == 0
#guard ((draw demoLine 7 40).map (fun t => settleAll { tl := t, issuerHard := 0, holderHard := 0 })
          |>.map (·.issuerHard)) == some (40 : Int)

/-! ### §5b — THE SETTLED FLOOR, both polarities.

⚑ THIS IS THE TOOTH THE EXPORT EXISTS TO CARRY. `repayS` refuses inside `(drawn − settled, drawn]`
where §2's `repay` ADMITS. If this pair ever agrees, the export has silently become a weaker gate
than `node/src/trustline_service.rs:1155-1161` and every routed repay widens a money check. -/

/-- Drawn 30, of which 20 already settled — outstanding 10. -/
def demoSettled : SLine := { tl := (draw (Line.init 100) 7 30).getD (Line.init 100), settled := 20 }

#guard demoSettled.outstanding == 10
#guard decide demoSettled.WF
-- The boundary repay admits…
#guard (repayS demoSettled 10).isSome
-- …and ONE ABOVE IT REFUSES, while the §2 gate would have admitted it. Both halves asserted.
#guard (repayS demoSettled 11).isNone
#guard (repay demoSettled.tl 11).isSome
-- Settle is gated the same way, and leaves `drawn` and the registry alone.
#guard (settleS demoSettled 11).isNone
#guard ((settleS demoSettled 10).map (·.settled)) == some 30
#guard ((settleS demoSettled 10).map (·.tl.drawn)) == some 30
-- A burned digest stays burned across a settle epoch.
#guard ((settleS demoSettled 10).bind (fun s => drawS s 7 1)).isNone

-- THE WIRE, all three outcome shapes.
--                       op ceil drawn settled hAcct iWell  a1  a2  n
#guard trustlineStepWire "0  100     0       0     0     0   7  40  0"
         == "100 40 0 40 -40 1 7"                    -- draw 40 on digest 7 — COMMITTED
#guard trustlineStepWire "0  100     0       0     0     0   7 101  0" == "0"   -- over-line
#guard trustlineStepWire "0  100    40       0    40   -40   7  10  1 7" == "0" -- replay REFUSED
#guard trustlineStepWire "1  100    40       0    40   -40  41   0  1 7" == "0" -- over-repay
#guard trustlineStepWire "1  100    40       0    40   -40  40   0  1 7"
         == "100 0 0 0 0 1 7"                        -- repay 40 — digest STAYS burned
-- THE SETTLED FLOOR ON THE WIRE: outstanding is 10, so 11 REFUSES even though drawn is 30.
#guard trustlineStepWire "1  100    30      20    30   -30  11   0  1 7" == "0"
#guard trustlineStepWire "1  100    30      20    30   -30  10   0  1 7"
         == "100 20 20 20 -20 1 7"
-- settleS marches the redemption register and leaves `drawn` in place (the DEPLOYED shape).
#guard trustlineStepWire "2  100    30      20    30   -30  10   0  1 7"
         == "100 30 30 30 -30 1 7"
#guard trustlineStepWire "2  100    30      20    30   -30  11   0  1 7" == "0"

-- FAIL-CLOSED on every malformation: short, long, non-numeric, bad registry length, unknown op.
#guard trustlineStepWire "0 100 0 0 0 0 7 40" == ""            -- short (no registry length)
#guard trustlineStepWire "0 100 0 0 0 0 7 40 0 9" == ""        -- registry longer than declared
#guard trustlineStepWire "0 100 0 0 0 0 7 40 1" == ""          -- registry shorter than declared
#guard trustlineStepWire "0 100 0 0 0 0 seven 40 0" == ""      -- non-numeric
#guard trustlineStepWire "0 -100 0 0 0 0 7 40 0" == ""         -- a NEGATIVE ceiling is not a Nat
#guard trustlineStepWire "0 100 0 -1 0 0 7 40 0" == ""         -- a NEGATIVE settled is not a Nat
#guard trustlineStepWire "3 100 0 0 0 0 7 40 0" == ""          -- unknown op ⇒ NO VERDICT
#guard trustlineStepWire "" == ""                              -- empty ⇒ NO VERDICT

-- Signed registers round-trip through the wire (the wells carry negatives).
#guard trustlineStepWire "1 100 40 0 40 -40 40 0 1 7" == "100 0 0 0 0 1 7"

end Dregg2.Apps.TrustlineCore
