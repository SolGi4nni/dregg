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

/-! ## §4 — the `@[export]` wire codec (Rust → Lean).

Single-line, space-separated token stream. The FULL channel state travels both directions, because
the anti-replay leg is the point: the `draws` registry must be DECIDED here, never summarised into
a Rust-computed "is it fresh" bit.

**Request** — `op` then the six channel registers, then two op arguments, then the digest registry
as a length-prefixed run:

```
op  ceiling  drawn  holderAcct  issuerWell  issuerHard  holderHard  a1  a2  n  d1 … dn
```

| `op` | meaning | `a1` | `a2` |
|---|---|---|---|
| `0` | `draw`      | digest | amount |
| `1` | `repay`     | amount | (ignored) |
| `2` | `settlePay` | amount | (ignored) |
| `3` | `settleAll` | (ignored) | (ignored) |

`ceiling`, `drawn`, `a1`, `a2`, `n` and each `dᵢ` are unsigned decimals; `holderAcct`, `issuerWell`,
`issuerHard`, `holderHard` are SIGNED decimals. A digest is an arbitrary-precision `Nat`, so a
32-byte hash marshals as its full 78-digit decimal with **no truncation** — Rust must not fold it to
64 bits, or two distinct debits could collide into one burned digest.

**Reply** — the six post-state registers followed by the post-state registry:

```
ceiling  drawn  holderAcct  issuerWell  issuerHard  holderHard  n  d1 … dn
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

/-- Render the post-state: six registers then the length-prefixed digest registry. -/
def renderChannel (c : Channel) : String :=
  let regs :=
    toString c.tl.ceiling ++ " " ++ toString c.tl.drawn ++ " "
      ++ toString c.tl.holderAcct ++ " " ++ toString c.tl.issuerWell ++ " "
      ++ toString c.issuerHard ++ " " ++ toString c.holderHard
  let ds := c.tl.draws.foldl (fun acc d => acc ++ " " ++ toString d) ""
  regs ++ " " ++ toString c.tl.draws.length ++ ds

/-- Parse the request wire into `(op, channel, a1, a2)`; `none` on any malformation. -/
def parseWire (s : String) : Option (Nat × Channel × Nat × Nat) :=
  match tokens s with
  | op :: ceiling :: drawn :: holderAcct :: issuerWell :: issuerHard :: holderHard
      :: a1 :: a2 :: n :: rest =>
    match parseNat? op, parseNat? ceiling, parseNat? drawn, parseInt? holderAcct,
          parseInt? issuerWell, parseInt? issuerHard, parseInt? holderHard,
          parseNat? a1, parseNat? a2, parseNat? n with
    | some op, some ceiling, some drawn, some holderAcct,
      some issuerWell, some issuerHard, some holderHard,
      some a1, some a2, some n =>
        match parseDigests n rest with
        | some ds =>
            some (op,
              { tl := { ceiling := ceiling, drawn := drawn, draws := ds
                      , holderAcct := holderAcct, issuerWell := issuerWell }
              , issuerHard := issuerHard, holderHard := holderHard }, a1, a2)
        | none => none
    | _, _, _, _, _, _, _, _, _, _ => none
  | _ => none

/-- Apply `op` to the channel. `none` is a REFUSAL (a verdict), distinct from a parse failure. -/
def applyOp (op : Nat) (c : Channel) (a1 a2 : Nat) : Option Channel :=
  match op with
  | 0 => (draw c.tl a1 a2).map fun tl' => { c with tl := tl' }
  | 1 => (repay c.tl a1).map fun tl' => { c with tl := tl' }
  | 2 => settlePay c a1
  | 3 => some (settleAll c)
  | _ => none

/-- The whole `String → String` decision. Malformed wire ⇒ `""`; refusal ⇒ `"0"`; commit ⇒ the
rendered post-state. An unknown `op` is a malformation, not a refusal — a caller that asks for a
verb we do not have has NOT been told "no", it has been told nothing. -/
def trustlineStepWire (s : String) : String :=
  match parseWire s with
  | none => ""
  | some (op, c, a1, a2) =>
      if op > 3 then ""
      else match applyOp op c a1 a2 with
        | none => "0"
        | some c' => renderChannel c'

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

-- SETTLE: the hard-asset pair is conserved and the counter clears.
#guard (settleAll demoChannel).tl.drawn == 0
#guard ((draw demoLine 7 40).map (fun t => settleAll { tl := t, issuerHard := 0, holderHard := 0 })
          |>.map (·.issuerHard)) == some (40 : Int)

-- THE WIRE, all three outcome shapes.
--                            op ceil drawn hAcct iWell iHard hHard  a1  a2  n
#guard trustlineStepWire      "0  100    0     0     0     0     0    7  40  0"
         == "100 40 40 -40 0 0 1 7"                       -- draw 40 on digest 7 — COMMITTED
#guard trustlineStepWire      "0  100    0     0     0     0     0    7 101  0" == "0"
                                                          -- over-line — REFUSED
#guard trustlineStepWire      "0  100   40    40   -40     0     0    7  10  1 7" == "0"
                                                          -- digest 7 replayed — REFUSED
#guard trustlineStepWire      "1  100   40    40   -40     0     0   41   0  1 7" == "0"
                                                          -- over-repay — REFUSED
#guard trustlineStepWire      "1  100   40    40   -40     0     0   40   0  1 7"
         == "100 0 0 0 0 0 1 7"                           -- repay 40 — digest STAYS burned
#guard trustlineStepWire      "2  100   40    40   -40     0     0   40   0  1 7"
         == "100 0 0 0 40 -40 1 7"                        -- settlePay 40 — hard asset MOVED
#guard trustlineStepWire      "3  100   40    40   -40     0     0    0   0  1 7"
         == "100 0 0 0 40 -40 1 7"                        -- settleAll — same, drawn cleared

-- FAIL-CLOSED on every malformation: short, long, non-numeric, bad registry length, unknown op.
#guard trustlineStepWire "0 100 0 0 0 0 0 7 40" == ""          -- short (no registry length)
#guard trustlineStepWire "0 100 0 0 0 0 0 7 40 0 9" == ""      -- registry longer than declared
#guard trustlineStepWire "0 100 0 0 0 0 0 7 40 1" == ""        -- registry shorter than declared
#guard trustlineStepWire "0 100 0 0 0 0 0 seven 40 0" == ""    -- non-numeric
#guard trustlineStepWire "0 -100 0 0 0 0 0 7 40 0" == ""       -- a NEGATIVE ceiling is not a Nat
#guard trustlineStepWire "4 100 0 0 0 0 0 7 40 0" == ""        -- unknown op ⇒ NO VERDICT
#guard trustlineStepWire "" == ""                              -- empty ⇒ NO VERDICT

-- Signed registers round-trip through the wire (the wells carry negatives).
#guard trustlineStepWire "1 100 40 40 -40 -5 5 40 0 1 7" == "100 0 0 0 -5 5 1 7"

end Dregg2.Apps.TrustlineCore
