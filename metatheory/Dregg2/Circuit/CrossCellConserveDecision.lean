/-
# `Dregg2.Circuit.CrossCellConserveDecision` — the RUNTIME-CALLABLE cross-cell value-conservation
DECISION PROCEDURE (`Σδ = 0` per asset), `@[export]`-ed for the deployed executor (House Law #1).

## What this is (and what the committed AIR was NOT)

`Dregg2/Circuit/CrossCellConservation.lean` authors the turn-wide `Σδ = 0` AIR + proves its soundness
(`ccc_conserves`: a satisfying trace has `Σ credits = Σ debits` over ℤ). But that object exists ONLY as
an emitted JSON *descriptor* — it is NOT runtime-callable, so the deployed executor
(`turn/src/executor/atomic.rs`) decided conservation in a HAND-WRITTEN Rust twin
(`dregg_circuit::block_conservation::BlockConservation`) with ZERO runtime link to the proof. That twin
already drifted once into the asset-blind inflation bug.

This module closes that: an EXECUTABLE per-asset conservation decision over the `(asset, δ)` rows the
executor already holds (each `δ` is a verified per-cell proof's published signed `NET_DELTA`), plus any
DECLARED mint/burn supply rows. It is `@[export dregg_cross_cell_conserves]`-ed so Rust CALLS it — the
deployed conservation decision is COMPUTED BY THIS FUNCTION, not a Rust re-implementation.

`Dregg2/Circuit/CrossCellConserveRefine.lean` proves the REFINEMENT: this decision's per-asset boundary
`Σδ = 0` is EXACTLY the committed AIR's `creditSum = debitSum` boundary (`ccc_conserves`), so the
runtime route-through and the proven AIR cannot drift.

## Import discipline

Imports NOTHING beyond core `Init` — no Mathlib. The `@[export]`ed object must be self-contained so its
leanc-emitted `.c` splices into `libdregg_lean.a` without dragging a Mathlib-tactic initializer closure
into the FFI link (same discipline as `Dregg2.Exec.DeployedConstraint` / `Dregg2.Grain.R3Verify`; see
`dregg-lean-ffi/src/lean_init.c`). The refinement proof (which DOES import the committed AIR + Mathlib)
lives in the separate `CrossCellConserveRefine` module.

## The decision (mirrors `BlockConservation::check`, per-asset, ascending-asset-first-imbalanced)

Group the rows by asset key, sum each asset's signed deltas over ℤ, and ADMIT iff EVERY asset's sum is
`0`. On a violation report the FIRST imbalanced asset in ASCENDING key order — matching the Rust twin's
`BTreeMap` iteration so the routed executor's `PerAssetConservationViolation { asset, imbalance }` is
byte-identical to the pre-route path. A malformed wire fails CLOSED (refuse).
-/

namespace Dregg2.Circuit.CrossCellConserveDecision

set_option autoImplicit false

/-! ## §1 — the pure per-asset conservation decision (over ℤ). -/

/-- Signed sum of a list of integer deltas (the single-asset balance). Elementary recursion so the
refinement (`CrossCellConserveRefine`) can reason about it directly. -/
def sumInts : List Int → Int
  | [] => 0
  | x :: xs => x + sumInts xs

/-- The SINGLE-ASSET boundary decision: this asset's signed deltas conserve iff their sum is `0` — the
committed AIR's `creditSum = debitSum` (`balance[last] == 0`) boundary. -/
def conservesSingle (ds : List Int) : Bool := sumInts ds == 0

/-- Sum the signed deltas belonging to asset `a` across the mixed-asset row list. -/
def sumForAsset : List (Nat × Int) → Nat → Int
  | [], _ => 0
  | (k, d) :: rest, a => (if k == a then d else 0) + sumForAsset rest a

/-- Only asset `a`'s deltas, in row order (the single-asset projection the AIR certifies per asset). -/
def deltasForAsset : List (Nat × Int) → Nat → List Int
  | [], _ => []
  | (k, d) :: rest, a => (if k == a then [d] else []) ++ deltasForAsset rest a

/-- Insert `x` into a strictly-ascending, duplicate-free `Nat` list, keeping it so. -/
def insertSorted (x : Nat) : List Nat → List Nat
  | [] => [x]
  | y :: ys =>
    if x == y then y :: ys
    else if x < y then x :: y :: ys
    else y :: insertSorted x ys

/-- The DISTINCT asset keys of a row list, in ASCENDING order (mirrors the Rust twin's `BTreeMap<u32,_>`
key order, so the first-imbalanced asset reported on a violation is identical). -/
def keysAsc : List (Nat × Int) → List Nat
  | [] => []
  | (k, _) :: rest => insertSorted k (keysAsc rest)

/-- The FIRST imbalanced asset (ascending key order) and its signed imbalance, if any. -/
def firstImbalanced (rows : List (Nat × Int)) : Option (Nat × Int) :=
  (keysAsc rows).findSome? (fun a =>
    let b := sumForAsset rows a
    if b == 0 then none else some (a, b))

/-- **THE DECISION.** The block of `(asset, δ)` rows conserves iff EVERY asset's signed delta sum is `0`
(no asset imbalanced). -/
def conservesRows (rows : List (Nat × Int)) : Bool := (firstImbalanced rows).isNone

/-! ## §2 — declared mint/burn supply rows enter as explicit signed deltas.

A declared mint of magnitude `m` is a `+m` credit row; a declared burn is `-m`. A DISCLOSED supply
change balances; an UNdisclosed one (no matching row) is exactly what the boundary catches.

⚠ THE DEPLOYED EXECUTOR SENDS NO SUPPLY ROWS, AND THIS IS THE RULE BEING MORE GENERAL THAN THE
DEPLOYMENT — not a gap. This section used to name a Rust mirror
(`dregg_circuit::block_conservation::DeclaredSupplyChange::as_delta`, `credit := mint`); that type
and the `declared_supply` parameter threaded through
`turn/src/executor/atomic.rs::check_per_asset_conservation*` were DELETED on 2026-07-28, because no
producer for them existed anywhere in the tree — every call site, production and test, passed an
empty slice. The ratified dregg supply model
(`.docs-history-noclaude/SUPPLY-MODEL.md`) discloses a supply change as the issuer WELL's own PAIRED
ledger delta instead: `apply_mint` debits the asset's well (carrying `-supply`) and credits the
holder, so a mint reaches `conservesRows` as TWO rows of the same asset that cancel — auditable
state, and gated by the Rust image of `mintAuthorizedB`, which an asserted row was not.

So the wire's supply section (§3) is what the Rust bridge now always sends as `nSupply = 0`, and the
`#guard` below for it is a true theorem about THIS RULE that no deployed caller exercises. Keeping it
costs nothing and is what a future, properly-gated ex-nihilo supply design would route through. -/

/-- Fold one declared supply row `(asset, magnitude, mint?)` into a signed `(asset, δ)` delta. -/
def supplyRowDelta (asset mag : Nat) (mint : Bool) : Nat × Int :=
  (asset, if mint then (mag : Int) else -(mag : Int))

/-! ## §3 — the `@[export]` wire codec (Rust → Lean).

Single-line, space-separated token stream; a malformed wire fails CLOSED (refuse). Token order:

```
nRows(dec)  then nRows × [ asset(dec) delta(signed dec) ]
nSupply(dec) then nSupply × [ asset(dec) magnitude(dec) mint(0|1) ]
```

Output: `"1"` conserves (ADMIT) · `"0 <asset> <imbalance>"` the first imbalanced asset (REFUSE) ·
`"0"` malformed wire (fail-closed REFUSE). -/

/-- Parse an unsigned decimal token. -/
@[inline] def parseNat? (s : String) : Option Nat := s.toNat?

/-- Parse a signed decimal token (`-…` allowed). -/
def parseInt? (s : String) : Option Int :=
  if s.startsWith "-" then (s.drop 1).toNat?.map (fun n => -(Int.ofNat n))
  else s.toNat?.map Int.ofNat

/-- Pop `n` tokens, failing closed on underflow. -/
def popN : Nat → List String → Option (List String × List String)
  | 0, rest => some ([], rest)
  | _ + 1, [] => none
  | k + 1, t :: rest =>
    match popN k rest with
    | some (hd, tl) => some (t :: hd, tl)
    | none => none

/-- Parse `n` `(asset delta)` pairs from the token stream. -/
def parseRows : Nat → List String → Option (List (Nat × Int) × List String)
  | 0, rest => some ([], rest)
  | n + 1, a :: d :: rest =>
    match parseNat? a, parseInt? d with
    | some asset, some delta =>
      match parseRows n rest with
      | some (rows, tl) => some ((asset, delta) :: rows, tl)
      | none => none
    | _, _ => none
  | _ + 1, _ => none

/-- Parse `n` `(asset magnitude mint)` supply triples, folding each into a signed delta row. -/
def parseSupply : Nat → List String → Option (List (Nat × Int) × List String)
  | 0, rest => some ([], rest)
  | n + 1, a :: m :: mint :: rest =>
    match parseNat? a, parseNat? m, parseNat? mint with
    | some asset, some mag, some mintFlag =>
      match parseSupply n rest with
      | some (rows, tl) => some (supplyRowDelta asset mag (mintFlag != 0) :: rows, tl)
      | none => none
    | _, _, _ => none
  | _ + 1, _ => none

/-- Parse the full wire into the combined `(asset, δ)` row list (per-cell rows ++ supply rows). -/
def parseWire (s : String) : Option (List (Nat × Int)) :=
  let toks := (s.splitOn " ").filter (fun t => t != "")
  match toks with
  | nRowsTok :: rest =>
    match parseNat? nRowsTok with
    | some nRows =>
      match parseRows nRows rest with
      | some (rows, afterRows) =>
        match afterRows with
        | nSupTok :: rest2 =>
          match parseNat? nSupTok with
          | some nSup =>
            match parseSupply nSup rest2 with
            | some (supply, _) => some (rows ++ supply)
            | none => none
          | none => none
        | [] => some rows  -- supply section omitted ⇒ no declared supply
      | none => none
    | none => none
  | [] => none

/-- Render the decision as the output wire. -/
def render (rows : List (Nat × Int)) : String :=
  match firstImbalanced rows with
  | none => "1"
  | some (asset, imbalance) => "0 " ++ toString asset ++ " " ++ toString imbalance

/-- The whole `String → String` decision. A malformed wire refuses (`"0"`). -/
def conservesWire (s : String) : String :=
  match parseWire s with
  | none => "0"
  | some rows => render rows

/-- **`@[export dregg_cross_cell_conserves]`** — the FFI entry Rust calls. Runs the per-asset
conservation decision over the wire slice; the deployed executor's conservation verdict is COMPUTED
HERE. -/
@[export dregg_cross_cell_conserves]
def conservesFFI (s : String) : String := conservesWire s

/-! ## §4 — self-tests (`#guard` FAILS the build on regression — teeth, not comments). -/

-- HONEST: a matched transfer (asset 7: −10, +10) conserves.
#guard conservesRows [(7, -10), (7, 10)] == true
-- FORGED MINT: A −10, B +999 of the same asset (no declared mint) nets +989 ⇒ REFUSE, first
-- imbalanced asset reported.
#guard conservesRows [(7, -10), (7, 999)] == false
#guard firstImbalanced [(7, -10), (7, 999)] == some (7, 989)
-- CROSS-ASSET BORROWING: asset 7 short −10, asset 8 long +10 nets to zero ACROSS assets but each is
-- imbalanced ⇒ REFUSE; the LOWER asset key (7) is reported first (ascending order, = the Rust
-- `BTreeMap` first key).
#guard conservesRows [(7, -10), (8, 10)] == false
#guard firstImbalanced [(7, -10), (8, 10)] == some (7, -10)
-- DECLARED supply restores conservation: A −10, B +999 WITH a declared −989 burn row balances.
#guard conservesRows ([(7, -10), (7, 999)] ++ [supplyRowDelta 7 989 false]) == true
-- THE p-SUM FORGERY (matches `CrossCellConservation.ccc_psum_forgery_unsat`): two credit rows whose
-- true integer sum is EXACTLY p = 2013265921 (no debit) does NOT conserve — the single-felt design
-- accepted this (p ≡ 0); the ℤ decision REFUSES.
#guard conservesSingle [1006632961, 1006632960] == false
#guard sumInts [1006632961, 1006632960] == 2013265921
-- An empty block trivially conserves.
#guard conservesRows [] == true
-- Wire round-trip: honest admits, forged refuses with the asset+imbalance, malformed fails closed.
#guard conservesWire "2 7 -10 7 10 0" == "1"
#guard conservesWire "2 7 -10 7 999 0" == "0 7 989"
#guard conservesWire "garbage" == "0"

end Dregg2.Circuit.CrossCellConserveDecision
