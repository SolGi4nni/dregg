/-
# AutomataflRevealEmit — Lean-authored Leg S (sealed-move reveal), 11×11.

This is the missing commit→reveal leg in the Lean Automatafl braid.  Rust's old
`build_sealed` is behavioral archaeology only: the descriptor below is authored in
Lean and Rust may only consume its emitted value.

The two revealed openings are public.  For each seat the circuit:

* range-constrains `(fx,fy,tx,ty)` to `[0,11)` with 4-bit decompositions of both
  `coord` and `10-coord` (degree two, never the forbidden degree-11 membership gate),
* fixes the seat to A=0 / B=1,
* recomposes flattened `frm = 11*fy+fx` and `to = 11*ty+tx`, and
* serves a Poseidon2 chip row for
  `commit = hash_4_to_1([frm,to,seat,nonce])`.

PI `[0,16)` is the opaque door prefix.  PI `[16,25)` carries the nine-felt packed
commitment of the old 11×11 board (the same injective base-4 commitment used by Legs
R/A).  PI `[25,32)` and `[32,39)` expose the two openings as
`fx,fy,tx,ty,seat,nonce,commit`. PI `[39,41)` is a contiguous, constrained copy
of the two commitment felts. That last slice is shaped for the deployed recursive
app-root weld, whose binding carrier accepts a contiguous application-PI segment.

**Intentional integration seam.** This leaf proves that each commitment PI opens to
the published reveal and constrains the contiguous join copies. The existing app-root
weld has the shape to bind those copies to the cell's two commitment fields. The live
fields, however, hold truncated ~63-bit BLAKE3 seals, not these one-felt Poseidon2 values,
and the weld exposes only their low-32-bit field lane. It also cannot bind the nine-felt
old-board pack: that state lives in the heap, while the current carrier exposes only the
eight flat field lanes. The live playable game is still 5×5, whereas this descriptor is
11×11. For these reasons this standalone descriptor remains unregistered;
`AutomataflRevealJoin` states the exact join theorem and the remaining deployment
blockers rather than pretending they are closed.

The semantic SAT⇒reveal theorem lives in `AutomataflRevealRefine`.  This file keeps
only the IR-v2 value and structural/mutation teeth.  No on-disk artifact is installed
yet: registration is a coupled Rust-caller action, and silently placing an unused
golden would create another dark descriptor.
-/
import Dregg2.Circuit.DescriptorIR2
import Dregg2.Circuit.GateExpr

namespace Dregg2.Circuit.Emit.AutomataflRevealEmit

open Dregg2.Exec.CircuitEmit (EmittedExpr)
open Dregg2.Circuit.Emit.EffectVmEmit (VmConstraint VmRow)
open Dregg2.Circuit.DescriptorIR2
  (EffectVmDescriptor2 VmConstraint2 Lookup TableId chipLookupTuple CHIP_RATE CHIP_OUT_LANES
   emitVmJson2)

set_option autoImplicit false

/-! ## Layout. -/

def N : Nat := 11
def PACK_FELTS : Nat := 9
def DOOR_PI_COUNT : Nat := 16
def PACK_PI_BASE : Nat := 16
def OPEN_PI_BASE (seat : Nat) : Nat := 25 + 7 * seat
def JOIN_COMMIT_PI_BASE : Nat := 39
def REVEAL_PI_COUNT : Nat := 41

/-- Carried old-board packed-felt columns. -/
def boardPack (j : Nat) : Nat := j

/-- One opening uses 48 columns: 4 coordinates, 32 range bits, seat/nonce/flat
indices/commitment, and seven Poseidon output lanes. -/
def SEAT_WIDTH : Nat := 48
def seatBase (s : Nat) : Nat := PACK_FELTS + SEAT_WIDTH * s
def FX (s : Nat) : Nat := seatBase s
def FY (s : Nat) : Nat := seatBase s + 1
def TX (s : Nat) : Nat := seatBase s + 2
def TY (s : Nat) : Nat := seatBase s + 3

/-- Each coordinate owns eight bits: four for `coord`, four for `10-coord`. -/
def coordLo (s q : Nat) : Nat := seatBase s + 4 + 8 * q
def coordHi (s q : Nat) : Nat := seatBase s + 8 + 8 * q
def coordCol (s q : Nat) : Nat := [FX s, FY s, TX s, TY s].getD q (FX s)

def SEAT (s : Nat) : Nat := seatBase s + 36
def NONCE (s : Nat) : Nat := seatBase s + 37
def FRM (s : Nat) : Nat := seatBase s + 38
def TO (s : Nat) : Nat := seatBase s + 39
def COMMIT (s : Nat) : Nat := seatBase s + 40
def LANES (s : Nat) : List Nat := (List.range 7).map (fun i => seatBase s + 41 + i)
def REVEAL_WIDTH : Nat := PACK_FELTS + 2 * SEAT_WIDTH

/-! ## Constraint constructors. -/

def binExpr (c : Nat) : EmittedExpr :=
  Dregg2.Circuit.GateExpr.render Dregg2.Circuit.GateExpr.toEmitted
    (Dregg2.Circuit.GateExpr.gBool (.leaf c))

theorem binExpr_eq (c : Nat) :
    binExpr c = .mul (.var c) (.add (.var c) (.const (-1))) := rfl

def gate (e : EmittedExpr) : VmConstraint2 := .base (.gate e)

def bitsExpr (b : Nat) : EmittedExpr :=
  .add (.var b)
    (.add (.mul (.const 2) (.var (b + 1)))
      (.add (.mul (.const 4) (.var (b + 2)))
        (.mul (.const 8) (.var (b + 3)))))

def sub (a b : EmittedExpr) : EmittedExpr := .add a (.mul (.const (-1)) b)

/-- `0 ≤ c ≤ 10`, with both inequalities made explicit as four-bit values. -/
def coordRangeConstraints (c lo hi : Nat) : List VmConstraint2 :=
  [ gate (binExpr lo), gate (binExpr (lo + 1)), gate (binExpr (lo + 2)), gate (binExpr (lo + 3))
  , gate (binExpr hi), gate (binExpr (hi + 1)), gate (binExpr (hi + 2)), gate (binExpr (hi + 3))
  , gate (sub (.var c) (bitsExpr lo))
  , gate (sub (sub (.const 10) (.var c)) (bitsExpr hi)) ]

def coordConstraints (s : Nat) : List VmConstraint2 :=
  (List.range 4).flatMap (fun q =>
    coordRangeConstraints (coordCol s q) (coordLo s q) (coordHi s q))

def flatConstraints (s : Nat) : List VmConstraint2 :=
  [ gate (sub (.var (FRM s))
      (.add (.mul (.const 11) (.var (FY s))) (.var (FX s))))
  , gate (sub (.var (TO s))
      (.add (.mul (.const 11) (.var (TY s))) (.var (TX s)))) ]

def seatConstraints (s : Nat) : List VmConstraint2 :=
  [ gate (binExpr (SEAT s)), gate (sub (.var (SEAT s)) (.const (s : ℤ))) ]

def revealLookup (s : Nat) : VmConstraint2 :=
  .lookup ⟨TableId.poseidon2,
    chipLookupTuple [.var (FRM s), .var (TO s), .var (SEAT s), .var (NONCE s)]
      (COMMIT s) (LANES s)⟩

def openPins (s : Nat) : List VmConstraint2 :=
  [ .base (.piBinding VmRow.first (FX s) (OPEN_PI_BASE s))
  , .base (.piBinding VmRow.first (FY s) (OPEN_PI_BASE s + 1))
  , .base (.piBinding VmRow.first (TX s) (OPEN_PI_BASE s + 2))
  , .base (.piBinding VmRow.first (TY s) (OPEN_PI_BASE s + 3))
  , .base (.piBinding VmRow.first (SEAT s) (OPEN_PI_BASE s + 4))
  , .base (.piBinding VmRow.first (NONCE s) (OPEN_PI_BASE s + 5))
  , .base (.piBinding VmRow.first (COMMIT s) (OPEN_PI_BASE s + 6)) ]

def oneSeatConstraints (s : Nat) : List VmConstraint2 :=
  coordConstraints s ++ flatConstraints s ++ seatConstraints s ++ [revealLookup s] ++ openPins s

def boardCarryConstraints : List VmConstraint2 :=
  (List.range PACK_FELTS).map (fun j =>
    .base (.piBinding VmRow.first (boardPack j) (PACK_PI_BASE + j)))

/-- A contiguous duplicate of `(commitA, commitB)`. These are constraints, not ABI
decoration: the recursive app-root carrier consumes a contiguous application-PI slice,
while the full public openings place the commits seven felts apart. -/
def commitJoinPins : List VmConstraint2 :=
  (List.range 2).map (fun s =>
    .base (.piBinding VmRow.first (COMMIT s) (JOIN_COMMIT_PI_BASE + s)))

def revealConstraints : List VmConstraint2 :=
  boardCarryConstraints ++ oneSeatConstraints 0 ++ oneSeatConstraints 1 ++ commitJoinPins

/-- **Leg S, n=11** — two public openings, two published move commitments, and the
old-board packed commitment transported in the same statement. -/
def automataflRevealDesc11 : EffectVmDescriptor2 :=
  { name        := "dregg-automatafl-reveal-s-n11::poseidon2-v1"
  , traceWidth  := REVEAL_WIDTH
  , piCount     := REVEAL_PI_COUNT
  , tables      := []
  , constraints := revealConstraints
  , hashSites   := []
  , ranges      := [] }

/-! ## Structural and RED teeth. -/

#guard PACK_FELTS == 9
#guard REVEAL_WIDTH == 105
#guard REVEAL_PI_COUNT == 41
#guard (coordConstraints 0).length == 40
#guard (oneSeatConstraints 0).length == 52
#guard commitJoinPins.length == 2
#guard revealConstraints.length == 115
#guard (LANES 0).length == 7
#guard (chipLookupTuple [.var (FRM 0), .var (TO 0), .var (SEAT 0), .var (NONCE 0)]
  (COMMIT 0) (LANES 0)).length == CHIP_RATE + 1 + CHIP_OUT_LANES

-- A commitment mutation changes the served chip tuple.
#guard decide
  ((chipLookupTuple [.var (FRM 0), .var (TO 0), .var (SEAT 0), .var (NONCE 0)]
      (COMMIT 0) (LANES 0)).map (fun e => e.eval (fun i => if i = COMMIT 0 then 7 else 0))
   ≠
   (chipLookupTuple [.var (FRM 0), .var (TO 0), .var (SEAT 0), .var (NONCE 0)]
      (COMMIT 0) (LANES 0)).map (fun e => e.eval (fun i => if i = COMMIT 0 then 8 else 0)))

-- A flattened-move mutation also changes the served tuple.
#guard decide
  ((chipLookupTuple [.var (FRM 0), .var (TO 0), .var (SEAT 0), .var (NONCE 0)]
      (COMMIT 0) (LANES 0)).map (fun e => e.eval (fun i => if i = FRM 0 then 7 else 0))
   ≠
   (chipLookupTuple [.var (FRM 0), .var (TO 0), .var (SEAT 0), .var (NONCE 0)]
      (COMMIT 0) (LANES 0)).map (fun e => e.eval (fun i => if i = FRM 0 then 8 else 0)))

-- A column outside the opening tuple cannot fake a tuple mutation.
#guard decide
  ((chipLookupTuple [.var (FRM 0), .var (TO 0), .var (SEAT 0), .var (NONCE 0)]
      (COMMIT 0) (LANES 0)).map (fun e => e.eval (fun i => if i = 1000 then 7 else 0))
   =
   (chipLookupTuple [.var (FRM 0), .var (TO 0), .var (SEAT 0), .var (NONCE 0)]
      (COMMIT 0) (LANES 0)).map (fun e => e.eval (fun i => if i = 1000 then 8 else 0)))

-- The emitted value is nontrivial and names the intended descriptor.  The full byte
-- artifact is deliberately deferred until the Rust caller is installed.
#guard (emitVmJson2 automataflRevealDesc11).startsWith
  "{\"name\":\"dregg-automatafl-reveal-s-n11::poseidon2-v1\",\"ir\":2,\"trace_width\":105,\"public_input_count\":41"

end Dregg2.Circuit.Emit.AutomataflRevealEmit
