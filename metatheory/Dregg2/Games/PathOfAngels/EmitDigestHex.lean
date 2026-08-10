/-
# The POAG1 `Digest32` hex codec — factored out from under the aggregate emitter

⚑ **Why this module exists: an aggregator was sitting in a RUNTIME import path.**

`Emit.lean` is the PoA *aggregate* emitter: it imports every game's emit driver
(`VentCrawlEmit`, `DeckDescentEmit`, `ArtificerLogicEmit`, …) because its job is
to render one bundle containing all of them.  That is the right shape for a
module consumed by the emitter binary (`EmitMain`) and by its pins
(`EmitFixtures`), and by NOTHING ELSE.

It was not the shape in use.  Seven runtime/wire modules imported `Emit` —
`GalleyMaintenanceDailyRuntime`, `ActivatedContent`, `CrewFieldMissionRuntime`,
`BazaarGameRuntime`, `EventBatchRuntime`, `DarkBazaarJudgeWire`,
`WorldActivation` — and every one of them wanted the same three things:

    bytes32Hex · parseBytes32Hex? · isLowerHexOfLength

a byte-for-hex codec over `Core.Digest32` that decides nothing about any game.
Reaching those three through the aggregator dragged EVERY game in the rack into
the closure of every guard module downstream.  Measured 2026-08-09:
`CrewFieldMissionAdmissionFixtures` — a *crew* guard module — carried **177**
local modules, could not elaborate unless Vent Crawl elaborated, and lost a full
fixtures build to a Vent edit it has no relationship with.

So the codec moves DOWN, to the one place that has no game in it.  It is not
copied sideways: two spellings of a wire codec that agree today are two that
disagree later, and the wire is the last place to discover it.

⚑ **The namespace is deliberately `…PathOfAngels.Emit`, not `…EmitDigestHex`.**
These definitions did not change their identity, only their home, so
`Emit.bytes32Hex` still names exactly what it named before and not one call site
moved.  `Emit.lean` imports this module and re-exports it by namespace; a module
that wants only the codec imports THIS and pays for `Core` alone.

Depends on `Core` (for `Digest32`) and nothing else — closure of two.
-/
import Dregg2.Games.PathOfAngels.Core

namespace Dregg2.Games.PathOfAngels.Emit

open Dregg2.Games.PathOfAngels

/-! ## Lowercase hexadecimal digits -/

/-- ⚠ Not `private`, unlike the other helpers here: `Emit.uint64HexAux` (the FNV-1a byte
pin, which stays with the bundle it pins) renders its nibbles with this, and a `private`
def does not cross a module boundary.  The alternative was a second spelling of "render one
hex digit" in `Emit.lean`, which is the twin this move exists to avoid. -/
def lowerHexDigit (n : Nat) : Char :=
  if n < 10 then Char.ofNat ('0'.toNat + n)
  else Char.ofNat ('a'.toNat + (n - 10))

private def hexNibble? (c : Char) : Option Nat :=
  if '0' ≤ c ∧ c ≤ '9' then some (c.toNat - '0'.toNat)
  else if 'a' ≤ c ∧ c ≤ 'f' then some (10 + c.toNat - 'a'.toNat)
  else none

def isLowerHexOfLength (n : Nat) (s : String) : Bool :=
  s.length == n && s.toList.all (hexNibble? · |>.isSome)

def validSha256 (s : String) : Bool :=
  s.startsWith "sha256:" &&
    isLowerHexOfLength 64 (String.ofList (s.toList.drop 7))

/-! ## Parsing the wire spelling into `Core.Digest32` -/

private def parseByte? (hi lo : Char) : Option (Fin 256) := do
  let h ← hexNibble? hi
  let l ← hexNibble? lo
  let n := 16 * h + l
  if hn : n < 256 then some ⟨n, hn⟩ else none

private def parseDigestList? : List Char → Option (List (Fin 256))
  | [] => some []
  | hi :: lo :: rest => do
      let b ← parseByte? hi lo
      return b :: (← parseDigestList? rest)
  | _ => none

/-- Parse the exact wire spelling used by POAG1 into Core's 32-byte type. -/
def parseDigest32? (s : String) : Option Digest32 := do
  if !validSha256 s then none else
    let bytes ← parseDigestList? (s.toList.drop 7)
    if h : bytes.length = 32 then
      some { bytes := bytes, length_eq := h }
    else none

/-- Parse an identifier whose wire encoding is 64 lowercase hexadecimal digits
without the `sha256:` claim.  Federation identifiers use this spelling. -/
def parseBytes32Hex? (s : String) : Option Digest32 :=
  if isLowerHexOfLength 64 s then parseDigest32? ("sha256:" ++ s) else none

/-! ## Rendering a `Digest32` back to the wire -/

private def byteHex (b : Fin 256) : String :=
  String.ofList [lowerHexDigit (b.val / 16), lowerHexDigit (b.val % 16)]

def bytes32Hex (d : Digest32) : String :=
  String.join (d.bytes.map byteHex)

def digestHex (d : Digest32) : String :=
  "sha256:" ++ bytes32Hex d

end Dregg2.Games.PathOfAngels.Emit
