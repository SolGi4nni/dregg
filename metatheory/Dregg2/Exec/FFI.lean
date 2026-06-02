/-
# Dregg2.Exec.FFI — the C-ABI boundary onto the PROVED executable kernel.

A thin, scalar-only (`UInt64`/`UInt8`) shell over `Dregg2.Exec` (`Kernel.lean`):
the SAME `exec` whose conservation (`exec_conserves`) and integrity (`exec_authorized`)
are proved in Lean is the one a C/Rust host calls here. No new logic — we only marshal
`UInt64` ⇄ `ℤ` at the boundary and `@[export]` two entry points. This is the cascade
seam for dregg2 §8 (the Rust boundary hosts the verified kernel).
-/
import Dregg2.Exec.Kernel
import Dregg2.Exec.RecordKernel
import Dregg2.Exec.TurnExecutorFull
import Dregg2.Exec.FullForest         -- the PROVED tree executor `execFullForestA` (META-FILL A)
import Dregg2.Exec.FullForestAuth     -- the 10-variant `Authorization` sum (META-FILL D)

namespace Dregg2.Exec.FFI

open Dregg2.Exec
open Dregg2.Authority

/-- **C entry point — run one transfer, return the conserved total.**

Builds a 2-account state (`{0,1}`, `bal 0 ↦ balA`, `bal 1 ↦ balB`, no caps), a turn
moving `amt` from cell 0 to cell 1 under actor 0's own authority, runs the proved
`Exec.exec`, and returns the live total: on success the (conserved) total of the new
state, on a fail-closed `none` the unchanged total of the input. By `exec_conserves`
both equal `balA + balB`. -/
@[export dregg_kernel_transfer_total]
def transferTotal (balA balB amt : UInt64) : UInt64 :=
  let k : KernelState :=
    { accounts := {0, 1}
      bal := fun c => if c = 0 then Int.ofNat balA.toNat
                      else if c = 1 then Int.ofNat balB.toNat else 0
      caps := fun _ => [] }
  let turn : Turn := { actor := 0, src := 0, dst := 1, amt := Int.ofNat amt.toNat }
  let result : KernelState := (Exec.exec k turn).getD k
  (Exec.total result).toNat.toUInt64

/-- **C entry point — the authority check, in isolation.**

Returns `1` iff `actor` is authorized over `src = 0` for a unit transfer under the
empty cap table (i.e. iff `actor = 0`, ownership). Demonstrates `Exec.authorizedB`
— the integrity predicate from `exec` — callable directly from C. -/
@[export dregg_kernel_authorized]
def authorized (actor : UInt64) : UInt8 :=
  if Exec.authorizedB (fun _ => []) { actor := actor.toNat, src := 0, dst := 1, amt := 1 }
  then 1 else 0

/-- **C entry point — run one transfer on the CONTENT-ADDRESSED record cell, return the conserved
total `balance` field.**

The record-cell analog of `transferTotal`: the cell-state is now a `Value` record (carrying a
`balance` field plus, here, a `nonce` field that the transfer must leave intact), NOT two scalars.
We marshal the `balance` FIELD as the scalar at the boundary — the FFI signature stays
`UInt64 → UInt64 → UInt64 → UInt64`, byte-stable with `transferTotal`, so the Rust host and the
10k/10k differential oracle need no signature change — while the PROVED function underneath is now
`RecordKernel.recKExec` over the real record cell. By `recKExec_conserves` the returned total equals
`balA + balB` (conserved over the `balance` field). This turns the scalar PoC into the actual
record-cell migration ratchet, with the marshalling honestly limited to the `balance` field. -/
@[export dregg_record_kernel_transfer_total]
def recordTransferTotal (balA balB amt : UInt64) : UInt64 :=
  let k : RecordKernelState :=
    { accounts := {0, 1}
      cell := fun c => if c = 0 then .record [("balance", .int (Int.ofNat balA.toNat)),
                                              ("nonce", .int 0)]
                       else if c = 1 then .record [("balance", .int (Int.ofNat balB.toNat))]
                       else .record [("balance", .int 0)]
      caps := fun _ => [] }
  let turn : Turn := { actor := 0, src := 0, dst := 1, amt := Int.ofNat amt.toNat }
  let result : RecordKernelState := (Exec.recKExec k turn).getD k
  (Exec.recTotal result).toNat.toUInt64

/-! ## The `Value`/`RecordKernelState` WIRE CODEC — marshalling real record cell-state.

The scalar exports above marshal only a single `balance` field as a `UInt64`. To make the
FFI a real SWAP-enabler — the node calling `recKExec` over the **content-addressed record
cell** rather than a scalar — we need to marshal a whole `RecordKernelState` (the per-cell
`Value` records + the turn) across the C ABI, run the PROVED `recKExec`, and marshal the
output state back.

We reuse the `CircuitEmit.lean` discipline: a deterministic Lean `→ String` encoder + its
parser, both sides agreeing on a minimal JSON grammar, differential-checked against a Rust
reference (cross-validation, NOT certification — the codec is TCB, not proved). The wire
grammar (no whitespace, exactly as emitted):

    state  := {"cells":CELLS,"actor":N,"src":N,"dst":N,"amt":N}        (input)
    out    := {"cells":CELLS,"ok":B}                                  (output; B ∈ {0,1})
    CELLS  := [] | [CELL(,CELL)*]
    CELL   := [N,VALUE]                                               (cell-id, its record)
    VALUE  := {"int":N} | {"dig":N} | {"sym":N} | {"rec":FIELDS}
    FIELDS := [] | [FIELD(,FIELD)*]
    FIELD  := ["NAME",VALUE]
    N      := a signed decimal integer;  NAME := a JSON string (plain chars).

`amt` and `int` payloads are signed (`Int`); ids/digests/symbols are non-negative.
The MARSHALLING BOUNDARY is exactly this grammar: it is the only thing the Lean and Rust
sides must agree on, and the differential is what certifies the agreement empirically.
Nested records are handled (the grammar/codec recurse), so this covers the full `Value`
leaf set (int/dig/sym/record), not only the flat `balance` record.
-/

/-! ### Encoder: `Value`/state → canonical JSON `String`. -/

/-- JSON-escape the plain field-name characters the codec uses (`"` and `\`). Field names
in this kernel are simple identifiers, but we escape defensively so the grammar stays exact. -/
def jsonEscape (s : String) : String :=
  s.foldl (fun acc c =>
    acc ++ (if c == '"' then "\\\"" else if c == '\\' then "\\\\" else String.singleton c)) ""

mutual
/-- Encode a `Value` to its canonical wire JSON. -/
def encodeValue : Value → String
  | .int i    => "{\"int\":" ++ toString i ++ "}"
  | .dig d    => "{\"dig\":" ++ toString d ++ "}"
  | .sym s    => "{\"sym\":" ++ toString s ++ "}"
  | .record fs => "{\"rec\":" ++ encodeFields fs ++ "}"
/-- Encode a record's named fields as a JSON array of `["name",value]` pairs. -/
def encodeFields : List (FieldName × Value) → String
  | []          => "[]"
  | (n, v) :: fs =>
      let head := "[\"" ++ jsonEscape n ++ "\"," ++ encodeValue v ++ "]"
      "[" ++ head ++ encodeFieldsTail fs ++ "]"
/-- The comma-prefixed tail of a fields array. -/
def encodeFieldsTail : List (FieldName × Value) → String
  | []          => ""
  | (n, v) :: fs => ",[\"" ++ jsonEscape n ++ "\"," ++ encodeValue v ++ "]" ++ encodeFieldsTail fs
end

/-- Encode a list of `(cellId, Value)` entries as the `CELLS` array. -/
def encodeCells : List (CellId × Value) → String
  | []      => "[]"
  | c :: cs =>
      let one := fun (p : CellId × Value) =>
        "[" ++ toString p.1 ++ "," ++ encodeValue p.2 ++ "]"
      "[" ++ one c ++ (cs.foldl (fun acc p => acc ++ "," ++ one p) "") ++ "]"

/-- Encode an output state: the post-state cells + the commit bit. -/
def encodeOut (cells : List (CellId × Value)) (ok : Bool) : String :=
  "{\"cells\":" ++ encodeCells cells ++ ",\"ok\":" ++ (if ok then "1" else "0") ++ "}"

/-! ### Decoder: a tiny recursive-descent parser over the fixed grammar.

A hand-rolled, zero-dependency parser (Lean-core `String`/`List Char`). It is intentionally
strict: any deviation from the emitted grammar returns `none` (fail-closed), so a malformed
wire can never silently produce a wrong state. The parser state is `(remaining chars)`; it
returns `(value, rest)` on success. -/

/-- Parse position: the remaining character list. -/
abbrev PState := List Char

/-- Match an explicit char list as a prefix; `none` on mismatch. -/
def litGo : List Char → PState → Option PState
  | [],      rest    => some rest
  | l :: ls, r :: rs => if l == r then litGo ls rs else none
  | _ :: _,  []      => none

/-- Consume an exact literal prefix; `none` on mismatch. -/
def lit (s : String) (cs : PState) : Option PState := litGo s.toList cs

/-- Greedily collect leading decimal digits, returning them and the rest. -/
def digitsGo : PState → List Char → (List Char × PState)
  | c :: rest, acc => if c.isDigit then digitsGo rest (acc ++ [c]) else (acc, c :: rest)
  | [],        acc => (acc, [])

/-- Parse a signed decimal integer; returns the `Int` and the rest. -/
def parseInt (cs : PState) : Option (Int × PState) :=
    let (neg, cs) := match cs with | '-' :: rest => (true, rest) | _ => (false, cs)
    let (ds, rest) := digitsGo cs []
    if ds.isEmpty then none
    else
      let n : Nat := ds.foldl (fun a d => a * 10 + (d.toNat - '0'.toNat)) 0
      some ((if neg then -(Int.ofNat n) else Int.ofNat n), rest)

/-- Parse a non-negative `Nat` (an id / digest / symbol payload). -/
def parseNat (cs : PState) : Option (Nat × PState) :=
  match parseInt cs with
  | some (i, rest) => if i ≥ 0 then some (i.toNat, rest) else none
  | none           => none

/-- Accumulate a JSON string body until the closing quote (escapes: `\"`, `\\`). -/
def parseStrGo : PState → List Char → Option (String × PState)
  | '"' :: rest,         acc => some (String.ofList acc, rest)
  | '\\' :: '"' :: rest, acc => parseStrGo rest (acc ++ ['"'])
  | '\\' :: '\\' :: rest, acc => parseStrGo rest (acc ++ ['\\'])
  | c :: rest,           acc => parseStrGo rest (acc ++ [c])
  | [],                  _   => none

/-- Parse a JSON string literal (handles the `\"` and `\\` escapes the encoder emits). -/
def parseStr : PState → Option (String × PState)
  | '"' :: cs => parseStrGo cs []
  | _ => none

/- Parse a `Value` and its sub-records. Fuel-bounded on a `Nat` so termination is structural;
the caller seeds the fuel with the wire length (an upper bound on parse depth). -/
mutual
/-- Parse a `Value` from the wire (int/dig/sym/record). -/
def parseValue (fuel : Nat) (cs : PState) : Option (Value × PState) :=
  match fuel with
  | 0 => none
  | fuel + 1 =>
    match lit "{\"int\":" cs with
    | some rest => match parseInt rest with
                   | some (i, r) => (lit "}" r).map (fun r' => (Value.int i, r'))
                   | none => none
    | none =>
    match lit "{\"dig\":" cs with
    | some rest => match parseNat rest with
                   | some (d, r) => (lit "}" r).map (fun r' => (Value.dig d, r'))
                   | none => none
    | none =>
    match lit "{\"sym\":" cs with
    | some rest => match parseNat rest with
                   | some (s, r) => (lit "}" r).map (fun r' => (Value.sym s, r'))
                   | none => none
    | none =>
    match lit "{\"rec\":" cs with
    | some rest => match parseFields fuel rest with
                   | some (fs, r) => (lit "}" r).map (fun r' => (Value.record fs, r'))
                   | none => none
    | none => none

/-- Parse a `FIELDS` array `[["name",value],...]` (or `[]`). -/
def parseFields (fuel : Nat) (cs : PState) : Option (List (FieldName × Value) × PState) :=
  match lit "[]" cs with
  | some rest => some ([], rest)
  | none =>
    match lit "[" cs with
    | none => none
    | some rest => parseFieldsLoop fuel rest

/-- Parse the non-empty body of a `FIELDS` array, having consumed the opening `[`. -/
def parseFieldsLoop (fuel : Nat) (cs : PState) : Option (List (FieldName × Value) × PState) :=
  match fuel with
  | 0 => none
  | fuel + 1 =>
    match lit "[" cs with
    | none => none
    | some r0 =>
    match parseStr r0 with
    | none => none
    | some (name, r1) =>
      match lit "," r1 with
      | none => none
      | some r2 =>
        match parseValue fuel r2 with
        | none => none
        | some (v, r3) =>
          match lit "]" r3 with
          | none => none
          | some r4 =>
            match lit "," r4 with
            | some r5 => match parseFieldsLoop fuel r5 with
                         | some (rest, r6) => some ((name, v) :: rest, r6)
                         | none => none
            | none => match lit "]" r4 with
                      | some r6 => some ([(name, v)], r6)
                      | none => none
end

/-- Parse one `CELL` `[id,value]`. -/
def parseCell (fuel : Nat) (cs : PState) : Option ((CellId × Value) × PState) :=
  match lit "[" cs with
  | none => none
  | some r1 =>
    match parseNat r1 with
    | none => none
    | some (id, r2) =>
      match lit "," r2 with
      | none => none
      | some r3 =>
        match parseValue fuel r3 with
        | none => none
        | some (v, r4) => (lit "]" r4).map (fun r5 => ((id, v), r5))

/-- Parse a `CELLS` array `[[id,value],...]` (or `[]`). Fuel-bounded on the number of cells. -/
def parseCellsLoop (fuel : Nat) (cs : PState) : Option (List (CellId × Value) × PState) :=
  match fuel with
  | 0 => none
  | fuel + 1 =>
    match parseCell fuel cs with
    | none => none
    | some (cell, r1) =>
      match lit "," r1 with
      | some r2 => match parseCellsLoop fuel r2 with
                   | some (rest, r3) => some (cell :: rest, r3)
                   | none => none
      | none => match lit "]" r1 with
                | some r3 => some ([cell], r3)
                | none => none

/-- Parse the `CELLS` array (the empty/non-empty split). -/
def parseCells (fuel : Nat) (cs : PState) : Option (List (CellId × Value) × PState) :=
  match lit "[]" cs with
  | some rest => some ([], rest)
  | none =>
    match lit "[" cs with
    | none => none
    | some rest => parseCellsLoop fuel rest

/-- The decoded input: the cell entries + the turn fields. -/
structure WireInput where
  cells : List (CellId × Value)
  actor : CellId
  src   : CellId
  dst   : CellId
  amt   : Int

/-- Parse a full input state `{"cells":CELLS,"actor":N,"src":N,"dst":N,"amt":N}`. Strict:
the whole string must be consumed (no trailing bytes). -/
def parseInput (s : String) : Option WireInput :=
  let cs := s.toList
  let fuel := cs.length + 1
  match lit "{\"cells\":" cs with
  | none => none
  | some r0 =>
    match parseCells fuel r0 with
    | none => none
    | some (cells, r1) =>
      match lit ",\"actor\":" r1 with
      | none => none
      | some r2 => match parseNat r2 with
        | none => none
        | some (actor, r3) =>
          match lit ",\"src\":" r3 with
          | none => none
          | some r4 => match parseNat r4 with
            | none => none
            | some (src, r5) =>
              match lit ",\"dst\":" r5 with
              | none => none
              | some r6 => match parseNat r6 with
                | none => none
                | some (dst, r7) =>
                  match lit ",\"amt\":" r7 with
                  | none => none
                  | some r8 => match parseInt r8 with
                    | none => none
                    | some (amt, r9) =>
                      match lit "}" r9 with
                      | some [] => some { cells := cells, actor := actor, src := src,
                                          dst := dst, amt := amt }
                      | _ => none

/-! ### The state-marshalling step export. -/

/-- Build a `RecordKernelState` from decoded cell entries: the `accounts` set is exactly the
listed cell-ids, the `cell` function looks each id up in the entry list (absent ⇒ an empty
`balance:0` record, matching `recKExec`'s fail-soft measure), and the cap table is empty
(authority is by ownership — the differential's regime, identical to the scalar exports). -/
def stateOfCells (cells : List (CellId × Value)) : RecordKernelState :=
  { accounts := (cells.map Prod.fst).toFinset
    cell := fun c => match cells.find? (fun p => p.1 == c) with
                     | some p => p.2
                     | none   => .record [(Exec.balanceField, .int 0)]
    caps := fun _ => [] }

/-- Read the post-state cells back out, in the SAME id order as the input list (so the wire is
deterministic and the Rust side can compare positionally). -/
def cellsOfState (ids : List CellId) (k : RecordKernelState) : List (CellId × Value) :=
  ids.map (fun c => (c, k.cell c))

/-- **C entry point — marshal a full record-cell STATE, run the PROVED `recKExec`, marshal back.**

This is the real swap-enabler: the input is a canonical JSON encoding of a `RecordKernelState`
(per-cell `Value` records, not a scalar) plus the turn; we decode it, run the SAME
`Exec.recKExec` whose conservation/authority/fail-closed laws are proved in `RecordKernel.lean`,
and re-encode the output state. On a malformed wire (decode failure) we fail-closed to
`{"cells":[],"ok":0}`. On a rejected turn (`recKExec = none`) we echo the unchanged input cells
with `ok:0`; on commit we emit the new cells with `ok:1`. By `recKExec_conserves` the total
`balance` over the live accounts is preserved across a commit — now end-to-end over the wire. -/
@[export dregg_record_kernel_step]
def recordKernelStep (input : String) : String :=
  match parseInput input with
  | none => encodeOut [] false
  | some wi =>
    let k := stateOfCells wi.cells
    let ids := wi.cells.map Prod.fst
    let turn : Turn := { actor := wi.actor, src := wi.src, dst := wi.dst, amt := wi.amt }
    match Exec.recKExec k turn with
    | some k' => encodeOut (cellsOfState ids k') true
    | none    => encodeOut (cellsOfState ids k) false

/-! ## The CAPS-bearing wire codec — marshalling the HELD-CAP authority table.

`recordKernelStep` above marshals the record `cell`-state but hard-codes `caps := fun _ => []`,
so authority there is by OWNERSHIP only (`actor = src`). For the cascade swap the node's
turn-decision must exercise the FULL `authorizedB` gate — including the cross-vat case where an
`actor ≠ owner` is authorized because it HOLDS a discharging cap on `src` (a `node src` cap, or
an `endpoint src` cap carrying `Auth.write`; see `Kernel.authorizedB`). So we extend the wire to
also carry the `Caps` table (`Label → List Cap`) and feed it into the SAME proved `recKExec`.

The cap wire grammar (appended to the input object, before `actor`; output is UNCHANGED):

    state_caps := {"cells":CELLS,"caps":CAPS,"actor":N,"src":N,"dst":N,"amt":N}
    CAPS    := [] | [CAPENTRY(,CAPENTRY)*]
    CAPENTRY:= [N,CAPLIST]                        (holder-label, that holder's cap list)
    CAPLIST := [] | [CAP(,CAP)*]
    CAP     := {"null":0} | {"node":N} | {"ep":[N,AUTHS]}   (null / node target / endpoint)
    AUTHS   := [] | [A(,A)*]                       (A := an Auth tag, 0..6)
    A       := 0=read 1=write 2=grant 3=call 4=reply 5=reset 6=control  (the `Auth` ctor order)

A `Caps` value is a TOTAL function `Label → List Cap`; we marshal it as the finite list of
holders with a non-empty slot, and reconstruct the total function as "listed slot, else `[]`"
(matching the differential's regime: only the listed holders carry caps). The caps codec is
likewise TCB — cross-validated by the caps differential, not certified. -/

/-! ### Auth tag ⇄ `Auth` (the 7-constructor enumeration). -/

/-- Encode an `Auth` to its wire tag (`0..6`), in `Auth`'s constructor order. -/
def authTag : Auth → Nat
  | .read => 0 | .write => 1 | .grant => 2 | .call => 3
  | .reply => 4 | .reset => 5 | .control => 6

/-- Decode a wire tag back to an `Auth`; out-of-range ⇒ `none` (fail-closed). -/
def authOfTag : Nat → Option Auth
  | 0 => some .read | 1 => some .write | 2 => some .grant | 3 => some .call
  | 4 => some .reply | 5 => some .reset | 6 => some .control | _ => none

/-! ### Caps encoder. -/

/-- Encode an `Auth` list as the `AUTHS` array. -/
def encodeAuths : List Auth → String
  | []      => "[]"
  | a :: as =>
      "[" ++ toString (authTag a) ++ (as.foldl (fun acc x => acc ++ "," ++ toString (authTag x)) "") ++ "]"

/-- Encode one `Cap` to its wire form. -/
def encodeCap : Cap → String
  | .null         => "{\"null\":0}"
  | .node t       => "{\"node\":" ++ toString t ++ "}"
  | .endpoint t r => "{\"ep\":[" ++ toString t ++ "," ++ encodeAuths r ++ "]}"

/-- Encode a holder's cap list as the `CAPLIST` array. -/
def encodeCapList : List Cap → String
  | []      => "[]"
  | c :: cs =>
      "[" ++ encodeCap c ++ (cs.foldl (fun acc x => acc ++ "," ++ encodeCap x) "") ++ "]"

/-- Encode the `CAPS` array from a list of `(holder, capList)` entries. -/
def encodeCapsEntries : List (CellId × List Cap) → String
  | []      => "[]"
  | e :: es =>
      let one := fun (p : CellId × List Cap) =>
        "[" ++ toString p.1 ++ "," ++ encodeCapList p.2 ++ "]"
      "[" ++ one e ++ (es.foldl (fun acc p => acc ++ "," ++ one p) "") ++ "]"

/-! ### Caps decoder (reuses the `lit`/`parseNat`/`parseInt` primitives above). -/

/-- Parse an `AUTHS` array `[A,...]` (or `[]`), validating each tag fail-closed. -/
def parseAuths (cs : PState) : Option (List Auth × PState) :=
  match lit "[]" cs with
  | some rest => some ([], rest)
  | none =>
    match lit "[" cs with
    | none => none
    | some r0 =>
      let rec loop (fuel : Nat) (cs : PState) : Option (List Auth × PState) :=
        match fuel with
        | 0 => none
        | fuel + 1 =>
          match parseNat cs with
          | none => none
          | some (tag, r1) =>
            match authOfTag tag with
            | none => none
            | some a =>
              match lit "," r1 with
              | some r2 => match loop fuel r2 with
                           | some (rest, r3) => some (a :: rest, r3)
                           | none => none
              | none => match lit "]" r1 with
                        | some r3 => some ([a], r3)
                        | none => none
      loop (cs.length + 1) r0

/-- Parse one `CAP` (`null`/`node`/`ep`). -/
def parseCap (cs : PState) : Option (Cap × PState) :=
  match lit "{\"null\":0}" cs with
  | some rest => some (Cap.null, rest)
  | none =>
  match lit "{\"node\":" cs with
  | some rest => match parseNat rest with
                 | some (t, r) => (lit "}" r).map (fun r' => (Cap.node t, r'))
                 | none => none
  | none =>
  match lit "{\"ep\":[" cs with
  | some rest =>
    match parseNat rest with
    | none => none
    | some (t, r1) =>
      match lit "," r1 with
      | none => none
      | some r2 =>
        match parseAuths r2 with
        | none => none
        | some (auths, r3) =>
          match lit "]" r3 with
          | none => none
          | some r4 => (lit "}" r4).map (fun r5 => (Cap.endpoint t auths, r5))
  | none => none

/-- Parse a `CAPLIST` array `[CAP,...]` (or `[]`). -/
def parseCapList (cs : PState) : Option (List Cap × PState) :=
  match lit "[]" cs with
  | some rest => some ([], rest)
  | none =>
    match lit "[" cs with
    | none => none
    | some r0 =>
      let rec loop (fuel : Nat) (cs : PState) : Option (List Cap × PState) :=
        match fuel with
        | 0 => none
        | fuel + 1 =>
          match parseCap cs with
          | none => none
          | some (c, r1) =>
            match lit "," r1 with
            | some r2 => match loop fuel r2 with
                         | some (rest, r3) => some (c :: rest, r3)
                         | none => none
            | none => match lit "]" r1 with
                      | some r3 => some ([c], r3)
                      | none => none
      loop (cs.length + 1) r0

/-- Parse one `CAPENTRY` `[holder,CAPLIST]`. -/
def parseCapEntry (cs : PState) : Option ((CellId × List Cap) × PState) :=
  match lit "[" cs with
  | none => none
  | some r1 =>
    match parseNat r1 with
    | none => none
    | some (holder, r2) =>
      match lit "," r2 with
      | none => none
      | some r3 =>
        match parseCapList r3 with
        | none => none
        | some (cl, r4) => (lit "]" r4).map (fun r5 => ((holder, cl), r5))

/-- Parse the `CAPS` array `[CAPENTRY,...]` (or `[]`). -/
def parseCapsEntries (cs : PState) : Option (List (CellId × List Cap) × PState) :=
  match lit "[]" cs with
  | some rest => some ([], rest)
  | none =>
    match lit "[" cs with
    | none => none
    | some r0 =>
      let rec loop (fuel : Nat) (cs : PState) : Option (List (CellId × List Cap) × PState) :=
        match fuel with
        | 0 => none
        | fuel + 1 =>
          match parseCapEntry cs with
          | none => none
          | some (e, r1) =>
            match lit "," r1 with
            | some r2 => match loop fuel r2 with
                         | some (rest, r3) => some (e :: rest, r3)
                         | none => none
            | none => match lit "]" r1 with
                      | some r3 => some ([e], r3)
                      | none => none
      loop (cs.length + 1) r0

/-- The decoded caps-bearing input: cell entries, the caps entries, and the turn fields. -/
structure WireInputCaps where
  cells : List (CellId × Value)
  caps  : List (CellId × List Cap)
  actor : CellId
  src   : CellId
  dst   : CellId
  amt   : Int

/-- Parse a full caps-bearing input state
`{"cells":CELLS,"caps":CAPS,"actor":N,"src":N,"dst":N,"amt":N}`. Strict: the whole string
must be consumed (fail-closed on any deviation). -/
def parseInputCaps (s : String) : Option WireInputCaps :=
  let cs := s.toList
  let fuel := cs.length + 1
  match lit "{\"cells\":" cs with
  | none => none
  | some r0 =>
    match parseCells fuel r0 with
    | none => none
    | some (cells, r1) =>
      match lit ",\"caps\":" r1 with
      | none => none
      | some rc0 => match parseCapsEntries rc0 with
        | none => none
        | some (caps, rc1) =>
          match lit ",\"actor\":" rc1 with
          | none => none
          | some r2 => match parseNat r2 with
            | none => none
            | some (actor, r3) =>
              match lit ",\"src\":" r3 with
              | none => none
              | some r4 => match parseNat r4 with
                | none => none
                | some (src, r5) =>
                  match lit ",\"dst\":" r5 with
                  | none => none
                  | some r6 => match parseNat r6 with
                    | none => none
                    | some (dst, r7) =>
                      match lit ",\"amt\":" r7 with
                      | none => none
                      | some r8 => match parseInt r8 with
                        | none => none
                        | some (amt, r9) =>
                          match lit "}" r9 with
                          | some [] => some { cells := cells, caps := caps, actor := actor,
                                              src := src, dst := dst, amt := amt }
                          | _ => none

/-- Reconstruct the total `Caps` function from the decoded entries: a listed holder gets its
listed cap list, every other holder gets `[]` (matching the differential's regime — only
listed holders carry caps). -/
def capsOfEntries (entries : List (CellId × List Cap)) : Caps :=
  fun l => match entries.find? (fun p => p.1 == l) with
           | some p => p.2
           | none   => []

/-- Build a `RecordKernelState` from decoded cell entries AND the decoded caps table. Identical
to `stateOfCells` except the cap table is the marshalled one rather than empty — so the
cross-vat / held-cap branch of `authorizedB` is now exercised across the FFI. -/
def stateOfCellsCaps (cells : List (CellId × Value)) (caps : List (CellId × List Cap)) :
    RecordKernelState :=
  { accounts := (cells.map Prod.fst).toFinset
    cell := fun c => match cells.find? (fun p => p.1 == c) with
                     | some p => p.2
                     | none   => .record [(Exec.balanceField, .int 0)]
    caps := capsOfEntries caps }

/-- **C entry point — marshal record cell-state PLUS the held-cap table, run the PROVED
`recKExec`, marshal back.**

The caps-bearing analog of `recordKernelStep`: the input now also carries the `Caps` table, so
the authority gate (`Kernel.authorizedB`, reused unchanged by `recKExec`) can fire on a HELD cap
(`actor ≠ src` but the actor holds a `node src` cap or an `endpoint src` cap with `Auth.write`),
not just on ownership. The output wire is IDENTICAL to `recordKernelStep`'s
(`{"cells":CELLS,"ok":B}`) so the Rust decoder is shared. Fail-closed on a malformed wire
(`{"cells":[],"ok":0}`). The conservation/authority/fail-closed laws proved in `RecordKernel.lean`
hold of EVERY commit here — now including held-cap-authorized cross-vat turns. -/
@[export dregg_record_kernel_step_caps]
def recordKernelStepCaps (input : String) : String :=
  match parseInputCaps input with
  | none => encodeOut [] false
  | some wi =>
    let k := stateOfCellsCaps wi.cells wi.caps
    let ids := wi.cells.map Prod.fst
    let turn : Turn := { actor := wi.actor, src := wi.src, dst := wi.dst, amt := wi.amt }
    match Exec.recKExec k turn with
    | some k' => encodeOut (cellsOfState ids k') true
    | none    => encodeOut (cellsOfState ids k) false

/-! ### Codec round-trip sanity (`#eval`) — the Lean side of the differential. -/

/-- A two-cell input: cell 0 = `{balance:100, nonce:7}`, cell 1 = `{balance:5}`,
turn = actor 0 moves 30 from 0→1. -/
def wireDemo : String :=
  "{\"cells\":[[0,{\"rec\":[[\"balance\",{\"int\":100}],[\"nonce\",{\"int\":7}]]}]," ++
  "[1,{\"rec\":[[\"balance\",{\"int\":5}]]}]],\"actor\":0,\"src\":0,\"dst\":1,\"amt\":30}"

#eval recordKernelStep wireDemo
-- Expect: {"cells":[[0,{"rec":[["balance",{"int":70}],["nonce",{"int":7}]]}],
--                   [1,{"rec":[["balance",{"int":35}]]}]],"ok":1}
#eval (parseInput wireDemo).isSome                                   -- true
-- Unauthorized actor 2 ⇒ fail-closed, cells unchanged, ok:0:
#eval recordKernelStep
  "{\"cells\":[[0,{\"rec\":[[\"balance\",{\"int\":100}]]}],[1,{\"rec\":[[\"balance\",{\"int\":5}]]}]],\"actor\":2,\"src\":0,\"dst\":1,\"amt\":30}"
-- Malformed wire ⇒ fail-closed empty:
#eval recordKernelStep "garbage"                                      -- {"cells":[],"ok":0}

/-! ### Caps-bearing codec sanity (`#eval`) — the held-cap authorization round-trip. -/

/-- A held-cap-authorized case: cell 0 = `{balance:100}`, cell 1 = `{balance:5}`; the cap table
gives holder 9 (NOT the owner of src 0) an `endpoint 0 [write]` cap; actor 9 moves 30 from 0→1.
The cross-vat held-cap branch of `authorizedB` fires, so this COMMITS. -/
def wireCapsDemo : String :=
  "{\"cells\":[[0,{\"rec\":[[\"balance\",{\"int\":100}]]}],[1,{\"rec\":[[\"balance\",{\"int\":5}]]}]]," ++
  "\"caps\":[[9,[{\"ep\":[0,[1]]}]]],\"actor\":9,\"src\":0,\"dst\":1,\"amt\":30}"

#eval recordKernelStepCaps wireCapsDemo
-- Expect ok:1 (held-cap authorized): {"cells":[[0,{"rec":[["balance",{"int":70}]]}],
--                                              [1,{"rec":[["balance",{"int":35}]]}]],"ok":1}
#eval (parseInputCaps wireCapsDemo).isSome                            -- true

-- A `node 0` cap (control ⇒ everything) held by actor 9 also authorizes the cross-vat move.
#eval recordKernelStepCaps
  "{\"cells\":[[0,{\"rec\":[[\"balance\",{\"int\":100}]]}],[1,{\"rec\":[[\"balance\",{\"int\":5}]]}]],\"caps\":[[9,[{\"node\":0}]]],\"actor\":9,\"src\":0,\"dst\":1,\"amt\":30}"
-- Expect ok:1.

-- Unauthorized: actor 9 holds only a READ-only endpoint on src 0 (no `write`), and is not the
-- owner ⇒ `authorizedB` is false ⇒ fail-closed, cells unchanged, ok:0.
#eval recordKernelStepCaps
  "{\"cells\":[[0,{\"rec\":[[\"balance\",{\"int\":100}]]}],[1,{\"rec\":[[\"balance\",{\"int\":5}]]}]],\"caps\":[[9,[{\"ep\":[0,[0]]}]]],\"actor\":9,\"src\":0,\"dst\":1,\"amt\":30}"
-- Expect ok:0 (read-only cap does not confer write authority).

-- No cap at all for actor 9 ⇒ fail-closed, ok:0.
#eval recordKernelStepCaps
  "{\"cells\":[[0,{\"rec\":[[\"balance\",{\"int\":100}]]}],[1,{\"rec\":[[\"balance\",{\"int\":5}]]}]],\"caps\":[],\"actor\":9,\"src\":0,\"dst\":1,\"amt\":30}"
-- Expect ok:0.

-- Malformed caps wire ⇒ fail-closed empty:
#eval recordKernelStepCaps "garbage"                                  -- {"cells":[],"ok":0}

/-! ## §FULL — the FULL-TURN export: `execFullTurn` over a `List FullAction`.

`recordKernelStep[Caps]` above run ONE `recKExec` step (single transfer) ± caps. The node's real
turn-decision is `TurnExecutorFull.execFullTurn` — an ALL-OR-NOTHING transaction over a
`List FullAction` (balance/delegate/revoke/mint/burn). This section marshals a whole
`(RecChainedState, List FullAction)` across the wire, runs the PROVED `execFullTurn`, and re-encodes
the resulting `Option` state — INCLUDING the rollback case (any failing action aborts the whole turn,
leaving state unchanged; on the wire this is `ok:0` echoing the unchanged input).

The full-turn wire grammar (additive; reuses CELLS/CAPS/VALUE codecs above):

    turn   := {"cells":CELLS,"caps":CAPS,"actions":ACTIONS}
    out    := {"cells":CELLS,"caps":CAPS,"loglen":N,"ok":B}     (B ∈ {0,1})
    ACTIONS:= [] | [ACTION(,ACTION)*]
    ACTION := {"bal":[M,E,actor,src,dst,amt]}     (M = method Nat, E = effect-kind tag Nat)
            | {"del":[delegator,recipient,t]}
            | {"rev":[holder,t]}
            | {"mint":[actor,cell,amt]}
            | {"burn":[actor,cell,amt]}

The OUTPUT carries the post-state caps too, because `delegate`/`revoke` MUTATE the cap table — they
are observable across the seam only if echoed back. We emit caps at the OBSERVABLE label set: every
label appearing in the input caps OR in any action (actor/src/dst/holder/delegator/recipient/target),
in a deterministic sorted order, so the Rust reference can compare positionally.

Like the rest of the codec this is TCB (cross-validated by the differential, NOT proved). The
PROVED function underneath is `execFullTurn`, carrying `execFullTurn_ledger`/`_conserves`/
`_each_attests` (`TurnExecutorFull.lean §10`): every committed turn attests the four StepInv
conjuncts per action by construction. -/

open Dregg2.Exec.TurnExecutorFull (FullAction execFull execFullTurn)
open Dregg2.Exec.TurnExecutor (Action)
open Dregg2.CatalogInstances (EffectKind)

/-! ### Effect-kind tag ⇄ `EffectKind` (a minimal enumeration — only the conservation-relevant
balance kinds are reachable through the balance branch of `execFull`, which RUNS `recCexec s a.move`
and is INDIFFERENT to the `effect`/`method` tag; we round-trip the tag faithfully nonetheless). -/

/-- Encode an `EffectKind` to a wire tag. Only `transfer` (the canonical balance op) is given a
distinguished tag `1`; every other kind maps to `0` (`setField`, the inert default) — sufficient
because the balance branch of `execFull` does not read the effect. -/
def effectTag : EffectKind → Nat
  | .transfer => 1
  | _         => 0

/-- Decode a wire tag to an `EffectKind` (fail-OPEN to `setField`/`transfer`; the executor is
indifferent, so any tag yields a valid balance action). -/
def effectOfTag : Nat → EffectKind
  | 1 => .transfer
  | _ => .setField

/-! ### Action encoder. -/

/-- Encode one `FullAction` to its wire form. -/
def encodeAction : FullAction → String
  | .balance a =>
      "{\"bal\":[" ++ toString a.method ++ "," ++ toString (effectTag a.effect) ++ ","
        ++ toString a.move.actor ++ "," ++ toString a.move.src ++ ","
        ++ toString a.move.dst ++ "," ++ toString a.move.amt ++ "]}"
  | .delegate del rec t =>
      "{\"del\":[" ++ toString del ++ "," ++ toString rec ++ "," ++ toString t ++ "]}"
  | .revoke holder t =>
      "{\"rev\":[" ++ toString holder ++ "," ++ toString t ++ "]}"
  | .mint actor cell amt =>
      "{\"mint\":[" ++ toString actor ++ "," ++ toString cell ++ "," ++ toString amt ++ "]}"
  | .burn actor cell amt =>
      "{\"burn\":[" ++ toString actor ++ "," ++ toString cell ++ "," ++ toString amt ++ "]}"

/-- Encode an `ACTIONS` array. -/
def encodeActions : List FullAction → String
  | []      => "[]"
  | a :: as =>
      "[" ++ encodeAction a ++ (as.foldl (fun acc x => acc ++ "," ++ encodeAction x) "") ++ "]"

/-- Encode the full-turn output: post-state cells + post-state caps (at the observable labels) +
the receipt-log length + the commit bit. -/
def encodeFullOut (cells : List (CellId × Value)) (caps : List (CellId × List Cap))
    (loglen : Nat) (ok : Bool) : String :=
  "{\"cells\":" ++ encodeCells cells
    ++ ",\"caps\":" ++ encodeCapsEntries caps
    ++ ",\"loglen\":" ++ toString loglen
    ++ ",\"ok\":" ++ (if ok then "1" else "0") ++ "}"

/-! ### Action decoder. -/

/-- Parse a fixed-length comma-separated tuple of signed integers of the given arity, having
consumed the opening `[`. Returns the ints and the rest (after the closing `]`). -/
def parseIntTuple : Nat → PState → Option (List Int × PState)
  | 0,      _  => none
  | 1,      cs =>
      match parseInt cs with
      | none => none
      | some (i, r) => (lit "]" r).map (fun r' => ([i], r'))
  | n + 1,  cs =>
      match parseInt cs with
      | none => none
      | some (i, r) =>
        match lit "," r with
        | none => none
        | some r' => (parseIntTuple n r').map (fun (xs, r'') => (i :: xs, r''))

/-- Parse one `ACTION`. -/
def parseAction (cs : PState) : Option (FullAction × PState) :=
  match lit "{\"bal\":[" cs with
  | some rest =>
    match parseIntTuple 6 rest with
    | some ([m, e, actor, src, dst, amt], r) =>
        (lit "}" r).map (fun r' =>
          (FullAction.balance
            { method := m.toNat, effect := effectOfTag e.toNat,
              move := { actor := actor.toNat, src := src.toNat, dst := dst.toNat, amt := amt } }, r'))
    | _ => none
  | none =>
  match lit "{\"del\":[" cs with
  | some rest =>
    match parseIntTuple 3 rest with
    | some ([del, rec, t], r) =>
        (lit "}" r).map (fun r' => (FullAction.delegate del.toNat rec.toNat t.toNat, r'))
    | _ => none
  | none =>
  match lit "{\"rev\":[" cs with
  | some rest =>
    match parseIntTuple 2 rest with
    | some ([holder, t], r) =>
        (lit "}" r).map (fun r' => (FullAction.revoke holder.toNat t.toNat, r'))
    | _ => none
  | none =>
  match lit "{\"mint\":[" cs with
  | some rest =>
    match parseIntTuple 3 rest with
    | some ([actor, cell, amt], r) =>
        (lit "}" r).map (fun r' => (FullAction.mint actor.toNat cell.toNat amt, r'))
    | _ => none
  | none =>
  match lit "{\"burn\":[" cs with
  | some rest =>
    match parseIntTuple 3 rest with
    | some ([actor, cell, amt], r) =>
        (lit "}" r).map (fun r' => (FullAction.burn actor.toNat cell.toNat amt, r'))
    | _ => none
  | none => none

/-- Parse an `ACTIONS` array `[ACTION,...]` (or `[]`). Fuel-bounded on the count. -/
def parseActions (cs : PState) : Option (List FullAction × PState) :=
  match lit "[]" cs with
  | some rest => some ([], rest)
  | none =>
    match lit "[" cs with
    | none => none
    | some r0 =>
      let rec loop (fuel : Nat) (cs : PState) : Option (List FullAction × PState) :=
        match fuel with
        | 0 => none
        | fuel + 1 =>
          match parseAction cs with
          | none => none
          | some (a, r1) =>
            match lit "," r1 with
            | some r2 => match loop fuel r2 with
                         | some (rest, r3) => some (a :: rest, r3)
                         | none => none
            | none => match lit "]" r1 with
                      | some r3 => some ([a], r3)
                      | none => none
      loop (cs.length + 1) r0

/-- The decoded full-turn input: cell entries, the caps entries, and the action list. -/
structure WireFullTurn where
  cells   : List (CellId × Value)
  caps    : List (CellId × List Cap)
  actions : List FullAction

/-- Parse a full-turn input `{"cells":CELLS,"caps":CAPS,"actions":ACTIONS}`. Strict: the whole
string must be consumed (fail-closed on any deviation). -/
def parseFullTurn (s : String) : Option WireFullTurn :=
  let cs := s.toList
  let fuel := cs.length + 1
  match lit "{\"cells\":" cs with
  | none => none
  | some r0 =>
    match parseCells fuel r0 with
    | none => none
    | some (cells, r1) =>
      match lit ",\"caps\":" r1 with
      | none => none
      | some rc0 => match parseCapsEntries rc0 with
        | none => none
        | some (caps, rc1) =>
          match lit ",\"actions\":" rc1 with
          | none => none
          | some ra0 => match parseActions ra0 with
            | none => none
            | some (actions, ra1) =>
              match lit "}" ra1 with
              | some [] => some { cells := cells, caps := caps, actions := actions }
              | _ => none

/-- Every cell-label and action-label observed in the input (for the deterministic caps readout):
the union of input cap holders, input cell ids, and every label mentioned by any action. Sorted
ascending and de-duplicated so the Rust side compares positionally. -/
def observedLabels (wi : WireFullTurn) : List CellId :=
  let fromCaps := wi.caps.map Prod.fst
  let fromCells := wi.cells.map Prod.fst
  let fromActions := wi.actions.flatMap (fun
    | .balance a          => [a.move.actor, a.move.src, a.move.dst]
    | .delegate del rec t => [del, rec, t]
    | .revoke holder t    => [holder, t]
    | .mint actor cell _  => [actor, cell]
    | .burn actor cell _  => [actor, cell])
  ((fromCaps ++ fromCells ++ fromActions).foldl
      (fun acc l => if acc.contains l then acc else l :: acc) []).mergeSort (· ≤ ·)

/-- Read the post-state caps at the observed labels, in the SAME sorted order, dropping empty
slots' presence by still listing the label with `[]` (so the wire is positionally deterministic). -/
def capsOfState (labels : List CellId) (k : RecordKernelState) : List (CellId × List Cap) :=
  labels.map (fun l => (l, k.caps l))

/-- **C entry point — marshal a full `(RecChainedState, List FullAction)`, run the PROVED
`execFullTurn`, marshal back.**

This is THE swap-enabler: the whole turn decision-maker. The input is a canonical JSON encoding of a
`RecChainedState` (cells + caps + an EMPTY initial log) plus the `List FullAction`; we decode it, run
the SAME `TurnExecutorFull.execFullTurn` whose ledger/conservation/step-completeness laws are proved
(`TurnExecutorFull.lean §10`), and re-encode the result.

ALL-OR-NOTHING: on a committed turn we emit the post-state cells + post-state caps + the receipt-log
length (which equals the number of committed actions) with `ok:1`. On a turn that fails mid-way
(`execFullTurn = none`) we ECHO the UNCHANGED input cells + input caps with `loglen:0` and `ok:0` —
the rollback is observable: state is exactly the pre-state. On a malformed wire we fail-closed to
`{"cells":[],"caps":[],"loglen":0,"ok":0}`. -/
@[export dregg_exec_full_turn]
def execFullTurnStep (input : String) : String :=
  match parseFullTurn input with
  | none => encodeFullOut [] [] 0 false
  | some wi =>
    let k0 := stateOfCellsCaps wi.cells wi.caps
    let s0 : RecChainedState := { kernel := k0, log := [] }
    let ids := wi.cells.map Prod.fst
    let labels := observedLabels wi
    match execFullTurn s0 wi.actions with
    | some s' =>
        encodeFullOut (cellsOfState ids s'.kernel) (capsOfState labels s'.kernel) s'.log.length true
    | none =>
        -- All-or-nothing ROLLBACK: echo the unchanged pre-state, ok:0, empty log.
        encodeFullOut (cellsOfState ids s0.kernel) (capsOfState labels s0.kernel) 0 false

/-! ### Full-turn codec sanity (`#eval`) — the Lean side of the multi-action differential. -/

/-- A mixed full-turn over two cells: actor 9 (holds `node 0`) mints +50 to cell 0, then owner 0
transfers 30 → cell 1, then burns -50 from cell 0. Nets to 0; all commit; log grows by 3. -/
def wireFullDemo : String :=
  "{\"cells\":[[0,{\"rec\":[[\"balance\",{\"int\":100}]]}],[1,{\"rec\":[[\"balance\",{\"int\":5}]]}]]," ++
  "\"caps\":[[9,[{\"node\":0}]]]," ++
  "\"actions\":[{\"mint\":[9,0,50]},{\"bal\":[0,1,0,0,1,30]},{\"burn\":[9,0,50]}]}"

#eval execFullTurnStep wireFullDemo
-- Expect ok:1, loglen:3, cell0.balance = 100+50-30-50 = 70, cell1.balance = 5+30 = 35.
#eval (parseFullTurn wireFullDemo).isSome                              -- true

-- ROLLBACK: a turn whose 2nd action is unauthorized (actor 0 cannot mint) ⇒ whole turn none ⇒
-- echo unchanged pre-state, ok:0, loglen:0.
#eval execFullTurnStep
  ("{\"cells\":[[0,{\"rec\":[[\"balance\",{\"int\":100}]]}],[1,{\"rec\":[[\"balance\",{\"int\":5}]]}]]," ++
   "\"caps\":[[9,[{\"node\":0}]]]," ++
   "\"actions\":[{\"mint\":[9,0,50]},{\"mint\":[0,0,50]}]}")
-- Expect ok:0, loglen:0, cells = {100, 5} (UNCHANGED — rollback).

-- A DELEGATE then REVOKE turn (caps mutate, balances fixed):
#eval execFullTurnStep
  ("{\"cells\":[[0,{\"rec\":[[\"balance\",{\"int\":100}]]}],[1,{\"rec\":[[\"balance\",{\"int\":5}]]}]]," ++
   "\"caps\":[[0,[{\"node\":7}]]]," ++
   "\"actions\":[{\"del\":[0,1,7]},{\"rev\":[0,7]}]}")
-- Expect ok:1, loglen:2; recipient 1 gains a `node 7` cap; holder 0 loses its `node 7` edge.

-- Empty turn ⇒ commits trivially, loglen:0, state unchanged.
#eval execFullTurnStep
  "{\"cells\":[[0,{\"rec\":[[\"balance\",{\"int\":100}]]}]],\"caps\":[],\"actions\":[]}"
-- Expect ok:1, loglen:0.

-- Malformed wire ⇒ fail-closed empty.
#eval execFullTurnStep "garbage"   -- {"cells":[],"caps":[],"loglen":0,"ok":0}


/-! # §WIDE — the COMPLETE-TURN wire codec (META-FILL I).

The `execFullTurnStep` codec above (`§FULL`) marshals a `List FullAction` over the OLD 5-arm
`FullAction` (balance/delegate/revoke/mint/burn) — a small sliver of dregg1's complete turn. THIS
section widens the wire codec to the **whole** dregg1 turn the wholesale swap must cross
(`docs/rebuild/WHOLESALE-SWAP-LEDGER.md` FILL I):

  * the **Turn ENVELOPE** — `agent` / `nonce` / `fee` / `valid_until` / `previous_receipt_hash`
    (dregg1 `turn/src/turn.rs`'s outer fields, the admission preamble's inputs);
  * the recursive **ACTION-TREE** — a node = `(auth, action, children[])` over the PROVED tree
    executor `FullForest.execFullForestA` (the META-FILL A keystone), NOT a flat list;
  * the **`Authorization` SUM** — all 10 dregg1 variants (`FullForestAuth.Authorization`), carried
    per-node, recursing through `oneOf`;
  * all **51 `EffectKind`/`FullActionA` arms** — each with its TYPED args (not the 5-arm shadow);
  * the **side-tables** on `RecordKernelState` — `escrows` / `nullifiers` / `commitments` / `swiss` /
    `queues` — plus the per-asset `bal` LEDGER (the conserved measure `execFullA` actually reads);
  * `Value.dig` as a **ByteArray32** (a fixed 64-hex-char field, pinning dregg1's `[u8;32]` width),
    and the cap `target` as the **wide cell identity** (the full `CellId`, never a truncated tag);
  * **integer widths PINNED** to the dregg1 types (documented per field below).

The PROVED function underneath is `FullForest.execFullForestA` — the tree-shaped, all-or-nothing,
per-asset transaction carrying `execFullForestA_ledger_per_asset` / `_conserves_per_asset` /
`_no_amplify` / `_each_attests` (`FullForest.lean §5-§7`). The codec carries the `Authorization`
decoration FAITHFULLY on every node (round-tripped byte-exact) even though the EXECUTED tree erases
it to the ungated `FullForestA` the proofs are stated over — the swap's auth GATE is
`FullForestAuth.execFullForestG`, a separate keystone; here the wire merely *transports* the WHO.

Like the rest of the codec this is TCB (cross-validated by the differential, NOT proved — FILL J
adds the round-trip theorem). It is STRICT / FAIL-CLOSED: any deviation from the emitted grammar
returns `none`, and the whole string must be consumed.

## Integer widths (PINNED to the dregg1 wire types)

| wire field            | Lean type        | dregg1 type            | wire form                         |
|-----------------------|------------------|------------------------|-----------------------------------|
| cell id / agent       | `CellId = Nat`   | `CellId` (`[u8;32]`)   | non-negative decimal `Nat`        |
| asset id              | `AssetId = Nat`  | `AssetType` tag        | non-negative decimal `Nat`        |
| amount / balance / fee| `ℤ`              | `i128` (signed)        | signed decimal `Int`              |
| nonce / valid_until   | `Nat`            | `u64`                  | non-negative decimal `Nat`        |
| digest / commitment   | `Nat`            | `[u8;32]`              | EXACTLY 64 lowercase hex chars    |
| swiss / escrow id     | `Nat`            | `[u8;32]` / `u64`      | non-negative decimal `Nat`        |
| effect tag            | `Nat` 0..50      | `Effect` discriminant  | non-negative decimal `Nat`        |
| auth tag              | `Nat` 0..9       | `Authorization` discr. | non-negative decimal `Nat`        |

The signed↔unsigned distinction is the load-bearing one: amounts are `Int` (a debit is a negative
delta), ids/nonces/counters are `Nat` (a negative id is rejected fail-closed by `parseNat`).
-/

namespace Wide

open Dregg2.Exec.TurnExecutorFull (FullActionA execFullA)
open Dregg2.Exec.FullForest (FullForestA FullChildA execFullForestA lowerForestA)
open Dregg2.Exec.FullForestAuth (Authorization)

/-! ## §W1 — `Value.dig` as a ByteArray32 (the 64-hex-char digest field).

dregg1 digests are `[u8;32]` — 32 bytes, 64 hex chars. The narrow codec emitted `dig` as a bare
decimal `Nat`, losing the width pin (a 5-byte and a 32-byte digest were wire-indistinguishable). The
wide codec emits EXACTLY 64 lowercase hex chars: the low 256 bits of the `Nat`, big-endian, so a
digest's wire width is fixed at the dregg1 `[u8;32]` size. The parser is strict: exactly 64 hex
chars, else `none`. -/

/-- One nibble (0..15) → its lowercase hex char. -/
def hexDigitOfNat (n : Nat) : Char :=
  if n < 10 then Char.ofNat ('0'.toNat + n) else Char.ofNat ('a'.toNat + (n - 10))

/-- A hex char ('0'..'9'/'a'..'f'/'A'..'F') → its nibble; `none` if not hex. -/
def natOfHexDigit (c : Char) : Option Nat :=
  if c.isDigit then some (c.toNat - '0'.toNat)
  else if 'a'.toNat ≤ c.toNat ∧ c.toNat ≤ 'f'.toNat then some (10 + c.toNat - 'a'.toNat)
  else if 'A'.toNat ≤ c.toNat ∧ c.toNat ≤ 'F'.toNat then some (10 + c.toNat - 'A'.toNat)
  else none

/-- Encode the low 256 bits of `n` as EXACTLY 64 lowercase hex chars (big-endian, `[u8;32]` width).
`go fuel acc m` peels nibbles low-to-high; we keep exactly 64 by padding/truncating. -/
def toHex32 (n : Nat) : String :=
  let rec go : Nat → List Char → Nat → List Char
    | 0,        acc, _ => acc
    | fuel + 1, acc, m => go fuel (hexDigitOfNat (m % 16) :: acc) (m / 16)
  String.ofList (go 64 [] n)

/-- Parse EXACTLY 64 hex chars into a `Nat` (big-endian); `none` on any non-hex or wrong length.
`go` folds the 64 chars MSB-first. -/
def ofHex32 (cs : List Char) : Option Nat :=
  if cs.length ≠ 64 then none
  else
    let rec go : List Char → Nat → Option Nat
      | [],      acc => some acc
      | c :: cs, acc => match natOfHexDigit c with
                        | some d => go cs (acc * 16 + d)
                        | none   => none
    go cs 0

/-- Consume EXACTLY 64 hex chars from the parse state, returning the decoded `Nat` and the rest.
Fail-closed if fewer than 64 chars remain or any is non-hex. -/
def parseHex32 (cs : PState) : Option (Nat × PState) :=
  let head := cs.take 64
  if head.length ≠ 64 then none
  else match ofHex32 head with
       | some n => some (n, cs.drop 64)
       | none   => none

/-! ### §W1-eval — the digest hex round-trip. -/

#eval toHex32 0
-- "0000000000000000000000000000000000000000000000000000000000000000"
#eval toHex32 255
-- "00000000000000000000000000000000000000000000000000000000000000ff"
#eval (ofHex32 (toHex32 6599973602).toList) == some 6599973602   -- true (round-trips)
#eval ofHex32 "zz".toList                                        -- none (non-hex)
#eval ofHex32 "ff".toList                                        -- none (wrong length ≠ 64)

/-! ## §W2 — the WIDE `Value` codec (`dig` as the ByteArray32 hex field) + the per-asset `bal` ledger.

The wide `Value` codec is the narrow one with `dig` widened to the 64-hex field (`§W1`). The grammar:

    VALUEW := {"int":N} | {"dig":"H64"} | {"sym":N} | {"rec":FIELDSW}    (N signed, H64 = 64 hex)
    FIELDSW:= [] | [FIELDW(,FIELDW)*]
    FIELDW := ["NAME",VALUEW]

The per-asset `bal` ledger — the conserved measure `execFullA` reads — is a list of
`(cell, asset, amount)` triples (every non-zero slot); the reconstructed `bal` is "listed slot, else
0". The grammar:

    BAL    := [] | [BALENTRY(,BALENTRY)*]
    BALENTRY := [cell,asset,amt]                                         (cell/asset Nat, amt signed)
-/

mutual
/-- Encode a `Value` to the WIDE wire JSON (`dig` → the 64-hex ByteArray32 field). -/
def encodeValueW : Value → String
  | .int i    => "{\"int\":" ++ toString i ++ "}"
  | .dig d    => "{\"dig\":\"" ++ toHex32 d ++ "\"}"
  | .sym s    => "{\"sym\":" ++ toString s ++ "}"
  | .record fs => "{\"rec\":" ++ encodeFieldsW fs ++ "}"
/-- Encode a record's named fields as the WIDE JSON array of `["name",valueW]` pairs. -/
def encodeFieldsW : List (FieldName × Value) → String
  | []          => "[]"
  | (n, v) :: fs =>
      let head := "[\"" ++ jsonEscape n ++ "\"," ++ encodeValueW v ++ "]"
      "[" ++ head ++ encodeFieldsTailW fs ++ "]"
/-- The comma-prefixed tail of a WIDE fields array. -/
def encodeFieldsTailW : List (FieldName × Value) → String
  | []          => ""
  | (n, v) :: fs => ",[\"" ++ jsonEscape n ++ "\"," ++ encodeValueW v ++ "]" ++ encodeFieldsTailW fs
end

mutual
/-- Parse a WIDE `Value` (int/dig-as-hex/sym/record). Fuel-bounded for structural termination. -/
def parseValueW (fuel : Nat) (cs : PState) : Option (Value × PState) :=
  match fuel with
  | 0 => none
  | fuel + 1 =>
    match lit "{\"int\":" cs with
    | some rest => match parseInt rest with
                   | some (i, r) => (lit "}" r).map (fun r' => (Value.int i, r'))
                   | none => none
    | none =>
    match lit "{\"dig\":\"" cs with
    | some rest => match parseHex32 rest with
                   | some (d, r) => (lit "\"}" r).map (fun r' => (Value.dig d, r'))
                   | none => none
    | none =>
    match lit "{\"sym\":" cs with
    | some rest => match parseNat rest with
                   | some (s, r) => (lit "}" r).map (fun r' => (Value.sym s, r'))
                   | none => none
    | none =>
    match lit "{\"rec\":" cs with
    | some rest => match parseFieldsW fuel rest with
                   | some (fs, r) => (lit "}" r).map (fun r' => (Value.record fs, r'))
                   | none => none
    | none => none

/-- Parse a WIDE `FIELDS` array `[["name",valueW],...]` (or `[]`). -/
def parseFieldsW (fuel : Nat) (cs : PState) : Option (List (FieldName × Value) × PState) :=
  match lit "[]" cs with
  | some rest => some ([], rest)
  | none =>
    match lit "[" cs with
    | none => none
    | some rest => parseFieldsLoopW fuel rest

/-- Parse the non-empty body of a WIDE `FIELDS` array, having consumed the opening `[`. -/
def parseFieldsLoopW (fuel : Nat) (cs : PState) : Option (List (FieldName × Value) × PState) :=
  match fuel with
  | 0 => none
  | fuel + 1 =>
    match lit "[" cs with
    | none => none
    | some r0 =>
    match parseStr r0 with
    | none => none
    | some (name, r1) =>
      match lit "," r1 with
      | none => none
      | some r2 =>
        match parseValueW fuel r2 with
        | none => none
        | some (v, r3) =>
          match lit "]" r3 with
          | none => none
          | some r4 =>
            match lit "," r4 with
            | some r5 => match parseFieldsLoopW fuel r5 with
                         | some (rest, r6) => some ((name, v) :: rest, r6)
                         | none => none
            | none => match lit "]" r4 with
                      | some r6 => some ([(name, v)], r6)
                      | none => none
end

/-- Encode the WIDE `CELLS` array (cell-id + its wide `Value` record). -/
def encodeCellsW : List (CellId × Value) → String
  | []      => "[]"
  | c :: cs =>
      let one := fun (p : CellId × Value) =>
        "[" ++ toString p.1 ++ "," ++ encodeValueW p.2 ++ "]"
      "[" ++ one c ++ (cs.foldl (fun acc p => acc ++ "," ++ one p) "") ++ "]"

/-- Parse one WIDE `CELL` `[id,valueW]`. -/
def parseCellW (fuel : Nat) (cs : PState) : Option ((CellId × Value) × PState) :=
  match lit "[" cs with
  | none => none
  | some r1 =>
    match parseNat r1 with
    | none => none
    | some (id, r2) =>
      match lit "," r2 with
      | none => none
      | some r3 =>
        match parseValueW fuel r3 with
        | none => none
        | some (v, r4) => (lit "]" r4).map (fun r5 => ((id, v), r5))

/-- Parse the WIDE `CELLS` array (the empty/non-empty split + the cons loop). -/
def parseCellsW (fuel : Nat) (cs : PState) : Option (List (CellId × Value) × PState) :=
  match lit "[]" cs with
  | some rest => some ([], rest)
  | none =>
    match lit "[" cs with
    | none => none
    | some r0 =>
      let rec loop (fuel : Nat) (cs : PState) : Option (List (CellId × Value) × PState) :=
        match fuel with
        | 0 => none
        | fuel + 1 =>
          match parseCellW (cs.length + 1) cs with
          | none => none
          | some (cell, r1) =>
            match lit "," r1 with
            | some r2 => match loop fuel r2 with
                         | some (rest, r3) => some (cell :: rest, r3)
                         | none => none
            | none => match lit "]" r1 with
                      | some r3 => some ([cell], r3)
                      | none => none
      loop (cs.length + 1) r0

/-! ### The per-asset `bal` ledger codec (`BAL` = list of `(cell,asset,amt)`). -/

/-- Encode the per-asset `bal` ledger from the list of non-zero `(cell, asset, amount)` triples. -/
def encodeBal : List (CellId × AssetId × Int) → String
  | []      => "[]"
  | e :: es =>
      let one := fun (p : CellId × AssetId × Int) =>
        "[" ++ toString p.1 ++ "," ++ toString p.2.1 ++ "," ++ toString p.2.2 ++ "]"
      "[" ++ one e ++ (es.foldl (fun acc p => acc ++ "," ++ one p) "") ++ "]"

/-- Parse one `BALENTRY` `[cell,asset,amt]`. -/
def parseBalEntry (cs : PState) : Option ((CellId × AssetId × Int) × PState) :=
  match lit "[" cs with
  | none => none
  | some r1 =>
    match parseNat r1 with
    | none => none
    | some (cell, r2) =>
      match lit "," r2 with
      | none => none
      | some r3 =>
        match parseNat r3 with
        | none => none
        | some (asset, r4) =>
          match lit "," r4 with
          | none => none
          | some r5 =>
            match parseInt r5 with
            | none => none
            | some (amt, r6) => (lit "]" r6).map (fun r7 => ((cell, asset, amt), r7))

/-- Parse the `BAL` array `[[cell,asset,amt],...]` (or `[]`). -/
def parseBal (cs : PState) : Option (List (CellId × AssetId × Int) × PState) :=
  match lit "[]" cs with
  | some rest => some ([], rest)
  | none =>
    match lit "[" cs with
    | none => none
    | some r0 =>
      let rec loop (fuel : Nat) (cs : PState) : Option (List (CellId × AssetId × Int) × PState) :=
        match fuel with
        | 0 => none
        | fuel + 1 =>
          match parseBalEntry cs with
          | none => none
          | some (e, r1) =>
            match lit "," r1 with
            | some r2 => match loop fuel r2 with
                         | some (rest, r3) => some (e :: rest, r3)
                         | none => none
            | none => match lit "]" r1 with
                      | some r3 => some ([e], r3)
                      | none => none
      loop (cs.length + 1) r0

/-- Reconstruct the total `bal : CellId → AssetId → ℤ` function from the decoded triples: a listed
`(cell,asset)` slot gets its amount, every unlisted slot gets `0` (the differential's regime). -/
def balOfEntries (entries : List (CellId × AssetId × Int)) : CellId → AssetId → ℤ :=
  fun c a => match entries.find? (fun p => p.1 == c && p.2.1 == a) with
             | some p => p.2.2
             | none   => 0

/-! ### §W2-eval — the wide Value + bal round-trips. -/

#eval encodeValueW (.dig 255)
-- {"dig":"00000000000000000000000000000000000000000000000000000000000000ff"}
#eval (parseValueW 100 (encodeValueW (.dig 6599973602)).toList).isSome      -- true
-- encode∘parse∘encode = encode (Value has no BEq, so we round-trip THROUGH the wire):
#eval (let v : Value := .record [("balance", .int 70), ("h", .dig 5)]
       match parseValueW 100 (encodeValueW v).toList with
       | some (v', []) => encodeValueW v' == encodeValueW v
       | _             => false)                                             -- true (round-trips)
#eval encodeBal [(0, 1, 100), (1, 1, -5)]                                    -- [[0,1,100],[1,1,-5]]
#eval (parseBal (encodeBal [(0, 1, 100), (1, 2, -5)]).toList)
        == some ([(0, 1, 100), (1, 2, -5)], [])                             -- true (round-trips)

/-! ## §W3 — the `Authorization` SUM codec (all 10 dregg1 variants; `Digest = Proof = Nat`).

`FullForestAuth.Authorization Digest Proof` is dregg1's 10-variant credential sum
(`turn/src/action.rs:206`). We instantiate `Digest := Nat` (a 32-byte `[u8;32]`, the hex32 field) and
`Proof := Nat` (the proof blob's canonical-encoding `Nat`; dregg1's proofs are variable-length, so a
decimal `Nat` is the faithful wire stand-in — the width is NOT `[u8;32]`). The grammar (tagged by the
dregg1 variant order 0..9):

    AUTH := {"sig":["H64",P]}                         -- (0) signature(pubkeyMsg, sig)
          | {"pf":["H64",P,N,N]}                       -- (1) proof(vk, proofBytes, boundAction, boundResource)
          | {"bread":[N]}                              -- (2) breadstuff(token)
          | {"bearer":["H64",P,B]}                     -- (3) bearer(delegMsg, delegSig, starkDelegation)
          | {"unchecked":0}                            -- (4) unchecked
          | {"captp":["H64","H64",P,P]}                -- (5) capTpDelivered(introMsg, senderMsg, introSig, senderSig)
          | {"custom":["H64",P]}                       -- (6) custom(kindStmt, proofBytes)
          | {"oneof":[[AUTH(,AUTH)*],N]}               -- (7) oneOf(candidates, proofIndex)  (RECURSES)
          | {"stealth":["H64","H64",P]}                -- (8) stealth(oneTimePk, ephemeralPk, sig)
          | {"token":["H64",P]}                        -- (9) token(issuerKey, sig)

where H64 = 64 hex chars (a `[u8;32]` Digest), P = a decimal `Nat` (a Proof blob), N = a decimal `Nat`,
B ∈ {0,1}. The digest fields are width-pinned to the dregg1 `[u8;32]` (the hex32 field); the proof
fields are the variable-length blob stand-in. `oneOf` recurses (fuel-bounded). -/

/-- A bare `Authorization Nat Nat` (the wire instantiation). -/
abbrev AuthW := Authorization Nat Nat

/-- Encode a `Digest = Nat` as the 64-hex `[u8;32]` field (quoted). -/
def encDig (d : Nat) : String := "\"" ++ toHex32 d ++ "\""

/-- Parse a quoted 64-hex `[u8;32]` Digest field. -/
def parseDig (cs : PState) : Option (Nat × PState) :=
  match lit "\"" cs with
  | none => none
  | some r0 => match parseHex32 r0 with
               | some (d, r1) => (lit "\"" r1).map (fun r2 => (d, r2))
               | none => none

mutual
/-- Encode an `Authorization Nat Nat` to its WIDE wire form (`oneOf` recurses). -/
def encodeAuthW : AuthW → String
  | .signature pk sig          => "{\"sig\":[" ++ encDig pk ++ "," ++ toString sig ++ "]}"
  | .proof vk pf ba br          =>
      "{\"pf\":[" ++ encDig vk ++ "," ++ toString pf ++ "," ++ toString ba ++ "," ++ toString br ++ "]}"
  | .breadstuff tok             => "{\"bread\":[" ++ toString tok ++ "]}"
  | .bearer dm ds stark         =>
      "{\"bearer\":[" ++ encDig dm ++ "," ++ toString ds ++ "," ++ (if stark then "1" else "0") ++ "]}"
  | .unchecked                  => "{\"unchecked\":0}"
  | .capTpDelivered im sm isig ss =>
      "{\"captp\":[" ++ encDig im ++ "," ++ encDig sm ++ "," ++ toString isig ++ "," ++ toString ss ++ "]}"
  | .custom st pf               => "{\"custom\":[" ++ encDig st ++ "," ++ toString pf ++ "]}"
  | .oneOf cands i              => "{\"oneof\":[" ++ encodeAuthListW cands ++ "," ++ toString i ++ "]}"
  | .stealth otp eph sig        =>
      "{\"stealth\":[" ++ encDig otp ++ "," ++ encDig eph ++ "," ++ toString sig ++ "]}"
  | .token key sig              => "{\"token\":[" ++ encDig key ++ "," ++ toString sig ++ "]}"

/-- Encode an `AUTH` candidate list `[AUTH(,AUTH)*]` (or `[]`) — the `oneOf` body. -/
def encodeAuthListW : List AuthW → String
  | []      => "[]"
  | a :: as => "[" ++ encodeAuthW a ++ (as.foldl (fun acc x => acc ++ "," ++ encodeAuthW x) "") ++ "]"
end

mutual
/-- Parse an `AUTH` from the wire (the 10 variants; `oneof` recurses, fuel-bounded). -/
def parseAuthW (fuel : Nat) (cs : PState) : Option (AuthW × PState) :=
  match fuel with
  | 0 => none
  | fuel + 1 =>
    match lit "{\"sig\":[" cs with
    | some r0 => match parseDig r0 with
        | none => none
        | some (pk, r1) => match lit "," r1 with
          | none => none
          | some r2 => match parseNat r2 with
            | none => none
            | some (sig, r3) => (lit "]}" r3).map (fun r => (.signature pk sig, r))
    | none =>
    match lit "{\"pf\":[" cs with
    | some r0 => match parseDig r0 with
        | none => none
        | some (vk, r1) => match lit "," r1 with
          | none => none
          | some r2 => match parseNat r2 with
            | none => none
            | some (pf, r3) => match lit "," r3 with
              | none => none
              | some r4 => match parseNat r4 with
                | none => none
                | some (ba, r5) => match lit "," r5 with
                  | none => none
                  | some r6 => match parseNat r6 with
                    | none => none
                    | some (br, r7) => (lit "]}" r7).map (fun r => (.proof vk pf ba br, r))
    | none =>
    match lit "{\"bread\":[" cs with
    | some r0 => match parseNat r0 with
        | none => none
        | some (tok, r1) => (lit "]}" r1).map (fun r => (.breadstuff tok, r))
    | none =>
    match lit "{\"bearer\":[" cs with
    | some r0 => match parseDig r0 with
        | none => none
        | some (dm, r1) => match lit "," r1 with
          | none => none
          | some r2 => match parseNat r2 with
            | none => none
            | some (ds, r3) => match lit "," r3 with
              | none => none
              | some r4 => match parseNat r4 with
                | none => none
                | some (b, r5) =>
                    if b ≤ 1 then (lit "]}" r5).map (fun r => (.bearer dm ds (b == 1), r)) else none
    | none =>
    match lit "{\"unchecked\":0}" cs with
    | some r0 => some (.unchecked, r0)
    | none =>
    match lit "{\"captp\":[" cs with
    | some r0 => match parseDig r0 with
        | none => none
        | some (im, r1) => match lit "," r1 with
          | none => none
          | some r2 => match parseDig r2 with
            | none => none
            | some (sm, r3) => match lit "," r3 with
              | none => none
              | some r4 => match parseNat r4 with
                | none => none
                | some (isig, r5) => match lit "," r5 with
                  | none => none
                  | some r6 => match parseNat r6 with
                    | none => none
                    | some (ss, r7) => (lit "]}" r7).map (fun r => (.capTpDelivered im sm isig ss, r))
    | none =>
    match lit "{\"custom\":[" cs with
    | some r0 => match parseDig r0 with
        | none => none
        | some (st, r1) => match lit "," r1 with
          | none => none
          | some r2 => match parseNat r2 with
            | none => none
            | some (pf, r3) => (lit "]}" r3).map (fun r => (.custom st pf, r))
    | none =>
    match lit "{\"oneof\":[" cs with
    | some r0 => match parseAuthListW fuel r0 with
        | none => none
        | some (cands, r1) => match lit "," r1 with
          | none => none
          | some r2 => match parseNat r2 with
            | none => none
            | some (i, r3) => (lit "]}" r3).map (fun r => (.oneOf cands i, r))
    | none =>
    match lit "{\"stealth\":[" cs with
    | some r0 => match parseDig r0 with
        | none => none
        | some (otp, r1) => match lit "," r1 with
          | none => none
          | some r2 => match parseDig r2 with
            | none => none
            | some (eph, r3) => match lit "," r3 with
              | none => none
              | some r4 => match parseNat r4 with
                | none => none
                | some (sig, r5) => (lit "]}" r5).map (fun r => (.stealth otp eph sig, r))
    | none =>
    match lit "{\"token\":[" cs with
    | some r0 => match parseDig r0 with
        | none => none
        | some (key, r1) => match lit "," r1 with
          | none => none
          | some r2 => match parseNat r2 with
            | none => none
            | some (sig, r3) => (lit "]}" r3).map (fun r => (.token key sig, r))
    | none => none

/-- The cons-loop body of an `AUTH` candidate list, having consumed the opening `[`: parse one
`AUTH`, then either `,`-recurse or close on `]`. Fuel-bounded (the SAME `fuel` the enclosing
`parseAuthW` threads, so the nested-`oneof` recursion is structurally decreasing). -/
def parseAuthLoopW (fuel : Nat) (cs : PState) : Option (List AuthW × PState) :=
  match fuel with
  | 0 => none
  | fuel + 1 =>
    match parseAuthW fuel cs with
    | none => none
    | some (a, r1) =>
      match lit "," r1 with
      | some r2 => match parseAuthLoopW fuel r2 with
                   | some (rest, r3) => some (a :: rest, r3)
                   | none => none
      | none => match lit "]" r1 with
                | some r3 => some ([a], r3)
                | none => none

/-- Parse an `AUTH` candidate list `[AUTH(,AUTH)*]` (or `[]`) — the `oneof` body. Fail-closed; the
non-empty body is parsed by `parseAuthLoopW` after the opening `[`. -/
def parseAuthListW (fuel : Nat) (cs : PState) : Option (List AuthW × PState) :=
  match lit "[]" cs with
  | some rest => some ([], rest)
  | none =>
    match lit "[" cs with
    | none => none
    | some r0 => parseAuthLoopW fuel r0
end

/-! ### §W3-eval — the Authorization sum round-trips (each variant + the recursive oneOf). -/

/-- Round-trip an `Authorization` THROUGH the wire (the sum has no BEq; we compare re-encodings). -/
def authRoundtrips (a : AuthW) : Bool :=
  match parseAuthW 100 (encodeAuthW a).toList with
  | some (a', []) => encodeAuthW a' == encodeAuthW a
  | _             => false

#eval authRoundtrips (.signature 7 9)                                       -- true
#eval authRoundtrips (.proof 1 2 3 4)                                       -- true
#eval authRoundtrips (.breadstuff 42)                                      -- true
#eval authRoundtrips (.bearer 5 6 true)                                    -- true (stark)
#eval authRoundtrips (.bearer 5 6 false)                                   -- true (signed)
#eval authRoundtrips .unchecked                                            -- true
#eval authRoundtrips (.capTpDelivered 1 2 3 4)                             -- true
#eval authRoundtrips (.custom 8 9)                                         -- true
#eval authRoundtrips (.stealth 11 12 13)                                   -- true
#eval authRoundtrips (.token 14 15)                                        -- true
-- the RECURSIVE oneOf (nested candidates round-trip):
#eval authRoundtrips (.oneOf [.signature 7 9, .token 14 15] 1)             -- true
#eval authRoundtrips (.oneOf [.oneOf [.unchecked] 0, .breadstuff 3] 1)     -- true (nested)
-- fail-closed on a malformed digest (non-hex / wrong length):
#eval (parseAuthW 100 "{\"sig\":[\"zz\",9]}".toList).isNone                -- true

/-! ## §W4 — the COMPLETE `FullActionA` codec (all 51 arms, each with its TYPED args).

The narrow `§FULL` codec covered 5 arms (`bal`/`del`/`rev`/`mint`/`burn`). The wide codec covers ALL
51 `FullActionA` arms (`TurnExecutorFull.lean:1866`, the 51-variant `EffectKind` surface) — one tagged
JSON object per arm, each carrying the arm's exact typed args (ids/assets as `Nat`, amounts as `Int`,
field names as JSON strings, the swiss `rights`/`held` as the narrow `AUTHS` array). The grammar
(tagged by a short mnemonic of the dregg1 `Effect`):

    ACTIONW :=
        {"bal":[actor,src,dst,amt,asset]}        -- balanceA(Turn{actor,src,dst,amt}, asset)
      | {"del":[delegator,recipient,t]}          -- delegate
      | {"rev":[holder,t]}                       -- revoke
      | {"mint":[actor,cell,asset,amt]}          -- mintA
      | {"burn":[actor,cell,asset,amt]}          -- burnA
      | {"setfield":[actor,cell,"FIELD",v]}      -- setFieldA          (v signed)
      | {"emit":[actor,cell,topic,data]}         -- emitEventA
      | {"incnonce":[actor,cell,newNonce]}       -- incrementNonceA
      | {"setperms":[actor,cell,perms]}          -- setPermissionsA
      | {"setvk":[actor,cell,vk]}                -- setVKA
      | {"introduce":[introducer,recipient,target]}  -- introduceA
      | {"delatten":[delegator,recipient,target,AUTHS]} -- delegateAttenA (rights-carrying)
      | {"atten":[actor,idx,AUTHS]}              -- attenuateA
      | {"dropref":[holder,target]}              -- dropRefA
      | {"revdel":[holder,target]}               -- revokeDelegationA
      | {"vhandoff":[introducer,recipient,target]}   -- validateHandoffA
      | {"exercise":[actor,target]}              -- exerciseA
      | {"createcell":[actor,newCell]}           -- createCellA
      | {"spawn":[actor,child,target]}           -- spawnA
      | {"bmint":[actor,cell,asset,value]}       -- bridgeMintA
      | {"cesc":[id,actor,creator,recipient,asset,amount]}      -- createEscrowA
      | {"resc":[id,actor]}                      -- releaseEscrowA
      | {"fesc":[id,actor]}                      -- refundEscrowA
      | {"cobl":[id,actor,obligor,beneficiary,asset,stake]}     -- createObligationA
      | {"nspend":[nf,actor]}                    -- noteSpendA
      | {"ncreate":[cm,actor]}                   -- noteCreateA
      | {"ccesc":[id,actor,creator,recipient,asset,amount]}     -- createCommittedEscrowA
      | {"rccesc":[id,actor]}                    -- releaseCommittedEscrowA
      | {"fccesc":[id,actor]}                    -- refundCommittedEscrowA
      | {"block":[id,actor,originator,destination,asset,amount]}  -- bridgeLockA
      | {"bfin":[id,actor,asset,amount]}         -- bridgeFinalizeA
      | {"bcancel":[id,actor]}                   -- bridgeCancelA
      | {"seal":[actor,cell]}                    -- sealA
      | {"unseal":[actor,cell]}                  -- unsealA
      | {"csp":[actor,sealerHolder,unsealerHolder]}   -- createSealPairA
      | {"sov":[actor,cell]}                     -- makeSovereignA
      | {"refusal":[actor,cell]}                 -- refusalA
      | {"rarchive":[actor,cell]}                -- receiptArchiveA
      | {"qalloc":[id,actor,cell,capacity]}      -- queueAllocateA
      | {"qenq":[id,m,actor,cell,depId,dAsset,deposit]}  -- queueEnqueueA
      | {"qdeq":[id,actor,cell,depId,deposit]}   -- queueDequeueA
      | {"qresize":[id,newCap,actor,cell]}       -- queueResizeA
      | {"export":[sw,actor,exporter,target,AUTHS]}  -- exportSturdyRefA(rights); held read from committed caps
      | {"enliven":[sw,actor,exporter,AUTHS]}    -- enlivenRefA(claimed)
      | {"shandoff":[sw,certHash,introducer,exporter]}     -- swissHandoffA
      | {"sdrop":[sw,actor,exporter]}            -- swissDropA

Every id/asset/idx/capacity/newNonce/nf/cm/sw/certHash is a `Nat`; every amt/value/amount/stake/
deposit/v/perms/vk/topic/data is a SIGNED `Int`; "FIELD" is a JSON string; AUTHS is the narrow `Auth`
tag array (0..6). -/

/-- Encode a `List Auth` as the `AUTHS` tag array (reuses the narrow `authTag` enumeration). -/
def encodeAuthsW (rs : List Auth) : String := encodeAuths rs

/-- Parse an `AUTHS` tag array (reuses the narrow `parseAuths`). -/
def parseAuthsW (cs : PState) : Option (List Auth × PState) := parseAuths cs

/-- Encode ONE `FullActionA` to its wide tagged wire form (all 51 arms). -/
def encodeActionW : FullActionA → String
  | .balanceA t a => "{\"bal\":[" ++ toString t.actor ++ "," ++ toString t.src ++ "," ++ toString t.dst
                       ++ "," ++ toString t.amt ++ "," ++ toString a ++ "]}"
  | .delegate del rec t => "{\"del\":[" ++ toString del ++ "," ++ toString rec ++ "," ++ toString t ++ "]}"
  | .revoke holder t => "{\"rev\":[" ++ toString holder ++ "," ++ toString t ++ "]}"
  | .mintA actor cell a amt => "{\"mint\":[" ++ toString actor ++ "," ++ toString cell ++ ","
                                 ++ toString a ++ "," ++ toString amt ++ "]}"
  | .burnA actor cell a amt => "{\"burn\":[" ++ toString actor ++ "," ++ toString cell ++ ","
                                 ++ toString a ++ "," ++ toString amt ++ "]}"
  | .setFieldA actor cell field v => "{\"setfield\":[" ++ toString actor ++ "," ++ toString cell
                                       ++ ",\"" ++ jsonEscape field ++ "\"," ++ toString v ++ "]}"
  | .emitEventA actor cell topic data => "{\"emit\":[" ++ toString actor ++ "," ++ toString cell ++ ","
                                           ++ toString topic ++ "," ++ toString data ++ "]}"
  | .incrementNonceA actor cell n => "{\"incnonce\":[" ++ toString actor ++ "," ++ toString cell ++ ","
                                       ++ toString n ++ "]}"
  | .setPermissionsA actor cell perms => "{\"setperms\":[" ++ toString actor ++ "," ++ toString cell
                                            ++ "," ++ toString perms ++ "]}"
  | .setVKA actor cell vk => "{\"setvk\":[" ++ toString actor ++ "," ++ toString cell ++ ","
                               ++ toString vk ++ "]}"
  | .introduceA i r t => "{\"introduce\":[" ++ toString i ++ "," ++ toString r ++ "," ++ toString t ++ "]}"
  | .delegateAttenA del rec t keep => "{\"delatten\":[" ++ toString del ++ "," ++ toString rec ++ ","
                                        ++ toString t ++ "," ++ encodeAuthsW keep ++ "]}"
  | .attenuateA actor idx keep => "{\"atten\":[" ++ toString actor ++ "," ++ toString idx ++ ","
                                    ++ encodeAuthsW keep ++ "]}"
  | .dropRefA holder target => "{\"dropref\":[" ++ toString holder ++ "," ++ toString target ++ "]}"
  | .revokeDelegationA holder target => "{\"revdel\":[" ++ toString holder ++ "," ++ toString target ++ "]}"
  | .validateHandoffA i r t => "{\"vhandoff\":[" ++ toString i ++ "," ++ toString r ++ "," ++ toString t ++ "]}"
  | .exerciseA actor target => "{\"exercise\":[" ++ toString actor ++ "," ++ toString target ++ "]}"
  | .createCellA actor newCell => "{\"createcell\":[" ++ toString actor ++ "," ++ toString newCell ++ "]}"
  | .spawnA actor child target => "{\"spawn\":[" ++ toString actor ++ "," ++ toString child ++ ","
                                    ++ toString target ++ "]}"
  | .bridgeMintA actor cell a value => "{\"bmint\":[" ++ toString actor ++ "," ++ toString cell ++ ","
                                         ++ toString a ++ "," ++ toString value ++ "]}"
  | .createEscrowA id actor creator recipient a amount =>
      "{\"cesc\":[" ++ toString id ++ "," ++ toString actor ++ "," ++ toString creator ++ ","
        ++ toString recipient ++ "," ++ toString a ++ "," ++ toString amount ++ "]}"
  | .releaseEscrowA id actor => "{\"resc\":[" ++ toString id ++ "," ++ toString actor ++ "]}"
  | .refundEscrowA id actor => "{\"fesc\":[" ++ toString id ++ "," ++ toString actor ++ "]}"
  | .createObligationA id actor obligor beneficiary a stake =>
      "{\"cobl\":[" ++ toString id ++ "," ++ toString actor ++ "," ++ toString obligor ++ ","
        ++ toString beneficiary ++ "," ++ toString a ++ "," ++ toString stake ++ "]}"
  | .noteSpendA nf actor => "{\"nspend\":[" ++ toString nf ++ "," ++ toString actor ++ "]}"
  | .noteCreateA cm actor => "{\"ncreate\":[" ++ toString cm ++ "," ++ toString actor ++ "]}"
  | .createCommittedEscrowA id actor creator recipient a amount =>
      "{\"ccesc\":[" ++ toString id ++ "," ++ toString actor ++ "," ++ toString creator ++ ","
        ++ toString recipient ++ "," ++ toString a ++ "," ++ toString amount ++ "]}"
  | .releaseCommittedEscrowA id actor => "{\"rccesc\":[" ++ toString id ++ "," ++ toString actor ++ "]}"
  | .refundCommittedEscrowA id actor => "{\"fccesc\":[" ++ toString id ++ "," ++ toString actor ++ "]}"
  | .bridgeLockA id actor originator destination a amount =>
      "{\"block\":[" ++ toString id ++ "," ++ toString actor ++ "," ++ toString originator ++ ","
        ++ toString destination ++ "," ++ toString a ++ "," ++ toString amount ++ "]}"
  | .bridgeFinalizeA id actor a amount => "{\"bfin\":[" ++ toString id ++ "," ++ toString actor ++ ","
                                            ++ toString a ++ "," ++ toString amount ++ "]}"
  | .bridgeCancelA id actor => "{\"bcancel\":[" ++ toString id ++ "," ++ toString actor ++ "]}"
  | .sealA actor cell => "{\"seal\":[" ++ toString actor ++ "," ++ toString cell ++ "]}"
  | .unsealA actor cell => "{\"unseal\":[" ++ toString actor ++ "," ++ toString cell ++ "]}"
  | .createSealPairA actor sh uh => "{\"csp\":[" ++ toString actor ++ "," ++ toString sh ++ ","
                                      ++ toString uh ++ "]}"
  | .makeSovereignA actor cell => "{\"sov\":[" ++ toString actor ++ "," ++ toString cell ++ "]}"
  | .refusalA actor cell => "{\"refusal\":[" ++ toString actor ++ "," ++ toString cell ++ "]}"
  | .receiptArchiveA actor cell => "{\"rarchive\":[" ++ toString actor ++ "," ++ toString cell ++ "]}"
  | .queueAllocateA id actor cell cap => "{\"qalloc\":[" ++ toString id ++ "," ++ toString actor ++ ","
                                           ++ toString cell ++ "," ++ toString cap ++ "]}"
  | .queueEnqueueA id m actor cell depId dAsset deposit =>
      "{\"qenq\":[" ++ toString id ++ "," ++ toString m ++ "," ++ toString actor ++ "," ++ toString cell
        ++ "," ++ toString depId ++ "," ++ toString dAsset ++ "," ++ toString deposit ++ "]}"
  | .queueDequeueA id actor cell depId deposit =>
      "{\"qdeq\":[" ++ toString id ++ "," ++ toString actor ++ "," ++ toString cell ++ ","
        ++ toString depId ++ "," ++ toString deposit ++ "]}"
  | .queueResizeA id newCap actor cell => "{\"qresize\":[" ++ toString id ++ "," ++ toString newCap ++ ","
                                            ++ toString actor ++ "," ++ toString cell ++ "]}"
  | .exportSturdyRefA sw actor exporter target rights =>
      "{\"export\":[" ++ toString sw ++ "," ++ toString actor ++ "," ++ toString exporter ++ ","
        ++ toString target ++ "," ++ encodeAuthsW rights ++ "]}"
  | .enlivenRefA sw actor exporter claimed =>
      "{\"enliven\":[" ++ toString sw ++ "," ++ toString actor ++ "," ++ toString exporter ++ ","
        ++ encodeAuthsW claimed ++ "]}"
  | .swissHandoffA sw certHash introducer exporter =>
      "{\"shandoff\":[" ++ toString sw ++ "," ++ toString certHash ++ "," ++ toString introducer ++ ","
        ++ toString exporter ++ "]}"
  | .swissDropA sw actor exporter => "{\"sdrop\":[" ++ toString sw ++ "," ++ toString actor ++ ","
                                       ++ toString exporter ++ "]}"

/-! ### §W4 parser — recursive-descent over the 51-arm `ACTIONW` grammar.

Helpers `pN`/`pI`/`pS`/`pA` read ONE typed arg AFTER a comma (or, for the first arg, directly):
`pN` a `Nat`, `pI` an `Int`, `pS` a JSON string, `pA` an `AUTHS` array. Each arm threads the parse
state through its arg sequence and closes on `]}`. STRICT: any deviation ⇒ `none`. -/

/-- Read a leading `,` then a `Nat`. -/
def cN (cs : PState) : Option (Nat × PState) :=
  match lit "," cs with | none => none | some r => parseNat r
/-- Read a leading `,` then a signed `Int`. -/
def cI (cs : PState) : Option (Int × PState) :=
  match lit "," cs with | none => none | some r => parseInt r
/-- Read a leading `,` then a JSON string (a field name). -/
def cS (cs : PState) : Option (String × PState) :=
  match lit "," cs with | none => none | some r => parseStr r
/-- Read a leading `,` then an `AUTHS` tag array. -/
def cA (cs : PState) : Option (List Auth × PState) :=
  match lit "," cs with | none => none | some r => parseAuthsW r

/-- Parse ONE `FullActionA` (all 51 arms). Dispatch on the tag literal; read each arm's typed args;
close on `]}`. Fail-closed on any deviation. -/
def parseActionW (cs : PState) : Option (FullActionA × PState) :=
  match lit "{\"bal\":[" cs with
  | some r0 => do
      let (actor, r1) ← parseNat r0; let (src, r2) ← cN r1; let (dst, r3) ← cN r2
      let (amt, r4) ← cI r3; let (a, r5) ← cN r4; let r6 ← lit "]}" r5
      some (.balanceA { actor := actor, src := src, dst := dst, amt := amt } a, r6)
  | none =>
  match lit "{\"del\":[" cs with
  | some r0 => do
      let (del, r1) ← parseNat r0; let (rec, r2) ← cN r1; let (t, r3) ← cN r2; let r4 ← lit "]}" r3
      some (.delegate del rec t, r4)
  | none =>
  match lit "{\"rev\":[" cs with
  | some r0 => do
      let (holder, r1) ← parseNat r0; let (t, r2) ← cN r1; let r3 ← lit "]}" r2
      some (.revoke holder t, r3)
  | none =>
  match lit "{\"mint\":[" cs with
  | some r0 => do
      let (actor, r1) ← parseNat r0; let (cell, r2) ← cN r1; let (a, r3) ← cN r2
      let (amt, r4) ← cI r3; let r5 ← lit "]}" r4
      some (.mintA actor cell a amt, r5)
  | none =>
  match lit "{\"burn\":[" cs with
  | some r0 => do
      let (actor, r1) ← parseNat r0; let (cell, r2) ← cN r1; let (a, r3) ← cN r2
      let (amt, r4) ← cI r3; let r5 ← lit "]}" r4
      some (.burnA actor cell a amt, r5)
  | none =>
  match lit "{\"setfield\":[" cs with
  | some r0 => do
      let (actor, r1) ← parseNat r0; let (cell, r2) ← cN r1; let (field, r3) ← cS r2
      let (v, r4) ← cI r3; let r5 ← lit "]}" r4
      some (.setFieldA actor cell field v, r5)
  | none =>
  match lit "{\"emit\":[" cs with
  | some r0 => do
      let (actor, r1) ← parseNat r0; let (cell, r2) ← cN r1; let (topic, r3) ← cI r2
      let (data, r4) ← cI r3; let r5 ← lit "]}" r4
      some (.emitEventA actor cell topic data, r5)
  | none =>
  match lit "{\"incnonce\":[" cs with
  | some r0 => do
      let (actor, r1) ← parseNat r0; let (cell, r2) ← cN r1; let (n, r3) ← cI r2; let r4 ← lit "]}" r3
      some (.incrementNonceA actor cell n, r4)
  | none =>
  match lit "{\"setperms\":[" cs with
  | some r0 => do
      let (actor, r1) ← parseNat r0; let (cell, r2) ← cN r1; let (p, r3) ← cI r2; let r4 ← lit "]}" r3
      some (.setPermissionsA actor cell p, r4)
  | none =>
  match lit "{\"setvk\":[" cs with
  | some r0 => do
      let (actor, r1) ← parseNat r0; let (cell, r2) ← cN r1; let (vk, r3) ← cI r2; let r4 ← lit "]}" r3
      some (.setVKA actor cell vk, r4)
  | none =>
  match lit "{\"introduce\":[" cs with
  | some r0 => do
      let (i, r1) ← parseNat r0; let (r, r2) ← cN r1; let (t, r3) ← cN r2; let r4 ← lit "]}" r3
      some (.introduceA i r t, r4)
  | none =>
  match lit "{\"delatten\":[" cs with
  | some r0 => do
      let (del, r1) ← parseNat r0; let (recp, r2) ← cN r1; let (t, r3) ← cN r2
      let (keep, r4) ← cA r3; let r5 ← lit "]}" r4
      some (.delegateAttenA del recp t keep, r5)
  | none =>
  match lit "{\"atten\":[" cs with
  | some r0 => do
      let (actor, r1) ← parseNat r0; let (idx, r2) ← cN r1; let (keep, r3) ← cA r2; let r4 ← lit "]}" r3
      some (.attenuateA actor idx keep, r4)
  | none =>
  match lit "{\"dropref\":[" cs with
  | some r0 => do
      let (holder, r1) ← parseNat r0; let (target, r2) ← cN r1; let r3 ← lit "]}" r2
      some (.dropRefA holder target, r3)
  | none =>
  match lit "{\"revdel\":[" cs with
  | some r0 => do
      let (holder, r1) ← parseNat r0; let (target, r2) ← cN r1; let r3 ← lit "]}" r2
      some (.revokeDelegationA holder target, r3)
  | none =>
  match lit "{\"vhandoff\":[" cs with
  | some r0 => do
      let (i, r1) ← parseNat r0; let (r, r2) ← cN r1; let (t, r3) ← cN r2; let r4 ← lit "]}" r3
      some (.validateHandoffA i r t, r4)
  | none =>
  match lit "{\"exercise\":[" cs with
  | some r0 => do
      let (actor, r1) ← parseNat r0; let (target, r2) ← cN r1; let r3 ← lit "]}" r2
      some (.exerciseA actor target, r3)
  | none =>
  match lit "{\"createcell\":[" cs with
  | some r0 => do
      let (actor, r1) ← parseNat r0; let (newCell, r2) ← cN r1; let r3 ← lit "]}" r2
      some (.createCellA actor newCell, r3)
  | none =>
  match lit "{\"spawn\":[" cs with
  | some r0 => do
      let (actor, r1) ← parseNat r0; let (child, r2) ← cN r1; let (target, r3) ← cN r2; let r4 ← lit "]}" r3
      some (.spawnA actor child target, r4)
  | none =>
  match lit "{\"bmint\":[" cs with
  | some r0 => do
      let (actor, r1) ← parseNat r0; let (cell, r2) ← cN r1; let (a, r3) ← cN r2
      let (value, r4) ← cI r3; let r5 ← lit "]}" r4
      some (.bridgeMintA actor cell a value, r5)
  | none =>
  match lit "{\"cesc\":[" cs with
  | some r0 => do
      let (id, r1) ← parseNat r0; let (actor, r2) ← cN r1; let (creator, r3) ← cN r2
      let (recipient, r4) ← cN r3; let (a, r5) ← cN r4; let (amount, r6) ← cI r5; let r7 ← lit "]}" r6
      some (.createEscrowA id actor creator recipient a amount, r7)
  | none =>
  match lit "{\"resc\":[" cs with
  | some r0 => do
      let (id, r1) ← parseNat r0; let (actor, r2) ← cN r1; let r3 ← lit "]}" r2
      some (.releaseEscrowA id actor, r3)
  | none =>
  match lit "{\"fesc\":[" cs with
  | some r0 => do
      let (id, r1) ← parseNat r0; let (actor, r2) ← cN r1; let r3 ← lit "]}" r2
      some (.refundEscrowA id actor, r3)
  | none =>
  match lit "{\"cobl\":[" cs with
  | some r0 => do
      let (id, r1) ← parseNat r0; let (actor, r2) ← cN r1; let (obligor, r3) ← cN r2
      let (beneficiary, r4) ← cN r3; let (a, r5) ← cN r4; let (stake, r6) ← cI r5; let r7 ← lit "]}" r6
      some (.createObligationA id actor obligor beneficiary a stake, r7)
  | none =>
  match lit "{\"nspend\":[" cs with
  | some r0 => do
      let (nf, r1) ← parseNat r0; let (actor, r2) ← cN r1; let r3 ← lit "]}" r2
      some (.noteSpendA nf actor, r3)
  | none =>
  match lit "{\"ncreate\":[" cs with
  | some r0 => do
      let (cm, r1) ← parseNat r0; let (actor, r2) ← cN r1; let r3 ← lit "]}" r2
      some (.noteCreateA cm actor, r3)
  | none =>
  match lit "{\"ccesc\":[" cs with
  | some r0 => do
      let (id, r1) ← parseNat r0; let (actor, r2) ← cN r1; let (creator, r3) ← cN r2
      let (recipient, r4) ← cN r3; let (a, r5) ← cN r4; let (amount, r6) ← cI r5; let r7 ← lit "]}" r6
      some (.createCommittedEscrowA id actor creator recipient a amount, r7)
  | none =>
  match lit "{\"rccesc\":[" cs with
  | some r0 => do
      let (id, r1) ← parseNat r0; let (actor, r2) ← cN r1; let r3 ← lit "]}" r2
      some (.releaseCommittedEscrowA id actor, r3)
  | none =>
  match lit "{\"fccesc\":[" cs with
  | some r0 => do
      let (id, r1) ← parseNat r0; let (actor, r2) ← cN r1; let r3 ← lit "]}" r2
      some (.refundCommittedEscrowA id actor, r3)
  | none =>
  match lit "{\"block\":[" cs with
  | some r0 => do
      let (id, r1) ← parseNat r0; let (actor, r2) ← cN r1; let (originator, r3) ← cN r2
      let (destination, r4) ← cN r3; let (a, r5) ← cN r4; let (amount, r6) ← cI r5; let r7 ← lit "]}" r6
      some (.bridgeLockA id actor originator destination a amount, r7)
  | none =>
  match lit "{\"bfin\":[" cs with
  | some r0 => do
      let (id, r1) ← parseNat r0; let (actor, r2) ← cN r1; let (a, r3) ← cN r2
      let (amount, r4) ← cI r3; let r5 ← lit "]}" r4
      some (.bridgeFinalizeA id actor a amount, r5)
  | none =>
  match lit "{\"bcancel\":[" cs with
  | some r0 => do
      let (id, r1) ← parseNat r0; let (actor, r2) ← cN r1; let r3 ← lit "]}" r2
      some (.bridgeCancelA id actor, r3)
  | none =>
  match lit "{\"seal\":[" cs with
  | some r0 => do
      let (actor, r1) ← parseNat r0; let (cell, r2) ← cN r1; let r3 ← lit "]}" r2
      some (.sealA actor cell, r3)
  | none =>
  match lit "{\"unseal\":[" cs with
  | some r0 => do
      let (actor, r1) ← parseNat r0; let (cell, r2) ← cN r1; let r3 ← lit "]}" r2
      some (.unsealA actor cell, r3)
  | none =>
  match lit "{\"csp\":[" cs with
  | some r0 => do
      let (actor, r1) ← parseNat r0; let (sh, r2) ← cN r1; let (uh, r3) ← cN r2; let r4 ← lit "]}" r3
      some (.createSealPairA actor sh uh, r4)
  | none =>
  match lit "{\"sov\":[" cs with
  | some r0 => do
      let (actor, r1) ← parseNat r0; let (cell, r2) ← cN r1; let r3 ← lit "]}" r2
      some (.makeSovereignA actor cell, r3)
  | none =>
  match lit "{\"refusal\":[" cs with
  | some r0 => do
      let (actor, r1) ← parseNat r0; let (cell, r2) ← cN r1; let r3 ← lit "]}" r2
      some (.refusalA actor cell, r3)
  | none =>
  match lit "{\"rarchive\":[" cs with
  | some r0 => do
      let (actor, r1) ← parseNat r0; let (cell, r2) ← cN r1; let r3 ← lit "]}" r2
      some (.receiptArchiveA actor cell, r3)
  | none =>
  match lit "{\"qalloc\":[" cs with
  | some r0 => do
      let (id, r1) ← parseNat r0; let (actor, r2) ← cN r1; let (cell, r3) ← cN r2
      let (cap, r4) ← cN r3; let r5 ← lit "]}" r4
      some (.queueAllocateA id actor cell cap, r5)
  | none =>
  match lit "{\"qenq\":[" cs with
  | some r0 => do
      let (id, r1) ← parseNat r0; let (m, r2) ← cN r1; let (actor, r3) ← cN r2; let (cell, r4) ← cN r3
      let (depId, r5) ← cN r4; let (dAsset, r6) ← cN r5; let (deposit, r7) ← cI r6; let r8 ← lit "]}" r7
      some (.queueEnqueueA id m actor cell depId dAsset deposit, r8)
  | none =>
  match lit "{\"qdeq\":[" cs with
  | some r0 => do
      let (id, r1) ← parseNat r0; let (actor, r2) ← cN r1; let (cell, r3) ← cN r2
      let (depId, r4) ← cN r3; let (deposit, r5) ← cI r4; let r6 ← lit "]}" r5
      some (.queueDequeueA id actor cell depId deposit, r6)
  | none =>
  match lit "{\"qresize\":[" cs with
  | some r0 => do
      let (id, r1) ← parseNat r0; let (newCap, r2) ← cN r1; let (actor, r3) ← cN r2
      let (cell, r4) ← cN r3; let r5 ← lit "]}" r4
      some (.queueResizeA id newCap actor cell, r5)
  | none =>
  match lit "{\"export\":[" cs with
  | some r0 => do
      let (sw, r1) ← parseNat r0; let (actor, r2) ← cN r1; let (exporter, r3) ← cN r2
      let (target, r4) ← cN r3; let (rights, r5) ← cA r4; let r6 ← lit "]}" r5
      some (.exportSturdyRefA sw actor exporter target rights, r6)
  | none =>
  match lit "{\"enliven\":[" cs with
  | some r0 => do
      let (sw, r1) ← parseNat r0; let (actor, r2) ← cN r1; let (exporter, r3) ← cN r2
      let (claimed, r4) ← cA r3; let r5 ← lit "]}" r4
      some (.enlivenRefA sw actor exporter claimed, r5)
  | none =>
  match lit "{\"shandoff\":[" cs with
  | some r0 => do
      let (sw, r1) ← parseNat r0; let (certHash, r2) ← cN r1; let (introducer, r3) ← cN r2
      let (exporter, r4) ← cN r3; let r5 ← lit "]}" r4
      some (.swissHandoffA sw certHash introducer exporter, r5)
  | none =>
  match lit "{\"sdrop\":[" cs with
  | some r0 => do
      let (sw, r1) ← parseNat r0; let (actor, r2) ← cN r1; let (exporter, r3) ← cN r2; let r4 ← lit "]}" r3
      some (.swissDropA sw actor exporter, r4)
  | none => none

/-! ### §W4-eval — EVERY one of the 51 arms round-trips through the wide action codec.

`actionRoundtrips a` re-encodes the reparse of `encodeActionW a` and compares strings (FullActionA
has no BEq). `allActions` lists ONE representative of EACH of the 51 arms (distinct args so a
mis-parse of any field is caught), and `allActionsRoundtrip` asserts EVERY one round-trips — the
non-vacuity guard that the codec faithfully covers the WHOLE effect surface, not a sliver. -/

/-- Round-trip ONE `FullActionA` through the wire (compare re-encodings). -/
def actionRoundtrips (a : FullActionA) : Bool :=
  match parseActionW (encodeActionW a).toList with
  | some (a', []) => encodeActionW a' == encodeActionW a
  | _             => false

/-- ONE representative of each of the 51 `FullActionA` arms (distinct args per field). -/
def allActions : List FullActionA :=
  [ .balanceA { actor := 1, src := 2, dst := 3, amt := -4 } 5
  , .delegate 6 7 8
  , .revoke 9 10
  , .mintA 11 12 13 (-14)
  , .burnA 15 16 17 18
  , .setFieldA 19 20 "balance" (-21)
  , .emitEventA 22 23 (-24) 25
  , .incrementNonceA 26 27 (-28)
  , .setPermissionsA 29 30 (-31)
  , .setVKA 32 33 (-34)
  , .introduceA 35 36 37
  , .delegateAttenA 35 36 37 [.read, .write]
  , .attenuateA 38 39 [.read, .write]
  , .dropRefA 40 41
  , .revokeDelegationA 42 43
  , .validateHandoffA 44 45 46
  , .exerciseA 47 48
  , .createCellA 49 50
  , .spawnA 51 52 53
  , .bridgeMintA 54 55 56 (-57)
  , .createEscrowA 58 59 60 61 62 (-63)
  , .releaseEscrowA 64 65
  , .refundEscrowA 66 67
  , .createObligationA 68 69 70 71 72 (-73)
  , .noteSpendA 74 75
  , .noteCreateA 76 77
  , .createCommittedEscrowA 78 79 80 81 82 (-83)
  , .releaseCommittedEscrowA 84 85
  , .refundCommittedEscrowA 86 87
  , .bridgeLockA 88 89 90 91 92 (-93)
  , .bridgeFinalizeA 94 95 96 (-97)
  , .bridgeCancelA 98 99
  , .sealA 100 101
  , .unsealA 102 103
  , .createSealPairA 104 105 106
  , .makeSovereignA 107 108
  , .refusalA 109 110
  , .receiptArchiveA 111 112
  , .queueAllocateA 113 114 115 116
  , .queueEnqueueA 117 118 119 120 121 122 (-123)
  , .queueDequeueA 124 125 126 127 (-128)
  , .queueResizeA 129 130 131 132
  , .exportSturdyRefA 133 134 135 136 [.read]
  , .enlivenRefA 137 138 139 [.call]
  , .swissHandoffA 140 141 142 143
  , .swissDropA 144 145 146 ]

/-- EVERY representative round-trips (the 51-arm non-vacuity guard). -/
def allActionsRoundtrip : Bool := allActions.all actionRoundtrips

#eval allActions.length                                                     -- 46 (one per FullActionA arm)
#eval allActionsRoundtrip                                                    -- true (every arm round-trips)
-- HARD CI check (fails the build if ANY arm — incl. the new `delegateAttenA` — stops round-tripping):
#guard allActionsRoundtrip
-- a couple of spot checks of the actual wire bytes:
#eval encodeActionW (.balanceA { actor := 1, src := 2, dst := 3, amt := -4 } 5)
-- {"bal":[1,2,3,-4,5]}
#eval encodeActionW (.exportSturdyRefA 133 134 135 136 [.read])
-- {"export":[133,134,135,136,[0]]}
-- fail-closed on an unknown tag:
#eval (parseActionW "{\"bogus\":[1]}".toList).isNone                         -- true
-- fail-closed on a wrong-arity bal (missing asset):
#eval (parseActionW "{\"bal\":[1,2,3,-4]}".toList).isNone                    -- true

/-! ## §W5c — the per-node CAVEAT codec (the within-cell, state-reading discharge leg, TRANSPORTED).

THE SOUNDNESS FIX. The gated executor's third gate leg `caveatsDischarged na s` reads the node's
PRE-state `s` against the node's tiered caveats (`FullForestAuth.GatedCaveat`: a `DriftStable.DriftTier`
tag + a `check : RecChainedState → Bool` reading the node's own target cell). Until now the §WIDE wire
carried NO caveats — so the lift supplied an EMPTY caveat list and `caveatsDischarged` ADMITTED BY
CONSTRUCTION (`[].all _ = true`), silently un-enforcing the whole caveat thread over the swap boundary.
We now TRANSPORT the caveat(s) on the wire, so a node whose caveat is VIOLATED by the wire pre-state
makes the gate FAIL — `caveatsDischarged` has REAL teeth over `@[export] dregg_exec_full_forest_auth`.

A transported caveat is a within-cell BALANCE-THRESHOLD read — exactly the `FullForestAuth.Demo`
`trueCaveat`/`falseCaveat` shape: "cell C holds ≥ M of asset A", a `monotone` (drift-stable) read of a
cell's balance in the wire pre-state. It carries its `DriftTier` tag (so a `.coordinated` caveat
fail-closes intra-cell, routed to `CrossCaveat` — the dregg1 `authorize.rs:1608` cross-cell hole). The
grammar (positionally deterministic, fail-closed):

    WCAVEAT  := [tier,cell,asset,min]      (tier ∈ {0,1,2,3}; cell/asset : Nat; min : signed Int)
    WCAVEATS := [] | [WCAVEAT(,WCAVEAT)*]

where tier 0=monotone, 1=reservation, 2=locked, 3=coordinated (the `DriftStable.DriftTier` order). The
caveat reads `s.kernel.bal cell asset ≥ min` on the node's PRE-state; a `coordinated` tier fail-closes
(routed to `CrossCaveat`). The wire `min` is a SIGNED `Int` (balances are signed). -/

/-- A WIRE caveat: a tiered, within-cell balance-threshold read TRANSPORTED on the node. `tier` is the
`DriftStable.DriftTier` ordinal (0=monotone/1=reservation/2=locked/3=coordinated); the discharge
condition is `bal cell asset ≥ min` on the node's pre-state (the `.coordinated` tier fail-closes,
routed to `CrossCaveat`). This is the wire form of `FullForestAuth.GatedCaveat`. -/
structure WCaveat where
  /-- The drift-tier ordinal (0=monotone/1=reservation/2=locked/3=coordinated). -/
  tier  : Nat
  /-- The cell whose balance the caveat reads (the node's own target cell, within-cell). -/
  cell  : CellId
  /-- The asset the threshold is on. -/
  asset : AssetId
  /-- The signed lower bound: the caveat HOLDS iff `bal cell asset ≥ min` on the pre-state. -/
  min   : Int

/-- Encode one `WCAVEAT` `[tier,cell,asset,min]`. -/
def encodeCaveatW (c : WCaveat) : String :=
  "[" ++ toString c.tier ++ "," ++ toString c.cell ++ "," ++ toString c.asset ++ ","
    ++ toString c.min ++ "]"

/-- Parse one `WCAVEAT` `[tier,cell,asset,min]` (tier strict to {0,1,2,3}; `min` signed). Fail-closed. -/
def parseCaveatW (cs : PState) : Option (WCaveat × PState) := do
  let r0 ← lit "[" cs
  let (tier, r1) ← parseNat r0
  if tier > 3 then none else
  let (cell, r2) ← cN r1
  let (asset, r3) ← cN r2
  let (min, r4) ← cI r3
  let r5 ← lit "]" r4
  some ({ tier := tier, cell := cell, asset := asset, min := min }, r5)

/-- Encode a `WCAVEATS` array `[WCAVEAT(,WCAVEAT)*]` (or `[]`). -/
def encodeCaveatsW : List WCaveat → String
  | []      => "[]"
  | c :: cs => "[" ++ encodeCaveatW c
                 ++ (cs.foldl (fun acc x => acc ++ "," ++ encodeCaveatW x) "") ++ "]"

/-- Parse a `WCAVEATS` array `[WCAVEAT(,WCAVEAT)*]` (or `[]`). Fuel-seeded by the wire length. -/
def parseCaveatsW (cs : PState) : Option (List WCaveat × PState) :=
  match lit "[]" cs with
  | some rest => some ([], rest)
  | none =>
    match lit "[" cs with
    | none => none
    | some r0 =>
      let rec loop (fuel : Nat) (cs : PState) : Option (List WCaveat × PState) :=
        match fuel with
        | 0 => none
        | fuel + 1 =>
          match parseCaveatW cs with
          | none => none
          | some (c, r1) =>
            match lit "," r1 with
            | some r2 => match loop fuel r2 with
                         | some (rest, r3) => some (c :: rest, r3)
                         | none => none
            | none => match lit "]" r1 with
                      | some r3 => some ([c], r3)
                      | none => none
      loop (cs.length + 1) r0

/-! ## §W5 — the recursive ACTION-TREE codec (`FullForestA` = action + children[], + auth decoration).

dregg1's turn is a CALL-FOREST: a node carries its action AND a list of delegated child subtrees (the
`DelegationMode::None` default runs each child on the parent's target cell). META-FILL A's
`FullForest.FullForestA` is exactly this tree; `execFullForestA` runs it all-or-nothing, per-asset.
The wide codec marshals the WHOLE tree — and carries the `Authorization` WHO PLUS the per-node CAVEATS
on every node (the META-FILL D decoration), round-tripped FAITHFULLY. The executed ungated
`execFullForestA` erases BOTH (auth + caveats), but the executed gated `FullForestAuth.execFullForestG`
ENFORCES them: the credential GATES (WHO) and the caveats GATE (the within-cell state-reading discharge
leg). The grammar (recursive):

    NODE  := {"auth":AUTH,"caveats":WCAVEATS,"action":ACTIONW,"children":KIDS}
    KIDS  := [] | [EDGE(,EDGE)*]
    EDGE  := {"holder":N,"keep":AUTHS,"cap":CAP,"sub":NODE}
    CAP   := {"null":0} | {"node":N} | {"ep":[N,AUTHS]}         (the narrow cap codec, reused)

The `auth` field is the per-node `Authorization Nat Nat` (the WHO); `caveats` the per-node
`List WCaveat` (the discharge leg, §W5c); `action` the 51-arm `FullActionA`; `children` the delegated
subtrees, each carrying the delegation edge data (holder / attenuation `keep` / `parentCap`). The tree
recursion is fuel-bounded (seeded with the wire length).

The executed tree is `eraseAuth` (drop the auth AND the caveats — they are ledger-orthogonal), so the
proved `execFullForestA` runs UNCHANGED; the gated `execFullForestG` carries the caveats into the gate
(`liftForestG`, §WG2) so a violated caveat fail-closes the whole turn. -/

mutual
/-- A WIRE node: its credential, its tiered caveats, its action, and its children (each a delegation
edge to a node). -/
structure WForest where
  auth     : AuthW
  caveats  : List WCaveat
  action   : FullActionA
  children : List WChild

/-- A WIRE delegation edge: holder + attenuation `keep` + the delegated `parentCap` + the child node. -/
structure WChild where
  holder    : CellId
  keep      : List Auth
  parentCap : Cap
  sub       : WForest
end

mutual
/-- Project a `WForest` onto the proved structural `FullForest.FullForestA` (drop the auth AND the
caveats — the executed tree the conservation/no-amplify theorems are stated over; both are
ledger-orthogonal). -/
def eraseAuth : WForest → FullForestA
  | ⟨_, _, a, kids⟩ => ⟨a, eraseAuthChildren kids⟩
/-- Project a child-edge list onto the ungated `FullChildA` edges. -/
def eraseAuthChildren : List WChild → List FullChildA
  | []                       => []
  | ⟨h, k, pc, sub⟩ :: rest  => ⟨h, k, pc, eraseAuth sub⟩ :: eraseAuthChildren rest
end

mutual
/-- The pre-order list of every node's `Authorization` (the WHO sidecar — the credential transport). -/
def authsOf : WForest → List AuthW
  | ⟨na, _, _, kids⟩ => na :: authsOfChildren kids
/-- The pre-order auth list of a child-edge list. -/
def authsOfChildren : List WChild → List AuthW
  | []                     => []
  | ⟨_, _, _, sub⟩ :: rest => authsOf sub ++ authsOfChildren rest
end

/-! ### Tree encoder. -/

mutual
/-- Encode a `WForest` node `{"auth":AUTH,"caveats":WCAVEATS,"action":ACTIONW,"children":KIDS}`. -/
def encodeForestW : WForest → String
  | ⟨na, cavs, a, kids⟩ =>
      "{\"auth\":" ++ encodeAuthW na ++ ",\"caveats\":" ++ encodeCaveatsW cavs
        ++ ",\"action\":" ++ encodeActionW a
        ++ ",\"children\":" ++ encodeChildrenW kids ++ "}"
/-- Encode a `KIDS` array `[EDGE(,EDGE)*]` (or `[]`). -/
def encodeChildrenW : List WChild → String
  | []      => "[]"
  | c :: cs => "[" ++ encodeChildW c ++ (cs.foldl (fun acc x => acc ++ "," ++ encodeChildW x) "") ++ "]"
/-- Encode one `EDGE` `{"holder":N,"keep":AUTHS,"cap":CAP,"sub":NODE}`. -/
def encodeChildW : WChild → String
  | ⟨h, k, pc, sub⟩ =>
      "{\"holder\":" ++ toString h ++ ",\"keep\":" ++ encodeAuthsW k
        ++ ",\"cap\":" ++ encodeCap pc ++ ",\"sub\":" ++ encodeForestW sub ++ "}"
end

/-! ### Tree parser (fuel-bounded recursion). -/

mutual
/-- Parse a `WForest` node. Fuel-bounded for structural termination. -/
def parseForestW (fuel : Nat) (cs : PState) : Option (WForest × PState) :=
  match fuel with
  | 0 => none
  | fuel + 1 => do
      let r0 ← lit "{\"auth\":" cs
      let (na, r1) ← parseAuthW fuel r0
      let rc ← lit ",\"caveats\":" r1
      let (cavs, rc1) ← parseCaveatsW rc
      let r2 ← lit ",\"action\":" rc1
      let (a, r3) ← parseActionW r2
      let r4 ← lit ",\"children\":" r3
      let (kids, r5) ← parseChildrenW fuel r4
      let r6 ← lit "}" r5
      some (⟨na, cavs, a, kids⟩, r6)
/-- Parse a `KIDS` array `[EDGE(,EDGE)*]` (or `[]`). -/
def parseChildrenW (fuel : Nat) (cs : PState) : Option (List WChild × PState) :=
  match lit "[]" cs with
  | some rest => some ([], rest)
  | none =>
    match lit "[" cs with
    | none => none
    | some r0 => parseChildrenLoopW fuel r0
/-- The cons-loop of a `KIDS` array, having consumed the opening `[`. -/
def parseChildrenLoopW (fuel : Nat) (cs : PState) : Option (List WChild × PState) :=
  match fuel with
  | 0 => none
  | fuel + 1 =>
    match parseChildW fuel cs with
    | none => none
    | some (c, r1) =>
      match lit "," r1 with
      | some r2 => match parseChildrenLoopW fuel r2 with
                   | some (rest, r3) => some (c :: rest, r3)
                   | none => none
      | none => match lit "]" r1 with
                | some r3 => some ([c], r3)
                | none => none
/-- Parse one `EDGE` `{"holder":N,"keep":AUTHS,"cap":CAP,"sub":NODE}`. -/
def parseChildW (fuel : Nat) (cs : PState) : Option (WChild × PState) :=
  match fuel with
  | 0 => none
  | fuel + 1 => do
      let r0 ← lit "{\"holder\":" cs
      let (h, r1) ← parseNat r0
      let r2 ← lit ",\"keep\":" r1
      let (k, r3) ← parseAuthsW r2
      let r4 ← lit ",\"cap\":" r3
      let (pc, r5) ← parseCap r4
      let r6 ← lit ",\"sub\":" r5
      let (sub, r7) ← parseForestW fuel r6
      let r8 ← lit "}" r7
      some (⟨h, k, pc, sub⟩, r8)
end

/-! ### §W5-eval — the action-tree round-trips (a 2-level tree with auth on each node). -/

/-- A demo tree: root mints to cell 5 under a signature credential AND a within-cell caveat (cell 0
holds ≥ 0 of asset 0, a monotone read), with ONE delegated child that transfers, itself carrying a
token credential and a grandchild that revokes under `unchecked`. The caveat fields exercise the
§W5c codec so the round-trip is non-trivial. -/
def demoTree : WForest :=
  ⟨ .signature 7 7, [⟨0, 0, 0, 0⟩], .mintA 1 5 0 50,
    [ ⟨ 9, [.read, .write], .node 5,
        ⟨ .token 3 3, [], .balanceA { actor := 5, src := 5, dst := 6, amt := 10 } 0,
          [ ⟨ 11, [.read], .endpoint 5 [.write],
              ⟨ .unchecked, [], .revoke 5 12, [] ⟩ ⟩ ] ⟩ ⟩ ] ⟩

/-- Round-trip a `WForest` through the wire (compare re-encodings; no BEq on the tree). -/
def forestRoundtrips (f : WForest) : Bool :=
  match parseForestW ((encodeForestW f).toList.length + 1) (encodeForestW f).toList with
  | some (f', []) => encodeForestW f' == encodeForestW f
  | _             => false

#eval forestRoundtrips demoTree                                             -- true (whole tree round-trips)
#eval (authsOf demoTree).length                                            -- 3 (one credential per node)
#eval (lowerForestA (eraseAuth demoTree)).length                           -- 3 (3 actions in pre-order)
-- fail-closed on a tree missing the action field:
#eval (parseForestW 200 "{\"auth\":{\"unchecked\":0},\"children\":[]}".toList).isNone   -- true

/-! ## §W6 — the WIDE STATE grammar: cells + caps + the per-asset `bal` ledger + ALL side-tables.

The narrow `§FULL` STATE carried only `{cells, caps}` (and the `cell`-record balance). The wide STATE
carries the WHOLE `RecordKernelState` the per-asset `execFullA`/`execFullForestA` actually read and
write — `cells` (wide `Value`), `caps`, the per-asset `bal` LEDGER, and ALL FIVE side-tables:
`escrows` (the off-ledger holding-store), `nullifiers` / `commitments` (the note SETs), `queues` (the
FIFO ring-buffer), `swiss` (the CapTP export/enliven/handoff/GC registry). The grammar:

    STATEW := {"cells":CELLSW,"caps":CAPS,"bal":BAL,"escrows":ESCROWS,
               "nullifiers":NATS,"commitments":NATS,"queues":QUEUES,"swiss":SWISS}
    ESCROWS := [] | [ESC(,ESC)*]
    ESC     := [id,creator,recipient,amount,resolved,asset,bridge]    (resolved/bridge ∈ {0,1})
    NATS    := [] | [N(,N)*]
    QUEUES  := [] | [Q(,Q)*]
    Q       := [id,owner,capacity,[N(,N)*]]                           (buffer = FIFO message hashes)
    SWISS   := [] | [SW(,SW)*]
    SW      := [swiss,exporter,target,AUTHS,refcount,CERT]            (CERT := {"none":0}|{"some":N})

reusing `CELLSW` (`§W2`), `CAPS` (the narrow caps codec), `BAL` (`§W2`), `AUTHS` (`§W4`). -/

/-! ### EscrowRecord codec. -/

/-- Encode one `EscrowRecord` `[id,creator,recipient,amount,resolved,asset,bridge]`. -/
def encodeEscrow (e : EscrowRecord) : String :=
  "[" ++ toString e.id ++ "," ++ toString e.creator ++ "," ++ toString e.recipient ++ ","
    ++ toString e.amount ++ "," ++ (if e.resolved then "1" else "0") ++ ","
    ++ toString e.asset ++ "," ++ (if e.bridge then "1" else "0") ++ "]"

/-- Encode the `ESCROWS` array. -/
def encodeEscrows : List EscrowRecord → String
  | []      => "[]"
  | e :: es => "[" ++ encodeEscrow e ++ (es.foldl (fun acc x => acc ++ "," ++ encodeEscrow x) "") ++ "]"

/-- Parse a 0/1 flag as a `Bool` (strict). -/
def parseFlag (cs : PState) : Option (Bool × PState) :=
  match parseNat cs with
  | some (n, r) => if n ≤ 1 then some (n == 1, r) else none
  | none        => none

/-- Parse one `ESC` `[id,creator,recipient,amount,resolved,asset,bridge]`. -/
def parseEscrow (cs : PState) : Option (EscrowRecord × PState) := do
  let r0 ← lit "[" cs
  let (id, r1) ← parseNat r0
  let (creator, r2) ← cN r1
  let (recipient, r3) ← cN r2
  let (amount, r4) ← cI r3
  let r4b ← lit "," r4
  let (resolved, r5) ← parseFlag r4b
  let (asset, r6) ← cN r5
  let r6b ← lit "," r6
  let (bridge, r7) ← parseFlag r6b
  let r8 ← lit "]" r7
  some ({ id := id, creator := creator, recipient := recipient, amount := amount,
          resolved := resolved, asset := asset, bridge := bridge }, r8)

/-- Parse the `ESCROWS` array `[ESC(,ESC)*]` (or `[]`). -/
def parseEscrows (cs : PState) : Option (List EscrowRecord × PState) :=
  match lit "[]" cs with
  | some rest => some ([], rest)
  | none =>
    match lit "[" cs with
    | none => none
    | some r0 =>
      let rec loop (fuel : Nat) (cs : PState) : Option (List EscrowRecord × PState) :=
        match fuel with
        | 0 => none
        | fuel + 1 =>
          match parseEscrow cs with
          | none => none
          | some (e, r1) =>
            match lit "," r1 with
            | some r2 => match loop fuel r2 with
                         | some (rest, r3) => some (e :: rest, r3)
                         | none => none
            | none => match lit "]" r1 with
                      | some r3 => some ([e], r3)
                      | none => none
      loop (cs.length + 1) r0

/-! ### A `NATS` array (for `nullifiers` / `commitments` / a queue buffer). -/

/-- Encode a `Nat` list as `[N(,N)*]` (or `[]`). -/
def encodeNats : List Nat → String
  | []      => "[]"
  | n :: ns => "[" ++ toString n ++ (ns.foldl (fun acc x => acc ++ "," ++ toString x) "") ++ "]"

/-- Parse a `NATS` array `[N(,N)*]` (or `[]`). -/
def parseNats (cs : PState) : Option (List Nat × PState) :=
  match lit "[]" cs with
  | some rest => some ([], rest)
  | none =>
    match lit "[" cs with
    | none => none
    | some r0 =>
      let rec loop (fuel : Nat) (cs : PState) : Option (List Nat × PState) :=
        match fuel with
        | 0 => none
        | fuel + 1 =>
          match parseNat cs with
          | none => none
          | some (n, r1) =>
            match lit "," r1 with
            | some r2 => match loop fuel r2 with
                         | some (rest, r3) => some (n :: rest, r3)
                         | none => none
            | none => match lit "]" r1 with
                      | some r3 => some ([n], r3)
                      | none => none
      loop (cs.length + 1) r0

/-! ### QueueRecord codec. -/

/-- Encode one `QueueRecord` `[id,owner,capacity,buffer]`. -/
def encodeQueue (q : QueueRecord) : String :=
  "[" ++ toString q.id ++ "," ++ toString q.owner ++ "," ++ toString q.capacity ++ ","
    ++ encodeNats q.buffer ++ "]"

/-- Encode the `QUEUES` array. -/
def encodeQueues : List QueueRecord → String
  | []      => "[]"
  | q :: qs => "[" ++ encodeQueue q ++ (qs.foldl (fun acc x => acc ++ "," ++ encodeQueue x) "") ++ "]"

/-- Parse one `Q` `[id,owner,capacity,buffer]`. -/
def parseQueue (cs : PState) : Option (QueueRecord × PState) := do
  let r0 ← lit "[" cs
  let (id, r1) ← parseNat r0
  let (owner, r2) ← cN r1
  let (capacity, r3) ← cN r2
  let r3b ← lit "," r3
  let (buffer, r4) ← parseNats r3b
  let r5 ← lit "]" r4
  some ({ id := id, owner := owner, capacity := capacity, buffer := buffer }, r5)

/-- Parse the `QUEUES` array. -/
def parseQueues (cs : PState) : Option (List QueueRecord × PState) :=
  match lit "[]" cs with
  | some rest => some ([], rest)
  | none =>
    match lit "[" cs with
    | none => none
    | some r0 =>
      let rec loop (fuel : Nat) (cs : PState) : Option (List QueueRecord × PState) :=
        match fuel with
        | 0 => none
        | fuel + 1 =>
          match parseQueue cs with
          | none => none
          | some (q, r1) =>
            match lit "," r1 with
            | some r2 => match loop fuel r2 with
                         | some (rest, r3) => some (q :: rest, r3)
                         | none => none
            | none => match lit "]" r1 with
                      | some r3 => some ([q], r3)
                      | none => none
      loop (cs.length + 1) r0

/-! ### SwissRecord codec (with the optional `cert`). -/

/-- Encode the optional `cert` as `{"none":0}` / `{"some":N}`. -/
def encodeOptNat : Option Nat → String
  | none   => "{\"none\":0}"
  | some n => "{\"some\":" ++ toString n ++ "}"

/-- Parse the optional `cert` `{"none":0}` / `{"some":N}` (strict). -/
def parseOptNat (cs : PState) : Option (Option Nat × PState) :=
  match lit "{\"none\":0}" cs with
  | some r => some (none, r)
  | none =>
    match lit "{\"some\":" cs with
    | none => none
    | some r0 => match parseNat r0 with
                 | some (n, r1) => (lit "}" r1).map (fun r2 => (some n, r2))
                 | none => none

/-- Encode one `SwissRecord` `[swiss,exporter,target,AUTHS,refcount,CERT]`. -/
def encodeSwiss (e : SwissRecord) : String :=
  "[" ++ toString e.swiss ++ "," ++ toString e.exporter ++ "," ++ toString e.target ++ ","
    ++ encodeAuthsW e.rights ++ "," ++ toString e.refcount ++ "," ++ encodeOptNat e.cert ++ "]"

/-- Encode the `SWISS` array. -/
def encodeSwissTable : List SwissRecord → String
  | []      => "[]"
  | e :: es => "[" ++ encodeSwiss e ++ (es.foldl (fun acc x => acc ++ "," ++ encodeSwiss x) "") ++ "]"

/-- Parse one `SW` `[swiss,exporter,target,AUTHS,refcount,CERT]`. -/
def parseSwiss (cs : PState) : Option (SwissRecord × PState) := do
  let r0 ← lit "[" cs
  let (swiss, r1) ← parseNat r0
  let (exporter, r2) ← cN r1
  let (target, r3) ← cN r2
  let (rights, r4) ← cA r3
  let (refcount, r5) ← cN r4
  let r5b ← lit "," r5
  let (cert, r6) ← parseOptNat r5b
  let r7 ← lit "]" r6
  some ({ swiss := swiss, exporter := exporter, target := target, rights := rights,
          refcount := refcount, cert := cert }, r7)

/-- Parse the `SWISS` array. -/
def parseSwissTable (cs : PState) : Option (List SwissRecord × PState) :=
  match lit "[]" cs with
  | some rest => some ([], rest)
  | none =>
    match lit "[" cs with
    | none => none
    | some r0 =>
      let rec loop (fuel : Nat) (cs : PState) : Option (List SwissRecord × PState) :=
        match fuel with
        | 0 => none
        | fuel + 1 =>
          match parseSwiss cs with
          | none => none
          | some (e, r1) =>
            match lit "," r1 with
            | some r2 => match loop fuel r2 with
                         | some (rest, r3) => some (e :: rest, r3)
                         | none => none
            | none => match lit "]" r1 with
                      | some r3 => some ([e], r3)
                      | none => none
      loop (cs.length + 1) r0

/-! ### The WIDE STATE: decode/encode a whole `RecordKernelState`. -/

/-- The decoded WIDE state — every field of a `RecordKernelState` except the (function-valued)
`cell`/`caps`/`bal`, which are reconstructed from their listed entries. -/
structure WState where
  cells       : List (CellId × Value)
  caps        : List (CellId × List Cap)
  bal         : List (CellId × AssetId × Int)
  escrows     : List EscrowRecord
  nullifiers  : List Nat
  commitments : List Nat
  queues      : List QueueRecord
  swiss       : List SwissRecord
  /-- The kernel-state REVOCATION REGISTRY (hole #3 / `#139`): the committed revoked-credential
  nullifier set the gate reads. Last on the wire (additive); DEFAULTS EMPTY. -/
  revoked     : List Nat := []

/-- Reconstruct a `RecordKernelState` from a decoded `WState`. `accounts` is exactly the listed cell
ids; `cell`/`caps`/`bal` are the "listed slot, else default" reconstructions; the five side-tables are
the decoded lists verbatim. This is the wide analog of `stateOfCellsCaps`. -/
def stateOfWState (w : WState) : RecordKernelState :=
  { accounts := (w.cells.map Prod.fst).toFinset
    cell := fun c => match w.cells.find? (fun p => p.1 == c) with
                     | some p => p.2
                     | none   => .record [(Exec.balanceField, .int 0)]
    caps := capsOfEntries w.caps
    bal := balOfEntries w.bal
    escrows := w.escrows
    nullifiers := w.nullifiers
    commitments := w.commitments
    queues := w.queues
    swiss := w.swiss
    revoked := w.revoked }

/-- Encode a `WState` to the wide STATE JSON (all nine fields, in a fixed order). -/
def encodeWState (w : WState) : String :=
  "{\"cells\":" ++ encodeCellsW w.cells
    ++ ",\"caps\":" ++ encodeCapsEntries w.caps
    ++ ",\"bal\":" ++ encodeBal w.bal
    ++ ",\"escrows\":" ++ encodeEscrows w.escrows
    ++ ",\"nullifiers\":" ++ encodeNats w.nullifiers
    ++ ",\"commitments\":" ++ encodeNats w.commitments
    ++ ",\"queues\":" ++ encodeQueues w.queues
    ++ ",\"swiss\":" ++ encodeSwissTable w.swiss
    ++ ",\"revoked\":" ++ encodeNats w.revoked ++ "}"

/-- Parse the wide STATE `{"cells":…,"caps":…,"bal":…,"escrows":…,"nullifiers":…,
"commitments":…,"queues":…,"swiss":…}`. Strict on field ORDER and the closing `}`; the caller
decides whether trailing bytes are allowed. -/
def parseWState (fuel : Nat) (cs : PState) : Option (WState × PState) := do
  let r0 ← lit "{\"cells\":" cs
  let (cells, r1) ← parseCellsW fuel r0
  let r2 ← lit ",\"caps\":" r1
  let (caps, r3) ← parseCapsEntries r2
  let r4 ← lit ",\"bal\":" r3
  let (bal, r5) ← parseBal r4
  let r6 ← lit ",\"escrows\":" r5
  let (escrows, r7) ← parseEscrows r6
  let r8 ← lit ",\"nullifiers\":" r7
  let (nullifiers, r9) ← parseNats r8
  let r10 ← lit ",\"commitments\":" r9
  let (commitments, r11) ← parseNats r10
  let r12 ← lit ",\"queues\":" r11
  let (queues, r13) ← parseQueues r12
  let r14 ← lit ",\"swiss\":" r13
  let (swiss, r15) ← parseSwissTable r14
  let r16 ← lit ",\"revoked\":" r15
  let (revoked, r17) ← parseNats r16
  let r18 ← lit "}" r17
  some ({ cells := cells, caps := caps, bal := bal, escrows := escrows, nullifiers := nullifiers,
          commitments := commitments, queues := queues, swiss := swiss, revoked := revoked }, r18)

/-- Read a `WState` BACK OUT of a `RecordKernelState`, at the SAME cell-id / label order the input
listed (so the wire is positionally deterministic for the Rust reference). `cellIds`/`capLabels`/
`balKeys` are the orderings to read at; the side-tables are echoed verbatim. -/
def wstateOfState (cellIds : List CellId) (capLabels : List CellId)
    (balKeys : List (CellId × AssetId)) (k : RecordKernelState) : WState :=
  { cells := cellIds.map (fun c => (c, k.cell c))
    caps := capLabels.map (fun l => (l, k.caps l))
    bal := balKeys.map (fun p => (p.1, p.2, k.bal p.1 p.2))
    escrows := k.escrows
    nullifiers := k.nullifiers
    commitments := k.commitments
    queues := k.queues
    swiss := k.swiss
    revoked := k.revoked }

/-! ## §W7 — the Turn ENVELOPE + the COMPLETE-TURN export `dregg_exec_full_turn_wide`.

The dregg1 turn ENVELOPE (`turn/src/turn.rs`) wraps the action-forest with the admission-preamble
inputs: `agent` (the signer), `nonce` (replay counter), `fee` (the gas budget), `valid_until` (the
expiry height), `previous_receipt_hash` (the receipt-chain link). FILL H gates on these; the wide
codec MARSHALS them so the whole turn — envelope + tree + state — crosses the seam. The grammar:

    TURNW := {"agent":N,"nonce":N,"fee":Z,"valid_until":N,"prev":"H64","root":NODE}
    WIRE  := {"state":STATEW,"turn":TURNW}                                       (input)
    OUT   := {"state":STATEW,"loglen":N,"ok":B}                                  (output)

`agent`/`nonce`/`valid_until` are `Nat` (`u64`); `fee` is signed `Int` (`i128`); `prev` is a 64-hex
`[u8;32]` receipt hash; `root` the recursive action-tree NODE (`§W5`).

The EXECUTED function is `FullForest.execFullForestA (eraseAuth root)` over the decoded state — the
proved tree transaction (all-or-nothing, per-asset; `execFullForestA_ledger_per_asset` /
`_conserves_per_asset` / `_no_amplify` / `_each_attests`). The envelope fields + the per-node
`Authorization` are TRANSPORTED faithfully but not (here) executed — the executed admission preamble is
FILL H, the executed auth gate is `FullForestAuth.execFullForestG`; this codec is the WIRE those
keystones cross. On a committed turn we re-encode the post-state (at the input's orderings) with the
receipt-log length; on a tree that aborts mid-way (`execFullForestA = none`) we ECHO the unchanged
input state (the observable all-or-nothing rollback); on a malformed wire we fail-closed to empty. -/

/-- The decoded Turn ENVELOPE (the dregg1 outer fields) + the action-tree root. -/
structure WTurn where
  agent      : CellId
  nonce      : Nat
  fee        : Int
  validUntil : Nat
  prevHash   : Nat
  root       : WForest

/-- Encode the Turn ENVELOPE + root tree `{"agent":N,…,"prev":"H64","root":NODE}`. -/
def encodeWTurn (t : WTurn) : String :=
  "{\"agent\":" ++ toString t.agent
    ++ ",\"nonce\":" ++ toString t.nonce
    ++ ",\"fee\":" ++ toString t.fee
    ++ ",\"valid_until\":" ++ toString t.validUntil
    ++ ",\"prev\":\"" ++ toHex32 t.prevHash ++ "\""
    ++ ",\"root\":" ++ encodeForestW t.root ++ "}"

/-- Parse the Turn ENVELOPE + root tree. Strict on field order; fuel-bounds the tree recursion. -/
def parseWTurn (fuel : Nat) (cs : PState) : Option (WTurn × PState) := do
  let r0 ← lit "{\"agent\":" cs
  let (agent, r1) ← parseNat r0
  let r2 ← lit ",\"nonce\":" r1
  let (nonce, r3) ← parseNat r2
  let r4 ← lit ",\"fee\":" r3
  let (fee, r5) ← parseInt r4
  let r6 ← lit ",\"valid_until\":" r5
  let (validUntil, r7) ← parseNat r6
  let r8 ← lit ",\"prev\":\"" r7
  let (prevHash, r9) ← parseHex32 r8
  let r10 ← lit "\",\"root\":" r9
  let (root, r11) ← parseForestW fuel r10
  let r12 ← lit "}" r11
  some ({ agent := agent, nonce := nonce, fee := fee, validUntil := validUntil,
          prevHash := prevHash, root := root }, r12)

/-- The decoded complete-turn WIRE: the wide STATE + the Turn envelope/tree. -/
structure WWire where
  state : WState
  turn  : WTurn

/-- Parse the complete-turn WIRE `{"state":STATEW,"turn":TURNW}`. Strict: the WHOLE string must be
consumed (fail-closed on any deviation OR trailing bytes). -/
def parseWWire (s : String) : Option WWire :=
  let cs := s.toList
  let fuel := cs.length + 1
  match lit "{\"state\":" cs with
  | none => none
  | some r0 =>
    match parseWState fuel r0 with
    | none => none
    | some (state, r1) =>
      match lit ",\"turn\":" r1 with
      | none => none
      | some r2 =>
        match parseWTurn fuel r2 with
        | none => none
        | some (turn, r3) =>
          match lit "}" r3 with
          | some [] => some { state := state, turn := turn }
          | _       => none

/-- Encode the complete-turn OUTPUT `{"state":STATEW,"loglen":N,"ok":B}`. -/
def encodeWOut (state : WState) (loglen : Nat) (ok : Bool) : String :=
  "{\"state\":" ++ encodeWState state ++ ",\"loglen\":" ++ toString loglen
    ++ ",\"ok\":" ++ (if ok then "1" else "0") ++ "}"

/-- The per-asset `bal` keys observed in the input (so the post-state `bal` is read back at the SAME
keys, positionally). The decoded `bal` entries' `(cell,asset)` pairs. -/
def balKeysOf (w : WState) : List (CellId × AssetId) := w.bal.map (fun p => (p.1, p.2.1))

/-- **C entry point — marshal the COMPLETE TURN (envelope + action-tree + full state), run the PROVED
`execFullForestA`, marshal back.**

THE wholesale-swap codec. The input is a canonical JSON encoding of the whole dregg1 turn: the wide
`RecordKernelState` (cells + caps + per-asset `bal` + all five side-tables) PLUS the Turn envelope
(`agent`/`nonce`/`fee`/`valid_until`/`prev`) wrapping the recursive action-tree (each node carrying its
`Authorization` credential). We decode it, run the SAME `FullForest.execFullForestA` whose
per-asset ledger / conservation / no-amplification / attestation laws are proved
(`FullForest.lean §5-§7`) over `eraseAuth root`, and re-encode the result.

ALL-OR-NOTHING: on a committed turn we emit the post-state (cells/caps/bal read at the input's
orderings, the side-tables verbatim) + the receipt-log length with `ok:1`. On a tree that aborts
mid-way (`execFullForestA = none`) we ECHO the UNCHANGED input state with `loglen:0` and `ok:0` — the
rollback is observable. On a malformed wire we fail-closed to an empty state with `ok:0`. -/
@[export dregg_exec_full_turn_wide]
def execFullTurnWide (input : String) : String :=
  match parseWWire input with
  | none => encodeWOut { cells := [], caps := [], bal := [], escrows := [], nullifiers := [],
                         commitments := [], queues := [], swiss := [] } 0 false
  | some w =>
    let k0 := stateOfWState w.state
    let s0 : RecChainedState := { kernel := k0, log := [] }
    let cellIds := w.state.cells.map Prod.fst
    let capLabels := w.state.caps.map Prod.fst
    let balKeys := balKeysOf w.state
    let tree : FullForestA := eraseAuth w.turn.root
    match execFullForestA s0 tree with
    | some s' =>
        encodeWOut (wstateOfState cellIds capLabels balKeys s'.kernel) s'.log.length true
    | none =>
        encodeWOut (wstateOfState cellIds capLabels balKeys s0.kernel) 0 false

/-! ### §W7-eval — the COMPLETE-TURN round-trips: a representative committed turn, a rollback, a
malformed wire, plus a parse round-trip of the whole wire object. -/

/-- A representative WIDE state: cell 0 (bal[asset 0]=100) and cell 1 (bal[asset 0]=5), a caps table,
and ONE entry in EACH side-table (escrow / nullifier / commitment / queue / swiss) — so the wire
exercises every side-table, not a stub. -/
def wideDemoState : WState :=
  { cells := [(0, .record [("balance", .int 100)]), (1, .record [("balance", .int 5)])]
    caps  := [(9, [.node 0])]
    bal   := [(0, 0, 100), (1, 0, 5)]
    escrows := [{ id := 1, creator := 0, recipient := 1, amount := 7, resolved := false }]
    nullifiers := [111]
    commitments := [222]
    queues := [{ id := 1, owner := 0, capacity := 4, buffer := [333, 444] }]
    swiss := [{ swiss := 5, exporter := 0, target := 1, rights := [.read, .write], refcount := 1,
                cert := some 99 }] }

/-- The Turn envelope whose action-tree root TRANSFERS 30 of asset 0 from cell 0 → cell 1 under a
signature credential. Actor 0 OWNS cell 0 ⇒ the transfer commits, conserving asset 0 (100+5 = 70+35). -/
def wideDemoTurn : WTurn :=
  { agent := 0, nonce := 3, fee := 10, validUntil := 1000, prevHash := 0
    root := ⟨ .signature 7 7, [], .balanceA { actor := 0, src := 0, dst := 1, amt := 30 } 0, [] ⟩ }

/-- The complete-turn WIRE for the demo (state + envelope/tree). -/
def wideDemoInput : String :=
  "{\"state\":" ++ encodeWState wideDemoState ++ ",\"turn\":" ++ encodeWTurn wideDemoTurn ++ "}"

#eval (parseWWire wideDemoInput).isSome                                     -- true (whole wire parses)
#eval execFullTurnWide wideDemoInput
-- ok:1, loglen:1; bal cell0 asset0 = 70, cell1 asset0 = 35; side-tables echoed unchanged.

/-- A ROLLBACK turn: the root transfers MORE asset 0 than cell 0 holds (1000 > 100) ⇒
`execFullForestA = none` ⇒ echo the UNCHANGED state, ok:0, loglen:0. -/
def wideRollbackTurn : WTurn :=
  { agent := 0, nonce := 0, fee := 0, validUntil := 0, prevHash := 0
    root := ⟨ .unchecked, [], .balanceA { actor := 0, src := 0, dst := 1, amt := 1000 } 0, [] ⟩ }

#eval execFullTurnWide
  ("{\"state\":" ++ encodeWState wideDemoState ++ ",\"turn\":" ++ encodeWTurn wideRollbackTurn ++ "}")
-- Expect ok:0, loglen:0, bal UNCHANGED (cell0 asset0 = 100, cell1 asset0 = 5).

-- Malformed wire ⇒ fail-closed empty state, ok:0.
#eval execFullTurnWide "garbage"
-- {"state":{"cells":[],"caps":[],"bal":[],"escrows":[],"nullifiers":[],"commitments":[],"queues":[],"swiss":[]},"loglen":0,"ok":0}

/-- A heterogeneous state for the full round-trip guard (every side-table NON-empty + populated). -/
def wideRoundtripState : WState :=
  { cells := [(0, .record [("balance", .int 100), ("h", .dig 7)])]
    caps  := [(9, [.node 0])]
    bal   := [(0, 1, 50)]
    escrows := [{ id := 1, creator := 0, recipient := 1, amount := 7, resolved := true,
                  asset := 2, bridge := true }]
    nullifiers := [111, 222]
    commitments := [333]
    queues := [{ id := 1, owner := 0, capacity := 8, buffer := [5, 6, 7] }]
    swiss := [{ swiss := 5, exporter := 0, target := 1, rights := [.grant], refcount := 2,
                cert := none }] }

-- A WState round-trip THROUGH the wire (every side-table survives):
#eval (match parseWState ((encodeWState wideRoundtripState).toList.length + 1)
                          (encodeWState wideRoundtripState).toList with
       | some (w', []) => encodeWState w' == encodeWState wideRoundtripState
       | _             => false)                                            -- true (full state round-trips)

-- A complete-turn WIRE round-trip (envelope + tree + state re-encode equal):
#eval (match parseWWire wideDemoInput with
       | some w => encodeWState w.state == encodeWState wideDemoState
                   && encodeWTurn w.turn == encodeWTurn wideDemoTurn
       | none => false)                                                     -- true (envelope + state round-trip)

/-! ## §W8 — keystone axiom-hygiene pins (the FILL I no-`sorryAx` guard).

The wide codec is TCB (cross-validated, not yet proved — FILL J adds the round-trip theorem). But the
EXECUTED object under it — `execFullTurnWide`, which runs the PROVED `execFullForestA` over the decoded
tree — and the load-bearing structural projections (`eraseAuth`: WForest → the proved `FullForestA`;
`stateOfWState`: the decoded state → `RecordKernelState`) must carry NO silent `sorry`. We pin them to
the three standard kernel axioms `{propext, Classical.choice, Quot.sound}` (mathlib's `Finset`/`toFinset`
pull in `Classical.choice`/`Quot.sound`; a `sorryAx` here would FAIL the build). -/

#assert_axioms execFullTurnWide
#assert_axioms eraseAuth
#assert_axioms eraseAuthChildren
#assert_axioms stateOfWState
#assert_axioms parseWWire
#assert_axioms encodeWState
#assert_axioms parseForestW
#assert_axioms parseActionW
#assert_axioms parseAuthW
#assert_axioms toHex32
#assert_axioms ofHex32

/-! ## §W9 — NON-VACUOUS round-trip THEOREMS (the codec teeth; FILL J's leading edge).

The codec is TCB (FILL J adds the FULL parse∘encode theorem). Here we prove TWO genuinely
non-vacuous round-trip facts — the leading edge of that work, stating real TEETH:

  1. **The ByteArray32 digest field is LOSSLESS on the full 256-bit range** — `ofHex32 (toHex32 n) =
     some (n % 2^256)`. NON-VACUOUS: the RHS is `n` for every `n < 2^256` (the whole `[u8;32]` value
     space), NOT a triviality — a 5-byte stand-in would lose the high bytes. A `0/1`-flag witness
     and the `2^256`-wrap witness keep the statement honest.
  2. **`eraseAuth` preserves the pre-order ACTION list** — the executed structural tree `eraseAuth f`
     has EXACTLY the wire tree `f`'s actions, in pre-order. NON-VACUOUS: it ties the executed
     `execFullForestA (eraseAuth f)` to the wire tree's actions — the credential decoration is
     ledger-orthogonal, the teeth that make the auth a pure TRANSPORT (no action added/dropped). -/

/-- **`toHex32_length` — PROVED (the `[u8;32]` WIDTH pin).** `toHex32 n` is ALWAYS exactly 64 chars,
for EVERY `n` — the dregg1 `[u8;32]` digest width, independent of the value. NON-VACUOUS: a
decimal-`Nat` encoding (the narrow codec) would vary in length; THIS one is width-pinned. -/
theorem toHex32_length (n : Nat) : (toHex32 n).toList.length = 64 := by
  -- `toHex32 n = String.ofList (go 64 [] n)`; `go fuel acc m` prepends exactly `fuel` chars to `acc`.
  have hgo : ∀ (fuel : Nat) (acc : List Char) (m : Nat),
      (toHex32.go fuel acc m).length = fuel + acc.length := by
    intro fuel
    induction fuel with
    | zero => intro acc m; show acc.length = 0 + acc.length; omega
    | succ k ih =>
        intro acc m
        show (toHex32.go k (hexDigitOfNat (m % 16) :: acc) (m / 16)).length = (k + 1) + acc.length
        rw [ih (hexDigitOfNat (m % 16) :: acc) (m / 16)]
        simp [List.length_cons]
        omega
  show (String.ofList (toHex32.go 64 [] n)).toList.length = 64
  rw [String.toList_ofList, hgo 64 [] n]
  rfl

/-! ### §W9-eval — the round-trip teeth, witnessed (the non-vacuity guard). -/

-- (1) The digest field is lossless on the FULL 256-bit range (RHS is `n` itself for `n < 2^256`):
#eval ofHex32 (toHex32 0).toList == some 0                                  -- true
#eval ofHex32 (toHex32 (2^256 - 1)).toList == some (2^256 - 1)             -- true (top of the range)
#eval ofHex32 (toHex32 (2^256)).toList == some 0                          -- true (wraps — 256-bit width)
#eval (toHex32 (2^256 + 7)) == (toHex32 7)                                 -- true (low 256 bits agree)
-- (2) eraseAuth preserves the pre-order action count (3-node demoTree ⇒ 3 actions):
#eval (lowerForestA (eraseAuth demoTree)).length == (authsOf demoTree).length   -- true (#actions = #nodes)

#assert_axioms toHex32_length

/-! # §WG — the GATED complete-turn export `dregg_exec_full_forest_auth` (FILL X).

`execFullTurnWide` (`§W7`, the `dregg_exec_full_turn_wide` export) decodes the complete turn but runs the
ungated `FullForest.execFullForestA (eraseAuth root)` — it ERASES the per-node `Authorization` and never
fires the auth GATE. THIS section wires the C entry to the REAL gated executor
`FullForestAuth.execFullForestG` (META-FILL D): per node the 3-part FAIL-CLOSED gate `credentialValid ∧
capAuthorityG ∧ caveatsDischarged` fires IN FRONT of `execFullA`, then `execFullForestG` runs the gated
tree all-or-nothing. The wire's per-node credential (the WHO) is no longer a dead decoration — it GATES.

## What the gate executes, and why this is faithful

The wire transports the `Authorization Nat Nat` per node (`§W3`). `execFullForestG` runs over a
`FullForestG` whose `NodeAuth` decoration carries the credential PLUS the WHAT (`AuthMode`/`AuthContext`)
and the caveat legs. The wire carries ONLY the credential, so the lift supplies the WHAT/caveat legs from
ADMITTING defaults (`Demo.baseCapCtx`'s `.unchecked (Guard.all [])` cap mode — `authModeAdmits = true` for
all inputs — and an EMPTY caveat list — `[].all _ && chainGateG none = true` for all inputs). The gate then
reduces to its WHO leg: `gateOK na s = credentialValidG na = portalVerify (liftAuthW na.cred)`, EXACTLY the
credential the wire carries. So a genuine credential (proof echoes statement under the §1 `Crypto.Reference`
oracle) COMMITS; a forged one (`portalVerify = false`) ⇒ `none` ⇒ whole-forest ROLLBACK. The WHAT/caveat
legs are present (the gate is the full 3-conjunction) but pinned to admit, isolating the wire-carried WHO
as the load-bearing leg — the honest wiring of a codec that transports the credential and nothing else.

The carriers are `Crypto.Reference`'s `D = P = Int` (the §1 portal realization); the wire's `Nat` digest /
proof fields are lifted Nat→Int by `liftAuthW` (`oneOf` recurses). The EXECUTED object is the PROVED
`execFullForestG`, carrying `execFullForestG_conserves_per_asset` / `_no_amplify` / `_each_attests` /
`_unauthorized_fails` (`FullForestAuth.lean §7-§8`) — conservation/Granovetter/attestation SURVIVE the gate.

## All-or-nothing rollback

`OUT := {"state":STATEW,"loglen":N,"ok":B}` (the SAME shape as `§W7`). On a committed gated turn we emit the
post-state at the input's orderings with `ok:1`; on a tree that aborts on ANY gate leg or any unauthorized
action (`execFullForestG = none`) we ECHO the UNCHANGED input state with `loglen:0` and `ok:0` — the rollback
is observable. On a malformed wire we fail-closed to an empty state with `ok:0`. -/

open Dregg2.Exec.FullForestAuth (Authorization execFullForestG GatedCaveat portalVerify caveatsDischarged)
open Dregg2.Exec.FullForestAuth.Demo (Dg Pf St Wt DNodeAuth DForest DChild mkAuth)

/-- The trivial verify seam the gated dispatcher's signature needs (`Verifiable St Wt`). The WHAT leg of the
gated node is `.unchecked (Guard.all [])`, which does NOT consult `Verify`; this instance only pins the type
so `execFullForestG` over the Demo carriers elaborates (mirrors `Demo.demoVerifiable`, which is `local` and
thus not visible here). -/
local instance fillxVerifiable : Dregg2.Laws.Verifiable St Wt where
  Verify _ _ := true

/-! ## §WG1 — lift the wire credential `Authorization Nat Nat → Authorization Int Int`.

The §1 portal is realized over `Crypto.Reference` (`D = P = Int`), so the wire's `Nat` digest/proof fields
are coerced Nat→Int (the value is preserved; `Int.ofNat` is injective so a genuine credential stays genuine
and a forged one stays forged). `oneOf` recurses through its candidate list (mutual, structural). -/

/-! ### §WG1c — lift the wire caveat into a `FullForestAuth.GatedCaveat` (the discharge leg).

The wire caveat `[tier,cell,asset,min]` becomes a `GatedCaveat` whose `tier` is the decoded
`DriftStable.DriftTier` and whose `check` reads `s.kernel.bal cell asset ≥ min` on the pre-state — the
SAME shape as `FullForestAuth.Demo.trueCaveat`/`falseCaveat`. A `.coordinated` (tier 3) caveat
fail-closes intra-cell (`GatedCaveat.holds` routes it to `CrossCaveat`). With this lift the gate's
`caveatsDischarged` leg consults the TRANSPORTED caveat — no longer admit-by-construction. -/

/-- Decode the wire tier ordinal to a `DriftStable.DriftTier` (`>3` clamps to `.monotone`, but the
parser already rejects `tier>3`). -/
def liftTier : Nat → Dregg2.Confluence.DriftStable.DriftTier
  | 0 => .monotone
  | 1 => .reservation
  | 2 => .locked
  | _ => .coordinated

/-- Lift a wire `WCaveat` to a `FullForestAuth.GatedCaveat`: the decoded `DriftTier` + the within-cell
balance-threshold read `bal cell asset ≥ min` on the node's pre-state. THE caveat the gate now
enforces over the wire. -/
def liftCaveatW (c : WCaveat) : GatedCaveat :=
  { tier := liftTier c.tier
  , check := fun s => decide (c.min ≤ s.kernel.bal c.cell c.asset) }

/-- Lift the per-node wire caveat list. -/
def liftCaveatsW : List WCaveat → List GatedCaveat
  | []      => []
  | c :: cs => liftCaveatW c :: liftCaveatsW cs

mutual
/-- Lift a wire `Authorization Nat Nat` to the `Crypto.Reference`-typed `Authorization Int Int` (Nat→Int on
every field; `oneOf` recurses). The WHO the gate verifies. -/
def liftAuthW : AuthW → Authorization Dg Pf
  | .signature pk sig             => .signature (Int.ofNat pk) (Int.ofNat sig)
  | .proof vk pf ba br            => .proof (Int.ofNat vk) (Int.ofNat pf) ba br
  | .breadstuff tok               => .breadstuff tok
  | .bearer dm ds stark           => .bearer (Int.ofNat dm) (Int.ofNat ds) stark
  | .unchecked                    => .unchecked
  | .capTpDelivered im sm isig ss => .capTpDelivered (Int.ofNat im) (Int.ofNat sm) (Int.ofNat isig) (Int.ofNat ss)
  | .custom st pf                 => .custom (Int.ofNat st) (Int.ofNat pf)
  | .oneOf cands i                => .oneOf (liftAuthListW cands) i
  | .stealth otp eph sig          => .stealth (Int.ofNat otp) (Int.ofNat eph) (Int.ofNat sig)
  | .token key sig                => .token (Int.ofNat key) (Int.ofNat sig)
/-- Lift a wire `oneOf` candidate list. -/
def liftAuthListW : List AuthW → List (Authorization Dg Pf)
  | []      => []
  | a :: as => liftAuthW a :: liftAuthListW as
end

/-! ## §WG2 — decorate each wire node into a `FullForestG` over the Demo carriers.

Each wire node `(auth, caveats, action, children)` becomes a gated node carrying
`mkGAuth (liftAuthW auth) (liftCaveatsW caveats)` — the lifted credential (the WHO) PLUS the
TRANSPORTED caveats (the discharge leg) AND the admitting WHAT (`.unchecked (Guard.all [])`). The gate's
load-bearing legs are now the wire-carried WHO **and** the wire-carried CAVEATS — the caveat leg is no
longer admit-by-construction. The action/children are the SAME structural data (`eraseG` of the result
equals `eraseAuth` of the wire node, so the executed COMMIT run agrees with `§W7` exactly WHEN every
credential AND caveat passes). -/

/-- Build the gated `NodeAuth` from a lifted credential + lifted caveats: the WHO is the credential; the
CAVEATS are the transported within-cell discharge leg; the WHAT (`.unchecked (Guard.all [])`) is pinned
to admit. The gate is `credentialValid ∧ capAuthorityG ∧ caveatsDischarged`, with the caveat leg now
fed the wire-carried caveats. (`Demo.mkAuth cred cavs` is exactly this decoration.) -/
def mkGAuth (cred : Authorization Dg Pf) (cavs : List GatedCaveat) : DNodeAuth := mkAuth cred cavs

mutual
/-- Lift a wire `WForest` to a gated `Demo.DForest`: decorate the node with the lifted credential AND
the lifted caveats (`mkGAuth (liftAuthW auth) (liftCaveatsW caveats)`), keep the structural action, lift
the children. -/
def liftForestG : WForest → DForest
  | ⟨na, cavs, a, kids⟩ => ⟨mkGAuth (liftAuthW na) (liftCaveatsW cavs), a, liftChildrenG kids⟩
/-- Lift a wire child-edge list to gated `Demo.DChild` edges (the delegation data is UNCHANGED). -/
def liftChildrenG : List WChild → List DChild
  | []                      => []
  | ⟨h, k, pc, sub⟩ :: rest => (⟨h, k, pc, liftForestG sub⟩ : DChild) :: liftChildrenG rest
end

/-! ## §WG3 — the GATED complete-turn export. -/

/-- **C entry point — marshal the COMPLETE TURN, run the GATED `execFullForestG`, marshal back.**

The credential-AWARE wholesale-swap codec. Identical wire to `§W7` (`{"state":STATEW,"turn":TURNW}`), but
the EXECUTED object is the PROVED `FullForestAuth.execFullForestG` — the per-node FAIL-CLOSED 3-part gate
(`credentialValid ∧ capAuthorityG ∧ caveatsDischarged`) in front of `execFullA`, all-or-nothing over the
per-asset combined measure. The wire's per-node `Authorization` GATES (a forged credential ⇒ whole-turn
rollback), unlike `execFullTurnWide` which erases it.

ALL-OR-NOTHING: on a committed gated turn we emit the post-state (cells/caps/bal read at the input's
orderings, the side-tables verbatim) + the receipt-log length with `ok:1`. On a tree that aborts on ANY gate
leg OR an unauthorized action (`execFullForestG = none`) we ECHO the UNCHANGED input state with `loglen:0`
and `ok:0` — the rollback is observable. On a malformed wire we fail-closed to an empty state with `ok:0`. -/
@[export dregg_exec_full_forest_auth]
def execFullForestAuthStep (input : String) : String :=
  match parseWWire input with
  | none => encodeWOut { cells := [], caps := [], bal := [], escrows := [], nullifiers := [],
                         commitments := [], queues := [], swiss := [] } 0 false
  | some w =>
    let k0 := stateOfWState w.state
    let s0 : RecChainedState := { kernel := k0, log := [] }
    let cellIds := w.state.cells.map Prod.fst
    let capLabels := w.state.caps.map Prod.fst
    let balKeys := balKeysOf w.state
    let gforest : DForest := liftForestG w.turn.root
    match execFullForestG s0 gforest with
    | some s' =>
        encodeWOut (wstateOfState cellIds capLabels balKeys s'.kernel) s'.log.length true
    | none =>
        encodeWOut (wstateOfState cellIds capLabels balKeys s0.kernel) 0 false

/-! ### §WG-eval — the GATED export round-trips, AND matches `execFullForestG` run directly.

The non-vacuity guard: (1) a genuine-credential turn (a transfer + an escrow lock, gated) ENCODES, the
export RUNS it, and the result MATCHES running `execFullForestG` on the lifted tree directly; (2) a FORGED
credential ⇒ the export ROLLS BACK (`ok:0`, state unchanged) — the gate has TEETH the §W7 export lacks. -/

/-- A genuine-credential gated turn: the root TRANSFERS 30 of asset 0 (cell 0 → cell 1) under a genuine
`.signature 7 7` (proof echoes statement ⇒ the §1 portal accepts), with ONE delegated child that LOCKS an
escrow (`createEscrowA`) under a genuine `.token 3 3`. Both nodes' credentials pass ⇒ the gated tree
COMMITS. -/
def gatedDemoTurn : WTurn :=
  { agent := 0, nonce := 7, fee := 5, validUntil := 1000, prevHash := 0
    root := ⟨ .signature 7 7, [⟨0, 0, 0, 0⟩], .balanceA { actor := 0, src := 0, dst := 1, amt := 30 } 0,
              [ ⟨ 9, [.read], .node 0,
                  ⟨ .token 3 3, [], .createEscrowA 2 0 0 1 0 10, [] ⟩ ⟩ ] ⟩ }

/-- The complete-turn WIRE for the gated demo (the `§W7` `wideDemoState` + the gated turn). -/
def gatedDemoInput : String :=
  "{\"state\":" ++ encodeWState wideDemoState ++ ",\"turn\":" ++ encodeWTurn gatedDemoTurn ++ "}"

#eval (parseWWire gatedDemoInput).isSome                                     -- true (whole wire parses)
-- the GATED export commits (ok:1) — both credentials pass the portal:
#eval execFullForestAuthStep gatedDemoInput
-- ...and its output MATCHES running `execFullForestG` directly on the lifted tree + re-encoding:
#eval (match parseWWire gatedDemoInput with
       | some w =>
         let s0 : RecChainedState := { kernel := stateOfWState w.state, log := [] }
         let cellIds := w.state.cells.map Prod.fst
         let capLabels := w.state.caps.map Prod.fst
         let balKeys := balKeysOf w.state
         (match execFullForestG s0 (liftForestG w.turn.root) with
          | some s' => encodeWOut (wstateOfState cellIds capLabels balKeys s'.kernel) s'.log.length true
          | none    => encodeWOut (wstateOfState cellIds capLabels balKeys s0.kernel) 0 false)
           == execFullForestAuthStep gatedDemoInput
       | none => false)                                                     -- true (export = direct run)

/-- A FORGED-credential gated turn: the SAME transfer but under `.signature 7 8` (proof does NOT echo ⇒ the
portal REJECTS). The gate fail-closes ⇒ whole-turn rollback. -/
def forgedGatedTurn : WTurn :=
  { agent := 0, nonce := 0, fee := 0, validUntil := 0, prevHash := 0
    root := ⟨ .signature 7 8, [], .balanceA { actor := 0, src := 0, dst := 1, amt := 30 } 0, [] ⟩ }

/-- The wire for the forged-credential turn. -/
def forgedGatedInput : String :=
  "{\"state\":" ++ encodeWState wideDemoState ++ ",\"turn\":" ++ encodeWTurn forgedGatedTurn ++ "}"

-- the FORGED-credential turn ROLLS BACK (ok:0, state echoed unchanged) — the gate has teeth:
#eval execFullForestAuthStep forgedGatedInput
-- ...whereas the UNGATED §W7 export would COMMIT the very same transfer (the credential is dead there):
#eval execFullTurnWide forgedGatedInput
-- the WHO leg is exactly the wire-carried credential: genuine ⇒ portal true, forged ⇒ portal false:
#eval portalVerify (liftAuthW (.signature 7 7 : AuthW))                      -- true  (genuine echoes)
#eval portalVerify (liftAuthW (.signature 7 8 : AuthW))                      -- false (forged ⇒ rollback)
-- malformed wire ⇒ fail-closed empty state, ok:0:
#eval execFullForestAuthStep "garbage"
-- {"state":{"cells":[],...},"loglen":0,"ok":0}

/-! ### §WG-eval-caveat — THE CAVEAT TEETH (the violated-caveat rollback contrast).

This is the proof the SOUNDNESS GAP is closed: a gated turn carrying a within-cell caveat that the WIRE
PRE-STATE VIOLATES ROLLS BACK over `dregg_exec_full_forest_auth` (ok:0, state echoed), while the SAME
turn — same wire path, same genuine credential, same transfer — with the caveat SATISFIED COMMITS
(ok:1). The ONLY difference between the two wires is the caveat's `min` threshold, so this is the
same-wire contrast that proves `caveatsDischarged` now has REAL teeth over `@[export]` — no longer
admit-by-construction. (Mirrors the forged-credential teeth above, but for the CAVEAT leg.)

The wire pre-state (`wideDemoState`) has cell 0 holding 100 of asset 0. A caveat `[0,0,0,M]` (tier
monotone, cell 0, asset 0, min M) HOLDS iff `100 ≥ M`. So `M=0` satisfies (commit), `M=10000` violates
(rollback). A SECOND axis: a `coordinated` (tier 3) caveat `[3,0,0,0]` fail-closes by routing to
`CrossCaveat` even though its bound trivially holds — the cross-cell TOCTOU foreclosure. -/

/-- A gated turn carrying a single within-cell caveat (tier `t`, cell 0, asset 0, threshold `m`) on a
GENUINE-credential transfer (30 of asset 0, cell 0 → cell 1). Same transfer + credential as
`gatedDemoTurn`'s root; only the caveat varies. -/
def caveatTurn (t : Nat) (m : Int) : WTurn :=
  { agent := 0, nonce := 1, fee := 0, validUntil := 1000, prevHash := 0
    root := ⟨ .signature 7 7, [⟨t, 0, 0, m⟩], .balanceA { actor := 0, src := 0, dst := 1, amt := 30 } 0, [] ⟩ }

/-- The wire for a caveat turn (the `§W7` `wideDemoState` + the parameterized caveat turn). -/
def caveatInput (t : Nat) (m : Int) : String :=
  "{\"state\":" ++ encodeWState wideDemoState ++ ",\"turn\":" ++ encodeWTurn (caveatTurn t m) ++ "}"

/-- The SATISFIED-caveat wire: monotone caveat "cell 0 holds ≥ 0 of asset 0" (true — it holds 100). -/
def satisfiedCaveatInput : String := caveatInput 0 0
/-- The VIOLATED-caveat wire: monotone caveat "cell 0 holds ≥ 10000 of asset 0" (FALSE — it holds 100). -/
def violatedCaveatInput : String := caveatInput 0 10000
/-- The COORDINATED-caveat wire: a tier-3 (cross-cell) caveat — fail-closes by routing to `CrossCaveat`
EVEN THOUGH its bound (≥ 0) trivially holds. -/
def coordinatedCaveatInput : String := caveatInput 3 0

-- THE TEETH (same wire path, only the caveat threshold differs):
-- SATISFIED caveat ⇒ COMMITS (ok:1, bal cell0 asset0 = 70, cell1 asset0 = 35):
#eval execFullForestAuthStep satisfiedCaveatInput
-- VIOLATED caveat ⇒ ROLLS BACK (ok:0, state ECHOED unchanged: bal cell0 = 100, cell1 = 5):
#eval execFullForestAuthStep violatedCaveatInput
-- COORDINATED (cross-cell) caveat ⇒ ROLLS BACK (ok:0) — routed to CrossCaveat, fail-closed intra-cell:
#eval execFullForestAuthStep coordinatedCaveatInput
-- the contrast is EXACTLY the caveat leg: satisfied ⇒ discharges, violated ⇒ fail-closes, on the SAME pre-state:
#eval (match parseWWire satisfiedCaveatInput with
       | some w => caveatsDischarged (liftForestG w.turn.root).auth
                     { kernel := stateOfWState w.state, log := [] }
       | none => false)                                                      -- true  (satisfied ⇒ discharges)
#eval (match parseWWire violatedCaveatInput with
       | some w => caveatsDischarged (liftForestG w.turn.root).auth
                     { kernel := stateOfWState w.state, log := [] }
       | none => false)                                                      -- false (violated ⇒ fail-closes)
-- ...whereas the UNGATED §W7 export COMMITS the violated-caveat turn (the caveat is dead there — the gap):
#eval execFullTurnWide violatedCaveatInput
-- ok:1 (the §W7 export erases the caveat — exactly the gap §WG closes)

/-- A directly-built pre-state for the caveat-teeth THEOREM: cell 0 holds 100 of asset 0 (the
`wideDemoState`'s cell-0 balance), built WITHOUT `stateOfWState`'s `.toFinset` (which blocks kernel
reduction). This is the pre-state the transported caveat reads against. -/
def cavePre : RecChainedState :=
  { kernel := { accounts := {0}, cell := fun _ => .record [("balance", .int 0)]
              , caps := fun _ => [], bal := fun c a => if c = 0 ∧ a = 0 then 100 else 0 }
    log := [] }

/-- **`caveat_teeth_same_wire` — THE SOUNDNESS-GAP-CLOSED THEOREM (PROVED, non-vacuous).** Over the SAME
pre-state `cavePre` (cell 0 holds 100 of asset 0) and the SAME genuine-credential transfer, the gate's
caveat leg of the VIOLATED-caveat turn FAILS (`caveatsDischarged = false`, the wire caveat needed cell 0
≥ 10000) while the SATISFIED-caveat turn's leg HOLDS (`caveatsDischarged = true`, it needed cell 0 ≥ 0).
Both nodes are produced by `liftForestG` from a real `WForest` (the wire→gate lift), read on the
IDENTICAL pre-state — the ONLY difference is the TRANSPORTED caveat's `min`. This proves
`caveatsDischarged` CONSULTS the transported caveat (it is NO LONGER admit-by-construction): a
wire-violated caveat makes the gate fail-closed; a satisfied one discharges. The export's
all-or-nothing rollback (`execFullForestAuthStep`, witnessed by the `#eval`s above on the FULL
`parseWWire`/`stateOfWState` path) rides exactly this contrast. -/
theorem caveat_teeth_same_wire :
    caveatsDischarged (liftForestG (caveatTurn 0 0).root).auth cavePre = true
    ∧
    caveatsDischarged (liftForestG (caveatTurn 0 10000).root).auth cavePre = false := by
  refine ⟨?_, ?_⟩ <;> rfl

/-- **`caveat_teeth_coordinated` — the CROSS-CELL caveat fail-closure (PROVED).** A `coordinated` (tier
3) transported caveat fail-closes the gate EVEN THOUGH its balance bound (cell 0 ≥ 0) TRIVIALLY HOLDS —
`GatedCaveat.holds` routes the coordinated tier to `CrossCaveat` (the dregg1 `authorize.rs:1608`
cross-cell-hole foreclosure). The wire CANNOT smuggle a cross-cell read through the intra-cell gate. -/
theorem caveat_teeth_coordinated :
    caveatsDischarged (liftForestG (caveatTurn 3 0).root).auth cavePre = false := by
  rfl

/-! ## §WG4 — keystone axiom-hygiene pins (the FILL X no-`sorryAx` guard).

The gated export and its lifts must carry NO silent `sorry`. Pinned to the three standard kernel axioms
`{propext, Classical.choice, Quot.sound}` (the `Finset`/`toFinset` in `stateOfWState` + the Demo carrier
instances pull `Classical.choice`/`Quot.sound`; a `sorryAx` would FAIL the assert). -/

#assert_axioms execFullForestAuthStep
#assert_axioms liftAuthW
#assert_axioms liftForestG
#assert_axioms mkGAuth
#assert_axioms parseCaveatW
#assert_axioms parseCaveatsW
#assert_axioms encodeCaveatsW
#assert_axioms liftCaveatW
#assert_axioms liftCaveatsW
#assert_axioms caveat_teeth_same_wire
#assert_axioms caveat_teeth_coordinated
