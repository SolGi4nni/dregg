/-
# Dregg2.Circuit.DescriptorCanonicalJson — reading a served descriptor back into a Lean term.

⚑ **WHY THIS EXISTS, AND WHAT IT IS NOT.** `DescriptorCanonical.canonicalBytes` encodes a Lean
`EffectVmDescriptor2`. To gate it against the deployed Rust encoder over the whole served tree, the
two sides must compute from **the same input** — otherwise the comparison is a fact about two trees
rather than about two encoders. The input both sides can share is the descriptor JSON on disk, so
Lean needs to read it. That is this module.

⚠ **IT IS THE INVERSE OF `emitVmJson2`, NOT A TRANSCRIPTION OF THE RUST PARSER.** The grammar it
accepts is the one `DescriptorIR2.emitVmJson2` and the v1 `EffectVmEmit` renderers produce — the
authoring side's own spec. Where the Rust door REFUSES (a vacuous range width, a narrow
`proof_bind`, a coefficient outside the field), this refuses too and for the same reason: a parser
more permissive than the door would hand the encoder a descriptor no deployed reader would accept,
and a parser more restrictive would turn an admitted descriptor into a false red.

⚠ **A parse failure is a REFUSAL, never a skipped row.** A reader that dropped what it could not
understand would silently shrink the corpus its gate reports on, which is how a differential comes to
cover less than its own summary line claims.

⚑ **THE DECLARED CHALLENGE COUNT IS CHECKED, NOT STORED.** The Lean `EffectVmDescriptor2` has no
`challenges` field — `DescriptorIR2.challengeCount` DERIVES it from the constraints, so it cannot
disagree with them. The wire carries a value, so this reader compares the two and refuses on
disagreement rather than preferring one.
-/
import Dregg2.Circuit.DescriptorCanonical

namespace Dregg2.Circuit.DescriptorCanonicalJson

open Dregg2.Exec.CircuitEmit (EmittedExpr)
open Dregg2.Circuit.Emit.EffectVmEmit
open Dregg2.Circuit.DescriptorIR2
open Dregg2.Crypto

/-! ## §1 — The two doors this reader mirrors. -/

/-- The BabyBear prime. A gate coefficient at or above it cannot round-trip a felt, and the deployed
strict cursor (`lean_descriptor_air.rs::JsonCursor::parse_int_field`) REFUSES it rather than folding
it — so this does too. -/
def BABYBEAR_P : Nat := 2013265921

/-- A range width at or above this refuses nothing at BabyBear (`p < 2^31`), so
`descriptor_ir2::parse_table_def` refuses a `range` table declaring it. Lean twin of the fact:
`Dregg2.Circuit.RangeFieldContainment.range_vacuous_at_or_above_31`. -/
def VACUOUS_RANGE_BITS : Nat := 31

/-- The wire id of a table, inverted. `TableId.wireId` is injective
(`TableId.wireId_injective`), so this is its genuine section. -/
def tableIdOfWire : Nat → TableId
  | 0 => .main
  | 1 => .poseidon2
  | 2 => .range
  | 3 => .memory
  | 4 => .mapOps
  | n => .custom (n - 5)

/-- ⚑ **THE SECTION IS A SECTION.** Reading a wire id and writing it back is the identity — so a
descriptor's table ids survive the round trip through this reader, and the canonical bytes the
encoder then writes carry the ids the file declared. -/
theorem wireId_tableIdOfWire (n : Nat) : (tableIdOfWire n).wireId = n := by
  match n with
  | 0 | 1 | 2 | 3 | 4 => rfl
  | (k + 5) => simp [tableIdOfWire, TableId.wireId]; omega

/-- The universal-memory domain code, inverted. `none` on a code no `Domain` carries — refused
rather than defaulted, since a wrong domain is a wrong address space. -/
def domainOfWire : Nat → Option UniversalMemory.Domain
  | 0 => some .registers
  | 1 => some .heap
  | 2 => some .caps
  | 3 => some .nullifiers
  | 4 => some .index
  | 5 => some .working
  | _ => none

/-- Every domain's code reads back as that domain. -/
theorem domainOfWire_domainCode (d : UniversalMemory.Domain) :
    domainOfWire (domainCode d).toNat = some d := by
  cases d <;> rfl

/-! ## §2 — A byte cursor over the file.

The emitted grammar has no escapes and (as emitted) no whitespace; whitespace is skipped anyway so a
reformatted file reads. Every parser threads a `Nat` offset into a fixed `ByteArray`: no substring
allocation, no `List Char`. -/

/-- Skip ASCII whitespace. -/
partial def skipWs (s : ByteArray) (i : Nat) : Nat :=
  if h : i < s.size then
    let b := s[i]
    if b == 32 || b == 9 || b == 10 || b == 13 then skipWs s (i + 1) else i
  else i

/-- The byte at `i`, if any. -/
def peek (s : ByteArray) (i : Nat) : Option UInt8 :=
  if h : i < s.size then some s[i] else none

/-- Consume the given byte or refuse. -/
def expectByte (s : ByteArray) (i : Nat) (b : UInt8) : Except String Nat :=
  let i := skipWs s i
  match peek s i with
  | some c => if c == b then .ok (i + 1) else
      .error s!"expected byte {b} at offset {i}, found {c}"
  | none => .error s!"unexpected end of input at offset {i}, expected byte {b}"

/-- Consume a run of ASCII digits as a `Nat`. -/
partial def natDigits (s : ByteArray) (i : Nat) (acc : Nat) (any : Bool) : Except String (Nat × Nat) :=
  match peek s i with
  | some c =>
      if c ≥ 48 && c ≤ 57 then natDigits s (i + 1) (acc * 10 + (c.toNat - 48)) true
      else if any then .ok (acc, i) else .error s!"expected a digit at offset {i}"
  | none => if any then .ok (acc, i) else .error s!"expected a digit at offset {i}"

/-- A non-negative integer literal. -/
def parseNat (s : ByteArray) (i : Nat) : Except String (Nat × Nat) :=
  natDigits s (skipWs s i) 0 false

/-- A signed integer literal. -/
def parseInt (s : ByteArray) (i : Nat) : Except String (Int × Nat) := do
  let i := skipWs s i
  if peek s i == some 45 then
    let (n, i) ← natDigits s (i + 1) 0 false
    return (-(Int.ofNat n), i)
  else
    let (n, i) ← natDigits s i 0 false
    return (Int.ofNat n, i)

/-- ⚑ A **field** coefficient: the same literal, under the deployed door's refusal. A coefficient at
or above the BabyBear prime cannot round-trip a felt; the strict Rust cursor refuses it and so does
this, so a descriptor is either readable by both or by neither. -/
def parseFieldInt (s : ByteArray) (i : Nat) : Except String (Int × Nat) := do
  let (v, i) ← parseInt s i
  if v.natAbs ≥ BABYBEAR_P then
    .error s!"oversized constant {v} at offset {i}: at or above the BabyBear prime, so it cannot round-trip a felt (the deployed strict cursor refuses it too)"
  else return (v, i)

/-- Scan to the closing quote of a string literal (no escapes in this grammar). -/
partial def strEnd (s : ByteArray) (i : Nat) : Except String Nat :=
  match peek s i with
  | some 34 => .ok i
  | some 92 => .error s!"unexpected escape in string at offset {i}"
  | some _ => strEnd s (i + 1)
  | none => .error "unterminated string"

/-- A quoted string. -/
def parseString (s : ByteArray) (i : Nat) : Except String (String × Nat) := do
  let i ← expectByte s i 34
  let e ← strEnd s i
  match String.fromUTF8? (s.extract i e) with
  | some t => return (t, e + 1)
  | none => .error s!"invalid UTF-8 in string at offset {i}"

/-- A quoted key followed by its colon. -/
def expectKey (s : ByteArray) (i : Nat) (k : String) : Except String Nat := do
  let (got, i) ← parseString s i
  if got == k then expectByte s i 58
  else .error s!"expected key \"{k}\" at offset {i}, found \"{got}\""

/-- `true` / `false`. -/
def parseBool (s : ByteArray) (i : Nat) : Except String (Bool × Nat) := do
  let i := skipWs s i
  if peek s i == some 116 then return (true, i + 4)
  else if peek s i == some 102 then return (false, i + 5)
  else .error s!"expected a boolean at offset {i}"

/-- `null`, consumed only if present. -/
def tryNull (s : ByteArray) (i : Nat) : Option Nat :=
  let i := skipWs s i
  if peek s i == some 110 then some (i + 4) else none

/-- The comma-separated tail of a JSON array. -/
partial def arrayTail {α : Type} (f : ByteArray → Nat → Except String (α × Nat)) (s : ByteArray)
    (i : Nat) (acc : List α) : Except String (List α × Nat) := do
  let (x, i) ← f s i
  let i := skipWs s i
  match peek s i with
  | some 44 => arrayTail f s (i + 1) (x :: acc)
  | some 93 => return ((x :: acc).reverse, i + 1)
  | other => .error s!"expected ',' or ']' at offset {i}, found {repr other}"

/-- A JSON array of `f`-parsed elements. -/
def parseArray {α : Type} (f : ByteArray → Nat → Except String (α × Nat)) (s : ByteArray) (i : Nat) :
    Except String (List α × Nat) := do
  let i ← expectByte s i 91
  let i := skipWs s i
  if peek s i == some 93 then return ([], i + 1) else arrayTail f s i []

/-- Skip to the end of a balanced object or array, given the nesting depth already entered. -/
partial def skipBalanced (s : ByteArray) (i depth : Nat) : Except String Nat := do
  match peek s i with
  | none => .error "unterminated object or array"
  | some 34 => do let (_, j) ← parseString s i; skipBalanced s j depth
  | some 123 | some 91 => skipBalanced s (i + 1) (depth + 1)
  | some 125 | some 93 => if depth ≤ 1 then return (i + 1) else skipBalanced s (i + 1) (depth - 1)
  | some _ => skipBalanced s (i + 1) depth

/-- Skip one balanced JSON value (used for the chip `params` object, which carries deployed pins and
contributes nothing to the canonical record). -/
def skipValue (s : ByteArray) (i : Nat) : Except String Nat := do
  let i := skipWs s i
  match peek s i with
  | some 34 => do let (_, j) ← parseString s i; return j
  | some 123 | some 91 => skipBalanced s i 0
  | _ => do
      let (_, j) ← parseInt s i
      return j

/-! ## §3 — The expression grammars. -/

/-- `EmittedExpr`, the inverse of `EmittedExpr.toJson`. -/
def parseExpr : Nat → ByteArray → Nat → Except String (EmittedExpr × Nat)
  | 0, _, i => .error s!"expression nesting too deep at offset {i}"
  | fuel + 1, s, i => do
    let i ← expectByte s i 123
    let i ← expectKey s i "t"
    let (tag, i) ← parseString s i
    let (e, i) ← match tag with
      | "var" => do
          let i ← expectByte s i 44
          let i ← expectKey s i "v"
          let (n, i) ← parseNat s i
          pure (EmittedExpr.var n, i)
      | "const" => do
          let i ← expectByte s i 44
          let i ← expectKey s i "v"
          let (v, i) ← parseFieldInt s i
          pure (EmittedExpr.const v, i)
      | "add" | "mul" => do
          let i ← expectByte s i 44
          let i ← expectKey s i "l"
          let (l, i) ← parseExpr fuel s i
          let i ← expectByte s i 44
          let i ← expectKey s i "r"
          let (r, i) ← parseExpr fuel s i
          pure (if tag == "add" then EmittedExpr.add l r else EmittedExpr.mul l r, i)
      | other => .error s!"unknown expr tag \"{other}\" at offset {i}"
    let i ← expectByte s i 125
    return (e, i)

/-- `WindowExpr`, the inverse of `WindowExpr.toJson`. -/
def parseWindowExpr : Nat → ByteArray → Nat → Except String (WindowExpr × Nat)
  | 0, _, i => .error s!"window expression nesting too deep at offset {i}"
  | fuel + 1, s, i => do
    let i ← expectByte s i 123
    let i ← expectKey s i "t"
    let (tag, i) ← parseString s i
    let (e, i) ← match tag with
      | "loc" => do
          let i ← expectByte s i 44
          let i ← expectKey s i "c"
          let (n, i) ← parseNat s i
          pure (WindowExpr.loc n, i)
      | "nxt" => do
          let i ← expectByte s i 44
          let i ← expectKey s i "c"
          let (n, i) ← parseNat s i
          pure (WindowExpr.nxt n, i)
      | "const" => do
          let i ← expectByte s i 44
          let i ← expectKey s i "v"
          let (v, i) ← parseFieldInt s i
          pure (WindowExpr.const v, i)
      | "add" | "mul" => do
          let i ← expectByte s i 44
          let i ← expectKey s i "l"
          let (l, i) ← parseWindowExpr fuel s i
          let i ← expectByte s i 44
          let i ← expectKey s i "r"
          let (r, i) ← parseWindowExpr fuel s i
          pure (if tag == "add" then WindowExpr.add l r else WindowExpr.mul l r, i)
      | other => .error s!"unknown window expr tag \"{other}\" at offset {i}"
    let i ← expectByte s i 125
    return (e, i)

/-- `ChalExpr`: the window grammar plus the CHALLENGE LEAF `{"t":"chal","i":N}`. -/
def parseChalExpr : Nat → ByteArray → Nat → Except String (ChalExpr × Nat)
  | 0, _, i => .error s!"chal expression nesting too deep at offset {i}"
  | fuel + 1, s, i => do
    let i ← expectByte s i 123
    let i ← expectKey s i "t"
    let (tag, i) ← parseString s i
    let (e, i) ← match tag with
      | "loc" => do
          let i ← expectByte s i 44
          let i ← expectKey s i "c"
          let (n, i) ← parseNat s i
          pure (ChalExpr.loc n, i)
      | "nxt" => do
          let i ← expectByte s i 44
          let i ← expectKey s i "c"
          let (n, i) ← parseNat s i
          pure (ChalExpr.nxt n, i)
      | "const" => do
          let i ← expectByte s i 44
          let i ← expectKey s i "v"
          let (v, i) ← parseFieldInt s i
          pure (ChalExpr.const v, i)
      | "chal" => do
          let i ← expectByte s i 44
          let i ← expectKey s i "i"
          let (n, i) ← parseNat s i
          pure (ChalExpr.chal n, i)
      | "add" | "mul" => do
          let i ← expectByte s i 44
          let i ← expectKey s i "l"
          let (l, i) ← parseChalExpr fuel s i
          let i ← expectByte s i 44
          let i ← expectKey s i "r"
          let (r, i) ← parseChalExpr fuel s i
          pure (if tag == "add" then ChalExpr.add l r else ChalExpr.mul l r, i)
      | other => .error s!"unknown chal expr tag \"{other}\" at offset {i}"
    let i ← expectByte s i 125
    return (e, i)

/-! ## §4 — Tables, hash sites, ranges. -/

/-- The member loop of one table definition. -/
partial def tableDefMembers (s : ByteArray) (i : Nat) (id arity bits : Option Nat)
    (name semTag : Option String) (rows : Option (List (List Nat))) :
    Except String (TableDef × Nat) := do
    let (key, i) ← parseString s i
    let i ← expectByte s i 58
    let (id, arity, bits, name, semTag, rows, i) ← match key with
      | "id" => do let (v, i) ← parseNat s i; pure (some v, arity, bits, name, semTag, rows, i)
      | "arity" => do let (v, i) ← parseNat s i; pure (id, some v, bits, name, semTag, rows, i)
      | "bits" => do let (v, i) ← parseNat s i; pure (id, arity, some v, name, semTag, rows, i)
      | "name" => do let (v, i) ← parseString s i; pure (id, arity, bits, some v, semTag, rows, i)
      | "sem" => do let (v, i) ← parseString s i; pure (id, arity, bits, name, some v, rows, i)
      | "rows" => do
          let (v, i) ← parseArray (parseArray parseNat) s i
          pure (id, arity, bits, name, semTag, some v, i)
      | "params" => do let i ← skipValue s i; pure (id, arity, bits, name, semTag, rows, i)
      | other => .error s!"unknown table-def key \"{other}\" at offset {i}"
    let i := skipWs s i
    match peek s i with
    | some 44 => tableDefMembers s (i + 1) id arity bits name semTag rows
    | some 125 => do
        let some semTag := semTag | .error "table def missing \"sem\""
        let sem ← match semTag with
          | "main" => pure RowSemantics.mainRow
          | "poseidon2_chip" => pure RowSemantics.permutation
          | "range" => do
              let some b := bits | .error "range table def missing \"bits\""
              if b ≥ VACUOUS_RANGE_BITS then
                .error s!"range table declares bits {b} >= {VACUOUS_RANGE_BITS}: the BabyBear field is below 2^31, so the lookup refuses nothing (the deployed door refuses it too)"
              else pure (RowSemantics.rangeLimb b)
          | "memory" => pure RowSemantics.memAccess
          | "map_ops" => pure RowSemantics.mapReconcile
          | "umemory" => pure RowSemantics.umemAccess
          | "umem_boundary" => pure RowSemantics.umemBoundaryRow
          | "exact_public_rows" => do
              let some r := rows | .error "exact-public table def missing \"rows\""
              pure (RowSemantics.exactPublicRows r)
          -- ⚑ THE ONE PLACE THE TWO ALGEBRAS ARE NOT IN BIJECTION. Rust's `TableSem` carries
          -- `UMemBoundaryCohort` (canonical tag 7); Lean's `RowSemantics` has no constructor for it.
          -- No served descriptor declares one. Refused by NAME rather than mapped to a neighbour.
          | "umem_boundary_cohort" =>
              .error "table sem \"umem_boundary_cohort\" has no RowSemantics constructor: canonical tag 7 is Rust-only and this reader will not map it to a neighbouring semantics"
          | other => .error s!"unknown table sem \"{other}\" at offset {i}"
        let some id := id | .error "table def missing \"id\""
        let some name := name | .error "table def missing \"name\""
        let some arity := arity | .error "table def missing \"arity\""
        return (⟨tableIdOfWire id, name, arity, sem⟩, i + 1)
    | other => .error s!"expected ',' or '}}' in table def at offset {i}, found {repr other}"

/-- One table definition. Key-dispatched (the optional `bits` / `rows` / `params` members depend on
the semantics tag), exactly as `parse_table_def` is. -/
def parseTableDef (s : ByteArray) (i : Nat) : Except String (TableDef × Nat) := do
  let i ← expectByte s i 123
  tableDefMembers s i none none none none none none

/-- One hash-site input. -/
def parseHashInput (s : ByteArray) (i : Nat) : Except String (HashInput × Nat) := do
  let i ← expectByte s i 123
  let i ← expectKey s i "t"
  let (tag, i) ← parseString s i
  let (h, i) ← match tag with
    | "col" => do
        let i ← expectByte s i 44
        let i ← expectKey s i "c"
        let (n, i) ← parseNat s i
        pure (HashInput.col n, i)
    | "digest" => do
        let i ← expectByte s i 44
        let i ← expectKey s i "k"
        let (n, i) ← parseNat s i
        pure (HashInput.digest n, i)
    | "zero" => pure (HashInput.zero, i)
    | other => .error s!"unknown hash input tag \"{other}\" at offset {i}"
  let i ← expectByte s i 125
  return (h, i)

/-- One hash site. -/
def parseHashSite (s : ByteArray) (i : Nat) : Except String (VmHashSite × Nat) := do
  let i ← expectByte s i 123
  let i ← expectKey s i "digest_col"
  let (digestCol, i) ← parseNat s i
  let i ← expectByte s i 44
  let i ← expectKey s i "arity"
  let (arity, i) ← parseNat s i
  let i ← expectByte s i 44
  let i ← expectKey s i "inputs"
  let (inputs, i) ← parseArray parseHashInput s i
  let i ← expectByte s i 125
  return (⟨digestCol, inputs, arity⟩, i)

/-- One range tooth. -/
def parseRange (s : ByteArray) (i : Nat) : Except String (VmRange × Nat) := do
  let i ← expectByte s i 123
  let i ← expectKey s i "wire"
  let (wire, i) ← parseNat s i
  let i ← expectByte s i 44
  let i ← expectKey s i "bits"
  let (bits, i) ← parseNat s i
  let i ← expectByte s i 125
  return (⟨wire, bits⟩, i)

/-! ## §5 — Constraints. -/

/-- Maximum expression nesting this reader will follow. The deployed canonical decoder caps at the
same depth (`MAX_EXPRESSION_DEPTH`). -/
def MAX_EXPR_DEPTH : Nat := 1024

/-- A boundary-row tag. -/
def parseRow (s : ByteArray) (i : Nat) : Except String (VmRow × Nat) := do
  let (t, i) ← parseString s i
  match t with
  | "first" => return (.first, i)
  | "last" => return (.last, i)
  | other => .error s!"unknown row tag \"{other}\" at offset {i}"

/-- A memory access kind. -/
def parseMemKind (s : ByteArray) (i : Nat) : Except String (MemoryChecking.Kind × Nat) := do
  let (t, i) ← parseString s i
  match t with
  | "read" => return (.read, i)
  | "write" => return (.write, i)
  | other => .error s!"unknown mem kind \"{other}\" at offset {i}"

/-- A map reconciliation kind. -/
def parseMapKind (s : ByteArray) (i : Nat) : Except String (MapOpKind × Nat) := do
  let (t, i) ← parseString s i
  match t with
  | "read" => return (.read, i)
  | "write" => return (.write, i)
  | "absent" => return (.absent, i)
  | "insert" => return (.insert, i)
  | "aafi_insert" => return (.aafiInsert, i)
  | other => .error s!"unknown map op kind \"{other}\" at offset {i}"

/-- The eight-lane digest group a `map_op` root carries. Refused at any other length, exactly as the
deployed door refuses it — a shorter group is a narrower tie, not a shorter check. -/
def eightLanes (what : String) (l : List EmittedExpr) : Except String (Fin 8 → EmittedExpr) :=
  if l.length == 8 then .ok (fun i => l.getD i.1 (.const 0))
  else .error s!"{what} group has {l.length} lanes, expected 8"

/-- What holds the commit lanes: a bound lane vector, or a PORT carrying the two names of its cover.
⚠ A bare `null` and a bare array are the retired v3 spellings and are REFUSED, never promoted. -/
def parseCommitBinding (s : ByteArray) (i : Nat) : Except String (CommitBinding × Nat) := do
  let i ← expectByte s i 123
  let i ← expectKey s i "t"
  let (tag, i) ← parseString s i
  let (b, i) ← match tag with
    | "bound" => do
        let i ← expectByte s i 44
        let i ← expectKey s i "lanes"
        let (l, i) ← parseArray (parseExpr MAX_EXPR_DEPTH) s i
        pure (CommitBindingOf.bound l, i)
    | "port" => do
        let i ← expectByte s i 44
        let i ← expectKey s i "port"
        let (p, i) ← parseString s i
        let i ← expectByte s i 44
        let i ← expectKey s i "seam"
        let (sm, i) ← parseString s i
        pure (CommitBindingOf.port ⟨p, sm⟩, i)
    | other => .error s!"unknown commit-binding tag \"{other}\" at offset {i}"
  let i ← expectByte s i 125
  return (b, i)

/-- One v2 constraint. Positional after the tag, exactly as both the Lean renderer and the deployed
parser are. -/
def parseConstraint (s : ByteArray) (i : Nat) : Except String (VmConstraint2 × Nat) := do
  let i ← expectByte s i 123
  let i ← expectKey s i "t"
  let (tag, i) ← parseString s i
  let expr := parseExpr MAX_EXPR_DEPTH
  let comma (i : Nat) (k : String) : Except String Nat := do
    let i ← expectByte s i 44
    expectKey s i k
  let (c, i) ← match tag with
    | "gate" => do
        let i ← comma i "body"
        let (b, i) ← expr s i
        pure (VmConstraint2.base (.gate b), i)
    | "transition" => do
        let i ← comma i "hi"
        let (hi, i) ← parseNat s i
        let i ← comma i "lo"
        let (lo, i) ← parseNat s i
        pure (VmConstraint2.base (.transition hi lo), i)
    | "boundary" => do
        let i ← comma i "row"
        let (r, i) ← parseRow s i
        let i ← comma i "body"
        let (b, i) ← expr s i
        pure (VmConstraint2.base (.boundary r b), i)
    | "pi_binding" => do
        let i ← comma i "row"
        let (r, i) ← parseRow s i
        let i ← comma i "col"
        let (col, i) ← parseNat s i
        let i ← comma i "pi_index"
        let (k, i) ← parseNat s i
        pure (VmConstraint2.base (.piBinding r col k), i)
    | "lookup" => do
        let i ← comma i "table"
        let (t, i) ← parseNat s i
        let i ← comma i "tuple"
        let (tu, i) ← parseArray expr s i
        pure (VmConstraint2.lookup ⟨tableIdOfWire t, tu⟩, i)
    | "mem_op" => do
        let i ← comma i "kind"
        let (kind, i) ← parseMemKind s i
        let i ← comma i "guard"
        let (guard, i) ← expr s i
        let i ← comma i "addr"
        let (addr, i) ← expr s i
        let i ← comma i "value"
        let (value, i) ← expr s i
        let i ← comma i "prev_value"
        let (pv, i) ← expr s i
        let i ← comma i "prev_serial"
        let (ps, i) ← expr s i
        pure (VmConstraint2.memOp ⟨guard, addr, value, pv, ps, kind⟩, i)
    | "umem_op" => do
        let i ← comma i "kind"
        let (kind, i) ← parseMemKind s i
        let i ← comma i "domain"
        let (dw, i) ← parseNat s i
        let some dom := domainOfWire dw
          | .error s!"unknown umem_op domain code {dw} at offset {i}"
        let i ← comma i "guard"
        let (guard, i) ← expr s i
        let i ← comma i "key"
        let (key, i) ← expr s i
        let i ← comma i "present"
        let (pres, i) ← expr s i
        let i ← comma i "value"
        let (value, i) ← expr s i
        let i ← comma i "prev_present"
        let (pp, i) ← expr s i
        let i ← comma i "prev_value"
        let (pv, i) ← expr s i
        let i ← comma i "prev_serial"
        let (ps, i) ← expr s i
        pure (VmConstraint2.umemOp ⟨guard, dom, key, pres, value, pp, pv, ps, kind⟩, i)
    | "map_op" => do
        let i ← comma i "op"
        let (op, i) ← parseMapKind s i
        let i ← comma i "guard"
        let (guard, i) ← expr s i
        let i ← comma i "root"
        let (rootL, i) ← parseArray expr s i
        let root ← eightLanes "map_op root" rootL
        let i ← comma i "key"
        let (key, i) ← expr s i
        let i ← comma i "value"
        let (value, i) ← expr s i
        let i ← comma i "new_root"
        let (newRootL, i) ← parseArray expr s i
        let newRoot ← eightLanes "map_op new_root" newRootL
        pure (VmConstraint2.mapOp ⟨guard, root, key, value, newRoot, op⟩, i)
    | "proof_bind" => do
        let i ← comma i "guard"
        let (guard, i) ← expr s i
        let i ← comma i "commit"
        let (commit, i) ← parseArray expr s i
        let i ← comma i "vk"
        let (vk, i) ← parseArray expr s i
        let i ← comma i "vk_pin"
        let (vkPin, i) ← match tryNull s i with
          | some j => pure ((none : Option (List Int)), j)
          | none => do
              let (p, i) ← parseArray parseInt s i
              pure (some p, i)
        let i ← comma i "bound"
        let (bound, i) ← parseCommitBinding s i
        let m : ProofBind := ⟨guard, commit, vk, vkPin, bound⟩
        -- ⚑ THE JSON DOOR's width refusal, in the authoring language: `ProofBind.widthOk` is the
        -- Lean predicate the AIRs already carry, so this is not a second transcription of
        -- `ProofBindSpec::width_ok` — it is the same verdict one stage upstream.
        if m.widthOk then pure (VmConstraint2.proofBind m, i)
        else .error s!"proof_bind refused by widthOk at offset {i}: a seam below the lane floor ties a limb"
    | "window_gate" => do
        let i ← comma i "on_transition"
        let (ot, i) ← parseBool s i
        let i ← comma i "body"
        let (b, i) ← parseWindowExpr MAX_EXPR_DEPTH s i
        pure (VmConstraint2.windowGate ⟨b, ot⟩, i)
    | "chal_gate" => do
        let i ← comma i "on_transition"
        let (ot, i) ← parseBool s i
        let i ← comma i "body"
        let (b, i) ← parseChalExpr MAX_EXPR_DEPTH s i
        pure (VmConstraint2.chalGate ⟨b, ot⟩, i)
    | other => .error s!"unknown constraint tag \"{other}\" at offset {i}"
  let i ← expectByte s i 125
  return (c, i)

/-! ## §6 — The descriptor. -/

/-- The member loop of a descriptor object. -/
partial def descriptorMembers (s : ByteArray) (i : Nat) (name : Option String)
    (ir traceWidth piCount challenges : Option Nat)
    (tables : List TableDef) (constraints : Option (List VmConstraint2))
    (hashSites : List VmHashSite) (ranges : List VmRange) :
    Except String EffectVmDescriptor2 := do
  let (key, i) ← parseString s i
  let i ← expectByte s i 58
  let (name, ir, traceWidth, piCount, challenges, tables, constraints, hashSites, ranges, i) ←
    match key with
    | "name" => do
        let (v, i) ← parseString s i
        pure (some v, ir, traceWidth, piCount, challenges, tables, constraints, hashSites, ranges, i)
    | "ir" => do
        let (v, i) ← parseNat s i
        pure (name, some v, traceWidth, piCount, challenges, tables, constraints, hashSites, ranges, i)
    | "trace_width" => do
        let (v, i) ← parseNat s i
        pure (name, ir, some v, piCount, challenges, tables, constraints, hashSites, ranges, i)
    | "public_input_count" => do
        let (v, i) ← parseNat s i
        pure (name, ir, traceWidth, some v, challenges, tables, constraints, hashSites, ranges, i)
    | "challenges" => do
        let (v, i) ← parseNat s i
        pure (name, ir, traceWidth, piCount, some v, tables, constraints, hashSites, ranges, i)
    | "tables" => do
        let (v, i) ← parseArray parseTableDef s i
        pure (name, ir, traceWidth, piCount, challenges, v, constraints, hashSites, ranges, i)
    | "constraints" => do
        let (v, i) ← parseArray parseConstraint s i
        pure (name, ir, traceWidth, piCount, challenges, tables, some v, hashSites, ranges, i)
    | "hash_sites" => do
        let (v, i) ← parseArray parseHashSite s i
        pure (name, ir, traceWidth, piCount, challenges, tables, constraints, v, ranges, i)
    | "ranges" => do
        let (v, i) ← parseArray parseRange s i
        pure (name, ir, traceWidth, piCount, challenges, tables, constraints, hashSites, v, i)
    | other => .error s!"unknown descriptor key \"{other}\" at offset {i}"
  let i := skipWs s i
  match peek s i with
  | some 44 =>
      descriptorMembers s (i + 1) name ir traceWidth piCount challenges tables constraints
        hashSites ranges
  | some 125 =>
      if skipWs s (i + 1) != s.size then
        .error s!"{s.size - skipWs s (i + 1)} trailing bytes after the descriptor"
      else do
        let some name := name | .error "descriptor missing \"name\""
        let some ir := ir | .error "descriptor has no \"ir\" key (v1 wire), refusing"
        if ir != 2 then .error s!"descriptor declares ir {ir}, this reader is the v2 grammar"
        let some traceWidth := traceWidth | .error "descriptor missing \"trace_width\""
        let some piCount := piCount | .error "descriptor missing \"public_input_count\""
        let some declared := challenges
          | .error "descriptor missing \"challenges\": an ir:2 record without it is the pre-2026-08-05 shape and is refused, never read as zero"
        let some constraints := constraints | .error "descriptor missing \"constraints\""
        let d : EffectVmDescriptor2 :=
          ⟨name, traceWidth, piCount, tables, constraints, hashSites, ranges⟩
        -- ⚑ The Lean descriptor DERIVES its challenge count, so the wire's value is a claim to be
        -- checked rather than a field to be stored. A disagreement is refused here rather than
        -- silently resolved in either direction.
        if challengeCount d != declared then
          .error s!"descriptor declares {declared} challenges, its constraints derive {challengeCount d}"
        else return d
  | other => .error s!"expected ',' or '}}' in descriptor at offset {i}, found {repr other}"

/-- ⚑ **Read a served DescriptorIR-v2 file into a Lean `EffectVmDescriptor2`.** Key-dispatched at the
top level (as the deployed reader is), so member order is not load-bearing. Refuses on: a missing
`"ir":2`, any missing member, a trailing byte, and a declared challenge count that disagrees with the
one the constraints derive. -/
def parseDescriptor (s : ByteArray) : Except String EffectVmDescriptor2 := do
  let i ← expectByte s 0 123
  descriptorMembers s i none none none none none [] none [] []

/-- The whole pin, from a served descriptor file's bytes: parse, encode, hash, pack.
⚑ This is `vk_pin` computation with no Rust anywhere in the path. -/
def vkPinLanesOfJson (s : ByteArray) : Except String (Option (List Nat)) := do
  let d ← parseDescriptor s
  match DescriptorCanonical.vkPinLanesNatOf d with
  | .ok r => return r
  | .error e => .error e.message

/-! ## §7 — The round trip, as named theorems.

⚠ These are what keep the READER honest. The gate below compares Lean's encoder against Rust's over
the same file; if the reader mis-read a member, that comparison would go red — but it would go red
without saying which side was wrong. These say the reader inverts the emitter. -/

open Dregg2.Circuit.DescriptorCanonical in
/-- ⚑ **THE READER INVERTS THE EMITTER.** Rendering a descriptor and reading it back gives a term
that renders identically — so no member is dropped, merged or aliased on the way through. Stated on
the wire string because `EffectVmDescriptor2` carries function-valued members (`MapOp.root`) and has
no `DecidableEq`. -/
theorem parse_emit_roundtrip_demoV2 :
    (parseDescriptor (emitVmJson2 demoV2).toUTF8).map emitVmJson2 = .ok (emitVmJson2 demoV2) := by
  native_decide

open Dregg2.Circuit.DescriptorCanonical in
/-- The same, on a descriptor carrying a challenge gate and a ported `proof_bind` — the two members
the falsifiers drop, and the two that no v1 round trip ever exercised. -/
theorem parse_emit_roundtrip_demoPort :
    (parseDescriptor (emitVmJson2 demoPort).toUTF8).map emitVmJson2 = .ok (emitVmJson2 demoPort) := by
  native_decide

open Dregg2.Circuit.DescriptorCanonical in
/-- ⚑ **AND THE ROUND TRIP PRESERVES THE PROTOCOL IDENTITY.** The canonical bytes of the re-read term
are the canonical bytes of the original, so a fingerprint taken after a round trip is the same
fingerprint. This is the property the differential's whole reading rests on. -/
theorem parse_emit_preserves_canonical_bytes_demoChal :
    (parseDescriptor (emitVmJson2 DescriptorCanonical.demoChal).toUTF8).toOption.bind
        (fun d => (canonicalBytes d).toOption.map Blake3.toHex)
      = (canonicalBytes DescriptorCanonical.demoChal).toOption.map Blake3.toHex := by
  native_decide

#assert_compiled parse_emit_roundtrip_demoV2
#assert_compiled parse_emit_roundtrip_demoPort
#assert_compiled parse_emit_preserves_canonical_bytes_demoChal
#assert_axioms wireId_tableIdOfWire
#assert_axioms domainOfWire_domainCode

end Dregg2.Circuit.DescriptorCanonicalJson
