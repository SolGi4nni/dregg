/-
# Dregg2.Circuit.DescriptorCanonical — the CANONICAL DescriptorIR-v2 RECORD, authored in Lean.

⚑ **THE HOP THAT WAS RUST-ONLY, AND WHY IT MATTERED.** A `vk_pin` is

```text
EffectVmDescriptor2 ──canonicalBytes──▶ fixed record ──blake3Derive──▶ 32 bytes ──keyToLanes9──▶ 9 lanes
```

`870ed1d93` landed hops 2 and 3 in pure Lean (`Dregg2.Crypto.Blake3Compute`,
`Dregg2.Circuit.KeyLanes9`), gated on all 159 served descriptors. Hop 1 —
`circuit/src/descriptor_ir2_canonical.rs::canonical_effect_vm_descriptor2_bytes` — existed **only in
Rust**, so `VkPinCompute.vkPinLanes` had to be HANDED bytes it could not produce, and a Lean
`EffectVmDescriptor2` term could not be fingerprinted at all. That is why thirteen `*_VK_LANES`
constants across six Lean modules are transcribed digits. This module is that hop.

## ⚠ THE ENCODER IS NOT `emitVmJson2`, AND CONFLATING THEM IS A LIVE ERROR

`DescriptorIR2.emitVmJson2` renders the **JSON build artifact**; this renders the **protocol
identity**. They are different objects and neither is a re-spelling of the other:
`by-name/accumulator-nonrev.json` is 10 229 JSON bytes and 2 646 canonical bytes. The semantic
fingerprint is `blake3::derive_key` over the CANONICAL bytes and never sees the JSON; the SHA-256
the registry pins (`Argus/EmitRoundtrip.lean`) is over the JSON and is a different digest for a
different purpose. Three separate write-ups have now asserted that `emitVmJson2` closes this hop.
It does not, and the header bytes say so: the record opens `44 52 45 47 47 49 52 32` = `DREGGIR2`.

## The record

Versioned magic header, fixed field order, explicit one-byte enum tags, little-endian fixed-width
integers, `u64`-length-prefixed UTF-8 strings and sequences. No maps, no floats, no serde, no
platform-width integers, no ignored fields. Every match below is exhaustive, so a new descriptor
constructor fails to elaborate here until a schema version is designed for it — the same tripwire
the Rust module carries, in the language the AIRs are authored in.

## ⚠ TRUST CLASS, SAID OUT LOUD

This is a **computation**, not a soundness result. `canonicalBytes` produces the same bytes the
deployed Rust produces — an IDENTITY claim, gated by
`scripts/check-descriptor-canonical-differential.sh` over every served descriptor on every run, both
sides recomputed. Nothing here is proved about what a fingerprint MEANS.

⚑ **A WRONG ENCODER FAILS SILENTLY.** Every fingerprint it computes would be self-consistent and
wrong — *"two agreeing transcriptions are not two witnesses; they are one witness copied"*, generated
at scale. `EncoderVariant` (§5) is why that is checkable: two deliberately wrong encoders that share
every other line with the true one, each agreeing with it on the majority of the served tree and
diverging on the descriptors that carry the feature it drops.
-/
import Dregg2.Circuit.DescriptorIR2
import Dregg2.Circuit.VkPinCompute
import Dregg2.Tactics

namespace Dregg2.Circuit.DescriptorCanonical

open Dregg2.Exec.CircuitEmit (EmittedExpr)
open Dregg2.Circuit.Emit.EffectVmEmit
open Dregg2.Circuit.DescriptorIR2
open Dregg2.Crypto

/-! ## §1 — The record's pinned constants (the Rust twins are named beside each). -/

/-- Eight-byte discriminator. Rust: `EFFECT_VM_DESCRIPTOR2_CANONICAL_MAGIC`. -/
def CANONICAL_MAGIC : List Nat := [0x44, 0x52, 0x45, 0x47, 0x47, 0x49, 0x52, 0x32] -- "DREGGIR2"

/-- Schema version of the fixed record. Rust: `EFFECT_VM_DESCRIPTOR2_CANONICAL_VERSION`.

⚑ Bumped `3 → 4` on 2026-08-10 (the `proof_bind` nullability flag day): tag `5`'s `bound` half is a
two-state sum — bound, or a PORT carrying the two NAMES of its cover — so the retired "absent" tag
no longer exists and a v3 record decodes to a DIFFERENT relation. Every bump rotates every
fingerprint; the version is INSIDE the bytes so an old record refuses rather than being
reinterpreted. -/
def CANONICAL_VERSION : Nat := 4

/-- Hard allocation boundary. Rust: `MAX_CANONICAL_EFFECT_VM_DESCRIPTOR2_BYTES`. -/
def MAX_CANONICAL_BYTES : Nat := 64 * 1024 * 1024

/-- The BLAKE3 derive-key context of the semantic fingerprint. This is the SAME string
`Dregg2.Crypto.Blake3.descriptor2FingerprintContext` carries — named here only so the two halves of
the pin are readable in one place; the gate reads the Rust source and compares. -/
def FINGERPRINT_CONTEXT : String := Blake3.descriptor2FingerprintContext

/-! ## §2 — Refusals.

⚑ Every one of these is a case Rust cannot reach and Lean can. `usize`/`i64` are bounded on the
host; `Nat` and `ℤ` are not. An encoder that truncated instead would produce a self-consistent wrong
fingerprint for a descriptor no Rust reader could ever have produced — so the wide cases REFUSE. -/

/-- Why a descriptor has no canonical encoding. -/
inductive CanonError where
  /-- A `Nat` index does not fit the record's fixed `u64` width. -/
  | indexTooWide (field : String) (value : Nat)
  /-- An `ℤ` coefficient does not fit the record's fixed `i64` width. -/
  | constOutOfRange (field : String) (value : Int)
  /-- A `Nat` cell does not fit the record's fixed `u32` width. -/
  | cellTooWide (field : String) (value : Nat)
  /-- The complete record exceeds the protocol's explicit allocation bound. -/
  | recordTooLarge (len max : Nat)
  deriving Repr, DecidableEq, Inhabited

/-- A readable refusal. -/
def CanonError.message : CanonError → String
  | .indexTooWide f v => s!"{f} value {v} does not fit canonical u64"
  | .constOutOfRange f v => s!"{f} coefficient {v} does not fit canonical i64"
  | .cellTooWide f v => s!"{f} cell {v} does not fit canonical u32"
  | .recordTooLarge len max => s!"canonical descriptor has {len} bytes, maximum is {max}"

/-! ## §3 — Byte primitives (little-endian, fixed width). -/

/-- Push `width` little-endian bytes of `n`. -/
def pushLE : ByteArray → Nat → Nat → ByteArray
  | w, 0, _ => w
  | w, (k + 1), n => pushLE (w.push (UInt8.ofNat (n % 256))) k (n / 256)

/-- The `u64` two's-complement image of an `ℤ` (the bit pattern Rust's `i64::to_le_bytes` writes). -/
def i64Bits (v : Int) : Nat := ((v % (2 ^ 64 : Int) + (2 ^ 64 : Int)).toNat) % 2 ^ 64

/-- A one-byte tag. -/
def wTag (w : ByteArray) (t : Nat) : ByteArray := w.push (UInt8.ofNat t)

/-- A `u16`. -/
def wU16 (w : ByteArray) (n : Nat) : ByteArray := pushLE w 2 n

/-- A `u32` cell, refusing anything the width cannot hold. -/
def wU32 (field : String) (w : ByteArray) (n : Nat) : Except CanonError ByteArray :=
  if n < 2 ^ 32 then .ok (pushLE w 4 n) else .error (.cellTooWide field n)

/-- A `u64` index, refusing anything the width cannot hold. -/
def wIndex (field : String) (w : ByteArray) (n : Nat) : Except CanonError ByteArray :=
  if n < 2 ^ 64 then .ok (pushLE w 8 n) else .error (.indexTooWide field n)

/-- An `i64` coefficient, refusing anything the width cannot hold. -/
def wI64 (field : String) (w : ByteArray) (v : Int) : Except CanonError ByteArray :=
  if -(2 ^ 63 : Int) ≤ v ∧ v < (2 ^ 63 : Int) then .ok (pushLE w 8 (i64Bits v))
  else .error (.constOutOfRange field v)

/-- A `u64`-length-prefixed UTF-8 string. ⚠ The length is the **byte** length, not the character
count: `String.length` would disagree with Rust's `str::len()` on every non-ASCII name. -/
def wString (field : String) (w : ByteArray) (s : String) : Except CanonError ByteArray := do
  let bs := s.toUTF8
  let w ← wIndex field w bs.size
  return w ++ bs

/-- A `u64`-length-prefixed sequence. -/
def wSeq {α : Type} (field : String) (w : ByteArray) (xs : List α)
    (f : ByteArray → α → Except CanonError ByteArray) : Except CanonError ByteArray := do
  let w ← wIndex field w xs.length
  xs.foldlM f w

/-! ## §4 — The wire codes, taken from the authoring language rather than retyped.

⚑ Every tag family below whose codes already exist in `DescriptorIR2` is READ from there
(`TableId.wireId`, `MapOpKind.code`, `kindCode`, `domainCode`). A second transcription of those
numbers here is exactly the defect this module exists to end. -/

/-- The `MemKind` tag byte. Rust: `write_mem_kind`. -/
def memKindTag (k : MemoryChecking.Kind) : Nat := (kindCode k).toNat

/-- The `MapKind` tag byte. Rust: `write_map_kind`. -/
def mapKindTag (k : MapOpKind) : Nat := k.code.toNat

/-- The universal-memory domain, as the `u32` the record carries. Rust: `writer.u32(*domain)`. -/
def domainWire (d : UniversalMemory.Domain) : Nat := (domainCode d).toNat

/-- The boundary-row tag byte. Rust: `write_vm_row`. -/
def vmRowTag : VmRow → Nat
  | .first => 0
  | .last => 1

/-! ## §5 — ⚑ `EncoderVariant`: the falsifier knob, and the ONLY reason it exists.

A wrong encoder is silent. So the two wrong ones live HERE, sharing every other line with the true
encoder — a falsifier that duplicated the walk would prove nothing about the paths it duplicated.

⚠ **`.canonical` is the only value any caller may use.** `canonicalBytes` is the knob-free entry
point and nothing else in the tree names this type. The other two exist to be caught, and
`scripts/check-descriptor-canonical-differential.sh` asserts a POSITIVE divergence count for each:
a falsifier that quietly became a no-op is how an adversary dies while its gate stays green. -/
inductive EncoderVariant where
  /-- The deployed record. -/
  | canonical
  /-- ⚑ **THE CHALLENGE LEAF IS NOT IN THE FINGERPRINT.** Encodes `ChalExpr.chal i` as the constant
  `i` — what a pre-schema-v2 encoder, which had no leaf for it, would be forced to do. Byte-identical
  to `.canonical` on every descriptor carrying no `chalGate` (155 of the 159 served), and different
  on the four that do. The defect it stands for is stated in the Rust encoder's own docblock: *"two
  descriptors that differ only in which challenge a gate reads have different fingerprints"* — this
  is the encoder for which that sentence is false. -/
  | chalAsConst
  /-- ⚑ **A PORT'S COVER NAMES ARE NOT IN THE FINGERPRINT.** Writes the `port` tag and drops the two
  names, on the reasoning the 2026-08-10 flag day rejected: a ported half emits no polynomial, so
  "it needs no payload". Byte-identical to `.canonical` on the 156 served descriptors with no ported
  `proof_bind` and different on the three that have one. Under it, two descriptors differing only in
  which seam is claimed to cover a port have the same protocol identity. -/
  | portNamesElided
  deriving Repr, DecidableEq, Inhabited

/-! ## §6 — The thirteen writers. -/

/-- `LeanExpr`: `Var | Const | Add | Mul` at tags `0..3`. -/
def wExpr (w : ByteArray) : EmittedExpr → Except CanonError ByteArray
  | .var c => wIndex "LeanExpr::Var.column" (wTag w 0) c
  | .const k => wI64 "LeanExpr::Const" (wTag w 1) k
  | .add l r => do let w ← wExpr (wTag w 2) l; wExpr w r
  | .mul l r => do let w ← wExpr (wTag w 3) l; wExpr w r

/-- The v1 `VmConstraint` forms at tags `0..3`. -/
def wVmConstraint (w : ByteArray) : VmConstraint → Except CanonError ByteArray
  | .gate body => wExpr (wTag w 0) body
  | .transition hi lo => do
      let w ← wIndex "VmConstraint::Transition.hi" (wTag w 1) hi
      wIndex "VmConstraint::Transition.lo" w lo
  | .boundary row body => wExpr (wTag (wTag w 2) (vmRowTag row)) body
  | .piBinding row col k => do
      let w ← wIndex "VmConstraint::PiBinding.col" (wTag (wTag w 3) (vmRowTag row)) col
      wIndex "VmConstraint::PiBinding.pi_index" w k

/-- `TableSem` at tags `0..8`.

⚠ Rust's tag `7` (`TableSem::UMemBoundaryCohort`) has **no `RowSemantics` constructor** — it is
Rust-only and unreachable from Lean. No served descriptor declares it. Named rather than silently
skipped: it is the one place the two algebras are not in bijection. -/
def wTableSem (w : ByteArray) : RowSemantics → Except CanonError ByteArray
  | .mainRow => .ok (wTag w 0)
  | .permutation => .ok (wTag w 1)
  | .rangeLimb bits => wIndex "TableSem::Range.bits" (wTag w 2) bits
  | .memAccess => .ok (wTag w 3)
  | .mapReconcile => .ok (wTag w 4)
  | .umemAccess => .ok (wTag w 5)
  | .umemBoundaryRow => .ok (wTag w 6)
  | .exactPublicRows rows =>
      wSeq "TableSem::ExactPublicRows.rows" (wTag w 8) rows fun w row =>
        wSeq "TableSem::ExactPublicRows.row" w row fun w v =>
          wU32 "TableSem::ExactPublicRows.cell" w v

/-- One declared table: id, name, arity, semantics. -/
def wTable (w : ByteArray) (t : TableDef) : Except CanonError ByteArray := do
  let w ← wIndex "TableDef2.id" w t.id.wireId
  let w ← wString "TableDef2.name" w t.name
  let w ← wIndex "TableDef2.arity" w t.arity
  wTableSem w t.sem

/-- `WindowExpr` at tags `0..4`. -/
def wWindowExpr (w : ByteArray) : WindowExpr → Except CanonError ByteArray
  | .loc c => wIndex "WindowExpr::Loc.column" (wTag w 0) c
  | .nxt c => wIndex "WindowExpr::Nxt.column" (wTag w 1) c
  | .const k => wI64 "WindowExpr::Const" (wTag w 2) k
  | .add l r => do let w ← wWindowExpr (wTag w 3) l; wWindowExpr w r
  | .mul l r => do let w ← wWindowExpr (wTag w 4) l; wWindowExpr w r

/-- `ChalExpr`. Tags `0..4` are byte-identical to `wWindowExpr`'s so the shared fragment encodes the
same way in both grammars; tag `5` is the CHALLENGE LEAF and carries its index.

⚑ Under `.chalAsConst` the leaf is written as the constant `i` — see `EncoderVariant`. -/
def wChalExpr (v : EncoderVariant) (w : ByteArray) : ChalExpr → Except CanonError ByteArray
  | .loc c => wIndex "ChalExpr::Loc.column" (wTag w 0) c
  | .nxt c => wIndex "ChalExpr::Nxt.column" (wTag w 1) c
  | .const k => wI64 "ChalExpr::Const" (wTag w 2) k
  | .chal i =>
      match v with
      | .chalAsConst => wI64 "ChalExpr::Chal.index" (wTag w 2) (Int.ofNat i)
      | _ => wIndex "ChalExpr::Chal.index" (wTag w 5) i
  | .add l r => do let w ← wChalExpr v (wTag w 3) l; wChalExpr v w r
  | .mul l r => do let w ← wChalExpr v (wTag w 4) l; wChalExpr v w r

/-- `HashInput` at tags `0..2`. -/
def wHashInput (w : ByteArray) : HashInput → Except CanonError ByteArray
  | .col c => wIndex "HashInput::Col.column" (wTag w 0) c
  | .digest k => wIndex "HashInput::Digest.index" (wTag w 1) k
  | .zero => .ok (wTag w 2)

/-- One hash site. ⚠ The record's field order is `digest_col`, `arity`, `inputs` — which is NOT the
Lean structure's declaration order (`digestCol`, `inputs`, `arity`). Writing the fields in
declaration order would produce a self-consistent wrong record. -/
def wHashSite (w : ByteArray) (s : VmHashSite) : Except CanonError ByteArray := do
  let w ← wIndex "VmHashSite.digest_col" w s.digestCol
  let w ← wIndex "VmHashSite.arity" w s.arity
  wSeq "VmHashSite.inputs" w s.inputs wHashInput

/-- One range tooth. -/
def wRange (w : ByteArray) (r : VmRange) : Except CanonError ByteArray := do
  let w ← wIndex "RangeSpec.wire" w r.wire
  wIndex "RangeSpec.bits" w r.bits

/-- The declared program pin: tag `0` = unpinned, tag `1` = a lane sequence of literals. -/
def wVkPin (w : ByteArray) : Option (List Int) → Except CanonError ByteArray
  | none => .ok (wTag w 0)
  | some p => wSeq "ProofBindSpec.vk_pin" (wTag w 1) p fun w v => wI64 "ProofBindSpec.vk_pin" w v

/-- What holds the commit lanes: tag `0` = bound (a lane sequence), tag `1` = a PORT carrying the two
NAMES of its cover.

⚑ Under `.portNamesElided` the names are dropped — see `EncoderVariant`. -/
def wCommitBinding (v : EncoderVariant) (w : ByteArray) :
    CommitBinding → Except CanonError ByteArray
  | .bound bs => wSeq "ProofBindSpec.bound" (wTag w 0) bs wExpr
  | .port c =>
      match v with
      | .portNamesElided => .ok (wTag w 1)
      | _ => do
          let w ← wString "ProofBindSpec.bound.port" (wTag w 1) c.port
          wString "ProofBindSpec.bound.seam" w c.seam

/-- The eight v2 constraint kinds at tags `0..7`. -/
def wConstraint (v : EncoderVariant) (w : ByteArray) :
    VmConstraint2 → Except CanonError ByteArray
  | .base c => wVmConstraint (wTag w 0) c
  | .lookup l => do
      let w ← wIndex "LookupSpec.table" (wTag w 1) l.table.wireId
      wSeq "LookupSpec.tuple" w l.tuple wExpr
  | .memOp m => do
      let w ← wExpr (wTag w 2) m.guard
      let w ← wExpr w m.addr
      let w ← wExpr w m.value
      let w ← wExpr w m.prevValue
      let w ← wExpr w m.prevSerial
      return wTag w (memKindTag m.kind)
  | .mapOp m => do
      let w ← wExpr (wTag w 3) m.guard
      let w ← wSeq "MapOpSpec.root" w (List.ofFn m.root) wExpr
      let w ← wExpr w m.key
      let w ← wExpr w m.value
      let w ← wSeq "MapOpSpec.new_root" w (List.ofFn m.newRoot) wExpr
      return wTag w (mapKindTag m.op)
  | .umemOp m => do
      let w ← wExpr (wTag w 4) m.guard
      let w ← wU32 "UMemOpSpec.domain" w (domainWire m.domain)
      let w ← wExpr w m.key
      let w ← wExpr w m.present
      let w ← wExpr w m.value
      let w ← wExpr w m.prevPresent
      let w ← wExpr w m.prevValue
      let w ← wExpr w m.prevSerial
      return wTag w (memKindTag m.kind)
  | .proofBind m => do
      let w ← wExpr (wTag w 5) m.guard
      let w ← wSeq "ProofBindSpec.commit" w m.commit wExpr
      let w ← wSeq "ProofBindSpec.vk" w m.vk wExpr
      let w ← wVkPin w m.vkPin
      wCommitBinding v w m.bound
  | .windowGate g => do
      let w ← wWindowExpr (wTag w 6) g.body
      return wTag w (if g.onTransition then 1 else 0)
  | .chalGate g => do
      let w ← wChalExpr v (wTag w 7) g.body
      return wTag w (if g.onTransition then 1 else 0)

/-! ## §7 — The record. -/

/-- Encode a typed DescriptorIR-v2 relation under the given variant. `.canonical` is the deployed
record; see `EncoderVariant` for why the other two exist. -/
def canonicalBytesWith (v : EncoderVariant) (d : EffectVmDescriptor2) :
    Except CanonError ByteArray := do
  let w := CANONICAL_MAGIC.foldl wTag ByteArray.empty
  let w := wU16 w CANONICAL_VERSION
  let w ← wString "EffectVmDescriptor2.name" w d.name
  let w ← wIndex "EffectVmDescriptor2.trace_width" w d.traceWidth
  let w ← wIndex "EffectVmDescriptor2.public_input_count" w d.piCount
  -- ⚑ The DECLARED CHALLENGE COUNT is inside the fingerprint, and it is DERIVED from the
  -- constraints (`DescriptorIR2.challengeCount`) rather than carried as a free field, so it cannot
  -- disagree with them. It is `0` on every descriptor served before the challenge leaf existed —
  -- a value, so the number is countable rather than absent.
  let w ← wIndex "EffectVmDescriptor2.challenges" w (challengeCount d)
  let w ← wSeq "EffectVmDescriptor2.tables" w d.tables wTable
  let w ← wSeq "EffectVmDescriptor2.constraints" w d.constraints (wConstraint v)
  let w ← wSeq "EffectVmDescriptor2.hash_sites" w d.hashSites wHashSite
  let w ← wSeq "EffectVmDescriptor2.ranges" w d.ranges wRange
  if w.size > MAX_CANONICAL_BYTES then
    .error (.recordTooLarge w.size MAX_CANONICAL_BYTES)
  else
    return w

/-- ⚑⚑ **THE CANONICAL BYTES OF A LEAN DESCRIPTOR TERM.** Rust twin:
`descriptor_ir2_canonical::canonical_effect_vm_descriptor2_bytes`. Byte-exact against it on every
served descriptor, on every run of
`scripts/check-descriptor-canonical-differential.sh`. -/
def canonicalBytes (d : EffectVmDescriptor2) : Except CanonError ByteArray :=
  canonicalBytesWith .canonical d

/-! ## §8 — ⚑⚑ THE CLOSED LOOP: a Lean term to its nine `vk_pin` lanes, with no Rust in the path. -/

/-- ⚑ **The semantic fingerprint of a Lean descriptor TERM.** `blake3::derive_key(ctx)` over the
canonical record, both hops Lean-authored. Rust twin:
`effect_vm_descriptor2_semantic_fingerprint`. -/
def fingerprintOf (d : EffectVmDescriptor2) : Except CanonError ByteArray := do
  return Blake3.descriptor2Fingerprint (← canonicalBytes d)

/-- The fingerprint as the lowercase hex the tooling prints. -/
def fingerprintHexOf (d : EffectVmDescriptor2) : Except CanonError String := do
  return Blake3.toHex (← fingerprintOf d)

/-- ⚑⚑ **THE `vk_pin` OF A LEAN DESCRIPTOR TERM** — the nine base-`2^29` `Faithful9` lanes, computed
end to end from the term. This is the value thirteen `*_VK_LANES` constants across six modules are a
transcription of; it can now be written as this call.

`none` on the (unreachable) case of a digest that is not 32 bytes — a short digest padded to 32 would
encode to lanes that look fine and mean nothing. -/
def vkPinLanesOf (d : EffectVmDescriptor2) : Except CanonError (Option (List Int)) := do
  return VkPinCompute.vkPinLanes (← canonicalBytes d)

/-- The same, as `Nat`s (the shape `key_limbs9` reports and the differential compares). -/
def vkPinLanesNatOf (d : EffectVmDescriptor2) : Except CanonError (Option (List Nat)) := do
  return VkPinCompute.vkPinLanesNat (← canonicalBytes d)

/-! ## §9 — Shape tripwires, as named theorems.

⚠ Named, not `#guard`ed: a `#guard` checks one closed instance, leaves no term anything can build on,
and is invisible to axiom accounting (`metatheory/docs/GUARD-DISCIPLINE.md`). -/

/-- The discriminator is the eight ASCII bytes of `DREGGIR2`. -/
theorem canonical_magic_is_dreggir2 :
    CANONICAL_MAGIC = "DREGGIR2".toUTF8.toList.map UInt8.toNat := by native_decide

/-- ⚑ **THE FIXED-WIDTH PROPERTY, AS A GENERAL FACT.** `pushLE` appends exactly `width` bytes
whatever the value — stated for every width and every value rather than checked at one instance. It
is what makes the record a FIXED record: a reader advances by a width it knows before it has seen the
value, so no field's length depends on its content and there is no place for a length to be inferred
wrongly. -/
theorem pushLE_size (w : ByteArray) (width n : Nat) :
    (pushLE w width n).size = w.size + width := by
  induction width generalizing w n with
  | zero => simp [pushLE]
  | succ k ih => simp [pushLE, ih, ByteArray.size_push]; omega

/-- Every `u64` index costs exactly eight bytes. -/
theorem wIndex_size {f : String} {w w' : ByteArray} {n : Nat} (h : wIndex f w n = .ok w') :
    w'.size = w.size + 8 := by
  unfold wIndex at h
  split at h
  · injection h with h; subst h; exact pushLE_size _ _ _
  · exact absurd h (by simp)

/-- Every `i64` coefficient costs exactly eight bytes — the same as an index, whatever its sign. -/
theorem wI64_size {f : String} {w w' : ByteArray} {v : Int} (h : wI64 f w v = .ok w') :
    w'.size = w.size + 8 := by
  unfold wI64 at h
  split at h
  · injection h with h; subst h; exact pushLE_size _ _ _
  · exact absurd h (by simp)

/-- ⚑ **A STRING COSTS ITS LENGTH PREFIX PLUS ITS UTF-8 BYTES** — `String.toUTF8.size`, NOT
`String.length`. The two agree on ASCII and disagree on every other name, and an encoder that wrote
the character count would produce a record whose own reader walks off the end of the field. Stated
generally so the trap is closed for every string in the record, not sampled. -/
theorem wString_size {f : String} {w w' : ByteArray} {s : String} (h : wString f w s = .ok w') :
    w'.size = w.size + 8 + s.toUTF8.size := by
  unfold wString at h
  simp only [bind, Except.bind] at h
  split at h
  · exact absurd h (by simp)
  · rename_i wm hm
    injection h with h
    subst h
    rw [ByteArray.size_append, wIndex_size hm]

/-- The two's-complement image is a genuine 64-bit pattern. -/
theorem i64Bits_lt (v : Int) : i64Bits v < 2 ^ 64 :=
  Nat.mod_lt _ (by norm_num)

/-- ⚑ **`0` and `-1` are the two ends of the `i64` image**, and they are distinct — the fact a
sign-blind encoder (one that wrote `Int.toNat`) would break. A gate coefficient of `-1` is the single
most common constant in the served tree. -/
theorem i64Bits_neg_one : i64Bits (-1) = 2 ^ 64 - 1 := by decide

/-- Zero is zero. -/
theorem i64Bits_zero : i64Bits 0 = 0 := by decide

#assert_compiled canonical_magic_is_dreggir2
#assert_axioms pushLE_size
#assert_axioms wIndex_size
#assert_axioms wI64_size
#assert_axioms wString_size
#assert_axioms i64Bits_lt
#assert_axioms i64Bits_neg_one
#assert_axioms i64Bits_zero

/-! ## §10 — ⚑ The falsifiers, and the proof that they have content.

Two encoders that are wrong in one place each. The claim a falsifier must support is not "it differs
somewhere" — it is *"it agrees on the easy inputs and is caught on a real one"*, which is what makes
its silence on the easy inputs informative. The corpus-scale half of that lives in
`scripts/check-descriptor-canonical-differential.sh` (155 agreements / 4 divergences for
`.chalAsConst`, 156 / 3 for `.portNamesElided`, all recomputed); the WITNESSES live here. -/

/-- A descriptor with no `chalGate` and no ported `proofBind` — the shape 152 of the 159 served
descriptors have. Both falsifiers are byte-identical to the truth on it. -/
def demoPlain : EffectVmDescriptor2 :=
  { name := "canon-demo-plain", traceWidth := 2, piCount := 1
  , tables := [mainTableDef 2, rangeTableDef 30]
  , constraints :=
      [ .base (.gate (.add (.var 0) (.mul (.const (-1)) (.var 1))))
      , .base (.transition 0 0)
      , .base (.boundary .first (.var 0))
      , .base (.piBinding .last 1 0)
      , .lookup ⟨.range, [.var 0]⟩
      , .windowGate ⟨.add (.nxt 0) (.mul (.const (-1)) (.loc 1)), true⟩ ]
  , hashSites := [], ranges := [⟨1, 30⟩] }

/-- The same descriptor with ONE challenge gate added — the feature `.chalAsConst` drops. -/
def demoChal : EffectVmDescriptor2 :=
  { demoPlain with
    name := "canon-demo-chal"
    constraints := demoPlain.constraints ++
      [ .chalGate ⟨.add (.mul (.chal 0) (.loc 0)) (.mul (.chal 1) (.loc 1)), false⟩ ] }

/-- A minimal ported `proofBind` at the deployed lane floor — the feature `.portNamesElided` drops. -/
def demoPortedBind : ProofBind :=
  { guard := .const 1
  , commit := (List.range PROOF_BIND_MIN_LANES).map EmittedExpr.var
  , vk := (List.range PROOF_BIND_MIN_LANES).map (fun i => EmittedExpr.var (i + 8))
  , vkPin := none
  , bound := .port ⟨"commit", "canon-demo-seam"⟩ }

/-- The plain descriptor plus one ported `proofBind`. -/
def demoPort : EffectVmDescriptor2 :=
  { demoPlain with
    name := "canon-demo-port"
    constraints := demoPlain.constraints ++ [ .proofBind demoPortedBind ] }

/-- The ported seam is well-formed at the deployed floor, so the divergence below is a fact about a
descriptor the Rust doors ADMIT — not one they would refuse anyway. -/
theorem demoPortedBind_widthOk : demoPortedBind.widthOk = true := by decide

/-- ⚑ **`.chalAsConst` IS SILENT ON THE EASY INPUT.** It reproduces the true record byte for byte on
a descriptor carrying no challenge gate — which is why its silence there says nothing. -/
theorem chalAsConst_agrees_without_a_chal_gate :
    canonicalBytesWith .chalAsConst demoPlain = canonicalBytes demoPlain := by native_decide

/-- ⚑ **AND IT IS CAUGHT BY ONE.** Add a single challenge gate and the records differ: the leaf is
inside the fingerprint, so a descriptor that reads challenge `i` cannot fingerprint-match one that
multiplies by the constant `i`. -/
theorem chalAsConst_diverges_on_a_chal_gate :
    canonicalBytesWith .chalAsConst demoChal ≠ canonicalBytes demoChal := by native_decide

/-- ⚑ **`.portNamesElided` IS SILENT ON THE EASY INPUT.** -/
theorem portNamesElided_agrees_without_a_ported_bind :
    canonicalBytesWith .portNamesElided demoPlain = canonicalBytes demoPlain := by native_decide

/-- ⚑ **AND IT IS CAUGHT BY ONE.** The two names a port carries are inside the fingerprint, so two
descriptors differing only in which seam is claimed to cover a port have different protocol
identities. That is the whole content of the 2026-08-10 flag day, and this is the encoder for which
it is false. -/
theorem portNamesElided_diverges_on_a_ported_bind :
    canonicalBytesWith .portNamesElided demoPort ≠ canonicalBytes demoPort := by native_decide

/-- ⚑ **THE TWO FALSIFIERS ARE NOT THE SAME FALSIFIER.** Each is caught by an input the other passes,
so neither is a redundant copy: `.portNamesElided` reproduces the truth on the challenge-bearing
descriptor and `.chalAsConst` reproduces it on the ported one. -/
theorem the_falsifiers_are_independent :
    canonicalBytesWith .portNamesElided demoChal = canonicalBytes demoChal ∧
      canonicalBytesWith .chalAsConst demoPort = canonicalBytes demoPort := by
  constructor <;> native_decide

/-- ⚑ **THE ENCODER IS NOT VACUOUS.** It produces bytes on a real descriptor, they open with the
version-4 `DREGGIR2` header, and the whole record is longer than that header — a "succeeds" that did
not check the output would be satisfied by an encoder returning the empty array. -/
theorem canonicalBytes_demoPort_has_the_header :
    ((canonicalBytes demoPort).map (fun b => (b.toList.take 10, decide (10 < b.size))))
      = .ok ((CANONICAL_MAGIC ++ [CANONICAL_VERSION, 0]).map UInt8.ofNat, true) := by
  native_decide

#assert_compiled chalAsConst_agrees_without_a_chal_gate
#assert_compiled chalAsConst_diverges_on_a_chal_gate
#assert_compiled portNamesElided_agrees_without_a_ported_bind
#assert_compiled portNamesElided_diverges_on_a_ported_bind
#assert_compiled the_falsifiers_are_independent
#assert_compiled canonicalBytes_demoPort_has_the_header
#assert_axioms demoPortedBind_widthOk

end Dregg2.Circuit.DescriptorCanonical
