/-
# CheckDescriptorCanonical — the Lean canonical ENCODER against the deployed Rust one, over EVERY
# DescriptorIR-v2 record this tree serves.

⚑ **THIS IS THE GATE, NOT A TEST RUN.** Driven by
`scripts/check-descriptor-canonical-differential.sh`, which regenerates its Rust side on every
invocation with `cargo run -p dregg-circuit --example descriptor_canonical_dump`.

## ⚑ WHAT MAKES IT A DIFFERENTIAL AND NOT A FIXTURE COMPARISON

**Both sides compute from the same input: the descriptor JSON on disk.** Rust parses it
(`parse_vm_descriptor2`) and encodes it (`canonical_effect_vm_descriptor2_bytes`); Lean parses it
(`DescriptorCanonicalJson.parseDescriptor`) and encodes it
(`DescriptorCanonical.canonicalBytes`). Nothing is stored anywhere: there is no expected value to go
stale, and a sibling lane's uncommitted re-emit moves BOTH sides identically, so it cannot flatter
the result. `DREGG_DESCRIPTOR_ROOT` retargets both at a materialised tree together.

## ⚑ IT CHECKS THE WHOLE CHAIN, NOT ONLY THE ENCODER

A `vk_pin` is `descriptor → canonical bytes → BLAKE3 derive-key fingerprint → nine base-2^29 lanes`.
`scripts/check-blake3-differential.sh` gates hops 2 and 3 *given* canonical bytes; this gates hop 1
and then re-runs 2 and 3 **from the Lean-encoded bytes**, so the composite claim — *a Lean
`EffectVmDescriptor2` term produces the same nine lanes the deployed Rust tool prints* — is checked
end to end rather than inferred from two half-results.

## ⚠ WHAT DISAGREEMENT WOULD MEAN

A wrong encoder fails **silently**: every fingerprint it computes is self-consistent and wrong. That
is *"two agreeing transcriptions are not two witnesses; they are one witness copied"*, generated at
scale. Do not "fix" a red here by re-emitting descriptors — the two sides read the SAME file.

## ⚑ THE FALSIFIER ARM

Arm 4 measures the two deliberately-wrong encoders (`DescriptorCanonical.EncoderVariant`) across the
corpus and REFUSES unless each one both **agrees** with the truth on most descriptors and
**diverges** on at least one. A falsifier that agrees everywhere has become a no-op — the way an
adversary dies while its gate stays green — and one that agrees nowhere is not testing the feature it
names, it is merely a different encoder.

Usage: `lake env lean --run CheckDescriptorCanonical.lean <dump.tsv> <descriptor-root> [<min-rows>]`

Each line of `dump.tsv` is `name \t path \t canonical-hex \t fingerprint-hex \t l0,…,l8`.
-/
import Dregg2.Circuit.DescriptorCanonicalJson

open Dregg2.Crypto.Blake3
open Dregg2.Circuit.DescriptorIR2
open Dregg2.Circuit.DescriptorCanonical
open Dregg2.Circuit.DescriptorCanonicalJson

/-- One dumped record: what the DEPLOYED Rust computed, and where its input lives. -/
structure Row where
  /-- The descriptor's declared name. -/
  name : String
  /-- Its path under the descriptor root — the input BOTH sides read. -/
  path : String
  /-- The canonical bytes Rust encoded from that file. -/
  canonical : ByteArray
  /-- The fingerprint Rust took over exactly those bytes. -/
  fingerprint : String
  /-- The nine base-`2^29` lanes Rust's `key_limbs9` packs that fingerprint into. -/
  lanes : List Nat

/-- Parse one TSV line; `none` on a malformed row, which the caller treats as a REFUSAL and never as
a row to skip — a parser that silently drops rows is a gate that shrinks its own corpus. -/
def parseRow (line : String) : Option Row :=
  match line.splitOn "\t" with
  | [name, path, canonHex, fpHex, laneCsv] => do
    let bytes ← ofHex canonHex
    let lanes ← (laneCsv.splitOn ",").mapM String.toNat?
    if lanes.length ≠ 9 then none
    else some { name, path, canonical := bytes, fingerprint := fpHex, lanes }
  | _ => none

/-- The index of the first differing byte, and the two bytes there. -/
def firstDiff (a b : ByteArray) : Option (Nat × Nat × Nat) := Id.run do
  let n := min a.size b.size
  for i in [0:n] do
    if a[i]! != b[i]! then return some (i, (a[i]!).toNat, (b[i]!).toNat)
  if a.size != b.size then return some (n, a.size, b.size)
  return none

/-- ByteArray equality, by content. -/
def bytesEq (a b : ByteArray) : Bool := a.size == b.size && a.data == b.data

def main (args : List String) : IO UInt32 := do
  let some (dumpPath : String) := args[0]? | do
    IO.eprintln "usage: CheckDescriptorCanonical <dump.tsv> <descriptor-root> [<min-rows>]"
    return 2
  let some (root : String) := args[1]? | do
    IO.eprintln "usage: CheckDescriptorCanonical <dump.tsv> <descriptor-root> [<min-rows>]"
    return 2
  let minRows := (args[2]?.bind String.toNat?).getD 100
  let lines := (← IO.FS.lines dumpPath).filter (fun l => ¬ l.isEmpty)

  let mut rows : Array Row := #[]
  for line in lines do
    match parseRow line with
    | some r => rows := rows.push r
    | none =>
      IO.eprintln s!"REFUSED: malformed dump row (a dropped row is a shrunk corpus): {line.take 120}"
      return 2

  if rows.size < minRows then
    IO.eprintln s!"REFUSED: {rows.size} descriptors in the dump, floor is {minRows} — a differential over a truncated tree is not the claim it reads as"
    return 2

  let mut badParse : Array String := #[]
  let mut badBytes : Array String := #[]
  let mut badFp : Array String := #[]
  let mut badLanes : Array String := #[]
  -- The falsifier census: (agreements, divergences) for each wrong encoder.
  let mut chalAgree := 0
  let mut chalDiverge := 0
  let mut portAgree := 0
  let mut portDiverge := 0
  let mut totalCanonical := 0
  let mut totalJson := 0

  for r in rows do
    let src ← IO.FS.readBinFile (System.FilePath.mk root / r.path)
    totalJson := totalJson + src.size
    match parseDescriptor src with
    | .error e =>
        badParse := badParse.push s!"  {r.path}\n    descriptor `{r.name}`\n    Lean reader refused: {e}"
    | .ok d =>
      match canonicalBytes d with
      | .error e =>
          badBytes := badBytes.push s!"  {r.path}\n    descriptor `{r.name}`\n    Lean encoder refused: {e.message}"
      | .ok leanBytes =>
        totalCanonical := totalCanonical + leanBytes.size
        if ¬ bytesEq leanBytes r.canonical then
          let where_ := match firstDiff leanBytes r.canonical with
            | some (i, x, y) => s!"first difference at byte {i}: lean {x}, rust {y}"
            | none => "sizes and contents agree — but bytesEq said otherwise"
          badBytes := badBytes.push
            s!"  {r.path}\n    descriptor `{r.name}`\n    lean {leanBytes.size} canonical bytes, rust {r.canonical.size}\n    {where_}"
        -- ⚑ The rest of the chain, run on the LEAN-encoded bytes rather than on Rust's, so a
        -- disagreement anywhere in `descriptor → bytes → fingerprint → lanes` is caught here.
        let fp := toHex (descriptor2Fingerprint leanBytes)
        if fp ≠ r.fingerprint then
          badFp := badFp.push
            s!"  {r.path}\n    descriptor `{r.name}`\n    rust: {r.fingerprint}\n    lean: {fp}"
        match Dregg2.Circuit.VkPinCompute.vkPinLanesNat leanBytes with
        | none => badLanes := badLanes.push s!"  {r.path}: Lean produced a digest that is not 32 bytes"
        | some ls =>
          if ls ≠ r.lanes then
            badLanes := badLanes.push
              s!"  {r.path}\n    descriptor `{r.name}`\n    rust key_limbs9:  {r.lanes}\n    lean end-to-end:  {ls}"
        -- ⚑ ARM 4: the falsifiers, measured on the same real inputs.
        match canonicalBytesWith .chalAsConst d with
        | .ok b => if bytesEq b leanBytes then chalAgree := chalAgree + 1
                   else chalDiverge := chalDiverge + 1
        | .error _ => chalDiverge := chalDiverge + 1
        match canonicalBytesWith .portNamesElided d with
        | .ok b => if bytesEq b leanBytes then portAgree := portAgree + 1
                   else portDiverge := portDiverge + 1
        | .error _ => portDiverge := portDiverge + 1

  let mut failed := false

  unless badParse.isEmpty do
    failed := true
    IO.eprintln s!"FAIL: the Lean reader refused {badParse.size} of {rows.size} descriptors the deployed Rust reader accepted"
    for b in badParse do IO.eprintln b
    IO.eprintln "⚠ A refusal here is NOT a pass with a caveat: the corpus this gate reports on is"
    IO.eprintln "  smaller than its summary line claims until every row reads."

  unless badBytes.isEmpty do
    failed := true
    IO.eprintln s!"FAIL: {badBytes.size} of {rows.size} descriptors disagree between the Lean canonical encoder and the deployed Rust one"
    for b in badBytes do IO.eprintln b
    IO.eprintln "⚠ A self-consistent wrong encoder is the failure this gate exists to catch. Do NOT"
    IO.eprintln "  'fix' it by re-emitting descriptors: the two sides read the SAME file."

  unless badFp.isEmpty do
    failed := true
    IO.eprintln s!"FAIL: {badFp.size} of {rows.size} fingerprints disagree between the pure-Lean chain and the deployed Rust one"
    for b in badFp do IO.eprintln b

  unless badLanes.isEmpty do
    failed := true
    IO.eprintln s!"FAIL: {badLanes.size} of {rows.size} vk_pin lane vectors disagree between the pure-Lean chain and Rust key_limbs9"
    for b in badLanes do IO.eprintln b

  -- ⚑ THE FALSIFIER REFUSAL. Both halves bite: a falsifier that never diverges has become a no-op,
  -- and one that never agrees is a trivially-different encoder rather than a probe of one feature.
  for (nm, agree, diverge, feature) in
      [ ("chalAsConst", chalAgree, chalDiverge, "the challenge leaf"),
        ("portNamesElided", portAgree, portDiverge, "a port's two cover names") ] do
    if diverge == 0 then
      failed := true
      IO.eprintln s!"FAIL: the `{nm}` falsifier diverged on NONE of {rows.size} served descriptors."
      IO.eprintln s!"  It is a no-op on this corpus, so its silence proves nothing about {feature}"
      IO.eprintln "  being inside the canonical record. Either the feature has left the served tree"
      IO.eprintln "  (then this arm needs a synthetic carrier) or the falsifier stopped falsifying."
    if agree == 0 then
      failed := true
      IO.eprintln s!"FAIL: the `{nm}` falsifier agreed with the truth on NONE of {rows.size} served descriptors."
      IO.eprintln "  A falsifier that differs everywhere is a different encoder, not a probe: its"
      IO.eprintln "  divergence carries no information about the one feature it is supposed to drop."

  if failed then return 1

  IO.println s!"descriptor canonical differential: {rows.size} served descriptors"
  IO.println s!"  input read by BOTH sides: {totalJson} JSON bytes under {root}"
  IO.println s!"  hop 1 PASS — Lean canonicalBytes == deployed canonical_effect_vm_descriptor2_bytes"
  IO.println s!"               on all {rows.size}, {totalCanonical} canonical bytes, byte for byte"
  IO.println s!"  hop 2 PASS — pure-Lean blake3Derive over the LEAN-encoded bytes matches the deployed fingerprint on all {rows.size}"
  IO.println s!"  hop 3 PASS — Lean keyToLanes9 matches Rust key_limbs9 on all {rows.size}"
  IO.println s!"  falsifiers  — chalAsConst: {chalAgree} agree / {chalDiverge} diverge;  portNamesElided: {portAgree} agree / {portDiverge} diverge"
  IO.println s!"  ⇒ a Lean EffectVmDescriptor2 term is fingerprintable end to end, with no Rust in the path"
  return 0
