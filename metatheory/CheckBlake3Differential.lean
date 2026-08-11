/-
# CheckBlake3Differential — the pure-Lean `vk_pin` computation against the deployed Rust one, over
# EVERY DescriptorIR-v2 record this tree serves.

⚑ **THIS IS THE GATE, NOT A TEST RUN.** Driven by `scripts/check-blake3-differential.sh`, which
regenerates its input on every invocation with
`cargo run -p dregg-circuit --example descriptor_canonical_dump`. Neither side is a committed
fixture: Rust re-encodes and re-hashes every descriptor on disk, Lean re-derives the same values from
the same bytes, and the two are compared. A stale expectation cannot survive here because there is no
expectation stored anywhere.

## ⚑ IT CHECKS THE WHOLE PIN, NOT ONLY THE HASH

A `vk_pin` is `canonical bytes → BLAKE3 derive-key fingerprint → nine base-2^29 lanes`, and the
transcription defect lives on BOTH hops — six files in this tree carried their own copy of the lane
packing, and THIRTEEN `*_VK_LANES` constants across six Lean modules carry copies of the resulting numbers. So this driver checks:

  1. `Dregg2.Crypto.Blake3.descriptor2Fingerprint` (pure Lean) against the deployed Rust fingerprint;
  2. `Dregg2.Circuit.KeyLanes9.keyToLanes9` — the LEAN-AUTHORED encoder the AIRs are proved against,
     the one with `keyToLanes9_injective` — against Rust's `key_limbs9`, on all 158 real
     fingerprints.

Hop 2 is not implied by hop 1. Equal bytes say nothing about two lane encoders agreeing, and
"agreeing" is exactly what six hand-rolled copies were assumed to do.

⚠ **WHAT DISAGREEMENT WOULD MEAN.** A wrong `blake3Derive` fails silently — every pin it computes is
self-consistent and wrong. That is *"two agreeing transcriptions are not two witnesses; they are one
witness copied"*, generated at scale. The vectors in `Dregg2.Crypto.Blake3Kat` are the third-party
half (the BLAKE3 team's own file); this is the *deployed-input* half, on the exact byte strings the
tree's fingerprints are taken over — lengths, embedded names, tag bytes and all.

Usage: `lake env lean --run CheckBlake3Differential.lean <dump.tsv> [<min-rows>]`

Each line of `dump.tsv` is `name \t path \t canonical-hex \t fingerprint-hex \t l0,…,l8`.

⚠ A walk over an empty or truncated dump must REFUSE, not report PASS: `<min-rows>` (default 100)
is the vacuity floor, and a dump that parses to zero rows exits non-zero from the producer too.
-/
import Dregg2.Crypto.Blake3Compute
import Dregg2.Circuit.VkPinCompute

open Dregg2.Crypto.Blake3

/-- One dumped record. -/
structure Row where
  /-- The descriptor's declared name. -/
  name : String
  /-- Its path under the descriptor root, for the failure message. -/
  path : String
  /-- Its canonical DescriptorIR-v2 bytes. -/
  canonical : ByteArray
  /-- The fingerprint the deployed Rust library computed over exactly those bytes. -/
  expected : String
  /-- The nine base-`2^29` lanes Rust's `key_limbs9` packs that fingerprint into — the `vk_pin`. -/
  expectedLanes : List Nat

/-- Parse one TSV line; `none` on a malformed row (which the caller treats as a REFUSAL, never as a
row to skip — a parser that silently drops rows is a gate that shrinks its own corpus). -/
def parseRow (line : String) : Option Row :=
  match line.splitOn "\t" with
  | [name, path, canonHex, fpHex, laneCsv] => do
    let bytes ← ofHex canonHex
    let lanes ← (laneCsv.splitOn ",").mapM String.toNat?
    if lanes.length ≠ 9 then none
    else some { name, path, canonical := bytes, expected := fpHex, expectedLanes := lanes }
  | _ => none

/-- The Lean-side pin computation under test. ⚑ It is the LIBRARY function
`Dregg2.Circuit.VkPinCompute.vkPinLanesNat`, not a local re-spelling of it — a driver that carried
its own copy would be comparing Rust against a twin of the thing it is supposed to be gating. -/
def leanPin (canonical : ByteArray) : Option (List Nat) :=
  Dregg2.Circuit.VkPinCompute.vkPinLanesNat canonical

def main (args : List String) : IO UInt32 := do
  let some (dumpPath : String) := args[0]? | do
    IO.eprintln "usage: CheckBlake3Differential <dump.tsv> [<min-rows>]"
    return 2
  let minRows := (args[1]?.bind String.toNat?).getD 100
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

  let mut badHash : Array String := #[]
  let mut badLanes : Array String := #[]
  let mut totalBytes := 0
  for r in rows do
    totalBytes := totalBytes + r.canonical.size
    let got := toHex (descriptor2Fingerprint r.canonical)
    if got ≠ r.expected then
      badHash := badHash.push s!"  {r.path}\n    descriptor `{r.name}` ({r.canonical.size} canonical bytes)\n    rust: {r.expected}\n    lean: {got}"
    match leanPin r.canonical with
    | none => badLanes := badLanes.push s!"  {r.path}: Lean produced a digest that is not 32 bytes"
    | some ls =>
      if ls ≠ r.expectedLanes then
        badLanes := badLanes.push s!"  {r.path}\n    descriptor `{r.name}`\n    rust key_limbs9:   {r.expectedLanes}\n    lean keyToLanes9:  {ls}"

  if badHash.isEmpty && badLanes.isEmpty then
    IO.println s!"blake3 differential: {rows.size} served descriptors, {totalBytes} canonical bytes"
    IO.println s!"  context: {descriptor2FingerprintContext}"
    IO.println s!"  hop 1 PASS — pure-Lean blake3Derive agrees with the deployed Rust fingerprint on all {rows.size}"
    IO.println s!"  hop 2 PASS — Lean keyToLanes9 agrees with Rust key_limbs9 on all {rows.size} fingerprints"
    IO.println s!"  ⇒ the whole vk_pin value (canonical bytes → fingerprint → nine lanes) is computable in Lean"
    return 0
  else
    unless badHash.isEmpty do
      IO.eprintln s!"FAIL: {badHash.size} of {rows.size} descriptors disagree between pure-Lean blake3Derive and the deployed Rust fingerprint"
      for b in badHash do IO.eprintln b
      IO.eprintln "⚠ A self-consistent wrong hash is the failure this gate exists to catch. Do not"
      IO.eprintln "  'fix' it by re-emitting descriptors: the two sides read the SAME bytes."
    unless badLanes.isEmpty do
      IO.eprintln s!"FAIL: {badLanes.size} of {rows.size} fingerprints disagree between Lean keyToLanes9 and Rust key_limbs9"
      for b in badLanes do IO.eprintln b
    return 1
