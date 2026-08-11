/-
# Dregg2.Crypto.Blake3Compute — BLAKE3 in pure Lean, hash / keyed / **derive-key**.

## What this is, and what it is NOT

⚑ **This is a COMPUTABLE definition sitting BESIDE `Dregg2.Crypto.PortalFloor.Blake3Kernel`, never
in place of it.** The floor stays uninterpreted on purpose: it carries `collisionHard` /
`noCollision`, and a *computable* floor would put hash evaluation inside proofs — the Poseidon2
reduction-bomb shape (one permutation measured at 47.6 GB / 68 min). Nothing here is imported by a
soundness argument. It exists so that a value a Rust tool computes and a human **types into Lean**
can instead be *computed in Lean*.

⚠ **TRUST CLASS: COMPILER-TRUSTED, NOT KERNEL-TRUSTED.** Every fact this module pins about real
inputs is `by native_decide` + `#assert_compiled` (see `Blake3Kat.lean`). Read the label literally:
"true by compiled evaluation, and I am recording that the compiler is in the trust base." A pin
computed here is an **IDENTITY** claim — *this Lean function agrees with the deployed hash* — and
never a soundness one. It buys exactly one thing, which the transcribed form did not have: the value
cannot go stale silently.

⚑ **WHY THIS PORTS WHERE POSEIDON2 DID NOT.** BLAKE3 is add-rotate-xor over `UInt32`, which is what
Lean's machine words do well. Poseidon2's `perm` explodes because `whnf` zeta-expands its `let`
helpers over field arithmetic; there is no field arithmetic here. That asymmetry is the whole reason
Route 2 was viable and the portal route was not.

## ⚑ NO `@[implemented_by]` TWIN, DELIBERATELY

The brief that opened this work allowed "an `@[implemented_by]` fast twin **if** the pure def is too
slow to evaluate." It is not: this *is* the machine-word definition, so there is nothing to twin.
That is the stronger outcome and not a shortcut — a twin means two objects that must agree, and
`Dregg2.Crypto.MlDsaRingTwinDifferential` records what that costs: while `@[implemented_by]` sat on
the pure def, `fastNtt x == ntt x` compared `fastNtt` with `fastNtt` and printed `true` for **any**
twin. One object cannot drift from itself. The compiler is still in the trust base (that is what
`native_decide` means and what `#assert_compiled` records), but no second definition is.

## The portal route, and why it is not taken

⚠ The eighteen `@[extern]` declarations in `PortalFloor.lean` **do not resolve** — measured, `#eval
blake3HashExtern [1,2,3]` under `lake env lean` errors with *"Could not find native implementation of
external declaration"*. They bind symbols for `sel4/dregg-pd/executor-pd/crypto-floor/`, a `no_std`
staticlib cross-built for a seL4 protection domain, and `metatheory/lakefile.toml` has no
`extern_lib` and no `moreLinkArgs`. All 494 `@[export]`s in the tree run Rust → Lean. Do not revive
"route it through the portal"; the probe already killed it.

## THE SPEC THIS IMPLEMENTS

BLAKE3 (the reference implementation's `reference_impl.rs`), at 32-bit words:

* `compress` — 7 rounds of the 8-`g` mixing schedule over a 16-word state, then the feed-forward
  `state[i] ^= state[i+8]; state[i+8] ^= cv[i]`;
* chunks of `CHUNK_LEN = 1024` bytes, each 64-byte block chained, first block flagged `CHUNK_START`
  and last `CHUNK_END`, chunk index as the 64-bit counter;
* the chunk CVs merged by the reference's stack rule (`while total_chunks & 1 == 0`), parent nodes
  compressed under `PARENT` with the key as chaining value and counter `0`;
* the root node's output block re-compressed under `ROOT` with an incrementing output-block counter
  — the extended-output (XOF) path, which is what the official test vectors exercise at 131 bytes.

⚠ **derive-key mode is a TWO-PASS construction and is the mode this repo actually uses.** Every
descriptor fingerprint, every `vk_pin`, is `blake3::Hasher::new_derive_key(ctx)`: hash the context
string under `DERIVE_KEY_CONTEXT` to 32 bytes, then hash the material under `DERIVE_KEY_MATERIAL`
keyed by those bytes. The flag bits differ from plain-hash mode, so **an implementation checked only
against generic hash-mode KATs would pass and still produce wrong pins.** `Blake3Kat.lean` pins all
three modes over all 35 official vectors for exactly that reason.
-/

namespace Dregg2.Crypto.Blake3

/-! ## §1 — Constants (BLAKE3 §2.1). -/

/-- Digest length in bytes. -/
def OUT_LEN : Nat := 32
/-- Key length in bytes (keyed and derive-key modes). -/
def KEY_LEN : Nat := 32
/-- Compression-function block length in bytes. -/
def BLOCK_LEN : Nat := 64
/-- Chunk length in bytes; a chunk is the unit the tree's leaves cover. -/
def CHUNK_LEN : Nat := 1024

/-- Flag: this block is the first of its chunk. -/
def CHUNK_START : UInt32 := 1
/-- Flag: this block is the last of its chunk. -/
def CHUNK_END : UInt32 := 2
/-- Flag: this compression is an interior tree node, not a chunk block. -/
def PARENT : UInt32 := 4
/-- Flag: this compression produces the extended output of the root node. -/
def ROOT : UInt32 := 8
/-- Base flag for keyed-hash mode. -/
def KEYED_HASH : UInt32 := 16
/-- Base flag for the FIRST pass of derive-key mode (hashing the context string). -/
def DERIVE_KEY_CONTEXT : UInt32 := 32
/-- Base flag for the SECOND pass of derive-key mode (hashing the key material). -/
def DERIVE_KEY_MATERIAL : UInt32 := 64

/-- The BLAKE3 initialisation vector (the SHA-256 IV). -/
def IV : Array UInt32 :=
  #[0x6A09E667, 0xBB67AE85, 0x3C6EF372, 0xA54FF53A,
    0x510E527F, 0x9B05688C, 0x1F83D9AB, 0x5BE0CD19]

/-- The message-word permutation applied between rounds. -/
def MSG_PERMUTATION : Array Nat :=
  #[2, 6, 3, 10, 7, 0, 4, 13, 1, 11, 12, 5, 9, 14, 15, 8]

/-! ## §2 — Word plumbing. -/

/-- Rotate a 32-bit word right by `n` (used only at `n ∈ {7, 8, 12, 16}`). -/
@[inline] def rotr (x : UInt32) (n : UInt32) : UInt32 :=
  (x >>> n) ||| (x <<< (32 - n))

/-- Byte `i` of a `ByteArray`, or `0` at or past `stop` — the zero padding a short final block gets. -/
@[inline] def byteAt (b : ByteArray) (stop i : Nat) : UInt8 :=
  if i < stop && i < b.size then b.get! i else 0

/-- The sixteen little-endian message words of the 64-byte block at `off`, zero-padded past `stop`. -/
def wordsFrom (b : ByteArray) (off stop : Nat) : Array UInt32 :=
  Array.ofFn (n := 16) fun i =>
    let j := off + 4 * i.val
    (byteAt b stop j).toUInt32
      ||| ((byteAt b stop (j + 1)).toUInt32 <<< 8)
      ||| ((byteAt b stop (j + 2)).toUInt32 <<< 16)
      ||| ((byteAt b stop (j + 3)).toUInt32 <<< 24)

/-- The eight key words of a 32-byte key, little-endian. -/
def wordsFromKey (k : ByteArray) : Array UInt32 :=
  Array.ofFn (n := 8) fun i =>
    let j := 4 * i.val
    (byteAt k k.size j).toUInt32
      ||| ((byteAt k k.size (j + 1)).toUInt32 <<< 8)
      ||| ((byteAt k k.size (j + 2)).toUInt32 <<< 16)
      ||| ((byteAt k k.size (j + 3)).toUInt32 <<< 24)

/-- A 32-bit word as four little-endian bytes. -/
@[inline] def u32le (w : UInt32) : ByteArray :=
  ⟨#[w.toUInt8, (w >>> 8).toUInt8, (w >>> 16).toUInt8, (w >>> 24).toUInt8]⟩

/-! ## §3 — The compression function. -/

/-- The `g` mixing function on state positions `a b c d` with message words `mx my`. -/
@[inline] def g (st : Array UInt32) (a b c d : Nat) (mx my : UInt32) : Array UInt32 :=
  let va := st[a]!; let vb := st[b]!; let vc := st[c]!; let vd := st[d]!
  let va := va + vb + mx
  let vd := rotr (vd ^^^ va) 16
  let vc := vc + vd
  let vb := rotr (vb ^^^ vc) 12
  let va := va + vb + my
  let vd := rotr (vd ^^^ va) 8
  let vc := vc + vd
  let vb := rotr (vb ^^^ vc) 7
  (((st.set! a va).set! b vb).set! c vc).set! d vd

/-- One round: four column mixes then four diagonal mixes. -/
def roundFn (st : Array UInt32) (m : Array UInt32) : Array UInt32 :=
  let st := g st 0 4 8  12 m[0]!  m[1]!
  let st := g st 1 5 9  13 m[2]!  m[3]!
  let st := g st 2 6 10 14 m[4]!  m[5]!
  let st := g st 3 7 11 15 m[6]!  m[7]!
  let st := g st 0 5 10 15 m[8]!  m[9]!
  let st := g st 1 6 11 12 m[10]! m[11]!
  let st := g st 2 7 8  13 m[12]! m[13]!
  g st 3 4 9 14 m[14]! m[15]!

/-- The between-rounds message permutation. -/
def permute (m : Array UInt32) : Array UInt32 :=
  MSG_PERMUTATION.map (fun i => m[i]!)

/-- `n` rounds, permuting the message between them. -/
def rounds : Nat → Array UInt32 → Array UInt32 → Array UInt32
  | 0,     st, _ => st
  | (n+1), st, m => rounds n (roundFn st m) (permute m)

/-- The BLAKE3 compression function: sixteen output words (the first eight are the chaining value;
all sixteen are used on the root/extended-output path). -/
def compress (cv : Array UInt32) (block : Array UInt32)
    (counter : UInt64) (blockLen flags : UInt32) : Array UInt32 :=
  let st : Array UInt32 :=
    #[cv[0]!, cv[1]!, cv[2]!, cv[3]!, cv[4]!, cv[5]!, cv[6]!, cv[7]!,
      IV[0]!, IV[1]!, IV[2]!, IV[3]!,
      counter.toUInt32, (counter >>> 32).toUInt32, blockLen, flags]
  let st := rounds 7 st block
  (List.range 8).foldl
    (fun (s : Array UInt32) i => (s.set! i (s[i]! ^^^ s[i + 8]!)).set! (i + 8) (s[i + 8]! ^^^ cv[i]!))
    st

/-! ## §4 — Nodes.

An `Output` is a node's *deferred* compression: the reference implementation keeps the last block
rather than its chaining value, because the root node is compressed a second time with `ROOT` set
(and once more per 64 bytes of extended output). Collapsing it to a chaining value early is the
classic way to get a correct-looking implementation that is wrong at the root. -/

/-- A node whose compression has not been performed yet. -/
structure Output where
  /-- Chaining value entering this compression. -/
  inputCv : Array UInt32
  /-- The sixteen message words of this node's block. -/
  blockWords : Array UInt32
  /-- Chunk index (chunk nodes) or `0` (parent nodes). -/
  counter : UInt64
  /-- Number of input bytes in this block (`64` except for a chunk's short final block). -/
  blockLen : UInt32
  /-- Flags for this compression, without `ROOT`. -/
  flags : UInt32

/-- The eight-word chaining value this node hands to its parent. -/
def Output.chainingValue (o : Output) : Array UInt32 :=
  (compress o.inputCv o.blockWords o.counter o.blockLen o.flags).extract 0 8

/-- The node's extended output: `len` bytes, one 64-byte block per output-block counter, `ROOT` set. -/
def Output.rootBytes (o : Output) (len : Nat) : ByteArray :=
  let nBlocks := (len + 63) / 64
  let full := (List.range nBlocks).foldl
    (fun acc i =>
      (compress o.inputCv o.blockWords (UInt64.ofNat i) o.blockLen (o.flags ||| ROOT)).foldl
        (fun a w => a ++ u32le w) acc)
    ByteArray.empty
  full.extract 0 len

/-- A parent node over two child chaining values. -/
def parentOutput (l r key : Array UInt32) (flags : UInt32) : Output :=
  { inputCv := key, blockWords := l ++ r, counter := 0,
    blockLen := UInt32.ofNat BLOCK_LEN, flags := flags ||| PARENT }

/-- One chunk of `input[start, start+len)` as a node. `len = 0` is legal only for the single chunk of
an empty input, and produces the empty block flagged `CHUNK_START ||| CHUNK_END`. -/
def chunkOutput (key : Array UInt32) (baseFlags : UInt32) (counter : UInt64)
    (input : ByteArray) (start len : Nat) : Output :=
  if len == 0 then
    { inputCv := key, blockWords := wordsFrom ByteArray.empty 0 0, counter := counter,
      blockLen := 0, flags := baseFlags ||| CHUNK_START ||| CHUNK_END }
  else
    let stop := start + len
    let nBlocks := (len + 63) / 64
    let lastIdx := nBlocks - 1
    let cv := (List.range lastIdx).foldl
      (fun cv i =>
        let f := baseFlags ||| (if i == 0 then CHUNK_START else 0)
        (compress cv (wordsFrom input (start + 64 * i) stop) counter
          (UInt32.ofNat BLOCK_LEN) f).extract 0 8)
      key
    { inputCv := cv
      blockWords := wordsFrom input (start + 64 * lastIdx) stop
      counter := counter
      blockLen := UInt32.ofNat (len - 64 * lastIdx)
      flags := baseFlags ||| (if lastIdx == 0 then CHUNK_START else 0) ||| CHUNK_END }

/-- The reference implementation's subtree-stack merge rule: after chunk number `total`, merge while
`total` is even. `fuel` bounds the loop (`total` halves each step, so `64` can never be reached). -/
def mergeStack (key : Array UInt32) (flags : UInt32) :
    Nat → Array (Array UInt32) → Array UInt32 → UInt64 → Array (Array UInt32)
  | 0,     stack, cv, _ => stack.push cv
  | (f+1), stack, cv, total =>
    if (total &&& 1) == 0 && stack.size > 0 then
      let left := stack[stack.size - 1]!
      mergeStack key flags f stack.pop ((parentOutput left cv key flags).chainingValue) (total >>> 1)
    else stack.push cv

/-- The whole tree, as the still-uncompressed root node. `key`/`baseFlags` select the mode. -/
def hashInternal (key : Array UInt32) (baseFlags : UInt32) (input : ByteArray) : Output :=
  let n := input.size
  let nChunks := if n == 0 then 1 else (n + CHUNK_LEN - 1) / CHUNK_LEN
  let lastIdx := nChunks - 1
  let stack := (List.range lastIdx).foldl
    (fun stack i =>
      let out := chunkOutput key baseFlags (UInt64.ofNat i) input (i * CHUNK_LEN) CHUNK_LEN
      mergeStack key baseFlags 64 stack out.chainingValue (UInt64.ofNat (i + 1)))
    #[]
  let root := chunkOutput key baseFlags (UInt64.ofNat lastIdx) input
    (lastIdx * CHUNK_LEN) (n - lastIdx * CHUNK_LEN)
  (List.range stack.size).foldl
    (fun o k => parentOutput stack[stack.size - 1 - k]! o.chainingValue key baseFlags) root

/-! ## §5 — The three modes. -/

/-- Hash mode, extended output. -/
def hashXof (input : ByteArray) (len : Nat) : ByteArray :=
  (hashInternal IV 0 input).rootBytes len

/-- Hash mode, 32 bytes — `blake3::hash`. -/
def hash (input : ByteArray) : ByteArray := hashXof input OUT_LEN

/-- Keyed-hash mode, extended output. `key` must be 32 bytes. -/
def keyedHashXof (key input : ByteArray) (len : Nat) : ByteArray :=
  (hashInternal (wordsFromKey key) KEYED_HASH input).rootBytes len

/-- Keyed-hash mode, 32 bytes — `blake3::keyed_hash`. -/
def keyedHash (key input : ByteArray) : ByteArray := keyedHashXof key input OUT_LEN

/-- ⚑ **Derive-key mode, extended output — the two-pass construction.** Pass 1 hashes the context
bytes under `DERIVE_KEY_CONTEXT` to a 32-byte key; pass 2 hashes the material under
`DERIVE_KEY_MATERIAL` with that key. -/
def deriveKeyXof (context material : ByteArray) (len : Nat) : ByteArray :=
  let ctxKey := (hashInternal IV DERIVE_KEY_CONTEXT context).rootBytes KEY_LEN
  (hashInternal (wordsFromKey ctxKey) DERIVE_KEY_MATERIAL material).rootBytes len

/-- ⚑⚑ **`blake3Derive`** — the deployed shape: `blake3::Hasher::new_derive_key(context)` fed
`material`, finalised to 32 bytes. Every descriptor fingerprint and every `vk_pin` in this tree is
an instance of this call. -/
def blake3Derive (context : String) (material : ByteArray) : ByteArray :=
  deriveKeyXof context.toUTF8 material OUT_LEN

/-! ## §6 — The deployed fingerprint contexts.

⚑ These strings are the ONLY thing about the descriptor fingerprint that lives on both sides. They
are pinned against Rust by `scripts/check-blake3-differential.sh`, which reads them out of
`circuit/src/descriptor_ir2_canonical.rs` and `circuit/src/air_descriptor.rs` rather than trusting
this copy. -/

/-- `circuit/src/descriptor_ir2_canonical.rs::EFFECT_VM_DESCRIPTOR2_FINGERPRINT_CONTEXT`. -/
def descriptor2FingerprintContext : String :=
  "dregg.effect-vm-descriptor2.semantic-relation.v1"

/-- `circuit/src/air_descriptor.rs::fingerprint`'s derive-key context. -/
def airFingerprintContext : String := "dregg-air-fingerprint-v1"

/-- ⚑⚑ **THE DESCRIPTOR FINGERPRINT, COMPUTED IN LEAN.** Given a DescriptorIR-v2 record's canonical
bytes, this is byte-for-byte
`circuit::descriptor_ir2_canonical::effect_vm_descriptor2_semantic_fingerprint`.

⚠ **SCOPE, SAID PLAINLY.** What is now computable in Lean is the *hash*. The canonical **encoder**
(`canonical_effect_vm_descriptor2_bytes`, ~700 lines of tagged record writing) has no Lean
counterpart, so a Lean descriptor term still cannot be fingerprinted end-to-end without Rust
producing its bytes. That encoder is the remaining transcription and it is named as such in the
report; it is not hidden behind a green gate. -/
def descriptor2Fingerprint (canonicalBytes : ByteArray) : ByteArray :=
  blake3Derive descriptor2FingerprintContext canonicalBytes

/-- The AIR-descriptor fingerprint (`circuit/src/air_descriptor.rs`), given its pre-image bytes. -/
def airFingerprint (preimage : ByteArray) : ByteArray :=
  blake3Derive airFingerprintContext preimage

/-! ## §7 — Hex, for the differential drivers and the KAT tables. -/

/-- Lowercase hex of a byte array. -/
def toHex (b : ByteArray) : String :=
  let digit (v : Nat) : Char :=
    if v < 10 then Char.ofNat (48 + v) else Char.ofNat (87 + v)
  String.ofList (b.toList.flatMap (fun x : UInt8 => [digit (x.toNat / 16), digit (x.toNat % 16)]))

/-- Parse lowercase/uppercase hex; `none` on an odd length or a non-hex character. -/
def ofHex (s : String) : Option ByteArray :=
  let val (c : Char) : Option UInt8 :=
    let n := c.toNat
    if 48 ≤ n && n ≤ 57 then some (UInt8.ofNat (n - 48))
    else if 97 ≤ n && n ≤ 102 then some (UInt8.ofNat (n - 87))
    else if 65 ≤ n && n ≤ 70 then some (UInt8.ofNat (n - 55))
    else none
  let cs := s.toList
  if cs.length % 2 != 0 then none
  else
    let rec go : List Char → Array UInt8 → Option (Array UInt8)
      | [], acc => some acc
      | [_], _ => none
      | a :: b :: rest, acc =>
        match val a, val b with
        | some x, some y => go rest (acc.push ((x <<< 4) ||| y))
        | _, _ => none
    (go cs #[]).map ByteArray.mk

/-- The official BLAKE3 test-vector input: byte `i` is `i % 251`. A `def`, not a literal — so the
102 400-byte case costs nothing to state. -/
def katInput (n : Nat) : ByteArray :=
  ⟨Array.ofFn (n := n) fun i => UInt8.ofNat (i.val % 251)⟩

end Dregg2.Crypto.Blake3
