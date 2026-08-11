/-
# Dregg2.Circuit.VkPinCompute — a `vk_pin`, COMPUTED, end to end from canonical bytes.

⚑ **THE PAYOFF FUNCTION.** A `proof_bind` leg's `vk_pin` is nine `Faithful9` lanes of the bound
program's semantic fingerprint. Until 2026-08-10 an AIR author could not produce that value in Lean:
the fingerprint is `blake3::derive_key` over the descriptor's canonical encoding, so the nine digits
came off a Rust tool (`cargo run -p dregg-circuit --example conj_fingerprint`) and were **typed into
a Lean file**. Thirteen `*_VK_LANES` constants across six Lean modules are that transcription, and
`circuit/tests/vk_pin_closure_over_the_served_tree.rs` is red because a written-down derived value
goes stale.

This module is the two hops joined:

```text
canonical bytes ──Blake3.descriptor2Fingerprint──▶ 32-byte digest ──KeyLanes9.keyToLanes9──▶ 9 lanes
```

Both halves are Lean-authored: `Blake3Compute` is the pure-Lean BLAKE3, and `keyToLanes9` is the
encoder `KeyLanes9` proves injective (`keyToLanes9_injective`) and whose canonicity envelope the
emitted AIRs carry. Neither is a re-spelling of a Rust function — `scripts/check-blake3-differential.sh`
checks BOTH hops against the deployed Rust (`effect_vm_descriptor2_semantic_fingerprint` and
`key_limbs9`) over every one of the 158 descriptors this tree serves, both sides recomputed on every
run.

⚠ **TRUST CLASS.** This is a COMPUTATION, not a theorem: nothing here is proved, and evaluating it
goes through the compiled evaluator. A pin it produces is an IDENTITY claim — *the same nine numbers
the deployed hash gives* — never a soundness one. The uninterpreted `PortalFloor.Blake3Kernel` is
what proofs use and is untouched.

⚠ **WHAT IS STILL MISSING, AND IT IS THE REASON THE THIRTEEN CONSTANTS ARE STILL THERE.** The input
here is *canonical bytes*, and the canonical ENCODER —
`circuit/src/descriptor_ir2_canonical.rs::canonical_effect_vm_descriptor2_bytes`, 534 lines and 13
mutually recursive writers over the IR-v2 AST — exists **only in Rust**. So `vkPinLanes` cannot yet
be handed a Lean `EffectVmDescriptor2` term; something must produce its bytes first. Authoring that
encoder in Lean (and deleting the Rust one, per House Law #1) is the next hop, and it is a lane of
its own. Do not read this module as though the collapse had already happened.
-/
import Dregg2.Crypto.Blake3Compute
import Dregg2.Circuit.KeyLanes9

namespace Dregg2.Circuit.VkPinCompute

open Dregg2.Crypto.Blake3

/-- A 32-byte digest as the `Bytes32` the lane encoder takes. `none` on any other length — a short
digest padded to 32 would encode to lanes that look fine and mean nothing. -/
def digestToBytes32 (digest : ByteArray) : Option Dregg2.Circuit.FieldLanes9.Bytes32 :=
  if digest.size = 32 then
    some fun i => ⟨(digest.get! i.1).toNat, by
      have := (digest.get! i.1).toNat_lt_size
      omega⟩
  else none

/-- The nine base-`2^29` lanes of a 32-byte digest, via the Lean-authored `keyToLanes9`. -/
def digestLanes (digest : ByteArray) : Option (List Nat) :=
  (digestToBytes32 digest).map fun b =>
    (List.range 9).map fun i => Dregg2.Circuit.KeyLanes9.keyToLanes9 b ⟨i % 9, by omega⟩

/-- ⚑⚑ **THE `vk_pin`, COMPUTED.** Given a DescriptorIR-v2 record's canonical bytes, the nine `ℤ`
lanes a `proofBind` leg carries — the value that is currently typed in by hand at thirteen sites. -/
def vkPinLanes (canonicalBytes : ByteArray) : Option (List ℤ) :=
  (digestLanes (descriptor2Fingerprint canonicalBytes)).map (List.map Int.ofNat)

/-- The same, as `Nat`s (the shape `key_limbs9` reports and the differential compares). -/
def vkPinLanesNat (canonicalBytes : ByteArray) : Option (List Nat) :=
  digestLanes (descriptor2Fingerprint canonicalBytes)

end Dregg2.Circuit.VkPinCompute
