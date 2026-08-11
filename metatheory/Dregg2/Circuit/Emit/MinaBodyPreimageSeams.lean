/-
# `Dregg2.Circuit.Emit.MinaBodyPreimageSeams` — ⚑⚑ **THE FIRST TIE STOPS BEING AN EXECUTOR
COMPARISON.** Twenty-five seams from the gated preimage to the body-hash chain's absorbed stream.

## The residue this closes, in its author's own words

`MinaBodyPreimageBitsAir` §7, as it stood on 2026-08-08:

> *"The 302 limbs are PUBLISHED, which is what makes a `cb.connect` … REACHABLE at all. Until that
> fold exists the tie between these bits and that chain's absorbed stream is an EXECUTOR
> comparison. **A prover still chooses which 2 381 bits.**"*

⚑ **Publication bought reachability. This file spends it.** `bodyPreimageSeam j` is the elementwise
weld between `dregg-mina-body-preimage-bits::v1`'s 1 518 published limb slots and
`dregg-pasta-fp-chainlink::v1`'s absorbed block at link `j` — 25 seams, one per link of
`MinaStateBodyHashChain`, together covering every one of the 49 absorbed field elements exactly
once.

## ⚑ THE SHAPE, AND WHY THE ZERO-PINS ARE ON THE CHAIN SIDE

The chain's absorbed block is `SK = 32` eight-bit limbs an element, unconditionally. The preimage
claim publishes `SK` limbs for a WHOLE field element and only `⌈W_e/8⌉` for a PACKED one — the
`⌈W_e/8⌉` allocation `MinaBodyPreimageBitsAir` chose so that no published limb is inert. The
difference is not a rounding: it is the statement *"element `38+e` is below `2^(8·⌈W_e/8⌉)`"*, and a
weld that only connected the low limbs would leave the chain free to absorb
`element + k · 2^(8·⌈W_e/8⌉)`. So each seam carries `32 − ⌈W_e/8⌉` **zero-pins on the CHAIN side**,
and the odd tail's padding element carries 32 of them — the `bodyPacked ++ [0]` the rate-2 chunking
implies (`MinaStateBodyHashChain.the_body_chain_absorbs_the_preimage_in_order`), which until now no
constraint and no comparison forced at all.

⚑ `Seam.prefix_weld` is the general form of this reading and it is what §4's S2 crosses: low-`m`
weld plus high zero-pins is `mod 2^(8m)`, as arithmetic rather than as prose.

## ⚑ WHY TWENTY-FIVE SEAMS AND NOT ONE WIDE CARRY

A single seam whose right end was the chain's fold ROOT would have to carry all 25 links' absorbed
blocks — 1 600 lanes — through the fold. That direction is measured bad: a padded 3 048-lane carried
claim produced a `WitnessConflict` at `WitnessId(676)`, because `p3_circuit`'s `connect` is a
union-find MERGE onto one witness slot and a wide padded carry multiplies the classes that must
agree. Each seam here is applied where BOTH claims are already in scope — the preimage leaf's
`air_public_targets` and link `j`'s — so it adds **no carried lane at all**, only 64 merges per link.
Total: 1 518 pins + 82 zero-pins across 25 seams, and the fold's claim widths are unchanged.

## ⚠ STANDING, SAID PLAINLY

A `SeamSpec` does not turn recursion wiring into AIR (`SeamSpec.lean` §"What a `SeamSpec` does NOT
claim"). The connects are issued by `circuit-prove` reading these artifacts; the recursion circuit
proves on a box and inherits the undischarged FRI/STARK floor. What changed is that the tie is an
OBJECT with S1 (the pin lists name published slots of the deployed AIRs) and S2 (a named composition
theorem, shown FALSE without its seam hypothesis) instead of a `WeldCover` naming an executor
function.

## Axiom hygiene

Kernel-clean throughout; the real-block instances are `native_decide` + `#assert_compiled` and say
so. No `sorry`, no `#guard`, no new axiom.
-/
import Dregg2.Circuit.Emit.SeamSpec
import Dregg2.Circuit.Emit.MinaBodyPreimageBitsAir
import Dregg2.Circuit.Emit.MinaStateBodyHashChain
import Dregg2.Circuit.Emit.LightClientMinaLinkAir

namespace Dregg2.Circuit.Emit.MinaBodyPreimageSeams

open Dregg2.Circuit.EffectAirIR (EffectAir AirLeg PiPinLeg)
open Dregg2.Circuit.Emit.EffectVmEmit (VmRow)
open Dregg2.Circuit.Emit.Seam
open Dregg2.Circuit.Emit.PastaFieldSound (SK SB limbAt)
open Dregg2.Circuit.Emit.MinaBodyPreimageBitsAir
  (NFIELD NELEM NLIMB NFLIMB BODY_BITS_PI_COUNT PI_FLIMB PI_PLIMB PI_ABSORBED absorbedLimbCount
   FLIMB PLIMB limbCount limbBase bodyBitsAir fieldIdx limbIdx fieldPin limbPin)

set_option autoImplicit false
set_option maxRecDepth 100000

/-! ## §1 — THE TWO CLAIM LAYOUTS, and the chain's absorbed window.

⚑⚑ **BOTH ENDS ARE RAW DESCRIPTOR PI VECTORS — `apt.first()`, NOT an `expose_claim`.** This is
load-bearing and it is a MEASURED constraint on where the seam can be applied, not a style choice:
`circuit-prove/src/mina_phase2_chain_leaf.rs`'s leaf exposes
`in(96) ‖ out(96) ‖ seg_poseidon_commit(absorbed)` — **200 lanes, and the 64 ABSORBED LIMBS ARE NOT
AMONG THEM**, only their 8-lane Poseidon commitment. So a seam against the chain's `expose_claim`
(or against the fold ROOT, which carries the same 200 lanes) **cannot reach the absorbed stream at
all**; the only surface that carries it is the leaf's own `air_public_targets.first()`, the
descriptor's 256-slot PI vector. `SeamEnd` is descriptor-keyed, which is exactly the right key for
that surface.

⚑⚑ **AND THE ADAPTER THAT SURFACE NEEDED EXISTS SINCE 2026-08-10.**
`circuit-prove/src/mina_body_preimage_adapter.rs::prove_body_preimage_link_adapter` verifies the
preimage STARK and a chain-link STARK in ONE aggregation circuit — both children are
`RecursionInput::NativeBatchStark`, so the expose hook receives two RAW descriptor PI vectors — and
calls `apply_seam` on the two `apt.first()` slices. It publishes exactly the chain leaf's 200-lane
claim, so twenty-five adapters fold with the UNMODIFIED `fold_chain_links` into the same
`state_body_hash` root.

⚠ **What that does and does not settle is in §7.0, which is now a different sentence than it was.**
-/

/-- The preimage leaf's claim surface: the whole PI vector of
`dregg-mina-body-preimage-bits::v1`, in ABSORB order — 38 whole-field limb blocks of `SK`, then
eleven packed blocks of `⌈W_e/8⌉`. -/
def PREIMAGE_CLAIM_LEN : Nat := BODY_BITS_PI_COUNT

/-- The chain link leaf's claim surface: the whole 256-slot PI vector of
`dregg-pasta-fp-chainlink::v1`, `in(96) ‖ out(96) ‖ absorbed(64)`
(`MinaPhase1Chain.CHAIN_PI_COUNT`). ⚠ **NOT the 200-lane `expose_claim`** — see the section note. -/
def CHAIN_CLAIM_LEN : Nat := Dregg2.Circuit.Emit.MinaPhase1Chain.CHAIN_PI_COUNT

/-- Claim offset of the chain link's FIRST absorbed element — register 3's first-row pin block,
descriptor PI slot `6·SK`. -/
def CHAIN_ABSORBED_0 : Nat := 6 * SK
/-- …and of the SECOND — register 4's, slot `7·SK`. -/
def CHAIN_ABSORBED_1 : Nat := 7 * SK

/-- The claim offset of absorbed side `s ∈ {0,1}`. -/
def chainAbsorbedBase (s : Nat) : Nat := if s = 0 then CHAIN_ABSORBED_0 else CHAIN_ABSORBED_1

/-- How many absorbed field elements a `Protocol_state.Body` preimage has (`bodyPacked.length`). -/
def NABSORBED : Nat := 49

/-- The number of links — `⌈49/2⌉`, `MinaStateBodyHashChain.BODY_LINKS`. -/
def BODY_LINKS : Nat := Dregg2.Circuit.Emit.MinaStateBodyHashChain.BODY_LINKS

theorem the_claim_shapes_are_the_deployed_ones :
    PREIMAGE_CLAIM_LEN = 1518 ∧ CHAIN_CLAIM_LEN = 256
      ∧ CHAIN_ABSORBED_0 = 192 ∧ CHAIN_ABSORBED_1 = 224
      ∧ BODY_LINKS = 25 ∧ 2 * BODY_LINKS = NABSORBED + 1 := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-! ## §2 — ⚑ THE SEAM FAMILY. -/

/-- ⚑ `effect_vm_descriptor2_semantic_fingerprint(dregg-mina-body-preimage-bits::v1)`, as
`Faithful9` key lanes.

⚠ **MEASURED-OR-NOTHING.** Lean cannot compute blake3, so this literal is a MEASUREMENT of the
served artifact and nothing else. `EmitSeamSpecs` REFUSES to write any seam of this family while the
value is the unmeasured sentinel (`the_left_lanes_are_the_unmeasured_sentinel` is the verdict it
reads), so an unmeasured lane vector produces NO artifact rather than a plausible one — and
`seam.rs::SeamEnd::require_matches` RECOMPUTES the lanes from the descriptor it loads and refuses a
mismatch, so a STALE one is a loud red on the Rust side.

⚠ **FLAG DAY COUPLING:** re-emitting `dregg-mina-body-preimage-bits-v1.json` moves this literal and
re-emits all twenty-five seam artifacts.

⚑ **MEASURED 2026-08-10** by `cargo run -p dregg-circuit --release --example conj_fingerprint --
`circuit/descriptors/by-name/dregg-mina-body-preimage-bits-v1.json`, over the bytes at
`w=3899 pi=1518 cons=5417`,
`fp=df0bcb848a29279775bc1f0125f7fbf030929c8e27dc7004d9a1112f6c660679`. The sentinel below is
therefore FALSE and `EmitSeamSpecs` emits the family. -/
def BODY_BITS_VK_LANES : List ℤ :=
  [80415711, 423185492, 133111141, 401492482, 153292559, 236177230, 123998659, 226878004, 7931494]

/-- ⚑ **THE UNMEASURED SENTINEL, AS A VERDICT.** A gate that cannot go red is not a gate: this one
is `true` exactly while the lanes above are the all-zero placeholder, and `EmitSeamSpecs` refuses to
emit while it is. ⚠ It is `= true` at the time of writing — the descriptor's shape changed in the
same commit and the fingerprint had not been re-measured, so **no artifact of this family is
emitted**, which is the honest state rather than a hidden one. -/
def leftLanesAreUnmeasured : Bool := BODY_BITS_VK_LANES == List.replicate 9 (0 : ℤ)

/-- The pins welding absorbed element `n`'s published limbs onto the chain claim's block at
`base` — `absorbedLimbCount n` of them: `SK` for a whole field element, `⌈W_e/8⌉` for a packed one,
and NONE for the odd tail's padding element (`absorbedLimbCount 49 = 0`). -/
def sidePins (n base : Nat) : List (Nat × Nat) :=
  (List.range (absorbedLimbCount n)).map (fun k => (PI_ABSORBED n k, base + k))

/-- ⚑ The zero-pins: every chain-side limb the preimage claim does NOT publish. For a whole field
element there are none; for packed element `e` there are `32 − ⌈W_e/8⌉`; for the padding element
there are 32 — which is the only thing in the tree that forces `bodyPacked ++ [0]`'s tail zero. -/
def sideZeros (n base : Nat) : List Nat :=
  (List.range (SK - absorbedLimbCount n)).map (fun k => base + absorbedLimbCount n + k)

/-- ⚑⚑ **THE SEAM AT LINK `j`.** Link `j` absorbs elements `2j` and `2j+1`
(`MinaStateBodyHashChain.bodyLinkXs = pairsOf bodyPacked`), so the seam welds those two published
blocks onto the link claim's two absorbed windows and zero-pins the rest. -/
def bodyPreimageSeam (j : Nat) : SeamSpec :=
  { name  := "dregg-seam-body-preimage-link-" ++ toString j ++ "::v1"
  , left  := { claim := "mina-body-preimage-leaf", claimLen := PREIMAGE_CLAIM_LEN
             , descName := "dregg-mina-body-preimage-bits::v1", descLanes := BODY_BITS_VK_LANES }
  , right := { claim := "mina-body-chain-leaf", claimLen := CHAIN_CLAIM_LEN
             , descName := "dregg-pasta-fp-chainlink::v1"
             , descLanes := Dregg2.Circuit.Emit.LightClientMinaLinkAir.FP_CHAINLINK_VK_LANES }
  , pins := sidePins (2 * j) CHAIN_ABSORBED_0 ++ sidePins (2 * j + 1) CHAIN_ABSORBED_1
  , zeroLeft := []
  , zeroRight := sideZeros (2 * j) CHAIN_ABSORBED_0 ++ sideZeros (2 * j + 1) CHAIN_ABSORBED_1 }

/-- The registry: one seam per link. -/
def bodyPreimageSeams : List SeamSpec := (List.range BODY_LINKS).map bodyPreimageSeam

theorem bodyPreimageSeams_length : bodyPreimageSeams.length = 25 := by rfl

/-- ⚑ **EVERY SEAM IS WELL-FORMED** — indices in range on both ends, nine lanes per end, non-empty.
Over all twenty-five, not sampled. ⚠ COMPILED: the verdict walks 1 518 pins and 82 zero-pins. -/
theorem every_body_preimage_seam_is_wf :
    bodyPreimageSeams.all (fun s => s.wf) = true := by native_decide

/-- ⚑⚑ **THE FAMILY COVERS THE WHOLE CHAIN AND THE WHOLE CLAIM, EXACTLY ONCE.** Three counts that a
dropped or duplicated element would move: the total pin count is the preimage claim's whole length,
the total zero-pin count is the `32 − ⌈W_e/8⌉` deficit plus the padding element's 32, and the two
together are `25 × 64` — every absorbed limb of every link is either welded or pinned to zero, with
nothing left free. ⚠ Without the third conjunct a seam could weld a prefix and leave chain-side
limbs the prover picks. -/
theorem the_seams_cover_every_absorbed_limb :
    (bodyPreimageSeams.map (fun s => s.pins.length)).foldl (· + ·) 0 = PREIMAGE_CLAIM_LEN
      ∧ (bodyPreimageSeams.map (fun s => s.zeroRight.length)).foldl (· + ·) 0 = 82
      ∧ (bodyPreimageSeams.map (fun s => s.pins.length + s.zeroRight.length)).foldl (· + ·) 0
          = BODY_LINKS * (2 * SK)
      ∧ (bodyPreimageSeams.all (fun s => s.zeroLeft.isEmpty)) = true := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> native_decide

/-- ⚑ **AND EVERY LEFT SLOT IS USED EXACTLY ONCE.** The 1 518 pins' left endpoints are a
permutation of `[0, 1518)` — so no published limb is welded twice (which would be an aliasing bug a
count alone cannot see) and none is left unwelded. -/
theorem every_published_slot_is_welded_exactly_once :
    ((bodyPreimageSeams.flatMap (fun s => s.pins.map Prod.fst)).mergeSort (· ≤ ·))
      = List.range PREIMAGE_CLAIM_LEN := by native_decide

/-! ## §3 — S1: the pin lists name exactly the published slots they claim to.

Memberships in the ACTUAL `EffectAir` leg lists, constructed rather than decided (`AirLeg` has no
`DecidableEq`, and none is needed to build a `Mem`). -/

/-- The preimage leaf publishes whole field element `f`'s limb `k` at claim slot `PI_FLIMB f k`. -/
theorem preimage_field_slot_is_published (f k : Nat) (hf : f < NFIELD) (hk : k < SK) :
    AirLeg.pin ⟨VmRow.first, FLIMB f k, PI_FLIMB f k⟩ ∈ bodyBitsAir.legs := by
  have hmem : ((f, k) : Nat × Nat) ∈ fieldIdx :=
    List.mem_flatMap.mpr ⟨f, List.mem_range.mpr hf,
      List.mem_map.mpr ⟨k, List.mem_range.mpr hk, rfl⟩⟩
  have hin : AirLeg.pin ⟨VmRow.first, FLIMB f k, PI_FLIMB f k⟩
      ∈ (fieldIdx.map fun p => fieldPin p.1 p.2) :=
    List.mem_map.mpr ⟨(f, k), hmem, rfl⟩
  show _ ∈ ((((List.range NFIELD).map _ ++ _) ++ _) ++ (fieldIdx.map fun p => fieldPin p.1 p.2))
    ++ (limbIdx.map fun p => limbPin p.1 p.2)
  exact List.mem_append_left _ (List.mem_append_right _ hin)

/-- …and packed element `e`'s limb `k` at claim slot `PI_PLIMB e k`. -/
theorem preimage_packed_slot_is_published (e k : Nat) (he : e < NELEM) (hk : k < limbCount e) :
    AirLeg.pin ⟨VmRow.first, PLIMB e k, PI_PLIMB e k⟩ ∈ bodyBitsAir.legs := by
  have hmem : ((e, k) : Nat × Nat) ∈ limbIdx :=
    List.mem_flatMap.mpr ⟨e, List.mem_range.mpr he,
      List.mem_map.mpr ⟨k, List.mem_range.mpr hk, rfl⟩⟩
  have hin : AirLeg.pin ⟨VmRow.first, PLIMB e k, PI_PLIMB e k⟩
      ∈ (limbIdx.map fun p => limbPin p.1 p.2) :=
    List.mem_map.mpr ⟨(e, k), hmem, rfl⟩
  show _ ∈ ((((List.range NFIELD).map _ ++ _) ++ _) ++ _)
    ++ (limbIdx.map fun p => limbPin p.1 p.2)
  exact List.mem_append_right _ hin

/-- ⚑ The chain link's FIRST absorbed block is register 3's first-row pin block — claim slots
`[6·SK, 7·SK)`. -/
theorem chain_absorbed_0_is_register_three (i : Nat) (hi : i < SK) :
    AirLeg.pin ⟨VmRow.first, Dregg2.Circuit.Emit.MinaWrapVerifierProgram.regCol 3 + i,
        6 * SK + i⟩
      ∈ Dregg2.Circuit.Emit.MinaPhase1Chain.chainAir.legs := by
  show _ ∈ (Dregg2.Circuit.Emit.MinaWrapVerifierProgram.programAir
      Dregg2.Circuit.Emit.PastaFieldSound.pLimb
      Dregg2.Circuit.Emit.MinaWrapVerifierSpongeFp.fpAbsorbProg).legs
    ++ Dregg2.Circuit.Emit.MinaPhase2Chain.chainPins
  refine List.mem_append_right _ ?_
  show _ ∈ ((((((( Dregg2.Circuit.Emit.MinaWrapVerifierSponge.pinBlock VmRow.first 0 0
      ++ _) ++ _) ++ _) ++ _) ++ _)
      ++ Dregg2.Circuit.Emit.MinaWrapVerifierSponge.pinBlock VmRow.first 3 (6 * SK))
      ++ _)
  exact List.mem_append_left _ (List.mem_append_right _
    (List.mem_map.mpr ⟨i, List.mem_range.mpr hi, rfl⟩))

/-- …and the SECOND is register 4's first-row block — claim slots `[7·SK, 8·SK)`. ⚠ NOT register
4's LAST-row block, which is the outgoing sponge lane one rung over; the row selector is the
discriminator and a copy-paste that took the wrong one would weld the absorbed stream onto the
squeeze. -/
theorem chain_absorbed_1_is_register_four_first_row (i : Nat) (hi : i < SK) :
    AirLeg.pin ⟨VmRow.first, Dregg2.Circuit.Emit.MinaWrapVerifierProgram.regCol 4 + i,
        7 * SK + i⟩
      ∈ Dregg2.Circuit.Emit.MinaPhase1Chain.chainAir.legs := by
  show _ ∈ (Dregg2.Circuit.Emit.MinaWrapVerifierProgram.programAir
      Dregg2.Circuit.Emit.PastaFieldSound.pLimb
      Dregg2.Circuit.Emit.MinaWrapVerifierSpongeFp.fpAbsorbProg).legs
    ++ Dregg2.Circuit.Emit.MinaPhase2Chain.chainPins
  refine List.mem_append_right _ ?_
  show _ ∈ ((((((( _ ++ _) ++ _) ++ _) ++ _) ++ _) ++ _)
      ++ Dregg2.Circuit.Emit.MinaWrapVerifierSponge.pinBlock VmRow.first 4 (7 * SK))
  exact List.mem_append_right _ (List.mem_map.mpr ⟨i, List.mem_range.mpr hi, rfl⟩)

/-- ⚑ **S1 FOR THE PREIMAGE SEAM FAMILY.** Both ends of every weld are slots a real pin leg of the
deployed AIR publishes, and the pin list is exactly the two `sidePins` blocks. -/
theorem the_body_preimage_seams_weld_published_slots (j : Nat) :
    (bodyPreimageSeam j).pins
        = sidePins (2 * j) CHAIN_ABSORBED_0 ++ sidePins (2 * j + 1) CHAIN_ABSORBED_1
    ∧ (∀ f k, f < NFIELD → k < SK →
        AirLeg.pin ⟨VmRow.first, FLIMB f k, PI_FLIMB f k⟩ ∈ bodyBitsAir.legs)
    ∧ (∀ e k, e < NELEM → k < limbCount e →
        AirLeg.pin ⟨VmRow.first, PLIMB e k, PI_PLIMB e k⟩ ∈ bodyBitsAir.legs)
    ∧ (∀ i, i < SK →
        AirLeg.pin ⟨VmRow.first, Dregg2.Circuit.Emit.MinaWrapVerifierProgram.regCol 3 + i,
            6 * SK + i⟩ ∈ Dregg2.Circuit.Emit.MinaPhase1Chain.chainAir.legs)
    ∧ (∀ i, i < SK →
        AirLeg.pin ⟨VmRow.first, Dregg2.Circuit.Emit.MinaWrapVerifierProgram.regCol 4 + i,
            7 * SK + i⟩ ∈ Dregg2.Circuit.Emit.MinaPhase1Chain.chainAir.legs) :=
  ⟨rfl, preimage_field_slot_is_published, preimage_packed_slot_is_published,
   chain_absorbed_0_is_register_three, chain_absorbed_1_is_register_four_first_row⟩

/-! ## §4 — ⚑ THE SENTENCES AND S2, WITH BOTH POLES.

The vocabulary is `Seam.digitsVal` — the base-`2^SB` reading the whole cone's claim blocks are
written in — and `Seam.Renders`, whose canonicality hypothesis the preimage descriptor's felt gate
discharges (`MinaBodyPreimageBitsAir.the_field_gate_bounds_every_whole_element_limb`). -/

/-- The value the preimage claim publishes for absorbed element `n`, read base-`2^SB` over the
`absorbedLimbCount n` slots it actually allocates. -/
def claimValue (lv : List ℤ) (n : Nat) : ℤ :=
  digitsVal (fun i => lv.getD (PI_ABSORBED n i) 0) (absorbedLimbCount n)

/-- The value the chain claim's absorbed block at `base` denotes, over all `SK` limbs. -/
def chainAbsorbedValue (rv : List ℤ) (base : Nat) : ℤ :=
  digitsVal (fun i => rv.getD (base + i) 0) SK

/-- ⚑ **THE DIGIT LEMMA THE ZERO-PINS BUY** — digits above `m` that vanish do not contribute, so a
`SK`-digit reading collapses to the `m`-digit one. This is `Seam.prefix_weld`'s content in the form
this seam needs: the left claim allocates `m` limbs, the right allocates `SK`, and the zero-pins are
what make the two readings ONE number instead of the right one being the left plus an unconstrained
multiple of `2^(SB·m)`. -/
theorem digitsVal_zero_tail {get : Nat → ℤ} {m : Nat} :
    ∀ d, (∀ i, m ≤ i → i < m + d → get i = 0) → digitsVal get (m + d) = digitsVal get m := by
  intro d
  induction d with
  | zero => intro _; rfl
  | succ k ih =>
      intro hz
      have hstep : m + (k + 1) = (m + k) + 1 := by omega
      rw [hstep, digitsVal, List.range_succ, List.foldr_append]
      simp only [List.foldr_cons, List.foldr_nil]
      rw [hz (m + k) (by omega) (by omega)]
      show (List.range (m + k)).foldr _ (0 * (2 ^ SB : ℤ) + 0) = _
      rw [zero_mul, add_zero]
      exact ih (fun i hi hlt => hz i hi (by omega))

/-- ⚑ **WHAT THE PREIMAGE LEAF'S CLAIM SAYS** — every published limb is a BYTE. This is the
descriptor's own verdict, transported to the claim: the packed limbs are compositions of eight
boolean bit columns and the whole-field limbs are queries of the declared `range_w8` table
(`MinaBodyPreimageBitsAir.the_field_gate_bounds_every_whole_element_limb`). -/
def PreimageLeafSays (lv : List ℤ) : Prop :=
  ∀ n, n < NABSORBED → ∀ i, i < absorbedLimbCount n →
    0 ≤ lv.getD (PI_ABSORBED n i) 0 ∧ lv.getD (PI_ABSORBED n i) 0 < 2 ^ SB

/-- **WHAT THE CHAIN LINK'S CLAIM SAYS** — its two absorbed blocks render two canonical values.
Existential in the values, faithfully: which values is exactly what the seam supplies. -/
def ChainLinkSays (rv : List ℤ) : Prop :=
  ∃ x0 x1 : Nat, Renders rv CHAIN_ABSORBED_0 x0 ∧ Renders rv CHAIN_ABSORBED_1 x1

/-- ⚑⚑ **THE COMPOSED SENTENCE.** Link `j` absorbs the two elements the gated preimage claim
publishes — as VALUES, elementwise at full limb width, with no digest and therefore no birthday
bound — and those elements are read off byte-valued limbs. -/
def AbsorbsThePreimageAt (j : Nat) (lv rv : List ℤ) : Prop :=
  ∃ x0 x1 : Nat,
    Renders rv CHAIN_ABSORBED_0 x0 ∧ Renders rv CHAIN_ABSORBED_1 x1
    ∧ (x0 : ℤ) = claimValue lv (2 * j) ∧ (x1 : ℤ) = claimValue lv (2 * j + 1)
    ∧ (∀ i, i < absorbedLimbCount (2 * j) →
        0 ≤ lv.getD (PI_ABSORBED (2 * j) i) 0
          ∧ lv.getD (PI_ABSORBED (2 * j) i) 0 < 2 ^ SB)

/-- ⚑ **NO ELEMENT PUBLISHES MORE LIMBS THAN THE CHAIN ABSORBS** — `absorbedLimbCount n ≤ SK` for
EVERY `n`, not for the 49 that occur. ⚠ This is the hypothesis `side_value_of_seam` needs at a
SYMBOLIC `j`, which is why it is a general theorem and not a `decide` at the call site: the call
sites carry a free `j`, and `decide` cannot see a free variable. Both branches are terminal —
a whole field element publishes exactly `SK`, and a packed one publishes a `LIMB_COUNT` entry, every
one of which is `≤ 32` (the out-of-range default is `0`). -/
theorem absorbedLimbCount_le_SK (n : Nat) : absorbedLimbCount n ≤ SK := by
  unfold absorbedLimbCount
  split
  · exact Nat.le_refl SK
  · show limbCount (n - NFIELD) ≤ SK
    unfold limbCount
    by_cases hl : (n - NFIELD) < Dregg2.Circuit.Emit.MinaBodyPreimageBitsAir.LIMB_COUNT.length
    · have h : ∀ e < Dregg2.Circuit.Emit.MinaBodyPreimageBitsAir.LIMB_COUNT.length,
          Dregg2.Circuit.Emit.MinaBodyPreimageBitsAir.LIMB_COUNT.getD e 0 ≤ SK := by decide
      exact h _ hl
    · rw [List.getD_eq_getElem?_getD,
        List.getElem?_eq_none (Nat.le_of_not_lt hl)]
      exact Nat.zero_le _

/-- ⚑ **EVERY PUBLISHED ABSORBED SLOT IS INSIDE THE CLAIM** — bounded over the whole 49-element
stream, kernel-decided. ⚠ The §4a witnesses need this at a symbolic `n`/`i`, and the original
`revert; decide` could not: `∀ n i : ℕ, …` is an UNBOUNDED quantifier and has no `Decidable`
instance. Bounding both is what makes it a decision. -/
theorem pi_absorbed_lt_claim_len :
    ∀ n < NABSORBED, ∀ i < absorbedLimbCount n, PI_ABSORBED n i < PREIMAGE_CLAIM_LEN := by
  decide

/-- The bridge from a `Renders` to the digit reading: a rendered block's `digitsVal` IS its value. -/
private theorem renders_digitsVal {rv : List ℤ} {base s : Nat} (h : Renders rv base s) :
    chainAbsorbedValue rv base = (s : ℤ) := by
  unfold chainAbsorbedValue
  rw [digitsVal_congr (n := SK) (g := limbAt s) (fun i hi => h.2 i hi), digitsVal_limb]
  exact_mod_cast congrArg (fun n : Nat => (n : ℤ)) (Nat.mod_eq_of_lt h.1)

/-- One side of the S2 argument: the seam's pins carry the low `m` digits and its zero-pins kill the
rest, so the chain block's value IS the claim's element. -/
private theorem side_value_of_seam {lv rv : List ℤ} {n base : Nat}
    (hm : absorbedLimbCount n ≤ SK)
    (hpin : ∀ k, k < absorbedLimbCount n →
      lv.getD (PI_ABSORBED n k) 0 = rv.getD (base + k) 0)
    (hzero : ∀ k, k < SK - absorbedLimbCount n →
      rv.getD (base + absorbedLimbCount n + k) 0 = 0) :
    chainAbsorbedValue rv base = claimValue lv n := by
  set m := absorbedLimbCount n with hmdef
  have htail : digitsVal (fun i => rv.getD (base + i) 0) (m + (SK - m))
      = digitsVal (fun i => rv.getD (base + i) 0) m := by
    refine digitsVal_zero_tail (SK - m) (fun i hi hlt => ?_)
    have h := hzero (i - m) (by omega)
    have harith : base + m + (i - m) = base + i := by omega
    rwa [harith] at h
  have hsum : m + (SK - m) = SK := by omega
  rw [hsum] at htail
  unfold chainAbsorbedValue claimValue
  rw [htail]
  exact (digitsVal_congr (n := m) (fun i hi => hpin i hi)).symm

/-- ⚑⚑⚑ **S2 — THE COMPOSITION OBLIGATION FOR THE PREIMAGE SEAM AT LINK `j`.** The 64 welds and
zero-pins carry both absorbed values onto the two claim elements. ⚠ `hj : 2 * j + 1 ≤ NABSORBED`
is the real range condition — at `j = 24` the second element IS the padding slot, whose
`absorbedLimbCount` is `0` and whose 32 zero-pins say the chain absorbs `0` there. -/
theorem bodyPreimageSeamCertifies (j : Nat) (hj : 2 * j < NABSORBED) :
    SeamCertifies (bodyPreimageSeam j) PreimageLeafSays ChainLinkSays
      (AbsorbsThePreimageAt j) := by
  rintro lv rv hL ⟨x0, x1, h0, h1⟩ ⟨hpins, -, hzr⟩
  refine ⟨x0, x1, h0, h1, ?_, ?_, fun i hi => hL (2 * j) hj i hi⟩
  · rw [← renders_digitsVal h0]
    refine side_value_of_seam (n := 2 * j) (absorbedLimbCount_le_SK _) ?_ ?_
    · intro k hk
      exact hpins (PI_ABSORBED (2 * j) k, CHAIN_ABSORBED_0 + k)
        (List.mem_append_left _ (List.mem_map.mpr ⟨k, List.mem_range.mpr hk, rfl⟩))
    · intro k hk
      exact hzr (CHAIN_ABSORBED_0 + absorbedLimbCount (2 * j) + k)
        (List.mem_append_left _ (List.mem_map.mpr ⟨k, List.mem_range.mpr hk, rfl⟩))
  · rw [← renders_digitsVal h1]
    refine side_value_of_seam (n := 2 * j + 1) (absorbedLimbCount_le_SK _) ?_ ?_
    · intro k hk
      exact hpins (PI_ABSORBED (2 * j + 1) k, CHAIN_ABSORBED_1 + k)
        (List.mem_append_right _ (List.mem_map.mpr ⟨k, List.mem_range.mpr hk, rfl⟩))
    · intro k hk
      exact hzr (CHAIN_ABSORBED_1 + absorbedLimbCount (2 * j + 1) + k)
        (List.mem_append_right _ (List.mem_map.mpr ⟨k, List.mem_range.mpr hk, rfl⟩))

/-! ### §4a — ⚑⚑ THE RED POLE: S2 WITHOUT ITS SEAM HYPOTHESIS IS FALSE.

Not unprovable — FALSE, on concrete claims. A preimage claim whose every published limb is `0`
satisfies `PreimageLeafSays` (every limb is a byte) and a chain claim absorbing `1` satisfies
`ChainLinkSays`; the composed sentence would force `1 = 0`. A composition theorem that survived this
deletion would be `P → P` wearing a name, and this repo has shipped one. -/

/-- The `SK` base-256 limbs of `a`, as a claim block. -/
def limbBlock (a : Nat) : List ℤ := (List.range SK).map (limbAt a)

/-- A preimage claim carrying zero in every published slot. -/
def zeroPreimageClaim : List ℤ := List.replicate PREIMAGE_CLAIM_LEN 0

/-- A chain claim that absorbs `1` on side 0 and `0` on side 1. -/
def oneAbsorbingChainClaim : List ℤ :=
  List.replicate (6 * SK) 0 ++ limbBlock 1 ++ limbBlock 0

private theorem limbBlock_length (a : Nat) : (limbBlock a).length = SK := by
  simp [limbBlock]

private theorem oneAbsorbing_renders_0 : Renders oneAbsorbingChainClaim CHAIN_ABSORBED_0 1 := by
  refine ⟨by decide +kernel, fun i hi => ?_⟩
  show (List.replicate (6 * SK) (0 : ℤ) ++ limbBlock 1 ++ limbBlock 0).getD (6 * SK + i) 0
      = limbAt 1 i
  rw [List.append_assoc, List.getD_eq_getElem?_getD,
    List.getElem?_append_right (by simp), List.length_replicate, Nat.add_sub_cancel_left,
    List.getElem?_append_left (by rw [limbBlock_length]; exact hi)]
  simp [limbBlock, hi]

private theorem oneAbsorbing_renders_1 : Renders oneAbsorbingChainClaim CHAIN_ABSORBED_1 0 := by
  refine ⟨by decide +kernel, fun i hi => ?_⟩
  show (List.replicate (6 * SK) (0 : ℤ) ++ limbBlock 1 ++ limbBlock 0).getD (7 * SK + i) 0
      = limbAt 0 i
  rw [List.append_assoc, List.getD_eq_getElem?_getD,
    List.getElem?_append_right (by simp; omega), List.length_replicate,
    List.getElem?_append_right (by rw [limbBlock_length]; omega), limbBlock_length]
  have harith : 7 * SK + i - 6 * SK - SK = i := by
    have : SK = 32 := rfl
    omega
  rw [harith]
  simp [limbBlock, hi]

theorem zeroPreimage_says : PreimageLeafSays zeroPreimageClaim := by
  intro n hn i hi
  have hlt : PI_ABSORBED n i < PREIMAGE_CLAIM_LEN := pi_absorbed_lt_claim_len n hn i hi
  show 0 ≤ (List.replicate PREIMAGE_CLAIM_LEN (0 : ℤ)).getD (PI_ABSORBED n i) 0
    ∧ (List.replicate PREIMAGE_CLAIM_LEN (0 : ℤ)).getD (PI_ABSORBED n i) 0 < 2 ^ SB
  rw [List.getD_eq_getElem?_getD, List.getElem?_replicate]
  simp only [hlt, if_pos]
  refine ⟨by norm_num, ?_⟩
  show (0 : ℤ) < 2 ^ SB
  positivity

theorem oneAbsorbing_says : ChainLinkSays oneAbsorbingChainClaim :=
  ⟨1, 0, oneAbsorbing_renders_0, oneAbsorbing_renders_1⟩

/-- The zero claim's element 0 reads as `0` — the value the composed sentence would have to equal. -/
private theorem zeroPreimage_claimValue_zero : claimValue zeroPreimageClaim 0 = 0 := by
  unfold claimValue
  have hz : ∀ i, i < absorbedLimbCount 0 → zeroPreimageClaim.getD (PI_ABSORBED 0 i) 0 = 0 := by
    intro i hi
    have := (zeroPreimage_says 0 (by decide) i hi)
    show zeroPreimageClaim.getD (PI_ABSORBED 0 i) 0 = 0
    have hlt : PI_ABSORBED 0 i < PREIMAGE_CLAIM_LEN :=
      pi_absorbed_lt_claim_len 0 (by decide) i hi
    show (List.replicate PREIMAGE_CLAIM_LEN (0 : ℤ)).getD (PI_ABSORBED 0 i) 0 = 0
    rw [List.getD_eq_getElem?_getD, List.getElem?_replicate]
    simp [hlt]
  rw [digitsVal_congr (n := absorbedLimbCount 0) (g := fun _ => (0 : ℤ)) hz, digitsVal_zero]

/-- ⚑⚑⚑ **THE REFUTER.** Delete `SeamEq` from S2 and the implication is FALSE. Kernel-clean: the
witnesses are an all-zero preimage claim and a chain claim absorbing `1`, both child sentences hold
at them, and the contradiction is `(1 : ℤ) = 0`. -/
theorem body_preimage_seam_S2_needs_the_seam :
    ¬ (∀ lv rv, PreimageLeafSays lv → ChainLinkSays rv → AbsorbsThePreimageAt 0 lv rv) := by
  intro h
  obtain ⟨x0, x1, h0, h1, heq0, -, -⟩ :=
    h zeroPreimageClaim oneAbsorbingChainClaim zeroPreimage_says oneAbsorbing_says
  have hx0 : x0 = 1 := Renders.eq_of_weld h0 oneAbsorbing_renders_0 (fun _ _ => rfl)
  rw [hx0, zeroPreimage_claimValue_zero] at heq0
  exact absurd heq0 (by norm_num)

/-! ## §5 — ⚑ THE CERTIFIED BUNDLES, and the honest pole. -/

/-- The seam at link `j` as a `CertifiedSeam` — the bundle that cannot be built without S2. -/
def bodyPreimageCertifiedSeam (j : Nat) (hj : 2 * j < NABSORBED) :
    CertifiedSeam PreimageLeafSays ChainLinkSays (AbsorbsThePreimageAt j) :=
  { spec := bodyPreimageSeam j
  , wf := by
      have h := every_body_preimage_seam_is_wf
      have hmem : bodyPreimageSeam j ∈ bodyPreimageSeams := by
        refine List.mem_map.mpr ⟨j, List.mem_range.mpr ?_, rfl⟩
        have : NABSORBED = 49 := rfl
        have hb : BODY_LINKS = 25 := rfl
        omega
      exact List.all_eq_true.mp h _ hmem
  , certifies := bodyPreimageSeamCertifies j hj }

/-! ## §6 — ⚑⚑ THE HONEST POLE, ON THE REAL BLOCK — `SeamEq` IS INHABITED.

⚠ Without this, `bodyPreimageSeamCertifies` could be green over an UNSATISFIABLE `SeamEq` and
certify nothing at all — the `∃`-image vacuity this repo has already repaired once. The witnesses
are the real devnet block's own claims: `MinaBodyPreimageBitsAir.realPub` (the preimage descriptor's
honest PI vector) and `MinaStateBodyHashChain.bodyChainPIs j` (link `j`'s). -/

/-- The real block's preimage claim, as a claim VECTOR. -/
def realPreimageClaim : List ℤ :=
  (List.range PREIMAGE_CLAIM_LEN).map Dregg2.Circuit.Emit.MinaBodyPreimageBitsAir.realPub

/-- ⚑⚑ **THE SEAM HOLDS AT THE BLOCK'S OWN CLAIMS, AT EVERY LINK.** Twenty-five instances of
`SeamEq`, decided on the real witnesses — the preimage descriptor's published limbs against the
chain's absorbed blocks, including the `32 − ⌈W_e/8⌉` high zeros and the padding element's 32.
⚠ COMPILED: it reduces the 1 544-byte binprot parse, a two-block SHA-256 and the 819-chunk
assembly. -/
theorem the_preimage_seams_hold_on_the_real_block :
    ((List.range BODY_LINKS).all fun j =>
      ((bodyPreimageSeam j).pins.all fun p =>
        decide (realPreimageClaim.getD p.1 0
          = (Dregg2.Circuit.Emit.MinaStateBodyHashChain.bodyChainPIs j).getD p.2 0))
      && ((bodyPreimageSeam j).zeroRight.all fun i =>
        decide ((Dregg2.Circuit.Emit.MinaStateBodyHashChain.bodyChainPIs j).getD i 0 = 0)))
      = true := by
  native_decide

/-- ⚑⚑ **AND THE HONEST POLE IS NOT A STATEMENT ABOUT ZEROES — BUT IT IS NOT "EVERY LINK EITHER".**
A weld whose both sides were `0` everywhere would pass the theorem above and force nothing, so the
control names, EXACTLY, the links whose welded left slots are all zero.

⚠ **AND IT IS NOT THE EMPTY LIST, WHICH IS WHAT THIS FILE ASSERTED UNTIL 2026-08-10 AND WHAT
`native_decide` REFUSED.** The original control was `every link welds at least one non-zero value`;
it is **FALSE**, and the two counterexamples are not a defect in the seam. `Body.to_input` puts the
SOURCE and TARGET `Registers`' `Local_state.to_input` blocks at absorbed elements `9..12` and
`19..22` — an empty call stack, two zero transaction commitments, a zero local ledger — and a link
absorbs the PAIR `(2j, 2j+1)`, so links `5` (elements 10, 11) and `10` (elements 20, 21) weld two
genuinely-zero field elements and nothing else. The list below is that fact, and it is
cross-checkable against a measurement taken on the other side of the tree from the other object:
`circuit-prove/tests/mina_body_hash_chain_fold.rs` asserts the chain's own zero slots are
`[9, 10, 11, 12, 19, 20, 21, 22, 49]`, and `[5, 10]` is exactly its adjacent pairs.

⚑ So the control still refuses the degeneracy it exists to refuse — 23 of 25 links weld a non-zero
value, and the two that do not are NAMED rather than tolerated. A seam family that quietly welded
zeros everywhere would move this list, not satisfy it. -/
theorem the_real_welds_are_non_zero_except_at_the_two_local_state_links :
    ((List.range BODY_LINKS).filter fun j =>
      !((bodyPreimageSeam j).pins.any fun p =>
        decide (realPreimageClaim.getD p.1 0 ≠ 0))) = [5, 10] := by
  native_decide

/-! ## §7 — ⚠ WHAT THIS SEAM DOES NOT BUY, said in the same breath.

0. ⚑⚑ **THE CALL SITE EXISTS, AND THE REMAINING GAP IS ROUTING RATHER THAN ALGEBRA (2026-08-10).**
   The two surfaces this seam welds are `air_public_targets.first()` of two DIFFERENT leaves, and
   the older `apply_seam` call sites (`mina_wrap_finalize_fold.rs`, `mina_kimchi_verifier_gadget.rs`)
   weld two children's `expose_claim` instances instead — which is why the adapter had to be built
   rather than reused. `mina_body_preimage_adapter.rs` is it, and
   `circuit-prove/tests/mina_body_preimage_adapter.rs` drives BOTH POLES at the deployed prover: a
   preimage whose own descriptor accepts it (proved AND verified, asserted before the seam is asked
   anything) but which is not this block's is refused by `WitnessConflict`, as is the block's own
   preimage welded at the WRONG link — while seam `j` at link `j` proves.

   ⚠⚠ **AND IT IS NOT ROUTED, WHICH IS A WEAKER STATE THAN "DEPLOYED" AND IS RECORDED AS SUCH.**
   `circuit-prove/tests/mina_body_hash_chain_fold.rs` still folds PLAIN chain leaves, and
   `dregg_turn::executor::mina_head_verifier`'s REFUSAL 16 is still what a NODE runs. The 25-adapter
   whole-chain fold exists and terminates on block 540221's own `state_body_hash`, but it lives in
   an `#[ignore]`d test. **Tie 1 is a weld where the adapter runs; it is not yet what the deployed
   path runs**, and the difference is not rounded away here.
1. ⚠ **IT IS NOT AN IN-DESCRIPTOR CONSTRAINT.** `apply_seam` issues `cb.connect`s; the forcing lives
   in the recursion circuit, which proves on a box. `LightClientAnchorConnectivity`'s literals about
   `minaLinkDesc` do NOT move for a fold weld and must not be read as if they did — ⚠ and
   `minaLink_decorative_anchors`' docblock claim that *"the day a fold `cb.connect`s these slots
   in-circuit is the day this literal moves"* is **FALSE for the same reason**: a `cb.connect` emits
   no polynomial into `minaLinkDesc`. That tripwire is aimed at the right column and the wrong
   event, which is the class the 08-07 re-aiming already paid for once.
2. ⚠ **IT SAYS NOTHING ABOUT THE SECOND TIE.** The link rung's seventeen slots — `BODYHASH` (nine
   `Faithful9` lanes) and `BODY_ACC` (eight accumulator lanes) — are still covered by
   `MinaSeams.bodyHashWeld` / `bodyAccWeld`, i.e. by the executor's REFUSAL 16. ⚑ **And the
   `BODYHASH` half cannot be a `SeamSpec` at all as the two objects are encoded today**, for an
   arithmetic reason rather than a scheduling one: the chain publishes thirty-two 8-bit limbs and the
   link publishes nine 29-bit lanes, and a 256-bit recomposition is **not expressible as a BabyBear
   linear gate** — the coefficients `2^(8k)` run to `2^248` against a modulus below `2^31`, so the
   identity wraps. The transmutable fix is a bit-level re-limbing descriptor (256 boolean columns,
   32 byte-composition gates whose coefficients top out at `2^7`, 9 lane-composition gates whose
   coefficients top out at `2^28` — all inside BabyBear, all lookup-free, exactly this cone's own
   trick), which turns that tie into TWO descriptor-ended seams. **That is undone work, not a
   theorem of the model, and it is named here so it cannot be read as closed.**
3. ⚠ **NOTHING SAYS THE 49 ELEMENTS ARE A `Protocol_state.Body`.** `PICKLES_OPENING_WITNESSED`,
   unchanged.
-/

#assert_axioms the_claim_shapes_are_the_deployed_ones
#assert_axioms bodyPreimageSeams_length
#assert_axioms preimage_field_slot_is_published
#assert_axioms preimage_packed_slot_is_published
#assert_axioms chain_absorbed_0_is_register_three
#assert_axioms chain_absorbed_1_is_register_four_first_row
#assert_axioms the_body_preimage_seams_weld_published_slots
#assert_axioms digitsVal_zero_tail
#assert_axioms absorbedLimbCount_le_SK
#assert_axioms pi_absorbed_lt_claim_len
#assert_axioms bodyPreimageSeamCertifies
#assert_axioms zeroPreimage_says
#assert_axioms oneAbsorbing_says
#assert_axioms body_preimage_seam_S2_needs_the_seam

-- ⚑ COMPILER-TRUSTED, and said out loud: each reduces the 1 544-byte binprot parse, a two-block
-- SHA-256 and the 819-chunk assembly at every one of the twenty-five links.
#assert_compiled every_body_preimage_seam_is_wf
#assert_compiled the_seams_cover_every_absorbed_limb
#assert_compiled every_published_slot_is_welded_exactly_once
#assert_compiled the_preimage_seams_hold_on_the_real_block
#assert_compiled the_real_welds_are_non_zero_except_at_the_two_local_state_links
-- ⚠ `bodyPreimageCertifiedSeam` NAMES the compiled `wf` verdict, so the bundle inherits the
-- `native_decide` record. That is the honest tag, not a demotion — S1 and S2 are kernel-clean.
#assert_compiled bodyPreimageCertifiedSeam

end Dregg2.Circuit.Emit.MinaBodyPreimageSeams
