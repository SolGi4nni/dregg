/-
# `Dregg2.Circuit.Emit.MinaBodyHashRelimbSeams` — ⚑⚑⚑ **TIE 2, AS TWO DESCRIPTOR-ENDED SEAMS.**

## What this closes

The body-hash tie was an executor comparison (REFUSAL 16d) rather than a seam, for an arithmetic
reason: a direct `Σ_{k<32} 2^(8k)·limb_k = Σ_{l<9} 2^(29l)·lane_l` carries coefficients to `2^248`
against BabyBear's `2^31`, so it is not a linear gate. It still is not one and this file emits none.
`MinaBodyHashRelimbAir` publishes both spellings of one bit block — every coefficient at or below
`2^28` — so each END of the tie is an ELEMENTWISE pin list against a Lean-emitted descriptor, which
is exactly `SeamSpec`'s vocabulary.

## ⚑ THE TWO SEAMS

    dregg-pasta-fp-chainlink::v1              dregg-mina-bodyhash-relimb::v1
    PI [96, 128)  ─── byteSeam, 32 pins ───   PI [0, 32)     BYTE i
    (out lane 0, reg 4 LAST row,                   ↕  the_two_spellings_denote_one_value
     the squeezed `state_body_hash`)          PI [32, 41)    LANE l
                                                    │
                                              laneSeam, 9 pins
                                                    │
                                              dregg-mina-lightclient-link::v1  PI [20, 29)
                                              (`BODYHASH`, nine `Faithful9` lanes)

Both ends of both seams are **raw descriptor PI vectors** keyed by name AND recomputed fingerprint
lanes, which is what "descriptor-ended" means and is why `seam.rs::SeamEnd::require_matches` can
refuse a stale artifact at load.

⚑ **AND THE MIDDLE IS A THEOREM, NOT A GATE.** The two seams meet at the re-limb claim, and what
carries a value across it is `MinaBodyHashRelimbAir.the_two_spellings_denote_one_value` — a
regrouping of one bit block, no hypothesis, no coefficient above `2^28`.
`the_chains_body_hash_is_the_links_body_hash` is the composition: **the felt the chain squeezed IS
the felt the light client's nonet denotes.**

## ⚠ STANDING, SAID PLAINLY

A `SeamSpec` does not turn recursion wiring into AIR (`SeamSpec.lean` §"What a `SeamSpec` does NOT
claim"). The connects are issued by `circuit-prove` reading these artifacts; the recursion circuit
proves on a box and inherits the undischarged FRI/STARK floor. What changed is that the tie is an
OBJECT with S1 (pin lists naming published slots of the deployed AIRs) and S2 (named composition
theorems, each shown FALSE without its seam hypothesis) instead of a `WeldCover` naming an executor
function — and that the port census can now say **closed by seam, theorem S2** where it said
*"covered by REFUSAL 16d"*.

⚠ **AND IT IS NOT ROUTED.** No fold applies these two seams yet; `check_body_chain_binding`
(REFUSAL 16) is still what a node runs. The same weaker-than-deployed state
`MinaBodyPreimageSeams` §7.0 records for tie 1, recorded here rather than rounded away.

## Axiom hygiene

Kernel-clean throughout; the real-block instances are `native_decide` + `#assert_compiled` and say
so. No `sorry`, no `#guard`, no new axiom.
-/
import Dregg2.Circuit.Emit.SeamSpec
import Dregg2.Circuit.Emit.MinaBodyHashRelimbAir
import Dregg2.Circuit.Emit.MinaBodyPreimageSeams
import Dregg2.Circuit.Emit.MinaSeams

namespace Dregg2.Circuit.Emit.MinaBodyHashRelimbSeams

open Dregg2.Circuit.EffectAirIR (EffectAir AirLeg PiPinLeg)
open Dregg2.Circuit.Emit.EffectVmEmit (VmRow)
open Dregg2.Circuit.Emit.Seam
open Dregg2.Circuit.Emit.PastaFieldSound (SK SB limbAt)
open Dregg2.Circuit.Emit.MinaBodyHashRelimbAir
  (NBIT NBYTE NLANE LB TOP_LB PI_BYTE PI_LANE BYTE LANE RELIMB_PI_COUNT relimbAir relimbRowOk
   bytePin lanePin claimByteValue claimLaneValue digitsValW rowOfValue pubOfValue
   the_two_spellings_denote_one_value every_canonical_value_has_an_accepted_row
   the_accepted_row_denotes_its_value)

set_option autoImplicit false
set_option maxRecDepth 100000

/-! ## §1 — ⚑ THE THREE CLAIM LAYOUTS, AND THE CONSTANT RECONCILIATION.

⚠ Both ends of both seams are RAW descriptor PI vectors (`apt.first()`), not `expose_claim`s — the
same measured constraint `MinaBodyPreimageSeams` §1 records: a fold ROOT carries a 200-lane claim
that does not contain the chain's outgoing block, so the only surface that reaches it is the leaf's
own descriptor PI vector. `SeamEnd` is descriptor-keyed, which is the right key for that surface. -/

/-- The re-limb leaf's claim surface: the whole 41-slot PI vector of
`dregg-mina-bodyhash-relimb::v1` — 32 byte slots, then 9 lane slots. -/
def RELIMB_CLAIM_LEN : Nat := RELIMB_PI_COUNT

/-- The chain link leaf's claim surface: the whole 256-slot PI vector of
`dregg-pasta-fp-chainlink::v1`, `in(96) ‖ out(96) ‖ absorbed(64)`. -/
def CHAIN_CLAIM_LEN : Nat := Dregg2.Circuit.Emit.MinaPhase1Chain.CHAIN_PI_COUNT

/-- The link segment leaf's claim surface: the whole 46-slot PI vector of
`dregg-mina-lightclient-link::v1`. ⚑ 46 since `d12a348c6` published `PI_HEAD_OWN` at 37..45. -/
def LINK_CLAIM_LEN : Nat := Dregg2.Circuit.Emit.LightClientMinaLinkAir.MINA_LINK_PI_COUNT

/-- ⚑ Claim offset of the chain link's OUTGOING lane 0 — register 4's **LAST**-row pin block,
descriptor PI slot `3·SK`. ⚠ NOT register 4's FIRST-row block, which is
`MinaBodyPreimageSeams.CHAIN_ABSORBED_1` at `7·SK` — the row selector is the only discriminator and
a copy-paste that took the wrong one would weld the light client's body hash onto the absorbed
stream. -/
def CHAIN_OUT_LANE0 : Nat := 3 * SK

/-- The link's `BODYHASH` block base. -/
def LINK_BODYHASH_0 : Nat := Dregg2.Circuit.Emit.LightClientMinaLinkAir.PI_BODYHASH 0

theorem the_claim_shapes_are_the_deployed_ones :
    RELIMB_CLAIM_LEN = 41 ∧ CHAIN_CLAIM_LEN = 256 ∧ LINK_CLAIM_LEN = 46
      ∧ CHAIN_OUT_LANE0 = 96 ∧ LINK_BODYHASH_0 = 20
      ∧ CHAIN_OUT_LANE0 + SK = 128
      ∧ Dregg2.Circuit.Emit.LightClientMinaLinkAir.PI_BODYHASH 8 = 28 := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- ⚑⚑ **THE LANE CONSTANTS ARE THE LINK'S OWN — the forced reconciliation.**
`MinaBodyHashRelimbAir` restates `LB`/`TOP_LB`/`NLANE` locally so an EMIT cone need not evaluate
the link AIR at initialization; two constants for one fact is the twin this repo forbids, so the
agreement is a `rfl` theorem rather than a docblock. ⚠ It goes RED the day either side moves, which
is exactly when the re-limbing stops being the link's spelling. -/
theorem the_lane_widths_are_the_links :
    LB = Dregg2.Circuit.Emit.LightClientMinaAir.MINA_LANE_BITS
      ∧ TOP_LB = Dregg2.Circuit.Emit.LightClientMinaAir.MINA_TOP_LANE_BITS
      ∧ NLANE = Dregg2.Circuit.Emit.LightClientMinaAir.STATE_LIMBS
      ∧ NBYTE = SK
      ∧ LB * 8 + TOP_LB = NBIT := by
  refine ⟨rfl, rfl, rfl, rfl, rfl⟩

/-! ## §2 — ⚑ THE TWO SEAMS. -/

/-- ⚑ `effect_vm_descriptor2_semantic_fingerprint(dregg-mina-bodyhash-relimb::v1)`, as `Faithful9`
key lanes.

⚠ **MEASURED-OR-NOTHING.** Lean cannot compute blake3, so this literal is a MEASUREMENT of the
served artifact and nothing else. `EmitSeamSpecs` REFUSES to write either seam of this family while
the value is the unmeasured sentinel (`theRelimbLanesAreUnmeasured` is the verdict it reads), so an
unmeasured lane vector produces NO artifact rather than a plausible one — and
`seam.rs::SeamEnd::require_matches` RECOMPUTES the lanes from the descriptor it loads and refuses a
mismatch, so a STALE one is a loud red on the Rust side.

⚠ **FLAG DAY COUPLING:** re-emitting `dregg-mina-bodyhash-relimb-v1.json` moves this literal and
re-emits both seam artifacts.

⚑ **MEASURED 2026-08-10** by `cargo run -p dregg-circuit --release --example conj_fingerprint --
circuit/descriptors/by-name/dregg-mina-bodyhash-relimb-v1.json`, over the bytes at
`w=295 pi=41 cons=336`,
`fp=722c7fe68022970567e5cc31554d6f7a6deb3d01d2a5b2b2920c7fda3cf29bb0`. The sentinel below is
therefore FALSE and `EmitSeamSpecs` emits both rows. -/
def RELIMB_VK_LANES : List ℤ :=
  [108997746, 213455879, 322525633, 513452643, 515299238, 317259934, 306891466, 127619041, 11574258]

/-- ⚑ **THE UNMEASURED SENTINEL, AS A VERDICT.** A gate that cannot go red is not a gate: this one
is `true` exactly while the lanes above are the all-zero placeholder, and `EmitSeamSpecs` refuses to
emit while it is. -/
def theRelimbLanesAreUnmeasured : Bool := RELIMB_VK_LANES == List.replicate 9 (0 : ℤ)


/-- ⚑⚑ **THE BYTE SEAM** — the re-limb claim's 32 byte slots against the chain link's outgoing
lane 0, elementwise at full limb width. No digest, therefore no birthday bound
(`Seam.limb_inj`). -/
def bodyHashByteSeam : SeamSpec :=
  { name  := "dregg-seam-bodyhash-bytes-to-chain::v1"
  , left  := { claim := "mina-bodyhash-relimb-leaf", claimLen := RELIMB_CLAIM_LEN
             , descName := "dregg-mina-bodyhash-relimb::v1", descLanes := RELIMB_VK_LANES }
  , right := { claim := "mina-body-chain-leaf", claimLen := CHAIN_CLAIM_LEN
             , descName := "dregg-pasta-fp-chainlink::v1"
             , descLanes := Dregg2.Circuit.Emit.LightClientMinaLinkAir.FP_CHAINLINK_VK_LANES }
  , pins := (List.range NBYTE).map (fun i => (PI_BYTE i, CHAIN_OUT_LANE0 + i))
  , zeroLeft := []
  , zeroRight := [] }

/-- ⚑⚑ **THE LANE SEAM** — the re-limb claim's 9 lane slots against the link's `BODYHASH` nonet,
elementwise. -/
def bodyHashLaneSeam : SeamSpec :=
  { name  := "dregg-seam-bodyhash-lanes-to-link::v1"
  , left  := { claim := "mina-bodyhash-relimb-leaf", claimLen := RELIMB_CLAIM_LEN
             , descName := "dregg-mina-bodyhash-relimb::v1", descLanes := RELIMB_VK_LANES }
  , right := { claim := "mina-link-leaf", claimLen := LINK_CLAIM_LEN
             , descName := "dregg-mina-lightclient-link::v1"
             , descLanes := Dregg2.Circuit.Emit.LightClientMinaAir.LINK_VK_LANES }
  , pins := (List.range NLANE).map (fun l =>
              (PI_LANE l, Dregg2.Circuit.Emit.LightClientMinaLinkAir.PI_BODYHASH l))
  , zeroLeft := []
  , zeroRight := [] }

def relimbSeams : List SeamSpec := [bodyHashByteSeam, bodyHashLaneSeam]

/-- ⚑ **THE LINK END'S FINGERPRINT IS THE LINK AIR'S OWN LITERAL — one source, not a copy.**
`LightClientMinaAir.LINK_VK_LANES` is the head descriptor's pin of this same descriptor; re-measured
2026-08-10 against the served `dregg-mina-lightclient-link-v1.json` (`w=57 pi=46 cons=108`,
`fp=1e908aa5...`) it AGREES, so this family carries no second literal.
`the_link_end_is_the_link_airs_own_pin` is the `rfl` that keeps it that way.

⚑ The chainlink end likewise reads `LightClientMinaLinkAir.FP_CHAINLINK_VK_LANES`: the temporary
second measured literal used while the canonical-record flag day was pending has been merged, so
both seam families and the link AIR now name one fact. -/
theorem the_link_end_is_the_link_airs_own_pin :
    bodyHashLaneSeam.right.descLanes
      = Dregg2.Circuit.Emit.LightClientMinaAir.LINK_VK_LANES := rfl

/-- ⚑ **BOTH SEAMS ARE WELL-FORMED** — indices in range on both ends, nine fingerprint lanes per
end, non-empty. -/
theorem both_relimb_seams_are_wf : relimbSeams.all (fun s => s.wf) = true := by decide

/-- ⚑⚑ **THE TWO SEAMS COVER THE WHOLE RE-LIMB CLAIM, EXACTLY ONCE.** Every one of the 41 published
slots is welded by exactly one seam, and no slot is welded twice — the aliasing bug a count alone
cannot see. ⚠ Without this, a seam pair could weld the bytes twice and leave the lanes free. -/
theorem the_two_seams_weld_every_published_slot_exactly_once :
    ((relimbSeams.flatMap (fun s => s.pins.map Prod.fst)).mergeSort (· ≤ ·))
        = List.range RELIMB_CLAIM_LEN
      ∧ bodyHashByteSeam.pins.length = NBYTE
      ∧ bodyHashLaneSeam.pins.length = NLANE
      ∧ (relimbSeams.all (fun s => s.zeroLeft.isEmpty && s.zeroRight.isEmpty)) = true := by
  refine ⟨?_, rfl, rfl, rfl⟩
  native_decide

/-- ⚑ **AND NO ZERO-PIN IS NEEDED, WHICH IS A STATEMENT ABOUT THE LAYOUT.** `MinaBodyPreimageSeams`
carries 82 zero-pins because its left claim allocates `⌈W_e/8⌉` limbs against the chain's 32. Here
both partitions cover the SAME 254 bits and the chain block is exactly `SK`, so the weld is total
and a zero-pin would be a column the descriptor does not have. -/
theorem the_seams_are_total_and_need_no_zero_pins :
    bodyHashByteSeam.pins.length = SK
      ∧ bodyHashLaneSeam.pins.length
          = Dregg2.Circuit.Emit.LightClientMinaAir.STATE_LIMBS
      ∧ bodyHashByteSeam.zeroRight = [] ∧ bodyHashLaneSeam.zeroRight = [] := by
  refine ⟨rfl, rfl, rfl, rfl⟩

/-! ## §3 — S1: the pin lists name exactly the published slots they claim to.

Memberships in the ACTUAL `EffectAir` leg lists, constructed rather than decided. ⚠ Spelled with
`simp only [..., List.mem_append]; tauto` rather than a hand-counted `mem_append_left/right` chain,
which encodes the leg list's APPEND NESTING and reds with a type mismatch when a pin block is
appended anywhere — the accident the `headOwnPins` flag day paid for on 2026-08-10. -/

/-- The re-limb leaf publishes byte `i` at claim slot `PI_BYTE i`. -/
theorem relimb_byte_slot_is_published (i : Nat) (hi : i < NBYTE) :
    AirLeg.pin ⟨VmRow.first, BYTE i, PI_BYTE i⟩ ∈ relimbAir.legs := by
  have hmem : AirLeg.pin ⟨VmRow.first, BYTE i, PI_BYTE i⟩
      ∈ (List.range NBYTE).map bytePin :=
    List.mem_map.mpr ⟨i, List.mem_range.mpr hi, rfl⟩
  simp only [relimbAir, List.mem_append]
  tauto

/-- …and lane `l` at claim slot `PI_LANE l`. -/
theorem relimb_lane_slot_is_published (l : Nat) (hl : l < NLANE) :
    AirLeg.pin ⟨VmRow.first, LANE l, PI_LANE l⟩ ∈ relimbAir.legs := by
  have hmem : AirLeg.pin ⟨VmRow.first, LANE l, PI_LANE l⟩
      ∈ (List.range NLANE).map lanePin :=
    List.mem_map.mpr ⟨l, List.mem_range.mpr hl, rfl⟩
  simp only [relimbAir, List.mem_append]
  tauto

/-- ⚑ The chain link's OUTGOING lane 0 is register 4's **LAST**-row pin block — claim slots
`[3·SK, 4·SK)`. ⚠ The row selector is the discriminator; register 4's FIRST-row block at `7·SK` is
the second absorbed element. -/
theorem chain_out_lane0_is_register_four_last_row (i : Nat) (hi : i < SK) :
    AirLeg.pin ⟨VmRow.last, Dregg2.Circuit.Emit.MinaWrapVerifierProgram.regCol 4 + i,
        3 * SK + i⟩
      ∈ Dregg2.Circuit.Emit.MinaPhase1Chain.chainAir.legs := by
  have hmem : AirLeg.pin ⟨VmRow.last,
      Dregg2.Circuit.Emit.MinaWrapVerifierProgram.regCol 4 + i, 3 * SK + i⟩
      ∈ Dregg2.Circuit.Emit.MinaWrapVerifierSponge.pinBlock VmRow.last 4 (3 * SK) :=
    List.mem_map.mpr ⟨i, List.mem_range.mpr hi, rfl⟩
  simp only [Dregg2.Circuit.Emit.MinaPhase1Chain.chainAir,
    Dregg2.Circuit.Emit.MinaPhase2Chain.chainPins, List.mem_append]
  tauto

/-- ⚑ **S1 FOR BOTH SEAMS.** Every endpoint of every weld is a slot a real pin leg of the deployed
AIR publishes, and the pin lists are exactly the two contiguous blocks. The link end reuses
`MinaSeams`' own publication witness rather than a second copy of it. -/
theorem the_relimb_seams_weld_published_slots :
    bodyHashByteSeam.pins = (List.range NBYTE).map (fun i => (PI_BYTE i, CHAIN_OUT_LANE0 + i))
    ∧ bodyHashLaneSeam.pins = (List.range NLANE).map (fun l =>
        (PI_LANE l, Dregg2.Circuit.Emit.LightClientMinaLinkAir.PI_BODYHASH l))
    ∧ (∀ i, i < NBYTE → AirLeg.pin ⟨VmRow.first, BYTE i, PI_BYTE i⟩ ∈ relimbAir.legs)
    ∧ (∀ l, l < NLANE → AirLeg.pin ⟨VmRow.first, LANE l, PI_LANE l⟩ ∈ relimbAir.legs)
    ∧ (∀ i, i < SK →
        AirLeg.pin ⟨VmRow.last, Dregg2.Circuit.Emit.MinaWrapVerifierProgram.regCol 4 + i,
            3 * SK + i⟩ ∈ Dregg2.Circuit.Emit.MinaPhase1Chain.chainAir.legs) :=
  ⟨rfl, rfl, relimb_byte_slot_is_published, relimb_lane_slot_is_published,
   chain_out_lane0_is_register_four_last_row⟩

/-! ## §4 — ⚑ THE SENTENCES AND S2, WITH BOTH POLES. -/

/-- A claim vector of the re-limb leaf, as the descriptor's own claim function produces it. -/
def relimbClaimOf (v : Nat) : List ℤ := (List.range RELIMB_CLAIM_LEN).map (pubOfValue v)

theorem relimbClaimOf_get (v s : Nat) (hs : s < RELIMB_CLAIM_LEN) :
    (relimbClaimOf v).getD s 0 = pubOfValue v s := by
  unfold relimbClaimOf
  rw [List.getD_eq_getElem?_getD, List.getElem?_map]
  simp [hs]

/-- Byte slot `i` is inside the claim. -/
theorem byteSlot_lt {i : Nat} (hi : i < NBYTE) : PI_BYTE i < RELIMB_CLAIM_LEN := by
  unfold PI_BYTE RELIMB_CLAIM_LEN Dregg2.Circuit.Emit.MinaBodyHashRelimbAir.RELIMB_PI_COUNT
  unfold NBYTE NLANE at *
  omega

/-- Lane slot `l` is inside the claim. -/
theorem laneSlot_lt {l : Nat} (hl : l < NLANE) : PI_LANE l < RELIMB_CLAIM_LEN := by
  unfold PI_LANE RELIMB_CLAIM_LEN Dregg2.Circuit.Emit.MinaBodyHashRelimbAir.RELIMB_PI_COUNT
  unfold NLANE at *
  omega

/-- ⚑ **WHAT THE RE-LIMB LEAF'S CLAIM SAYS** — there is a row this descriptor accepts publishing
it. That is the whole sentence, and it is exactly what the STARK's acceptance buys: the byte block
and the lane block are two readings of one gated boolean bit vector. -/
def RelimbLeafSays (lv : List ℤ) : Prop :=
  ∃ row : Nat → ℤ, relimbRowOk row (fun s => lv.getD s 0)

/-- **WHAT THE CHAIN LINK'S CLAIM SAYS** — its outgoing lane 0 renders a canonical value.
Existential in the value, faithfully: WHICH value is what the seam supplies. -/
def ChainOutSays (rv : List ℤ) : Prop := ∃ x : Nat, Renders rv CHAIN_OUT_LANE0 x

/-- **WHAT THE LINK'S CLAIM SAYS** — its `BODYHASH` nonet is in the canonicality window its own
lane lookups enforce: eight lanes below `2^29` and the top below `2^22`, i.e. a value below `2^254`
(`LightClientMinaAir.MINA_TOP_LANE_BITS`' own reading). -/
def LinkBodyHashSays (rv : List ℤ) : Prop :=
  (∀ l, l + 1 < NLANE →
      0 ≤ rv.getD (Dregg2.Circuit.Emit.LightClientMinaLinkAir.PI_BODYHASH l) 0
        ∧ rv.getD (Dregg2.Circuit.Emit.LightClientMinaLinkAir.PI_BODYHASH l) 0 < 2 ^ LB)
  ∧ 0 ≤ rv.getD (Dregg2.Circuit.Emit.LightClientMinaLinkAir.PI_BODYHASH (NLANE - 1)) 0
  ∧ rv.getD (Dregg2.Circuit.Emit.LightClientMinaLinkAir.PI_BODYHASH (NLANE - 1)) 0 < 2 ^ TOP_LB

/-- ⚑ **THE COMPOSED SENTENCE OF THE BYTE SEAM.** The value the chain squeezed IS the value the
re-limb claim's NINE LANES denote — the crossing happens inside the re-limb claim, by
`the_two_spellings_denote_one_value`, and that is what a BabyBear gate could not do. -/
def ChainOutIsTheRelimbedNonet (lv rv : List ℤ) : Prop :=
  ∃ x : Nat, Renders rv CHAIN_OUT_LANE0 x ∧ (x : ℤ) = claimLaneValue (fun s => lv.getD s 0)

/-- The value the link's published nonet denotes, base `2^LB`. -/
def linkNonetValue (rv : List ℤ) : ℤ :=
  digitsValW LB (fun l =>
    rv.getD (Dregg2.Circuit.Emit.LightClientMinaLinkAir.PI_BODYHASH l) 0) NLANE

/-- ⚑ **THE COMPOSED SENTENCE OF THE LANE SEAM.** The link's published nonet denotes the value the
re-limb claim's THIRTY-TWO BYTES denote. -/
def LinkNonetIsTheRelimbedBytes (lv rv : List ℤ) : Prop :=
  linkNonetValue rv = claimByteValue (fun s => lv.getD s 0)

/-- The bridge from a `Renders` to the byte reading: a rendered block's `digitsVal` IS its value. -/
private theorem renders_byteValue {rv : List ℤ} {base s : Nat} (h : Renders rv base s) :
    digitsValW SB (fun i => rv.getD (base + i) 0) SK = (s : ℤ) := by
  have hcast : digitsValW SB (fun i => rv.getD (base + i) 0) SK
      = Dregg2.Circuit.Emit.Seam.digitsVal (fun i => rv.getD (base + i) 0) SK := rfl
  rw [hcast, digitsVal_congr (n := SK) (g := limbAt s) (fun i hi => h.2 i hi), digitsVal_limb]
  exact_mod_cast congrArg (fun n : Nat => (n : ℤ)) (Nat.mod_eq_of_lt h.1)

/-- ⚑⚑⚑ **S2 FOR THE BYTE SEAM.** The 32 welds carry the chain's squeezed value onto the re-limb
claim's byte block, and the re-limbing carries it across to the lane block. -/
theorem bodyHashByteSeamCertifies :
    SeamCertifies bodyHashByteSeam RelimbLeafSays ChainOutSays ChainOutIsTheRelimbedNonet := by
  rintro lv rv ⟨row, hrow⟩ ⟨x, hx⟩ ⟨hpins, -, -⟩
  refine ⟨x, hx, ?_⟩
  -- the seam makes the claim's byte slots the chain block's limbs
  have hbyte : ∀ i, i < NBYTE → lv.getD (PI_BYTE i) 0 = rv.getD (CHAIN_OUT_LANE0 + i) 0 := by
    intro i hi
    exact hpins (PI_BYTE i, CHAIN_OUT_LANE0 + i)
      (List.mem_map.mpr ⟨i, List.mem_range.mpr hi, rfl⟩)
  have hval : claimByteValue (fun s => lv.getD s 0) = (x : ℤ) := by
    unfold claimByteValue
    have hcong : digitsValW SB (fun i => lv.getD (PI_BYTE i) 0) NBYTE
        = digitsValW SB (fun i => rv.getD (CHAIN_OUT_LANE0 + i) 0) SK :=
      Dregg2.Circuit.Emit.MinaBodyHashRelimbAir.digitsValW_congr
        (fun i hi => hbyte i hi)
    rw [hcong, renders_byteValue hx]
  rw [← hval, the_two_spellings_denote_one_value hrow]

/-- ⚑⚑⚑ **S2 FOR THE LANE SEAM.** The 9 welds carry the re-limb claim's lane block onto the link's
published nonet, and the re-limbing says that block is the byte block's value. -/
theorem bodyHashLaneSeamCertifies :
    SeamCertifies bodyHashLaneSeam RelimbLeafSays LinkBodyHashSays LinkNonetIsTheRelimbedBytes := by
  rintro lv rv ⟨row, hrow⟩ - ⟨hpins, -, -⟩
  have hlane : ∀ l, l < NLANE →
      lv.getD (PI_LANE l) 0
        = rv.getD (Dregg2.Circuit.Emit.LightClientMinaLinkAir.PI_BODYHASH l) 0 := by
    intro l hl
    exact hpins (PI_LANE l, Dregg2.Circuit.Emit.LightClientMinaLinkAir.PI_BODYHASH l)
      (List.mem_map.mpr ⟨l, List.mem_range.mpr hl, rfl⟩)
  unfold LinkNonetIsTheRelimbedBytes linkNonetValue
  rw [the_two_spellings_denote_one_value hrow]
  unfold claimLaneValue
  exact (Dregg2.Circuit.Emit.MinaBodyHashRelimbAir.digitsValW_congr
    (fun l hl => hlane l hl)).symm

/-- ⚑⚑⚑ **TIE 2, COMPOSED — THE CHAIN'S `state_body_hash` IS THE LIGHT CLIENT'S `BODYHASH`.**
Both seams at once, over three claims: the value the body-hash chain squeezed at its terminal link
IS the felt the link descriptor's published nonet denotes. ⚠ The re-limb claim is the only place
the two encodings meet, and what carries the value across it is a theorem about one bit block, not
a gate — which is exactly the blocker `MinaBodyPreimageSeams` §7.2 measured and named. -/
theorem the_chains_body_hash_is_the_links_body_hash
    (lv rvChain rvLink : List ℤ)
    (hL : RelimbLeafSays lv) (hC : ChainOutSays rvChain) (hK : LinkBodyHashSays rvLink)
    (hA : SeamEq bodyHashByteSeam lv rvChain)
    (hB : SeamEq bodyHashLaneSeam lv rvLink) :
    ∃ x : Nat, Renders rvChain CHAIN_OUT_LANE0 x ∧ (x : ℤ) = linkNonetValue rvLink := by
  obtain ⟨x, hx, hxval⟩ := bodyHashByteSeamCertifies lv rvChain hL hC hA
  have hlane := bodyHashLaneSeamCertifies lv rvLink hL hK hB
  refine ⟨x, hx, ?_⟩
  rw [hxval]
  unfold LinkNonetIsTheRelimbedBytes at hlane
  rw [hlane]
  -- both readings of the re-limb claim are one value
  obtain ⟨row, hrow⟩ := hL
  exact (the_two_spellings_denote_one_value hrow).symm

/-! ### §4a — ⚑⚑ THE RED POLE: EACH S2 WITHOUT ITS SEAM HYPOTHESIS IS FALSE.

Not unprovable — FALSE, on concrete claims, kernel-clean. The model is
`MinaBodyPreimageSeams.body_preimage_seam_S2_needs_the_seam`: an all-zero left claim that genuinely
satisfies its sentence, against a right claim carrying `1`, with the composed sentence forcing
`(1 : ℤ) = 0`. -/

/-- The re-limb claim of the value ZERO — every one of its 41 slots is `0`, and it genuinely
satisfies `RelimbLeafSays` because `rowOfValue 0` is a row the descriptor accepts. -/
def zeroRelimbClaim : List ℤ := relimbClaimOf 0

theorem zeroRelimb_says : RelimbLeafSays zeroRelimbClaim := by
  refine ⟨rowOfValue 0, ?_⟩
  obtain ⟨h1, h2, h3, h4, h5⟩ := every_canonical_value_has_an_accepted_row 0
  refine ⟨h1, h2, h3, ?_, ?_⟩
  · intro i hi
    show zeroRelimbClaim.getD (PI_BYTE i) 0 = rowOfValue 0 (BYTE i)
    unfold zeroRelimbClaim
    rw [relimbClaimOf_get 0 (PI_BYTE i) (byteSlot_lt hi)]
    exact h4 i hi
  · intro l hl
    show zeroRelimbClaim.getD (PI_LANE l) 0 = rowOfValue 0 (LANE l)
    unfold zeroRelimbClaim
    rw [relimbClaimOf_get 0 (PI_LANE l) (laneSlot_lt hl)]
    exact h5 l hl

/-- Both readings of the zero claim are `0` — the value the composed sentences would have to
equal. Read off `the_accepted_row_denotes_its_value` at `v = 0` rather than re-decided. -/
theorem zeroRelimb_readings_are_zero :
    claimByteValue (fun s => zeroRelimbClaim.getD s 0) = 0
      ∧ claimLaneValue (fun s => zeroRelimbClaim.getD s 0) = 0 := by
  obtain ⟨hb0, hl0⟩ := the_accepted_row_denotes_its_value 0
  have hb : claimByteValue (fun s => zeroRelimbClaim.getD s 0) = claimByteValue (pubOfValue 0) := by
    unfold claimByteValue
    exact Dregg2.Circuit.Emit.MinaBodyHashRelimbAir.digitsValW_congr
      (fun i hi => relimbClaimOf_get 0 (PI_BYTE i) (byteSlot_lt hi))
  have hl : claimLaneValue (fun s => zeroRelimbClaim.getD s 0) = claimLaneValue (pubOfValue 0) := by
    unfold claimLaneValue
    exact Dregg2.Circuit.Emit.MinaBodyHashRelimbAir.digitsValW_congr
      (fun l hl => relimbClaimOf_get 0 (PI_LANE l) (laneSlot_lt hl))
  refine ⟨?_, ?_⟩
  · rw [hb, hb0]; norm_num
  · rw [hl, hl0]; norm_num

/-- The `SK` base-256 limbs of `a`, as a claim block. -/
def limbBlock (a : Nat) : List ℤ := (List.range SK).map (limbAt a)

/-- A chain claim whose outgoing lane 0 renders `1`. -/
def oneSqueezingChainClaim : List ℤ := List.replicate (3 * SK) 0 ++ limbBlock 1

private theorem limbBlock_length (a : Nat) : (limbBlock a).length = SK := by simp [limbBlock]

theorem oneSqueezing_renders : Renders oneSqueezingChainClaim CHAIN_OUT_LANE0 1 := by
  refine ⟨by decide +kernel, fun i hi => ?_⟩
  show (List.replicate (3 * SK) (0 : ℤ) ++ limbBlock 1).getD (3 * SK + i) 0 = limbAt 1 i
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by simp),
    List.length_replicate, Nat.add_sub_cancel_left]
  simp [limbBlock, hi]

theorem oneSqueezing_says : ChainOutSays oneSqueezingChainClaim := ⟨1, oneSqueezing_renders⟩

/-- ⚑⚑⚑ **THE BYTE SEAM'S REFUTER.** Delete `SeamEq` from S2 and the implication is FALSE.
Kernel-clean: an all-zero re-limb claim (which really is an accepted claim) against a chain claim
squeezing `1`, both child sentences hold, and the contradiction is `(1 : ℤ) = 0`. -/
theorem byte_seam_S2_needs_the_seam :
    ¬ (∀ lv rv, RelimbLeafSays lv → ChainOutSays rv → ChainOutIsTheRelimbedNonet lv rv) := by
  intro h
  obtain ⟨x, hx, hxval⟩ :=
    h zeroRelimbClaim oneSqueezingChainClaim zeroRelimb_says oneSqueezing_says
  have hx1 : x = 1 := Renders.eq_of_weld hx oneSqueezing_renders (fun _ _ => rfl)
  rw [hx1, zeroRelimb_readings_are_zero.2] at hxval
  exact absurd hxval (by norm_num)

/-- A link claim whose `BODYHASH` nonet is `[1, 0, …, 0]` — in range on every lane, so it really
does satisfy the link's own canonicality sentence. -/
def oneLinkClaim : List ℤ :=
  List.replicate LINK_BODYHASH_0 0 ++ [1] ++ List.replicate (LINK_CLAIM_LEN - LINK_BODYHASH_0 - 1) 0

theorem oneLink_bodyhash (l : Nat) (hl : l < NLANE) :
    oneLinkClaim.getD (Dregg2.Circuit.Emit.LightClientMinaLinkAir.PI_BODYHASH l) 0
      = (if l = 0 then 1 else 0) := by
  have h : ∀ l < NLANE,
      oneLinkClaim.getD (Dregg2.Circuit.Emit.LightClientMinaLinkAir.PI_BODYHASH l) 0
        = (if l = 0 then 1 else 0) := by decide
  exact h l hl

theorem oneLink_says : LinkBodyHashSays oneLinkClaim := by
  refine ⟨fun l hl => ?_, ?_, ?_⟩
  · rw [oneLink_bodyhash l (by unfold NLANE at *; omega)]
    by_cases h : l = 0
    · subst h; rw [if_pos rfl]; exact ⟨by decide, by decide⟩
    · rw [if_neg h]; exact ⟨by decide, by decide⟩
  · rw [oneLink_bodyhash (NLANE - 1) (by decide)]; decide
  · rw [oneLink_bodyhash (NLANE - 1) (by decide)]; decide

/-- ⚑⚑⚑ **THE LANE SEAM'S REFUTER.** Same shape on the other end: the link's nonet denotes `1`
and the all-zero re-limb claim's byte block denotes `0`. -/
theorem lane_seam_S2_needs_the_seam :
    ¬ (∀ lv rv, RelimbLeafSays lv → LinkBodyHashSays rv → LinkNonetIsTheRelimbedBytes lv rv) := by
  intro h
  have hc := h zeroRelimbClaim oneLinkClaim zeroRelimb_says oneLink_says
  unfold LinkNonetIsTheRelimbedBytes at hc
  rw [zeroRelimb_readings_are_zero.1] at hc
  have hone : linkNonetValue oneLinkClaim = 1 := by
    unfold linkNonetValue
    rw [Dregg2.Circuit.Emit.MinaBodyHashRelimbAir.digitsValW_congr
      (g := fun l => (if l = 0 then 1 else 0 : ℤ))
      (fun l hl => oneLink_bodyhash l hl)]
    decide
  rw [hone] at hc
  exact absurd hc (by norm_num)

/-! ## §5 — ⚑ THE CERTIFIED BUNDLES. -/

def bodyHashByteCertifiedSeam :
    CertifiedSeam RelimbLeafSays ChainOutSays ChainOutIsTheRelimbedNonet :=
  { spec := bodyHashByteSeam, certifies := bodyHashByteSeamCertifies }

def bodyHashLaneCertifiedSeam :
    CertifiedSeam RelimbLeafSays LinkBodyHashSays LinkNonetIsTheRelimbedBytes :=
  { spec := bodyHashLaneSeam, certifies := bodyHashLaneSeamCertifies }

/-! ## §6 — ⚑⚑ THE HONEST POLE, ON THE REAL BLOCK — `SeamEq` IS INHABITED.

⚠ Without this, both `SeamCertifies` could be green over an UNSATISFIABLE `SeamEq` and certify
nothing at all — the `∃`-image vacuity this repo has already repaired once. The witnesses are the
devnet block 540221's own objects. -/

/-- The real block's `state_body_hash`, from the chain that derives it. -/
def realBodyHash : Nat := Dregg2.Circuit.Emit.MinaStateBodyHashChain.realBodyHash

/-- ⚑⚑ **THE REAL BODY HASH IS INSIDE THE 254-BIT WINDOW.** ⚠ This is a genuine check and not a
formality: `pN` exceeds `2^254`, so an `Fp` element in `[2^254, pN)` exists, has no accepted row in
`MinaBodyHashRelimbAir`, and would make the byte seam UNSATISFIABLE rather than mis-welded. Block
540221's is not one, and a block whose is would refuse. -/
theorem the_real_body_hash_is_below_two_254 : realBodyHash < 2 ^ NBIT := by native_decide

/-- The real block's re-limb claim. -/
def realRelimbClaim : List ℤ := relimbClaimOf realBodyHash

/-- ⚑⚑ **THE BYTE SEAM HOLDS AT THE BLOCK'S OWN CLAIMS.** The re-limb claim's 32 byte slots against
the terminal link's outgoing lane 0 — the same 32 felts
`MinaStateBodyHashChain.the_body_hash_wire_block_is_the_body_hash` proves are `limbAt realBodyHash`.
⚠ COMPILED: it reduces the 1 544-byte binprot parse, a two-block SHA-256 and the 25-link fold. -/
theorem the_byte_seam_holds_on_the_real_block :
    (bodyHashByteSeam.pins.all fun p =>
      decide (realRelimbClaim.getD p.1 0
        = (Dregg2.Circuit.Emit.MinaStateBodyHashChain.bodyChainPIs
            Dregg2.Circuit.Emit.MinaStateBodyHashChain.BODY_HASH_LINK).getD p.2 0)) = true := by
  native_decide

/-- ⚑⚑ **AND THE LANE SEAM HOLDS AGAINST THE NONET THE LINK PUBLISHES.**
`MinaStateBodyHashChain.bodyHashNonet` is the `Faithful9` re-limbing the executor's REFUSAL 16d
computes by hand; the re-limb claim's nine lane slots ARE it, elementwise. ⚠ That agreement is the
statement that this descriptor computes the same function the deployed weld does — the differential
that keeps the new object from being a parallel encoding. -/
theorem the_lane_seam_holds_against_the_deployed_nonet :
    ((List.range NLANE).all fun l =>
      decide (realRelimbClaim.getD (PI_LANE l) 0
        = Dregg2.Circuit.Emit.MinaStateBodyHashChain.bodyHashNonet.getD l 0)) = true := by
  native_decide

/-- ⚑ **AND THE HONEST POLE IS NOT A STATEMENT ABOUT ZEROES.** A weld whose both sides were `0`
everywhere would pass the two theorems above and force nothing, so the control names how many of
the 41 welded slots carry a non-zero value. ⚠ It is not 41 — a `state_body_hash` has zero bytes and
that is normal; what matters is that the count is large and that it MOVES if the object degenerates.
-/
theorem the_real_welds_are_mostly_non_zero :
    ((List.range NBYTE).filter fun i =>
        decide (realRelimbClaim.getD (PI_BYTE i) 0 ≠ 0)).length ≥ 24
      ∧ ((List.range NLANE).filter fun l =>
        decide (realRelimbClaim.getD (PI_LANE l) 0 ≠ 0)).length = NLANE := by
  refine ⟨?_, ?_⟩ <;> native_decide

/-! ## §7 — ⚑⚑ THE PORT CENSUS: `bodyHashPort` GAINS A SEAM COVER.

`MinaSeams.bodyHashPort` is the link's `BODYHASH` block (PI 20..28). `CoveredPort` is a stronger
census object than the `WeldCover` it already carries: its `covers` obligation is DECIDED
(`seamCoversPort`), so a port whose slots the seam does not reach cannot be built, whereas a
`WeldCover` only names a Rust string Lean cannot check.

⚠ Coverage is not routing. No fold applies `bodyHashLaneSeam` yet, so what a NODE runs is still
REFUSAL 16d, and `MinaSeams.bodyHashWeld` stays until that changes. -/

/-- ⚑⚑ **THE BODY-HASH PORT, COVERED BY A SEAM.** The constructor does not elaborate unless
`bodyHashLaneSeam` reaches every one of the port's nine slots — the census as a refusal. -/
def bodyHashPortCovered : CoveredPort :=
  { descName := "dregg-mina-lightclient-link::v1"
  , port := Dregg2.Circuit.Emit.MinaSeams.bodyHashPort
  , seam := bodyHashLaneSeam }

/-- ⚑ **AND THE COVER IS REAL, NOT NOMINAL — it reaches every slot, and it would go red on a
tenth.** ⚠ "Resolution is not coverage": the census verdict below is `seamCoversPort`, which
demands each port slot be a PIN ENDPOINT of the seam, so a seam that merely named the descriptor
would fail it. The red pole is a port one slot wider than the seam's block. -/
theorem the_body_hash_port_is_seam_covered :
    seamCoversPort bodyHashLaneSeam "dregg-mina-lightclient-link::v1"
        Dregg2.Circuit.Emit.MinaSeams.bodyHashPort = true
      ∧ seamCoversPort bodyHashLaneSeam "dregg-mina-lightclient-link::v1"
        { Dregg2.Circuit.Emit.MinaSeams.bodyHashPort with width := 10 } = false
      ∧ seamCoversPort bodyHashLaneSeam "dregg-mina-lightclient-link::v1"
        Dregg2.Circuit.Emit.MinaSeams.bodyAccPort = false := by
  refine ⟨?_, ?_, ?_⟩ <;> decide

/-- ⚑⚑⚑ **THE LINK'S SEAM-UNCOVERABLE PORT COUNT IS ONE, AND IT IS NAMED.** Before this file both
link body ports were `WeldCover`-only; `bodyHashPort` is now covered by a REGISTERED seam and only
`bodyAccPort` remains an executor weld. ⚠ It is not covered here and it is not narrated as covered:
the eight `BODY_ACC` lanes weld against a fold ROOT's `transcript_acc`, and a fold root has no
descriptor — so `SeamEnd`'s descriptor key has nothing to name, which is a DIFFERENT blocker from
the arithmetic one this file removed and is not solved by it. -/
theorem the_link_body_ports_now_have_one_seam_and_one_weld :
    (Dregg2.Circuit.Emit.MinaSeams.linkPortSet.filter fun p =>
        !(relimbSeams.any fun s => seamCoversPort s "dregg-mina-lightclient-link::v1" p))
      = [Dregg2.Circuit.Emit.MinaSeams.bodyAccPort] := by
  decide

/-! ## §8 — ⚠ WHAT THIS DOES NOT BUY, said in the same breath.

1. ⚠ **NOT ROUTED.** No `apply_seam` call site issues these connects; `check_body_chain_binding`
   (REFUSAL 16) is what a node runs. The object exists, is emitted, and is gated by
   `circuit-prove/tests/seam_specs.rs`; the fold that consumes it does not exist yet. That is a
   weaker state than "deployed" and is recorded as such, as `MinaBodyPreimageSeams` §7.0 records the
   same gap for tie 1.
2. ⚠ **NOT AN IN-DESCRIPTOR CONSTRAINT.** `apply_seam` issues `cb.connect`s; the forcing lives in
   the recursion circuit, which proves on a box and inherits the undischarged FRI/STARK floor.
3. ⚠ **`BODY_ACC` IS STILL A `WeldCover`**, for a reason this file does not address (§7).
4. ⚠ **NOTHING SAYS THE 49 ELEMENTS ARE A `Protocol_state.Body`.** `PICKLES_OPENING_WITNESSED`,
   unchanged.
-/

#assert_axioms the_claim_shapes_are_the_deployed_ones
#assert_axioms the_lane_widths_are_the_links
#assert_axioms the_link_end_is_the_link_airs_own_pin
#assert_axioms both_relimb_seams_are_wf
#assert_axioms the_seams_are_total_and_need_no_zero_pins
#assert_axioms relimb_byte_slot_is_published
#assert_axioms relimb_lane_slot_is_published
#assert_axioms chain_out_lane0_is_register_four_last_row
#assert_axioms the_relimb_seams_weld_published_slots
#assert_axioms relimbClaimOf_get
#assert_axioms bodyHashByteSeamCertifies
#assert_axioms bodyHashLaneSeamCertifies
#assert_axioms the_chains_body_hash_is_the_links_body_hash
#assert_axioms oneSqueezing_renders
#assert_axioms oneSqueezing_says
#assert_axioms the_body_hash_port_is_seam_covered
#assert_axioms the_link_body_ports_now_have_one_seam_and_one_weld
#assert_axioms lane_seam_S2_needs_the_seam
#assert_axioms oneLink_says
#assert_axioms oneLink_bodyhash
#assert_axioms byte_seam_S2_needs_the_seam
#assert_axioms zeroRelimb_readings_are_zero
#assert_axioms zeroRelimb_says

-- ⚑ COMPILER-TRUSTED, and said out loud: the real-block rows reduce the 1 544-byte binprot parse,
-- a two-block SHA-256 and the twenty-five-link fold; the zero/one witnesses evaluate a 254-summand
-- bit fold.
#assert_compiled the_two_seams_weld_every_published_slot_exactly_once
#assert_compiled the_real_body_hash_is_below_two_254
#assert_compiled the_byte_seam_holds_on_the_real_block
#assert_compiled the_lane_seam_holds_against_the_deployed_nonet
#assert_compiled the_real_welds_are_mostly_non_zero

end Dregg2.Circuit.Emit.MinaBodyHashRelimbSeams
