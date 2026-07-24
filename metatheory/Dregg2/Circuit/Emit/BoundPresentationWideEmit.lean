/-
# Dregg2.Circuit.Emit.BoundPresentationWideEmit — the WIDE (8-felt federation-root) bound
presentation (felt-width E2 **#2a**)

**This is Lean-authored AIR.** This module authors the constraint algebra; Rust parses the emitted
IR2 bytes and supplies witnesses — it constructs no constraints.

## What this file IS

The WIDE additive replacement for the deployed 1-felt-root descriptor
`BoundPresentationEmit.boundPresentationDesc` (staged-additive-then-cutover; sits beside the
deployed file exactly as `MerkleMembership4aryWideEmit` sits beside the deployed membership
descriptor). The deployed descriptor is felt-width finding **#2**
(`docs/WOUND-felt-width-boundaries-2026-07-19.md`): `FEDERATION_ROOT` is carried as ONE felt
(~31-bit, 2^15.5-collidable) public input at summary col 0. This file widens the root PI echo
1 → 8: the summary's first field becomes the full 8-felt (~124-bit) federation-root digest, each
lane a PiBinding-CONSTRAINED public input.

## ⚠ ANTI-MASQUERADE — what this buys and what it does NOT

This descriptor merely **CARRIES** the federation root as constrained public inputs — a straight
PI echo. It does **not** FOLD the root anywhere. The honest claim is exactly:

> the WIDE bound-presentation **exposes the full 8-felt federation root** to the verifier / light
> client / recursion fold,

**NOT** "federation membership is now 124-bit." The membership proof that actually binds a
credential under that root is the separate blinded-membership descriptor, whose node fold chains
lane 0 — widening THAT fold (E2 **#2b**, the 8-lane fold) is the separate hard lane that makes
membership genuinely ~124-bit. Until 2b lands, a lane-0 collision inside the membership fold still
forges membership; what 2a removes is the BOUNDARY squeeze — the verifier no longer sees only a
31-bit shadow of the root it is trusting, and 2b has a full-width PI surface to land on. This file
is NOT the close of wound #2.

## The widened PI layout (federation root 1 → 8; every downstream base shifts +7)

| field              | deployed idx | wide idx  |
|--------------------|--------------|-----------|
| federation_root    | 0            | **0..7**  |
| action_binding     | 1..8         | **8..15** |
| timestamp          | 9            | **16**    |
| presentation_tag   | 10           | **17**    |
| revealed_facts     | 11..18       | **18..25**|
| verifier_nonce     | 19           | **26**    |
| piCount            | 20           | **27**    |

The single 1-felt federation-root pin becomes **8 pi_bindings** (root lanes 0..7). Everything else
is the deployed gate algebra verbatim at shifted indices: `summaryPins` is still the auto-generated
`(List.range SUMMARY_WIDTH).map …`, and the nonce pin / tag-binding Poseidon2 chip lookup reference
the named constants, so shifting the constants does the work. The `+7` ripple against the deployed
constants is byte-pinned in §4.

## Refinement disposition

The deployed refinement tier (`BoundPresentationRefine.boundPresentation_sat_refines`,
`BoundPresentationRung2`) is NOT parametric in the layout constants — its statements open the
concrete `boundPresentationDesc` and its proofs `decide` at the literal indices. Re-instantiation
therefore means RE-AUTHORING at the wide layout, done here in §5–§7: the wide functional spec
`BoundPresentationWide`, the whole-descriptor bridge `boundPresentationWide_sat_refines`
(SAT ⟹ SEM, the load-bearing soundness direction, under the same named `ChipTableSound` Poseidon2
carrier and the same canonicality envelope), the inhabited TRUE pole (`concrete_sat` /
`witness_spec`), the FALSE pole (`spec_false`), the tag-forge tooth (`concrete_fail_tag`), and the
WIDE-specific tooth `forge_root_lane_rejected` — a forge on root lane 7, a lane the deployed
descriptor does not even carry, is rejected. NAMED RESIDUAL: the remaining Rung2 forge catalog
(action/facts forges + honest-pole packaging) at the wide layout is a follow-up
`BoundPresentationWideRung2`; the genuinely hard residual for wound #2 is the 2b blinded-membership
8-lane fold, not anything in this family.

## DEFERRED coordinated deploy (integrator, one epoch)

The Rust consumer repoint — the `circuit/src/bound_presentation_witness.rs` witness signature
(8 root lanes in, 27 PIs out), the `sdk/src/verify.rs` / `bridge/src/present.rs` compare-loops
(compare all 8 root lanes, never lane 0 alone), the descriptor-JSON golden regen into
`circuit/descriptors/`, and the `vk_hash` registry rotation — is the coordinated cutover; nothing
here changes the deployed descriptor, `Dregg2.lean`, or `EmitByName.lean`.

## Axiom hygiene

Definitional descriptor + byte-pinned `#guard` on the wire string + non-vacuous shape/semantic
lemmas; both poles inhabited (accept-honest AND reject-forge). `#assert_axioms` ⊆
{propext, Classical.choice, Quot.sound} on every keystone; the sole cryptographic carrier is the
NAMED chip soundness `ChipTableSound hash (t.tf .poseidon2)`, never a Lean axiom. NEW file; imports
read-only.
-/
import Dregg2.Circuit.Emit.BoundPresentationEmit

namespace Dregg2.Circuit.Emit.BoundPresentationWideEmit

open Dregg2.Circuit (Assignment)
open Dregg2.Exec.CircuitEmit (EmittedExpr)
open Dregg2.Circuit.Emit.EffectVmEmit (VmConstraint VmRow VmRowEnv)
open Dregg2.Circuit.DescriptorIR2
  (EffectVmDescriptor2 VmConstraint2 Satisfied2 VmTrace envAt Lookup TableId
   ChipTableSound chip_lookup_sound chipLookupTuple chipRow CHIP_RATE CHIP_OUT_LANES
   emitVmJson2 memLog mapLog memCheck_nil)

set_option autoImplicit false

/-! ## §1 — the WIDE trace column layout (one logical summary row).

The 26 summary columns are the deployed 19 with the federation root widened to a full 8-felt
digest group at the front; past them sit the same four tag-binding witness columns and the seven
Poseidon2 chip output lanes, each shifted +7. -/

/-- Summary cols 0..7: the 8-felt `federation_root` digest group (WIDE — was 1 felt, col 0). -/
def FEDERATION_ROOT_BASE : Nat := 0
/-- The federation root is a FULL 8-lane digest here (the whole point of #2a). -/
def FEDERATION_ROOT_WIDTH : Nat := 8
/-- Summary cols 8..15: `request_predicate` (`action_binding`, 8 felts). -/
def REQUEST_PREDICATE_BASE : Nat := 8
/-- Summary col 16: `timestamp`. -/
def TIMESTAMP : Nat := 16
/-- Summary col 17: `presentation_tag` (narrow; CONSTRAINED in-circuit to its Poseidon2 image). -/
def PRESENTATION_TAG : Nat := 17
/-- Summary cols 18..25: `revealed_facts_commitment` (8 felts). -/
def REVEALED_FACTS_BASE : Nat := 18

/-- The WIDE summary width (`8 + 8 + 1 + 1 + 8`). -/
def SUMMARY_WIDTH : Nat := 26

/-- Tag-binding col 26: `final_root` — the end-of-chain state root; a HIDDEN witness (not a PI). -/
def FINAL_ROOT : Nat := 26
/-- Tag-binding col 27: `presentation_randomness` — fresh per presentation; HIDDEN (unlinkability). -/
def RANDOMNESS : Nat := 27
/-- Tag-binding col 28: `verifier_nonce` — the verifier's challenge; a PUBLIC input (`PI_NONCE`). -/
def VERIFIER_NONCE : Nat := 28

/-- The seven exposed Poseidon2 chip output lanes 1..7 (out0 is `PRESENTATION_TAG`). -/
def TAG_LANES : List Nat := [29, 30, 31, 32, 33, 34, 35]

/-- Total base-trace width: 26 summary + `final_root` + `randomness` + `verifier_nonce` + 7 lanes. -/
def BOUND_PRES_WIDTH : Nat := 36

/-- Public-input slot for the `verifier_nonce` (after the 26 summary PIs). -/
def PI_NONCE : Nat := 26

/-- Number of public inputs: the 26 summary slots + the verifier-nonce challenge. -/
def PI_COUNT : Nat := 27

/-- **The presentation-tag domain-separation constant** — identical to the deployed
`BoundPresentationEmit.PRESENTATION_TAG_DSK` (`BLAKE3("dregg-presentation-tag-v1")`'s first 4 bytes
little-endian mod the BabyBear prime; `binding.rs:311`). The widening does not touch the tag
preimage. -/
def PRESENTATION_TAG_DSK : ℤ := 1066441253

/-! ## §2 — the constraint list (26 summary copies · the nonce PI · the tag-binding chip lookup). -/

/-- The 26 summary copy constraints `row[i] == pi[i]` — the 8 `federation_root` lanes, the 8
`action_binding` felts, `timestamp`, the tag, and the 8 `revealed_facts` felts are ALL
PiBinding-CONSTRAINED verified public inputs. The first 8 ARE the widened root pins (root0..7). -/
def summaryPins : List VmConstraint2 :=
  (List.range SUMMARY_WIDTH).map (fun i => .base (.piBinding VmRow.first i i))

/-- The `verifier_nonce` public-input pin: `loc[VERIFIER_NONCE] == pi[PI_NONCE]` (first row). -/
def noncePin : VmConstraint2 := .base (.piBinding VmRow.first VERIFIER_NONCE PI_NONCE)

/-- **The tag-binding chip lookup** — the deployed arity-4 `TID_P2` Poseidon2 lookup verbatim at
the shifted columns: absorbs `[final_root, presentation_randomness, verifier_nonce, DSK]`, binds
out0 to `PRESENTATION_TAG`. Fires on EVERY row (a lookup is never gated). -/
def tagLookup : VmConstraint2 :=
  .lookup ⟨TableId.poseidon2,
    chipLookupTuple [.var FINAL_ROOT, .var RANDOMNESS, .var VERIFIER_NONCE, .const PRESENTATION_TAG_DSK]
      PRESENTATION_TAG TAG_LANES⟩

/-- **`boundPresentationWideDesc`** — the bound presentation with the federation root exposed at
FULL 8-felt width. Constraints: the 26 summary PiBindings (8 of them the root lanes), the
verifier-nonce PI pin, and the tag-binding chip lookup. The chip table (`TID_P2`) is IMPLICITLY
present (Presence-detected from the lookup), so `tables` is empty exactly as the deployed
descriptor leaves it. -/
def boundPresentationWideDesc : EffectVmDescriptor2 :=
  { name        := "dregg-bound-presentation-wide::v1"
  , traceWidth  := BOUND_PRES_WIDTH
  , piCount     := PI_COUNT
  , tables      := []
  , constraints := summaryPins ++ [noncePin, tagLookup]
  , hashSites   := []
  , ranges      := [] }

/-! ## §3 — the byte-pinned wire golden (the decoder ingests THIS string). -/

#guard emitVmJson2 boundPresentationWideDesc ==
  "{\"name\":\"dregg-bound-presentation-wide::v1\",\"ir\":2,\"trace_width\":36,\"public_input_count\":27,\"tables\":[],\"constraints\":[{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":0,\"pi_index\":0},{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":1,\"pi_index\":1},{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":2,\"pi_index\":2},{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":3,\"pi_index\":3},{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":4,\"pi_index\":4},{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":5,\"pi_index\":5},{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":6,\"pi_index\":6},{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":7,\"pi_index\":7},{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":8,\"pi_index\":8},{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":9,\"pi_index\":9},{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":10,\"pi_index\":10},{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":11,\"pi_index\":11},{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":12,\"pi_index\":12},{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":13,\"pi_index\":13},{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":14,\"pi_index\":14},{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":15,\"pi_index\":15},{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":16,\"pi_index\":16},{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":17,\"pi_index\":17},{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":18,\"pi_index\":18},{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":19,\"pi_index\":19},{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":20,\"pi_index\":20},{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":21,\"pi_index\":21},{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":22,\"pi_index\":22},{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":23,\"pi_index\":23},{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":24,\"pi_index\":24},{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":25,\"pi_index\":25},{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":28,\"pi_index\":26},{\"t\":\"lookup\",\"table\":1,\"tuple\":[{\"t\":\"const\",\"v\":4},{\"t\":\"var\",\"v\":26},{\"t\":\"var\",\"v\":27},{\"t\":\"var\",\"v\":28},{\"t\":\"const\",\"v\":1066441253},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"var\",\"v\":17},{\"t\":\"var\",\"v\":29},{\"t\":\"var\",\"v\":30},{\"t\":\"var\",\"v\":31},{\"t\":\"var\",\"v\":32},{\"t\":\"var\",\"v\":33},{\"t\":\"var\",\"v\":34},{\"t\":\"var\",\"v\":35}]}],\"hash_sites\":[],\"ranges\":[]}"

/-! ## §4 — shape pins (genuinely-proven, non-vacuous) + the +7 ripple against the deployed file. -/

/-- The one-glance descriptor shape, definitionally. -/
theorem descriptor_shape :
    (boundPresentationWideDesc.name, boundPresentationWideDesc.traceWidth,
     boundPresentationWideDesc.piCount, boundPresentationWideDesc.tables,
     boundPresentationWideDesc.constraints.length)
      = ("dregg-bound-presentation-wide::v1", BOUND_PRES_WIDTH, PI_COUNT, [],
         SUMMARY_WIDTH + 2) := rfl

/-- The tag-binding chip tuple has the canonical chip width `arity + CHIP_RATE + CHIP_OUT_LANES`. -/
theorem tagLookup_tuple_width :
    (chipLookupTuple [.var FINAL_ROOT, .var RANDOMNESS, .var VERIFIER_NONCE,
        .const PRESENTATION_TAG_DSK] PRESENTATION_TAG TAG_LANES).length
      = 1 + CHIP_RATE + CHIP_OUT_LANES := by
  simp [chipLookupTuple, Dregg2.Circuit.DescriptorIR2.padToE, CHIP_RATE, CHIP_OUT_LANES, TAG_LANES]

-- Shape pins.
#guard boundPresentationWideDesc.traceWidth == BOUND_PRES_WIDTH
#guard boundPresentationWideDesc.piCount == PI_COUNT
#guard boundPresentationWideDesc.constraints.length == SUMMARY_WIDTH + 2
#guard boundPresentationWideDesc.tables.length == 0
#guard decide (PRESENTATION_TAG_DSK ≠ 0)

-- The exact +7 index ripple against the DEPLOYED constants (byte-pinned, not prose).
#guard decide (FEDERATION_ROOT_BASE = BoundPresentationEmit.FEDERATION_ROOT)
#guard decide (REQUEST_PREDICATE_BASE = BoundPresentationEmit.REQUEST_PREDICATE_BASE + 7)
#guard decide (TIMESTAMP = BoundPresentationEmit.TIMESTAMP + 7)
#guard decide (PRESENTATION_TAG = BoundPresentationEmit.PRESENTATION_TAG + 7)
#guard decide (REVEALED_FACTS_BASE = BoundPresentationEmit.REVEALED_FACTS_BASE + 7)
#guard decide (SUMMARY_WIDTH = BoundPresentationEmit.SUMMARY_WIDTH + 7)
#guard decide (FINAL_ROOT = BoundPresentationEmit.FINAL_ROOT + 7)
#guard decide (RANDOMNESS = BoundPresentationEmit.RANDOMNESS + 7)
#guard decide (VERIFIER_NONCE = BoundPresentationEmit.VERIFIER_NONCE + 7)
-- E7: the DEPLOYED narrow twin was narrowed onto `TID_P2_NARROW`, so its 7 chip lane columns are
-- gone. This WIDE twin is a SEPARATE staged-additive descriptor (distinct name, distinct VK) and
-- still commits its own lane block, so the two widths now differ by the 7 extra federation-root
-- lanes PLUS the 7 chip lanes only this twin still carries.
#guard decide (TAG_LANES.length = CHIP_OUT_LANES - 1)
#guard decide (BOUND_PRES_WIDTH
  = BoundPresentationEmit.BOUND_PRES_WIDTH + 7 + (CHIP_OUT_LANES - 1))
#guard decide (PI_NONCE = BoundPresentationEmit.PI_NONCE + 7)
#guard decide (PI_COUNT = BoundPresentationEmit.PI_COUNT + 7)
#guard decide (PRESENTATION_TAG_DSK = BoundPresentationEmit.PRESENTATION_TAG_DSK)
-- The widening is REAL: 7 more summary lanes, all federation-root.
#guard decide (SUMMARY_WIDTH - BoundPresentationEmit.SUMMARY_WIDTH = FEDERATION_ROOT_WIDTH - 1)

/-! ## §5 — the WIDE functional spec (trace-independent).

The deployed refinement tier is stated over the concrete deployed descriptor (its `decide`s bake in
the literal indices), so the wide tier is RE-AUTHORED here rather than instantiated. -/

/-- **`BoundPresentationWide hash loc pub`** — THE FUNCTIONAL SPEC the wide descriptor certifies:
every one of the 26 summary felts (the 8 federation-root lanes among them) EQUALS its verified
public input; the `verifier_nonce` column equals its PI; and the presentation-tag PI is the genuine
Poseidon2 image of `[final_root, randomness, verifier_nonce, DSK]`. -/
def BoundPresentationWide (hash : List ℤ → ℤ) (loc pub : Assignment) : Prop :=
  (∀ i, i < SUMMARY_WIDTH → loc i = pub i)
  ∧ loc VERIFIER_NONCE = pub PI_NONCE
  ∧ pub PRESENTATION_TAG
      = hash [loc FINAL_ROOT, loc RANDOMNESS, loc VERIFIER_NONCE, PRESENTATION_TAG_DSK]

/-- **The widened boundary, stated:** under the spec, EVERY lane of the 8-felt federation root is
exposed as (equals) its committed public input — the full ~124-bit digest crosses the PI boundary,
not a 31-bit lane-0 shadow. -/
theorem wide_root_exposed {hash : List ℤ → ℤ} {loc pub : Assignment}
    (h : BoundPresentationWide hash loc pub) (k : Nat) (hk : k < FEDERATION_ROOT_WIDTH) :
    loc (FEDERATION_ROOT_BASE + k) = pub (FEDERATION_ROOT_BASE + k) := by
  refine h.1 _ ?_
  show 0 + k < 26
  have : k < 8 := hk
  omega

/-! ## §6 — the whole-descriptor bridge (SAT ⟹ SEM), re-authored at the wide layout. -/

/-- Membership tactic for the two non-summary constraints. -/
local macro "bpw_mem" : tactic =>
  `(tactic| (show _ ∈ boundPresentationWideDesc.constraints;
             simp [boundPresentationWideDesc, noncePin, tagLookup]))

/-- Every summary PiBinding `col i → pi i` (for `i < 26`) is literally in the descriptor. -/
theorem summaryPin_mem (i : Nat) (hi : i < SUMMARY_WIDTH) :
    VmConstraint2.base (.piBinding VmRow.first i i) ∈ boundPresentationWideDesc.constraints := by
  show _ ∈ summaryPins ++ [noncePin, tagLookup]
  apply List.mem_append_left
  simp only [summaryPins, List.mem_map, List.mem_range]
  exact ⟨i, hi, rfl⟩

/-- **The 8 root-lane pins are IN the descriptor** — the constraint the 1-felt deployed descriptor
cannot even state for lanes 1..7. -/
theorem root_lanes_pinned (k : Nat) (hk : k < FEDERATION_ROOT_WIDTH) :
    VmConstraint2.base (.piBinding VmRow.first (FEDERATION_ROOT_BASE + k) (FEDERATION_ROOT_BASE + k))
      ∈ boundPresentationWideDesc.constraints := by
  refine summaryPin_mem _ ?_
  show 0 + k < 26
  have : k < 8 := hk
  omega

/-- A declared first-row PI binding pins `loc[col] ≡ pub[k] [ZMOD p]` on row 0 — the field-faithful
pin; the ℤ reading lives in the bridge under the `BoundPresWideCanon` envelope. -/
theorem firstPiG {hash : List ℤ → ℤ} {t : VmTrace} {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat}
    {maddrs : List ℤ} (hsat : Satisfied2 hash boundPresentationWideDesc minit mfin maddrs t)
    (hlen : 0 < t.rows.length) (col k : Nat)
    (hmem : VmConstraint2.base (.piBinding VmRow.first col k)
      ∈ boundPresentationWideDesc.constraints) :
    (envAt t 0).loc col ≡ t.pub k [ZMOD 2013265921] := by
  have h := hsat.rowConstraints 0 hlen _ hmem
  simp only [VmConstraint2.holdsAt, VmConstraint.holdsVm] at h
  exact h (by decide)

/-- Two canonical representatives congruent mod `p` are EQUAL. -/
theorem eq_of_modEq_of_canon {a b : ℤ} (h : a ≡ b [ZMOD 2013265921])
    (ha : 0 ≤ a ∧ a < 2013265921) (hb : 0 ≤ b ∧ b < 2013265921) : a = b := by
  obtain ⟨k, hk⟩ := h.dvd
  omega

/-- **The wide canonicality envelope.** Every row-0 summary column and its bound public input, and
the nonce column + nonce PI, are canonical representatives in `[0, p)` — the deployed range-check
invariant, threaded through the whole-descriptor bridge. -/
def BoundPresWideCanon (t : VmTrace) : Prop :=
  (∀ i, i < SUMMARY_WIDTH →
      (0 ≤ (envAt t 0).loc i ∧ (envAt t 0).loc i < 2013265921)
      ∧ (0 ≤ t.pub i ∧ t.pub i < 2013265921))
  ∧ (0 ≤ (envAt t 0).loc VERIFIER_NONCE ∧ (envAt t 0).loc VERIFIER_NONCE < 2013265921)
  ∧ (0 ≤ t.pub PI_NONCE ∧ t.pub PI_NONCE < 2013265921)

/-- **The tag-binding tooth extracted** — against the NAMED sound chip table, the tag lookup forces
the tag column to be the genuine Poseidon2 image on row 0 (`chip_lookup_sound`). -/
theorem tagSound {hash : List ℤ → ℤ} {t : VmTrace} {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat}
    {maddrs : List ℤ} (hsat : Satisfied2 hash boundPresentationWideDesc minit mfin maddrs t)
    (hChip : ChipTableSound hash (t.tf .poseidon2)) (hlen : 0 < t.rows.length) :
    (envAt t 0).loc PRESENTATION_TAG
      = hash [(envAt t 0).loc FINAL_ROOT, (envAt t 0).loc RANDOMNESS,
              (envAt t 0).loc VERIFIER_NONCE, PRESENTATION_TAG_DSK] := by
  have h := hsat.rowConstraints 0 hlen _ (by bpw_mem :
    tagLookup ∈ boundPresentationWideDesc.constraints)
  simp only [tagLookup, VmConstraint2.holdsAt, Lookup.holdsAt] at h
  have hs := chip_lookup_sound hash (t.tf .poseidon2) hChip (envAt t 0).loc
    [.var FINAL_ROOT, .var RANDOMNESS, .var VERIFIER_NONCE, .const PRESENTATION_TAG_DSK]
    PRESENTATION_TAG TAG_LANES (by show (4 : Nat) ≤ CHIP_RATE; decide) h
  simpa [EmittedExpr.eval] using hs

/-- **`boundPresentationWide_sat_refines` — THE WHOLE-DESCRIPTOR BRIDGE (SAT_IMPLIES_SEM).**
A `Satisfied2` of `boundPresentationWideDesc`, against the NAMED Poseidon2 chip carrier, binds
`BoundPresentationWide` between the row-0 witness columns and the committed public inputs — for
ANY non-empty trace. Composes the 26 summary PiBindings (the 8 root lanes among them), the nonce
pin, and the tag-binding chip lookup. -/
theorem boundPresentationWide_sat_refines {hash : List ℤ → ℤ} {t : VmTrace} {minit : ℤ → ℤ}
    {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ}
    (hlen : 0 < t.rows.length)
    (hsat : Satisfied2 hash boundPresentationWideDesc minit mfin maddrs t)
    (hChip : ChipTableSound hash (t.tf .poseidon2))
    (hcanon : BoundPresWideCanon t) :
    BoundPresentationWide hash (envAt t 0).loc t.pub := by
  refine ⟨?_, ?_, ?_⟩
  · intro i hi
    exact eq_of_modEq_of_canon (firstPiG hsat hlen i i (summaryPin_mem i hi))
      (hcanon.1 i hi).1 (hcanon.1 i hi).2
  · exact eq_of_modEq_of_canon (firstPiG hsat hlen VERIFIER_NONCE PI_NONCE (by bpw_mem))
      hcanon.2.1 hcanon.2.2
  · have htag := tagSound hsat hChip hlen
    have h17 : (envAt t 0).loc PRESENTATION_TAG = t.pub PRESENTATION_TAG :=
      eq_of_modEq_of_canon
        (firstPiG hsat hlen PRESENTATION_TAG PRESENTATION_TAG
          (summaryPin_mem PRESENTATION_TAG (by decide)))
        (hcanon.1 PRESENTATION_TAG (by decide)).1 (hcanon.1 PRESENTATION_TAG (by decide)).2
    rw [← h17]; exact htag

/-! ## §7 — non-vacuity + the teeth (both poles, at the WIDE layout). -/

/-- A concrete little-endian digit hash — `[a,b,c,d] ↦ ((a·100+b)·100+c)·100+d`. -/
private def cHash : List ℤ → ℤ := fun xs => xs.foldl (fun acc x => acc * 100 + x) 0

/-- The genuine tag for the honest preimage `[1, 2, 3, DSK]`: `1020300 + 1066441253 = 1067461553`. -/
private def cGenuineTag : ℤ := 1067461553

/-- The honest height-1 row: summary cols `0..25` carry their index (tag col 17 = the genuine tag),
hidden `final_root = 1`, `randomness = 2`, `verifier_nonce = 3`, lanes `0`. Root lanes 0..7 carry
`0..7` — eight DISTINCT lane values, so the widened pins are exercised at full width. -/
private def hRow : Assignment := fun c =>
  if c = PRESENTATION_TAG then cGenuineTag
  else if c = FINAL_ROOT then 1
  else if c = RANDOMNESS then 2
  else if c = VERIFIER_NONCE then 3
  else if c < SUMMARY_WIDTH then (c : ℤ)
  else 0

/-- The honest public inputs: summary PIs `0..25` mirror the row, the nonce PI (26) is `3`. -/
private def hPub : Assignment := fun k =>
  if k = PRESENTATION_TAG then cGenuineTag
  else if k = PI_NONCE then 3
  else if k < SUMMARY_WIDTH then (k : ℤ)
  else 0

/-- The chip table: the one genuine `[final_root, randomness, nonce, DSK] → tag` `chipRow`. -/
private def hTbl : List (List ℤ) :=
  [chipRow cHash [1, 2, 3, PRESENTATION_TAG_DSK] (List.replicate 7 0)]

/-- The concrete HEIGHT-1 honest trace (`rows = [hRow]`). -/
private def hTrace : VmTrace :=
  { rows := [hRow], pub := hPub
    tf := fun tid => match tid with | .poseidon2 => hTbl | _ => [] }

/-- The honest chip table is genuinely SOUND (its one row is a real `chipRow cHash`). -/
theorem concrete_chipSound : ChipTableSound cHash (hTrace.tf .poseidon2) := by
  intro r hr
  simp only [hTrace, hTbl, List.mem_cons, List.not_mem_nil, or_false] at hr
  exact ⟨[1, 2, 3, PRESENTATION_TAG_DSK], List.replicate 7 0, by decide, by decide, hr⟩

/-- **The `Satisfied2` HYPOTHESIS IS INHABITED** — the honest trace satisfies the WHOLE wide
descriptor: all 26 summary pins (the 8 root lanes at 8 distinct values), the nonce pin, and the
tag chip lookup. The empty memory / map legs close. -/
theorem concrete_sat :
    Satisfied2 cHash boundPresentationWideDesc (fun _ => 0) (fun _ => (0, 0)) [] hTrace := by
  have hmemlog : memLog boundPresentationWideDesc hTrace = [] := rfl
  have hmaplog : mapLog boundPresentationWideDesc hTrace = [] := rfl
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i hi c hc
    rw [show hTrace.rows.length = 1 from rfl] at hi
    interval_cases i
    rw [show boundPresentationWideDesc.constraints
          = summaryPins ++ [noncePin, tagLookup] from rfl] at hc
    rcases List.mem_append.mp hc with hsum | hextra
    · simp only [summaryPins, List.mem_map, List.mem_range] at hsum
      obtain ⟨k, hk, rfl⟩ := hsum
      simp only [VmConstraint2.holdsAt, VmConstraint.holdsVm]
      intro _
      have hk26 : k < 26 := hk
      simp only [envAt, hTrace, List.getD_cons_zero]
      interval_cases k <;> decide
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hextra
      rcases hextra with rfl | rfl
      · simp only [VmConstraint2.holdsAt, VmConstraint.holdsVm, noncePin]
        intro _; decide
      · simp only [VmConstraint2.holdsAt, Lookup.holdsAt, tagLookup]
        decide
  · intro i _; trivial
  · intro i _ r hr; simp [boundPresentationWideDesc] at hr
  · exact List.nodup_nil
  · intro op hop; rw [hmemlog] at hop; simp at hop
  · rw [hmemlog]; trivial
  · rw [hmemlog]; exact memCheck_nil _ _
  · rw [hmemlog]; rfl
  · rw [hmaplog]; rfl

/-- The honest witness inhabits the canonicality envelope (all 26 lanes + the nonce pair). -/
theorem hTrace_canon : BoundPresWideCanon hTrace := by
  refine ⟨?_, ⟨by decide, by decide⟩, ⟨by decide, by decide⟩⟩
  intro i hi
  have hi26 : i < 26 := hi
  interval_cases i <;> exact ⟨⟨by decide, by decide⟩, ⟨by decide, by decide⟩⟩

/-- **The bridge fires end-to-end on the concrete inhabited witness** (SAT ⟹ SEM, non-vacuously). -/
theorem witness_spec : BoundPresentationWide cHash (envAt hTrace 0).loc hTrace.pub :=
  boundPresentationWide_sat_refines (by decide) concrete_sat concrete_chipSound hTrace_canon

/-- **Witness FALSE — the spec CONSTRAINS.** A wrong published tag is NOT `BoundPresentationWide`. -/
theorem spec_false :
    ¬ BoundPresentationWide cHash hRow (fun k => if k = PRESENTATION_TAG then 999 else hPub k) := by
  rintro ⟨_, _, htag⟩
  revert htag
  decide

/-- A trace with a FORGED tag (`999`, PI likewise, so the copy pin holds): the genuine chip row
still carries `cGenuineTag` — the lookup cannot land. -/
private def hRowBadTag : Assignment := fun c => if c = PRESENTATION_TAG then 999 else hRow c
private def hPubBadTag : Assignment := fun k => if k = PRESENTATION_TAG then 999 else hPub k
private def hTraceBadTag : VmTrace :=
  { rows := [hRowBadTag], pub := hPubBadTag
    tf := fun tid => match tid with | .poseidon2 => hTbl | _ => [] }

/-- **The wide descriptor genuinely REJECTS a forged tag (the tag chip lookup BITES).** -/
theorem concrete_fail_tag :
    ¬ Satisfied2 cHash boundPresentationWideDesc (fun _ => 0) (fun _ => (0, 0)) [] hTraceBadTag := by
  intro h
  have hmem : tagLookup ∈ boundPresentationWideDesc.constraints := by bpw_mem
  have hc := h.rowConstraints 0 (by decide) _ hmem
  simp only [tagLookup, VmConstraint2.holdsAt, Lookup.holdsAt] at hc
  revert hc
  decide

/-- **THE WIDE-SPECIFIC TOOTH** — a forge on federation-root lane 7 (a lane the deployed 1-felt
descriptor does not even CARRY): witness col 7 forged to `424242` while the committed PI 7 stays
`7`. Lane 0 (and every other lane) is honest — precisely the forge class a 1-felt root echo is
blind to at the boundary. -/
private def forgeRootRow : Assignment := fun c =>
  if c = FEDERATION_ROOT_BASE + 7 then 424242 else hRow c
private def forgeRootTrace : VmTrace := { hTrace with rows := [forgeRootRow] }

/-- The forged lane genuinely disagrees with its committed public input (`424242 ≠ 7`). -/
theorem forge_root_mismatch :
    (envAt forgeRootTrace 0).loc (FEDERATION_ROOT_BASE + 7)
      ≠ forgeRootTrace.pub (FEDERATION_ROOT_BASE + 7) := by
  simp only [envAt, forgeRootTrace, hTrace, forgeRootRow, List.getD_cons_zero]
  decide

/-- **The widened root pins BITE.** No `Satisfied2` exists for the lane-7 root forge: the lane-7
PiBinding forces `loc[7] = pub[7]`, i.e. `424242 = 7`. Under the deployed 1-felt descriptor this
lane crosses no boundary at all — the pin exists ONLY because the root was widened. -/
theorem forge_root_lane_rejected :
    ¬ Satisfied2 cHash boundPresentationWideDesc (fun _ => 0) (fun _ => (0, 0)) [] forgeRootTrace := by
  intro h
  have hpin := firstPiG h (by decide) (FEDERATION_ROOT_BASE + 7) (FEDERATION_ROOT_BASE + 7)
    (root_lanes_pinned 7 (by decide))
  exact forge_root_mismatch hpin

/-! ## §8 — value pins + axiom hygiene. -/

#guard decide (hTrace.rows.length = 1)
#guard decide (cHash [1, 2, 3, PRESENTATION_TAG_DSK] = cGenuineTag)
#guard decide (cHash [1, 2, 3, PRESENTATION_TAG_DSK] ≠ 999)

#assert_axioms descriptor_shape
#assert_axioms tagLookup_tuple_width
#assert_axioms wide_root_exposed
#assert_axioms summaryPin_mem
#assert_axioms root_lanes_pinned
#assert_axioms firstPiG
#assert_axioms tagSound
#assert_axioms boundPresentationWide_sat_refines
#assert_axioms concrete_chipSound
#assert_axioms concrete_sat
#assert_axioms witness_spec
#assert_axioms spec_false
#assert_axioms concrete_fail_tag
#assert_axioms forge_root_lane_rejected

end Dregg2.Circuit.Emit.BoundPresentationWideEmit
