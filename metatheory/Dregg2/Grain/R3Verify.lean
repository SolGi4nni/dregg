/-
# `Dregg2.Grain.R3Verify` — GRAIN R3: the whole execution history is UNFOOLABLE, from a constant-size
aggregate, with NO host trust. The EXECUTABLE verifier, EXPORTED to run as native code.

**What R3 is.** A grain (`grain-verify`) attests a running acknowledged head/root at R1. R3 is the
guarantee that the WHOLE execution history BEHIND that head is unfoolable: every turn executed correctly
per the verified executor (execution INTEGRITY) and the chain is correctly ordered with nothing dropped,
inserted or reordered (COMPLETENESS — no host fabrication) — learned from ONE succinct aggregate, the
host re-witnessing nothing. **Honest scope (not an overclaim):** this REDUCES `grain-verify`'s
`WHOLE_HISTORY_GAP` to the STARK/apex soundness — it does NOT close it unconditionally. The load-bearing
`EngineSound` hypothesis is an ASSUMED boundary: `recursive_sound`/`binding_sound` are the FRI legs
proved *outside* Lean, and `leaf_sound` is only *dischargeable* by the single-turn apex
(`EngineSoundOfApex`) modulo its three still-open reconciliation mismatches. GIVEN that soundness, a
lying host cannot serve a fabricated or truncated history under an honest-looking head — but R3 here is a
genuine *reduction plus head-binding*, not an unconditional proof of unfoolability.

## THE FELT-WIDTH + SELF-ANCHORING REPAIR (wound #22) — what changed and why

`docs/WOUND-felt-width-boundaries-2026-07-19.md` #22 catalogued the R3 accept decision as a HIGH design
wound with TWO independently fatal conjuncts, and this module is its close. The pre-fix decision was

  `r3VerifyCoreNarrow aggregateVerified aggregateHead anchoredHead` over **ℤ**,

which the Rust seam fed with `proof.final_root[0].as_u32()` — **lane 0 of an 8-felt anchor**, ~31 bits —
while `verify_whole_chain_proof_bytes` was called with `proof.root_vk_fingerprint()`, the fingerprint
**the artifact itself supplied**. Both halves are repaired here, and NEITHER repair alone is enough:

  * **the WIDTH.** `r3VerifyCore` now decides on the FULL `Digest8` (`Fin 8 → Felt`, faithful to Rust
    `[BabyBear; SEG_ANCHOR_WIDTH]` = `WholeChainProof.final_root`), not a lane-0 projection. The
    falsifier `narrowHead_conflates` exhibits two GENUINELY DISTINCT wide anchors that the lane-0 form
    ACCEPTS as equal (`forgedHead` agrees with `anchorHead` on lane 0, differs at lane 1 — exactly the
    product of a ~2^31 offline grind); `r3_wide_head_mismatch_rejected` /
    `wideHead_refuses_the_forgery` are the fix-soundness.
  * **the SELF-ANCHORING.** `r3VerifyCore` now takes the presented VK fingerprint AND the caller's
    expected anchor as SEPARATE arguments and decides their equality. `selfAnchoredVk_vacuous` proves
    the pre-fix shape (`expectedVk := presentedVk`) is INDEPENDENT of which circuit the presented root
    belongs to — a conjunct that establishes nothing; `r3_vk_mismatch_rejected` is the fix-soundness.
    This is not our invention of a stricter rule: `WholeChainProof::root_vk_fingerprint`'s own docstring
    states "A VERIFIER must NEVER take the anchor from the artifact it is verifying", and
    `verify_whole_chain_proof_bytes`'s states "`expected_vk` is the caller's OWN configured anchor — it
    is NEVER read from the envelope". The pre-fix R3 seam violated a documented API contract.
  * **THE ANTI-LAUNDER.** `neither_half_alone_suffices` proves BOTH single-half repairs still broken:
    widening the head while keeping the self-anchored VK (`headWidenedOnly_admits_foreign_circuit`)
    still accepts a foreign circuit's root, and pinning the VK while keeping the lane-0 head
    (`vkPinnedOnly_still_conflates`) still accepts the ~31-bit grind. This is the
    `Cell.InterfaceIdWidth.finalSqueezeOnly_still_conflates` failure shape, stated for BOTH conjuncts.

**Where the expected VK comes from.** NOT the proof. `r3VerifyCore` takes it as a parameter and
`grain_verify::r3_verify` takes it from its CALLER — the honest-setup anchor a party extracts ONCE from a
locally produced fold (`grain_verify::r3::r3_setup_anchor`) and holds out of band, exactly as the
upstream light-client contract prescribes. A governance constant is NOT usable here: the fingerprint is a
function of the root circuit SHAPE, which varies with `num_turns` and the leaf trace heights (per
`root_vk_fingerprint`'s docstring), so one pinned scalar cannot cover the fold shapes R3 sees — unlike
`DREGG_APEX_RECURSION_VK`, which pins the ONE fixed apex-shrink shape. Pushing the obligation to the
caller is the correct fix at this layer; self-anchoring was not a fix at all.

## The decision is the Lean-proven object

`r3VerifyCore` is a plain executable `def`, `@[export]`ed as `r3VerifyFFI` for the Rust `grain-verify` to
call. Its SOUNDNESS is not re-derived: `r3_unfoolable` COMPOSES the already-proved whole-history
aggregation headline `Circuit.RecursiveAggregation.light_client_verifies_whole_history` (a verified
aggregate ⟹ the whole history is `AggregateAttests`) with the widened head binding.

**The boundary is INHERITED, not introduced (named, not laundered).** `r3VerifyCore` takes the STARK
verifier's verified-status as an INPUT Bool: it is `verify agg.root`, the output of the heavy Rust
`verify_whole_chain_proof_bytes`, whose in-circuit soundness is the named, realizable
`RecursiveAggregation.EngineSound` boundary (a `structure` field, not an axiom). R3 carries `EngineSound`
through UNCHANGED; it adds NO new axiom and NO `def …Hard`. The width and VK equalities are plain
decidable comparisons — no crypto, fully proved. **No new crypto floor is introduced by this repair:**
the widened head equality is exact `Digest8` equality (no hash), and the VK equality is exact
`RecursionVk` byte equality; the ~124-bit strength of the 8-felt anchor is the ALREADY-CARRIED Poseidon2
state-commit floor, not a new hypothesis.

**RESIDUAL, precisely.** The `RecursiveAggregation` model's `Aggregate.finalRoot` and `foldedFinalRoot`
remain `ℤ`-valued, with that ℤ *denoting* the 8-felt anchor by its own docstring ("the 8-felt (~124-bit)
state anchor … NOT a single ~15-bit felt"). `r3_unfoolable` therefore takes an EXPLICIT denotation
`den : Digest8 → Felt` plus its coherence `agg.finalRoot = den wideAggHead`, which makes that modeling
step VISIBLE as a hypothesis instead of silently assumed at the seam. What #22 was actually about — the
DEPLOYED marshaling projecting an 8-felt anchor to lane 0, and the VK read off the artifact — is closed;
widening `foldedFinalRoot` itself to `Digest8` is a separate, larger model refactor across
`RecursiveAggregation`/`HistoryAggregation`, not attempted here.

`#assert_axioms`-clean (⊆ {propext, Classical.choice, Quot.sound}); `EngineSound` enters as a hypothesis
FIELD exactly as it does in the composed headline. Verified with `lake build Dregg2.Grain.R3Verify`.
-/
import Dregg2.Circuit.RecursiveAggregation

namespace Dregg2.Grain.R3Verify

open Dregg2.Exec (RecChainedState recCexec)
open Dregg2.Distributed.HistoryAggregation (ChainStep ChainBound foldedFinalRoot)
open Dregg2.Circuit.RecursiveAggregation
  (Aggregate EngineSound AggregateAttests light_client_verifies_whole_history)

/-! ## 0. The wide values at the seam — felt resolution.

Both sides of the binding the wound named carry a WIDE value at HEAD, and this is the type that says so:

  * the aggregate's committed head is Rust `WholeChainProof.final_root : [BabyBear; SEG_ANCHOR_WIDTH]`
    with `SEG_ANCHOR_WIDTH = 8` (`circuit-prove/src/ivc_turn_chain.rs:284`) — the ~124-bit faithful
    state anchor; and
  * the renter's anchored head is sourced from the leg's `wide_new_root8() : Option<[BabyBear; 8]>`
    (`circuit-prove/src/joint_turn_aggregation.rs:1330`), the AFTER 8-felt commit.

Modeled at felt resolution exactly as `Distributed.FinalityCertWidth` and `Cell.InterfaceIdWidth` do: a
lane is its canonical `as_u32()` value, kept as an integer (the BabyBear range prices the offline grind
but is irrelevant to the binding's injectivity). -/

/-- One field lane, modeled by its canonical `as_u32()` value. -/
abbrev Felt : Type := ℤ

/-- The WIDE 8-felt (~124-bit) state anchor — faithful to Rust `[BabyBear; SEG_ANCHOR_WIDTH]`. -/
abbrev Digest8 : Type := Fin 8 → Felt

/-- The root-circuit verifier-key fingerprint — Rust `RecursionVk(pub [u8; 32])`, a blake3-32 over the
VK MATERIAL (`recursion_vk_fingerprint`, `circuit-prove/src/plonky3_recursion_impl.rs:711`), carried on
the wire as eight `u32` lanes, big-endian per 4-byte chunk. That repacking is a BIJECTION on the 32
bytes, so lane equality here IS byte equality of the fingerprints (the Rust side pins this with
`vk_lane_packing_is_injective_per_byte`, which flips each of the 32 bytes in turn).

These lanes reuse `Felt`'s integer carrier for convenience; they are NOT field elements (a `u32` lane
exceeds the BabyBear range). Nothing below treats them as field elements — the only operation is
equality, and `Felt := ℤ` is unbounded, so the model is faithful. -/
abbrev Vk8 : Type := Fin 8 → Felt

/-- The pre-fix seam's squeeze — lane 0 of the eight, i.e. Rust `final_root[0].as_u32()`, ~31 bits. -/
def lane0 (d : Digest8) : Felt := d 0

section Verify

variable (Proof : Type)
variable (verify : Proof → Bool)
variable (CH : Dregg2.Exec.CellId → Dregg2.Exec.Value → ℤ)
variable (RH : Dregg2.Exec.RecordKernelState → ℤ)
variable (cmb : ℤ → ℤ → ℤ)
variable (compress : ℤ → ℤ → ℤ)
variable (compressN : List ℤ → ℤ)

/-! ## 1. The two cores — the FALSIFIED narrow one, and the DEPLOYED wide one.

`r3VerifyCoreNarrow` is the PRE-FIX decision, retained as the subject of the falsifiers (§5) and as the
step `r3_unfoolable` reduces through. `r3VerifyCore` is the deployed decision the `@[export]` compiles
and `grain-verify` calls. -/

/-- **THE PRE-FIX (FALSIFIED) CORE.** `aggregateVerified && aggregateHead == anchoredHead` over a SINGLE
felt, with the VK conjunct absent because the Rust seam self-anchored it. Retained ONLY as the falsified
form the repair is measured against — it is NOT exported and NOT the decision any caller reaches. -/
def r3VerifyCoreNarrow (aggregateVerified : Bool) (aggregateHead anchoredHead : Felt) : Bool :=
  aggregateVerified && aggregateHead == anchoredHead

/-- **THE DEPLOYED R3 VERIFY CORE (post-repair).** Decides R3-accept from four facts the Rust
`grain-verify` marshals:
  * `aggregateVerified : Bool` — the verified-status of the whole-chain STARK aggregate, i.e. the output
    of the heavy `verify_whole_chain_proof_bytes` run **against the caller's expected anchor**
    (`= verify agg.root` in the model). Its SOUNDNESS is the named `EngineSound` boundary.
  * `presentedVk : Vk8` — the fingerprint RECOMPUTED from the presented root (`root_vk_fingerprint`).
  * `expectedVk : Vk8` — the CALLER's out-of-band honest-setup anchor. Comparing these two is what makes
    the verified-status a statement about the RIGHT circuit; taking `expectedVk := presentedVk` is the
    self-anchoring `selfAnchoredVk_vacuous` proves empty.
  * `aggregateHead`, `anchoredHead : Digest8` — the aggregate's committed 8-felt head and the R1-anchored
    8-felt head. FULL-WIDTH equality binds the aggregate to THIS grain's THIS history.

A plain `def … : Bool`, fail-closed: any mismatch is `false`. This IS the object `@[export]` compiles to
native and `grain-verify` calls. -/
def r3VerifyCore (aggregateVerified : Bool) (presentedVk expectedVk : Vk8)
    (aggregateHead anchoredHead : Digest8) : Bool :=
  aggregateVerified
    && (List.ofFn presentedVk == List.ofFn expectedVk)
    && (List.ofFn aggregateHead == List.ofFn anchoredHead)

/-- Decomposition of the PRE-FIX accept decision. Pure `Bool` algebra (`Int` is `LawfulBEq`). -/
theorem r3VerifyCoreNarrow_true {v : Bool} {a b : Felt} (h : r3VerifyCoreNarrow v a b = true) :
    v = true ∧ a = b := by
  unfold r3VerifyCoreNarrow at h
  rw [Bool.and_eq_true] at h
  exact ⟨h.1, by simp only [beq_iff_eq] at h; exact h.2⟩

/-- Decomposition of the DEPLOYED accept decision: it accepts IFF the aggregate verified AND the
presented VK IS the caller's anchor AND the FULL 8-felt heads agree. `List.ofFn` is injective, so the
lane-list equalities reflect equality of the wide values themselves. -/
theorem r3VerifyCore_true {v : Bool} {p e : Vk8} {a b : Digest8}
    (h : r3VerifyCore v p e a b = true) : v = true ∧ p = e ∧ a = b := by
  unfold r3VerifyCore at h
  rw [Bool.and_eq_true, Bool.and_eq_true] at h
  obtain ⟨⟨hv, hvk⟩, hhd⟩ := h
  refine ⟨hv, ?_, ?_⟩
  · have h1 : List.ofFn p = List.ofFn e := by simp only [beq_iff_eq] at hvk; exact hvk
    exact List.ofFn_inj.mp h1
  · have h2 : List.ofFn a = List.ofFn b := by simp only [beq_iff_eq] at hhd; exact hhd
    exact List.ofFn_inj.mp h2

/-- **THE REFINEMENT.** The deployed wide decision IMPLIES the pre-fix narrow one under ANY denotation
`den` of a wide anchor as the model's single field element — so the widened core's accept set is a SUBSET
of the narrow core's, and every soundness consequence of the narrow form is inherited unchanged. (The
inclusion is STRICT: §5's falsifiers exhibit narrow-accepts that the wide core refuses.) -/
theorem r3VerifyCore_implies_narrow (den : Digest8 → Felt) {v : Bool} {p e : Vk8} {a b : Digest8}
    (h : r3VerifyCore v p e a b = true) : r3VerifyCoreNarrow v (den a) (den b) = true := by
  obtain ⟨hv, _, hab⟩ := r3VerifyCore_true h
  unfold r3VerifyCoreNarrow
  rw [hv, hab]
  simp

/-! ## 2. THE R3 VERDICT + THE SOUNDNESS HEADLINE — unfoolable = integrity + completeness, anchored.

`R3Attested` is the precise "unfoolable whole history anchored at `anchoredHead`", using the aggregation
theorem's own conclusion vocabulary:
  * `integrity` — every turn executed correctly per the verified executor (`AggregateAttests.every_turn`);
  * `complete`  — the chain is correctly ordered, nothing dropped/inserted/reordered
    (`AggregateAttests.ordered`, `ChainBound`); and
  * `anchored_is_genuine_fold` — the R1-anchored head IS the genuine fold of THIS whole history
    (`anchoredHead = foldedFinalRoot g steps`), the binding that pins the sound history to the grain. -/

/-- **`R3Attested`** — the unfoolable-whole-history verdict for a grain anchored at `anchoredHead`. -/
structure R3Attested (agg : Aggregate Proof) (g : RecChainedState) (steps : List ChainStep)
    (anchoredHead : ℤ) : Prop where
  /-- INTEGRITY: every turn in the history executed correctly per the verified executor. -/
  integrity : ∀ s ∈ steps, recCexec s.pre s.turn = some s.post
  /-- COMPLETENESS: the chain is correctly ordered — no host fabrication (no drop/insert/reorder). -/
  complete : ChainBound CH RH cmb compress compressN steps
  /-- ANCHORING: the R1-anchored head IS the genuine fold of THIS whole history — so the sound history
  is about THIS grain's THIS head, not a swapped one. -/
  anchored_is_genuine_fold :
    anchoredHead = foldedFinalRoot CH RH cmb compress compressN g steps

/-- **`r3_unfoolable_narrow`** — the composed headline at the PRE-FIX core's resolution, retained as the
step the deployed headline reduces through. Given the pre-fix accept, the whole history is `R3Attested`.
COMPOSITION only: `light_client_verifies_whole_history` delivers `AggregateAttests` from
`verify agg.root = true`, and the head equality rewrites its `final_is_genuine_fold` pin onto
`anchoredHead`. The load-bearing recursion soundness is the SAME `es : EngineSound` hypothesis. -/
theorem r3_unfoolable_narrow
    (agg : Aggregate Proof) (g : RecChainedState) (steps : List ChainStep) (anchoredHead : ℤ)
    (es : EngineSound Proof verify CH RH cmb compress compressN agg g steps)
    (h : r3VerifyCoreNarrow (verify agg.root) agg.finalRoot anchoredHead = true) :
    R3Attested Proof CH RH cmb compress compressN agg g steps anchoredHead := by
  obtain ⟨hroot, hhead⟩ := r3VerifyCoreNarrow_true h
  have hatt := light_client_verifies_whole_history Proof verify CH RH cmb compress compressN
    agg g steps es hroot
  exact
    { integrity := hatt.every_turn
    , complete := hatt.ordered
    , anchored_is_genuine_fold := by rw [← hhead]; exact hatt.final_is_genuine_fold }

/-- **`r3_unfoolable` (THE R3 HEADLINE, post-repair).** If the DEPLOYED `r3VerifyCore` accepts — the
whole-chain aggregate verified, the presented root's fingerprint IS the caller's out-of-band anchor, and
the FULL 8-felt aggregate head equals the FULL 8-felt R1-anchored head — then the whole history behind
that anchor is `R3Attested`: execution-integrity-sound AND complete, with the anchored head pinned to its
genuine fold. A lying host cannot serve a fabricated/truncated history under this head, cannot re-point a
genuine proof at a foreign anchor by matching ~31 bits of it, and cannot substitute a different circuit's
root.

`den` is the EXPLICIT denotation of a wide 8-felt anchor as the `RecursiveAggregation` model's single
field element, with `hden` its coherence at the seam. This is the modeling step the pre-fix code performed
SILENTLY (and unfaithfully, as `den := lane0`); here it is a visible hypothesis. No step is re-derived and
no axiom is added — the recursion soundness is the SAME `es : EngineSound`. -/
theorem r3_unfoolable
    (agg : Aggregate Proof) (g : RecChainedState) (steps : List ChainStep)
    (den : Digest8 → Felt) (wideAggHead wideAnchoredHead : Digest8) (presentedVk expectedVk : Vk8)
    (hden : agg.finalRoot = den wideAggHead)
    (es : EngineSound Proof verify CH RH cmb compress compressN agg g steps)
    (h : r3VerifyCore (verify agg.root) presentedVk expectedVk wideAggHead wideAnchoredHead = true) :
    R3Attested Proof CH RH cmb compress compressN agg g steps (den wideAnchoredHead) := by
  refine r3_unfoolable_narrow Proof verify CH RH cmb compress compressN agg g steps
    (den wideAnchoredHead) es ?_
  have hnarrow := r3VerifyCore_implies_narrow den h
  rw [hden]
  exact hnarrow

/-! ## 3. THE TEETH — a swapped head, a ~31-bit-only match, and a foreign circuit are all REJECTED.

R3's addition over the aggregation headline is meaningful only if a valid aggregate for history A cannot
be accepted against a DIFFERENT grain's anchored head, and only if the verified-status is about the RIGHT
circuit. Three teeth, all fail-closed regardless of the verified-status. -/

/-- **`r3_wide_head_mismatch_rejected` (THE ANTI-GHOST TOOTH, at full width).** When the aggregate's
committed 8-felt head differs from the anchored 8-felt head — in ANY lane, not just lane 0 — R3 REJECTS.
`&&` short-circuits to `false` no matter the verified-status `v` or the VKs. This is the tooth that makes
the anchoring load-bearing at ~124 bits instead of ~31. -/
theorem r3_wide_head_mismatch_rejected (v : Bool) (p e : Vk8) (a b : Digest8) (hne : a ≠ b) :
    r3VerifyCore v p e a b = false := by
  unfold r3VerifyCore
  have hb : (List.ofFn a == List.ofFn b) = false := by
    simp only [beq_eq_false_iff_ne, ne_eq]
    intro hh
    exact hne (List.ofFn_inj.mp hh)
  rw [hb, Bool.and_false]

/-- **`r3_vk_mismatch_rejected` (THE ANTI-SELF-ANCHOR TOOTH).** When the fingerprint recomputed from the
presented root differs from the caller's out-of-band anchor, R3 REJECTS regardless of everything else — a
root of a DIFFERENT circuit cannot be laundered through by shipping its own fingerprint alongside it. -/
theorem r3_vk_mismatch_rejected (v : Bool) (p e : Vk8) (a b : Digest8) (hne : p ≠ e) :
    r3VerifyCore v p e a b = false := by
  unfold r3VerifyCore
  have hb : (List.ofFn p == List.ofFn e) = false := by
    simp only [beq_eq_false_iff_ne, ne_eq]
    intro hh
    exact hne (List.ofFn_inj.mp hh)
  rw [hb, Bool.and_false, Bool.false_and]

/-- **`r3_unverified_rejected` (THE FAIL-CLOSED TOOTH).** A non-accepting verified-status REJECTS
regardless of the VKs and heads. `grain-verify` RELIES on this proven fact for its fold-failure path: when
the fold or the light-verify fails there is no root to fingerprint, so it marshals status `0` and lets
THIS theorem — not a Rust convention — carry the refusal. -/
theorem r3_unverified_rejected (p e : Vk8) (a b : Digest8) : r3VerifyCore false p e a b = false := by
  simp [r3VerifyCore]

/-- The PRE-FIX tooth, retained: a lane-0 mismatch also rejected. This is ALL the pre-fix core had, and
§5 shows it is not enough. -/
theorem r3_narrow_head_mismatch_rejected (v : Bool) (aggHead anchHead : Felt)
    (hne : aggHead ≠ anchHead) : r3VerifyCoreNarrow v aggHead anchHead = false := by
  unfold r3VerifyCoreNarrow
  have hb : (aggHead == anchHead) = false := by
    simp only [beq_eq_false_iff_ne]; exact hne
  rw [hb, Bool.and_false]

/-! ## 4. The `@[export]` FFI entry (Rust → Lean), running the verified executable core. -/

/-- Read eight consecutive lanes off the parsed wire (missing lanes read `0`; the length gate below
means that never happens on a well-formed wire). -/
def lanesFrom (xs : List Felt) (off : ℕ) : Digest8 := fun i => xs.getD (off + i.val) 0

/-- The number of decimal integers the post-repair wire carries: the status, then FOUR eight-lane
values (presented VK ‖ expected VK ‖ aggregate head ‖ anchored head). -/
def r3WireLen : ℕ := 33

/-- Strict wire parse — EVERY whitespace-separated token must be an integer (`mapM`, not `filterMap`:
a malformed token can no longer be silently dropped and shift the lanes) and the count must be exactly
`r3WireLen`. Anything else is `none`, which the entry renders as the fail-closed `"0"`. -/
def parseWire (input : String) : Option (Bool × Vk8 × Vk8 × Digest8 × Digest8) :=
  match (input.splitOn " ").mapM String.toInt? with
  | some xs =>
      if xs.length = r3WireLen then
        some (xs.getD 0 0 != 0, lanesFrom xs 1, lanesFrom xs 9, lanesFrom xs 17, lanesFrom xs 25)
      else none
  | none => none

/-- **FFI entry** (Rust→`grain-verify`→Lean): `r3WireLen` space-separated decimal ints
`"aggregateVerified presentedVk[0..8] expectedVk[0..8] aggregateHead[0..8] anchoredHead[0..8]"` —
`aggregateVerified` nonzero = the STARK verifier accepted the whole-chain proof AGAINST THE CALLER'S
ANCHOR — → the extracted `r3VerifyCore` as `"1"` (accept) / `"0"` (reject). Runs the VERIFIED Lean R3
decision as native code, the "Lean is the runtime" shape shared with `dregg_fips204_verify` /
`dregg_storage_content_root`. Malformed input fails CLOSED (`"0"`) — including the PRE-REPAIR three-int
wire, so a stale caller can never re-open the ~31-bit binding by accident. -/
@[export dregg_grain_r3_verify]
def r3VerifyFFI (input : String) : String :=
  match parseWire input with
  | some (av, p, e, a, b) => if r3VerifyCore av p e a b then "1" else "0"
  | none => "0"

end Verify

/-! ## 5. THE FALSIFIERS + THE ANTI-LAUNDER — both pre-fix conjuncts were empty, and neither repair
alone is enough.

The wound named two independently fatal weaknesses. Here they are proved, over the concrete perturbation
shape the campaign's Rust teeth use (lane 0 fixed, lane 1 bumped — `Distributed.FinalityCertWidth`'s
`forkRoot`, `Cell.InterfaceIdWidth`'s `leafBumped`), and the repair is proved to refuse exactly them. -/

/-- A concrete honest wide anchor (all eight lanes zero). -/
def anchorHead : Digest8 := fun _ => 0

/-- The lane-0-preserving forgery: agrees with `anchorHead` on lane 0, differs at lane 1. This is the
shape a ~2^31 offline grind buys a lying host — a fabricated whole-history final anchor whose lane 0
matches the renter's honest anchored head. -/
def forgedHead : Digest8 := fun i => if i = 1 then 1 else 0

/-- The two anchors are GENUINELY distinct (they differ at lane 1). -/
theorem forgedHead_ne_anchorHead : forgedHead ≠ anchorHead := by
  intro h
  have h1 := congrFun h 1
  simp [forgedHead, anchorHead] at h1

/-- … yet their lane-0 squeezes — ALL the pre-fix seam compared — are IDENTICAL. -/
theorem lane0_forged_eq_anchor : lane0 forgedHead = lane0 anchorHead := by
  simp [lane0, forgedHead, anchorHead]

/-- **THE HEAD FALSIFIER.** The pre-fix lane-0 core ACCEPTS a whole-history aggregate whose wide
committed head is GENUINELY DIFFERENT from the renter's anchored head — the anti-ghost tooth is defeated
by matching ~31 bits. This is the wound's stated harm, over the concrete grind product. -/
theorem narrowHead_conflates :
    ∃ f a : Digest8, f ≠ a ∧ r3VerifyCoreNarrow true (lane0 f) (lane0 a) = true := by
  refine ⟨forgedHead, anchorHead, forgedHead_ne_anchorHead, ?_⟩
  unfold r3VerifyCoreNarrow
  rw [lane0_forged_eq_anchor]
  simp

/-- **THE NARROW SEAM UNDERDETERMINES.** Sharper than the single witness: a lane-0 pin — everything a
pre-fix accept constrains about the aggregate's head — admits two DISTINCT wide anchors. So the pre-fix
decision simply does not determine which history was folded. -/
theorem narrow_seam_underdetermines (x : Felt) :
    ∃ f a : Digest8, f ≠ a ∧ lane0 f = x ∧ lane0 a = x := by
  refine ⟨fun i => if i = 1 then x + 1 else x, fun _ => x, ?_, ?_, rfl⟩
  · intro h
    have h1 : x + 1 = x := by simpa using congrFun h 1
    simp at h1
  · simp [lane0]

/-- Bump a VK fingerprint's lane 0 — a DIFFERENT circuit's fingerprint, for any given anchor. -/
def bumpVk (e : Vk8) : Vk8 := fun i => if i = 0 then e i + 1 else e i

theorem bumpVk_ne (e : Vk8) : bumpVk e ≠ e := by
  intro h
  have h1 : e 0 + 1 = e 0 := by simpa [bumpVk] using congrFun h 0
  simp at h1

/-- **THE VK FALSIFIER.** The pre-fix seam verified the aggregate against the fingerprint the PROOF
ITSELF supplied (`expectedVk := presentedVk`). That conjunct is VACUOUS: the decision is literally
INDEPENDENT of which circuit the presented root belongs to — every fingerprint whatsoever passes it. So
the pre-fix `verified` status said "this supplied blob self-verifies", never "this is the renter's
chain", which is exactly why the (~31-bit) head equality was carrying the whole binding. -/
theorem selfAnchoredVk_vacuous (v : Bool) (a b : Digest8) (p q : Vk8) :
    r3VerifyCore v p p a b = r3VerifyCore v q q a b := by
  simp [r3VerifyCore]

/-- … and concretely: the self-anchored form ACCEPTS a foreign circuit's root, which the repaired form
REFUSES. -/
theorem selfAnchoredVk_accepts_foreign_root (e : Vk8) :
    r3VerifyCore true (bumpVk e) (bumpVk e) anchorHead anchorHead = true ∧
      r3VerifyCore true (bumpVk e) e anchorHead anchorHead = false := by
  refine ⟨by simp [r3VerifyCore], ?_⟩
  exact r3_vk_mismatch_rejected true (bumpVk e) e anchorHead anchorHead (bumpVk_ne e)

/-! ### The fix-soundness, on exactly the falsified inputs. -/

/-- **FIX SOUND (width).** The repaired core REFUSES the ~31-bit grind product: `forgedHead` matches the
anchor on lane 0 but differs at lane 1, and the full-width equality rejects it — for ANY verified-status
and ANY VKs, including the self-anchored pair. -/
theorem wideHead_refuses_the_forgery (v : Bool) (p e : Vk8) :
    r3VerifyCore v p e forgedHead anchorHead = false :=
  r3_wide_head_mismatch_rejected v p e forgedHead anchorHead forgedHead_ne_anchorHead

/-- **FIX SOUND (VK).** The repaired core REFUSES a presented root whose recomputed fingerprint is not
the caller's out-of-band anchor — for ANY verified-status and ANY heads, including matching ones. -/
theorem vkPin_refuses_the_foreign_root (v : Bool) (e : Vk8) (a b : Digest8) :
    r3VerifyCore v (bumpVk e) e a b = false :=
  r3_vk_mismatch_rejected v (bumpVk e) e a b (bumpVk_ne e)

/-! ### THE ANTI-LAUNDER — half a repair is a green that means nothing.

`Cell.InterfaceIdWidth.finalSqueezeOnly_still_conflates` proved this failure shape once for a widened
tail over narrow leaves. Wound #22 has TWO conjuncts, so the launder has two forms and BOTH are proved
broken here: widening the felt alone leaves the self-anchored VK intact, and pinning the VK alone leaves
the ~31-bit binding intact. -/

/-- The head-widened-but-still-self-anchored form — repair (1) alone. -/
def r3VerifyHeadWidenedOnly (v : Bool) (presentedVk : Vk8) (aggHead anchHead : Digest8) : Bool :=
  r3VerifyCore v presentedVk presentedVk aggHead anchHead

/-- The VK-pinned-but-still-lane-0 form — repair (2) alone. -/
def r3VerifyVkPinnedOnly (v : Bool) (presentedVk expectedVk : Vk8)
    (aggHead anchHead : Digest8) : Bool :=
  v && (List.ofFn presentedVk == List.ofFn expectedVk) && (lane0 aggHead == lane0 anchHead)

/-- **ANTI-LAUNDER A.** Widening the head ALONE is not a repair: the decision remains INDEPENDENT of
which circuit the presented root belongs to, so a foreign circuit's root still passes. Widening the felt
without fixing the self-anchoring would have produced a green that means nothing. -/
theorem headWidenedOnly_still_vacuous_in_vk (v : Bool) (a b : Digest8) (p q : Vk8) :
    r3VerifyHeadWidenedOnly v p a b = r3VerifyHeadWidenedOnly v q a b :=
  selfAnchoredVk_vacuous v a b p q

theorem headWidenedOnly_admits_foreign_circuit (e : Vk8) :
    bumpVk e ≠ e ∧ r3VerifyHeadWidenedOnly true (bumpVk e) anchorHead anchorHead = true := by
  refine ⟨bumpVk_ne e, ?_⟩
  unfold r3VerifyHeadWidenedOnly
  simp [r3VerifyCore]

/-- **ANTI-LAUNDER B.** Pinning the VK ALONE is not a repair either: the head binding is still the
lane-0 equality, so the ~2^31 grind product is still ACCEPTED even with the VK correctly anchored. -/
theorem vkPinnedOnly_still_conflates (e : Vk8) :
    ∃ f a : Digest8, f ≠ a ∧ r3VerifyVkPinnedOnly true e e f a = true := by
  refine ⟨forgedHead, anchorHead, forgedHead_ne_anchorHead, ?_⟩
  unfold r3VerifyVkPinnedOnly
  rw [lane0_forged_eq_anchor]
  simp

/-- **NEITHER HALF ALONE SUFFICES (the joint anti-launder).** For any honest anchor `e`: (A) the
head-widened-only form admits a foreign circuit's root; (B) the VK-pinned-only form admits the ~31-bit
grind; and (C)+(D) the DEPLOYED core refuses both. Fixing ONE conjunct of wound #22 leaves the wound
open — which is why this repair changed both. -/
theorem neither_half_alone_suffices (e : Vk8) :
    (bumpVk e ≠ e ∧ r3VerifyHeadWidenedOnly true (bumpVk e) anchorHead anchorHead = true)
      ∧ (∃ f a : Digest8, f ≠ a ∧ r3VerifyVkPinnedOnly true e e f a = true)
      ∧ (∀ (v : Bool) (a b : Digest8), r3VerifyCore v (bumpVk e) e a b = false)
      ∧ (∀ (v : Bool) (p q : Vk8), r3VerifyCore v p q forgedHead anchorHead = false) :=
  ⟨headWidenedOnly_admits_foreign_circuit e, vkPinnedOnly_still_conflates e,
   fun v a b => vkPin_refuses_the_foreign_root v e a b,
   fun v p q => wideHead_refuses_the_forgery v p q⟩

/-! ## 6. NON-VACUITY — R3 FIRES on a real chain, and both teeth BITE.

The headline would be hollow if `r3VerifyCore` could not accept a real verified history, or if either
new conjunct were vacuous. We reuse `RecursiveAggregation`'s realizing instance (`realAggregate` over the
honest 1-step `realSteps` from `teethGenesis`, whose `real_engine_sound` witnesses the aggregation legs)
and anchor at its GENUINE head. -/

section Realize

open Dregg2.Circuit.RecursiveAggregation
  (RealProof acceptAll zCH zRH zcmb zcompress zcompressN realAggregate realSteps real_engine_sound)
open Dregg2.Exec.ConsensusExec (teethGenesis)

/-- A concrete honest-setup VK anchor for the realizing instance. -/
def realVk : Vk8 := fun i => (i.val : Felt)

/-- Present a model field element as a wide anchor by broadcasting it across the eight lanes. This is
the SAME `FAITHFUL-FLOOR` lift the Rust waist performs for a narrow leg ("a narrow leg broadcasts its
single rotated commit felt across the eight lanes", `WholeChainProof.genesis_root`'s docstring), so the
realizing instance is a real deployed shape; a genuinely wide leg has eight independent lanes and every
theorem above applies to it verbatim. -/
def broadcast (x : Felt) : Digest8 := fun _ => x

theorem lane0_broadcast (x : Felt) : lane0 (broadcast x) = x := rfl

/-- **`r3_fires_on_real_chain` (non-vacuity, POSITIVE).** On the realizing instance, with the presented
fingerprint EQUAL to the honest-setup anchor and the wide aggregate head equal to the wide anchored head,
the DEPLOYED `r3VerifyCore` accepts and `r3_unfoolable` delivers a real `R3Attested` over the honest
1-step history — so the post-repair headline is not an empty implication. -/
theorem r3_fires_on_real_chain :
    R3Attested RealProof zCH zRH zcmb zcompress zcompressN
      realAggregate teethGenesis realSteps realAggregate.finalRoot :=
  r3_unfoolable RealProof acceptAll zCH zRH zcmb zcompress zcompressN
    realAggregate teethGenesis realSteps lane0
    (broadcast realAggregate.finalRoot) (broadcast realAggregate.finalRoot) realVk realVk
    (lane0_broadcast realAggregate.finalRoot).symm real_engine_sound
    (by simp [r3VerifyCore, acceptAll])

/-- **`r3_real_chain_turn_executed` (the attestation is REAL).** Reading R3's conclusion on the witnessed
instance: the (only) turn of the honest history executed — `recCexec teethGenesis honestTurn = some _`. So
R3's verdict is a TRUE fact about a real executor run, not a formal husk. -/
theorem r3_real_chain_turn_executed :
    recCexec teethGenesis Dregg2.Exec.ConsensusExec.honestTurn
      = some Dregg2.Distributed.HistoryAggregation.honestStep.post := by
  have h := r3_fires_on_real_chain.integrity
              Dregg2.Distributed.HistoryAggregation.honestStep (by simp [realSteps])
  simpa [Dregg2.Distributed.HistoryAggregation.honestStep] using h

/-- **`r3_wrong_head_rejected` (non-vacuity, NEGATIVE — the width tooth BITES on the real instance).** A
wide anchored head differing from the genuine one ONLY OUTSIDE LANE 0 makes the DEPLOYED core REJECT on
the realizing instance. Under the PRE-FIX core the very same pair was ACCEPTED (`narrowHead_conflates`),
so this is the repair biting on a real aggregate, not a restatement. -/
theorem r3_wrong_head_rejected :
    r3VerifyCore (acceptAll realAggregate.root) realVk realVk
      (broadcast realAggregate.finalRoot)
      (fun i => if i = 1 then realAggregate.finalRoot + 1 else realAggregate.finalRoot) = false := by
  refine r3_wide_head_mismatch_rejected (acceptAll realAggregate.root) realVk realVk _ _ ?_
  intro h
  have h1 : realAggregate.finalRoot = realAggregate.finalRoot + 1 := by
    simpa [broadcast] using congrFun h 1
  omega

/-- **`r3_foreign_vk_rejected` (non-vacuity, NEGATIVE — the anti-self-anchor tooth BITES on the real
instance).** A presented fingerprint that is not the honest-setup anchor is REJECTED even though the
aggregate verifies and the heads match exactly. Under the PRE-FIX self-anchored seam the same input was
ACCEPTED (`selfAnchoredVk_accepts_foreign_root`). -/
theorem r3_foreign_vk_rejected :
    r3VerifyCore (acceptAll realAggregate.root) (bumpVk realVk) realVk
      (broadcast realAggregate.finalRoot) (broadcast realAggregate.finalRoot) = false :=
  vkPin_refuses_the_foreign_root (acceptAll realAggregate.root) realVk _ _

/-! ### The wire reflects the core — the falsification vectors, on the exported entry.

`wireOf` builds the exact `r3WireLen`-int wire `grain_verify::r3::r3_verify` formats. The vectors below
are the SAME perturbations the Rust falsification test routes through the extracted native code. -/

/-- Render a wire from a status and four eight-lane values. -/
def wireOf (av : ℕ) (p e a b : List Felt) : String :=
  String.intercalate " " (toString av :: (p ++ e ++ a ++ b).map toString)

/-- An honest-setup VK anchor, as eight `u32` lanes. -/
def vkA : List Felt := [11, 22, 33, 44, 55, 66, 77, 88]
/-- A DIFFERENT circuit's fingerprint (lane 0 bumped). -/
def vkB : List Felt := [12, 22, 33, 44, 55, 66, 77, 88]
/-- An honest wide anchored head. -/
def headA : List Felt := [7, 101, 102, 103, 104, 105, 106, 107]
/-- The ~2^31 grind product: lane 0 IDENTICAL to `headA`, lane 1 different. Everything the pre-fix seam
compared is equal; the repaired core sees the difference. -/
def headForged : List Felt := [7, 999, 102, 103, 104, 105, 106, 107]

-- ACCEPT: verified, the presented fingerprint IS the anchor, the full 8-felt heads agree.
#guard r3VerifyFFI (wireOf 1 vkA vkA headA headA) = "1"
-- THE WIDTH TOOTH ON THE WIRE: a forged head differing ONLY OUTSIDE LANE 0 is REFUSED …
#guard r3VerifyFFI (wireOf 1 vkA vkA headForged headA) = "0"
-- … and its lane-0 squeeze — all the pre-fix seam compared — is IDENTICAL, so the pre-fix core accepted.
#guard headForged.headD 0 == headA.headD 0
#guard r3VerifyCoreNarrow true (headForged.headD 0) (headA.headD 0) = true
-- THE ANTI-SELF-ANCHOR TOOTH ON THE WIRE: a foreign circuit's fingerprint is REFUSED …
#guard r3VerifyFFI (wireOf 1 vkB vkA headA headA) = "0"
-- … while the self-anchored form (presented == expected, whatever it is) accepted it.
#guard r3VerifyFFI (wireOf 1 vkB vkB headA headA) = "1"
-- A non-accepting aggregate status REJECTS.
#guard r3VerifyFFI (wireOf 0 vkA vkA headA headA) = "0"
-- FAIL-CLOSED: the PRE-REPAIR three-int wire is now REFUSED, so a stale caller cannot re-open the
-- ~31-bit binding by accident.
#guard r3VerifyFFI "1 42 42" = "0"
-- FAIL-CLOSED: malformed input, and a wire with a non-integer token (strict `mapM`, never a silent drop).
#guard r3VerifyFFI "garbage" = "0"
#guard r3VerifyFFI (wireOf 1 vkA vkA headA headA ++ " x") = "0"

end Realize

/-! ## 7. Axiom hygiene. -/

#assert_axioms Dregg2.Grain.R3Verify.r3VerifyCoreNarrow_true
#assert_axioms Dregg2.Grain.R3Verify.r3VerifyCore_true
#assert_axioms Dregg2.Grain.R3Verify.r3VerifyCore_implies_narrow
#assert_axioms Dregg2.Grain.R3Verify.r3_unfoolable_narrow
#assert_axioms Dregg2.Grain.R3Verify.r3_unfoolable
#assert_axioms Dregg2.Grain.R3Verify.r3_wide_head_mismatch_rejected
#assert_axioms Dregg2.Grain.R3Verify.r3_vk_mismatch_rejected
#assert_axioms Dregg2.Grain.R3Verify.r3_unverified_rejected
#assert_axioms Dregg2.Grain.R3Verify.r3_narrow_head_mismatch_rejected
#assert_axioms Dregg2.Grain.R3Verify.forgedHead_ne_anchorHead
#assert_axioms Dregg2.Grain.R3Verify.lane0_forged_eq_anchor
#assert_axioms Dregg2.Grain.R3Verify.narrowHead_conflates
#assert_axioms Dregg2.Grain.R3Verify.narrow_seam_underdetermines
#assert_axioms Dregg2.Grain.R3Verify.bumpVk_ne
#assert_axioms Dregg2.Grain.R3Verify.selfAnchoredVk_vacuous
#assert_axioms Dregg2.Grain.R3Verify.selfAnchoredVk_accepts_foreign_root
#assert_axioms Dregg2.Grain.R3Verify.wideHead_refuses_the_forgery
#assert_axioms Dregg2.Grain.R3Verify.vkPin_refuses_the_foreign_root
#assert_axioms Dregg2.Grain.R3Verify.headWidenedOnly_still_vacuous_in_vk
#assert_axioms Dregg2.Grain.R3Verify.headWidenedOnly_admits_foreign_circuit
#assert_axioms Dregg2.Grain.R3Verify.vkPinnedOnly_still_conflates
#assert_axioms Dregg2.Grain.R3Verify.neither_half_alone_suffices
#assert_axioms Dregg2.Grain.R3Verify.r3_fires_on_real_chain
#assert_axioms Dregg2.Grain.R3Verify.r3_real_chain_turn_executed
#assert_axioms Dregg2.Grain.R3Verify.r3_wrong_head_rejected
#assert_axioms Dregg2.Grain.R3Verify.r3_foreign_vk_rejected

end Dregg2.Grain.R3Verify
