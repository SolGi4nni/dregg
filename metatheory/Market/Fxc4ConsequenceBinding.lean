/-
# Market.Fxc4ConsequenceBinding — the apex consequence root LOSSLESSLY binds every semantic leg
  (D2 Bazaar-apex lane: the CONSEQUENCE leg's binding law, stated over the exact deployed layout).

The v4 apex boundary (`circuit-prove/src/shielded_exact_apex_v4.rs`) publishes ONE 8-lane
`shielded_consequence_root` = `hash_many_8` of the exact 146-lane FXC4 preimage
(`canonical_fxc4_preimage`): domain + code-owned selectors (`RULE_ID`, ring length, selected leg)
+ the complete ledger/exact endpoints + the full 256-bit nullifier + the 16-lane wide value/asset
binding + the NINETEEN Dark-AMM public lanes + the TWENTY-SEVEN ring public lanes + the exact
output-note count/root. The consequence LEG of the apex campaign needs exactly one law from this
transcript: **the preimage layout is LOSSLESS** — fixed-offset, fixed-width, no field aliasing
into another — so that under the `node8` CR floor the single published root BINDS every leg
simultaneously. A substituted Dark-AMM statement, ring surface, selected leg, nullifier, wide
binding, or output-note root cannot share a consequence root.

This module PROVES that losslessness (`encode_binds`: 146-lane equality forces every one of the
sixteen semantic fields equal — pure `List.append_inj` structure over the pinned widths) and
states the binding law under ONE named floor (`consequence_root_binds_all_legs`), with the
substitution teeth in the `PrivateClearingGameConsequence.substituted_*_cannot_dispatch` register.

**Why this matters for the felt-width class**: the FXC4 root is EIGHT lanes over a lossless
146-lane preimage — the GOOD shape (contrast the ~31-bit `legacy_binding` squeeze priced in
`ShieldedWideJoinPin` / `Market.WideCarrierSameOpening`, which reduces mod p BEFORE binding and
hands over free collisions). What this module does NOT claim: that any deployed AIR *recomputes*
this root in-circuit over the shared witness — today `canonical_fxc4_preimage` is Rust transcript
assembly ("transcript data, never proof authority", its own doc), and the in-AIR recompute is the
apex campaign's authoring work (Lean-authored, law #1). This law is the SPEC that authoring must
refine.

**Scope (honest).** Lanes are `ℤ` (per-lane BabyBear width priced elsewhere); the hash is an
abstract 8-lane function of the exact assembly; the CR floor is named injectivity-style on the
preimage space (the standing Poseidon2 idealization — its game-theoretic grounding is the
`WideCommitBoundary` §R program). Selector constants (`FXC4` domain) are pinned in the encoding;
`RULE_ID`/ring-length are fields so the law also states that they cannot be swapped — the Rust
side pins them code-owned, and the future AIR must too.

`#assert_axioms`-clean (⊆ {propext, Classical.choice, Quot.sound}).
-/
import Mathlib.Tactic
import Dregg2.Tactics

set_option autoImplicit false

namespace Market.Fxc4ConsequenceBinding

/-! ## 1. The exact 146-lane FXC4 preimage, field by field (widths pinned as invariants). -/

/-- ASCII `FXC4` (`SHIELDED_CONSEQUENCE_DOMAIN`, `shielded_exact_apex_v4.rs:59`). -/
def domainFXC4 : ℤ := 0x46584334

/-- The FXC4 preimage: every semantic field of `canonical_fxc4_preimage`, with its exact deployed
lane width pinned as an invariant. Total: `4 + 4+8+16+16+8+8+4+4+8+8 + 19 + 27 + 4+8 = 146`. -/
structure Fxc4Preimage where
  /-- Code-owned Dark-AMM rule selector (`dark_amm_private::RULE_ID`). -/
  ruleId : ℤ
  /-- Code-owned ring public length selector (`RING_ENDPOINT_PUBLIC_LEN`). -/
  ringLen : ℤ
  /-- The selected spent ring leg being promoted to full-width exact authority. -/
  ringLeg : ℤ
  /-- `historical_root_height`, u64 as four u16 lanes. -/
  height : List ℤ
  /-- The historical note root (8 lanes). -/
  historicalRoot : List ℤ
  /-- The FULL 256-bit nullifier, sixteen u16 lanes. -/
  nullifier : List ℤ
  /-- The 16-lane wide value/asset binding (the `WideCarrierSameOpening` carrier). -/
  wideBinding : List ℤ
  /-- Successor exact root (8 lanes, FNI4). -/
  successorRoot : List ℤ
  /-- Prior exact root (8 lanes, FNI4). -/
  priorRoot : List ℤ
  /-- Pre-count, u64/u16x4. -/
  preCount : List ℤ
  /-- Post-count, u64/u16x4. -/
  postCount : List ℤ
  /-- Before outer commitment (8 lanes). -/
  beforeOuter : List ℤ
  /-- After outer commitment (8 lanes). -/
  afterOuter : List ℤ
  /-- The NINETEEN Dark-AMM public lanes (`DARK_AMM_PUBLIC_INPUT_COUNT = 19`). -/
  darkAmm : List ℤ
  /-- The TWENTY-SEVEN ring public lanes (`RING_ENDPOINT_PUBLIC_LEN = 27`). -/
  ring : List ℤ
  /-- Output-note count, u64/u16x4. -/
  outputCount : List ℤ
  /-- The FXO4 output-notes root (8 lanes). -/
  outputRoot : List ℤ
  height_len : height.length = 4
  historicalRoot_len : historicalRoot.length = 8
  nullifier_len : nullifier.length = 16
  wideBinding_len : wideBinding.length = 16
  successorRoot_len : successorRoot.length = 8
  priorRoot_len : priorRoot.length = 8
  preCount_len : preCount.length = 4
  postCount_len : postCount.length = 4
  beforeOuter_len : beforeOuter.length = 8
  afterOuter_len : afterOuter.length = 8
  darkAmm_len : darkAmm.length = 19
  ring_len : ring.length = 27
  outputCount_len : outputCount.length = 4
  outputRoot_len : outputRoot.length = 8

/-- The exact 146-lane assembly, in `canonical_fxc4_preimage`'s deployed order. Right-associated
so each field peels off against its pinned width. -/
def encode (x : Fxc4Preimage) : List ℤ :=
  domainFXC4 :: x.ruleId :: x.ringLen :: x.ringLeg ::
  (x.height ++ (x.historicalRoot ++ (x.nullifier ++ (x.wideBinding ++
   (x.successorRoot ++ (x.priorRoot ++ (x.preCount ++ (x.postCount ++
   (x.beforeOuter ++ (x.afterOuter ++ (x.darkAmm ++ (x.ring ++
   (x.outputCount ++ x.outputRoot)))))))))))))

/-- The assembly has the exact deployed width (`SHIELDED_CONSEQUENCE_PREIMAGE_LANES = 146`). -/
theorem encode_length (x : Fxc4Preimage) : (encode x).length = 146 := by
  simp [encode, x.height_len, x.historicalRoot_len, x.nullifier_len, x.wideBinding_len,
        x.successorRoot_len, x.priorRoot_len, x.preCount_len, x.postCount_len,
        x.beforeOuter_len, x.afterOuter_len, x.darkAmm_len, x.ring_len,
        x.outputCount_len, x.outputRoot_len]

/-! ## 2. LOSSLESSNESS — the layout is injective on every semantic field. Pure structure. -/

private theorem peel {a b c d : List ℤ} (hac : a.length = c.length)
    (h : a ++ b = c ++ d) : a = c ∧ b = d :=
  List.append_inj h hac

/-- **`encode_binds` (the lossless layout).** Equal 146-lane preimages force EVERY semantic field
equal — selectors, ledger endpoints, full nullifier, wide binding, all 19 Dark-AMM lanes, all 27
ring lanes, and the output notes. No hash involved: this is the fixed-offset/fixed-width
structure of the deployed assembly. -/
theorem encode_binds {x y : Fxc4Preimage} (h : encode x = encode y) :
    x.ruleId = y.ruleId ∧ x.ringLen = y.ringLen ∧ x.ringLeg = y.ringLeg ∧
    x.height = y.height ∧ x.historicalRoot = y.historicalRoot ∧
    x.nullifier = y.nullifier ∧ x.wideBinding = y.wideBinding ∧
    x.successorRoot = y.successorRoot ∧ x.priorRoot = y.priorRoot ∧
    x.preCount = y.preCount ∧ x.postCount = y.postCount ∧
    x.beforeOuter = y.beforeOuter ∧ x.afterOuter = y.afterOuter ∧
    x.darkAmm = y.darkAmm ∧ x.ring = y.ring ∧
    x.outputCount = y.outputCount ∧ x.outputRoot = y.outputRoot := by
  simp only [encode, List.cons.injEq, true_and] at h
  obtain ⟨h1, h2, h3, h⟩ := h
  obtain ⟨hHeight, h⟩ := peel (x.height_len.trans y.height_len.symm) h
  obtain ⟨hHist, h⟩ := peel (x.historicalRoot_len.trans y.historicalRoot_len.symm) h
  obtain ⟨hNul, h⟩ := peel (x.nullifier_len.trans y.nullifier_len.symm) h
  obtain ⟨hWide, h⟩ := peel (x.wideBinding_len.trans y.wideBinding_len.symm) h
  obtain ⟨hSucc, h⟩ := peel (x.successorRoot_len.trans y.successorRoot_len.symm) h
  obtain ⟨hPrior, h⟩ := peel (x.priorRoot_len.trans y.priorRoot_len.symm) h
  obtain ⟨hPre, h⟩ := peel (x.preCount_len.trans y.preCount_len.symm) h
  obtain ⟨hPost, h⟩ := peel (x.postCount_len.trans y.postCount_len.symm) h
  obtain ⟨hBefore, h⟩ := peel (x.beforeOuter_len.trans y.beforeOuter_len.symm) h
  obtain ⟨hAfter, h⟩ := peel (x.afterOuter_len.trans y.afterOuter_len.symm) h
  obtain ⟨hAmm, h⟩ := peel (x.darkAmm_len.trans y.darkAmm_len.symm) h
  obtain ⟨hRing, h⟩ := peel (x.ring_len.trans y.ring_len.symm) h
  obtain ⟨hCount, hRoot⟩ := peel (x.outputCount_len.trans y.outputCount_len.symm) h
  exact ⟨h1, h2, h3, hHeight, hHist, hNul, hWide, hSucc, hPrior, hPre, hPost,
         hBefore, hAfter, hAmm, hRing, hCount, hRoot⟩

/-! ## 3. The binding law — one named floor, then the root binds EVERY leg. -/

/-- **The named floor**: `node8` (`hash_many_8`) is collision-free on FXC4 preimages
(injectivity-style, the standing Poseidon2-CR idealization). -/
def Node8CROnFxc4 (H8 : List ℤ → Fin 8 → ℤ) : Prop :=
  ∀ x y : Fxc4Preimage, H8 (encode x) = H8 (encode y) → encode x = encode y

/-- The published 8-lane consequence root. -/
def consequenceRoot (H8 : List ℤ → Fin 8 → ℤ) (x : Fxc4Preimage) : Fin 8 → ℤ :=
  H8 (encode x)

/-- **THE CONSEQUENCE LEG'S LAW**: under the one named floor, a shared consequence root forces
EVERY semantic leg equal — the 19 Dark-AMM lanes, the 27 ring lanes, the selected leg, the full
nullifier, the wide binding, the ledger endpoints, and the output notes, simultaneously. This is
the spec the apex AIR's in-circuit FXC4 recompute must refine. -/
theorem consequence_root_binds_all_legs (H8 : List ℤ → Fin 8 → ℤ)
    (floor : Node8CROnFxc4 H8) {x y : Fxc4Preimage}
    (h : consequenceRoot H8 x = consequenceRoot H8 y) :
    x.ruleId = y.ruleId ∧ x.ringLen = y.ringLen ∧ x.ringLeg = y.ringLeg ∧
    x.height = y.height ∧ x.historicalRoot = y.historicalRoot ∧
    x.nullifier = y.nullifier ∧ x.wideBinding = y.wideBinding ∧
    x.successorRoot = y.successorRoot ∧ x.priorRoot = y.priorRoot ∧
    x.preCount = y.preCount ∧ x.postCount = y.postCount ∧
    x.beforeOuter = y.beforeOuter ∧ x.afterOuter = y.afterOuter ∧
    x.darkAmm = y.darkAmm ∧ x.ring = y.ring ∧
    x.outputCount = y.outputCount ∧ x.outputRoot = y.outputRoot :=
  encode_binds (floor x y h)

/-! ## 4. Substitution teeth — the `substituted_*_cannot_dispatch` register, at the root. -/

/-- A substituted Dark-AMM public surface cannot share a consequence root. -/
theorem substituted_dark_amm_cannot_share_root (H8 : List ℤ → Fin 8 → ℤ)
    (floor : Node8CROnFxc4 H8) {x y : Fxc4Preimage} (hne : x.darkAmm ≠ y.darkAmm) :
    consequenceRoot H8 x ≠ consequenceRoot H8 y := by
  intro h
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, hAmm, -, -, -⟩ :=
    consequence_root_binds_all_legs H8 floor h
  exact hne hAmm

/-- A substituted ring public surface cannot share a consequence root. -/
theorem substituted_ring_cannot_share_root (H8 : List ℤ → Fin 8 → ℤ)
    (floor : Node8CROnFxc4 H8) {x y : Fxc4Preimage} (hne : x.ring ≠ y.ring) :
    consequenceRoot H8 x ≠ consequenceRoot H8 y := by
  intro h
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, hRing, -, -⟩ :=
    consequence_root_binds_all_legs H8 floor h
  exact hne hRing

/-- A substituted wide value/asset binding cannot share a consequence root — the consequence leg
composes with the `WideCarrierSameOpening` join: whichever binding the same-opening forces is the
one the consequence root then locks. -/
theorem substituted_wide_binding_cannot_share_root (H8 : List ℤ → Fin 8 → ℤ)
    (floor : Node8CROnFxc4 H8) {x y : Fxc4Preimage} (hne : x.wideBinding ≠ y.wideBinding) :
    consequenceRoot H8 x ≠ consequenceRoot H8 y := by
  intro h
  obtain ⟨-, -, -, -, -, -, hWide, -, -, -, -, -, -, -, -, -, -⟩ :=
    consequence_root_binds_all_legs H8 floor h
  exact hne hWide

/-- A substituted output-notes root cannot share a consequence root (the output-note leg's
transcript half). -/
theorem substituted_output_root_cannot_share_root (H8 : List ℤ → Fin 8 → ℤ)
    (floor : Node8CROnFxc4 H8) {x y : Fxc4Preimage} (hne : x.outputRoot ≠ y.outputRoot) :
    consequenceRoot H8 x ≠ consequenceRoot H8 y := by
  intro h
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hRoot⟩ :=
    consequence_root_binds_all_legs H8 floor h
  exact hne hRoot

/-- A substituted selected ring leg cannot share a consequence root (the selector is bound, so a
prover cannot re-point the promoted leg after the fact). -/
theorem substituted_ring_leg_cannot_share_root (H8 : List ℤ → Fin 8 → ℤ)
    (floor : Node8CROnFxc4 H8) {x y : Fxc4Preimage} (hne : x.ringLeg ≠ y.ringLeg) :
    consequenceRoot H8 x ≠ consequenceRoot H8 y := by
  intro h
  obtain ⟨-, -, hLeg, -, -, -, -, -, -, -, -, -, -, -, -, -, -⟩ :=
    consequence_root_binds_all_legs H8 floor h
  exact hne hLeg

/-! ## 5. NON-VACUITY — concrete preimages; a false `#guard` is a build error. -/

/-- All-zero baseline preimage at the exact deployed widths. -/
def demoZero : Fxc4Preimage where
  ruleId := 0
  ringLen := 27
  ringLeg := 0
  height := [0, 0, 0, 0]
  historicalRoot := List.replicate 8 0
  nullifier := List.replicate 16 0
  wideBinding := List.replicate 16 0
  successorRoot := List.replicate 8 0
  priorRoot := List.replicate 8 0
  preCount := [0, 0, 0, 0]
  postCount := [1, 0, 0, 0]
  beforeOuter := List.replicate 8 0
  afterOuter := List.replicate 8 0
  darkAmm := List.replicate 19 0
  ring := List.replicate 27 0
  outputCount := [1, 0, 0, 0]
  outputRoot := List.replicate 8 0
  height_len := rfl
  historicalRoot_len := rfl
  nullifier_len := rfl
  wideBinding_len := rfl
  successorRoot_len := rfl
  priorRoot_len := rfl
  preCount_len := rfl
  postCount_len := rfl
  beforeOuter_len := rfl
  afterOuter_len := rfl
  darkAmm_len := rfl
  ring_len := rfl
  outputCount_len := rfl
  outputRoot_len := rfl

/-- The same preimage with ONE Dark-AMM lane substituted. -/
def demoAmmSwap : Fxc4Preimage :=
  { demoZero with
    darkAmm := 5 :: List.replicate 18 0
    darkAmm_len := rfl }

-- The assembly is exactly 146 lanes on the concrete instance:
#guard decide ((encode demoZero).length = 146) = true
-- One substituted Dark-AMM lane already separates the preimages (losslessness bites):
#guard decide (encode demoAmmSwap ≠ encode demoZero) = true
-- …while their other legs agree (the separation is exactly the substituted field):
#guard decide (demoAmmSwap.ring = demoZero.ring) = true
#guard decide (demoAmmSwap.wideBinding = demoZero.wideBinding) = true

/-- The demo pair is a genuine Dark-AMM substitution (non-vacuity of the §4 teeth's hypothesis). -/
theorem demo_amm_swap_is_substitution : demoAmmSwap.darkAmm ≠ demoZero.darkAmm := by decide

/-! ## 6. Axiom hygiene. -/

#assert_all_clean [
  Market.Fxc4ConsequenceBinding.encode_length,
  Market.Fxc4ConsequenceBinding.encode_binds,
  Market.Fxc4ConsequenceBinding.consequence_root_binds_all_legs,
  Market.Fxc4ConsequenceBinding.substituted_dark_amm_cannot_share_root,
  Market.Fxc4ConsequenceBinding.substituted_ring_cannot_share_root,
  Market.Fxc4ConsequenceBinding.substituted_wide_binding_cannot_share_root,
  Market.Fxc4ConsequenceBinding.substituted_output_root_cannot_share_root,
  Market.Fxc4ConsequenceBinding.substituted_ring_leg_cannot_share_root,
  Market.Fxc4ConsequenceBinding.demo_amm_swap_is_substitution]

end Market.Fxc4ConsequenceBinding
