/-
# Dregg2.Distributed.BlsQuorumCert — the DISTRIBUTED-consensus meaning of a BLS quorum certificate.

`federation/src/threshold.rs` + the `hints` crate (BLS12-381 + KZG weighted-threshold signatures) give
the federation ONE *constant-size* aggregate certificate (`ThresholdQC`, `threshold.rs:62`) proving a
weighted threshold of committee members signed a message. `Crypto/BlsThreshold.lean` already proves the
SINGLE-CERT soundness reduction (the three-gate `verify_aggregate` cascade → "a genuine weighted quorum
signed `m`", under the named irreducible primitives `KzgBinding` / `BlsAggUnforgeable` / `SnarkPolyIOP`).

This module is the DISTRIBUTED layer ON TOP of that single-cert reduction — the property the *consensus*
uses and that single-cert soundness does NOT give you: under the federation's canonical BFT corruption
bound `f = ⌊n/3⌋`, an accepting QC's extracted signer set must contain an HONEST member, and any two
accepting QCs over the same committee must SHARE an honest member. That is the non-forgeability + the
non-equivocation backbone of using a BLS QC as a consensus certificate at `n > 1`.

## What is REUSED (no duplication)

* `Dregg2.Crypto.BlsThreshold` — the single-cert objects: `Committee`, `ThresholdCert`, its
  `SnarkContract` (the SNARK binds `aggWeight = selectedWeight selected`, `selected ⊆ members`), and
  `accepting_cert_has_quorum`. We do NOT re-derive selector arithmetic; we CONSUME `quorum_weight_suffices`
  to get `selectedWeight selected ≥ threshold` and build the corruption-set reasoning on top.
* `Dregg2.Distributed.EpochReconfig.quorumThreshold` (= `n − n/3`, the `compute_bft_threshold` /
  `quorum_threshold` of `federation/src/lib.rs:155`, `epoch.rs:186`). We REUSE the count formula and its
  `quorum_gt_half`; we do NOT re-prove the count-cardinality `quorums_intersect` — instead we prove the
  *Finset-level, corruption-set-aware* versions that EpochReconfig's `Nat`-cardinality lemma cannot state
  (it is about disjoint reconfig quorums of distinct old members; this is about an honest signer existing
  inside ONE BLS aggregate's selected set against a named corruption set `B`).

## The honest primitive boundary

The fact that `selected` is a genuine set of members who signed `msg` is the content of the named
irreducible BLS/SNARK primitives, DISCHARGED via `Crypto.BlsThreshold`'s `SnarkContract` / `BlsContract`
hypotheses — NEVER faked `:= True`. What is PROVED here (pure finite combinatorics, no crypto) is the
distributed consequence: honest-signer presence and pairwise honest-signer overlap under `|B| ≤ ⌊n/3⌋`.

`#assert_axioms`-clean (⊆ {propext, Classical.choice, Quot.sound}); NO `sorry`/`:=True`/`native_decide`.
Differential anchor: `federation/src/lib.rs::{quorum_threshold,fault_tolerance}` (`#guard` golden vectors)
+ `threshold.rs` equal-weight committee semantics. Companion: `EpochReconfig` (reconfig quorum) and
`CheckpointPrune` (the QC as a checkpoint attestation portal).
-/
import Dregg2.Crypto.BlsThreshold
import Dregg2.Distributed.EpochReconfig

namespace Dregg2.Distributed.BlsQuorumCert

open Finset
open Dregg2.Crypto.BlsThreshold (Committee ThresholdCert)
open Dregg2.Crypto.BlsThreshold.Committee (totalWeight selectedWeight)
open Dregg2.Crypto.BlsThreshold.ThresholdCert (accepts SnarkContract)
open Dregg2.Distributed.EpochReconfig (quorumThreshold quorum_gt_half quorum_le)

universe u

/-! ## §1 — the BFT fault budget (faithful to `federation/src/lib.rs::fault_tolerance`).

`fault_tolerance n = ⌊n/3⌋` (`lib.rs:169`) and `quorum_threshold n = n − ⌊n/3⌋` (`lib.rs:155`). We REUSE
`EpochReconfig.quorumThreshold` for the quorum count; here we name the dual `faultBudget` and pin the
ONE relation the distributed proofs need: `quorumThreshold n > faultBudget n` for `n ≥ 1` (a quorum is
strictly larger than the corruption budget — that is WHY a quorum cannot be all-corrupt). -/

/-- **`faultBudget n = ⌊n/3⌋`** — the maximum number of Byzantine/corrupt committee members the
federation tolerates (`fault_tolerance`, `federation/src/lib.rs:169`). -/
def faultBudget (n : ℕ) : ℕ := n / 3

@[simp] theorem faultBudget_def (n : ℕ) : faultBudget n = n / 3 := rfl

/-- The quorum threshold IS the membership minus the fault budget (`quorum_threshold = n − f`,
`lib.rs:155-160`). Pins the two REUSED Rust formulas to each other. -/
theorem quorumThreshold_eq_sub (n : ℕ) : quorumThreshold n = n - faultBudget n := rfl

/-- **`quorum_gt_faultBudget`** (PROVED) — a quorum is STRICTLY larger than the corruption budget for
`n ≥ 1`: `n − ⌊n/3⌋ > ⌊n/3⌋`. This is the distributed safety backbone: a set of `quorumThreshold n`
members can never be contained in any corruption set of size `≤ faultBudget n`. -/
theorem quorum_gt_faultBudget (n : ℕ) (hn : 1 ≤ n) :
    faultBudget n < quorumThreshold n := by
  unfold faultBudget quorumThreshold
  omega

/-- **`StrictBft n`** — the GENUINE robust-BFT regime `n > 3·⌊n/3⌋`, i.e. `n` is NOT an exact multiple
of `3·f`. This is the HONEST precondition for honest-overlap: when `n = 3f` exactly (e.g. `n=3, f=1`)
the BFT quorum `n−f = 2f` can share EXACTLY one member, which could be the single corrupt one — so two
QCs need NOT share an honest signer. Robust BFT (`n ≥ 3f+1`) excludes this. We carry it explicitly
rather than fake a margin that is false at `n=3,6,9,…`. -/
def StrictBft (n : ℕ) : Prop := 3 * faultBudget n < n

/-- The strict-BFT regime is exactly "`n` not a multiple of 3" (since `f = ⌊n/3⌋`). -/
theorem strictBft_iff (n : ℕ) : StrictBft n ↔ ¬ (3 ∣ n) := by
  unfold StrictBft faultBudget
  constructor
  · intro h hdvd
    obtain ⟨k, rfl⟩ := hdvd
    omega
  · intro h
    rcases Nat.lt_or_ge (3 * (n / 3)) n with hlt | hge
    · exact hlt
    · exfalso; exact h ⟨n / 3, by omega⟩

/-- **`quorum_overlap_gt_faultBudget`** (PROVED, under `StrictBft`) — the inclusion–exclusion margin:
two quorums each omit at most `faultBudget n` honest spots, and together exceed `n`, so they must share
more than the corruption budget. `2·quorumThreshold n − n > faultBudget n`. Under `StrictBft` (`n > 3f`)
this holds; it is FALSE at `n = 3f` exactly — which is precisely why robust BFT demands `n ≥ 3f+1`. -/
theorem quorum_overlap_gt_faultBudget (n : ℕ) (hn : 1 ≤ n) (hbft : StrictBft n) :
    faultBudget n < 2 * quorumThreshold n - n := by
  unfold StrictBft faultBudget quorumThreshold at *
  omega

/-! ## §2 — the equal-weight committee specialization (faithful to `threshold.rs`).

`federation/src/threshold.rs` uses EQUAL weights (every member weight 1, `threshold.rs:228`), so
`selectedWeight S = |S|` (the count) and the BFT `threshold` is a member COUNT (`threshold_value` u64,
`threshold.rs:48`). We carry the equal-weight predicate explicitly so the count-based corruption
reasoning is honest about its hypothesis (the general weighted case is left to `Crypto.BlsThreshold`). -/

variable {PK : Type u}

/-- **`EqualWeight C`** — every committee member has weight 1 (`federation/src/threshold.rs:228`,
`weights = vec![F::one(); num_members]`). Under this, `selectedWeight S` over `S ⊆ members` is `|S|`. -/
def EqualWeight (C : Committee PK) : Prop := ∀ i ∈ C.members, C.weight i = 1

/-- Under equal weight, the selected weight of a sub-committee IS its cardinality. -/
theorem selectedWeight_eq_card {C : Committee PK} (hw : EqualWeight C)
    {S : Finset ℕ} (hS : S ⊆ C.members) :
    C.selectedWeight S = S.card := by
  classical
  unfold Dregg2.Crypto.BlsThreshold.Committee.selectedWeight
  rw [Finset.sum_congr rfl (fun i hi => hw i (hS hi))]
  simp

/-! ## §3 — the corruption set and the SIGNER-SET extracted from an accepting QC.

A `Corruption C` is a NAMED set `B ⊆ members` of up-to-`faultBudget` Byzantine members (the adversary
the federation is hardened against). The honest members are `members \ B`. An accepting `ThresholdCert`'s
`selected` set (the SNARK's `b`-bitvector, bound by `SnarkContract`) is the set that signed. The whole
distributed point: that signer set, at quorum threshold, reaches OUTSIDE `B`. -/

/-- **`Corruption C`** — a Byzantine corruption set: `members'` ⊆ committee with `|members'| ≤ faultBudget`.
This is the adversary the BLS QC must be sound against — it can sign with every corrupt key but cannot
forge an honest member's signature (that is `BlsAggUnforgeable`, discharged in `Crypto.BlsThreshold`). -/
structure Corruption (C : Committee PK) where
  /-- The set of corrupt committee members. -/
  corrupt : Finset ℕ
  /-- Corrupt members are genuine committee members. -/
  sub : corrupt ⊆ C.members
  /-- At most `faultBudget |members|` are corrupt — the BFT bound `f = ⌊n/3⌋`. -/
  bounded : corrupt.card ≤ faultBudget C.members.card

/-- The honest committee members: `members \ corrupt`. -/
def Corruption.honest {C : Committee PK} (B : Corruption C) : Finset ℕ :=
  C.members \ B.corrupt

/-! ## §4 — THE DISTRIBUTED SOUNDNESS THEOREMS (proved; pure finite combinatorics on top of the
single-cert `SnarkContract`). -/

/-- **`quorum_size_exceeds_faultBudget`** (PROVED) — an accepting equal-weight cert at the canonical
quorum threshold selects MORE members than the corruption budget. From `quorum_weight_suffices`
(`Crypto.BlsThreshold`) we get `selectedWeight selected ≥ threshold`; with equal weight that is
`|selected| ≥ threshold`; at `threshold = quorumThreshold n` and `quorum_gt_faultBudget` we get
`|selected| > faultBudget n`. -/
theorem quorum_size_exceeds_faultBudget
    {C : Committee PK} {msg : ℕ} (cert : ThresholdCert C msg)
    (hw : EqualWeight C) (hacc : cert.accepts) (hsnark : cert.SnarkContract)
    (hthr : cert.threshold = quorumThreshold C.members.card)
    (hn : 1 ≤ C.members.card) :
    faultBudget C.members.card < cert.selected.card := by
  have hge : C.selectedWeight cert.selected ≥ cert.threshold :=
    Dregg2.Crypto.BlsThreshold.quorum_weight_suffices cert hacc hsnark
  rw [selectedWeight_eq_card hw hsnark.selected_sub] at hge
  have hq : faultBudget C.members.card < quorumThreshold C.members.card :=
    quorum_gt_faultBudget _ hn
  omega

/-- **`quorum_has_honest_signer`** (PROVED — the NON-FORGEABILITY backbone at `n > 1`). An accepting
equal-weight QC at quorum threshold, against ANY corruption set `B` with `|B| ≤ faultBudget n`, has at
least one HONEST signer: a member `i ∈ selected ∩ honest`. So a QC CANNOT be produced by the corrupt set
alone — the adversary, holding only `≤ ⌊n/3⌋` keys, cannot gather a quorum. This is the distributed
consequence the single-cert reduction does not give: it ties the SNARK-extracted signer set to the
corruption model. -/
theorem quorum_has_honest_signer
    {C : Committee PK} {msg : ℕ} (cert : ThresholdCert C msg) (B : Corruption C)
    (hw : EqualWeight C) (hacc : cert.accepts) (hsnark : cert.SnarkContract)
    (hthr : cert.threshold = quorumThreshold C.members.card)
    (hn : 1 ≤ C.members.card) :
    ∃ i, i ∈ cert.selected ∧ i ∈ B.honest := by
  classical
  -- |selected| > |corrupt|, so selected ⊄ corrupt; the witness is honest.
  have hbig : faultBudget C.members.card < cert.selected.card :=
    quorum_size_exceeds_faultBudget cert hw hacc hsnark hthr hn
  have hcorr : B.corrupt.card ≤ faultBudget C.members.card := B.bounded
  have hnotsub : ¬ cert.selected ⊆ B.corrupt := by
    intro hsub
    have := Finset.card_le_card hsub
    omega
  obtain ⟨i, hi_sel, hi_notcorr⟩ := Finset.not_subset.mp hnotsub
  refine ⟨i, hi_sel, ?_⟩
  -- i ∈ selected ⊆ members and i ∉ corrupt ⇒ i ∈ members \ corrupt = honest.
  have hi_mem : i ∈ C.members := hsnark.selected_sub hi_sel
  simp only [Corruption.honest, Finset.mem_sdiff]
  exact ⟨hi_mem, hi_notcorr⟩

/-- **`two_quorums_share_member`** (PROVED) — two accepting equal-weight QCs over the SAME committee at
quorum threshold share a committee member: `selected₁ ∩ selected₂ ≠ ∅`. Inclusion–exclusion:
`|S₁| + |S₂| ≥ 2·quorumThreshold n > n ≥ |S₁ ∪ S₂|`. This is the BLS-QC analogue of EpochReconfig's
`quorums_intersect`, but at the Finset level over the SAME committee's signer sets (not reconfig
cardinalities) — the precondition for honest-overlap below. -/
theorem two_quorums_share_member
    {C : Committee PK} {m₁ m₂ : ℕ}
    (cert₁ : ThresholdCert C m₁) (cert₂ : ThresholdCert C m₂)
    (hw : EqualWeight C)
    (hacc₁ : cert₁.accepts) (hsnark₁ : cert₁.SnarkContract)
    (hacc₂ : cert₂.accepts) (hsnark₂ : cert₂.SnarkContract)
    (hthr₁ : cert₁.threshold = quorumThreshold C.members.card)
    (hthr₂ : cert₂.threshold = quorumThreshold C.members.card)
    (hn : 1 ≤ C.members.card) :
    (cert₁.selected ∩ cert₂.selected).Nonempty := by
  classical
  -- |selected_k| ≥ quorumThreshold n
  have hc₁ : quorumThreshold C.members.card ≤ cert₁.selected.card := by
    have hge := Dregg2.Crypto.BlsThreshold.quorum_weight_suffices cert₁ hacc₁ hsnark₁
    rw [selectedWeight_eq_card hw hsnark₁.selected_sub, hthr₁] at hge
    exact hge
  have hc₂ : quorumThreshold C.members.card ≤ cert₂.selected.card := by
    have hge := Dregg2.Crypto.BlsThreshold.quorum_weight_suffices cert₂ hacc₂ hsnark₂
    rw [selectedWeight_eq_card hw hsnark₂.selected_sub, hthr₂] at hge
    exact hge
  -- union ⊆ members ⇒ |union| ≤ n
  have hunion_sub : cert₁.selected ∪ cert₂.selected ⊆ C.members :=
    Finset.union_subset hsnark₁.selected_sub hsnark₂.selected_sub
  have hunion_le : (cert₁.selected ∪ cert₂.selected).card ≤ C.members.card :=
    Finset.card_le_card hunion_sub
  -- inclusion–exclusion: |A| + |B| = |A∪B| + |A∩B|
  have hie := Finset.card_union_add_card_inter cert₁.selected cert₂.selected
  -- strict majority: 2·quorumThreshold n > n
  have hgt := quorum_gt_half C.members.card hn
  -- If the intersection were empty its card is 0; then |A|+|B| = |A∪B| ≤ n, contradicting 2q > n.
  rw [Finset.nonempty_iff_ne_empty]
  intro hempty
  rw [hempty, Finset.card_empty] at hie
  omega

/-- **`two_quorums_share_honest_member`** (PROVED — the NON-EQUIVOCATION backbone). Two accepting
equal-weight QCs over the same committee at quorum threshold, against ANY corruption set `B`, share an
HONEST member: `∃ i ∈ selected₁ ∩ selected₂ ∩ honest`. The shared signer cannot be entirely accounted
for by the corrupt set, because the forced overlap `2·quorumThreshold n − n` strictly exceeds
`faultBudget n`. So if two conflicting messages each gather a QC, some HONEST member signed BOTH. -/
theorem two_quorums_share_honest_member
    {C : Committee PK} {m₁ m₂ : ℕ}
    (cert₁ : ThresholdCert C m₁) (cert₂ : ThresholdCert C m₂) (B : Corruption C)
    (hw : EqualWeight C)
    (hacc₁ : cert₁.accepts) (hsnark₁ : cert₁.SnarkContract)
    (hacc₂ : cert₂.accepts) (hsnark₂ : cert₂.SnarkContract)
    (hthr₁ : cert₁.threshold = quorumThreshold C.members.card)
    (hthr₂ : cert₂.threshold = quorumThreshold C.members.card)
    (hn : 1 ≤ C.members.card) (hbft : StrictBft C.members.card) :
    ∃ i, i ∈ cert₁.selected ∧ i ∈ cert₂.selected ∧ i ∈ B.honest := by
  classical
  set n := C.members.card with hn_def
  -- cardinalities of the two quorums.
  have hc₁ : quorumThreshold n ≤ cert₁.selected.card := by
    have hge := Dregg2.Crypto.BlsThreshold.quorum_weight_suffices cert₁ hacc₁ hsnark₁
    rw [selectedWeight_eq_card hw hsnark₁.selected_sub, hthr₁] at hge
    exact hge
  have hc₂ : quorumThreshold n ≤ cert₂.selected.card := by
    have hge := Dregg2.Crypto.BlsThreshold.quorum_weight_suffices cert₂ hacc₂ hsnark₂
    rw [selectedWeight_eq_card hw hsnark₂.selected_sub, hthr₂] at hge
    exact hge
  -- |selected₁ ∩ selected₂| ≥ 2·quorumThreshold n − n > faultBudget n.
  have hunion_sub : cert₁.selected ∪ cert₂.selected ⊆ C.members :=
    Finset.union_subset hsnark₁.selected_sub hsnark₂.selected_sub
  have hunion_le : (cert₁.selected ∪ cert₂.selected).card ≤ n :=
    Finset.card_le_card hunion_sub
  have hie := Finset.card_union_add_card_inter cert₁.selected cert₂.selected
  have hoverlap : faultBudget n < (cert₁.selected ∩ cert₂.selected).card := by
    have hmargin := quorum_overlap_gt_faultBudget n hn hbft
    omega
  -- The intersection ⊆ members, has card > faultBudget ≥ |corrupt|, so it escapes the corrupt set.
  have hinter_sub : cert₁.selected ∩ cert₂.selected ⊆ C.members :=
    (Finset.inter_subset_left).trans hsnark₁.selected_sub
  have hcorr : B.corrupt.card ≤ faultBudget n := B.bounded
  have hnotsub : ¬ (cert₁.selected ∩ cert₂.selected) ⊆ B.corrupt := by
    intro hsub
    have := Finset.card_le_card hsub
    omega
  obtain ⟨i, hi_inter, hi_notcorr⟩ := Finset.not_subset.mp hnotsub
  have hi₁ : i ∈ cert₁.selected := Finset.mem_inter.mp hi_inter |>.1
  have hi₂ : i ∈ cert₂.selected := Finset.mem_inter.mp hi_inter |>.2
  refine ⟨i, hi₁, hi₂, ?_⟩
  have hi_mem : i ∈ C.members := hinter_sub hi_inter
  simp only [Corruption.honest, Finset.mem_sdiff]
  exact ⟨hi_mem, hi_notcorr⟩

/-- **`no_equivocating_qcs`** (PROVED — the per-slot single-decision theorem). If NO honest member
signs two distinct/conflicting messages (`hHonestNoDouble`: the honest-member protocol discipline — an
honest validator votes once per slot), then two accepting QCs over the same committee for DISTINCT
messages at quorum threshold are IMPOSSIBLE. So at most ONE message gets a QC per slot: the BLS QC is a
sound consensus certificate. This is the headline distributed property, and it is FALSE without the
corruption bound (which is why it lives here, not in the single-cert reduction). -/
theorem no_equivocating_qcs
    {C : Committee PK} {m₁ m₂ : ℕ}
    (cert₁ : ThresholdCert C m₁) (cert₂ : ThresholdCert C m₂) (B : Corruption C)
    (hw : EqualWeight C)
    (hacc₁ : cert₁.accepts) (hsnark₁ : cert₁.SnarkContract)
    (hacc₂ : cert₂.accepts) (hsnark₂ : cert₂.SnarkContract)
    (hthr₁ : cert₁.threshold = quorumThreshold C.members.card)
    (hthr₂ : cert₂.threshold = quorumThreshold C.members.card)
    (hn : 1 ≤ C.members.card) (hbft : StrictBft C.members.card)
    (hbls₁ : ∀ i ∈ cert₁.selected, C.SignedBy i m₁)
    (hbls₂ : ∀ i ∈ cert₂.selected, C.SignedBy i m₂)
    (hHonestNoDouble : ∀ i ∈ B.honest, C.SignedBy i m₁ → C.SignedBy i m₂ → m₁ = m₂) :
    m₁ = m₂ := by
  obtain ⟨i, hi₁, hi₂, hi_honest⟩ :=
    two_quorums_share_honest_member cert₁ cert₂ B hw hacc₁ hsnark₁ hacc₂ hsnark₂ hthr₁ hthr₂ hn hbft
  exact hHonestNoDouble i hi_honest (hbls₁ i hi₁) (hbls₂ i hi₂)

/-! ## §5 — non-vacuity + the equal-weight federation differential (vs `federation/src/lib.rs`).

A concrete 4-member equal-weight committee (the `generate_test_committee(4, 3)` shape) with a corruption
set of size 1 (`faultBudget 4 = 1`). We witness every theorem FIRES, and a NEGATIVE corner: a sub-quorum
QC over the corrupt-only set cannot exist (it never reaches the threshold). -/

namespace Reference

open Dregg2.Crypto.BlsThreshold.Reference (fed4 passingCert passingCert_accepts passingCert_snark)

/-- Equal weight holds for the reference `fed4` (every weight is 1). -/
theorem fed4_equalWeight : EqualWeight fed4 := by
  intro i _; rfl

/-- `fed4` has 4 members. -/
theorem fed4_card : fed4.members.card = 4 := by decide

/-- `fed4`'s quorum threshold is 3 = `quorum_threshold(4)` (`lib.rs` golden vector). -/
theorem fed4_quorumThreshold : quorumThreshold fed4.members.card = 3 := by
  rw [fed4_card]; decide

/-- `fed4`'s fault budget is 1 = `fault_tolerance(4)` (`lib.rs` golden vector). -/
theorem fed4_faultBudget : faultBudget fed4.members.card = 1 := by
  rw [fed4_card]; decide

/-- A concrete corruption set: member 3 is Byzantine (`|{3}| = 1 ≤ faultBudget 4 = 1`). -/
def corruptOne : Corruption fed4 where
  corrupt := {3}
  sub := by decide
  bounded := by rw [fed4_card]; decide

/-- The reference passing cert's threshold IS the canonical quorum threshold for `fed4`. -/
theorem passingCert_threshold : passingCert.threshold = quorumThreshold fed4.members.card := by
  rw [fed4_quorumThreshold]; rfl

/-- **The honest-signer theorem FIRES on the reference**: the 3-of-4 QC, against corrupt member 3, has
an honest signer (in fact 0,1,2 are all honest signers; member 3 is not even in `selected`). -/
theorem ref_has_honest_signer :
    ∃ i, i ∈ passingCert.selected ∧ i ∈ corruptOne.honest :=
  quorum_has_honest_signer passingCert corruptOne fed4_equalWeight
    passingCert_accepts passingCert_snark passingCert_threshold (by rw [fed4_card]; decide)

/-- `fed4` is in the strict-BFT regime (`n = 4` is not a multiple of 3, so `n > 3f`). -/
theorem fed4_strictBft : StrictBft fed4.members.card := by
  rw [strictBft_iff, fed4_card]; decide

/-- **Two-QC honest overlap FIRES**: two copies of the 3-of-4 QC share an honest member. -/
theorem ref_two_qcs_share_honest :
    ∃ i, i ∈ passingCert.selected ∧ i ∈ passingCert.selected ∧ i ∈ corruptOne.honest :=
  two_quorums_share_honest_member passingCert passingCert corruptOne fed4_equalWeight
    passingCert_accepts passingCert_snark passingCert_accepts passingCert_snark
    passingCert_threshold passingCert_threshold (by rw [fed4_card]; decide) fed4_strictBft

/-- ANTI-VACUITY: the corrupt-only set `{3}` (size 1 = faultBudget) is STRICTLY smaller than any quorum
(size ≥ 3) — so a QC selecting only corrupt members is impossible. Witnesses the corruption bound is
load-bearing: `quorum_size_exceeds_faultBudget` would be violated. -/
theorem corrupt_cannot_reach_quorum :
    corruptOne.corrupt.card < quorumThreshold fed4.members.card := by
  rw [fed4_quorumThreshold]; decide

/-! ### §5b — differential `#guard`s pinning `faultBudget`/`quorumThreshold` to `federation/src/lib.rs`
(`fault_tolerance` `lib.rs:169`, `quorum_threshold` `lib.rs:155`; golden vectors from the Rust tests
`lib.rs:178-196`). A false `#guard` is a BUILD ERROR. -/

-- fault_tolerance golden vectors (lib.rs:188-195): f = ⌊n/3⌋.
#guard faultBudget 0 == 0
#guard faultBudget 1 == 0
#guard faultBudget 2 == 0
#guard faultBudget 3 == 1
#guard faultBudget 4 == 1
#guard faultBudget 7 == 2
#guard faultBudget 10 == 3
-- quorum_threshold golden vectors (lib.rs:179-184): q = n − ⌊n/3⌋.
#guard quorumThreshold 1 == 1
#guard quorumThreshold 2 == 2
#guard quorumThreshold 3 == 2
#guard quorumThreshold 4 == 3
#guard quorumThreshold 7 == 5
#guard quorumThreshold 10 == 7
-- quorum strictly exceeds the fault budget at each n ≥ 1 (the distributed safety margin).
#guard decide (faultBudget 4 < quorumThreshold 4)
#guard decide (faultBudget 7 < quorumThreshold 7)
#guard decide (faultBudget 10 < quorumThreshold 10)
-- the inclusion–exclusion honest-overlap margin 2q − n > f.
#guard decide (faultBudget 4 < 2 * quorumThreshold 4 - 4)
#guard decide (faultBudget 7 < 2 * quorumThreshold 7 - 7)
#guard decide (faultBudget 10 < 2 * quorumThreshold 10 - 10)

end Reference

/-! ## §6 — axiom-hygiene tripwires: the distributed proofs pin exactly the whitelist; the crypto is
in `Crypto.BlsThreshold`'s NAMED carriers (consumed via `SnarkContract`), never as Lean axioms here. -/

#assert_axioms quorum_gt_faultBudget
#assert_axioms strictBft_iff
#assert_axioms quorum_overlap_gt_faultBudget
#assert_axioms selectedWeight_eq_card
#assert_axioms quorum_size_exceeds_faultBudget
#assert_axioms quorum_has_honest_signer
#assert_axioms two_quorums_share_member
#assert_axioms two_quorums_share_honest_member
#assert_axioms no_equivocating_qcs
#assert_axioms Reference.ref_has_honest_signer
#assert_axioms Reference.ref_two_qcs_share_honest
#assert_axioms Reference.corrupt_cannot_reach_quorum

end Dregg2.Distributed.BlsQuorumCert
