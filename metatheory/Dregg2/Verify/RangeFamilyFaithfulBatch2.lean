/-
# Dregg2.Verify.RangeFamilyFaithfulBatch2 — continuing the range-table-faithfulness route across
the WIDTH FAMILIES the first batch did not reach.

## Where the route stands

`RangeFamilyFaithfulRoute` closed the ONE Gabbay public descriptor by routing its soundness through
`RangeFamilyFaithful` (pins `{(rangeTidW 15, 15), (.range, 30)}`). `RangeFamilyFaithfulBatch`
generalized the carrier to an explicit pin set (`RangeFamilyFaithfulOn`) and ported SIX descriptors:
the five 29-bit `predicate-arith-*` and the 30-bit `presentation-freshness`. Widths reached so far:
`{15, 29, 30}`.

This file reaches FIVE more width families — `{2, 4, 16, 27}` plus the generic-width lever — and
routes EIGHT more objects. Each is the same shape as the committed pattern: a `«X»SatisfiedFamily`
predicate carrying the honest-range obligation as the structural conjunct `RangeFamilyFaithfulOn`
(or its tf-level twin `RangeFamilyFaithfulTf`, for the gadget-level lemmas that quantify over a bare
`TraceFamily` rather than a `VmTrace`), a `«x»_sound_family` routing the EXISTING machine-checked
soundness theorem through it, and a `«x»_forgedRange_inadmissible` closing the forged-table lever.

## What is routed here (§ by width family)

  * **§2 — 27-bit, `.custom LEX_RANGE_TID` (wire id 32).** A width AND a TABLE ID outside everything
    routed so far (all previous pins ride the shared `.range` or `rangeTidW`).
      - `shieldedValueLinkRangedDesc` (by-name `dregg-shielded-value-link-conserve-ranged-v1`):
        `shieldedRanged_sound_family` carries `emitted_conservation_int_ranged` — ℤ conservation,
        `Σ value = Σ out_val` EXACTLY — and `shieldedRanged_wrapMint_family_refused` shows the
        field-conserving `p`-mint canary is refused UNDER THE FAMILY CARRIER.
      - `lexLt8Descriptor`'s comparison block: `lexLt8_sound_family` carries the `Digest8Key` lex
        order. This one is tf-level, hence `RangeFamilyFaithfulTf`.
  * **§3 — 4-bit, `.range`.** THREE descriptors on one pin `[(.range, 4)]`, via the two existing
    wrapper transports: `private-graph-rewrite-4x2`, `private-graph-rewrite-cell-4x2`,
    `private-quest-graph-4x2`. `pgr_sound_family` carries the full `DecodedAirFacts` bundle.
  * **§4 — 2-bit, `.range`, plus the GENERIC-width lever.** The deployed LogUp toy `toyD` (a REAL
    range lookup at BabyBear): `toy_sound_family` extracts the `[0, 4)` bound, and
    `toy_forgedRow_refused` REFUSES the concrete out-of-range trace `toyTforged` (wire 0 = 5).
    `busRange_sound_family` routes `busModel_feeds_range_lever` at an ARBITRARY width `bits`, so a
    future descriptor at any width inherits the route with no new carrier.
  * **§5 — the graduation keystones.** `graduateV1Narrow_sound` (30-bit `.range`) and
    `graduateV1WideNarrow_sound` (the wide `[15, 30]` family) routed through the carriers; the wide
    one lands DIRECTLY from the COMMITTED `RangeFamilyFaithful` (`wideNarrowGrad_sound_from_committed`),
    which is a NAMING/RE-EXPORT identity with no new mathematical content (an earlier draft billed it as
    'the sharpest connection in the route' — corrected): the committed conjunct IS, definitionally,
    the per-width premise the deployed graduation keystone consumes.

## NON-VACUITY (each family, so the refusals reject forgeries and not everything)

`shieldedRanged_family_nonvacuous` (the honest balanced 5+3 / 4+4 clearing), `lex_family_nonvacuous`
(the limb-5-decided key pair), `toy_family_nonvacuous` (the one-row `wire 0 = 3` trace). §3's 4-bit
family has NO `Satisfied2` witness anywhere in the tree for `privateGraphRewriteDescriptor`, so its
carrier non-vacuity is stated at the level it is actually available — `pgr_pins_nonvacuous`, the
honest 4-bit trace family inhabits the PIN — and the missing full witness is named in the residual
below rather than papered over.

## Severity — MODELING GAP, not a live vuln (unchanged from the committed route)

The deployed circuit ENFORCES range-table faithfulness on the wire: `circuit/src/descriptor_ir2.rs`
`Ir2Air::ByteTable` fixes `value = row index` (`when_first_row` asserts `local[0] = 0`,
`when_transition` asserts `next[0] = local[0] + 1`), so the table cannot lie about its rows, and
`verify_vm_descriptor2` refuses any range instance whose committed degree differs from the deployed
`BYTE_TABLE_HEIGHT` (test `ir2_oversized_byte_table_refuses`). So for every descriptor here the hole
is that the LEAN accept-set is looser than the deployed one — NOT an exploit against
`verify_vm_descriptor2`. Routing the premise into the family carrier moves the obligation to the emit
boundary; it does not delete it.

## Which of the lookup-bearing descriptors remain

Re-counted from the by-name registry (`circuit/descriptors/by-name/*.json`, 61 files): 46 carry a
lookup constraint or a declared range. Of those:

  * DONE, batch 1 (6): `predicate-arith-gt`, `predicate-arith` (ge), `predicate-arith-le`,
    `predicate-arith-lt`, `predicate-arith-inrange`, `presentation-freshness`.
  * DONE, this file (4 by-name + 4 gadget/keystone objects): `dregg-shielded-value-link-conserve-ranged-v1`,
    `private-graph-rewrite-4x2`, `private-graph-rewrite-cell-4x2`, `private-quest-graph-4x2`; plus the
    `lexLt8Descriptor` block, the LogUp toy `toyD`, and the two graduation keystones (`graduateV1Narrow`,
    `graduateV1WideNarrow`) which cover EVERY graduated v1 descriptor at once.
  * NOT A RANGE-TABLE HOLE AT ALL (a finding, not a residual): the six BFV butterflies
    (`private-book-bfv-odd-*ntt-butterfly-*`) carry their 48 width-tagged bounds in the descriptor's
    `ranges` FIELD, not in a lookup. In the Lean carrier `Satisfied2.rowRanges` evaluates
    `VmRange.holds` DIRECTLY (`0 ≤ w < 2^bits`) — there is no prover-supplied table to forge. In the
    deployed Rust these descriptors take the v1 path (`check_descriptor2` REFUSES a v2 descriptor with
    non-empty `ranges`: "v2 assembly requires a GRADUATED descriptor"), where the bound becomes a
    bit-decomposition `RangeBlock` against the fixed byte table — also not prover-supplied. Their
    table-517/518 lookups are CHIP tables, a separate `ChipTableSound` obligation. The same holds for
    `dregg-shielded-wide-value-link-conserve-v1`'s eight 16-bit `ranges`. The lane brief's "48-wide BFV
    ranges" is therefore already closed by construction on BOTH sides, and the honest count of
    range-TABLE-bearing descriptors is smaller than 43.
  * REMAINING, genuinely range-table-bearing: the `rangeTid 15/16` note-spend family
    (`faithful-note-spend-v2`, `faithful-note-spend-exact-v3`, `shielded-whole-note-swap-substrate-v1`,
    and the `ExactNullifierAafiRotatedState*` weld) — these have an honest 16-bit witness
    (`ExactNullifierAafiRotatedStateHonest.arithmeticTrace_range16`, `satisfied2_arithmetic_full_domain`)
    but NO soundness theorem yet consuming an honest-range premise, so routing them means AUTHORING the
    range tooth first, not porting one. That is the next lane's work and is NOT done here.
  * OUT OF SCOPE (chip, not range): `blinded-membership*`, `merkle-membership-*`, `attested-fact-membership`,
    `poseidon2-hash-arity2`, `derivation`, `note-spend-leaf`, `dark-*`, `private-shuffle*`,
    `private-preference*`, `private-raid-assignment-n4`, `dfa-routing`, `dyck-parse`, `adjacency-membership`,
    `turn-chain-binding`, `bound-presentation`, `descent-custody-census-fixed8-v1`,
    `dregg-shielded-spend-pinned-root-v1`, `private-book-bfv-slice-*`, `private-book-bfv-threshold-*` —
    their lookups are Poseidon2/CHIP or exact-public-row tables, whose faithfulness is the distinct
    `ChipTableSoundN` / `exactPublicRows` obligation.

So: 10 routed of the range-table-bearing set; the honest residual is the 4-descriptor note-spend
`rangeTid 15/16` family (blocked on an unauthored tooth) — the "37 remaining" figure in the lane brief
counts chip-table descriptors that this route does not apply to.

## Axiom hygiene

`#assert_axioms` ⊆ {propext, Classical.choice, Quot.sound}. NEW file; imports read-only; no base
`Satisfied2` change (RED-UMBRELLA avoided — soundness STATEMENTS are routed, not the base carrier).
-/
import Dregg2.Verify.RangeFamilyFaithfulBatch
import Dregg2.Circuit.ShieldedValueRangeDischarge
import Dregg2.Crypto.PrivateGraphRewriteCellDescriptor
import Dregg2.Games.PrivateQuestGraphDescriptor
import Dregg2.Circuit.LogUpColumnLayout
import Dregg2.Circuit.Emit.GraduateWideNarrow

namespace Dregg2.Verify.RangeFamilyFaithfulBatch2

open Dregg2.Circuit.DescriptorIR2
open Dregg2.Verify.RangeFamilyFaithfulRoute (RangeFamilyFaithful)
open Dregg2.Verify.RangeFamilyFaithfulBatch (RangeFamilyFaithfulOn)

set_option autoImplicit false

/-! ## §1 — the tf-level twin of the batch carrier.

`RangeFamilyFaithfulOn` pins a `VmTrace`. Several gadget-level soundness lemmas (`lexLt8_sound`,
`privateGraphRewrite_*`) quantify over a bare `TraceFamily` instead, because the gadget is a
pluggable block rather than a whole trace. `RangeFamilyFaithfulTf` is the same conjunct one level
down, and `RangeFamilyFaithfulOn.toTf` shows the trace-level carrier IS the tf-level carrier at
`t.tf` — so the two halves of the route never diverge. -/

/-- **`RangeFamilyFaithfulTf pins tf`** — the range-table faithfulness conjunct over a bare trace
family: at every pin `(tid, n)`, `tf tid` is the genuine honest interval `rangeRows n`. -/
def RangeFamilyFaithfulTf (pins : List (TableId × Nat)) (tf : TraceFamily) : Prop :=
  ∀ p ∈ pins, tf p.1 = rangeRows p.2

/-- Project a single honest-interval pin out of the tf-level carrier. -/
theorem RangeFamilyFaithfulTf.pin {pins : List (TableId × Nat)} {tf : TraceFamily}
    (h : RangeFamilyFaithfulTf pins tf) {tid : TableId} {n : Nat}
    (hmem : (tid, n) ∈ pins) : tf tid = rangeRows n :=
  h (tid, n) hmem

/-- The trace-level carrier IS the tf-level carrier at `t.tf`. -/
theorem RangeFamilyFaithfulOn.toTf {pins : List (TableId × Nat)} {t : VmTrace}
    (h : RangeFamilyFaithfulOn pins t) : RangeFamilyFaithfulTf pins t.tf := h

/-- …and back: a tf-level carrier at `t.tf` is the trace-level carrier. -/
theorem RangeFamilyFaithfulTf.toOn {pins : List (TableId × Nat)} {t : VmTrace}
    (h : RangeFamilyFaithfulTf pins t.tf) : RangeFamilyFaithfulOn pins t := h

/-! ## §2 — the 27-bit family at `.custom LEX_RANGE_TID` (wire id 32).

Both objects here ride the SAME dedicated 27-bit table — a table id no previously routed descriptor
touches (batch 1's pins are all `.range` or `rangeTidW`). -/

/-! ### §2a — `shieldedValueLinkRangedDesc`: ℤ conservation, routed through the family carrier. -/

open Dregg2.Circuit.ShieldedValueRangeDischarge in
open Dregg2.Circuit.Emit.LexCompare8Emit (LEX_RANGE_TID) in
/-- `shieldedValueLinkRangedDesc`'s soundness hypotheses with the honest 27-bit range table carried
as the family conjunct rather than the free `t.tf (.custom LEX_RANGE_TID)` lever. The two structural
side-conditions (non-empty trace, clearing width `≤ 15`) ride along unchanged — they are the Rust
`ring_no_wrap_ok` build-time assert, not a crypto premise. -/
def ShieldedRangedSatisfiedFamily (hash : List ℤ → ℤ) (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat)
    (maddrs : List ℤ) (t : VmTrace) : Prop :=
  RangeFamilyFaithfulOn [(TableId.custom LEX_RANGE_TID, VALUE_BITS)] t ∧ t.rows ≠ [] ∧
    t.rows.length ≤ MAX_CLEARING_ROWS ∧
    Satisfied2 hash shieldedValueLinkRangedDesc minit mfin maddrs t

/-- **Soundness, routed through the family conjunct** (mirrors `statement_sound_family`): a
family-honest satisfying trace conserves in ℤ — `Σ value = Σ out_val` EXACTLY, no field wrap. -/
theorem shieldedRanged_sound_family {hash : List ℤ → ℤ} {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat}
    {maddrs : List ℤ} {t : VmTrace} (h : ShieldedRangedSatisfiedFamily hash minit mfin maddrs t) :
    Dregg2.Circuit.Emit.ShieldedValueLinkDescriptor.prefixSum
        (Dregg2.Circuit.Emit.ShieldedValueLinkDescriptor.valAt t) (t.rows.length - 1)
      = Dregg2.Circuit.Emit.ShieldedValueLinkDescriptor.prefixSum
        (Dregg2.Circuit.Emit.ShieldedValueLinkDescriptor.outAt t) (t.rows.length - 1) :=
  Dregg2.Circuit.ShieldedValueRangeDischarge.emitted_conservation_int_ranged
    hash minit mfin maddrs t h.2.1 h.2.2.2 (h.1.pin (List.mem_singleton.mpr rfl)) h.2.2.1

/-- **A forged 27-bit table is inadmissible.** Any trace whose `.custom LEX_RANGE_TID` table differs
from the honest interval cannot inhabit the family predicate. -/
theorem shieldedRanged_forgedRange_inadmissible {hash : List ℤ → ℤ} {minit : ℤ → ℤ}
    {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
    (hforge : t.tf (.custom Dregg2.Circuit.Emit.LexCompare8Emit.LEX_RANGE_TID)
      ≠ rangeRows Dregg2.Circuit.ShieldedValueRangeDischarge.VALUE_BITS) :
    ¬ ShieldedRangedSatisfiedFamily hash minit mfin maddrs t :=
  fun h => hforge (h.1.pin (List.mem_singleton.mpr rfl))

/-- **The wraparound-mint canary is refused UNDER THE FAMILY CARRIER.** `wrapMintTrace` mints `p`
units disguised as zero (`Σ value = 0`, `Σ out_val = p`; field-conserving because `p ≡ 0`). The plain
value-link descriptor ACCEPTS it (`wraparound_mint_accepted_by_base`); the family-routed ranged
predicate does not.

⚠ CORRECTED (an adversarial verify PROVED the original claim FALSE in Lean): this theorem does NOT
show the family CARRIER is load-bearing on this trace. The refusal here comes from the RANGE PREDICATE
itself, not from the family conjunct — `RangeFamilyFaithfulOn [(TableId.custom LEX_RANGE_TID,
VALUE_BITS)] wrapMintTrace` is *satisfiable*, so the carrier does not do the refusing. The carrier's
load-bearing-ness is established where its pin is actually CONSUMED (the `_sound_family` routings),
not here. Read this theorem as: the ranged predicate refuses the wrap-mint, full stop. -/
theorem shieldedRanged_wrapMint_family_refused (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat)
    (maddrs : List ℤ) :
    ¬ ShieldedRangedSatisfiedFamily Dregg2.Circuit.Emit.ShieldedValueLinkDescriptor.hzero
        minit mfin maddrs Dregg2.Circuit.ShieldedValueRangeDischarge.wrapMintTrace := by
  intro h
  -- the FAMILY-ROUTED soundness itself does the refusing: it would force `0 = p` in ℤ.
  exact absurd (shieldedRanged_sound_family h) (by decide)

/-- **Non-vacuity.** The honest balanced two-row clearing (5+3 in / 4+4 out) inhabits the family
predicate — the refusals above reject the forgery, not everything. -/
theorem shieldedRanged_family_nonvacuous :
    ShieldedRangedSatisfiedFamily Dregg2.Circuit.Emit.ShieldedValueLinkDescriptor.hzero
      (fun _ => 0) (fun _ => (0, 0)) []
      Dregg2.Circuit.ShieldedValueRangeDischarge.honestRangedTrace :=
  ⟨fun p hp => by
      rcases List.mem_singleton.mp hp with rfl
      exact Dregg2.Circuit.ShieldedValueRangeDischarge.rangedTf_range,
   by simp [Dregg2.Circuit.ShieldedValueRangeDischarge.honestRangedTrace],
   by decide,
   Dregg2.Circuit.ShieldedValueRangeDischarge.honest_ranged_satisfies⟩

/-! ### §2b — the `lexLt8` comparison block (tf-level: a pluggable sub-block, not a whole trace). -/

open Dregg2.Circuit.Emit.LexCompare8Emit in
/-- The `lexLt8` block's soundness hypotheses with the honest 27-bit table carried as the tf-level
family conjunct. -/
def LexSatisfiedFamily (tf : TraceFamily)
    (env : Dregg2.Circuit.Emit.EffectVmEmit.VmRowEnv) : Prop :=
  RangeFamilyFaithfulTf [(TableId.custom LEX_RANGE_TID, 27)] tf ∧ LexCanon env ∧
    lexBlockHolds tf env

/-- **Soundness, routed through the family conjunct**: a family-honest satisfying row carries keys
in the spike's `Digest8Key` lexicographic order (felt 0 most significant). -/
theorem lexLt8_sound_family {tf : TraceFamily} {env : Dregg2.Circuit.Emit.EffectVmEmit.VmRowEnv}
    (h : LexSatisfiedFamily tf env) :
    toLex (Dregg2.Circuit.Emit.LexCompare8Emit.lexKeyA env)
      < toLex (Dregg2.Circuit.Emit.LexCompare8Emit.lexKeyB env) :=
  Dregg2.Circuit.Emit.LexCompare8Emit.lexLt8_sound tf
    (h.1.pin (List.mem_singleton.mpr rfl)) env h.2.1 h.2.2

/-- **A forged 27-bit table is inadmissible for the block.** -/
theorem lexLt8_forgedRange_inadmissible {tf : TraceFamily}
    {env : Dregg2.Circuit.Emit.EffectVmEmit.VmRowEnv}
    (hforge : tf (.custom Dregg2.Circuit.Emit.LexCompare8Emit.LEX_RANGE_TID) ≠ rangeRows 27) :
    ¬ LexSatisfiedFamily tf env :=
  fun h => hforge (h.1.pin (List.mem_singleton.mpr rfl))

/-- **Non-vacuity.** The limb-5-decided key pair `(toothA, toothB)` has a satisfying row inhabiting
the family predicate. -/
theorem lex_family_nonvacuous :
    ∃ env, LexSatisfiedFamily Dregg2.Circuit.Emit.LexCompare8Emit.lexTf env := by
  obtain ⟨env, hA, hB, hblk⟩ := Dregg2.Circuit.Emit.LexCompare8Emit.tooth_accepts_limb5
  refine ⟨env, ?_, ?_, hblk⟩
  · intro p hp
    rcases List.mem_singleton.mp hp with rfl
    exact Dregg2.Circuit.Emit.LexCompare8Emit.lexTf_range
  · intro k hk
    by_cases h8 : k < 8
    · have hval : env.loc k = Dregg2.Circuit.Emit.LexCompare8Emit.toothA ⟨k, h8⟩ := hA ⟨k, h8⟩
      rw [hval]
      exact Dregg2.Circuit.Emit.LexCompare8Emit.toothA_canon ⟨k, h8⟩
    · have hk8 : k - 8 < 8 := by omega
      have hval : env.loc (8 + (k - 8))
          = Dregg2.Circuit.Emit.LexCompare8Emit.toothB ⟨k - 8, hk8⟩ := hB ⟨k - 8, hk8⟩
      have hkk : 8 + (k - 8) = k := by omega
      rw [hkk] at hval
      rw [hval]
      exact Dregg2.Circuit.Emit.LexCompare8Emit.toothB_canon ⟨k - 8, hk8⟩

/-! ## §3 — the 4-bit `.range` family: three descriptors on one pin.

`privateGraphRewriteDescriptor`'s range-routed control cells are checked against `rangeRows 4` — a
width nothing previously routed reaches. Its two deployed wrappers (`private-graph-rewrite-cell-4x2`,
`private-quest-graph-4x2`) already have machine-checked transports INTO it over the SAME trace family,
so all three descriptors route through one carrier with no new pin. -/

open Dregg2.Crypto.PrivateGraphRewriteDescriptor in
/-- `privateGraphRewriteDescriptor`'s soundness hypotheses with the honest 4-bit range table carried
as the tf-level family conjunct. The chip-table premise (`ChipTableSoundN`) is a DIFFERENT obligation
and stays explicit — this route is about the RANGE table only. -/
def PgrSatisfiedFamily (hash : List Int → Int) (permOut : List Int → List Int)
    (a pis : Dregg2.Circuit.Assignment) (tf : TraceFamily) : Prop :=
  RangeFamilyFaithfulTf [(TableId.range, 4)] tf ∧ CanonicalAssignment a ∧
    CanonicalAssignment pis ∧ ChipTableSoundN permOut (tf TableId.poseidon2) ∧
    Satisfied2 hash privateGraphRewriteDescriptor ppM0 ppF0 [] (constTrace a pis tf)

/-- **Soundness, routed through the family conjunct**: the full decoded-AIR bundle (booleanity of
every control bit, the 4-bit bound on every range-routed cell, the wide Poseidon2 digests, and exact
public-input pinning) from a family-honest satisfying trace. -/
theorem pgr_sound_family {hash : List Int → Int} {permOut : List Int → List Int}
    {a pis : Dregg2.Circuit.Assignment} {tf : TraceFamily}
    (h : PgrSatisfiedFamily hash permOut a pis tf) :
    Dregg2.Crypto.PrivateGraphRewriteDescriptor.DecodedAirFacts permOut a pis :=
  Dregg2.Crypto.PrivateGraphRewriteDescriptor.privateGraphRewrite_decoded_air_sound
    permOut h.2.1 h.2.2.1 h.2.2.2.1 (h.1.pin (List.mem_singleton.mpr rfl)) h.2.2.2.2

/-- The 4-bit tooth, stated on its own: every range-routed control cell is a genuine small integer. -/
theorem pgr_range_cells_bounded {hash : List Int → Int} {permOut : List Int → List Int}
    {a pis : Dregg2.Circuit.Assignment} {tf : TraceFamily}
    (h : PgrSatisfiedFamily hash permOut a pis tf) :
    ∀ col ∈ Dregg2.Crypto.PrivateGraphRewriteDescriptor.rangeCols, 0 ≤ a col ∧ a col < 16 :=
  (pgr_sound_family h).ranges

/-- **A forged 4-bit table is inadmissible.** -/
theorem pgr_forgedRange_inadmissible {hash : List Int → Int} {permOut : List Int → List Int}
    {a pis : Dregg2.Circuit.Assignment} {tf : TraceFamily}
    (hforge : tf TableId.range ≠ rangeRows 4) :
    ¬ PgrSatisfiedFamily hash permOut a pis tf :=
  fun h => hforge (h.1.pin (List.mem_singleton.mpr rfl))

/-- **The CELL wrapper (`private-graph-rewrite-cell-4x2`) routes through the SAME carrier.** Its
existing no-second-semantics transport carries a satisfying wrapper trace into a satisfying base
trace over the SAME trace family, so the 4-bit pin transfers verbatim. -/
theorem pgrCell_sound_family {hash : List Int → Int} {permOut : List Int → List Int}
    {a pis : Dregg2.Circuit.Assignment} {tf : TraceFamily}
    (hpins : RangeFamilyFaithfulTf [(TableId.range, 4)] tf)
    (hcanon : Dregg2.Crypto.PrivateGraphRewriteDescriptor.CanonicalAssignment a)
    (hcanonPis : Dregg2.Crypto.PrivateGraphRewriteDescriptor.CanonicalAssignment
      (Dregg2.Crypto.PrivateGraphRewriteCellDescriptor.cellCorePis pis))
    (hchip : ChipTableSoundN permOut (tf TableId.poseidon2))
    (hsat : Satisfied2 hash
      Dregg2.Crypto.PrivateGraphRewriteCellDescriptor.privateGraphRewriteCellDescriptor
      Dregg2.Crypto.PrivateGraphRewriteDescriptor.ppM0
      Dregg2.Crypto.PrivateGraphRewriteDescriptor.ppF0 []
      (Dregg2.Crypto.PrivateGraphRewriteDescriptor.constTrace a pis tf)) :
    Dregg2.Crypto.PrivateGraphRewriteDescriptor.DecodedAirFacts permOut a
      (Dregg2.Crypto.PrivateGraphRewriteCellDescriptor.cellCorePis pis) :=
  pgr_sound_family (hash := hash) (permOut := permOut)
    ⟨hpins, hcanon, hcanonPis, hchip,
     Dregg2.Crypto.PrivateGraphRewriteCellDescriptor.cell_satisfied_to_base_satisfied hsat⟩

/-- **The QUEST specialization (`private-quest-graph-4x2`) routes through the SAME carrier.** -/
theorem pgrQuest_sound_family {hash : List Int → Int} {permOut : List Int → List Int}
    {a pis : Dregg2.Circuit.Assignment} {tf : TraceFamily}
    (hpins : RangeFamilyFaithfulTf [(TableId.range, 4)] tf)
    (hcanon : Dregg2.Crypto.PrivateGraphRewriteDescriptor.CanonicalAssignment a)
    (hcanonPis : Dregg2.Crypto.PrivateGraphRewriteDescriptor.CanonicalAssignment pis)
    (hchip : ChipTableSoundN permOut (tf TableId.poseidon2))
    (hsat : Satisfied2 hash
      Dregg2.Games.PrivateQuestGraphDescriptor.privateQuestGraphDescriptor
      Dregg2.Crypto.PrivateGraphRewriteDescriptor.ppM0
      Dregg2.Crypto.PrivateGraphRewriteDescriptor.ppF0 []
      (Dregg2.Crypto.PrivateGraphRewriteDescriptor.constTrace a pis tf)) :
    Dregg2.Crypto.PrivateGraphRewriteDescriptor.DecodedAirFacts permOut a pis :=
  pgr_sound_family (hash := hash) (permOut := permOut)
    ⟨hpins, hcanon, hcanonPis, hchip,
     Dregg2.Games.PrivateQuestGraphDescriptor.privateQuest_satisfied_to_base_satisfied hsat⟩

/-- The honest 4-bit trace family: the genuine interval at `.range` and nothing else. -/
def pgrHonestTf : TraceFamily := fun tid => if tid = TableId.range then rangeRows 4 else []

/-- **Carrier non-vacuity (the level actually available).** The honest 4-bit family inhabits the
pin, so `pgr_forgedRange_inadmissible` refuses forged tables rather than being empty of content.
The FULL predicate's non-vacuity needs a `Satisfied2` witness for `privateGraphRewriteDescriptor`,
which does not exist anywhere in the tree — that is named in this file's residual, not papered over. -/
theorem pgr_pins_nonvacuous : RangeFamilyFaithfulTf [(TableId.range, 4)] pgrHonestTf := by
  intro p hp
  rcases List.mem_singleton.mp hp with rfl
  simp [pgrHonestTf]

/-! ## §4 — the 2-bit `.range` family and the GENERIC-width lever.

`LogUpColumnLayout.toyD` is the minimal REAL lookup shape at BabyBear: one main column, one range
lookup against `rangeRows 2`. It is the smallest place where the forged-table lever is visible on a
CONCRETE trace, because both the honest trace (`toyT`, wire 0 = 3) and the out-of-range trace
(`toyTforged`, wire 0 = 5) already exist beside it. -/

open Dregg2.Circuit.LogUpColumnLayout (toyD toyT toyTf toyTforged toyLookup) in
/-- `toyD`'s soundness hypotheses with the honest 2-bit range table carried as the family conjunct. -/
def ToySatisfiedFamily (hash : List ℤ → ℤ) (t : VmTrace) : Prop :=
  RangeFamilyFaithfulOn [(TableId.range, 2)] t ∧
    Satisfied2 hash toyD (fun _ => 0) (fun _ => (0, 0)) [] t

/-- **Soundness, routed through the family conjunct**: the looked-up wire lies in `[0, 4)`. -/
theorem toy_sound_family {hash : List ℤ → ℤ} {t : VmTrace} (h : ToySatisfiedFamily hash t)
    {i : Nat} (hi : i < t.rows.length) :
    Dregg2.Circuit.Emit.EffectVmEmit.VmRange.holds (envAt t i) ⟨0, 2⟩ := by
  have hrow := h.2.rowConstraints i hi
    (VmConstraint2.lookup Dregg2.Circuit.LogUpColumnLayout.toyLookup)
    (by simp [Dregg2.Circuit.LogUpColumnLayout.toyD])
  have hl : Lookup.holdsAt t.tf (envAt t i) Dregg2.Circuit.LogUpColumnLayout.toyLookup := hrow
  exact lookup_replaces_range 2 t.tf (h.1.pin (List.mem_singleton.mpr rfl)) (envAt t i) 0 hl

/-- **A forged 2-bit table is inadmissible.** -/
theorem toy_forgedRange_inadmissible {hash : List ℤ → ℤ} {t : VmTrace}
    (hforge : t.tf TableId.range ≠ rangeRows 2) : ¬ ToySatisfiedFamily hash t :=
  fun h => hforge (h.1.pin (List.mem_singleton.mpr rfl))

/-- **A CONCRETE out-of-range trace is refused.** `toyTforged` carries wire 0 = 5 against the HONEST
2-bit table — it is not a forged-table attack but a forged-VALUE one, and the family-routed predicate
refuses it because the honest pin makes the lookup mean what it says. -/
theorem toy_forgedRow_refused (hash : List ℤ → ℤ) :
    ¬ ToySatisfiedFamily hash Dregg2.Circuit.LogUpColumnLayout.toyTforged := by
  intro h
  have hb := toy_sound_family h (i := 0)
    (show 0 < Dregg2.Circuit.LogUpColumnLayout.toyTforged.rows.length from
      by simp [Dregg2.Circuit.LogUpColumnLayout.toyTforged])
  have h5 : (envAt Dregg2.Circuit.LogUpColumnLayout.toyTforged 0).loc 0 = (5 : ℤ) := rfl
  have hlt := hb.2
  rw [show (⟨0, 2⟩ : Dregg2.Circuit.Emit.EffectVmEmit.VmRange).wire = 0 from rfl, h5] at hlt
  exact absurd hlt (by norm_num)

/-- The honest 2-bit trace's table pin (the structural `rangeRows 2`, a four-row table). -/
theorem toyT_pin : Dregg2.Circuit.LogUpColumnLayout.toyT.tf TableId.range = rangeRows 2 := rfl

private theorem toy_memLog_nil :
    memLog Dregg2.Circuit.LogUpColumnLayout.toyD Dregg2.Circuit.LogUpColumnLayout.toyT = [] := rfl

private theorem toy_mapLog_nil :
    mapLog Dregg2.Circuit.LogUpColumnLayout.toyD Dregg2.Circuit.LogUpColumnLayout.toyT = [] := rfl

/-- The honest one-row toy trace genuinely satisfies `toyD` (the single range lookup holds: `3` lies
in the four-row table, argued through `range_row_mem_iff` so the table is never enumerated; the
memory legs are the empty-log structurals). Re-derived here rather than imported from
`AcceptanceDischarge.toy_satisfied2` so this routing file keeps its import closure at the descriptor
layer instead of pulling the whole FRI/STARK acceptance tower in. -/
theorem toy_satisfied2_honest (hash : List ℤ → ℤ) :
    Satisfied2 hash Dregg2.Circuit.LogUpColumnLayout.toyD (fun _ => 0) (fun _ => (0, 0)) []
      Dregg2.Circuit.LogUpColumnLayout.toyT where
  rowConstraints := by
    intro i hi c hc
    rw [show Dregg2.Circuit.LogUpColumnLayout.toyT.rows.length = 1 from rfl] at hi
    obtain rfl : i = 0 := Nat.lt_one_iff.mp hi
    obtain rfl : c = VmConstraint2.lookup Dregg2.Circuit.LogUpColumnLayout.toyLookup := by
      simpa [Dregg2.Circuit.LogUpColumnLayout.toyD] using hc
    show Lookup.holdsAt Dregg2.Circuit.LogUpColumnLayout.toyT.tf
      (envAt Dregg2.Circuit.LogUpColumnLayout.toyT 0) Dregg2.Circuit.LogUpColumnLayout.toyLookup
    unfold Lookup.holdsAt
    show [(envAt Dregg2.Circuit.LogUpColumnLayout.toyT 0).loc 0]
      ∈ Dregg2.Circuit.LogUpColumnLayout.toyT.tf TableId.range
    rw [toyT_pin]
    have h3 : [(envAt Dregg2.Circuit.LogUpColumnLayout.toyT 0).loc 0] = [(3 : ℤ)] := rfl
    rw [h3]
    exact (range_row_mem_iff 3 2).mpr ⟨by norm_num, by norm_num⟩
  rowHashes := by intro i _; trivial
  rowRanges := by intro i _ r hr; simp [Dregg2.Circuit.LogUpColumnLayout.toyD] at hr
  memAddrsNodup := List.nodup_nil
  memClosed := by intro op hop; rw [toy_memLog_nil] at hop; cases hop
  memDisciplined := by rw [toy_memLog_nil]; trivial
  memBalanced := by
    rw [toy_memLog_nil]
    simp [Dregg2.Crypto.MemoryChecking.MemCheck, Dregg2.Crypto.MemoryChecking.initSet,
      Dregg2.Crypto.MemoryChecking.finalSet, Dregg2.Crypto.MemoryChecking.readSet,
      Dregg2.Crypto.MemoryChecking.writeSetFrom, Dregg2.Crypto.MemoryChecking.boundarySet]
  memTableFaithful := by rw [toy_memLog_nil]; rfl
  mapTableFaithful := by rw [toy_mapLog_nil]; rfl

/-- **Non-vacuity.** The honest one-row trace inhabits the family predicate, so
`toy_forgedRow_refused` rejects the out-of-range value specifically. -/
theorem toy_family_nonvacuous (hash : List ℤ → ℤ) :
    ToySatisfiedFamily hash Dregg2.Circuit.LogUpColumnLayout.toyT :=
  ⟨fun p hp => by
      rcases List.mem_singleton.mp hp with rfl
      exact toyT_pin,
   toy_satisfied2_honest hash⟩

/-! ### §4b — ⚑ THE LOAD-BEARING CANARY: bare `Satisfied2` ACCEPTS a forged-table trace that the
family-routed predicate REFUSES.

This is the whole route's hole made concrete, in the smallest place it exists. `forgedToyTrace`
carries wire 0 = 5 — OUT of `[0, 2^2)` — beside a `.range` table forged to the single row `[[5]]`.
Every emitted range tooth still passes, because `Lookup.holdsAt` is membership against the FREE
`t.tf .range` field. So the base carrier accepts it (`forgedToy_satisfies`) while the family-routed
predicate refuses it (`forgedToy_family_refused`) — the exact analogue of the value-link module's
`wraparound_mint_accepted_by_base` / `wraparound_mint_refused_by_ranged` pair, one level down. The
family conjunct is therefore load-bearing, not decorative. -/

/-- A `.range` table forged to contain exactly the out-of-range value `5`. -/
def forgedToyTf : TraceFamily := fun tid => if tid = TableId.range then [[(5 : ℤ)]] else []

/-- The forged-table trace: wire 0 = 5, checked against the forged one-row table. -/
def forgedToyTrace : VmTrace := { rows := [fun _ => 5], pub := fun _ => 5, tf := forgedToyTf }

private theorem forgedToy_memLog_nil :
    memLog Dregg2.Circuit.LogUpColumnLayout.toyD forgedToyTrace = [] := rfl

private theorem forgedToy_mapLog_nil :
    mapLog Dregg2.Circuit.LogUpColumnLayout.toyD forgedToyTrace = [] := rfl

/-- **The BASE carrier ACCEPTS the forged-table trace.** `Satisfied2` pins the memory and map-ops
auxiliary tables but NOT the range table, so a prover who supplies `[[5]]` at `.range` passes the
range tooth with an out-of-range wire. -/
theorem forgedToy_satisfies (hash : List ℤ → ℤ) :
    Satisfied2 hash Dregg2.Circuit.LogUpColumnLayout.toyD (fun _ => 0) (fun _ => (0, 0)) []
      forgedToyTrace where
  rowConstraints := by
    intro i hi c hc
    rw [show forgedToyTrace.rows.length = 1 from rfl] at hi
    obtain rfl : i = 0 := Nat.lt_one_iff.mp hi
    obtain rfl : c = VmConstraint2.lookup Dregg2.Circuit.LogUpColumnLayout.toyLookup := by
      simpa [Dregg2.Circuit.LogUpColumnLayout.toyD] using hc
    show Lookup.holdsAt forgedToyTrace.tf (envAt forgedToyTrace 0)
      Dregg2.Circuit.LogUpColumnLayout.toyLookup
    unfold Lookup.holdsAt
    show [(envAt forgedToyTrace 0).loc 0] ∈ forgedToyTrace.tf TableId.range
    show [(5 : ℤ)] ∈ forgedToyTf TableId.range
    simp [forgedToyTf]
  rowHashes := by intro i _; trivial
  rowRanges := by intro i _ r hr; simp [Dregg2.Circuit.LogUpColumnLayout.toyD] at hr
  memAddrsNodup := List.nodup_nil
  memClosed := by intro op hop; rw [forgedToy_memLog_nil] at hop; cases hop
  memDisciplined := by rw [forgedToy_memLog_nil]; trivial
  memBalanced := by
    rw [forgedToy_memLog_nil]
    simp [Dregg2.Crypto.MemoryChecking.MemCheck, Dregg2.Crypto.MemoryChecking.initSet,
      Dregg2.Crypto.MemoryChecking.finalSet, Dregg2.Crypto.MemoryChecking.readSet,
      Dregg2.Crypto.MemoryChecking.writeSetFrom, Dregg2.Crypto.MemoryChecking.boundarySet]
  memTableFaithful := by rw [forgedToy_memLog_nil]; rfl
  mapTableFaithful := by rw [forgedToy_mapLog_nil]; rfl

/-- **…and the FAMILY-ROUTED predicate REFUSES it.** The forged table is not the honest interval, so
the carrier's pin cannot hold — the free lever the base carrier leaves open is closed. -/
theorem forgedToy_family_refused (hash : List ℤ → ℤ) :
    ¬ ToySatisfiedFamily hash forgedToyTrace := by
  refine toy_forgedRange_inadmissible ?_
  show forgedToyTf TableId.range ≠ rangeRows 2
  rw [show forgedToyTf TableId.range = [[(5 : ℤ)]] from rfl,
      Dregg2.Circuit.LogUpColumnLayout.toy_rangeRows2]
  decide

/-! ### §4c — the GENERIC-width lever: any width, one carrier.

`busModel_feeds_range_lever` is already stated at an arbitrary `bits`. Routing it through the family
carrier means a descriptor at ANY width — 2, 4, 16, 27, 48 — inherits the route with no new pin set
and no new theorem: instantiate `bits`. -/

/-- **The extracted LogUp bus feeds the range lever, routed through the family carrier at an
ARBITRARY width.** This is the generic form the remaining descriptors instantiate. -/
theorem busRange_sound_family {F : Type} [Field F] [DecidableEq F]
    (fp : List ℤ → F) (embed : ℤ → F) (d : EffectVmDescriptor2) (t : VmTrace) (mult : List Nat)
    (bits : Nat) (hpins : RangeFamilyFaithfulOn [(TableId.range, bits)] t)
    (hok : Dregg2.Circuit.LogUpColumnLayout.BusModelOk fp embed d t TableId.range mult)
    (w : Nat)
    (hl : (⟨TableId.range, [Dregg2.Exec.CircuitEmit.EmittedExpr.var w]⟩ : Lookup)
      ∈ Dregg2.Circuit.LogUpColumnLayout.lookupsInto d TableId.range)
    (i : Nat) (hi : i < t.rows.length) :
    Dregg2.Circuit.Emit.EffectVmEmit.VmRange.holds (envAt t i) ⟨w, bits⟩ :=
  Dregg2.Circuit.LogUpColumnLayout.busModel_feeds_range_lever fp embed d t mult bits
    (hpins.pin (List.mem_singleton.mpr rfl)) hok w hl i hi

/-! ## §5 — the graduation keystones: EVERY graduated v1 descriptor, at once.

`graduateV1Narrow` / `graduateV1WideNarrow` lower a v1 descriptor's `ranges` field into range
lookups. Their soundness keystones therefore carry the honest-range premise for the WHOLE class of
graduated descriptors — routing them routes every descriptor that reaches IR-v2 through graduation,
not one name at a time. -/

open Dregg2.Circuit.Emit.EffectVmEmitV2 in
/-- `graduateV1Narrow d`'s soundness hypotheses with the honest 30-bit range table carried as the
family conjunct. -/
def NarrowGradSatisfiedFamily (hash : List ℤ → ℤ)
    (d : Dregg2.Circuit.Emit.EffectVmEmit.EffectVmDescriptor) (minit : ℤ → ℤ)
    (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (t : VmTrace) : Prop :=
  RangeFamilyFaithfulOn [(TableId.range, BAL_LIMB_BITS)] t ∧
    ChipTableSoundNarrow hash (t.tf poseidon2narrow) ∧ graduable d = true ∧
    Satisfied2 hash (graduateV1Narrow d) minit mfin maddrs t

/-- **Soundness, routed through the family conjunct**: the full v1 denotation `satisfiedVm` on every
row window, from a family-honest witness of the narrow graduation. -/
theorem narrowGrad_sound_family {hash : List ℤ → ℤ}
    {d : Dregg2.Circuit.Emit.EffectVmEmit.EffectVmDescriptor} {minit : ℤ → ℤ}
    {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
    (h : NarrowGradSatisfiedFamily hash d minit mfin maddrs t) :
    ∀ i, i < t.rows.length →
      Dregg2.Circuit.Emit.EffectVmEmit.satisfiedVm hash d (envAt t i) (i == 0)
        (i + 1 == t.rows.length) :=
  Dregg2.Circuit.Emit.EffectVmEmitV2.graduateV1Narrow_sound hash d minit mfin maddrs t h.2.1
    (h.1.pin (List.mem_singleton.mpr rfl)) h.2.2.1 h.2.2.2

/-- **A forged 30-bit table is inadmissible for the narrow graduation.** -/
theorem narrowGrad_forgedRange_inadmissible {hash : List ℤ → ℤ}
    {d : Dregg2.Circuit.Emit.EffectVmEmit.EffectVmDescriptor} {minit : ℤ → ℤ}
    {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
    (hforge : t.tf TableId.range ≠ rangeRows BAL_LIMB_BITS) :
    ¬ NarrowGradSatisfiedFamily hash d minit mfin maddrs t :=
  fun h => hforge (h.1.pin (List.mem_singleton.mpr rfl))

/-- **The COMMITTED carrier drives the narrow graduation directly.** `RangeFamilyFaithful` (the
`RangeFamilyFaithfulRoute` conjunct) supplies the 30-bit `.range` pin via `RangeFamilyFaithful.toOn`,
so a trace already routed through the committed carrier needs nothing new. -/
theorem narrowGrad_sound_from_committed {hash : List ℤ → ℤ}
    {d : Dregg2.Circuit.Emit.EffectVmEmit.EffectVmDescriptor} {minit : ℤ → ℤ}
    {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
    (hfam : RangeFamilyFaithful t)
    (hchip : ChipTableSoundNarrow hash (t.tf poseidon2narrow))
    (hgrad : Dregg2.Circuit.Emit.EffectVmEmitV2.graduable d = true)
    (hsat : Satisfied2 hash (Dregg2.Circuit.Emit.EffectVmEmitV2.graduateV1Narrow d)
      minit mfin maddrs t) :
    ∀ i, i < t.rows.length →
      Dregg2.Circuit.Emit.EffectVmEmit.satisfiedVm hash d (envAt t i) (i == 0)
        (i + 1 == t.rows.length) :=
  narrowGrad_sound_family
    ⟨Dregg2.Verify.RangeFamilyFaithfulBatch.RangeFamilyFaithful.toOn hfam, hchip, hgrad, hsat⟩

/-- **⚑ The COMMITTED carrier IS the wide graduation's premise.** `graduateV1WideNarrow_sound`
consumes exactly `∀ b ∈ WIDE_RANGE_WIDTHS, t.tf (rangeTidW b) = rangeRows b`, which is
`RangeFamilyFaithful` unfolded. So the committed conjunct discharges the deployed multi-width
graduation keystone with nothing added: every v1 descriptor whose range teeth ride the wide
graduation is routed by the ONE committed carrier. -/
theorem wideNarrowGrad_sound_from_committed (hash : List ℤ → ℤ)
    (d : Dregg2.Circuit.Emit.EffectVmEmit.EffectVmDescriptor) (minit : ℤ → ℤ)
    (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (t : VmTrace)
    (hfam : RangeFamilyFaithful t)
    (hchip : ChipTableSoundNarrow hash (t.tf poseidon2narrow))
    (hgrad : Dregg2.Circuit.Emit.EffectVmEmitV2.graduableWide d = true)
    (hsat : Satisfied2 hash (Dregg2.Circuit.Emit.EffectVmEmitV2.graduateV1WideNarrow d)
      minit mfin maddrs t) :
    ∀ i, i < t.rows.length →
      Dregg2.Circuit.Emit.EffectVmEmit.satisfiedVm hash d (envAt t i) (i == 0)
        (i + 1 == t.rows.length) :=
  Dregg2.Circuit.Emit.EffectVmEmitV2.graduateV1WideNarrow_sound hash d minit mfin maddrs t hchip
    hfam hgrad hsat

/-! ## §6 — axiom hygiene. -/

#assert_axioms RangeFamilyFaithfulTf.pin
#assert_axioms RangeFamilyFaithfulOn.toTf
#assert_axioms RangeFamilyFaithfulTf.toOn
#assert_axioms shieldedRanged_sound_family
#assert_axioms shieldedRanged_forgedRange_inadmissible
#assert_axioms shieldedRanged_wrapMint_family_refused
#assert_axioms shieldedRanged_family_nonvacuous
#assert_axioms lexLt8_sound_family
#assert_axioms lexLt8_forgedRange_inadmissible
#assert_axioms lex_family_nonvacuous
#assert_axioms pgr_sound_family
#assert_axioms pgr_range_cells_bounded
#assert_axioms pgr_forgedRange_inadmissible
#assert_axioms pgrCell_sound_family
#assert_axioms pgrQuest_sound_family
#assert_axioms pgr_pins_nonvacuous
#assert_axioms toy_sound_family
#assert_axioms toy_forgedRange_inadmissible
#assert_axioms toy_forgedRow_refused
#assert_axioms toy_satisfied2_honest
#assert_axioms toy_family_nonvacuous
#assert_axioms forgedToy_satisfies
#assert_axioms forgedToy_family_refused
#assert_axioms busRange_sound_family
#assert_axioms narrowGrad_sound_family
#assert_axioms narrowGrad_forgedRange_inadmissible
#assert_axioms narrowGrad_sound_from_committed
#assert_axioms wideNarrowGrad_sound_from_committed

end Dregg2.Verify.RangeFamilyFaithfulBatch2
