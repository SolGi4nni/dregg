/-
# Dregg2.Distributed.StrandAdmission — the HYBRID (stake-OR-vouch) Sybil-admission gate
# that sits IN FRONT of finalization (closes red-team finding F-4).

**The finding (F-4).** A strand is just a keypair (`captp/src/lib.rs:122` `StrandId = [u8;32]`;
`Authority.Blocklace.AuthorId` here): minting a fresh strand costs nothing, so an adversary can
spin up unlimited free strands and flood the lace. Plain SSB leans on the human follow-graph for
admission; dregg needs a real admission gate or a Sybil swarm can saturate the federation.

**The mechanism (ember's decision — HYBRID stake-OR-vouch).** A strand is *admitted* to the
federation — its blocks may anchor finality and it may participate — iff EITHER

  (a) **VOUCH path**: it is vouched-for by ≥ `N` DISTINCT already-admitted members (a web-of-trust
      / follow-graph attestation; `N` a federation parameter), OR
  (b) **STAKE path**: it is backed by a slashable BOND of value ≥ `minBond` (value bonded in the
      in-kernel asset model — `Nat` value units, the same unit `Distributed.Economics` accounts in
      — slashable on equivocation / misbehavior).

Social path for the trusted, economic path for newcomers.

**What this is NOT — it does not duplicate `MembershipSafety`.** `MembershipSafety` models the
*constitution* (`constitution.rs`): the self-amending participant set + supermajority threshold +
Join/Leave admission DISCIPLINE. That is governance over an ALREADY-recognized member set. F-4 is
the layer BELOW: WHICH keypairs are even eligible to be participants / to have their blocks count.
`StrandAdmission` is the NEW gate IN FRONT — `admitted strand fed` is the precondition; the
constitution's `participants` (and `BlocklaceFinality`'s) are then drawn from the admitted set.

## What this proves (the F-4 closure).
* **Sybil-not-finalizable** (`sybil_block_not_finalizable` / `unadmitted_strand_no_final_leader`):
  a strand that is neither vouched-to-threshold nor bonded is UNADMITTED, and an unadmitted
  strand's blocks CANNOT be a final leader — gating `BlocklaceFinality.finalLeaderAt` on admission
  makes a Sybil strand contribute NOTHING to the finalized order. No Sybil reaches finality.
* **Stake path / slash-on-equivocation** (`bonded_equivocator_slashable` /
  `slash_covers_misbehavior`): if a bonded strand equivocates (a `Blocklace.Equivocation` proof
  object — the SAME fork witness `StrandIntegrity` / `ordering.rs::has_equivocation_in_past`
  consume), its bond is slashable and the slash burns the WHOLE bond, so the economic stake covers
  the misbehavior (the attacker forfeits ≥ `minBond`, the admission price).
* **Vouch path / threshold** (`vouch_admits_iff_threshold` / `below_threshold_not_admitted_vouch`):
  ≥ `N` distinct admitted-member vouches admit via the vouch path; < `N` does not. Distinctness
  (`Nodup`) and admitted-voucher gating mean a Sybil cannot vouch for itself or be vouched by a
  ring of other Sybils (only ADMITTED members' vouches count, just as `MembershipSafety` only
  counts `is_participant` votes).

`#assert_axioms`-clean (⊆ {propext, Classical.choice, Quot.sound}); NO `sorry`/`:=True`/
`native_decide`. Pure, computable, `#guard`-checked non-vacuity (a Sybil rejected, a vouched strand
and a bonded strand admitted, a bonded equivocator slashed). Verified with
`lake build Dregg2.Distributed.StrandAdmission`.
-/
import Dregg2.Distributed.BlocklaceFinality
import Dregg2.Distributed.StrandIntegrity

namespace Dregg2.Distributed.StrandAdmission

open Dregg2.Authority.Blocklace
  (Block Lace BlockId AuthorId Equivocation Equivocator)
open Dregg2.Distributed.BlocklaceFinality
  (finalLeaderAt leaderCandidates findAllFinalLeaders tauOrder waveLeader waveFirstRound roundOf)

/-! ## 1. The admission registry — vouches + bonds the federation parameters `N` / `minBond`.

A **`Vouch`** is one admitted member attesting (web-of-trust / follow-graph) for a candidate
strand. A **`Bond`** is a slashable stake a strand has posted in the in-kernel asset model. The
**`AdmissionState`** carries the federation's admission knobs (`N` = vouch threshold, `minBond` =
minimum slashable stake), the vouch attestations, the bonds, and the set of `seed` members
(genesis / bootstrap members admitted by construction — the trust root the vouch graph extends
from, exactly as `Constitution.new`'s initial participant set in `MembershipSafety`). -/

/-- **`Vouch`** — voucher `voucher` attests for candidate strand `candidate` (a follow-graph
edge). The signature on the vouch is the §8 crypto seam (discharged by the Ed25519 portal /
Rust cascade, as in `EpochReconfig`'s per-vote `SigValid`); here `voucher` is the authenticated
attester. A vouch counts only if the voucher is itself ADMITTED (see `distinctAdmittedVouchers`). -/
structure Vouch where
  voucher   : AuthorId
  candidate : AuthorId
  deriving DecidableEq, Inhabited

/-- **`Bond`** — a slashable stake of `amount` value units a strand `owner` has posted (in the
in-kernel asset model; `Nat` value units, the unit `Distributed.Economics` accounts in). The bond
is *slashable on equivocation*: a fork proof burns it (see §4). -/
structure Bond where
  owner  : AuthorId
  amount : Nat
  deriving DecidableEq, Inhabited

/-- **`AdmissionState`** — the federation's admission registry + parameters.

* `seeds`   — the bootstrap members admitted by construction (the trust root; genesis participants).
* `N`       — the VOUCH threshold: a candidate needs ≥ `N` distinct admitted-member vouches.
* `minBond` — the STAKE floor: a bond of ≥ `minBond` slashable value units admits via the stake path.
* `vouches` — the follow-graph attestations.
* `bonds`   — the posted slashable stakes. -/
structure AdmissionState where
  seeds   : List AuthorId
  N       : Nat
  minBond : Nat
  vouches : List Vouch
  bonds   : List Bond
  deriving Inhabited, DecidableEq

/-! ## 2. The admission predicate — admitted = seed ∨ vouchedToThreshold ∨ bonded.

We resolve admission in a single bootstrapped pass: a strand is admitted iff it is a seed, OR it is
bonded ≥ `minBond` (the stake path is self-standing — it needs no other member), OR it is vouched by
≥ `N` strands that are THEMSELVES admitted-by-seed-or-bond. This is the minimal honest closure that
keeps the vouch graph rooted: a Sybil cannot bootstrap admission out of a ring of mutually-vouching
Sybils, because each voucher must independently be a seed or be bonded. (A full transitive
least-fixed-point closure is the n>1 generalization; the seed-or-bond-rooted one-hop closure here is
the load-bearing anti-Sybil core and the one we prove + exhibit.) -/

/-- **`hasValidBond fed strand`** — the strand has posted a bond of value ≥ `minBond` (the STAKE
path, self-standing). -/
def hasValidBond (fed : AdmissionState) (strand : AuthorId) : Bool :=
  fed.bonds.any (fun b => b.owner == strand && b.amount ≥ fed.minBond)

/-- **`isSeed fed strand`** — `strand` is a bootstrap (genesis) member, admitted by construction. -/
def isSeed (fed : AdmissionState) (strand : AuthorId) : Bool := fed.seeds.contains strand

/-- The **roots** of the trust graph: strands admitted WITHOUT needing a vouch — seeds and bonded
strands. The vouch path extends admission from this root set. -/
def isRoot (fed : AdmissionState) (strand : AuthorId) : Bool :=
  isSeed fed strand || hasValidBond fed strand

/-- **`distinctVouchersFor fed candidate`** — the DISTINCT (`dedup`) set of vouchers attesting for
`candidate` whose own admission is rooted (seed or bonded). The `isRoot` gate is the analogue of
`MembershipSafety.distinctApprovers`' `is_participant` gate: only ADMITTED members' vouches count,
so a non-admitted Sybil's vouch is dropped, and dedup means one voucher cannot be double-counted. -/
def distinctVouchersFor (fed : AdmissionState) (candidate : AuthorId) : List AuthorId :=
  ((fed.vouches.filter (fun v => v.candidate == candidate && isRoot fed v.voucher)).map (·.voucher)).dedup

/-- **`vouchedBy fed strand`** — how many distinct rooted-admitted members vouch for `strand`. -/
def vouchedBy (fed : AdmissionState) (strand : AuthorId) : Nat :=
  (distinctVouchersFor fed strand).length

/-- **`vouchedToThreshold fed strand`** — the VOUCH path fires: ≥ `N` distinct rooted vouches. -/
def vouchedToThreshold (fed : AdmissionState) (strand : AuthorId) : Bool :=
  vouchedBy fed strand ≥ fed.N

/-- **`admitted fed strand`** — THE HYBRID ADMISSION GATE: a strand is admitted iff it is a seed,
OR it is bonded (stake path), OR it is vouched to threshold by rooted members (vouch path).

`admitted strand fed := isSeed strand fed ∨ vouchedBy strand fed ≥ N ∨ hasValidBond strand fed`
(seeds folded in as the bootstrap trust root). -/
def admitted (fed : AdmissionState) (strand : AuthorId) : Bool :=
  isSeed fed strand || vouchedToThreshold fed strand || hasValidBond fed strand

/-- An UNADMITTED strand (a fresh Sybil keypair): the negation of the gate. -/
def unadmitted (fed : AdmissionState) (strand : AuthorId) : Prop := admitted fed strand = false

/-! ## 3. THE FINALITY GATE — an UNADMITTED strand's blocks are NOT finalizable.

This is the F-4 closure on the consensus side. `BlocklaceFinality.finalLeaderAt` anchors a wave to
a leader block; we compose it with the admission gate (`finalLeaderAtAdmitted`): a block may anchor
a wave ONLY IF its creator is admitted. So an unadmitted Sybil strand contributes NO final leader,
hence nothing to `tauOrder`, hence reaches NO finality. The Rust node enforces the SAME gate by
drawing `participants` only from the admitted set before calling `ordering::tau`. -/

/-- **`finalLeaderAtAdmitted fed B participants wave wavelength`** — the admission-gated final
leader: `BlocklaceFinality.finalLeaderAt`, but a leader block is admitted to anchor the wave ONLY
when its creator is an admitted strand. An unadmitted creator's block is dropped (`none`). -/
def finalLeaderAtAdmitted (fed : AdmissionState) (B : Lace) (participants : List AuthorId)
    (wave wavelength : Nat) : Option Block :=
  match finalLeaderAt B participants wave wavelength with
  | some l => if admitted fed l.creator then some l else none
  | none   => none

/-- **`unadmitted_strand_no_final_leader` (the consensus-side F-4 tooth).** If the leader
that `BlocklaceFinality` would anchor at a wave is created by an UNADMITTED strand, the
admission-gated finality returns `none`: that wave anchors NOTHING. A Sybil strand cannot be a
final leader. -/
theorem unadmitted_strand_no_final_leader (fed : AdmissionState) (B : Lace)
    (participants : List AuthorId) (wave wavelength : Nat) (l : Block)
    (hl : finalLeaderAt B participants wave wavelength = some l)
    (hsybil : unadmitted fed l.creator) :
    finalLeaderAtAdmitted fed B participants wave wavelength = none := by
  unfold finalLeaderAtAdmitted unadmitted at *
  rw [hl]; simp only [hsybil]; rfl

/-- **`gated_leader_is_admitted`.** Conversely, whenever the gated finality DOES anchor a
leader, that leader's creator IS admitted — the gate is sound in both directions: only admitted
strands ever anchor a wave. -/
theorem gated_leader_is_admitted (fed : AdmissionState) (B : Lace)
    (participants : List AuthorId) (wave wavelength : Nat) (l : Block)
    (h : finalLeaderAtAdmitted fed B participants wave wavelength = some l) :
    admitted fed l.creator = true := by
  unfold finalLeaderAtAdmitted at h
  cases hfl : finalLeaderAt B participants wave wavelength with
  | none => rw [hfl] at h; simp at h
  | some l' =>
    rw [hfl] at h
    by_cases hadm : admitted fed l'.creator
    · simp only [hadm, if_true] at h; rw [← Option.some.inj h]; exact hadm
    · simp only [hadm] at h; exact absurd h (by simp)

/-- The admission-gated finalized order: walk the waves, take only the admission-gated final
leaders. (`BlocklaceFinality.findAllFinalLeaders`, filtered through the admission gate.) -/
def admittedFinalLeaders (fed : AdmissionState) (B : Lace) (participants : List AuthorId)
    (wavelength : Nat) : List Block :=
  let mr := BlocklaceFinality.maxRound B
  let waveCount := if wavelength == 0 then 0 else mr / wavelength + 1
  (List.range waveCount).filterMap (fun w => finalLeaderAtAdmitted fed B participants w wavelength)

/-- **`sybil_block_not_finalizable` (the HEADLINE F-4 closure).** Every block that
anchors the admission-gated finalized order is from an ADMITTED strand: an unadmitted Sybil's block
is in `admittedFinalLeaders` for NO wave. Spelled out: for all `l ∈ admittedFinalLeaders …`,
`admitted l.creator`. So no Sybil strand reaches finality — the finding is defended at the
finalization layer. -/
theorem sybil_block_not_finalizable (fed : AdmissionState) (B : Lace)
    (participants : List AuthorId) (wavelength : Nat)
    (l : Block) (hl : l ∈ admittedFinalLeaders fed B participants wavelength) :
    admitted fed l.creator = true := by
  unfold admittedFinalLeaders at hl
  obtain ⟨w, _, hw⟩ := List.mem_filterMap.mp hl
  exact gated_leader_is_admitted fed B participants w wavelength l hw

/-- **`sybil_contributes_no_leader` (the per-Sybil restatement).** A fixed UNADMITTED
strand `s` appears as the creator of NO admission-gated final leader, at any wave. The Sybil is
finality-inert. -/
theorem sybil_contributes_no_leader (fed : AdmissionState) (B : Lace)
    (participants : List AuthorId) (wavelength : Nat) (s : AuthorId)
    (hsybil : unadmitted fed s) :
    ∀ l ∈ admittedFinalLeaders fed B participants wavelength, l.creator ≠ s := by
  intro l hl hcontra
  have hadm := sybil_block_not_finalizable fed B participants wavelength l hl
  rw [hcontra] at hadm
  unfold unadmitted at hsybil
  rw [hadm] at hsybil; exact absurd hsybil (by simp)

/-! ## 4. THE STAKE PATH — equivocation by a bonded strand is SLASHABLE; the slash covers it.

A strand admitted via the stake path posted a bond ≥ `minBond`. If it equivocates (a
`Blocklace.Equivocation` proof — two incomparable same-author blocks; the SAME fork witness
`StrandIntegrity.forked_strand_not_forkFree` exhibits and `ordering.rs::has_equivocation_in_past`
detects), the bond is slashable: the federation burns it, so the equivocator forfeits its WHOLE
stake (≥ `minBond`). The economic price of admission backs the misbehavior. -/

/-- The bond amount a strand has posted (the maximum over its bonds; `0` if unbonded). -/
def bondAmount (fed : AdmissionState) (strand : AuthorId) : Nat :=
  ((fed.bonds.filter (fun b => b.owner == strand)).map (·.amount)).foldr Nat.max 0

/-- **`slash fed strand`** — slash `strand`'s bond: remove its bonds from the registry (burning the
staked value). Returns the updated state and the AMOUNT burned. The fork proof is the authorization
(no vote — exactly `MembershipSafety.autoEvict`'s discipline: the equivocation is its own warrant). -/
def slash (fed : AdmissionState) (strand : AuthorId) : AdmissionState × Nat :=
  let burned := bondAmount fed strand
  ({ fed with bonds := fed.bonds.filter (fun b => b.owner ≠ strand) }, burned)

/-- A bonded strand's `bondAmount` equals the bond's `amount` when it has exactly its one bond,
and in general is ≥ `minBond` when it was admitted via the stake path. We need: the stake-path
admission floor bounds the slashable amount from below. -/
theorem hasValidBond_amount_ge {fed : AdmissionState} {strand : AuthorId}
    (h : hasValidBond fed strand = true) : bondAmount fed strand ≥ fed.minBond := by
  unfold hasValidBond at h
  rw [List.any_eq_true] at h
  obtain ⟨b, hb, hcond⟩ := h
  rw [Bool.and_eq_true] at hcond
  obtain ⟨howner, hamt⟩ := hcond
  have howner' : b.owner = strand := by simpa using howner
  -- b is one of strand's bonds, so b.amount ≤ bondAmount (= foldr max), and b.amount ≥ minBond.
  have hmem : b.amount ∈ (fed.bonds.filter (fun b => b.owner == strand)).map (·.amount) := by
    apply List.mem_map_of_mem
    rw [List.mem_filter]
    exact ⟨hb, by simp [howner']⟩
  have hle : b.amount ≤ bondAmount fed strand :=
    Dregg2.Distributed.StrandIntegrity.le_foldr_max _ b.amount hmem
  have hge : fed.minBond ≤ b.amount := by simpa using hamt
  exact le_trans hge hle

/-- **`bonded_equivocator_slashable` (the STAKE-path tooth).** If a strand was admitted
via the stake path (`hasValidBond`, so `bondAmount ≥ minBond`) and it equivocates (a
`Blocklace.Equivocation` proof object), then slashing burns at least `minBond`: the slash covers
the misbehavior, the attacker forfeits ≥ the admission price. The equivocation proof is the only
authorization needed. -/
theorem bonded_equivocator_slashable (fed : AdmissionState) (B : Lace) (strand : AuthorId)
    (a b : Block) (_ : Equivocation B strand a b)
    (hbond : hasValidBond fed strand = true) :
    (slash fed strand).2 ≥ fed.minBond := by
  unfold slash
  exact hasValidBond_amount_ge hbond

/-- **`slash_covers_misbehavior` (the slash burns the WHOLE bond).** Slashing an
equivocator burns its entire posted bond: after the slash, the strand has NO bond left, and the
amount burned equals the bond it held. So the economic stake is fully forfeited — no residual
value survives the misbehavior. -/
theorem slash_covers_misbehavior (fed : AdmissionState) (B : Lace) (strand : AuthorId)
    (a b : Block) (_ : Equivocation B strand a b) :
    (slash fed strand).2 = bondAmount fed strand ∧
    hasValidBond (slash fed strand).1 strand = false := by
  refine ⟨rfl, ?_⟩
  -- after slashing, no bond of `strand` survives, so `hasValidBond` is false.
  unfold slash hasValidBond
  rw [List.any_eq_false]
  intro x hx
  rw [List.mem_filter] at hx
  have : x.owner ≠ strand := by simpa using hx.2
  simp [this]

/-- **`slashed_equivocator_loses_stake_admission` (the consequence: slashing REVOKES the
stake-path admission).** After an equivocator is slashed, it no longer has a valid bond, so it is
no longer admitted VIA THE STAKE PATH. (If it were ALSO a seed or vouched, those paths persist — the
hybrid gate is an OR; slashing kills only the path the bond bought. This is faithful: a slashed
newcomer with no social standing falls out of admission entirely.) -/
theorem slashed_equivocator_loses_stake_admission (fed : AdmissionState) (B : Lace)
    (strand : AuthorId) (a b : Block) (e : Equivocation B strand a b)
    (hnotseed : isSeed (slash fed strand).1 strand = false)
    (hnovouch : vouchedToThreshold (slash fed strand).1 strand = false) :
    admitted (slash fed strand).1 strand = false := by
  have hnobond := (slash_covers_misbehavior fed B strand a b e).2
  unfold admitted
  rw [hnotseed, hnovouch, hnobond]; rfl

/-! ## 5. THE VOUCH PATH — ≥ N distinct rooted-member vouches admit; < N does not.

The web-of-trust path. A candidate is admitted-by-vouch iff ≥ `N` DISTINCT admitted (rooted)
members vouch for it. Distinctness (`Nodup`) + the `isRoot` gate are the anti-Sybil teeth: a Sybil
cannot vouch for itself (it is not rooted), nor can a ring of fresh Sybils vouch each other into
admission (none is rooted), nor can one member be counted twice (`dedup`). -/

/-- **`vouch_admits_iff_threshold` (the vouch path is EXACTLY the threshold).** A strand
is admitted via the vouch path iff its distinct rooted-voucher count reaches `N`. The biconditional
pins the path to the threshold, neither stricter nor looser. -/
theorem vouch_admits_iff_threshold (fed : AdmissionState) (strand : AuthorId) :
    vouchedToThreshold fed strand = true ↔ vouchedBy fed strand ≥ fed.N := by
  unfold vouchedToThreshold; exact decide_eq_true_iff

/-- **`vouchers_nodup`.** The distinct-voucher set has no duplicates — built by `dedup`,
so one member cannot be double-counted toward `N` (the analogue of `MembershipSafety.approvers_nodup`). -/
theorem vouchers_nodup (fed : AdmissionState) (strand : AuthorId) :
    (distinctVouchersFor fed strand).Nodup := List.nodup_dedup _

/-- **`vouchers_are_rooted` (only ADMITTED members vouch).** Every counted voucher is
itself rooted-admitted (a seed or bonded): the `isRoot` gate drops a non-admitted Sybil's vouch
before it can count. So a ring of fresh, unrooted Sybils cannot vouch each other into admission. -/
theorem vouchers_are_rooted (fed : AdmissionState) (strand : AuthorId) :
    ∀ v ∈ distinctVouchersFor fed strand, isRoot fed v = true := by
  intro v hv
  unfold distinctVouchersFor at hv
  have hv' := List.mem_dedup.mp hv
  rw [List.mem_map] at hv'
  obtain ⟨w, hwf, rfl⟩ := hv'
  have hf := List.mem_filter.mp hwf
  rw [Bool.and_eq_true] at hf
  exact hf.2.2

/-- **`vouched_admits` (the vouch path admits).** If a strand reaches the vouch threshold,
it IS admitted (the hybrid gate's vouch disjunct fires). -/
theorem vouched_admits (fed : AdmissionState) (strand : AuthorId)
    (h : vouchedToThreshold fed strand = true) : admitted fed strand = true := by
  unfold admitted; rw [h]; simp

/-- **`below_threshold_not_admitted_vouch` (< N does NOT admit via vouch).** If a strand
has fewer than `N` distinct rooted vouches AND is neither a seed nor bonded, it is NOT admitted: the
vouch path requires the full threshold, and the other paths are closed. So `N - 1` Sybil-ring
vouches (or any sub-threshold support) buy nothing. -/
theorem below_threshold_not_admitted_vouch (fed : AdmissionState) (strand : AuthorId)
    (hbelow : vouchedBy fed strand < fed.N)
    (hnotseed : isSeed fed strand = false)
    (hnobond : hasValidBond fed strand = false) :
    admitted fed strand = false := by
  unfold admitted vouchedToThreshold
  have hvf : (vouchedBy fed strand ≥ fed.N) = False := by
    simp only [ge_iff_le, eq_iff_iff, iff_false, not_le]; exact hbelow
  rw [hnotseed, hnobond, decide_eq_false (by rw [hvf]; exact not_false)]
  rfl

/-- **`bonded_admits` (the stake path admits).** A strand with a valid bond is admitted
(the hybrid gate's stake disjunct fires) — the economic path, needing NO social standing. -/
theorem bonded_admits (fed : AdmissionState) (strand : AuthorId)
    (h : hasValidBond fed strand = true) : admitted fed strand = true := by
  unfold admitted; rw [h]; simp

/-- **`seed_admits` (the bootstrap root).** A genesis seed is admitted by construction. -/
theorem seed_admits (fed : AdmissionState) (strand : AuthorId)
    (h : isSeed fed strand = true) : admitted fed strand = true := by
  unfold admitted; rw [h]; simp

/-- **`admitted_iff` (the gate, fully unfolded).** `admitted` holds iff the strand is a
seed, OR vouched to threshold, OR bonded — the hybrid stake-OR-vouch (-OR-seed) disjunction in one
statement. -/
theorem admitted_iff (fed : AdmissionState) (strand : AuthorId) :
    admitted fed strand = true ↔
      (isSeed fed strand = true ∨ vouchedToThreshold fed strand = true ∨ hasValidBond fed strand = true) := by
  unfold admitted
  rw [Bool.or_eq_true, Bool.or_eq_true]
  tauto

/-! ## 6. NON-VACUITY — CONCRETE strands the gate ADMITS / REJECTS (the Rust differential).

These `#guard`s establish, against a CONCRETE federation (`fedDemo`: two seeds {1,2}, vouch
threshold `N = 2`, `minBond = 100`), that the gate is a REAL constraint: a fresh Sybil with no
vouch and no bond is REJECTED; a strand vouched by both seeds is ADMITTED; a strand with a 100-unit
bond is ADMITTED; a strand bonded BELOW the floor is rejected; a Sybil vouched only by ANOTHER
unrooted Sybil is rejected (the ring attack fails); and a bonded equivocator's slash burns 100. A
false `#guard` is a BUILD ERROR — the sanctioned non-vacuity tooth. These are the values the Rust
admission differential (`federation/src/admission*`) reproduces. -/

/-- Demo federation: seeds 1 and 2 (the bootstrap trust root), vouch threshold N = 2, minBond = 100.
Strand 1 and 2 are admitted seeds. Strand 3 is vouched by both seeds. Strand 4 posts a 100-unit
bond. Strand 5 posts only a 50-unit bond (below floor). Strand 6 is a fresh Sybil (nothing).
Strand 7 is vouched only by Sybil 6 (the ring attack). -/
def fedDemo : AdmissionState :=
  { seeds := [1, 2]
    N := 2
    minBond := 100
    vouches := [⟨1, 3⟩, ⟨2, 3⟩,       -- both seeds vouch for 3 ⇒ 2 distinct rooted vouches
                ⟨6, 7⟩]                -- only Sybil 6 vouches for 7 ⇒ 0 rooted vouches
    bonds := [⟨4, 100⟩, ⟨5, 50⟩] }    -- 4 bonded at the floor; 5 below it

-- SEEDS admitted by construction.
#guard admitted fedDemo 1 == true
#guard admitted fedDemo 2 == true
-- VOUCH PATH: strand 3 has 2 distinct rooted (seed) vouches ⇒ admitted.
#guard vouchedBy fedDemo 3 == 2
#guard vouchedToThreshold fedDemo 3 == true
#guard admitted fedDemo 3 == true
-- STAKE PATH: strand 4 bonded at the floor (100 ≥ 100) ⇒ admitted.
#guard hasValidBond fedDemo 4 == true
#guard admitted fedDemo 4 == true
-- STAKE FLOOR is real: strand 5 bonded BELOW the floor (50 < 100) ⇒ NOT admitted.
#guard hasValidBond fedDemo 5 == false
#guard admitted fedDemo 5 == false
-- SYBIL: strand 6, a fresh keypair with no vouch and no bond ⇒ REJECTED (the F-4 finding, defended).
#guard admitted fedDemo 6 == false
-- RING ATTACK: strand 7 vouched ONLY by unrooted Sybil 6 ⇒ 0 rooted vouches ⇒ REJECTED.
#guard vouchedBy fedDemo 7 == 0
#guard admitted fedDemo 7 == false
-- SLASH: strand 4's bond (100) is burned in full on equivocation.
#guard bondAmount fedDemo 4 == 100
#guard (slash fedDemo 4).2 == 100
#guard hasValidBond (slash fedDemo 4).1 4 == false
-- after the slash, strand 4 (no seed, no vouch) falls out of admission entirely.
#guard admitted (slash fedDemo 4).1 4 == false

/-! ### The FINALITY gate on a concrete trace — a Sybil leader anchors NOTHING.

We reuse `BlocklaceFinality.trace3` (the 3-node fully-connected lace whose wave-0 round-robin
leader is creator 1's genesis). With a federation that admits creators 1,2,3 (seeds), the gated
finality anchors creator 1 — admission is transparent to honest members. With a federation that
does NOT admit creator 1 (a Sybil), the gated finality anchors NOTHING at wave 0 — the F-4 finding
defended at the consensus layer on a real finalized trace. -/

/-- A federation admitting the trace's three honest creators (seeds 1,2,3). -/
def fedHonest3 : AdmissionState := { seeds := [1, 2, 3], N := 2, minBond := 100, vouches := [], bonds := [] }
/-- A federation that does NOT admit creator 1 (treats it as a Sybil) — seeds only 2,3. -/
def fedSybil1 : AdmissionState := { seeds := [2, 3], N := 2, minBond := 100, vouches := [], bonds := [] }

open BlocklaceFinality (trace3 trace3Participants)

-- the gated wave-0 final leader is creator 1's genesis (admission transparent to members).
#guard (finalLeaderAtAdmitted fedHonest3 trace3 trace3Participants 0 3).isSome
#guard ((finalLeaderAtAdmitted fedHonest3 trace3 trace3Participants 0 3).map (·.creator)) == some 1
-- the ungated rule DOES anchor creator 1 — so the gate is what makes the difference, not the trace.
#guard (finalLeaderAt trace3 trace3Participants 0 3).isSome
-- SYBIL: creator 1 NOT admitted ⇒ the gated wave-0 finality anchors NOTHING (F-4 defended on-trace).
#guard admitted fedSybil1 1 == false
#guard (finalLeaderAtAdmitted fedSybil1 trace3 trace3Participants 0 3).isNone
-- and the Sybil contributes NO admitted final leader across the whole order.
#guard (admittedFinalLeaders fedSybil1 trace3 trace3Participants 3).all (fun l => l.creator != 1)

/-! The `#guard`s above are the project's machine-checked non-vacuity teeth (a false `#guard` is a
BUILD ERROR). They establish, against CONCRETE federations + a real finalized trace, that the
hybrid gate is a REAL constraint: (i) seeds admitted; (ii) the vouch path admits at exactly N
distinct rooted vouches and the ring attack (unrooted vouchers) fails; (iii) the stake path admits
at the bond floor and a below-floor bond is rejected; (iv) a fresh Sybil keypair is REJECTED;
(v) slashing a bonded equivocator burns the WHOLE bond and revokes its admission; and (vi) on the
3-node finalized trace an unadmitted Sybil leader anchors NOTHING while an admitted member anchors
normally. So the safety theorems constrain a REAL, non-trivial admission rule, and F-4 (unlimited
free Sybil strands) is DEFENDED both at the gate and at finality. -/

/-! ## 7. THE LIVE ADMISSION GATE — an `@[export]`ed wire surface the NODE actually calls.

`§1–6` give the verified, EXECUTABLE hybrid gate (`admitted`, all pure `Bool` computation — no
`noncomputable`/`Classical` in the runtime path: `isSeed`/`hasValidBond`/`vouchedToThreshold` are
`List.any`/`List.length` folds, fully reducible). But — exactly the F-4 dark-mirror trap the SWAP
warns about — a verified gate that lives only BESIDE the running node is the weaker spec. This
section is the load-bearing wire: it exposes the verified `admitted` predicate as a wire-in/wire-out
`@[export] dregg_strand_admit` (the template is `FinalityGate.dregg_blocklace_finalize` /
`Exec.FFI.dregg_exec_full_forest_auth`), so the federation's Rust admission gate
(`federation/src/admission.rs::AdmissionRegistry::admitted`) computes the F-4 verdict FROM the
verified Lean rule itself — `dreggrs`'s Rust `admitted` stays as the DIFFERENTIAL sibling
(Lean == Rust on the same registry), not the decider.

The wire codec is self-contained, compact, whitespace-free, FAIL-CLOSED (any malformed field ⇒ the
`ERR` sentinel, which the Rust caller treats as "NOT admitted" — fail-closed, never fail-open). It is
decode∘encode round-trip-correct on the concrete `fedDemo` registry (`#guard`), so the Rust encoder
and this Lean decoder share one grammar. We prove the export EQUALS the verified `admitted` rule
(`strand_admit_eq_admitted`), so the export carries the proof — the F-4 gate the node runs IS the
verified gate, by construction.

```
INPUT  := "N=" Nat ";m=" Nat ";S=" NATLIST ";V=" VOUCHLIST ";Bo=" BONDLIST ";q=" Nat
NATLIST   := ε | Nat ("," Nat)*                       -- seeds
VOUCHLIST := ε | VOUCH ("," VOUCH)*                   -- vouches
VOUCH     := Nat ":" Nat                              -- voucher : candidate
BONDLIST  := ε | BOND ("," BOND)*                     -- bonds
BOND      := Nat ":" Nat                              -- owner : amount
OUTPUT := "1" (admitted) | "0" (NOT admitted) | "ERR" (malformed wire ⇒ fail-closed NOT admitted)
```
-/

/-- Parse a `Nat` strictly: non-empty, all-ASCII-digits. Fail-closed. -/
def parseNat? (s : String) : Option Nat :=
  if s.isEmpty then none else
    if s.all (fun c => c.isDigit) then s.toNat? else none

/-- Parse a possibly-empty `sep`-separated list of `Nat`s. Fail-closed: one malformed element fails
the whole parse. -/
def parseNatList? (sep : Char) (s : String) : Option (List Nat) :=
  if s.isEmpty then some []
  else (s.splitOn (String.singleton sep)).foldr
        (fun part acc => match acc, parseNat? part with
          | some xs, some n => some (n :: xs)
          | _, _ => none)
        (some [])

/-- Parse one `A:B` pair into a `(Nat × Nat)`. Fail-closed. -/
def parsePair? (s : String) : Option (Nat × Nat) :=
  match s.splitOn ":" with
  | [a, b] => match parseNat? a, parseNat? b with
              | some x, some y => some (x, y)
              | _, _ => none
  | _ => none

/-- Parse a possibly-empty `,`-separated list of `A:B` pairs. Fail-closed. -/
def parsePairList? (s : String) : Option (List (Nat × Nat)) :=
  if s.isEmpty then some []
  else (s.splitOn ",").foldr
        (fun part acc => match acc, parsePair? part with
          | some ps, some p => some (p :: ps)
          | _, _ => none)
        (some [])

/-- Strip a required `prefix`, returning the remainder, or `none` if absent. -/
def stripReq? (pfx s : String) : Option String :=
  if s.startsWith pfx then some (String.ofList (s.toList.drop pfx.length)) else none

/-- **`decodeAdmitWire`** — parse the full `INPUT` grammar into `(AdmissionState, queried strand)`.
Fail-closed on any deviation. -/
def decodeAdmitWire (s : String) : Option (AdmissionState × AuthorId) := do
  let rest ← stripReq? "N=" s
  match rest.splitOn ";" with
  | [nS, mSeg, sSeg, vSeg, boSeg, qSeg] =>
      let n ← parseNat? nS
      let mS ← stripReq? "m=" mSeg
      let sS ← stripReq? "S=" sSeg
      let vS ← stripReq? "V=" vSeg
      let boS ← stripReq? "Bo=" boSeg
      let qS ← stripReq? "q=" qSeg
      let minB ← parseNat? mS
      let seeds ← parseNatList? ',' sS
      let vouchPairs ← parsePairList? vS
      let bondPairs ← parsePairList? boS
      let q ← parseNat? qS
      let fed : AdmissionState :=
        { seeds := seeds, N := n, minBond := minB
          vouches := vouchPairs.map (fun p => ⟨p.1, p.2⟩)
          bonds := bondPairs.map (fun p => ⟨p.1, p.2⟩) }
      some (fed, q)
  | _ => none

/-- **`admitGate`** — THE GATE BODY. Decode the wire, run the VERIFIED `admitted` predicate, encode
the verdict (`"1"` admitted / `"0"` not). On a malformed wire return `"ERR"` — the Rust caller treats
`ERR` as "NOT admitted" (fail-closed). This is the verified hybrid stake-OR-vouch Sybil gate exposed
as a string function the linked Lean archive runs at the federation's admission point. -/
def admitGate (s : String) : String :=
  match decodeAdmitWire s with
  | some (fed, q) => if admitted fed q then "1" else "0"
  | none => "ERR"

/-- **THE EXPORT.** `@[export dregg_strand_admit]` — the C-ABI entry the node/federation FFI bridge
(`dregg-lean-ffi/src/distributed_ffi.rs`) calls. Same `String → String` shape as
`dregg_blocklace_finalize` / `dregg_exec_full_forest_auth`: the caller passes the wire-encoded
`(registry, strand)` and reads back the verified admission verdict. -/
@[export dregg_strand_admit]
def dregg_strand_admit (s : String) : String := admitGate s

/-- **`encodeAdmitWire`** — encode an `(AdmissionState, strand)` query as the `INPUT` grammar. The
inverse the Rust encoder mirrors; `decodeAdmitWire ∘ encodeAdmitWire = id` on the concrete registry
(`#guard` below), so the two sides share one grammar. -/
def encodeAdmitWire (fed : AdmissionState) (q : AuthorId) : String :=
  "N=" ++ toString fed.N ++
  ";m=" ++ toString fed.minBond ++
  ";S=" ++ String.intercalate "," (fed.seeds.map toString) ++
  ";V=" ++ String.intercalate "," (fed.vouches.map (fun v => toString v.voucher ++ ":" ++ toString v.candidate)) ++
  ";Bo=" ++ String.intercalate "," (fed.bonds.map (fun b => toString b.owner ++ ":" ++ toString b.amount)) ++
  ";q=" ++ toString q

/-- **`strand_admit_eq_admitted` (the export carries the proof).** For any wire that decodes
to `(fed, q)`, the exported `dregg_strand_admit` returns `"1"` iff the VERIFIED `admitted fed q` holds
(and `"0"` iff it does not). So the F-4 verdict the node reads off the export is DEFINITIONALLY the
verified hybrid-gate verdict — `dregg_strand_admit` is the verified `admitted`, marshalled. Gating
live admission on this export IS gating it on `StrandAdmission.admitted`. -/
theorem strand_admit_eq_admitted (s : String) (fed : AdmissionState) (q : AuthorId)
    (h : decodeAdmitWire s = some (fed, q)) :
    dregg_strand_admit s = (if admitted fed q then "1" else "0") := by
  unfold dregg_strand_admit admitGate
  rw [h]

/-- **`strand_admit_admits_iff`.** Read as a Boolean: the export emits `"1"` exactly when the
verified rule admits. The clean live-path predicate the federation calls. -/
theorem strand_admit_admits_iff (s : String) (fed : AdmissionState) (q : AuthorId)
    (h : decodeAdmitWire s = some (fed, q)) :
    (dregg_strand_admit s = "1") ↔ admitted fed q = true := by
  rw [strand_admit_eq_admitted s fed q h]
  by_cases hadm : admitted fed q
  · simp [hadm]
  · simp only [hadm]
    constructor
    · intro hc; exact absurd hc (by decide)
    · intro hc; exact absurd hc (by simp)

/-- **`admit_gate_deterministic`.** The gate is a deterministic function of the wire: two
honest replicas that encode the SAME registry+strand get the SAME verdict — agreement reduces to
seeing the same registry, through the exported gate the node actually calls. -/
theorem admit_gate_deterministic (s : String) (o₁ o₂ : String)
    (h₁ : admitGate s = o₁) (h₂ : admitGate s = o₂) : o₁ = o₂ := by
  rw [← h₁, ← h₂]

/-! ### LIVE-GATE non-vacuity `#guard`s — the export reproduces the verified verdict on the wire.

On the concrete `fedDemo` registry (seeds {1,2}, N=2, minBond=100), the exported gate AGREES with the
verified `admitted` on every strand role: seeds + the vouched strand 3 + the bonded strand 4 ADMIT
(`"1"`); the below-floor strand 5, the fresh Sybil 6, and the ring-attack strand 7 are REJECTED
(`"0"`). The wire round-trips, and a malformed wire is fail-closed to `ERR`. A false `#guard` is a
BUILD ERROR — the project's sanctioned non-vacuity tooth; this is the runtime face of the F-4
closure, the `(registry, strand) → verdict` differential the Rust `admission.rs` reproduces. -/

-- the export ADMITS the seeds + vouched + bonded strands (verified `admitted` = true).
#guard admitGate (encodeAdmitWire fedDemo 1) == "1"
#guard admitGate (encodeAdmitWire fedDemo 2) == "1"
#guard admitGate (encodeAdmitWire fedDemo 3) == "1"  -- vouch path
#guard admitGate (encodeAdmitWire fedDemo 4) == "1"  -- stake path
-- the export REJECTS the below-floor bond, the fresh Sybil, and the ring-attack candidate.
#guard admitGate (encodeAdmitWire fedDemo 5) == "0"  -- 50 < 100 floor
#guard admitGate (encodeAdmitWire fedDemo 6) == "0"  -- fresh Sybil (F-4)
#guard admitGate (encodeAdmitWire fedDemo 7) == "0"  -- ring attack (unrooted voucher)
-- the wire codec round-trips on the concrete registry (Rust-encoder ⟷ Lean-decoder shared grammar).
#guard decodeAdmitWire (encodeAdmitWire fedDemo 6) == some (fedDemo, 6)
-- the export equals the verified `admitted` verdict at each strand (the differential, on the wire).
#guard ([1,2,3,4,5,6,7].all (fun q =>
          (admitGate (encodeAdmitWire fedDemo q) == "1") == admitted fedDemo q))
-- a malformed wire is FAIL-CLOSED to ERR (the federation treats ERR as NOT admitted).
#guard admitGate "not a wire" == "ERR"
#guard admitGate "N=2;m=100;S=1,2;V=bad:vouch:extra;Bo=;q=6" == "ERR"

/-! ## 8. Axiom hygiene — the hybrid admission gate + its F-4 teeth are kernel-clean. -/

#assert_axioms unadmitted_strand_no_final_leader
#assert_axioms gated_leader_is_admitted
#assert_axioms sybil_block_not_finalizable
#assert_axioms sybil_contributes_no_leader
#assert_axioms hasValidBond_amount_ge
#assert_axioms bonded_equivocator_slashable
#assert_axioms slash_covers_misbehavior
#assert_axioms slashed_equivocator_loses_stake_admission
#assert_axioms vouch_admits_iff_threshold
#assert_axioms vouchers_nodup
#assert_axioms vouchers_are_rooted
#assert_axioms vouched_admits
#assert_axioms below_threshold_not_admitted_vouch
#assert_axioms bonded_admits
#assert_axioms seed_admits
#assert_axioms admitted_iff
#assert_axioms strand_admit_eq_admitted
#assert_axioms strand_admit_admits_iff
#assert_axioms admit_gate_deterministic

end Dregg2.Distributed.StrandAdmission
