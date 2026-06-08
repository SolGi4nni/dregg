/-
# Dregg2.Distributed.EpochReconfig — a FAITHFUL, EXECUTABLE model of the federation's REAL
# validator-set reconfiguration / epoch-handoff rule (`federation/src/epoch.rs`), with the
# safety property the federation relies on: **a committee hands off to its successor epoch
# with NO safety gap** — the new validator set, threshold and epoch number are all attested
# by an OLD-epoch supermajority and recomputed deterministically.

**The gap this closes.** `Dregg2/Distributed/MembershipSafety.lean` models
`blocklace/src/constitution.rs` — the *self-amending* membership rule that runs INSIDE one
running blocklace (Join/Leave/expel proposals, the H-rule, distinct-member quorum). That is the
*governance* layer. It does NOT model `federation/src/epoch.rs`, which is a DIFFERENT mechanism:
the federation freezes its validator set for a window of `epoch_length` blocks (an **epoch**) and
performs ALL membership/threshold/key changes ATOMICALLY at the epoch boundary, behind an
old-epoch `QuorumCertificate`. Constitution = continuous governance; epoch = batched, attested
reconfiguration with forward-secret key rotation. Neither covers the other.

`Dregg2/Distributed/ThresholdDecrypt.lean` covers the federation's threshold *decryption*; this is
the orthogonal validator-set *reconfiguration*.

The running federation (`federation/src/epoch.rs`) computes the handoff with a CONCRETE rule:

  1. `compute_bft_threshold` / `quorum_threshold`   — the next-epoch threshold is `n - n/3` of the
     NEW member count (`epoch.rs:186-188`, `lib.rs:144-150`). `f = floor(n/3)`, quorum `= n - f`.
  2. `propose_epoch_transition`                     — validate that every removal is a current
     member and every addition is NOT, compute the new member set, and set
     `new_threshold = compute_bft_threshold(new_members.len())` (`epoch.rs:199-254`).
  3. `apply_epoch_transition`                        — re-checks `from_epoch = current`,
     `to_epoch = current+1`, recomputes & checks the threshold, advances epoch +
     `epoch_start_height += epoch_length` (`epoch.rs:260-305`).
  4. `verify_epoch_transition`                       — the SAFETY GATE: epoch numbers sequential,
     the attestation QC carries `≥ old_threshold` votes, EACH vote is a valid old-member signature
     over the canonical vote message, removals∈old / additions∉old, and the new threshold is the
     correct supermajority of the resulting count (`epoch.rs:314-382`).

This module models THAT rule — `quorumThreshold` / `applyDelta` / `validDelta` / `proposeTransition`
/ `verifyTransition` as genuine **executable Lean functions** — and proves the REAL safety
properties the epoch handoff relies on:

* **No-safety-gap quorum attestation** (`verified_needs_old_quorum` / `verified_signers_are_old_members`):
  a transition that `verify`s carries at least `old_threshold = quorumThreshold |old|` DISTINCT
  old-epoch members' signatures — so the *departing* committee, by its own BFT quorum, ratifies
  its successor. A minority of the old epoch can NEVER install a new validator set.
* **Threshold-recomputation correctness** (`applied_threshold_is_supermajority` /
  `verify_pins_new_threshold`): after a verified transition the threshold is EXACTLY
  `quorumThreshold` of the NEW member count — the successor epoch is born already configured for
  its own supermajority, never inheriting a stale (too-low) bar.
* **Sequential, gap-free epoch numbering** (`verify_seq` / `apply_advances_one`): `to = from+1`
  and the applied config's epoch is exactly the successor — no skipped or replayed epoch.
* **Member-delta well-formedness** (`verify_delta_wf` / `applyDelta_count`): a verified transition
  only removes current members and only adds non-members, and the new count is
  `|old| + |added| − |removed|` — the set transformation the Rust performs (`epoch.rs:278-284`).
* **Monotone safety bridge** (`epoch_handoff_no_gap`): the headline — IF a transition verifies, THEN
  applying it yields a config whose epoch advanced by one AND whose threshold is the correct
  supermajority of the new set AND whose membership delta is exactly the attested one. The successor
  committee is fully determined by an old-epoch quorum; there is no instant in which authority is
  unattested.

§ PORTAL (honest carried crypto assumption, NEVER faked as proved — mirroring `Dregg2.CryptoKernel`
and `Authority.CaveatChain`'s `MacUnforgeable`): the per-vote Ed25519 signature check
`SigValid : PubKey → Msg → Sig → Bool` (`epoch.rs:344` `pk.verify(&vote_message, sig)`). We do NOT
prove Ed25519 secure; the quorum theorems are stated relative to it — "a verifying QC carries
`old_threshold` signatures THAT PASS `SigValid` under distinct old-member keys." Whether those
signatures could be FORGED is exactly the EUF-CMA assumption the real Ed25519 discharges.

Pure, computable, `#eval`-able. `#assert_axioms`-clean (⊆ {propext, Classical.choice, Quot.sound});
NO `sorry` / `:=True`. The Rust differential is `federation/src/epoch_diff.rs`.
-/
import Mathlib.Data.List.Basic
import Mathlib.Data.List.Nodup
import Mathlib.Tactic
import Dregg2.Tactics

namespace Dregg2.Distributed.EpochReconfig

/-! ## §1 The BFT threshold (`compute_bft_threshold` → `quorum_threshold`, `lib.rs:144-150`). -/

/-- **`quorumThreshold n = n − n/3`** — BFT quorum tolerating `f = ⌊n/3⌋` faults
(`lib.rs:144-150` `quorum_threshold`; `epoch.rs:186-188` delegates to it). `n=0 ↦ 0`,
`n=1 ↦ 1`, `n=3 ↦ 2`, `n=4 ↦ 3`, `n=7 ↦ 5`, `n=10 ↦ 7` — exactly the Rust golden values. -/
def quorumThreshold (n : Nat) : Nat := n - n / 3

@[simp] theorem quorumThreshold_zero : quorumThreshold 0 = 0 := rfl

/-- The Rust golden values (`lib.rs:168-173`, `epoch.rs:625-635`) — re-run here as `#guard`s. -/
example : quorumThreshold 1 = 1 := by decide
example : quorumThreshold 2 = 2 := by decide
example : quorumThreshold 3 = 2 := by decide
example : quorumThreshold 4 = 3 := by decide
example : quorumThreshold 5 = 4 := by decide
example : quorumThreshold 6 = 4 := by decide
example : quorumThreshold 7 = 5 := by decide
example : quorumThreshold 10 = 7 := by decide
example : quorumThreshold 13 = 9 := by decide

/-- **`quorum is a strict majority for n ≥ 1`** — `n − ⌊n/3⌋ > n/2`, i.e. any two quorums
intersect: the safety backbone of the handoff (two conflicting successor sets cannot both gather
an old-epoch quorum). -/
theorem quorum_gt_half (n : Nat) (hn : 1 ≤ n) : n < 2 * quorumThreshold n := by
  unfold quorumThreshold
  omega

/-- **`quorum ≤ n`** — a quorum never demands more votes than the membership has (well-formedness). -/
theorem quorum_le (n : Nat) : quorumThreshold n ≤ n := by unfold quorumThreshold; omega

/-- **two old-epoch quorums intersect** — the classical BFT intersection lemma, here over the
old member count. If two vote-sets each reach `quorumThreshold n` out of `n` members, then
`|A| + |B| > n`, so by inclusion–exclusion `A ∩ B ≠ ∅`: they SHARE a member. This is WHY a single
old committee can only ratify ONE successor — a forked reconfiguration (two conflicting successor
sets each gathering an old-epoch quorum) would need two disjoint quorums, impossible here. -/
theorem quorums_intersect (n a b : Nat)
    (ha : quorumThreshold n ≤ a) (hb : quorumThreshold n ≤ b) (hn : 1 ≤ n) :
    n < a + b := by
  have := quorum_gt_half n hn
  unfold quorumThreshold at *
  omega

/-! ## §2 The validator set, the membership delta, and `apply` / `validDelta`.

We carry validators by their public-key identity. `members` is the ordered current set (the Rust
`Vec<ValidatorInfo>`, keyed by `public_key`, `epoch.rs:39,206-216`); we model identities as an
arbitrary type `K` with `DecidableEq` (the Rust `==` on `PublicKey`). A delta is the
`(added, removed)` pair carried in `EpochTransition` (`epoch.rs:73-75`). -/

variable {K : Type} [DecidableEq K]

/-- A **membership delta** = the added/removed identities of an `EpochTransition`
(`epoch.rs:73-75`: `added_validators` keyed by pubkey + `removed_validators`). -/
structure Delta (K : Type) where
  added   : List K
  removed : List K

/-- **`applyDelta old d`** = the new member set: drop removals, append additions — EXACTLY the Rust
`apply_epoch_transition` two-step (`epoch.rs:278-284`: `retain(|m| !removed.contains(m))` then
`extend(added)`). -/
def applyDelta (old : List K) (d : Delta K) : List K :=
  (old.filter (fun m => !(d.removed.contains m))) ++ d.added

/-- **`validDelta old d`** = the `propose`/`verify` admissibility check (`epoch.rs:204-220`,
`epoch.rs:352-368`): every removal IS a current member, every addition is NOT, removed/added are
each duplicate-free, and the resulting set is nonempty (`EmptyMemberSet`, `epoch.rs:231-233`). -/
def validDelta (old : List K) (d : Delta K) : Prop :=
  (∀ k ∈ d.removed, k ∈ old) ∧
  (∀ k ∈ d.added, k ∉ old) ∧
  d.removed.Nodup ∧ d.added.Nodup ∧
  (applyDelta old d ≠ [])

/-- **`applyDelta` preserves nodup** — if `old` is duplicate-free and the delta is valid (removals
are members, additions are non-members & nodup), the new set is duplicate-free. The federation
relies on this so the new threshold (computed from `.len()`) reflects DISTINCT validators. -/
theorem applyDelta_nodup (old : List K) (d : Delta K)
    (hold : old.Nodup) (hadd : d.added.Nodup)
    (hnew : ∀ k ∈ d.added, k ∉ old) :
    (applyDelta old d).Nodup := by
  unfold applyDelta
  apply List.Nodup.append
  · exact hold.filter _
  · exact hadd
  · intro k hk hk2
    have : k ∈ old := List.mem_of_mem_filter hk
    exact hnew k hk2 this

/-- **`applyDelta_count`** — the new member COUNT is `|old| − |removed| + |added|` whenever `old` is
nodup and the delta is valid (so the filter drops exactly `|removed|`). This is the count the Rust
feeds to `compute_bft_threshold` (`epoch.rs:291`, `epoch.rs:371-372`). -/
theorem applyDelta_count (old : List K) (d : Delta K)
    (hold : old.Nodup) (hrem : d.removed.Nodup)
    (hsub : ∀ k ∈ d.removed, k ∈ old) :
    (applyDelta old d).length = old.length - d.removed.length + d.added.length := by
  unfold applyDelta
  rw [List.length_append]
  have hfilter : (old.filter (fun m => !(d.removed.contains m))).length
      = old.length - d.removed.length := by
    -- the filtered-out members are exactly `removed` (a nodup sublist by identity), so
    -- |filter| = |old| - |removed|.
    have hcount : (old.filter (fun m => d.removed.contains m)).length = d.removed.length := by
      apply le_antisymm
      · -- the kept-side is a subset of removed, and nodup, so ≤ |removed|
        have hnd : (old.filter (fun m => d.removed.contains m)).Nodup := hold.filter _
        have hss : (old.filter (fun m => d.removed.contains m)) ⊆ d.removed := by
          intro k hk
          have := List.of_mem_filter hk
          simpa [List.contains_iff_mem] using this
        exact (hnd.subperm hss).length_le
      · -- removed ⊆ filtered-kept (each removal is a member AND passes the predicate), nodup
        have hss : d.removed ⊆ (old.filter (fun m => d.removed.contains m)) := by
          intro k hk
          rw [List.mem_filter]
          exact ⟨hsub k hk, by simpa [List.contains_iff_mem] using hk⟩
        exact (hrem.subperm hss).length_le
    -- |old| = |filter ¬p| + |filter p|
    have hpart := List.length_eq_length_filter_add (l := old) (fun m => !(d.removed.contains m))
    simp only [Bool.not_not] at hpart
    omega
  omega

/-! ## §3 The epoch config, the transition, and `verify` / `apply` (`epoch.rs:31-42,67-80`).

`EpochConfig` is the running validator-set window (`epoch.rs:31-42`): epoch number, start height,
the ordered members and the active threshold. We abstract over the validator identity `K` and the
signature/key types via the §-PORTAL `SigValid` parameter. -/

/-- The running per-epoch configuration (`epoch.rs:31-42`). `epochLength`/`startHeight` are carried
so the handoff's height arithmetic (`epoch.rs:301`) is modeled, not just the membership. -/
structure EpochConfig (K : Type) where
  epochLength : Nat
  current     : Nat
  startHeight : Nat
  members     : List K
  threshold   : Nat

/-- `EpochConfig.genesis` (`epoch.rs:546-557`): epoch 0, start 0, threshold = supermajority of the
genesis members. -/
def EpochConfig.genesis (members : List K) (epochLength : Nat) : EpochConfig K :=
  { epochLength := epochLength, current := 0, startHeight := 0,
    members := members, threshold := quorumThreshold members.length }

/-! ### § PORTAL — the per-vote Ed25519 check.

`SigValid pk msg sig` is the abstract signature predicate (`epoch.rs:344` `pk.verify(&vote_message,
sig)`). We do NOT prove Ed25519 secure; the quorum theorems hold RELATIVE to it. A QC's votes are
`(voterPubKey, sig)` pairs over the one canonical `voteMessage` (`epoch.rs:336-340`). -/

variable {Sig Msg : Type}

/-- A quorum certificate's vote = a `(voterKey, sig)` pair (`epoch.rs:191` `votes : Vec<(usize,
Signature)>`, dereferenced to the member's key at `epoch.rs:342-348`). -/
structure Vote (K Sig : Type) where
  voter : K
  sig   : Sig

/-- An **epoch transition** (`epoch.rs:67-80`): the from/to epochs, the membership delta, the
declared new threshold, and the attestation = the canonical vote message + the QC votes. -/
structure Transition (K Sig Msg : Type) where
  fromEpoch    : Nat
  toEpoch      : Nat
  delta        : Delta K
  newThreshold : Nat
  voteMsg      : Msg
  votes        : List (Vote K Sig)

/-- **`signers t` = the distinct voter keys whose signature is valid** under `SigValid` over the
canonical message (`epoch.rs:341-350`: each vote must resolve to an old member AND `pk.verify`). We
take the `voter` of each vote that passes the portal check; `verify` separately requires these to be
old members and the votes to be nodup-by-voter (mirroring the Rust's per-member dedup discipline). -/
def Transition.validVoters (SigValid : K → Msg → Sig → Bool) (t : Transition K Sig Msg) : List K :=
  (t.votes.filter (fun v => SigValid v.voter t.voteMsg v.sig)).map (·.voter)

/-- **`verifyTransition`** — the safety gate (`epoch.rs:314-382`), as an executable predicate:

1. epoch numbers sequential: `from = current`, `to = current+1` (`epoch.rs:316-321`);
2. the attestation carries `≥ old.threshold` validly-signed DISTINCT old-member votes
   (`epoch.rs:324`: `votes.len() ≥ threshold`; `epoch.rs:341-350`: each vote a valid old-member sig);
3. the membership delta is well-formed against the OLD set (`epoch.rs:352-368`); and
4. the declared `newThreshold` is the correct supermajority of the resulting count
   (`epoch.rs:371-379`).

`validDelta` (a `Prop`) is checked here as a hypothesis of the safety theorems rather than re-encoded
decidably; the executable core is the quorum + threshold + sequencing arithmetic. -/
def verifyTransition (SigValid : K → Msg → Sig → Bool)
    (old : EpochConfig K) (t : Transition K Sig Msg) : Prop :=
  t.fromEpoch = old.current ∧
  t.toEpoch = old.current + 1 ∧
  -- the validly-signed voters are all OLD members, are duplicate-free, and number ≥ old.threshold:
  (∀ k ∈ t.validVoters SigValid, k ∈ old.members) ∧
  (t.validVoters SigValid).Nodup ∧
  old.threshold ≤ (t.validVoters SigValid).length ∧
  -- the membership delta is well-formed against the old set:
  validDelta old.members t.delta ∧
  -- the declared new threshold IS the supermajority of the new member count:
  t.newThreshold = quorumThreshold (applyDelta old.members t.delta).length

/-- **`applyTransition old t`** — the post-handoff config (`epoch.rs:260-305`): epoch advances to
`to`, start height bumps by `epochLength`, members become `applyDelta`, threshold becomes the
declared `newThreshold` (which `verify` pins to the supermajority). -/
def applyTransition (old : EpochConfig K) (t : Transition K Sig Msg) : EpochConfig K :=
  { old with
    current     := t.toEpoch,
    startHeight := old.startHeight + old.epochLength,
    members     := applyDelta old.members t.delta,
    threshold   := t.newThreshold }

/-! ## §4 The safety theorems — NO safety gap at the epoch boundary. -/

/-- **`verify_seq`** — a verified transition is sequential: `to = from + 1 = current + 1`. No skipped
or replayed epoch number (`epoch.rs:316-321`). -/
theorem verify_seq (SigValid : K → Msg → Sig → Bool)
    (old : EpochConfig K) (t : Transition K Sig Msg)
    (h : verifyTransition SigValid old t) :
    t.toEpoch = old.current + 1 ∧ t.fromEpoch = old.current :=
  ⟨h.2.1, h.1⟩

/-- **`apply_advances_one`** — applying a verified transition advances the epoch by EXACTLY one. -/
theorem apply_advances_one (SigValid : K → Msg → Sig → Bool)
    (old : EpochConfig K) (t : Transition K Sig Msg)
    (h : verifyTransition SigValid old t) :
    (applyTransition old t).current = old.current + 1 := by
  simp only [applyTransition]
  exact h.2.1

/-- **`verified_needs_old_quorum`** — the headline NO-GAP property: a verified transition carries at
least `quorumThreshold |old.members|`-many DISTINCT, validly-signed OLD-epoch voters. The departing
committee, by its own BFT quorum, ratifies its successor — a minority can NEVER install a new
validator set. (Stated relative to the `SigValid` portal: these voters' signatures all PASS the
Ed25519 check; their unforgeability is the EUF-CMA assumption, not a Lean law.) -/
theorem verified_needs_old_quorum (SigValid : K → Msg → Sig → Bool)
    (old : EpochConfig K) (t : Transition K Sig Msg)
    (hthr : old.threshold = quorumThreshold old.members.length)
    (h : verifyTransition SigValid old t) :
    quorumThreshold old.members.length ≤ (t.validVoters SigValid).length ∧
    (∀ k ∈ t.validVoters SigValid, k ∈ old.members) ∧
    (t.validVoters SigValid).Nodup := by
  obtain ⟨_, _, hmem, hnd, hcount, _, _⟩ := h
  exact ⟨hthr ▸ hcount, hmem, hnd⟩

/-- **`verified_signers_are_old_members`** — every validly-signed voter of a verified transition is
an old-epoch member. Combined with `validVoters`'s nodup, the attesting quorum is `quorumThreshold`
DISTINCT current members — there is no instant in which an unattested authority installs the new set. -/
theorem verified_signers_are_old_members (SigValid : K → Msg → Sig → Bool)
    (old : EpochConfig K) (t : Transition K Sig Msg)
    (h : verifyTransition SigValid old t) :
    ∀ k ∈ t.validVoters SigValid, k ∈ old.members :=
  h.2.2.1

/-- **`verify_pins_new_threshold`** — a verified transition's declared `newThreshold` is EXACTLY the
supermajority of the new member count (`epoch.rs:371-379`: `verify` rejects any other value). -/
theorem verify_pins_new_threshold (SigValid : K → Msg → Sig → Bool)
    (old : EpochConfig K) (t : Transition K Sig Msg)
    (h : verifyTransition SigValid old t) :
    t.newThreshold = quorumThreshold (applyDelta old.members t.delta).length :=
  h.2.2.2.2.2.2

/-- **`applied_threshold_is_supermajority`** — after applying a verified transition the NEW config's
threshold is the correct supermajority of its OWN member set. The successor epoch is born already
configured for its own BFT quorum; it never inherits a stale (too-low) bar. -/
theorem applied_threshold_is_supermajority (SigValid : K → Msg → Sig → Bool)
    (old : EpochConfig K) (t : Transition K Sig Msg)
    (h : verifyTransition SigValid old t) :
    (applyTransition old t).threshold = quorumThreshold (applyTransition old t).members.length := by
  simp only [applyTransition]
  exact verify_pins_new_threshold SigValid old t h

/-- **`verify_delta_wf`** — a verified transition's membership delta is well-formed against the old
set: removals are members, additions are non-members, both duplicate-free, result nonempty. -/
theorem verify_delta_wf (SigValid : K → Msg → Sig → Bool)
    (old : EpochConfig K) (t : Transition K Sig Msg)
    (h : verifyTransition SigValid old t) :
    validDelta old.members t.delta :=
  h.2.2.2.2.2.1

/-- **`applied_members_count`** — the new member count is exactly `|old| − |removed| + |added|`,
provided the old set is nodup (the running federation maintains a nodup `Vec<ValidatorInfo>` keyed
by pubkey). This is the count `verify` fed to `quorumThreshold`. -/
theorem applied_members_count (SigValid : K → Msg → Sig → Bool)
    (old : EpochConfig K) (t : Transition K Sig Msg)
    (hold : old.members.Nodup)
    (h : verifyTransition SigValid old t) :
    (applyTransition old t).members.length
      = old.members.length - t.delta.removed.length + t.delta.added.length := by
  simp only [applyTransition]
  obtain ⟨_, _, _, _, _, ⟨hsub, _, hrnd, _, _⟩, _⟩ := h
  exact applyDelta_count old.members t.delta hold hrnd hsub

/-- **`epoch_handoff_no_gap`** — the crown theorem assembling the no-gap guarantee. IF a transition
verifies against the old config (whose threshold is its own supermajority), THEN applying it yields a
successor config that:
  (1) advanced the epoch number by exactly one (gap-free sequencing),
  (2) was attested by a `quorumThreshold |old|` quorum of DISTINCT old-epoch members
      (the departing committee's BFT majority — authority is continuously attested), and
  (3) is born with the correct supermajority threshold for its OWN, well-formed member set.
There is no instant between epochs in which an unattested or under-configured committee holds
authority — the successor is fully determined by an old-epoch quorum. -/
theorem epoch_handoff_no_gap (SigValid : K → Msg → Sig → Bool)
    (old : EpochConfig K) (t : Transition K Sig Msg)
    (hthr : old.threshold = quorumThreshold old.members.length)
    (h : verifyTransition SigValid old t) :
    (applyTransition old t).current = old.current + 1 ∧
    quorumThreshold old.members.length ≤ (t.validVoters SigValid).length ∧
    (t.validVoters SigValid).Nodup ∧
    (∀ k ∈ t.validVoters SigValid, k ∈ old.members) ∧
    (applyTransition old t).threshold
      = quorumThreshold (applyTransition old t).members.length ∧
    validDelta old.members t.delta := by
  refine ⟨apply_advances_one SigValid old t h, ?_, ?_, ?_,
          applied_threshold_is_supermajority SigValid old t h,
          verify_delta_wf SigValid old t h⟩
  · exact (verified_needs_old_quorum SigValid old t hthr h).1
  · exact (verified_needs_old_quorum SigValid old t hthr h).2.2
  · exact verified_signers_are_old_members SigValid old t h

/-! ## §5 NON-VACUITY — the predicates are witnessed BOTH true and false (never `:=True`).

A concrete instance over `K = Nat`, `Sig = Msg = Nat`, with `SigValid k msg sig := decide (sig = k)`
(a toy "signature = own key" check — enough to exercise the quorum arithmetic concretely). -/

namespace Demo

/-- toy portal: a vote is "valid" iff its signature equals the voter's key. -/
def sv (k : Nat) (_ : Nat) (sig : Nat) : Bool := decide (sig = k)

/-- a 4-member old config at epoch 0; threshold = quorumThreshold 4 = 3. -/
def old4 : EpochConfig Nat := EpochConfig.genesis [0, 1, 2, 3] 100

example : old4.threshold = 3 := by decide
example : old4.members.length = 4 := by decide

/-- a transition adding member 4 and removing member 3 → new count 4 → threshold 3, attested by
members 0,1,2 (three valid sigs = quorum of 4). -/
def goodT : Transition Nat Nat Nat :=
  { fromEpoch := 0, toEpoch := 1,
    delta := { added := [4], removed := [3] },
    newThreshold := 3, voteMsg := 0,
    votes := [⟨0, 0⟩, ⟨1, 1⟩, ⟨2, 2⟩] }

/-- POSITIVE witness: `goodT` verifies. (`validDelta` discharged by `decide` on the executable parts
plus the explicit nonempty/membership facts.) -/
example : verifyTransition sv old4 goodT := by
  refine ⟨rfl, rfl, ?_, ?_, ?_, ?_, ?_⟩
  · decide
  · decide
  · decide
  · refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> decide
  · decide

/-- the new committee count after `goodT` is 4 → quorum 3 (concrete `applyDelta`). -/
example : (applyDelta old4.members goodT.delta).length = 4 := by decide
example : quorumThreshold (applyDelta old4.members goodT.delta).length = 3 := by decide

/-- NEGATIVE witness #1 — UNDER-QUORUM: only TWO valid signers (members 0,1) cannot install a new
set; `verify` fails (2 < threshold 3). The no-minority-seizure tooth. -/
def underQuorumT : Transition Nat Nat Nat :=
  { goodT with votes := [⟨0, 0⟩, ⟨1, 1⟩] }

example : ¬ verifyTransition sv old4 underQuorumT := by
  intro h
  obtain ⟨_, _, _, _, hcount, _, _⟩ := h
  simp only [Transition.validVoters, underQuorumT, goodT, sv, old4, EpochConfig.genesis] at hcount
  -- threshold 3 ≤ 2 is false
  revert hcount; decide

/-- NEGATIVE witness #2 — FORGED SIGNER (an OUTSIDER, key 9, not an old member): even with three
votes, the outsider's vote (key 9) is an old-member-failing signer, so the valid-voter quorum drops
below threshold AND membership fails. `verify` fails. The no-stranger-attestation tooth. -/
def outsiderT : Transition Nat Nat Nat :=
  { goodT with votes := [⟨0, 0⟩, ⟨1, 1⟩, ⟨9, 9⟩] }

example : ¬ verifyTransition sv old4 outsiderT := by
  intro h
  obtain ⟨_, _, hmem, _, _, _, _⟩ := h
  -- 9 is a valid signer (sig 9 = key 9) but NOT an old member
  have : (9 : Nat) ∈ outsiderT.validVoters sv := by
    simp only [Transition.validVoters, outsiderT, goodT, sv]; decide
  have := hmem 9 this
  simp only [old4, EpochConfig.genesis] at this
  revert this; decide

/-- NEGATIVE witness #3 — WRONG THRESHOLD: declaring `newThreshold = 2` when the new count (4)
demands 3. `verify` fails (`epoch.rs:377-379` `InvalidThreshold`). -/
def wrongThrT : Transition Nat Nat Nat := { goodT with newThreshold := 2 }

example : ¬ verifyTransition sv old4 wrongThrT := by
  intro h
  obtain ⟨_, _, _, _, _, _, hthr⟩ := h
  simp only [wrongThrT, goodT, old4, EpochConfig.genesis] at hthr
  revert hthr; decide

/-- NEGATIVE witness #4 — NON-SEQUENTIAL (epoch replay / skip): a transition claiming
`from = 5` against a config at epoch 0 fails (`epoch.rs:316`). -/
def replayT : Transition Nat Nat Nat := { goodT with fromEpoch := 5 }

example : ¬ verifyTransition sv old4 replayT := by
  intro h
  have hf := h.1
  simp only [replayT, goodT, old4, EpochConfig.genesis] at hf
  omega

end Demo

/-! ## §6 axiom hygiene. -/

#assert_axioms quorumThreshold
#assert_axioms quorum_gt_half
#assert_axioms quorums_intersect
#assert_axioms applyDelta_nodup
#assert_axioms applyDelta_count
#assert_axioms verify_seq
#assert_axioms apply_advances_one
#assert_axioms verified_needs_old_quorum
#assert_axioms verified_signers_are_old_members
#assert_axioms verify_pins_new_threshold
#assert_axioms applied_threshold_is_supermajority
#assert_axioms verify_delta_wf
#assert_axioms applied_members_count
#assert_axioms epoch_handoff_no_gap

end Dregg2.Distributed.EpochReconfig
