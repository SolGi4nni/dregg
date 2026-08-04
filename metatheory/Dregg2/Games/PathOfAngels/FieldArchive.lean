/-
# Path of Angels — receipt-derived Field Archive

The archive is a projection of completed, closed game judgments.  Its acquisition
surface accepts `JudgedRun`, never a naked `ArtifactRef` or generic `RunReceipt`.
Each entry retains the exact receipt key, full mission, and activated content
domain from which it came.  Multiple genuine runs which discover the same artifact
therefore remain distinct provenance entries.

Archive membership is monotone, and re-acquiring the exact same projected origin
is idempotent because entries form a `Finset`.  No stronger artifact-level
idempotence is claimed.  Canon lifecycle is not cached in the archive: beta,
alpha, superseded, or unknown is recomputed from `CanonState` at display time.
-/
import Dregg2.Games.PathOfAngels.Canon
import Dregg2.Tactics

namespace Dregg2.Games.PathOfAngels.FieldArchive

set_option autoImplicit false

/-! ## Exact receipt projection -/

/-- The durable, presentation-free provenance of one judged acquisition. -/
structure ArchiveEntry where
  artifact : ArtifactRef
  originKey : ReceiptKey
  mission : MissionSpec
  federationId : Digest32
  contentRoot : Digest32
  activationDigest : Digest32
  contentSession : Digest32
  contentEpoch : EpochId
deriving DecidableEq

/-- The sole entry producer.  In particular, there is no `ArtifactRef →
ArchiveEntry` acquisition function. -/
def ArchiveEntry.ofJudged (run : JudgedRun) : ArchiveEntry where
  artifact := run.receipt.mission.artifact
  originKey := run.receipt.key
  mission := run.receipt.mission
  federationId := run.receipt.federationId
  contentRoot := run.receipt.contentRoot
  activationDigest := run.receipt.activationDigest
  contentSession := run.receipt.contentSession
  contentEpoch := run.receipt.contentEpoch

theorem ArchiveEntry.ofJudged_exact_provenance (run : JudgedRun) :
    (ArchiveEntry.ofJudged run).artifact = run.receipt.mission.artifact ∧
    (ArchiveEntry.ofJudged run).originKey = run.receipt.key ∧
    (ArchiveEntry.ofJudged run).mission = run.receipt.mission ∧
    (ArchiveEntry.ofJudged run).federationId = run.receipt.federationId ∧
    (ArchiveEntry.ofJudged run).contentRoot = run.receipt.contentRoot ∧
    (ArchiveEntry.ofJudged run).activationDigest = run.receipt.activationDigest ∧
    (ArchiveEntry.ofJudged run).contentSession = run.receipt.contentSession ∧
    (ArchiveEntry.ofJudged run).contentEpoch = run.receipt.contentEpoch := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem ArchiveEntry.artifact_is_origin_mission_artifact (run : JudgedRun) :
    (ArchiveEntry.ofJudged run).artifact = (ArchiveEntry.ofJudged run).mission.artifact := rfl

theorem ArchiveEntry.activated_content_is_mission_content (run : JudgedRun) :
    (ArchiveEntry.ofJudged run).contentRoot =
        (ArchiveEntry.ofJudged run).mission.contentRoot ∧
      (ArchiveEntry.ofJudged run).activationDigest =
        (ArchiveEntry.ofJudged run).mission.activationDigest := by
  exact ⟨run.receipt.content_root_matches, run.receipt.activation_matches⟩

/-- The archived artifact was actually recorded by the judged receipt's checked
world transition; provenance is not merely matching metadata. -/
theorem ArchiveEntry.artifact_recorded_in_origin_world (run : JudgedRun) :
    (ArchiveEntry.ofJudged run).artifact ∈ run.receipt.postWorld.betaArtifacts :=
  run.receipt.records_exact_artifact

/-! ## Acquisition is a closed judged transition -/

structure ArchiveState where
  entries : Finset ArchiveEntry
deriving DecidableEq

def ArchiveState.empty : ArchiveState := ⟨∅⟩

/-- Acquisition records exactly the receipt projection of a closed registry run. -/
def acquire (run : JudgedRun) (state : ArchiveState) : ArchiveState where
  entries := insert (ArchiveEntry.ofJudged run) state.entries

/-- This relation is the authority surface.  Arbitrarily constructing an
`ArchiveState` value does not constitute a valid acquisition transition. -/
inductive Acquisition : ArchiveState → ArchiveState → Prop where
  | judged (run : JudgedRun) (before : ArchiveState) :
      Acquisition before (acquire run before)

/-- Every valid acquisition exposes the closed `JudgedRun` which caused it. -/
theorem acquisition_requires_judged_origin {before after : ArchiveState}
    (transition : Acquisition before after) :
    ∃ run : JudgedRun, after = acquire run before := by
  cases transition with
  | judged run state => exact ⟨run, rfl⟩

theorem acquisition_adds_exact_origin {before after : ArchiveState}
    (transition : Acquisition before after) :
    ∃ run : JudgedRun,
      ArchiveEntry.ofJudged run ∈ after.entries ∧
      (ArchiveEntry.ofJudged run).originKey = run.receipt.key ∧
      (ArchiveEntry.ofJudged run).mission = run.receipt.mission := by
  cases transition with
  | judged run state =>
      exact ⟨run, by simp [acquire], rfl, rfl⟩

/-- Existing acquisitions never disappear. -/
theorem acquire_monotone (run : JudgedRun) (state : ArchiveState) :
    state.entries ⊆ (acquire run state).entries := by
  intro entry hentry
  exact Finset.mem_insert_of_mem hentry

theorem Acquisition.monotone {before after : ArchiveState}
    (transition : Acquisition before after) : before.entries ⊆ after.entries := by
  cases transition
  exact acquire_monotone _ _

/-- Idempotence is exact-origin idempotence: the identical receipt projection is
already present after one acquisition. -/
theorem acquire_exact_origin_idempotent (run : JudgedRun) (state : ArchiveState) :
    acquire run (acquire run state) = acquire run state := by
  cases state with
  | mk entries => simp [acquire]

theorem acquire_contains_origin (run : JudgedRun) (state : ArchiveState) :
    ArchiveEntry.ofJudged run ∈ (acquire run state).entries := by
  simp [acquire]

/-- Equal artifact identity does not collapse two different receipt origins. -/
theorem same_artifact_distinct_receipts_remain_distinct (left right : JudgedRun)
    (_sameArtifact : left.receipt.mission.artifact = right.receipt.mission.artifact)
    (differentOrigin : left.receipt.key ≠ right.receipt.key) :
    ArchiveEntry.ofJudged left ≠ ArchiveEntry.ofJudged right := by
  intro hentry
  apply differentOrigin
  exact congrArg ArchiveEntry.originKey hentry

theorem acquire_two_origins_contains_both (left right : JudgedRun) (state : ArchiveState) :
    ArchiveEntry.ofJudged left ∈ (acquire right (acquire left state)).entries ∧
      ArchiveEntry.ofJudged right ∈ (acquire right (acquire left state)).entries := by
  simp [acquire]

/-! ## Canon-derived display status -/

/-- No display label is stored on `ArchiveEntry`; the current canon state is the
only source of beta/alpha/superseded truth.  `none` means the artifact is not in
this canon state's known population. -/
def displayStatus (canon : CanonState) (entry : ArchiveEntry) : Option CanonStatus :=
  canon.status entry.artifact

theorem displayStatus_agrees_with_canon (canon : CanonState) (entry : ArchiveEntry) :
    displayStatus canon entry = canon.status entry.artifact := rfl

theorem displayStatus_none_iff (canon : CanonState) (entry : ArchiveEntry) :
    displayStatus canon entry = none ↔ entry.artifact ∉ canon.known := by
  by_cases hknown : entry.artifact ∈ canon.known
  · by_cases hsuperseded : entry.artifact ∈ canon.superseded
    · simp [displayStatus, CanonState.status, hknown, hsuperseded]
    · by_cases halpha : entry.artifact ∈ canon.alpha
      · simp [displayStatus, CanonState.status, hknown, hsuperseded, halpha]
      · simp [displayStatus, CanonState.status, hknown, hsuperseded, halpha]
  · simp [displayStatus, CanonState.status, hknown]

theorem displayStatus_beta_iff (canon : CanonState) (entry : ArchiveEntry) :
    displayStatus canon entry = some .beta ↔ canon.isBeta entry.artifact = true := by
  by_cases hknown : entry.artifact ∈ canon.known
  · by_cases hsuperseded : entry.artifact ∈ canon.superseded
    · simp [displayStatus, CanonState.status, CanonState.isBeta, hknown, hsuperseded]
    · by_cases halpha : entry.artifact ∈ canon.alpha
      · simp [displayStatus, CanonState.status, CanonState.isBeta, hknown, hsuperseded, halpha]
      · simp [displayStatus, CanonState.status, CanonState.isBeta, hknown, hsuperseded, halpha]
  · simp [displayStatus, CanonState.status, CanonState.isBeta, hknown]

theorem displayStatus_alpha_iff (canon : CanonState) (entry : ArchiveEntry) :
    displayStatus canon entry = some .alpha ↔ canon.isAlpha entry.artifact = true := by
  by_cases hknown : entry.artifact ∈ canon.known
  · by_cases hsuperseded : entry.artifact ∈ canon.superseded
    · simp [displayStatus, CanonState.status, CanonState.isAlpha, hknown, hsuperseded]
    · by_cases halpha : entry.artifact ∈ canon.alpha
      · simp [displayStatus, CanonState.status, CanonState.isAlpha, hknown, hsuperseded, halpha]
      · simp [displayStatus, CanonState.status, CanonState.isAlpha, hknown, hsuperseded, halpha]
  · simp [displayStatus, CanonState.status, CanonState.isAlpha, hknown]

theorem displayStatus_superseded_iff (canon : CanonState) (entry : ArchiveEntry) :
    displayStatus canon entry = some .superseded ↔ entry.artifact ∈ canon.superseded := by
  by_cases hsuperseded : entry.artifact ∈ canon.superseded
  · have hknown : entry.artifact ∈ canon.known := canon.superseded_known hsuperseded
    simp [displayStatus, CanonState.status, hknown, hsuperseded]
  · by_cases hknown : entry.artifact ∈ canon.known
    · by_cases halpha : entry.artifact ∈ canon.alpha
      · simp [displayStatus, CanonState.status, hknown, hsuperseded, halpha]
      · simp [displayStatus, CanonState.status, hknown, hsuperseded, halpha]
    · simp [displayStatus, CanonState.status, hknown, hsuperseded]

theorem same_artifact_has_same_display_status (canon : CanonState)
    (left right : ArchiveEntry) (h : left.artifact = right.artifact) :
    displayStatus canon left = displayStatus canon right := by
  simp [displayStatus, h]

/-! ## Hostile boundary checks -/

/-- An unchecked representation-level insertion is intentionally not exported as
an acquisition operation.  This helper lets the negative theorem state the attack. -/
private def uncheckedInsert (entry : ArchiveEntry) (state : ArchiveState) : ArchiveState where
  entries := insert entry state.entries

/-- A fresh manually inserted record cannot masquerade as an `Acquisition` unless
there really exists a closed judged run with exactly that full provenance. -/
theorem unchecked_fresh_insert_requires_matching_judged_origin
    (entry : ArchiveEntry) (before : ArchiveState)
    (fresh : entry ∉ before.entries)
    (claimed : Acquisition before (uncheckedInsert entry before)) :
    ∃ run : JudgedRun, ArchiveEntry.ofJudged run = entry := by
  obtain ⟨run, hstate⟩ := acquisition_requires_judged_origin claimed
  have hin : entry ∈ (uncheckedInsert entry before).entries := by
    simp [uncheckedInsert]
  rw [hstate] at hin
  rcases Finset.mem_insert.mp hin with heq | hold
  · exact ⟨run, heq.symm⟩
  · exact (fresh hold).elim

/-- Model an untrusted UI request which supplies its own claimed label.  Sanitizing
the request deliberately ignores that label and asks canon. -/
def statusFromUntrustedClaim (canon : CanonState) (entry : ArchiveEntry)
    (_claimed : Option CanonStatus) : Option CanonStatus :=
  displayStatus canon entry

theorem forged_status_claim_is_ignored (canon : CanonState) (entry : ArchiveEntry)
    (claimed : Option CanonStatus) :
    statusFromUntrustedClaim canon entry claimed = canon.status entry.artifact := rfl

#assert_axioms ArchiveEntry.ofJudged_exact_provenance
#assert_axioms ArchiveEntry.activated_content_is_mission_content
#assert_axioms ArchiveEntry.artifact_recorded_in_origin_world
#assert_axioms acquisition_requires_judged_origin
#assert_axioms acquisition_adds_exact_origin
#assert_axioms acquire_monotone
#assert_axioms Acquisition.monotone
#assert_axioms acquire_exact_origin_idempotent
#assert_axioms same_artifact_distinct_receipts_remain_distinct
#assert_axioms displayStatus_agrees_with_canon
#assert_axioms displayStatus_none_iff
#assert_axioms displayStatus_beta_iff
#assert_axioms displayStatus_alpha_iff
#assert_axioms displayStatus_superseded_iff
#assert_axioms unchecked_fresh_insert_requires_matching_judged_origin
#assert_axioms forged_status_claim_is_ignored

end Dregg2.Games.PathOfAngels.FieldArchive
