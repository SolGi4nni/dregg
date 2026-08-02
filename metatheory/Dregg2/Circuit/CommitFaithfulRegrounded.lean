/-
# Dregg2.Circuit.CommitFaithfulRegrounded — the live rotated eight-lane commitment.

The legacy EffectVM continuity leaf is the four-node `hash_4_to_1` tree over
`[balLo, balHi, nonce, fields[0..8], capRoot, recordDigest]`.  The last felt is not an
independent user field: in Rust it is `compute_authority_digest_felt`, lane zero of
`bytes32_to_8_limbs(blake3(authority_residue_bytes(cell)))`.

The previous model merely read a scalar named `recordDigest`.  An extra field therefore produced a
free `LimbDecodeCollision`, and the advertised recovery assumed that no collision exists anywhere in
a finite hash.  This file removes both errors:

* `AuthorityResidue` names the exact semantic sections serialized by
  `cell/src/commitment.rs::authority_residue_bytes`, in their Rust order.  Variable sections already
  include their Rust option/tag/u64-length framing.  Lifecycle, delegation epoch, committed height,
  and heap root are deliberately not claimed to be in this byte string at HEAD: the live rotated
  v9+ commitment carries them as separate named limbs.
* `DeployedCell.toValue` is the canonical abstract boundary.  `authorityInput` is domain-separated:
  a canonical value hashes its authority-residue object; a malformed/open record hashes the entire
  `Value` in an `abstract` domain.  Thus the total abstract model cannot erase an unnamed field.
* Equal clear limbs and equal authority preimages determine the whole `Value`.  Hence a collision of
  the 13-limb leaf reduces only to a genuine authority-fold collision or a genuine `h4` collision.
* Whole-kernel, nonce, and replay theorems are reduction-form.  The recovery event is the local
  adversary-failure event, which is inhabited on honest equal openings; no theorem assumes global
  nonexistence of collisions.

The legacy analysis remains as a diagnostic, but the keystone surface is the live 184-limb rotated
path.  `RotatedCell` and `rotatedLimb` place the authority octet at `[24,12..18]`, the faithful cap
and heap roots in their deployed groups, lifecycle/epoch/height at `29/30/31`, and publish the
eight-output `wireCommitR8`.  `CH_faithful8` uses a lossless tuple serialization only to fit the
older scalar `recStateCommit` interface; it adds no hash assumption and projects no lane.

Consequently the kernel/no-replay/transfer keystones return only a genuine collision of the full
eight-lane authority digest, the 184-limb wide chain, or an outer state-tree primitive.  A collision
visible only in legacy lane zero is no longer on their break surface.

⚑⚑ **2026-08-01 — `FaithfulBreak` IS FREE AT DEPLOYED PARAMETERS.**  Its first disjunct is
`SpongeCollision compressN`, a global existential that pigeonhole supplies at every field-bounded
sponge, so `k = k' ∨ FaithfulBreak …` holds by its right branch alone and
`recStateCommit_binds_kernel_faithful` — which `Circuit/Freshness`'s header calls "the live binding
consumer" for the deployed residue-fold leaf — said nothing at deployed parameters.  All five of its
disjuncts are that shape, so narrowing one would not have helped, and `FaithfulBreak` cannot be
narrowed IN PLACE at all: it is defined without reference to the opening `(k, k', t)`, and a
per-instance residual must name that opening.  §4 therefore adds a DIFFERENT predicate,
`FaithfulCommitColl` (= `StateCommitLeafRegrounded.RecStateCommitColl` at the faithful leaf), with
`_or_collides` / `_of_noColl` forms for the whole-kernel binding, the nonce binding, the surface, and
cross-turn no-replay; the leaf disjuncts still cash out per-instance to a genuine eight-lane
authority collision or a genuine wide-chain collision (`cellLeafColl_faithful8_reduces`).  The port
also DROPS the `Poseidon2Width8` carrier at `recStateCommit_binds_kernel_faithful_or_collides` —
⚠ NOT at `cellLeafColl_faithful8_reduces`, which still binds `hW : Poseidon2Width8 permW` and applies
it twice; an earlier draft of this header claimed the drop there.

⚑⚑ **2026-08-01 (later the same day) — `FaithfulBreak` IS NARROWED, AND THE HEADLINE HAS A TWIN.**
The paragraph above is kept because its diagnosis was right, but its CONCLUSION ("`FaithfulBreak`
cannot be narrowed IN PLACE at all") was wrong, and acting on it left the file's biggest theorem
free. What was actually true is that `FaithfulBreak` could not be narrowed WITHOUT CHANGING ITS
ARITY: a per-instance leg must name the opening, so the definition takes `(k, k', t)`. It now does.

* **`FaithfulBreak` now names a pair in EVERY leg** (not only the sponge one the brief asked for —
  all five disjuncts were the same shape, so narrowing one would have left the dichotomy free).
  The sponge leg is `FrameCNColl` at the TWO ORDERED FRAME-LEAF LISTS of this opening; the combiner
  and node legs are `CompressColl` at the argument quadruples the extraction visits; the two leaf
  legs are `FaithfulLeafBreak` — the deployed eight-lane authority digest / wide chain AT THE NAMED
  TAGGED PREIMAGES, via `cellLeafColl_faithful8_reduces`. `noFaithfulBreak_diag` REFUTES the whole
  disjunction on the diagonal at EVERY deployment; `faithfulBreak_refutable` FIRES it at the
  all-constant one; `faithfulBreak_sharper_than_global` shows both at ONE sponge.
* **The pre-narrowing shape is RETAINED as `FaithfulBreakGlobal`, WITH TEETH** —
  `faithfulBreakGlobal_free_of_fieldBounded` PROVES it outright at every field-bounded sponge and
  `orFaithfulBreakGlobal_iff_True` proves `P ∨ FaithfulBreakGlobal … ↔ True`. That refutation is the
  tombstone: the old shape is not merely deprecated here, it is machine-checked to say nothing. The
  three consumers that genuinely are global→global (`stateBreak_faithful_reduces`,
  `recStateCommit_binds_kernel_faithful_global`, `transfer_circuit_full_sound_faithful`) keep it and
  are labelled `⚠ BRIDGE ONLY`; every other consumer is ported in place.
* **`transfer_circuit_full_sound_faithful` HAS A TWIN.** `transfer_circuit_full_sound_faithful_or_collides`
  returns `TransferSpec k t k' ∨ TransferFaithfulColl …`, the residual being the frame sponge at
  `(k, k')` over THIS turn's carrier and the moved node at `(k'.cell, recTransfer k.cell …)` — the
  two raw layers the proof visits, at the pairs it visits them at, through
  `StateCommitLeafRegrounded.frameDigest_binds_or_collides` / `movedDigest_binds_or_collides`
  instead of `StateCommitReduce`'s free `_orBreak` twins. Its docstring no longer sells the absent
  injectivity premise as a strength. `FaithfulCommitSurface.commit_binds_nonce` likewise gained
  `commit_binds_nonce_or_collides` / `_of_noColl`.
* Teeth for the transfer residual: `noTransferFaithfulColl_of_spec` (SATISFIABLE at EVERY deployment
  — an honest post-state never trips it), `transferFaithfulColl_refutable` (it FIRES on the minted
  bystander cell at a lossy wide permutation), `noTransferFaithfulColl_not_provable`.
* `commit_binds_nonce_faithful_unconditional_false` is the LOAD-BEARING canary for the nonce twin.
  ⚠ `recStateCommit_binds_kernel_faithful_unconditional_false` does NOT cover it: that pair differs
  only in `nullifiers`, so its agent nonces AGREE and it refutes nothing about the nonce conclusion.
  The new one needed a `FinKernelState` with a NON-EMPTY `CanonMap` (`finNonce`), which the tree did
  not have; it is now here and reusable.

⚑⚑ **2026-08-01 (third pass) — THE BLOCKER PRINTED HERE WAS FALSE; THE CANARY IS LANDED.** The
paragraph this replaces said `transfer_circuit_full_sound_faithful_of_noColl` could not get an
`*_unconditional_false` canary because the witness needs "an INHABITANT of `RestHashIffFrameFin`,
which the tree still does not have (`Verify/RestFrameFiniteSupportSuccessor` proves the predicate
satisfiable-and-refutable, not inhabited by a named `RH`)". The tree has had one since 2026-07-31:
`Verify.RestFrameFiniteSupportSuccessor.restHashIffFrameFin_satisfiable` is a CLOSED theorem of type
`RestHashIffFrameFin (RH_fin Reference.refSponge)`. It NAMES the rest-hash and proves the predicate
OF it, carrying no hypothesis at all (`Poseidon2Binding.Reference.refSponge_CR` is itself a closed
proof, not a binder) — "SATISFIABLE" there IS the inhabitant. The blocker was written from that
file's section HEADINGS rather than its statements, and it cost this canary a pass.
* The ONE true half of it is kept: dropping `hRest` would NOT be a fix, because refuting a
  weaker-hypothesis statement does not refute the stronger one. So
  `transfer_circuit_full_sound_faithful_unconditional_false` keeps `RestHashIffFrameFin RH` INSIDE
  the quantifier and refutes the statement WITH it; the only thing deleted is `hno`.
* **The witness is `StateCommit`'s OWN reference forgery at a lossy deployment.** `finKS0` /
  `finForgedThirdCell` exhibit `kS0` and `forgedThirdCell` as `denote` images
  (`denote_finKS0` / `denote_finForgedThirdCell`) — that is what supplies the two
  `FiniteRepresentable` hypotheses, and it is the piece `finNonce` could not supply, since the nonce
  canary's states differ in a CELL but are not the transfer triple.
  `accountsWF_kS0` / `accountsWF_forgedThirdCell` supply the structural pair, and
  `satisfiedS_forgedThirdCell_at_lossy` builds the full satisfying assignment: the nine transfer
  gates by `decide` (`StateCommit`'s own `#guard` already records that `transferCircuit` ACCEPTS this
  forgery), `cSRestFrame` from `restHashIffFrameFin_satisfiable`'s REVERSE direction at the eighteen
  frozen non-cell components, `cSFrameReuse` / `cSMovedBind` from the collapsed constant primitives.
* ⚑ **THE PAIRING IS AT ONE AND THE SAME INSTANCE.** `transferFaithfulColl_refutable` already FIRES
  the residual at exactly this triple — `constantAuthorityFold8` / `constantWide` /
  `rotatedContextDemoIroot`, `kS0` / `forgedThirdCell` / `goodTurnS`. Read together the two teeth say:
  WITHOUT `hno` the conclusion is FALSE here, and `hno` is PRECISELY what this witness violates. That
  co-location is itself a theorem — `transfer_canary_and_residual_at_one_instance` — not a sentence,
  so an edit that moves either side stops elaborating instead of quietly decoupling them.
* ⚠ The `RH` the canary picks is the REFERENCE pole (`Encodable.encode`), the strongest rest hash the
  tree has, so the rest-frame gate genuinely bites and the forgery has to respect all eighteen frozen
  components. All the lossiness is on the CELL side (`constantWide` collapses `wireCommitR8`). A
  canary that had picked a weak `RH` would be refuting the statement by disabling the hypothesis it
  is supposed to keep.
* This file now IMPORTS `Dregg2.Verify.RestFrameFiniteSupportSuccessor` (a `Circuit` module reaching
  UP into `Verify`) to route through the one existing witness rather than re-proving it locally: a
  per-site copy of a satisfiability proof is exactly the second shape the campaign's rules forbid.
  No cycle — nothing in that module's cone imports this one.

No `sorry`, `admit`, `native_decide`, or new axiom.  Every theorem is audited below.
-/
import Dregg2.Tactics
import Dregg2.Circuit.CommitDifferential
import Dregg2.Circuit.StateCommitReduce
import Dregg2.Circuit.StateCommitLeafRegrounded
import Dregg2.Circuit.SpongeCollisionShirk
import Dregg2.Circuit.HashFloorHonesty
import Dregg2.Circuit.OodRomBound
import Dregg2.Circuit.Emit.EffectVmEmitRotationR
import Dregg2.Circuit.Emit.RotatedLayout
import Dregg2.Exec.RecordKernel
import Dregg2.Exec.EffectTransfer
-- ⚑ 2026-08-01: for `restHashIffFrameFin_satisfiable`, the CLOSED, NAMED inhabitant of
-- `RestHashIffFrameFin` the transfer canary's `cSRestFrame` gate needs.  Routed through the ONE
-- existing witness rather than re-proving it here (a per-site copy would be a second shape).
import Dregg2.Verify.RestFrameFiniteSupportSuccessor
import Mathlib.Data.List.OfFn
import Mathlib.Logic.Encodable.Pi

namespace Dregg2.Circuit.CommitFaithfulRegrounded

open Dregg2.Exec (CellId FieldName Value Turn RecordKernelState balOf balanceField recTransfer)
open Dregg2.Exec.EffectTransfer
open Dregg2.Circuit.CommitDifferential (effectVmCommit)
open Dregg2.Circuit.StateCommit
open Dregg2.Circuit.RestFrameFin (FiniteRepresentable RestHashIffFrameFin)
open Dregg2.Circuit.Transfer
open Dregg2.Crypto.ProbCrypto (winProb)
open Dregg2.Circuit.CollisionReduce (CellCollision SpongeCollision CompressCollision)
-- ⚑ `recStateCommit_binds_kernel_orBreak` is NO LONGER OPENED (2026-08-01): after the port this
-- file threads no `_orBreak` BINDING twin at term level.  `StateBreakP` survives only inside the
-- two retained `⚠ BRIDGE ONLY` reductions.  (`StateCommitReduceRaw`'s header still lists this module
-- among the three that thread them — stale as of this commit, and its to-fix.)
open Dregg2.Circuit.StateCommitReduce (StateBreakP recStateCommit_binds_kernel_or_collidesFin)
-- ⚑ the PER-INSTANCE residual vocabulary (2026-08-01, the free-disjunct port).
open Dregg2.Circuit.StateCommitLeafRegrounded (CellLeafColl RecStateCommitColl
  noRecStateCommitColl_diag CompressColl FrameCNColl FrameLeafColl FrameColl MovedLeafColl
  MovedColl CellDigestColl frameLeaves frameDigest_binds_or_collides movedDigest_binds_or_collides)
open Dregg2.Circuit.SpongeCollisionShirk (FieldBounded spongeCollision_of_fieldBounded)

set_option autoImplicit false

/-! ## 1. The Rust authority-residue preimage and canonical abstract cell. -/

/-- A byte section in the Rust serializer.  Fixed-width sections contain their bytes directly;
variable-width sections contain the exact option/tag/u64-length framing written by Rust. -/
abbrev ByteSection := List Nat

/-- The semantic sections of `authority_residue_bytes`, in serialization order.

`identity` is `cell.id || public_key || token_id`; `permissions` contains all eight authorization
tags and every custom permission VK; `delegation` contains source/epoch/refresh/staleness/snapshot;
the final four fields are the Swiss/refcount/overflow/system side-table roots. -/
structure AuthorityResidue where
  domainPrefix : ByteSection
  identity : ByteSection
  mode : ByteSection
  permissions : ByteSection
  verificationKey : ByteSection
  delegate : ByteSection
  delegation : ByteSection
  program : ByteSection
  overflowFields : ByteSection
  fieldVisibility : ByteSection
  commitments : ByteSection
  provedState : ByteSection
  swissRoot : ByteSection
  refcountRoot : ByteSection
  fieldsRootBytes : ByteSection
  systemRootsBytes : ByteSection
  deriving Repr

/-- The exact concatenation order fed to BLAKE3 by `authority_residue_bytes`. -/
def AuthorityResidue.toBytes (r : AuthorityResidue) : List Nat :=
  r.domainPrefix ++ r.identity ++ r.mode ++ r.permissions ++ r.verificationKey ++ r.delegate ++
    r.delegation ++ r.program ++ r.overflowFields ++ r.fieldVisibility ++ r.commitments ++
    r.provedState ++ r.swissRoot ++ r.refcountRoot ++ r.fieldsRootBytes ++ r.systemRootsBytes

/-- Preserve an already-framed byte section inside the open `Value` model without pretending it is
a field element.  Repeated `byte` entries retain order and multiplicity. -/
def byteSectionValue (xs : ByteSection) : Value :=
  .record (xs.map (fun b => ("byte", .dig b)))

/-- The canonical, named authority object stored at the Lean/Rust boundary.  The order is the Rust
serialization order; `toBytes` above is the byte-level denotation used by the real fold. -/
def AuthorityResidue.toValue (r : AuthorityResidue) : Value :=
  .record [("prefix", byteSectionValue r.domainPrefix), ("identity", byteSectionValue r.identity),
    ("mode", byteSectionValue r.mode), ("permissions", byteSectionValue r.permissions),
    ("verificationKey", byteSectionValue r.verificationKey),
    ("delegate", byteSectionValue r.delegate), ("delegation", byteSectionValue r.delegation),
    ("program", byteSectionValue r.program), ("overflowFields", byteSectionValue r.overflowFields),
    ("fieldVisibility", byteSectionValue r.fieldVisibility),
    ("commitments", byteSectionValue r.commitments), ("provedState", byteSectionValue r.provedState),
    ("swissRoot", byteSectionValue r.swissRoot), ("refcountRoot", byteSectionValue r.refcountRoot),
    ("fieldsRoot", byteSectionValue r.fieldsRootBytes),
    ("systemRootsDigest", byteSectionValue r.systemRootsBytes)]

private def emptyAuthorityResidue : AuthorityResidue where
  domainPrefix := []
  identity := []
  mode := []
  permissions := []
  verificationKey := []
  delegate := []
  delegation := []
  program := []
  overflowFields := []
  fieldVisibility := []
  commitments := []
  provedState := []
  swissRoot := []
  refcountRoot := []
  fieldsRootBytes := []
  systemRootsBytes := []

-- The exact serializer preimage moves when a permission-tag/custom-VK section moves.
#guard emptyAuthorityResidue.toBytes !=
  ({ emptyAuthorityResidue with permissions := [1, 7, 9] }).toBytes

/-- A canonical cell preimage for the legacy 13-limb EffectVM tree.  The authority object denotes
the BLAKE3 preimage; the other fields are the twelve clear commitment limbs before balance split. -/
structure DeployedCell where
  balance : Int
  nonce : Int
  f0 : Int
  f1 : Int
  f2 : Int
  f3 : Int
  f4 : Int
  f5 : Int
  f6 : Int
  f7 : Int
  capRoot : Int
  authorityResidue : Value
  deriving Repr

def DeployedCell.field (d : DeployedCell) : Fin 8 → Int
  | 0 => d.f0 | 1 => d.f1 | 2 => d.f2 | 3 => d.f3
  | 4 => d.f4 | 5 => d.f5 | 6 => d.f6 | 7 => d.f7

/-- The one canonical top-level `Value` layout accepted as a deployed cell.  Exact layout matters:
extra/reordered/duplicate fields are not silently discarded; they enter the fallback hash domain. -/
def DeployedCell.toValue (d : DeployedCell) : Value :=
  .record [("balance", .int d.balance), ("nonce", .int d.nonce),
    ("f0", .int d.f0), ("f1", .int d.f1), ("f2", .int d.f2), ("f3", .int d.f3),
    ("f4", .int d.f4), ("f5", .int d.f5), ("f6", .int d.f6), ("f7", .int d.f7),
    ("capRoot", .int d.capRoot), ("authorityResidue", d.authorityResidue)]

/-- Rust's 30-bit split modulus (`lo = balance & 0x3fff_ffff`, `hi = balance >> 30`). -/
def splitMod : Int := 1073741824

def balLoLimb (v : Value) : Int := balOf v % splitMod
def balHiLimb (v : Value) : Int := balOf v / splitMod
def nonceLimb (v : Value) : Int := nonceOf v

def fieldName : Fin 8 → FieldName
  | 0 => "f0" | 1 => "f1" | 2 => "f2" | 3 => "f3"
  | 4 => "f4" | 5 => "f5" | 6 => "f6" | 7 => "f7"

def fieldLimbs (v : Value) : Fin 8 → Int := fun i => (v.scalar (fieldName i)).getD 0
def capRootLimb (v : Value) : Int := (v.scalar "capRoot").getD 0
def authorityResidueValue (v : Value) : Value :=
  (v.field "authorityResidue").getD (.record [])

/-- Reconstruct the canonical deployed view from named reads. -/
def decodedCell (v : Value) : DeployedCell where
  balance := balOf v
  nonce := nonceOf v
  f0 := fieldLimbs v 0
  f1 := fieldLimbs v 1
  f2 := fieldLimbs v 2
  f3 := fieldLimbs v 3
  f4 := fieldLimbs v 4
  f5 := fieldLimbs v 5
  f6 := fieldLimbs v 6
  f7 := fieldLimbs v 7
  capRoot := capRootLimb v
  authorityResidue := authorityResidueValue v

/-- Exact canonicality at the abstract/deployed boundary. -/
def CanonicalCell (v : Value) : Prop := v = (decodedCell v).toValue

/-- Canonicality of the *deployed Rust* subset: the authority object itself is the named encoding of
an `AuthorityResidue`, not merely an arbitrary nested `Value`. -/
def CanonicalRustCell (v : Value) : Prop :=
  ∃ d : DeployedCell, ∃ r : AuthorityResidue,
    d.authorityResidue = r.toValue ∧ v = d.toValue

/-- The fold input is tagged.  `rust residue` is realized by
`bytes32_to_8_limbs(blake3(AuthorityResidue.toBytes residue))[0]`; `abstract wholeValue` is a
separate conservative domain for malformed/open abstract values. -/
inductive AuthorityInput where
  | rust : Value → AuthorityInput
  | abstract : Value → AuthorityInput
  deriving Repr

/-- Total, lossless boundary decode.  Canonical deployed values feed only the authority residue to
Rust's fold.  Everything else feeds the whole `Value` under a distinct tag, closing the old free
extra-field collision without changing the deployed canonical path. -/
noncomputable def authorityInput (v : Value) : AuthorityInput :=
  letI : Decidable (CanonicalCell v) := Classical.propDecidable _
  if CanonicalCell v then .rust (authorityResidueValue v) else .abstract v

/-- The scalar Rust fold (`compute_authority_digest_felt`).  Its concrete realization is BLAKE3
followed by faithful eight-limb decoding and projection to lane zero. -/
abbrev AuthorityFold := AuthorityInput → Int

/-- The full deployed authority digest (`compute_authority_digest_8`). -/
abbrev AuthorityFold8 := AuthorityInput → Fin 8 → Int

/-- The legacy scalar projection used by the 13-limb tree. -/
def lane0Fold (fold8 : AuthorityFold8) : AuthorityFold := fun x => fold8 x 0

/-- A lane-zero collision that the other seven deployed authority lanes distinguish.  The Rust
differential suite contains such a locked/open pair; this is why the 13-limb prefix alone is not the
128-bit binding surface. -/
def LegacyLane0OnlyCollision (fold8 : AuthorityFold8) : Prop :=
  ∃ x y : AuthorityInput, x ≠ y ∧ fold8 x 0 = fold8 y 0 ∧ ∃ i : Fin 8, fold8 x i ≠ fold8 y i

noncomputable def recordDigestLimb (fold : AuthorityFold) (v : Value) : Int := fold (authorityInput v)

/-- The faithful legacy leaf: exactly the differential-pinned Rust `CellState::compute_commitment`
tree, with `recordDigest` computed from the residue rather than read as a free scalar. -/
noncomputable def CH_faithful (fold : AuthorityFold) (h4 : Int → Int → Int → Int → Int)
    (_c : CellId) (v : Value) : Int :=
  effectVmCommit h4 (balLoLimb v) (balHiLimb v) (nonceLimb v) (fieldLimbs v)
    (capRootLimb v) (recordDigestLimb fold v)

/-- Direct deployed denotation on a canonical cell, useful both for the differential statement and
computable non-vacuity witnesses. -/
def deployedLeaf (fold : AuthorityFold) (h4 : Int → Int → Int → Int → Int) (d : DeployedCell) : Int :=
  effectVmCommit h4 (d.balance % splitMod) (d.balance / splitMod) d.nonce d.field d.capRoot
    (fold (.rust d.authorityResidue))

theorem DeployedCell.ext' {d e : DeployedCell}
    (hbalance : d.balance = e.balance) (hnonce : d.nonce = e.nonce)
    (hf0 : d.f0 = e.f0) (hf1 : d.f1 = e.f1) (hf2 : d.f2 = e.f2) (hf3 : d.f3 = e.f3)
    (hf4 : d.f4 = e.f4) (hf5 : d.f5 = e.f5) (hf6 : d.f6 = e.f6) (hf7 : d.f7 = e.f7)
    (hcap : d.capRoot = e.capRoot) (hauth : d.authorityResidue = e.authorityResidue) : d = e := by
  cases d
  cases e
  simp_all

theorem DeployedCell.toValue_canonical (d : DeployedCell) : CanonicalCell d.toValue := by
  cases d
  simp [CanonicalCell, decodedCell, DeployedCell.toValue, fieldLimbs, fieldName, capRootLimb,
    authorityResidueValue, balOf, balanceField, Value.scalar, Value.field, nonceOf, nonceField]

theorem authorityInput_of_canonicalRustCell {v : Value} (h : CanonicalRustCell v) :
    ∃ r : AuthorityResidue, authorityInput v = .rust r.toValue := by
  classical
  rcases h with ⟨d, r, hdr, rfl⟩
  refine ⟨r, ?_⟩
  have hc : CanonicalCell d.toValue := DeployedCell.toValue_canonical d
  simp only [authorityInput, if_pos hc]
  simp [DeployedCell.toValue, authorityResidueValue, hdr, Value.field]

theorem CH_faithful_toValue (fold : AuthorityFold) (h4 : Int → Int → Int → Int → Int)
    (c : CellId) (d : DeployedCell) :
    CH_faithful fold h4 c d.toValue = deployedLeaf fold h4 d := by
  classical
  have hcanon := DeployedCell.toValue_canonical d
  have hfields : fieldLimbs d.toValue = d.field := by
    funext i
    fin_cases i <;>
      simp [fieldLimbs, fieldName, DeployedCell.toValue, DeployedCell.field,
        Value.scalar, Value.field]
  simp only [CH_faithful, deployedLeaf, recordDigestLimb, authorityInput, if_pos hcanon]
  rw [hfields]
  simp [DeployedCell.toValue, authorityResidueValue, balLoLimb, balHiLimb, nonceLimb,
    capRootLimb, balOf, balanceField, Value.scalar, Value.field, nonceOf, nonceField]

#assert_axioms DeployedCell.ext'
#assert_axioms DeployedCell.toValue_canonical
#assert_axioms authorityInput_of_canonicalRustCell
#assert_axioms CH_faithful_toValue

/-! ### Non-vacuity: the residue is load-bearing in the exact Rust tree. -/

private def h4Demo : Int → Int → Int → Int → Int :=
  fun a b c d => a * 1000000000 + b * 1000000 + c * 1000 + d

private def foldDemo : AuthorityFold
  | .rust v =>
      match v.field "mode" with
      | some (.record ((_, .dig b) :: _)) => (b : Int) + 41
      | _ => 41
  | .abstract _ => -1

private def residueDemo (mode : Nat) : Value :=
  ({ emptyAuthorityResidue with mode := [mode] }).toValue

private def cellDemo (mode : Nat) : DeployedCell where
  balance := 5
  nonce := 7
  f0 := 10
  f1 := 11
  f2 := 12
  f3 := 13
  f4 := 14
  f5 := 15
  f6 := 16
  f7 := 17
  capRoot := 100
  authorityResidue := residueDemo mode

#guard deployedLeaf foldDemo h4Demo (cellDemo 0)
  == effectVmCommit h4Demo 5 0 7 (fun i => 10 + (i : Int)) 100 41
#guard deployedLeaf foldDemo h4Demo (cellDemo 0) != deployedLeaf foldDemo h4Demo (cellDemo 1)

/-! ## 2. Decode injectivity and honest collision reductions. -/

def SameSurface (v w : Value) : Prop :=
  balLoLimb v = balLoLimb w ∧ balHiLimb v = balHiLimb w ∧ nonceLimb v = nonceLimb w
    ∧ fieldLimbs v 0 = fieldLimbs w 0 ∧ fieldLimbs v 1 = fieldLimbs w 1
    ∧ fieldLimbs v 2 = fieldLimbs w 2 ∧ fieldLimbs v 3 = fieldLimbs w 3
    ∧ fieldLimbs v 4 = fieldLimbs w 4 ∧ fieldLimbs v 5 = fieldLimbs w 5
    ∧ fieldLimbs v 6 = fieldLimbs w 6 ∧ fieldLimbs v 7 = fieldLimbs w 7
    ∧ capRootLimb v = capRootLimb w

/-- The G3 close.  Clear-limb equality plus authority-preimage equality determines the entire
abstract `Value`, including malformed/open records (which live in the tagged fallback domain). -/
theorem sameSurface_authorityInput_injective {v w : Value}
    (hs : SameSurface v w) (ha : authorityInput v = authorityInput w) : v = w := by
  classical
  rcases hs with ⟨hlo, hhi, hnonce, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hcap⟩
  by_cases hv : CanonicalCell v
  · by_cases hw : CanonicalCell w
    · have hres : authorityResidueValue v = authorityResidueValue w := by
        simpa only [authorityInput, if_pos hv, if_pos hw, AuthorityInput.rust.injEq] using ha
      have hbal : balOf v = balOf w := by
        rw [← Int.emod_add_mul_ediv (balOf v) splitMod,
          ← Int.emod_add_mul_ediv (balOf w) splitMod]
        change balOf v % splitMod = balOf w % splitMod at hlo
        change balOf v / splitMod = balOf w / splitMod at hhi
        rw [hlo, hhi]
      have hdecoded : decodedCell v = decodedCell w :=
        DeployedCell.ext' hbal hnonce hf0 hf1 hf2 hf3 hf4 hf5 hf6 hf7 hcap hres
      rw [hv, hw, hdecoded]
    · simp only [authorityInput, if_pos hv, if_neg hw] at ha
      cases ha
  · by_cases hw : CanonicalCell w
    · simp only [authorityInput, if_neg hv, if_pos hw] at ha
      cases ha
    · simpa only [authorityInput, if_neg hv, if_neg hw, AuthorityInput.abstract.injEq] using ha

#assert_axioms sameSurface_authorityInput_injective

/-- A genuine collision in `compute_authority_digest_felt`'s complete, tagged preimage domain. -/
def AuthorityDigestCollision (fold : AuthorityFold) : Prop :=
  ∃ x y : AuthorityInput, x ≠ y ∧ fold x = fold y

theorem legacyLane0OnlyCollision_breaks_legacy (fold8 : AuthorityFold8)
    (h : LegacyLane0OnlyCollision fold8) : AuthorityDigestCollision (lane0Fold fold8) := by
  rcases h with ⟨x, y, hne, hzero, _⟩
  exact ⟨x, y, hne, hzero⟩

#assert_axioms legacyLane0OnlyCollision_breaks_legacy

/-- A genuine collision in one `hash_4_to_1` node. -/
def Compress4Collision (h4 : Int → Int → Int → Int → Int) : Prop :=
  ∃ a b c d a' b' c' d' : Int,
    ¬ (a = a' ∧ b = b' ∧ c = c' ∧ d = d') ∧ h4 a b c d = h4 a' b' c' d'

/-- Tree tracing: unequal 13-limb inputs with equal roots exhibit an actual `h4` collision. -/
theorem effectVmCommit_collision_of_ne (h4 : Int → Int → Int → Int → Int)
    (bl bh n : Int) (f : Fin 8 → Int) (cr rd : Int)
    (bl' bh' n' : Int) (f' : Fin 8 → Int) (cr' rd' : Int)
    (hne : ¬ (bl = bl' ∧ bh = bh' ∧ n = n'
      ∧ f 0 = f' 0 ∧ f 1 = f' 1 ∧ f 2 = f' 2 ∧ f 3 = f' 3
      ∧ f 4 = f' 4 ∧ f 5 = f' 5 ∧ f 6 = f' 6 ∧ f 7 = f' 7
      ∧ cr = cr' ∧ rd = rd'))
    (heq : effectVmCommit h4 bl bh n f cr rd = effectVmCommit h4 bl' bh' n' f' cr' rd') :
    Compress4Collision h4 := by
  simp only [effectVmCommit] at heq
  by_cases hr : (h4 bl bh n (f 0) = h4 bl' bh' n' (f' 0)
      ∧ h4 (f 1) (f 2) (f 3) (f 4) = h4 (f' 1) (f' 2) (f' 3) (f' 4)
      ∧ h4 (f 5) (f 6) (f 7) cr = h4 (f' 5) (f' 6) (f' 7) cr'
      ∧ rd = rd')
  · obtain ⟨he1, he2, he3, herd⟩ := hr
    by_cases ha : (bl = bl' ∧ bh = bh' ∧ n = n' ∧ f 0 = f' 0)
    · by_cases hb : (f 1 = f' 1 ∧ f 2 = f' 2 ∧ f 3 = f' 3 ∧ f 4 = f' 4)
      · by_cases hc : (f 5 = f' 5 ∧ f 6 = f' 6 ∧ f 7 = f' 7 ∧ cr = cr')
        · exfalso
          apply hne
          obtain ⟨e0, e1, e2, e3⟩ := ha
          obtain ⟨e4, e5, e6, e7⟩ := hb
          obtain ⟨e8, e9, e10, e11⟩ := hc
          exact ⟨e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, herd⟩
        · exact ⟨_, _, _, _, _, _, _, _, hc, he3⟩
      · exact ⟨_, _, _, _, _, _, _, _, hb, he2⟩
    · exact ⟨_, _, _, _, _, _, _, _, ha, he1⟩
  · exact ⟨_, _, _, _, _, _, _, _, hr, heq⟩

#assert_axioms effectVmCommit_collision_of_ne

def SameLimbs (fold : AuthorityFold) (v w : Value) : Prop :=
  SameSurface v w ∧ recordDigestLimb fold v = recordDigestLimb fold w

/-- Retained as a diagnostic name, but no longer a free gap: every such collision exhibits a real
authority-fold collision. -/
def LimbDecodeCollision (fold : AuthorityFold) (v w : Value) : Prop :=
  v ≠ w ∧ SameLimbs fold v w

theorem limbDecodeCollision_reduces (fold : AuthorityFold) {v w : Value}
    (h : LimbDecodeCollision fold v w) : AuthorityDigestCollision fold := by
  rcases h with ⟨hne, hs, hd⟩
  by_cases ha : authorityInput v = authorityInput w
  · exact absurd (sameSurface_authorityInput_injective hs ha) hne
  · exact ⟨authorityInput v, authorityInput w, ha, hd⟩

#assert_axioms limbDecodeCollision_reduces

/-- The faithful leaf collision has exactly two honest causes: the authority fold collides, or a
node of the deployed `h4` tree collides.  There is no unconditional decode-gap branch. -/
theorem cellCollision_faithful_reduces (fold : AuthorityFold)
    (h4 : Int → Int → Int → Int → Int) :
    CellCollision (CH_faithful fold h4) → AuthorityDigestCollision fold ∨ Compress4Collision h4 := by
  rintro ⟨c, v, w, hne, heq⟩
  simp only [CH_faithful] at heq
  by_cases hs : SameSurface v w
  · by_cases ha : authorityInput v = authorityInput w
    · exact absurd (sameSurface_authorityInput_injective hs ha) hne
    · by_cases hd : recordDigestLimb fold v = recordDigestLimb fold w
      · exact Or.inl ⟨authorityInput v, authorityInput w, ha, hd⟩
      · have hneLimbs : ¬ (SameSurface v w ∧
            recordDigestLimb fold v = recordDigestLimb fold w) := fun h => hd h.2
        exact Or.inr (effectVmCommit_collision_of_ne h4
          (balLoLimb v) (balHiLimb v) (nonceLimb v) (fieldLimbs v)
          (capRootLimb v) (recordDigestLimb fold v)
          (balLoLimb w) (balHiLimb w) (nonceLimb w) (fieldLimbs w)
          (capRootLimb w) (recordDigestLimb fold w)
          (by simpa only [SameSurface, and_assoc] using hneLimbs) heq)
  · have hneLimbs : ¬ (SameSurface v w ∧
        recordDigestLimb fold v = recordDigestLimb fold w) := fun h => hs h.1
    exact Or.inr (effectVmCommit_collision_of_ne h4
      (balLoLimb v) (balHiLimb v) (nonceLimb v) (fieldLimbs v)
      (capRootLimb v) (recordDigestLimb fold v)
      (balLoLimb w) (balHiLimb w) (nonceLimb w) (fieldLimbs w)
      (capRootLimb w) (recordDigestLimb fold w)
      (by simpa only [SameSurface, and_assoc] using hneLimbs) heq)

#assert_axioms cellCollision_faithful_reduces

/-! ## 3. The deployed rotated 184-limb / eight-output surface.

The legacy leaf above remains only as the differential-pinned diagnostic.  The binding consumer
below models the live wide route: the authority digest occupies all eight deployed lanes
`[24,12..18]`; the capability and heap roots occupy their eight-lane groups; lifecycle,
delegation epoch, and committed height remain explicit scalar limbs; and `wireCommitR8` publishes
the final eight-felt carrier. -/

abbrev Digest8 := Fin 8 → Int

def digest8Value (d : Digest8) : Value :=
  .record [("lane0", .int (d 0)), ("lane1", .int (d 1)), ("lane2", .int (d 2)),
    ("lane3", .int (d 3)), ("lane4", .int (d 4)), ("lane5", .int (d 5)),
    ("lane6", .int (d 6)), ("lane7", .int (d 7))]

def digest8OfValue (v : Value) : Digest8
  | 0 => (v.scalar "lane0").getD 0
  | 1 => (v.scalar "lane1").getD 0
  | 2 => (v.scalar "lane2").getD 0
  | 3 => (v.scalar "lane3").getD 0
  | 4 => (v.scalar "lane4").getD 0
  | 5 => (v.scalar "lane5").getD 0
  | 6 => (v.scalar "lane6").getD 0
  | 7 => (v.scalar "lane7").getD 0

theorem digest8OfValue_digest8Value (d : Digest8) : digest8OfValue (digest8Value d) = d := by
  funext i
  fin_cases i <;> simp [digest8OfValue, digest8Value, Value.scalar, Value.field]

/-- The per-cell semantic portion of Rust's rotated preimage.  Turn-level roots and carrier
material stay in `RotatedContext`; these fields are exactly the cell-owned values relevant to P1. -/
structure RotatedCell where
  balance : Int
  nonce : Int
  f0 : Int
  f1 : Int
  f2 : Int
  f3 : Int
  f4 : Int
  f5 : Int
  f6 : Int
  f7 : Int
  capRoot8 : Digest8
  authorityResidue : Value
  heapRoot8 : Digest8
  lifecycle : Int
  delegationEpoch : Int
  committedHeight : Int

def RotatedCell.field (d : RotatedCell) : Fin 8 → Int
  | 0 => d.f0 | 1 => d.f1 | 2 => d.f2 | 3 => d.f3
  | 4 => d.f4 | 5 => d.f5 | 6 => d.f6 | 7 => d.f7

def RotatedCell.toValue (d : RotatedCell) : Value :=
  .record [("balance", .int d.balance), ("nonce", .int d.nonce),
    ("f0", .int d.f0), ("f1", .int d.f1), ("f2", .int d.f2), ("f3", .int d.f3),
    ("f4", .int d.f4), ("f5", .int d.f5), ("f6", .int d.f6), ("f7", .int d.f7),
    ("capRoot8", digest8Value d.capRoot8), ("authorityResidue", d.authorityResidue),
    ("heapRoot8", digest8Value d.heapRoot8), ("lifecycle", .int d.lifecycle),
    ("delegationEpoch", .int d.delegationEpoch), ("committedHeight", .int d.committedHeight)]

def rotatedNestedValue (v : Value) (name : String) : Value :=
  (v.field name).getD (.record [])

def decodedRotatedCell (v : Value) : RotatedCell where
  balance := balOf v
  nonce := nonceOf v
  f0 := fieldLimbs v 0
  f1 := fieldLimbs v 1
  f2 := fieldLimbs v 2
  f3 := fieldLimbs v 3
  f4 := fieldLimbs v 4
  f5 := fieldLimbs v 5
  f6 := fieldLimbs v 6
  f7 := fieldLimbs v 7
  capRoot8 := digest8OfValue (rotatedNestedValue v "capRoot8")
  authorityResidue := authorityResidueValue v
  heapRoot8 := digest8OfValue (rotatedNestedValue v "heapRoot8")
  lifecycle := (v.scalar "lifecycle").getD 0
  delegationEpoch := (v.scalar "delegationEpoch").getD 0
  committedHeight := (v.scalar "committedHeight").getD 0

def CanonicalRotatedCell (v : Value) : Prop := v = (decodedRotatedCell v).toValue

def RotatedCell.clear (d : RotatedCell) :
    Int × Int × (Fin 8 → Int) × Digest8 × Digest8 × Int × Int × Int :=
  (d.balance, d.nonce, d.field, d.capRoot8, d.heapRoot8, d.lifecycle,
    d.delegationEpoch, d.committedHeight)

def rotatedClear (v : Value) := (decodedRotatedCell v).clear

theorem RotatedCell.ext_of_clear {d e : RotatedCell} (hc : d.clear = e.clear)
    (ha : d.authorityResidue = e.authorityResidue) : d = e := by
  cases d
  cases e
  simp only [RotatedCell.clear, Prod.mk.injEq] at hc
  have hf := hc.2.2.1
  have hf0 := congrFun hf (0 : Fin 8)
  have hf1 := congrFun hf (1 : Fin 8)
  have hf2 := congrFun hf (2 : Fin 8)
  have hf3 := congrFun hf (3 : Fin 8)
  have hf4 := congrFun hf (4 : Fin 8)
  have hf5 := congrFun hf (5 : Fin 8)
  have hf6 := congrFun hf (6 : Fin 8)
  have hf7 := congrFun hf (7 : Fin 8)
  simp only [RotatedCell.field] at hf0 hf1 hf2 hf3 hf4 hf5 hf6 hf7
  simp_all

theorem RotatedCell.toValue_canonical (d : RotatedCell) : CanonicalRotatedCell d.toValue := by
  cases d
  simp [CanonicalRotatedCell, decodedRotatedCell, RotatedCell.toValue, rotatedNestedValue,
    digest8OfValue_digest8Value, fieldLimbs, fieldName, authorityResidueValue, balOf, balanceField,
    Value.scalar, Value.field, nonceOf, nonceField]

/-- The exact wide boundary tag.  Canonical deployed cells hash only Rust's authority-residue
bytes; malformed/open abstract values hash their entire `Value` in the disjoint fallback domain. -/
noncomputable def rotatedAuthorityInput (v : Value) : AuthorityInput :=
  letI : Decidable (CanonicalRotatedCell v) := Classical.propDecidable _
  if CanonicalRotatedCell v then .rust (authorityResidueValue v) else .abstract v

theorem sameRotatedSurface_authorityInput_injective {v w : Value}
    (hs : rotatedClear v = rotatedClear w)
    (ha : rotatedAuthorityInput v = rotatedAuthorityInput w) : v = w := by
  classical
  by_cases hv : CanonicalRotatedCell v
  · by_cases hw : CanonicalRotatedCell w
    · have hres : authorityResidueValue v = authorityResidueValue w := by
        simpa only [rotatedAuthorityInput, if_pos hv, if_pos hw, AuthorityInput.rust.injEq] using ha
      have hd : decodedRotatedCell v = decodedRotatedCell w :=
        RotatedCell.ext_of_clear hs hres
      rw [hv, hw, hd]
    · simp only [rotatedAuthorityInput, if_pos hv, if_neg hw] at ha
      cases ha
  · by_cases hw : CanonicalRotatedCell w
    · simp only [rotatedAuthorityInput, if_neg hv, if_pos hw] at ha
      cases ha
    · simpa only [rotatedAuthorityInput, if_neg hv, if_neg hw,
        AuthorityInput.abstract.injEq] using ha

/-- The non-cell/turn-owned remainder of the deployed 184-limb row.  Known cell-owned positions are
overridden below; `residual` carries cells/nullifier/commitments/revoked roots, carrier octets,
and other already-modeled lanes without pretending they are authority bytes.

⚑ At the ninth-lane flag day (178 → 184) the two free pads are GONE and columns 176..183 are the
NINTH lane of `fields[0..7]` (`Dregg2.Circuit.FieldLanes9`). They are still carried as `residual`
here: this surface's conclusions are UNWEAKENED (it never claimed them), but the strengthening —
reading 176..183 as cell-owned field lanes, which is what makes the field octet injective — is NOT
taken yet. -/
structure RotatedContext where
  residual : Fin Dregg2.Circuit.Emit.rotatedNumPreLimbs → Int
  iroot : Int

abbrev RotatedContextProvider := CellId → Value → RotatedContext

/-- One exact deployed pre-iroot position.  The indices mirror
`cell::commitment::compute_rotated_pre_limbs` and `trace_rotated.rs` at HEAD.

⚑ The INDEX TYPE is `Fin rotatedNumPreLimbs`, not `Fin 184`.  A replica that carries its own idea of
the extent stays GREEN against its own length lemma while the deployed payload moves underneath it —
which is exactly what happened at the 2026-08-01 key-nonet flag day (184 → 187): this file would
have gone on committing a 184-limb object `wireCommitR8` no longer folds, self-consistently and
undetectably.  Every position past the old extent falls to the `ctx.residual` default, so widening
the index changes no named limb. -/
noncomputable def rotatedLimb (fold8 : AuthorityFold8) (ctx : RotatedContext)
    (v : Value) (i : Fin Dregg2.Circuit.Emit.rotatedNumPreLimbs) : Int :=
  let d := decodedRotatedCell v
  match i.1 with
  | 1 => d.balance % splitMod
  | 2 => d.nonce
  | 3 => d.balance / splitMod
  | 4 => d.field 0 | 5 => d.field 1 | 6 => d.field 2 | 7 => d.field 3
  | 8 => d.field 4 | 9 => d.field 5 | 10 => d.field 6 | 11 => d.field 7
  | 12 => fold8 (rotatedAuthorityInput v) 1
  | 13 => fold8 (rotatedAuthorityInput v) 2
  | 14 => fold8 (rotatedAuthorityInput v) 3
  | 15 => fold8 (rotatedAuthorityInput v) 4
  | 16 => fold8 (rotatedAuthorityInput v) 5
  | 17 => fold8 (rotatedAuthorityInput v) 6
  | 18 => fold8 (rotatedAuthorityInput v) 7
  | 24 => fold8 (rotatedAuthorityInput v) 0
  | 25 => d.capRoot8 0
  | 28 => d.heapRoot8 0
  | 29 => d.lifecycle
  | 30 => d.delegationEpoch
  | 31 => d.committedHeight
  | 52 => d.capRoot8 1 | 53 => d.capRoot8 2 | 54 => d.capRoot8 3
  | 55 => d.capRoot8 4 | 56 => d.capRoot8 5 | 57 => d.capRoot8 6 | 58 => d.capRoot8 7
  | 59 => d.heapRoot8 1 | 60 => d.heapRoot8 2 | 61 => d.heapRoot8 3
  | 62 => d.heapRoot8 4 | 63 => d.heapRoot8 5 | 64 => d.heapRoot8 6 | 65 => d.heapRoot8 7
  | _ => ctx.residual i

noncomputable def rotatedPreLimbs (fold8 : AuthorityFold8) (ctx : RotatedContext)
    (v : Value) : List Int :=
  List.ofFn (rotatedLimb fold8 ctx v)

theorem rotatedPreLimbs_length (fold8 : AuthorityFold8) (ctx : RotatedContext) (v : Value) :
    (rotatedPreLimbs fold8 ctx v).length = Dregg2.Circuit.Emit.rotatedNumPreLimbs := by
  unfold rotatedPreLimbs
  exact List.length_ofFn

open Dregg2.Circuit.Emit.EffectVmEmitRotationR
  (wireCommitR8 chainFrom8_len Poseidon2Width8 refWide)

noncomputable def rotatedCommit8 (fold8 : AuthorityFold8) (permW : List Int → List Int)
    (ctx : RotatedContext) (v : Value) : List Int :=
  wireCommitR8 permW (rotatedPreLimbs fold8 ctx v) ctx.iroot

/-- Computable direct twin on a canonical `RotatedCell`, used by the golden guards and by a Rust
differential: it avoids the abstract malformed-value branch while retaining the exact named indices. -/
def deployedRotatedLimb (fold8 : AuthorityFold8) (ctx : RotatedContext)
    (d : RotatedCell) (i : Fin Dregg2.Circuit.Emit.rotatedNumPreLimbs) : Int :=
  match i.1 with
  | 1 => d.balance % splitMod
  | 2 => d.nonce
  | 3 => d.balance / splitMod
  | 4 => d.field 0 | 5 => d.field 1 | 6 => d.field 2 | 7 => d.field 3
  | 8 => d.field 4 | 9 => d.field 5 | 10 => d.field 6 | 11 => d.field 7
  | 12 => fold8 (.rust d.authorityResidue) 1
  | 13 => fold8 (.rust d.authorityResidue) 2
  | 14 => fold8 (.rust d.authorityResidue) 3
  | 15 => fold8 (.rust d.authorityResidue) 4
  | 16 => fold8 (.rust d.authorityResidue) 5
  | 17 => fold8 (.rust d.authorityResidue) 6
  | 18 => fold8 (.rust d.authorityResidue) 7
  | 24 => fold8 (.rust d.authorityResidue) 0
  | 25 => d.capRoot8 0
  | 28 => d.heapRoot8 0
  | 29 => d.lifecycle
  | 30 => d.delegationEpoch
  | 31 => d.committedHeight
  | 52 => d.capRoot8 1 | 53 => d.capRoot8 2 | 54 => d.capRoot8 3
  | 55 => d.capRoot8 4 | 56 => d.capRoot8 5 | 57 => d.capRoot8 6 | 58 => d.capRoot8 7
  | 59 => d.heapRoot8 1 | 60 => d.heapRoot8 2 | 61 => d.heapRoot8 3
  | 62 => d.heapRoot8 4 | 63 => d.heapRoot8 5 | 64 => d.heapRoot8 6 | 65 => d.heapRoot8 7
  | _ => ctx.residual i

def deployedRotatedCommit8 (fold8 : AuthorityFold8) (permW : List Int → List Int)
    (ctx : RotatedContext) (d : RotatedCell) : List Int :=
  wireCommitR8 permW (List.ofFn (deployedRotatedLimb fold8 ctx d)) ctx.iroot

private def fold8Demo : AuthorityFold8 := fun x i =>
  match i.1 with
  | 0 => 41
  | 1 => foldDemo x
  | n => 41 + n

private def rotatedCellDemo (mode : Nat) : RotatedCell where
  balance := 5
  nonce := 7
  f0 := 10
  f1 := 11
  f2 := 12
  f3 := 13
  f4 := 14
  f5 := 15
  f6 := 16
  f7 := 17
  capRoot8 := fun i => 100 + i.1
  authorityResidue := residueDemo mode
  heapRoot8 := fun i => 200 + i.1
  lifecycle := 3
  delegationEpoch := 4
  committedHeight := 5

private def rotatedContextDemo : RotatedContext where
  residual := fun i => 300 + i.1
  iroot := 9

-- The legacy lane agrees, but authority lane 1 and therefore the live wide commitment differ.
#guard fold8Demo (.rust (rotatedCellDemo 0).authorityResidue) 0 ==
  fold8Demo (.rust (rotatedCellDemo 1).authorityResidue) 0
#guard fold8Demo (.rust (rotatedCellDemo 0).authorityResidue) 1 !=
  fold8Demo (.rust (rotatedCellDemo 1).authorityResidue) 1
#guard deployedRotatedCommit8 fold8Demo refWide rotatedContextDemo (rotatedCellDemo 0) !=
  deployedRotatedCommit8 fold8Demo refWide rotatedContextDemo (rotatedCellDemo 1)

theorem rotatedCommit8_length (permW : List Int → List Int) (hW : Poseidon2Width8 permW)
    (fold8 : AuthorityFold8) (ctx : RotatedContext) (v : Value) :
    (rotatedCommit8 fold8 permW ctx v).length = 8 := by
  unfold rotatedCommit8 wireCommitR8
  exact chainFrom8_len permW hW (hW ((rotatedPreLimbs fold8 ctx v).take 4))

/-- Lossless mathematical packing of the eight PIs into the scalar carrier expected by the older
`recStateCommit` abstraction.  This is serialization, not another hash: equality of packs recovers
all eight lanes under the deployed width contract. -/
def wideTuple (xs : List Int) : Fin 8 → Int := fun i => xs.getD i.1 0

def packWideTuple (xs : List Int) : Int :=
  Int.ofNat (Encodable.encode (wideTuple xs))

theorem list_eq_of_wideTuple_eq {xs ys : List Int} (hx : xs.length = 8) (hy : ys.length = 8)
    (h : wideTuple xs = wideTuple ys) : xs = ys := by
  apply List.ext_getElem
  · exact hx.trans hy.symm
  · intro i hi hi'
    have hi8 : i < 8 := by simpa [hx] using hi
    have hget := congrFun h (⟨i, hi8⟩ : Fin 8)
    simp only [wideTuple] at hget
    rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem hi, List.getElem?_eq_getElem hi'] at hget
    exact hget

noncomputable def CH_faithful8 (fold8 : AuthorityFold8) (permW : List Int → List Int)
    (ctx : RotatedContextProvider) (c : CellId) (v : Value) : Int :=
  packWideTuple (rotatedCommit8 fold8 permW (ctx c v) v)

/-- A collision of the complete authority digest: both distinct tagged preimages agree in all
eight lanes.  This is the only authority failure on the live wide surface. -/
def AuthorityDigest8Collision (fold8 : AuthorityFold8) : Prop :=
  ∃ x y : AuthorityInput, x ≠ y ∧ fold8 x = fold8 y

/-- A genuine collision of the deployed 184-limb plus iroot wide chain. -/
def WireCommit8Collision (permW : List Int → List Int) : Prop :=
  ∃ l l' : List Int, ∃ ir ir' : Int,
    (l ≠ l' ∨ ir ≠ ir') ∧ wireCommitR8 permW l ir = wireCommitR8 permW l' ir'

theorem rotatedPreLimbs_eq_implies (fold8 : AuthorityFold8)
    (ctx ctx' : RotatedContext) {v w : Value}
    (h : rotatedPreLimbs fold8 ctx v = rotatedPreLimbs fold8 ctx' w) :
    rotatedClear v = rotatedClear w ∧
      fold8 (rotatedAuthorityInput v) = fold8 (rotatedAuthorityInput w) := by
  have hfn : rotatedLimb fold8 ctx v = rotatedLimb fold8 ctx' w :=
    List.ofFn_injective h
  have hp (n : Nat) (hn : n < Dregg2.Circuit.Emit.rotatedNumPreLimbs) :
      rotatedLimb fold8 ctx v ⟨n, hn⟩ = rotatedLimb fold8 ctx' w ⟨n, hn⟩ :=
    congrFun hfn ⟨n, hn⟩
  have hlo : (decodedRotatedCell v).balance % splitMod =
      (decodedRotatedCell w).balance % splitMod := by
    simpa [rotatedLimb] using hp 1 (by decide)
  have hhi : (decodedRotatedCell v).balance / splitMod =
      (decodedRotatedCell w).balance / splitMod := by
    simpa [rotatedLimb] using hp 3 (by decide)
  have hbal : (decodedRotatedCell v).balance = (decodedRotatedCell w).balance := by
    rw [← Int.emod_add_mul_ediv (decodedRotatedCell v).balance splitMod,
      ← Int.emod_add_mul_ediv (decodedRotatedCell w).balance splitMod, hlo, hhi]
  have hn : (decodedRotatedCell v).nonce = (decodedRotatedCell w).nonce := by
    simpa [rotatedLimb] using hp 2 (by decide)
  have hf : (decodedRotatedCell v).field = (decodedRotatedCell w).field := by
    funext i
    fin_cases i
    · simpa [rotatedLimb] using hp 4 (by decide)
    · simpa [rotatedLimb] using hp 5 (by decide)
    · simpa [rotatedLimb] using hp 6 (by decide)
    · simpa [rotatedLimb] using hp 7 (by decide)
    · simpa [rotatedLimb] using hp 8 (by decide)
    · simpa [rotatedLimb] using hp 9 (by decide)
    · simpa [rotatedLimb] using hp 10 (by decide)
    · simpa [rotatedLimb] using hp 11 (by decide)
  have hcap : (decodedRotatedCell v).capRoot8 = (decodedRotatedCell w).capRoot8 := by
    funext i
    fin_cases i
    · simpa [rotatedLimb] using hp 25 (by decide)
    · simpa [rotatedLimb] using hp 52 (by decide)
    · simpa [rotatedLimb] using hp 53 (by decide)
    · simpa [rotatedLimb] using hp 54 (by decide)
    · simpa [rotatedLimb] using hp 55 (by decide)
    · simpa [rotatedLimb] using hp 56 (by decide)
    · simpa [rotatedLimb] using hp 57 (by decide)
    · simpa [rotatedLimb] using hp 58 (by decide)
  have hheap : (decodedRotatedCell v).heapRoot8 = (decodedRotatedCell w).heapRoot8 := by
    funext i
    fin_cases i
    · simpa [rotatedLimb] using hp 28 (by decide)
    · simpa [rotatedLimb] using hp 59 (by decide)
    · simpa [rotatedLimb] using hp 60 (by decide)
    · simpa [rotatedLimb] using hp 61 (by decide)
    · simpa [rotatedLimb] using hp 62 (by decide)
    · simpa [rotatedLimb] using hp 63 (by decide)
    · simpa [rotatedLimb] using hp 64 (by decide)
    · simpa [rotatedLimb] using hp 65 (by decide)
  have hlifecycle : (decodedRotatedCell v).lifecycle = (decodedRotatedCell w).lifecycle := by
    simpa [rotatedLimb] using hp 29 (by decide)
  have hepoch : (decodedRotatedCell v).delegationEpoch =
      (decodedRotatedCell w).delegationEpoch := by
    simpa [rotatedLimb] using hp 30 (by decide)
  have hheight : (decodedRotatedCell v).committedHeight =
      (decodedRotatedCell w).committedHeight := by
    simpa [rotatedLimb] using hp 31 (by decide)
  have hclear : rotatedClear v = rotatedClear w := by
    simp only [rotatedClear, RotatedCell.clear, Prod.mk.injEq]
    exact ⟨hbal, hn, hf, hcap, hheap, hlifecycle, hepoch, hheight⟩
  have hauth : fold8 (rotatedAuthorityInput v) = fold8 (rotatedAuthorityInput w) := by
    funext i
    fin_cases i
    · simpa [rotatedLimb] using hp 24 (by decide)
    · simpa [rotatedLimb] using hp 12 (by decide)
    · simpa [rotatedLimb] using hp 13 (by decide)
    · simpa [rotatedLimb] using hp 14 (by decide)
    · simpa [rotatedLimb] using hp 15 (by decide)
    · simpa [rotatedLimb] using hp 16 (by decide)
    · simpa [rotatedLimb] using hp 17 (by decide)
    · simpa [rotatedLimb] using hp 18 (by decide)
  exact ⟨hclear, hauth⟩

/-- A collision in the scalar compatibility view is never a lane-0 residue: it reduces to equality
of all eight authority lanes on distinct preimages, or to a genuine collision of the wide chain. -/
theorem cellCollision_faithful8_reduces (fold8 : AuthorityFold8)
    (permW : List Int → List Int) (hW : Poseidon2Width8 permW)
    (ctx : RotatedContextProvider) :
    CellCollision (CH_faithful8 fold8 permW ctx) →
      AuthorityDigest8Collision fold8 ∨ WireCommit8Collision permW := by
  rintro ⟨c, v, w, hne, hpack⟩
  have htuple : wideTuple (rotatedCommit8 fold8 permW (ctx c v) v) =
      wideTuple (rotatedCommit8 fold8 permW (ctx c w) w) := by
    apply Encodable.encode_injective
    exact Int.ofNat.inj (by simpa [CH_faithful8, packWideTuple] using hpack)
  have hcommit : rotatedCommit8 fold8 permW (ctx c v) v =
      rotatedCommit8 fold8 permW (ctx c w) w :=
    list_eq_of_wideTuple_eq
      (rotatedCommit8_length permW hW fold8 (ctx c v) v)
      (rotatedCommit8_length permW hW fold8 (ctx c w) w) htuple
  by_cases ha : rotatedAuthorityInput v = rotatedAuthorityInput w
  · by_cases hs : rotatedClear v = rotatedClear w
    · exact absurd (sameRotatedSurface_authorityInput_injective hs ha) hne
    · apply Or.inr
      have hl : rotatedPreLimbs fold8 (ctx c v) v ≠ rotatedPreLimbs fold8 (ctx c w) w := by
        intro heq
        exact hs (rotatedPreLimbs_eq_implies fold8 (ctx c v) (ctx c w) heq).1
      exact ⟨_, _, _, _, Or.inl hl, hcommit⟩
  · by_cases hd : fold8 (rotatedAuthorityInput v) = fold8 (rotatedAuthorityInput w)
    · exact Or.inl ⟨rotatedAuthorityInput v, rotatedAuthorityInput w, ha, hd⟩
    · apply Or.inr
      have hl : rotatedPreLimbs fold8 (ctx c v) v ≠ rotatedPreLimbs fold8 (ctx c w) w := by
        intro heq
        exact hd (rotatedPreLimbs_eq_implies fold8 (ctx c v) (ctx c w) heq).2
      exact ⟨_, _, _, _, Or.inl hl, hcommit⟩

#assert_axioms digest8OfValue_digest8Value
#assert_axioms RotatedCell.ext_of_clear
#assert_axioms RotatedCell.toValue_canonical
#assert_axioms sameRotatedSurface_authorityInput_injective
#assert_axioms rotatedPreLimbs_length
#assert_axioms rotatedCommit8_length
#assert_axioms list_eq_of_wideTuple_eq
#assert_axioms rotatedPreLimbs_eq_implies
#assert_axioms cellCollision_faithful8_reduces

/-! ## 4. Whole-kernel and freshness keystones on the live eight-lane leaf. -/

/-- ⚰ **TOMBSTONE — this WAS `FaithfulBreak` until 2026-08-01, and it says NOTHING.** A five-way
disjunction of GLOBAL existentials; its first disjunct `SpongeCollision compressN` is supplied by
pigeonhole at every field-bounded sponge, i.e. at every sponge this surface deploys. Retained, not
deleted, because a refuted shape with a visible refutation is the only kind that stays refuted:
`faithfulBreakGlobal_free_of_fieldBounded` PROVES it outright and `orFaithfulBreakGlobal_iff_True`
proves every `P ∨ FaithfulBreakGlobal …` is literally `True`. The live event is `FaithfulBreak`
below, which names the pair. -/
def FaithfulBreakGlobal (fold8 : AuthorityFold8) (permW : List Int → List Int)
    (cmb compress : Int → Int → Int) (compressN : List Int → Int) : Prop :=
  SpongeCollision compressN ∨ CompressCollision cmb ∨ CompressCollision compress
    ∨ AuthorityDigest8Collision fold8 ∨ WireCommit8Collision permW

/-- **⚑⚑ THE TOMBSTONE'S TEETH.** At any deployed-shaped (field-bounded) sponge the retired break
event HOLDS, with no adversary and no hypothesis about the other four primitives — the same
pigeonhole that refutes the injectivity floors ESTABLISHES it. -/
theorem faithfulBreakGlobal_free_of_fieldBounded (fold8 : AuthorityFold8)
    (permW : List Int → List Int) (cmb compress : Int → Int → Int) (compressN : List Int → Int)
    (hb : FieldBounded compressN) : FaithfulBreakGlobal fold8 permW cmb compress compressN :=
  Or.inl (spongeCollision_of_fieldBounded hb)

/-- **⚑⚑ THE TOMBSTONE'S TEETH, AS AN EQUIVALENCE.** Over an ARBITRARY good branch: at a deployed
sponge `P ∨ FaithfulBreakGlobal …` is `True` for EVERY `P`, so no theorem of that shape — including
the ones retained below as `⚠ BRIDGE ONLY` — discriminates at the parameters we deploy at. -/
theorem orFaithfulBreakGlobal_iff_True (fold8 : AuthorityFold8) (permW : List Int → List Int)
    (cmb compress : Int → Int → Int) (compressN : List Int → Int)
    (hb : FieldBounded compressN) (P : Prop) :
    (P ∨ FaithfulBreakGlobal fold8 permW cmb compress compressN) ↔ True :=
  ⟨fun _ => trivial,
   fun _ => Or.inr (faithfulBreakGlobal_free_of_fieldBounded fold8 permW cmb compress compressN hb)⟩

/-- ⚠ **BRIDGE ONLY.** Both sides are global existentials, so this records a strength relation
between two events that are each `True` at deployed parameters. The live reduction is
`cellLeafColl_faithful8_reduces` (per-instance, named pair). -/
theorem stateBreak_faithful_reduces (fold8 : AuthorityFold8)
    (permW : List Int → List Int) (hW : Poseidon2Width8 permW)
    (ctx : RotatedContextProvider) (cmb compress : Int → Int → Int)
    (compressN : List Int → Int) :
    StateBreakP (CH_faithful8 fold8 permW ctx) cmb compress compressN →
      FaithfulBreakGlobal fold8 permW cmb compress compressN := by
  rintro (hs | hcmb | hcomp | hcell)
  · exact Or.inl hs
  · exact Or.inr (Or.inl hcmb)
  · exact Or.inr (Or.inr (Or.inl hcomp))
  · rcases cellCollision_faithful8_reduces fold8 permW hW ctx hcell with ha | hwide
    · exact Or.inr (Or.inr (Or.inr (Or.inl ha)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr hwide)))

/-! ### ⚑⚑ THE PER-INSTANCE PORT, AND THE NARROWING (2026-08-01).

The retired `FaithfulBreakGlobal` OPENED with `SpongeCollision compressN`, a GLOBAL existential that
`SpongeCollisionShirk.spongeCollision_of_fieldBounded` SUPPLIES at every field-bounded sponge — i.e.
at every sponge this surface deploys. So `P ∨ FaithfulBreakGlobal …` holds by its right disjunct
alone, unconditionally (`orFaithfulBreakGlobal_iff_True`), and the consumers that returned it said
nothing at the parameters we deploy at. Its other four disjuncts are the same shape
(`∃ x y, x ≠ y ∧ fold8 x = fold8 y`, …), so narrowing only the sponge one would not have helped:
EVERY disjunct was a global existential, and any one of them being satisfiable makes the whole
dichotomy true. That is why the narrowing below rewrites ALL FIVE legs, not just the sponge.

⚠ **AN EARLIER DRAFT OF THIS PARAGRAPH CONCLUDED "`FaithfulBreak` cannot be repaired by narrowing it
in place", and that was wrong.** What is true is only that it cannot be narrowed WITHOUT CHANGING ITS
ARITY: a per-instance leg must name the opening `(k, k', t)`, and the old definition did not take
one. It takes one now. Two ports therefore exist, and both are live:

* `FaithfulCommitColl` = `StateCommitLeafRegrounded.RecStateCommitColl` AT THE FAITHFUL LEAF — the
  four commitment primitives at the SPECIFIC argument pairs the whole-kernel extraction visits. This
  is the residual the `_or_collides` / `_of_noColl` pairs below return, and it DROPS
  `hW : Poseidon2Width8 permW` (the width contract was only needed to unpack the scalar carrier on
  the way to the global reduction).
* `FaithfulBreak` (narrowed, §4 below) = the same four primitives PLUS the leaf disjuncts already
  cashed out through `cellLeafColl_faithful8_reduces` to the deployed eight-lane authority digest and
  wide chain, at the named preimages. This is what the consumers now return in place of the free
  global event, so their affirmative docstrings are affirmations again.

⚠ ONE of `FaithfulBreakGlobal`'s consumers genuinely is global→global and stays
(`stateBreak_faithful_reduces`); the other retained two (`recStateCommit_binds_kernel_faithful_global`,
`transfer_circuit_full_sound_faithful`) are `⚠ BRIDGE ONLY` re-derivations that record the strength
relation. Nothing outside this file consumes any of them (`Freshness`/`CircuitSoundness` name them in
prose only; `grep` over the tree finds no term-level use), so the narrowing broke no consumer. -/

/-- A collision of the complete eight-lane authority digest AT A NAMED PAIR of tagged preimages. -/
def AuthorityDigest8Coll (fold8 : AuthorityFold8) (x y : AuthorityInput) : Prop :=
  x ≠ y ∧ fold8 x = fold8 y

/-- A collision of the deployed 184-limb-plus-iroot wide chain AT A NAMED PAIR of openings. -/
def WireCommit8Coll (permW : List Int → List Int) (l l' : List Int) (ir ir' : Int) : Prop :=
  (l ≠ l' ∨ ir ≠ ir') ∧ wireCommitR8 permW l ir = wireCommitR8 permW l' ir'

/-- A named `AuthorityDigest8Coll` is a genuine `AuthorityDigest8Collision` (⚠ the direction that
loses the pair, kept for the bridges). -/
theorem AuthorityDigest8Coll.toGlobal {fold8 : AuthorityFold8} {x y : AuthorityInput}
    (h : AuthorityDigest8Coll fold8 x y) : AuthorityDigest8Collision fold8 := ⟨x, y, h.1, h.2⟩

/-- A named `WireCommit8Coll` is a genuine `WireCommit8Collision` (⚠ loses the pair). -/
theorem WireCommit8Coll.toGlobal {permW : List Int → List Int} {l l' : List Int} {ir ir' : Int}
    (h : WireCommit8Coll permW l l' ir ir') : WireCommit8Collision permW := ⟨l, l', ir, ir', h.1, h.2⟩

/-- **⚑ THE FAITHFUL LEAF'S BREAK AT A NAMED `(c, v, w)`.** The deployed guarantee `CH_faithful8`
was built to deliver, stated about the TWO openings in play and nothing else: either the complete
eight-lane authority digest agrees on the two NAMED tagged preimages, or the 184-limb-plus-iroot wide
chain agrees on the two NAMED limb openings. No `∃ two colliding inputs` anywhere, so pigeonhole does
not supply it: `noFaithfulLeafBreak_diag` refutes it at `v = w` for EVERY deployment. -/
def FaithfulLeafBreak (fold8 : AuthorityFold8) (permW : List Int → List Int)
    (ctx : RotatedContextProvider) (c : CellId) (v w : Value) : Prop :=
  AuthorityDigest8Coll fold8 (rotatedAuthorityInput v) (rotatedAuthorityInput w)
    ∨ WireCommit8Coll permW (rotatedPreLimbs fold8 (ctx c v) v)
        (rotatedPreLimbs fold8 (ctx c w) w) (ctx c v).iroot (ctx c w).iroot

/-- **⚑ THE PER-INSTANCE LEAF REDUCTION.** A collision of the scalar compatibility view AT A NAMED
`(c, v, w)` is never a lane-0 residue: it reduces to equality of ALL EIGHT authority lanes on the two
NAMED tagged preimages, or to a collision of the wide chain on the two NAMED limb openings. Same
content as `cellCollision_faithful8_reduces`, with the pair carried instead of forgotten — and
without the `Poseidon2Width8` carrier, which only the scalar-unpacking step needed. -/
theorem cellLeafColl_faithful8_reduces (fold8 : AuthorityFold8)
    (permW : List Int → List Int) (hW : Poseidon2Width8 permW)
    (ctx : RotatedContextProvider) (c : CellId) (v w : Value)
    (hc : CellLeafColl (CH_faithful8 fold8 permW ctx) c v w) :
    AuthorityDigest8Coll fold8 (rotatedAuthorityInput v) (rotatedAuthorityInput w)
      ∨ WireCommit8Coll permW (rotatedPreLimbs fold8 (ctx c v) v)
          (rotatedPreLimbs fold8 (ctx c w) w) (ctx c v).iroot (ctx c w).iroot := by
  obtain ⟨hne, hpack⟩ := hc
  have htuple : wideTuple (rotatedCommit8 fold8 permW (ctx c v) v) =
      wideTuple (rotatedCommit8 fold8 permW (ctx c w) w) := by
    apply Encodable.encode_injective
    exact Int.ofNat.inj (by simpa [CH_faithful8, packWideTuple] using hpack)
  have hcommit : rotatedCommit8 fold8 permW (ctx c v) v =
      rotatedCommit8 fold8 permW (ctx c w) w :=
    list_eq_of_wideTuple_eq
      (rotatedCommit8_length permW hW fold8 (ctx c v) v)
      (rotatedCommit8_length permW hW fold8 (ctx c w) w) htuple
  by_cases ha : rotatedAuthorityInput v = rotatedAuthorityInput w
  · by_cases hs : rotatedClear v = rotatedClear w
    · exact absurd (sameRotatedSurface_authorityInput_injective hs ha) hne
    · exact Or.inr ⟨Or.inl (fun heq =>
        hs (rotatedPreLimbs_eq_implies fold8 (ctx c v) (ctx c w) heq).1), hcommit⟩
  · by_cases hd : fold8 (rotatedAuthorityInput v) = fold8 (rotatedAuthorityInput w)
    · exact Or.inl ⟨ha, hd⟩
    · exact Or.inr ⟨Or.inl (fun heq =>
        hd (rotatedPreLimbs_eq_implies fold8 (ctx c v) (ctx c w) heq).2), hcommit⟩

/-- `cellLeafColl_faithful8_reduces` at the named event. -/
theorem faithfulLeafBreak_of_cellLeafColl (fold8 : AuthorityFold8)
    (permW : List Int → List Int) (hW : Poseidon2Width8 permW)
    (ctx : RotatedContextProvider) (c : CellId) (v w : Value)
    (hc : CellLeafColl (CH_faithful8 fold8 permW ctx) c v w) :
    FaithfulLeafBreak fold8 permW ctx c v w :=
  cellLeafColl_faithful8_reduces fold8 permW hW ctx c v w hc

/-- **⚑⚑ `FaithfulBreak` — NARROWED 2026-08-01: EVERY LEG NAMES A PAIR.** The five commitment
primitives of the live eight-lane surface, each stated AT THE SPECIFIC ARGUMENTS the whole-kernel
extraction visits for THIS opening `(k, k', t)` — never `∃ two colliding inputs`. Leg by leg:

1. the root combiner `cmb` at the two `(cellDigest, RH)` children;
2. the node hash `compress` at the `cellDigest` split (frame child ⊕ moved child);
3. the sponge `compressN` at the TWO ORDERED FRAME-LEAF LISTS (`FrameCNColl`) — the named-pair
   replacement for the global `SpongeCollision compressN` this definition used to OPEN with;
4. the leaf, at whichever untouched carrier cell equivocates — an `∃ c ∈` over the FINITE frame
   carrier OF THIS OPENING, indexed BY the claim rather than quantified outside it;
5. the node hash again at the moved leaf pair, and the leaf at `src` and at `dst`.

Every leaf leg is already cashed out to the deployed surface by `FaithfulLeafBreak`: a genuine
eight-lane authority collision or a genuine wide-chain collision, at named preimages.
`noFaithfulBreak_diag` refutes the whole disjunction on the diagonal at EVERY choice of
`fold8`/`permW`/`ctx`/`cmb`/`compress`/`compressN`/`RH` — contrast `FaithfulBreakGlobal`, which
`faithfulBreakGlobal_free_of_fieldBounded` supplies for free. -/
def FaithfulBreak (fold8 : AuthorityFold8) (permW : List Int → List Int)
    (ctx : RotatedContextProvider) (cmb compress : Int → Int → Int)
    (compressN : List Int → Int) (RH : RecordKernelState → Int)
    (k k' : RecordKernelState) (t : Turn) : Prop :=
  CompressColl cmb
      (cellDigest (CH_faithful8 fold8 permW ctx) compress compressN k t) (RH k)
      (cellDigest (CH_faithful8 fold8 permW ctx) compress compressN k' t) (RH k')
    ∨ CompressColl compress
        (frameDigest (CH_faithful8 fold8 permW ctx) compressN k (k.accounts \ {t.src, t.dst}))
        (movedDigest (CH_faithful8 fold8 permW ctx) compress k.cell t.src t.dst)
        (frameDigest (CH_faithful8 fold8 permW ctx) compressN k' (k.accounts \ {t.src, t.dst}))
        (movedDigest (CH_faithful8 fold8 permW ctx) compress k'.cell t.src t.dst)
    ∨ FrameCNColl (CH_faithful8 fold8 permW ctx) compressN k k' (k.accounts \ {t.src, t.dst})
    ∨ (∃ c ∈ k.accounts \ {t.src, t.dst},
        FaithfulLeafBreak fold8 permW ctx c (k.cell c) (k'.cell c))
    ∨ CompressColl compress
        (CH_faithful8 fold8 permW ctx t.src (k.cell t.src))
        (CH_faithful8 fold8 permW ctx t.dst (k.cell t.dst))
        (CH_faithful8 fold8 permW ctx t.src (k'.cell t.src))
        (CH_faithful8 fold8 permW ctx t.dst (k'.cell t.dst))
    ∨ FaithfulLeafBreak fold8 permW ctx t.src (k.cell t.src) (k'.cell t.src)
    ∨ FaithfulLeafBreak fold8 permW ctx t.dst (k.cell t.dst) (k'.cell t.dst)

/-- **⚑ THE NARROWING IS A NARROWING.** Every leg of `FaithfulBreak` implies the corresponding leg of
the retired `FaithfulBreakGlobal`, so the new event is CONTAINED in the old one at every opening —
`FaithfulBreak` is strictly the stronger conclusion, and nothing the old shape claimed is given up.
Together with `faithfulBreak_sharper_than_global` (the old one holds where the new one is refuted)
this pins the containment as PROPER at deployed parameters. -/
theorem faithfulBreakGlobal_of_faithfulBreak (fold8 : AuthorityFold8)
    (permW : List Int → List Int) (ctx : RotatedContextProvider)
    (cmb compress : Int → Int → Int) (compressN : List Int → Int)
    (RH : RecordKernelState → Int) {k k' : RecordKernelState} {t : Turn}
    (h : FaithfulBreak fold8 permW ctx cmb compress compressN RH k k' t) :
    FaithfulBreakGlobal fold8 permW cmb compress compressN := by
  have leaf : ∀ {c : CellId} {v w : Value}, FaithfulLeafBreak fold8 permW ctx c v w →
      FaithfulBreakGlobal fold8 permW cmb compress compressN := by
    rintro c v w (ha | hw)
    · exact Or.inr (Or.inr (Or.inr (Or.inl ha.toGlobal)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr hw.toGlobal)))
  rcases h with hr | hn | hcn | ⟨_, -, hl⟩ | hm | hl | hl
  · exact Or.inr (Or.inl hr.extracts)
  · exact Or.inr (Or.inr (Or.inl hn.extracts))
  · exact Or.inl ⟨_, _, hcn.1, hcn.2⟩
  · exact leaf hl
  · exact Or.inr (Or.inr (Or.inl hm.extracts))
  · exact leaf hl
  · exact leaf hl

/-- **`FaithfulCommitColl` — THE PER-INSTANCE RESIDUAL of the live eight-lane whole-kernel binding.**
The four commitment primitives (`cmb`, `compress`, `compressN`, and the faithful leaf `CH_faithful8`)
stated at the SPECIFIC argument pairs the whole-kernel extraction visits for THIS `(k, k', t)` —
never `∃ two colliding inputs`. Its leaf disjuncts cash out, still per-instance, through
`cellLeafColl_faithful8_reduces`. -/
abbrev FaithfulCommitColl (fold8 : AuthorityFold8) (permW : List Int → List Int)
    (ctx : RotatedContextProvider) (cmb compress : Int → Int → Int)
    (compressN : List Int → Int) (RH : RecordKernelState → Int)
    (k k' : RecordKernelState) (t : Turn) : Prop :=
  RecStateCommitColl (CH_faithful8 fold8 permW ctx) RH cmb compress compressN k k' t

/-- **⚑⚑ THE LIVE BINDING CONSUMER, PORTED.** Equal live-wide faithful roots determine the entire
kernel, OR the NAMED residual `FaithfulCommitColl` holds at the exact argument pairs the extraction
visits. No injectivity hypothesis, no global collision existential, and no `Poseidon2Width8`
carrier — this is what the deployed residue-fold leaf actually buys. -/
theorem recStateCommit_binds_kernel_faithful_or_collides (fold8 : AuthorityFold8)
    (permW : List Int → List Int)
    (ctx : RotatedContextProvider) (cmb compress : Int → Int → Int)
    (compressN : List Int → Int) (RH : RecordKernelState → Int)
    (hRest : RestHashIffFrameFin RH) (k k' : RecordKernelState) (t : Turn)
    (hwf : AccountsWF k) (hwf' : AccountsWF k')
    (hfin : FiniteRepresentable k) (hfin' : FiniteRepresentable k')
    (hroot : recStateCommit (CH_faithful8 fold8 permW ctx) RH cmb compress compressN k t =
      recStateCommit (CH_faithful8 fold8 permW ctx) RH cmb compress compressN k' t) :
    k = k' ∨ FaithfulCommitColl fold8 permW ctx cmb compress compressN RH k k' t :=
  recStateCommit_binds_kernel_or_collidesFin (CH_faithful8 fold8 permW ctx)
    cmb compress compressN RH hRest k k' t hwf hwf' hfin hfin' hroot

/-- **S3** — the injective original's conclusion (`k = k'`) from the PER-INSTANCE side condition. -/
theorem recStateCommit_binds_kernel_faithful_of_noColl (fold8 : AuthorityFold8)
    (permW : List Int → List Int)
    (ctx : RotatedContextProvider) (cmb compress : Int → Int → Int)
    (compressN : List Int → Int) (RH : RecordKernelState → Int)
    (hRest : RestHashIffFrameFin RH) (k k' : RecordKernelState) (t : Turn)
    (hwf : AccountsWF k) (hwf' : AccountsWF k')
    (hfin : FiniteRepresentable k) (hfin' : FiniteRepresentable k')
    (hno : ¬ FaithfulCommitColl fold8 permW ctx cmb compress compressN RH k k' t)
    (hroot : recStateCommit (CH_faithful8 fold8 permW ctx) RH cmb compress compressN k t =
      recStateCommit (CH_faithful8 fold8 permW ctx) RH cmb compress compressN k' t) :
    k = k' :=
  (recStateCommit_binds_kernel_faithful_or_collides fold8 permW ctx cmb compress compressN RH
    hRest k k' t hwf hwf' hfin hfin' hroot).resolve_right hno

/-- **⚑ THE PER-INSTANCE NONCE BINDING** — `commit_binds_nonce_faithful` at the named pair. -/
theorem commit_binds_nonce_faithful_or_collides (fold8 : AuthorityFold8)
    (permW : List Int → List Int)
    (ctx : RotatedContextProvider) (cmb compress : Int → Int → Int)
    (compressN : List Int → Int) (RH : RecordKernelState → Int)
    (hRest : RestHashIffFrameFin RH) (k k' : RecordKernelState) (t : Turn) (agent : CellId)
    (hwf : AccountsWF k) (hwf' : AccountsWF k')
    (hfin : FiniteRepresentable k) (hfin' : FiniteRepresentable k')
    (hroot : recStateCommit (CH_faithful8 fold8 permW ctx) RH cmb compress compressN k t =
      recStateCommit (CH_faithful8 fold8 permW ctx) RH cmb compress compressN k' t) :
    nonceOf (k.cell agent) = nonceOf (k'.cell agent)
      ∨ FaithfulCommitColl fold8 permW ctx cmb compress compressN RH k k' t :=
  Or.imp_left (fun hk => congrArg (fun s => nonceOf (RecordKernelState.cell s agent)) hk)
    (recStateCommit_binds_kernel_faithful_or_collides fold8 permW ctx cmb compress compressN RH
      hRest k k' t hwf hwf' hfin hfin' hroot)

/-- **⚑ THE PER-INSTANCE REPLAY TOOTH** — two states with different agent nonces cannot share the
faithful root unless the NAMED residual fires at exactly that pair. -/
theorem nonce_difference_reduces_perInstance (fold8 : AuthorityFold8)
    (permW : List Int → List Int)
    (ctx : RotatedContextProvider) (cmb compress : Int → Int → Int)
    (compressN : List Int → Int) (RH : RecordKernelState → Int)
    (hRest : RestHashIffFrameFin RH) (k k' : RecordKernelState) (t : Turn) (agent : CellId)
    (hwf : AccountsWF k) (hwf' : AccountsWF k')
    (hfin : FiniteRepresentable k) (hfin' : FiniteRepresentable k')
    (hnonce : nonceOf (k.cell agent) ≠ nonceOf (k'.cell agent))
    (hroot : recStateCommit (CH_faithful8 fold8 permW ctx) RH cmb compress compressN k t =
      recStateCommit (CH_faithful8 fold8 permW ctx) RH cmb compress compressN k' t) :
    FaithfulCommitColl fold8 permW ctx cmb compress compressN RH k k' t :=
  (commit_binds_nonce_faithful_or_collides fold8 permW ctx cmb compress compressN RH hRest
    k k' t agent hwf hwf' hfin hfin' hroot).resolve_left hnonce

/-- ⚠ The cash-out from the NAMED residual to the FREE apex break — the direction that forgets the
pair. Used only to re-derive the retained bridges below; nothing on a ported path travels this way
(`StateCommitReduce.orBreak_stateBreakP_iff_True` is why). -/
theorem stateBreakP_of_recStateCommitColl (CH : CellId → Value → Int)
    (RH : RecordKernelState → Int) (cmb compress : Int → Int → Int) (compressN : List Int → Int)
    {k k' : RecordKernelState} {t : Turn}
    (h : RecStateCommitColl CH RH cmb compress compressN k k' t) :
    StateBreakP CH cmb compress compressN := by
  rcases h with hr | hn | hf | hm
  · exact StateBreakP.ofCmb CH cmb compress compressN hr.extracts
  · exact StateBreakP.ofCompress CH cmb compress compressN hn.extracts
  · rcases hf.extracts with hs | hc
    · exact StateBreakP.ofSponge CH cmb compress compressN hs
    · exact StateBreakP.ofCell CH cmb compress compressN hc
  · rcases hm.extracts with hn2 | hc
    · exact StateBreakP.ofCompress CH cmb compress compressN hn2
    · exact StateBreakP.ofCell CH cmb compress compressN hc

/-- ⚠ The named residual cashes out as the FREE `FaithfulBreakGlobal` — the direction that forgets
the pair. Only the retained `⚠ BRIDGE ONLY` theorems travel this way. -/
theorem faithfulBreakGlobal_of_faithfulCommitColl (fold8 : AuthorityFold8)
    (permW : List Int → List Int) (hW : Poseidon2Width8 permW)
    (ctx : RotatedContextProvider) (cmb compress : Int → Int → Int)
    (compressN : List Int → Int) (RH : RecordKernelState → Int)
    {k k' : RecordKernelState} {t : Turn}
    (h : FaithfulCommitColl fold8 permW ctx cmb compress compressN RH k k' t) :
    FaithfulBreakGlobal fold8 permW cmb compress compressN :=
  stateBreak_faithful_reduces fold8 permW hW ctx cmb compress compressN
    (stateBreakP_of_recStateCommitColl (CH_faithful8 fold8 permW ctx) RH cmb compress compressN h)

/-- **⚑ THE NAMED RESIDUAL, CASHED OUT TO THE DEPLOYED SURFACE — STILL PER-INSTANCE.** Every leaf
disjunct of `FaithfulCommitColl` is pushed through `cellLeafColl_faithful8_reduces` to a genuine
eight-lane authority collision or a genuine wide-chain collision AT THE PAIR THAT LEAF WAS OPENED AT;
the combiner/node/sponge disjuncts are already at their named argument tuples. Nothing is forgotten,
so unlike `faithfulBreakGlobal_of_faithfulCommitColl` this direction is usable on a live path. -/
theorem faithfulBreak_of_faithfulCommitColl (fold8 : AuthorityFold8)
    (permW : List Int → List Int) (hW : Poseidon2Width8 permW)
    (ctx : RotatedContextProvider) (cmb compress : Int → Int → Int)
    (compressN : List Int → Int) (RH : RecordKernelState → Int)
    {k k' : RecordKernelState} {t : Turn}
    (h : FaithfulCommitColl fold8 permW ctx cmb compress compressN RH k k' t) :
    FaithfulBreak fold8 permW ctx cmb compress compressN RH k k' t := by
  rcases h with hroot | hnode | hframe | hmoved
  · exact Or.inl hroot
  · exact Or.inr (Or.inl hnode)
  · rcases hframe with hcn | ⟨c, hc, hl⟩
    · exact Or.inr (Or.inr (Or.inl hcn))
    · exact Or.inr (Or.inr (Or.inr (Or.inl
        ⟨c, hc, faithfulLeafBreak_of_cellLeafColl fold8 permW hW ctx c _ _ hl⟩)))
  · rcases hmoved with hn | hl | hl
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
        (faithfulLeafBreak_of_cellLeafColl fold8 permW hW ctx t.src _ _ hl))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (faithfulLeafBreak_of_cellLeafColl fold8 permW hW ctx t.dst _ _ hl))))))

/-- **⚑⚑ THE LIVE BINDING CONSUMER, NARROWED.** Equal live-wide faithful roots determine the entire
kernel, OR one of the five commitment primitives collides AT AN ARGUMENT PAIR THIS OPENING NAMES.
No injectivity hypothesis and — since 2026-08-01 — no global collision existential either: the break
disjunct is `FaithfulBreak … k k' t`, which `noFaithfulBreak_diag` refutes on the diagonal at EVERY
deployment. This is what `Circuit/Freshness`'s "the live binding consumer" can now mean without a
caveat. -/
theorem recStateCommit_binds_kernel_faithful (fold8 : AuthorityFold8)
    (permW : List Int → List Int) (hW : Poseidon2Width8 permW)
    (ctx : RotatedContextProvider) (cmb compress : Int → Int → Int)
    (compressN : List Int → Int) (RH : RecordKernelState → Int)
    (hRest : RestHashIffFrameFin RH) (k k' : RecordKernelState) (t : Turn)
    (hwf : AccountsWF k) (hwf' : AccountsWF k')
    (hfin : FiniteRepresentable k) (hfin' : FiniteRepresentable k')
    (hroot : recStateCommit (CH_faithful8 fold8 permW ctx) RH cmb compress compressN k t =
      recStateCommit (CH_faithful8 fold8 permW ctx) RH cmb compress compressN k' t) :
    k = k' ∨ FaithfulBreak fold8 permW ctx cmb compress compressN RH k k' t :=
  Or.imp_right (faithfulBreak_of_faithfulCommitColl fold8 permW hW ctx cmb compress compressN RH)
    (recStateCommit_binds_kernel_faithful_or_collides fold8 permW ctx cmb compress compressN RH
      hRest k k' t hwf hwf' hfin hfin' hroot)

/-- ⚠ **BRIDGE ONLY (2026-08-01).** The pre-narrowing conclusion: `FaithfulBreakGlobal` is a five-way
disjunction of GLOBAL existentials whose first disjunct pigeonhole supplies at every deployed sponge,
so THIS dichotomy is `True` as stated (`orFaithfulBreakGlobal_iff_True`) and the binding it announces
is carried by the break branch. Retained only so the strength relation to the narrowed theorem above
is machine-checked. Do not consume it. -/
theorem recStateCommit_binds_kernel_faithful_global (fold8 : AuthorityFold8)
    (permW : List Int → List Int) (hW : Poseidon2Width8 permW)
    (ctx : RotatedContextProvider) (cmb compress : Int → Int → Int)
    (compressN : List Int → Int) (RH : RecordKernelState → Int)
    (hRest : RestHashIffFrameFin RH) (k k' : RecordKernelState) (t : Turn)
    (hwf : AccountsWF k) (hwf' : AccountsWF k')
    (hfin : FiniteRepresentable k) (hfin' : FiniteRepresentable k')
    (hroot : recStateCommit (CH_faithful8 fold8 permW ctx) RH cmb compress compressN k t =
      recStateCommit (CH_faithful8 fold8 permW ctx) RH cmb compress compressN k' t) :
    k = k' ∨ FaithfulBreakGlobal fold8 permW cmb compress compressN :=
  Or.imp_right
    (faithfulBreakGlobal_of_faithfulCommitColl fold8 permW hW ctx cmb compress compressN RH)
    (recStateCommit_binds_kernel_faithful_or_collides fold8 permW ctx cmb compress compressN RH
      hRest k k' t hwf hwf' hfin hfin' hroot)

/-- The local adversarial event.  Unlike global `¬ ∃ collision`, its negation is satisfiable for
honest/equal openings and is the event on which deterministic recovery is meant to run. -/
def KernelEquivocation (fold8 : AuthorityFold8) (permW : List Int → List Int)
    (ctx : RotatedContextProvider)
    (cmb compress : Int → Int → Int) (compressN : List Int → Int)
    (RH : RecordKernelState → Int) (k k' : RecordKernelState) (t : Turn) : Prop :=
  AccountsWF k ∧ AccountsWF k' ∧ FiniteRepresentable k ∧ FiniteRepresentable k' ∧ k ≠ k' ∧
    recStateCommit (CH_faithful8 fold8 permW ctx) RH cmb compress compressN k t =
      recStateCommit (CH_faithful8 fold8 permW ctx) RH cmb compress compressN k' t

/-- An equivocation at this named opening EXHIBITS a collision of one of the five primitives at an
argument pair the opening itself names — not merely "some collision exists somewhere". -/
theorem kernelEquivocation_reduces (fold8 : AuthorityFold8)
    (permW : List Int → List Int) (hW : Poseidon2Width8 permW)
    (ctx : RotatedContextProvider) (cmb compress : Int → Int → Int)
    (compressN : List Int → Int) (RH : RecordKernelState → Int)
    (hRest : RestHashIffFrameFin RH) (k k' : RecordKernelState) (t : Turn)
    (heqv : KernelEquivocation fold8 permW ctx cmb compress compressN RH k k' t) :
    FaithfulBreak fold8 permW ctx cmb compress compressN RH k k' t := by
  rcases heqv with ⟨hwf, hwf', hfin, hfin', hne, hroot⟩
  rcases recStateCommit_binds_kernel_faithful fold8 permW hW ctx cmb compress compressN RH hRest
      k k' t hwf hwf' hfin hfin' hroot with hk | hb
  · exact absurd hk hne
  · exact hb

/-- Non-vacuous recovery: on a sampled key/run where this adversary did not equivocate, equal roots
recover equal states.  The premise is witnessed by `kernelEquivocation_refl_false`; it is not the
unsatisfiable assertion that a finite hash has no collisions anywhere. -/
theorem recStateCommit_binds_kernel_faithful_on_adversary_failure (fold8 : AuthorityFold8)
    (permW : List Int → List Int) (ctx : RotatedContextProvider)
    (cmb compress : Int → Int → Int)
    (compressN : List Int → Int) (RH : RecordKernelState → Int)
    (k k' : RecordKernelState) (t : Turn)
    (hNo : ¬ KernelEquivocation fold8 permW ctx cmb compress compressN RH k k' t)
    (hwf : AccountsWF k) (hwf' : AccountsWF k')
    (hfin : FiniteRepresentable k) (hfin' : FiniteRepresentable k')
    (hroot : recStateCommit (CH_faithful8 fold8 permW ctx) RH cmb compress compressN k t =
      recStateCommit (CH_faithful8 fold8 permW ctx) RH cmb compress compressN k' t) : k = k' := by
  by_contra hne
  exact hNo ⟨hwf, hwf', hfin, hfin', hne, hroot⟩

theorem kernelEquivocation_refl_false (fold8 : AuthorityFold8) (permW : List Int → List Int)
    (ctx : RotatedContextProvider) (cmb compress : Int → Int → Int)
    (compressN : List Int → Int) (RH : RecordKernelState → Int)
    (k : RecordKernelState) (t : Turn) :
    ¬ KernelEquivocation fold8 permW ctx cmb compress compressN RH k k t := by
  intro h
  exact h.2.2.2.2.1 rfl

/-- Faithful nonce binding in reduction form, at the NAMED opening: equal faithful roots give equal
agent nonces unless one of the five primitives collides at an argument pair this opening names. -/
theorem commit_binds_nonce_faithful (fold8 : AuthorityFold8)
    (permW : List Int → List Int) (hW : Poseidon2Width8 permW)
    (ctx : RotatedContextProvider) (cmb compress : Int → Int → Int)
    (compressN : List Int → Int) (RH : RecordKernelState → Int)
    (hRest : RestHashIffFrameFin RH) (k k' : RecordKernelState) (t : Turn) (agent : CellId)
    (hwf : AccountsWF k) (hwf' : AccountsWF k')
    (hfin : FiniteRepresentable k) (hfin' : FiniteRepresentable k')
    (hroot : recStateCommit (CH_faithful8 fold8 permW ctx) RH cmb compress compressN k t =
      recStateCommit (CH_faithful8 fold8 permW ctx) RH cmb compress compressN k' t) :
    nonceOf (k.cell agent) = nonceOf (k'.cell agent) ∨
      FaithfulBreak fold8 permW ctx cmb compress compressN RH k k' t := by
  rcases recStateCommit_binds_kernel_faithful fold8 permW hW ctx cmb compress compressN RH hRest
      k k' t hwf hwf' hfin hfin' hroot with hk | hb
  · exact Or.inl (congrArg (fun s => nonceOf (s.cell agent)) hk)
  · exact Or.inr hb

/-- Pairwise replay tooth: two states with different agent nonces cannot share the faithful root
unless a concrete commitment collision is exhibited AT AN ARGUMENT PAIR THOSE TWO STATES NAME. (Until
2026-08-01 the conclusion was `FaithfulBreakGlobal`, and this sentence was false: that event holds at
every deployed sponge, so the two states could share the root with nothing exhibited at all.) -/
theorem nonce_difference_reduces (fold8 : AuthorityFold8)
    (permW : List Int → List Int) (hW : Poseidon2Width8 permW)
    (ctx : RotatedContextProvider) (cmb compress : Int → Int → Int)
    (compressN : List Int → Int) (RH : RecordKernelState → Int)
    (hRest : RestHashIffFrameFin RH) (k k' : RecordKernelState) (t : Turn) (agent : CellId)
    (hwf : AccountsWF k) (hwf' : AccountsWF k')
    (hfin : FiniteRepresentable k) (hfin' : FiniteRepresentable k')
    (hnonce : nonceOf (k.cell agent) ≠ nonceOf (k'.cell agent))
    (hroot : recStateCommit (CH_faithful8 fold8 permW ctx) RH cmb compress compressN k t =
      recStateCommit (CH_faithful8 fold8 permW ctx) RH cmb compress compressN k' t) :
    FaithfulBreak fold8 permW ctx cmb compress compressN RH k k' t := by
  rcases commit_binds_nonce_faithful fold8 permW hW ctx cmb compress compressN RH hRest
      k k' t agent hwf hwf' hfin hfin' hroot with hn | hb
  · exact absurd hn hnonce
  · exact hb

/-! ### The faithful commitment surface and the full cross-turn no-replay consumer. -/

/-- The deployed binding surface without impossible injectivity fields.  Its only structural
carrier is the rest-frame correspondence; every hash failure is returned as `S.Break k k' t`, the
narrowed per-opening `FaithfulBreak`. -/
structure FaithfulCommitSurface where
  fold8 : AuthorityFold8
  permW : List Int → List Int
  width8 : Poseidon2Width8 permW
  ctx : RotatedContextProvider
  cmb : Int → Int → Int
  compress : Int → Int → Int
  compressN : List Int → Int
  RH : RecordKernelState → Int
  restFrame : RestHashIffFrameFin RH

noncomputable def FaithfulCommitSurface.commit (S : FaithfulCommitSurface)
    (k : RecordKernelState) (t : Turn) : Int :=
  recStateCommit (CH_faithful8 S.fold8 S.permW S.ctx) S.RH S.cmb S.compress S.compressN k t

/-- The surface's break event AT A NAMED OPENING (narrowed 2026-08-01: it used to be a 0-ary
`FaithfulBreakGlobal` and therefore `True` at every deployed sponge). -/
abbrev FaithfulCommitSurface.Break (S : FaithfulCommitSurface) (k k' : RecordKernelState)
    (t : Turn) : Prop :=
  FaithfulBreak S.fold8 S.permW S.ctx S.cmb S.compress S.compressN S.RH k k' t

theorem FaithfulCommitSurface.commit_binds_kernel (S : FaithfulCommitSurface)
    (k k' : RecordKernelState) (t : Turn) (hwf : AccountsWF k) (hwf' : AccountsWF k')
    (hfin : FiniteRepresentable k) (hfin' : FiniteRepresentable k')
    (hroot : S.commit k t = S.commit k' t) : k = k' ∨ S.Break k k' t :=
  recStateCommit_binds_kernel_faithful S.fold8 S.permW S.width8 S.ctx
    S.cmb S.compress S.compressN S.RH
    S.restFrame k k' t hwf hwf' hfin hfin' hroot

theorem FaithfulCommitSurface.commit_binds_nonce (S : FaithfulCommitSurface)
    (k k' : RecordKernelState) (t : Turn) (agent : CellId)
    (hwf : AccountsWF k) (hwf' : AccountsWF k')
    (hfin : FiniteRepresentable k) (hfin' : FiniteRepresentable k')
    (hroot : S.commit k t = S.commit k' t) :
    nonceOf (k.cell agent) = nonceOf (k'.cell agent) ∨ S.Break k k' t :=
  commit_binds_nonce_faithful S.fold8 S.permW S.width8 S.ctx
    S.cmb S.compress S.compressN S.RH S.restFrame
    k k' t agent hwf hwf' hfin hfin' hroot

/-- A verified sequence at the faithful surface.  The executor supplies `nonceMono` from its
never-rolled-back prologue; the commitment theorem supplies binding modulo explicit collisions. -/
structure FaithfulCommitChain (S : FaithfulCommitSurface) (agent : CellId) (t : Turn) where
  seq : Nat → RecordKernelState
  wf : ∀ i, AccountsWF (seq i)
  /-- ⚑ every state in the chain has FINITE per-cell support — the new structural side condition of
  the commitment binding after the 2026-07-31 rest-frame cutover (`Circuit.RestFrameFin`). -/
  finrep : ∀ i, FiniteRepresentable (seq i)
  nonceMono : ∀ {i j : Nat}, i < j → nonceOf ((seq i).cell agent) < nonceOf ((seq j).cell agent)

noncomputable def FaithfulCommitChain.commitAt {S : FaithfulCommitSurface} {agent : CellId}
    {t : Turn} (C : FaithfulCommitChain S agent t) (i : Nat) : Int := S.commit (C.seq i) t

def FaithfulCommitChain.LiveCommitMatches {S : FaithfulCommitSurface} {agent : CellId}
    {t : Turn} (C : FaithfulCommitChain S agent t) (i : Nat) (preCommit : Int) : Prop :=
  C.commitAt i = preCommit

/-- Full cross-turn no replay on the deployed faithful surface: one live pre-anchor cannot match two
different indices unless the proof exhibits a concrete authority/Poseidon collision AT AN ARGUMENT
PAIR THE TWO OPENED STATES NAME.  (Before 2026-08-01 the break disjunct was `FaithfulBreakGlobal`
and the sentence was false — that event holds at every deployed sponge.) -/
theorem no_replay_faithful {S : FaithfulCommitSurface} {agent : CellId} {t : Turn}
    (C : FaithfulCommitChain S agent t) {i j : Nat} {preCommit : Int}
    (hi : C.LiveCommitMatches i preCommit) (hj : C.LiveCommitMatches j preCommit) :
    i = j ∨ S.Break (C.seq i) (C.seq j) t := by
  by_cases hij : i = j
  · exact Or.inl hij
  · apply Or.inr
    have hroot : S.commit (C.seq i) t = S.commit (C.seq j) t := hi.trans hj.symm
    rcases Nat.lt_or_gt_of_ne hij with hlt | hgt
    · exact nonce_difference_reduces S.fold8 S.permW S.width8 S.ctx
        S.cmb S.compress S.compressN S.RH S.restFrame
        (C.seq i) (C.seq j) t agent (C.wf i) (C.wf j) (C.finrep i) (C.finrep j)
        (ne_of_lt (C.nonceMono hlt)) hroot
    · have hn : nonceOf ((C.seq i).cell agent) ≠ nonceOf ((C.seq j).cell agent) :=
        ne_of_gt (C.nonceMono hgt)
      exact nonce_difference_reduces S.fold8 S.permW S.width8 S.ctx
        S.cmb S.compress S.compressN S.RH S.restFrame
        (C.seq i) (C.seq j) t agent (C.wf i) (C.wf j) (C.finrep i) (C.finrep j) hn hroot

/-! ### ⚑⚑ The surface and the no-replay consumer, PORTED to the per-instance residual. -/

/-- **`S.CommitColl k k' t`** — the surface's per-instance residual: the four commitment primitives at
the SPECIFIC argument pairs the whole-kernel extraction visits for this opening. Replaces `S.Break`,
which is `FaithfulBreak` and therefore free at deployed parameters. -/
def FaithfulCommitSurface.CommitColl (S : FaithfulCommitSurface) (k k' : RecordKernelState)
    (t : Turn) : Prop :=
  FaithfulCommitColl S.fold8 S.permW S.ctx S.cmb S.compress S.compressN S.RH k k' t

/-- The surface binding, ported: equal commits determine the kernel or the NAMED residual holds. -/
theorem FaithfulCommitSurface.commit_binds_kernel_or_collides (S : FaithfulCommitSurface)
    (k k' : RecordKernelState) (t : Turn) (hwf : AccountsWF k) (hwf' : AccountsWF k')
    (hfin : FiniteRepresentable k) (hfin' : FiniteRepresentable k')
    (hroot : S.commit k t = S.commit k' t) : k = k' ∨ S.CommitColl k k' t :=
  recStateCommit_binds_kernel_faithful_or_collides S.fold8 S.permW S.ctx
    S.cmb S.compress S.compressN S.RH S.restFrame k k' t hwf hwf' hfin hfin' hroot

/-- **S3** — the surface binding from the per-instance side condition at the named opening. -/
theorem FaithfulCommitSurface.commit_binds_kernel_of_noColl (S : FaithfulCommitSurface)
    (k k' : RecordKernelState) (t : Turn) (hwf : AccountsWF k) (hwf' : AccountsWF k')
    (hfin : FiniteRepresentable k) (hfin' : FiniteRepresentable k')
    (hno : ¬ S.CommitColl k k' t)
    (hroot : S.commit k t = S.commit k' t) : k = k' :=
  (S.commit_binds_kernel_or_collides k k' t hwf hwf' hfin hfin' hroot).resolve_right hno

/-- **⚑ THE SURFACE NONCE BINDING, PORTED.** `commit_binds_nonce` had no per-instance twin: it
returned `S.Break`, which before the narrowing was `FaithfulBreakGlobal` and free. This returns the
NAMED residual at the opening `(k, k', t)`. -/
theorem FaithfulCommitSurface.commit_binds_nonce_or_collides (S : FaithfulCommitSurface)
    (k k' : RecordKernelState) (t : Turn) (agent : CellId)
    (hwf : AccountsWF k) (hwf' : AccountsWF k')
    (hfin : FiniteRepresentable k) (hfin' : FiniteRepresentable k')
    (hroot : S.commit k t = S.commit k' t) :
    nonceOf (k.cell agent) = nonceOf (k'.cell agent) ∨ S.CommitColl k k' t :=
  commit_binds_nonce_faithful_or_collides S.fold8 S.permW S.ctx S.cmb S.compress S.compressN S.RH
    S.restFrame k k' t agent hwf hwf' hfin hfin' hroot

/-- **S3** — the surface nonce binding from the per-instance side condition at the named opening. -/
theorem FaithfulCommitSurface.commit_binds_nonce_of_noColl (S : FaithfulCommitSurface)
    (k k' : RecordKernelState) (t : Turn) (agent : CellId)
    (hwf : AccountsWF k) (hwf' : AccountsWF k')
    (hfin : FiniteRepresentable k) (hfin' : FiniteRepresentable k')
    (hno : ¬ S.CommitColl k k' t)
    (hroot : S.commit k t = S.commit k' t) :
    nonceOf (k.cell agent) = nonceOf (k'.cell agent) :=
  (S.commit_binds_nonce_or_collides k k' t agent hwf hwf' hfin hfin' hroot).resolve_right hno

/-- **⚑⚑ FULL CROSS-TURN NO-REPLAY AT DEPLOYED PARAMETERS.** One live pre-anchor cannot match two
different indices unless the NAMED residual fires at exactly the pair of states those two indices
open. `no_replay_faithful` (retained below) concluded `i = j ∨ S.Break`, whose right disjunct is
supplied by pigeonhole at every deployed sponge — it excluded nothing. This one names the pair. -/
theorem no_replay_faithful_or_collides {S : FaithfulCommitSurface} {agent : CellId} {t : Turn}
    (C : FaithfulCommitChain S agent t) {i j : Nat} {preCommit : Int}
    (hi : C.LiveCommitMatches i preCommit) (hj : C.LiveCommitMatches j preCommit) :
    i = j ∨ S.CommitColl (C.seq i) (C.seq j) t := by
  by_cases hij : i = j
  · exact Or.inl hij
  · refine Or.inr ?_
    have hroot : S.commit (C.seq i) t = S.commit (C.seq j) t := hi.trans hj.symm
    have hn : nonceOf ((C.seq i).cell agent) ≠ nonceOf ((C.seq j).cell agent) := by
      rcases Nat.lt_or_gt_of_ne hij with hlt | hgt
      · exact ne_of_lt (C.nonceMono hlt)
      · exact ne_of_gt (C.nonceMono hgt)
    exact nonce_difference_reduces_perInstance S.fold8 S.permW S.ctx S.cmb S.compress S.compressN
      S.RH S.restFrame (C.seq i) (C.seq j) t agent (C.wf i) (C.wf j) (C.finrep i) (C.finrep j)
      hn hroot

/-- **S3** — no replay from the per-instance side condition at the two opened states. -/
theorem no_replay_faithful_of_noColl {S : FaithfulCommitSurface} {agent : CellId} {t : Turn}
    (C : FaithfulCommitChain S agent t) {i j : Nat} {preCommit : Int}
    (hno : ¬ S.CommitColl (C.seq i) (C.seq j) t)
    (hi : C.LiveCommitMatches i preCommit) (hj : C.LiveCommitMatches j preCommit) : i = j :=
  (no_replay_faithful_or_collides C hi hj).resolve_right hno

/-- Exact recovery on the satisfiable local adversary-failure event.  It quantifies only the pairs
the supplied chain opens, never global nonexistence of finite-hash collisions. -/
theorem no_replay_faithful_on_adversary_failure {S : FaithfulCommitSurface}
    {agent : CellId} {t : Turn} (C : FaithfulCommitChain S agent t)
    (hNo : ∀ a b : Nat,
      ¬ KernelEquivocation S.fold8 S.permW S.ctx S.cmb S.compress S.compressN S.RH
        (C.seq a) (C.seq b) t)
    {i j : Nat} {preCommit : Int}
    (hi : C.LiveCommitMatches i preCommit) (hj : C.LiveCommitMatches j preCommit) : i = j := by
  by_contra hij
  have hroot : S.commit (C.seq i) t = S.commit (C.seq j) t := hi.trans hj.symm
  have hnonce : nonceOf ((C.seq i).cell agent) ≠ nonceOf ((C.seq j).cell agent) := by
    rcases Nat.lt_or_gt_of_ne hij with hlt | hgt
    · exact ne_of_lt (C.nonceMono hlt)
    · exact ne_of_gt (C.nonceMono hgt)
  have hstate : C.seq i ≠ C.seq j := by
    intro hs
    apply hnonce
    exact congrArg (fun k => nonceOf (k.cell agent)) hs
  exact hNo i j ⟨C.wf i, C.wf j, C.finrep i, C.finrep j, hstate, hroot⟩

/-! ### Full transfer soundness, with collisions returned instead of injectivity assumed.

⚑⚑ **THE HEADLINE GOT ITS TWIN (2026-08-01).** `transfer_circuit_full_sound_faithful` routed through
`StateCommitReduce.frameDigestBindsCells_orBreak` and `movedDigestBindsCells_orBreak`, BOTH of which
return the free `StateBreakP` (`orBreak_stateBreakP_iff_True`), and its docstring sold the ABSENCE of
the `cellLeafInjective` / `compressInjective` / `compressNInjective` premises as a strength. It is not
one on its own: the premise left, and a free disjunct arrived. The per-instance replacements for both
raw layers are `StateCommitLeafRegrounded.frameDigest_binds_or_collides` /
`movedDigest_binds_or_collides`, whose residuals name the pairs; the twin below routes through those
and drops `Poseidon2Width8` as well (only the global cash-out ever needed it). -/

/-- **`TransferFaithfulColl` — THE PER-INSTANCE RESIDUAL OF FULL-TRANSFER SOUNDNESS.** The two raw
digest layers the proof visits, stated at the pairs it visits them at: the frame sponge (and its
leaves) at `(k, k')` over THIS turn's carrier, and the moved node (and its two leaves) at
`(k'.cell, recTransfer k.cell …)` — precisely the comparison the `cSMovedBind` gate makes. Note the
moved pair is NOT `(k.cell, k'.cell)`: full-transfer soundness compares the post state against the
SPEC's debit/credit of the pre leaves, so this residual is genuinely different from
`FaithfulCommitColl`'s and cannot be borrowed from it. -/
def TransferFaithfulColl (fold8 : AuthorityFold8) (permW : List Int → List Int)
    (ctx : RotatedContextProvider) (compress : Int → Int → Int) (compressN : List Int → Int)
    (k k' : RecordKernelState) (t : Turn) : Prop :=
  FrameColl (CH_faithful8 fold8 permW ctx) compressN k k' (frameCarrier k t)
    ∨ MovedColl (CH_faithful8 fold8 permW ctx) compress
        k'.cell (recTransfer k.cell t.src t.dst t.amt) t.src t.dst

/-- **⚑⚑ FULL-TRANSFER SOUNDNESS AT DEPLOYED PARAMETERS.** A satisfying full-state transfer witness
reconstructs the COMPLETE `TransferSpec` — the guard, the whole cell map, and all eighteen non-cell
frame components — OR the NAMED residual `TransferFaithfulColl` holds at exactly the two digest
openings this witness produced. No injectivity hypothesis, no global collision existential, and no
`Poseidon2Width8` carrier. -/
theorem transfer_circuit_full_sound_faithful_or_collides (fold8 : AuthorityFold8)
    (permW : List Int → List Int)
    (ctx : RotatedContextProvider) (cmb compress : Int → Int → Int)
    (compressN : List Int → Int) (RH : RecordKernelState → Int)
    (hRest : RestHashIffFrameFin RH) (k : RecordKernelState) (t : Turn) (k' : RecordKernelState)
    (hwf : AccountsWF k) (hwf' : AccountsWF k')
    (hfin : FiniteRepresentable k) (hfin' : FiniteRepresentable k')
    (h : satisfiedS cmb compress
      (encodeS (CH_faithful8 fold8 permW ctx) RH cmb compress compressN k t k')) :
    TransferSpec k t k' ∨ TransferFaithfulColl fold8 permW ctx compress compressN k k' t := by
  obtain ⟨hsat, _hcommit⟩ := h
  have e0 := encodeS_agrees_encodeT (CH_faithful8 fold8 permW ctx) RH cmb compress compressN
    k t k' vSrcPre (by decide)
  have e1 := encodeS_agrees_encodeT (CH_faithful8 fold8 permW ctx) RH cmb compress compressN
    k t k' vDstPre (by decide)
  have e2 := encodeS_agrees_encodeT (CH_faithful8 fold8 permW ctx) RH cmb compress compressN
    k t k' vSrcPost (by decide)
  have e3 := encodeS_agrees_encodeT (CH_faithful8 fold8 permW ctx) RH cmb compress compressN
    k t k' vDstPost (by decide)
  have e4 := encodeS_agrees_encodeT (CH_faithful8 fold8 permW ctx) RH cmb compress compressN
    k t k' vAmt (by decide)
  have e5 := encodeS_agrees_encodeT (CH_faithful8 fold8 permW ctx) RH cmb compress compressN
    k t k' vTAuth (by decide)
  have e6 := encodeS_agrees_encodeT (CH_faithful8 fold8 permW ctx) RH cmb compress compressN
    k t k' vTNonneg (by decide)
  have e7 := encodeS_agrees_encodeT (CH_faithful8 fold8 permW ctx) RH cmb compress compressN
    k t k' vTAvail (by decide)
  have e8 := encodeS_agrees_encodeT (CH_faithful8 fold8 permW ctx) RH cmb compress compressN
    k t k' vTDistinct (by decide)
  have e9 := encodeS_agrees_encodeT (CH_faithful8 fold8 permW ctx) RH cmb compress compressN
    k t k' vTSrcLive (by decide)
  have e10 := encodeS_agrees_encodeT (CH_faithful8 fold8 permW ctx) RH cmb compress compressN
    k t k' vTDstLive (by decide)
  have htsat : satisfied transferCircuit (encodeT k t k') := by
    intro c hc
    have hc' : c ∈ stateCircuit := by
      unfold stateCircuit
      exact List.mem_append_left _ hc
    have hcS := hsat c hc'
    unfold transferCircuit at hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      · unfold Constraint.holds at hcS ⊢
        simp only [cTAuth, cTNonneg, cTAvail, cTDistinct, cTSrcLive, cTDstLive, cTDebit,
          cTCredit, cTConserve, Expr.eval, e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10] at hcS ⊢
        exact hcS
  obtain ⟨hg, _hdeb, _hcre, _hcons⟩ := transfer_circuit_sound k t k' htsat
  obtain ⟨hauth, hnn, hav, hne, hsrc, hdst⟩ := hg
  have hrestgate : cSRestFrame.holds
      (encodeS (CH_faithful8 fold8 permW ctx) RH cmb compress compressN k t k') :=
    hsat cSRestFrame (by unfold stateCircuit; simp)
  have hframegate : cSFrameReuse.holds
      (encodeS (CH_faithful8 fold8 permW ctx) RH cmb compress compressN k t k') :=
    hsat cSFrameReuse (by unfold stateCircuit; simp)
  have hmovedgate : cSMovedBind.holds
      (encodeS (CH_faithful8 fold8 permW ctx) RH cmb compress compressN k t k') :=
    hsat cSMovedBind (by unfold stateCircuit; simp)
  have hRHeq : RH k = RH k' :=
    (srestframe_iff (CH_faithful8 fold8 permW ctx) RH cmb compress compressN k t k').mp hrestgate
  obtain ⟨hAcc, hCaps, hBal, hNul, hRev, hCom, hSC, hFac, hLif, hDC, hDel, hDgs,
    hDE, hDEA, hHeaps, hNR, hRR, hCR⟩ := (hRest k k' hfin hfin').mp hRHeq
  have hfdeq : frameDigest (CH_faithful8 fold8 permW ctx) compressN k (frameCarrier k t) =
      frameDigest (CH_faithful8 fold8 permW ctx) compressN k' (frameCarrier k t) :=
    (sframereuse_iff (CH_faithful8 fold8 permW ctx) RH cmb compress compressN k t k').mp hframegate
  rcases frameDigest_binds_or_collides
      (CH_faithful8 fold8 permW ctx) compressN k k' (frameCarrier k t) hfdeq with
    hcellframe | hb
  · have hmoveq : movedDigest (CH_faithful8 fold8 permW ctx) compress k'.cell t.src t.dst =
        movedDigest (CH_faithful8 fold8 permW ctx) compress
          (recTransfer k.cell t.src t.dst t.amt) t.src t.dst :=
      (smovedbind_iff (CH_faithful8 fold8 permW ctx) RH cmb compress compressN k t k').mp hmovedgate
    rcases movedDigest_binds_or_collides
        (CH_faithful8 fold8 permW ctx) compress k'.cell
        (recTransfer k.cell t.src t.dst t.amt) t.src t.dst hmoveq with hmove | hb
    · obtain ⟨hmsrc, hmdst⟩ := hmove
      have hcellmap : k'.cell = recTransfer k.cell t.src t.dst t.amt := by
        funext c
        by_cases hcsrc : c = t.src
        · subst hcsrc
          exact hmsrc
        · by_cases hcdst : c = t.dst
          · subst hcdst
            exact hmdst
          · by_cases hcacc : c ∈ k.accounts
            · have hmem : c ∈ frameCarrier k t := by
                unfold frameCarrier
                simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton, not_or]
                exact ⟨hcacc, hcsrc, hcdst⟩
              rw [← hcellframe c hmem]
              simp only [recTransfer, if_neg hcsrc, if_neg hcdst]
            · have hk'acc : c ∉ k'.accounts := by
                rw [hAcc]
                exact hcacc
              rw [hwf' c hk'acc]
              simp only [recTransfer, if_neg hcsrc, if_neg hcdst]
              exact (hwf c hcacc).symm
      exact Or.inl ⟨⟨hauth, hnn, hav, hne, hsrc, hdst⟩, hcellmap,
        hAcc, hCaps, hBal, hNul, hRev, hCom, hSC, hFac, hLif, hDC, hDel, hDgs, hDE, hDEA,
        hHeaps, hNR, hRR, hCR⟩
    · exact Or.inr (Or.inr hb)
  · exact Or.inr (Or.inl hb)

/-- **S3** — the full `TransferSpec` from the PER-INSTANCE side condition at the two digest openings
this witness produced. -/
theorem transfer_circuit_full_sound_faithful_of_noColl (fold8 : AuthorityFold8)
    (permW : List Int → List Int)
    (ctx : RotatedContextProvider) (cmb compress : Int → Int → Int)
    (compressN : List Int → Int) (RH : RecordKernelState → Int)
    (hRest : RestHashIffFrameFin RH) (k : RecordKernelState) (t : Turn) (k' : RecordKernelState)
    (hwf : AccountsWF k) (hwf' : AccountsWF k')
    (hfin : FiniteRepresentable k) (hfin' : FiniteRepresentable k')
    (hno : ¬ TransferFaithfulColl fold8 permW ctx compress compressN k k' t)
    (h : satisfiedS cmb compress
      (encodeS (CH_faithful8 fold8 permW ctx) RH cmb compress compressN k t k')) :
    TransferSpec k t k' :=
  (transfer_circuit_full_sound_faithful_or_collides fold8 permW ctx cmb compress compressN RH
    hRest k t k' hwf hwf' hfin hfin' h).resolve_right hno

/-- ⚠ The transfer residual cashes out as the FREE `FaithfulBreakGlobal` — the direction that
forgets the pair, used only to re-derive the retained bridge below.  Both `FrameColl.extracts` and
`MovedColl.extracts` are TOTAL (they hand back the colliding pair), so the loss happens here and
nowhere earlier. -/
theorem faithfulBreakGlobal_of_transferFaithfulColl (fold8 : AuthorityFold8)
    (permW : List Int → List Int) (hW : Poseidon2Width8 permW)
    (ctx : RotatedContextProvider) (cmb compress : Int → Int → Int)
    (compressN : List Int → Int) {k k' : RecordKernelState} {t : Turn}
    (h : TransferFaithfulColl fold8 permW ctx compress compressN k k' t) :
    FaithfulBreakGlobal fold8 permW cmb compress compressN := by
  rcases h with hf | hm
  · rcases hf.extracts with hs | hc
    · exact Or.inl hs
    · rcases cellCollision_faithful8_reduces fold8 permW hW ctx hc with ha | hwide
      · exact Or.inr (Or.inr (Or.inr (Or.inl ha)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr hwide)))
  · rcases hm.extracts with hn | hc
    · exact Or.inr (Or.inr (Or.inl hn))
    · rcases cellCollision_faithful8_reduces fold8 permW hW ctx hc with ha | hwide
      · exact Or.inr (Or.inr (Or.inr (Or.inl ha)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr hwide)))

/-- ⚠ **BRIDGE ONLY (2026-08-01).** The pre-twin shape of the full-transfer headline. Its break
disjunct `FaithfulBreakGlobal` is supplied by pigeonhole at every deployed sponge
(`orFaithfulBreakGlobal_iff_True`), so this dichotomy is `True` as stated and reconstructs nothing.
⚠ THE OLD DOCSTRING SOLD THE ABSENCE of `cellLeafInjective` / `compressInjective` /
`compressNInjective` as a strength; it was not one on its own — the premise left and a free disjunct
arrived. Re-derived from `transfer_circuit_full_sound_faithful_or_collides` by forgetting the pair;
retained only so the strength relation is machine-checked. Consume the twin instead. -/
theorem transfer_circuit_full_sound_faithful (fold8 : AuthorityFold8)
    (permW : List Int → List Int) (hW : Poseidon2Width8 permW)
    (ctx : RotatedContextProvider) (cmb compress : Int → Int → Int)
    (compressN : List Int → Int) (RH : RecordKernelState → Int)
    (hRest : RestHashIffFrameFin RH) (k : RecordKernelState) (t : Turn) (k' : RecordKernelState)
    (hwf : AccountsWF k) (hwf' : AccountsWF k')
    (hfin : FiniteRepresentable k) (hfin' : FiniteRepresentable k')
    (h : satisfiedS cmb compress
      (encodeS (CH_faithful8 fold8 permW ctx) RH cmb compress compressN k t k')) :
    TransferSpec k t k' ∨ FaithfulBreakGlobal fold8 permW cmb compress compressN :=
  Or.imp_right
    (faithfulBreakGlobal_of_transferFaithfulColl fold8 permW hW ctx cmb compress compressN)
    (transfer_circuit_full_sound_faithful_or_collides fold8 permW ctx cmb compress compressN RH
      hRest k t k' hwf hwf' hfin hfin' h)

-- ⚑⚑ the PER-INSTANCE port (2026-08-01) — the statements that discriminate at deployed parameters.
#assert_axioms cellLeafColl_faithful8_reduces
#assert_axioms faithfulLeafBreak_of_cellLeafColl
#assert_axioms faithfulBreak_of_faithfulCommitColl
#assert_axioms recStateCommit_binds_kernel_faithful_or_collides
#assert_axioms recStateCommit_binds_kernel_faithful_of_noColl
#assert_axioms commit_binds_nonce_faithful_or_collides
#assert_axioms nonce_difference_reduces_perInstance
#assert_axioms FaithfulCommitSurface.commit_binds_kernel_or_collides
#assert_axioms FaithfulCommitSurface.commit_binds_kernel_of_noColl
#assert_axioms FaithfulCommitSurface.commit_binds_nonce_or_collides
#assert_axioms FaithfulCommitSurface.commit_binds_nonce_of_noColl
#assert_axioms no_replay_faithful_or_collides
#assert_axioms no_replay_faithful_of_noColl
#assert_axioms transfer_circuit_full_sound_faithful_or_collides
#assert_axioms transfer_circuit_full_sound_faithful_of_noColl
-- ⚑ the consumers NARROWED IN PLACE onto the per-opening `FaithfulBreak` (2026-08-01).
#assert_axioms recStateCommit_binds_kernel_faithful
#assert_axioms kernelEquivocation_reduces
#assert_axioms recStateCommit_binds_kernel_faithful_on_adversary_failure
#assert_axioms kernelEquivocation_refl_false
#assert_axioms commit_binds_nonce_faithful
#assert_axioms nonce_difference_reduces
#assert_axioms FaithfulCommitSurface.commit_binds_kernel
#assert_axioms FaithfulCommitSurface.commit_binds_nonce
#assert_axioms no_replay_faithful
#assert_axioms no_replay_faithful_on_adversary_failure
-- ⚠ the free-disjunct bridges at the RETIRED `FaithfulBreakGlobal`, retained WITH its refutation.
#assert_axioms faithfulBreakGlobal_free_of_fieldBounded
#assert_axioms orFaithfulBreakGlobal_iff_True
#assert_axioms faithfulBreakGlobal_of_faithfulBreak
#assert_axioms stateBreakP_of_recStateCommitColl
#assert_axioms faithfulBreakGlobal_of_faithfulCommitColl
#assert_axioms faithfulBreakGlobal_of_transferFaithfulColl
#assert_axioms stateBreak_faithful_reduces
#assert_axioms recStateCommit_binds_kernel_faithful_global
#assert_axioms transfer_circuit_full_sound_faithful

/-! ## 4. Both poles fire. -/

def plus4 : Int → Int → Int → Int → Int := fun a b c d => a + b + c + d

theorem plus4_collision : Compress4Collision plus4 :=
  ⟨100, 5, 0, 0, 99, 6, 0, 0, by decide, by decide⟩

def constantAuthorityFold : AuthorityFold := fun _ => 0

private def abstractA : AuthorityInput := .abstract (.int 0)
private def abstractB : AuthorityInput := .abstract (.int 1)

theorem constantAuthorityFold_collision : AuthorityDigestCollision constantAuthorityFold :=
  ⟨abstractA, abstractB, by
    intro h
    have hv : Value.int 0 = Value.int 1 := AuthorityInput.abstract.inj h
    have hi : (0 : Int) = 1 := Value.int.inj hv
    omega, rfl⟩

def constantAuthorityFold8 : AuthorityFold8 := fun _ _ => 0

theorem constantAuthorityFold8_collision : AuthorityDigest8Collision constantAuthorityFold8 :=
  ⟨abstractA, abstractB, by
    intro h
    have hv : Value.int 0 = Value.int 1 := AuthorityInput.abstract.inj h
    have hi : (0 : Int) = 1 := Value.int.inj hv
    omega, rfl⟩

def constantWide : List Int → List Int := fun _ => List.replicate 8 0

theorem constantWide_width8 : Poseidon2Width8 constantWide := by
  intro xs
  simp [constantWide]

theorem constantWide_collision : WireCommit8Collision constantWide := by
  refine ⟨[0], [1], 0, 0, Or.inl (by decide), ?_⟩
  simp [wireCommitR8, constantWide]

theorem no_free_decode_gap (fold : AuthorityFold) :
    (∃ v w, LimbDecodeCollision fold v w) → AuthorityDigestCollision fold := by
  rintro ⟨v, w, h⟩
  exact limbDecodeCollision_reduces fold h

/-! ### ⚑⚑ TEETH FOR THE PER-INSTANCE RESIDUAL — SATISFIABLE, REFUTABLE, LOAD-BEARING.

The three discriminations `FaithfulBreakGlobal` provably cannot make: it is a disjunction of global
existentials, each of which pigeonhole supplies at deployed parameters, so
`P ∨ FaithfulBreakGlobal …` is `True` (`orFaithfulBreakGlobal_iff_True`) — never
satisfiable-but-unprovable, never load-bearing. The narrowed `FaithfulBreak` makes all three; its own
teeth are in the block after this one. -/

/-- **TOOTH (SATISFIABLE, AT EVERY HASH).** On the diagonal every disjunct of the residual demands an
argument-pair DISEQUALITY that `rfl` refutes, so `¬ S.CommitColl` is inhabited for EVERY choice of
`fold8`/`permW`/`ctx`/`cmb`/`compress`/`compressN`/`RH` — no injective instantiation is picked. -/
theorem noFaithfulCommitColl_diag (fold8 : AuthorityFold8) (permW : List Int → List Int)
    (ctx : RotatedContextProvider) (cmb compress : Int → Int → Int)
    (compressN : List Int → Int) (RH : RecordKernelState → Int)
    (k : RecordKernelState) (t : Turn) :
    ¬ FaithfulCommitColl fold8 permW ctx cmb compress compressN RH k k t :=
  noRecStateCommitColl_diag (CH_faithful8 fold8 permW ctx) RH cmb compress compressN k t

/-- The all-constant wide permutation collapses the whole 184-limb chain to one constant carrier —
the `permW` a lossy deployment would be. -/
theorem wireCommitR8_constantWide (l : List Int) (ir : Int) :
    wireCommitR8 constantWide l ir = List.replicate 8 0 := by
  unfold wireCommitR8
  rw [Dregg2.Circuit.Emit.EffectVmEmitRotationR.chainFrom8_snoc]
  rfl

/-- …hence the faithful leaf itself is constant there: it separates NOTHING. -/
theorem CH_faithful8_constantWide_const (fold8 : AuthorityFold8) (ctx : RotatedContextProvider)
    (c c' : CellId) (v w : Value) :
    CH_faithful8 fold8 constantWide ctx c v = CH_faithful8 fold8 constantWide ctx c' w := by
  simp only [CH_faithful8, rotatedCommit8, wireCommitR8_constantWide]

/-- **TOOTH (REFUTABLE — the residual FIRES).** At the all-constant deployment (constant authority
fold, constant wide permutation, constant outer primitives) two kernels differing at the moved cells
equivocate the faithful leaf, and the residual CATCHES it through its `MovedColl` disjunct. So
`¬ FaithfulCommitColl` is not a tautology — a lossy eight-lane deployment is caught here, not defined
away. -/
theorem faithfulCommitColl_refutable :
    FaithfulCommitColl constantAuthorityFold8 constantWide (fun _ _ => rotatedContextDemo)
      (fun _ _ => (0 : Int)) (fun _ _ => (0 : Int)) (fun _ => (0 : Int)) (fun _ => (0 : Int))
      ({ kS0 with cell := fun _ => Value.int 0 }) ({ kS0 with cell := fun _ => Value.int 1 })
      goodTurnS := by
  refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨?_, ?_⟩))))
  · intro h
    exact absurd (Value.int.inj h) (by decide)
  · exact CH_faithful8_constantWide_const _ _ _ _ _ _

/-- **TOOTH (NOT PROVABLE).** Some instantiation satisfies the residual, so `¬ FaithfulCommitColl` is
not a schema true of every deployment — a genuine per-instance obligation, discharged case by case. -/
theorem noFaithfulCommitColl_not_provable :
    ¬ ∀ (fold8 : AuthorityFold8) (permW : List Int → List Int) (ctx : RotatedContextProvider)
        (cmb compress : Int → Int → Int) (compressN : List Int → Int)
        (RH : RecordKernelState → Int) (k k' : RecordKernelState) (t : Turn),
      ¬ FaithfulCommitColl fold8 permW ctx cmb compress compressN RH k k' t :=
  fun h => h _ _ _ _ _ _ _ _ _ goodTurnS faithfulCommitColl_refutable

/-- **⚑⚑ TOOTH (LOAD-BEARING).** Delete the per-instance side condition from
`recStateCommit_binds_kernel_faithful_of_noColl` and the statement is FALSE — not weaker, FALSE — for
EVERY rest hash, honest or not, with the entire structural envelope (`AccountsWF`,
`FiniteRepresentable`) still in place. At the constant deployment two `AccountsWF`,
`FiniteRepresentable` kernels differing only in `nullifiers` share the faithful root. So `hno` is
carrying the argument. (`FaithfulBreak`'s dual reading: delete nothing from
`recStateCommit_binds_kernel_faithful` and it is still `True`.) -/
theorem recStateCommit_binds_kernel_faithful_unconditional_false (RH : RecordKernelState → Int) :
    ¬ (∀ (fold8 : AuthorityFold8) (permW : List Int → List Int) (ctx : RotatedContextProvider)
        (cmb compress : Int → Int → Int) (compressN : List Int → Int)
        (k k' : RecordKernelState) (t : Turn),
        AccountsWF k → AccountsWF k' → FiniteRepresentable k → FiniteRepresentable k' →
        recStateCommit (CH_faithful8 fold8 permW ctx) RH cmb compress compressN k t =
          recStateCommit (CH_faithful8 fold8 permW ctx) RH cmb compress compressN k' t →
        k = k') := by
  intro hall
  exact Dregg2.Circuit.StateCommitReduce.denote_finInit_ne_finNul
    (hall constantAuthorityFold8 constantWide (fun _ _ => rotatedContextDemo)
      (fun _ _ => 0) (fun _ _ => 0) (fun _ => 0) _ _ goodTurnS
      Dregg2.Circuit.StateCommitReduce.accountsWF_denote_finInit
      Dregg2.Circuit.StateCommitReduce.accountsWF_denote_finNul
      (Dregg2.Circuit.RestFrameFin.finiteRepresentable_of_denote _)
      (Dregg2.Circuit.RestFrameFin.finiteRepresentable_of_denote _)
      rfl)

/-! ### ⚑⚑ TEETH FOR THE NARROWED `FaithfulBreak` — THE THREE THINGS THE OLD SHAPE COULD NOT DO.

`FaithfulBreakGlobal` is PROVABLE at every deployed sponge, so it is neither refutable nor
load-bearing anywhere. The narrowed event is refuted at the honest opening at EVERY deployment
(`noFaithfulBreak_diag`), FIRES at a lossy one (`faithfulBreak_refutable`), and therefore is not a
schema (`noFaithfulBreak_not_provable`). `faithfulBreak_sharper_than_global` puts both facts at ONE
and the same sponge — the acceptance test for the narrowing. -/

/-- The leaf event is refuted at an EQUAL opening, for every `fold8`/`permW`/`ctx`: both disjuncts
demand a disequality that `rfl` refutes.  Nothing about the hash is assumed. -/
theorem noFaithfulLeafBreak_diag (fold8 : AuthorityFold8) (permW : List Int → List Int)
    (ctx : RotatedContextProvider) (c : CellId) (v : Value) :
    ¬ FaithfulLeafBreak fold8 permW ctx c v v := by
  rintro (ha | hw)
  · exact ha.1 rfl
  · rcases hw.1 with h | h <;> exact h rfl

/-- **⚑⚑ TOOTH (SATISFIABLE, AT EVERY DEPLOYMENT).** On the diagonal every one of the seven
disjuncts of `FaithfulBreak` demands an argument-pair DISEQUALITY that `rfl` refutes, so
`¬ FaithfulBreak … k k t` is inhabited for EVERY choice of
`fold8`/`permW`/`ctx`/`cmb`/`compress`/`compressN`/`RH` — no injective instantiation is picked, and
no field-boundedness escape hatch exists. THIS is what the old `FaithfulBreakGlobal` could not do:
`faithfulBreakGlobal_free_of_fieldBounded` proves the negation of this statement for it. -/
theorem noFaithfulBreak_diag (fold8 : AuthorityFold8) (permW : List Int → List Int)
    (ctx : RotatedContextProvider) (cmb compress : Int → Int → Int)
    (compressN : List Int → Int) (RH : RecordKernelState → Int)
    (k : RecordKernelState) (t : Turn) :
    ¬ FaithfulBreak fold8 permW ctx cmb compress compressN RH k k t := by
  rintro (hr | hn | hcn | ⟨c, -, hl⟩ | hm | hl | hl)
  · exact hr.1 ⟨rfl, rfl⟩
  · exact hn.1 ⟨rfl, rfl⟩
  · exact hcn.1 rfl
  · exact noFaithfulLeafBreak_diag fold8 permW ctx c (k.cell c) hl
  · exact hm.1 ⟨rfl, rfl⟩
  · exact noFaithfulLeafBreak_diag fold8 permW ctx t.src (k.cell t.src) hl
  · exact noFaithfulLeafBreak_diag fold8 permW ctx t.dst (k.cell t.dst) hl

/-- A context provider whose iroot READS the opening — the deployed shape (each cell/turn carries its
own inbound root), used so the wide-chain leg has a genuinely distinct named pair to fire on. -/
private def rotatedContextDemoIroot : RotatedContextProvider := fun _ v =>
  { residual := fun i => 300 + i.1
    iroot := match v with | .int n => n | _ => 0 }

/-- **TOOTH (REFUTABLE, LEAF LAYER).** At the all-constant wide permutation the 184-limb chain
collapses (`wireCommitR8_constantWide`), so two openings with DIFFERENT inbound roots produce the
SAME eight-lane carrier: the named wide-chain collision genuinely fires. -/
theorem faithfulLeafBreak_refutable (c : CellId) :
    FaithfulLeafBreak constantAuthorityFold8 constantWide rotatedContextDemoIroot c
      (Value.int 0) (Value.int 1) := by
  refine Or.inr ⟨Or.inr ?_, ?_⟩
  · intro h
    simp [rotatedContextDemoIroot] at h
  · simp only [wireCommitR8_constantWide]

/-- **⚑ TOOTH (REFUTABLE — the narrowed break FIRES).** At a lossy deployment two kernels differing
at the moved cells equivocate the faithful leaf, and `FaithfulBreak` CATCHES it through its `src`
leaf disjunct. So `¬ FaithfulBreak` is not a tautology: a lossy eight-lane deployment is caught here,
not defined away. -/
theorem faithfulBreak_refutable :
    FaithfulBreak constantAuthorityFold8 constantWide rotatedContextDemoIroot
      (fun _ _ => (0 : Int)) (fun _ _ => (0 : Int)) (fun _ => (0 : Int)) (fun _ => (0 : Int))
      ({ kS0 with cell := fun _ => Value.int 0 }) ({ kS0 with cell := fun _ => Value.int 1 })
      goodTurnS :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (faithfulLeafBreak_refutable goodTurnS.src))))))

/-- **TOOTH (NOT PROVABLE).** Some instantiation satisfies the narrowed break, so `¬ FaithfulBreak`
is not a schema true of every deployment — a genuine per-instance obligation. -/
theorem noFaithfulBreak_not_provable :
    ¬ ∀ (fold8 : AuthorityFold8) (permW : List Int → List Int) (ctx : RotatedContextProvider)
        (cmb compress : Int → Int → Int) (compressN : List Int → Int)
        (RH : RecordKernelState → Int) (k k' : RecordKernelState) (t : Turn),
      ¬ FaithfulBreak fold8 permW ctx cmb compress compressN RH k k' t :=
  fun h => h _ _ _ _ _ _ _ _ _ goodTurnS faithfulBreak_refutable

/-- **⚑⚑ THE ACCEPTANCE TEST FOR THE NARROWING.** At ONE AND THE SAME deployed-shaped sponge: the
retired `FaithfulBreakGlobal` HOLDS (so `P ∨ FaithfulBreakGlobal …` says nothing about `P`), while
the narrowed `FaithfulBreak` is REFUTED at the honest opening (so `P ∨ FaithfulBreak … k k t` forces
`P`). The replacement survives where the retired shape provably does not. -/
theorem faithfulBreak_sharper_than_global (fold8 : AuthorityFold8) (permW : List Int → List Int)
    (ctx : RotatedContextProvider) (cmb compress : Int → Int → Int) (compressN : List Int → Int)
    (RH : RecordKernelState → Int) (hb : FieldBounded compressN)
    (k : RecordKernelState) (t : Turn) :
    FaithfulBreakGlobal fold8 permW cmb compress compressN
      ∧ ¬ FaithfulBreak fold8 permW ctx cmb compress compressN RH k k t :=
  ⟨faithfulBreakGlobal_free_of_fieldBounded fold8 permW cmb compress compressN hb,
    noFaithfulBreak_diag fold8 permW ctx cmb compress compressN RH k t⟩

/-! ### ⚑ TOOTH (LOAD-BEARING) FOR THE NONCE TWIN.

`recStateCommit_binds_kernel_faithful_unconditional_false` above is NOT this tooth: its two witness
kernels differ only in `nullifiers`, so their agent nonces AGREE and it says nothing about the nonce
conclusion.  A nonce canary needs a pair differing in a CELL, i.e. a `FinKernelState` with a
non-empty `CanonMap` — which the tree did not have until here. -/

section NonceCanary

open Dregg2.Circuit.FinKernelState (FinKernelState finInit denote denote_finInit CanonMap SortedMap
  lookupList)

/-- A one-cell finite kernel whose cell `0` carries `nonce = 1`.  `accounts = {0}` is what makes it
`AccountsWF`; being a `denote` image is what makes it `FiniteRepresentable`.  Both structural side
conditions of the nonce binding therefore hold of it, so the canary below refutes the residual-free
statement WITH the envelope in place, not by dodging it. -/
private def finNonce : FinKernelState :=
  { finInit with
    accounts := {0}
    cell := ⟨⟨[(0, Value.record [("nonce", Value.int 1)])], by simp⟩, by
      intro p hp
      simp only [List.mem_singleton] at hp
      subst hp
      exact fun h => Value.noConfusion h⟩ }

private theorem accountsWF_denote_finNonce : AccountsWF (denote finNonce) := by
  intro c hc
  have hc0 : (0 : CellId) ≠ c := by
    intro h
    exact hc (by simp [finNonce, denote, ← h])
  simp [denote, finNonce, CanonMap.get, SortedMap.get, SortedMap.lookup, lookupList, hc0]
  rfl

private theorem nonceOf_denote_finNonce : nonceOf ((denote finNonce).cell 0) = 1 := by
  simp [denote, finNonce, CanonMap.get, SortedMap.get, SortedMap.lookup, lookupList, nonceOf,
    nonceField, Value.scalar, Value.field]

private theorem nonceOf_denote_finInit : nonceOf ((denote finInit).cell 0) = 0 := by
  rw [denote_finInit]
  simp [nonceOf, Value.scalar, Value.field]

/-- **⚑⚑ TOOTH (LOAD-BEARING).** Delete the per-instance side condition from
`FaithfulCommitSurface.commit_binds_nonce_of_noColl` and the statement is FALSE — not weaker, FALSE —
for EVERY rest hash, honest or not, with the entire structural envelope (`AccountsWF`,
`FiniteRepresentable`) still in place.  At the all-constant deployment two such kernels whose agent-`0`
nonces are `0` and `1` share the faithful root.  So `hno` carries the argument at the nonce layer too,
and the nonce twin is not a relabeling of the whole-kernel one. -/
theorem commit_binds_nonce_faithful_unconditional_false (RH : RecordKernelState → Int) :
    ¬ (∀ (fold8 : AuthorityFold8) (permW : List Int → List Int) (ctx : RotatedContextProvider)
        (cmb compress : Int → Int → Int) (compressN : List Int → Int)
        (k k' : RecordKernelState) (t : Turn) (agent : CellId),
        AccountsWF k → AccountsWF k' → FiniteRepresentable k → FiniteRepresentable k' →
        recStateCommit (CH_faithful8 fold8 permW ctx) RH cmb compress compressN k t =
          recStateCommit (CH_faithful8 fold8 permW ctx) RH cmb compress compressN k' t →
        nonceOf (k.cell agent) = nonceOf (k'.cell agent)) := by
  intro hall
  have h := hall constantAuthorityFold8 constantWide (fun _ _ => rotatedContextDemo)
    (fun _ _ => 0) (fun _ _ => 0) (fun _ => 0) _ _ goodTurnS 0
    Dregg2.Circuit.StateCommitReduce.accountsWF_denote_finInit
    accountsWF_denote_finNonce
    (Dregg2.Circuit.RestFrameFin.finiteRepresentable_of_denote _)
    (Dregg2.Circuit.RestFrameFin.finiteRepresentable_of_denote _)
    rfl
  rw [nonceOf_denote_finInit, nonceOf_denote_finNonce] at h
  exact absurd h (by decide)

end NonceCanary

/-! ### ⚑ TEETH FOR THE TRANSFER RESIDUAL (`TransferFaithfulColl`). -/

/-- **TOOTH (SATISFIABLE, AT EVERY DEPLOYMENT).** An HONEST post-state — one whose cell map really is
the spec's debit/credit of the pre leaves — never trips the transfer residual, for EVERY
`fold8`/`permW`/`ctx`/`compress`/`compressN`. So `¬ TransferFaithfulColl` is the ordinary case, not a
claim that some hash is injective. (The honest opening is the transfer analogue of the diagonal: the
moved leg compares `k'.cell` against `recTransfer k.cell …`, which agree exactly when the witness is
honest.) -/
theorem noTransferFaithfulColl_of_spec (fold8 : AuthorityFold8) (permW : List Int → List Int)
    (ctx : RotatedContextProvider) (compress : Int → Int → Int) (compressN : List Int → Int)
    (k k' : RecordKernelState) (t : Turn)
    (hcell : k'.cell = recTransfer k.cell t.src t.dst t.amt) :
    ¬ TransferFaithfulColl fold8 permW ctx compress compressN k k' t := by
  have hframe : ∀ c ∈ frameCarrier k t, k.cell c = k'.cell c := by
    intro c hc
    have hmem := Finset.mem_sdiff.mp hc
    have h1 : c ≠ t.src := fun h => hmem.2 (by simp [h])
    have h2 : c ≠ t.dst := fun h => hmem.2 (by simp [h])
    rw [hcell]
    simp only [recTransfer, if_neg h1, if_neg h2]
  rintro (hf | hm)
  · rcases hf with ⟨hne, -⟩ | ⟨c, hc, hl⟩
    · refine hne ?_
      show frameLeaves (CH_faithful8 fold8 permW ctx) k (frameCarrier k t) =
        frameLeaves (CH_faithful8 fold8 permW ctx) k' (frameCarrier k t)
      unfold frameLeaves
      refine List.map_congr_left ?_
      intro c hcs
      rw [hframe c ((Finset.mem_sort (· ≤ ·)).mp hcs)]
    · exact hl.1 (hframe c hc)
  · rcases hm with hn | hl | hl
    · exact hn.1 ⟨by rw [hcell], by rw [hcell]⟩
    · exact hl.1 (by rw [hcell])
    · exact hl.1 (by rw [hcell])

/-- **⚑ TOOTH (REFUTABLE — the transfer residual FIRES).** At the all-constant wide permutation the
faithful leaf separates nothing, so `StateCommit`'s own MINTED-BYSTANDER forgery (`forgedThirdCell`:
cells 0/1 honestly debited/credited, cell 2 minted 50 → 999) equivocates the frame sponge's leaf at
cell 2 — and the residual catches it through `FrameLeafColl`.  This is the exact forgery the injective
toy portal rejects and a lossy deployment would not; `¬ TransferFaithfulColl` is a real commitment. -/
theorem transferFaithfulColl_refutable :
    TransferFaithfulColl constantAuthorityFold8 constantWide rotatedContextDemoIroot
      (fun _ _ => (0 : Int)) (fun _ => (0 : Int)) kS0 forgedThirdCell goodTurnS := by
  refine Or.inl (Or.inr ⟨2, by decide, ?_, ?_⟩)
  · intro h
    simp [kS0, forgedThirdCell] at h
  · exact CH_faithful8_constantWide_const _ _ _ _ _ _

/-- **TOOTH (NOT PROVABLE).** Hence `¬ TransferFaithfulColl` is not a schema true of every
deployment. -/
theorem noTransferFaithfulColl_not_provable :
    ¬ ∀ (fold8 : AuthorityFold8) (permW : List Int → List Int) (ctx : RotatedContextProvider)
        (compress : Int → Int → Int) (compressN : List Int → Int)
        (k k' : RecordKernelState) (t : Turn),
      ¬ TransferFaithfulColl fold8 permW ctx compress compressN k k' t :=
  fun h => h _ _ _ _ _ _ _ goodTurnS transferFaithfulColl_refutable

/-! ### ⚑⚑ TOOTH (LOAD-BEARING) FOR THE TRANSFER TWIN — the canary the header said was impossible.

`transfer_circuit_full_sound_faithful_of_noColl` was the one ported statement with no
`*_unconditional_false` sibling, and the reason recorded in this file's header was FALSE: the witness
needs an inhabitant of `RestHashIffFrameFin`, and
`Verify.RestFrameFiniteSupportSuccessor.restHashIffFrameFin_satisfiable` is exactly that — a CLOSED
theorem naming `RH_fin Reference.refSponge`, carrying nothing.

What the witness genuinely needed beyond it was a satisfying `satisfiedS` assignment at a state pair
BOTH halves of which are `FiniteRepresentable`.  That is supplied by exhibiting `StateCommit`'s own
reference forgery — `kS0` (cells 0/1/2 at 100/5/50) and `forgedThirdCell` (0/1 honestly debited and
credited to 70/35, bystander cell 2 MINTED 50 → 999) — as `denote` images of two `FinKernelState`s.
The forgery is then run at the LOSSY deployment: `transferCircuit` accepts it (`StateCommit`'s own
`#guard` records that), the frame/moved gates collapse under the constant primitives, and the
rest-frame gate holds because the eighteen non-cell components are literally frozen.  So `satisfiedS`
holds and `TransferSpec` does not.

⚑ `transferFaithfulColl_refutable` above FIRES the residual at THIS SAME TRIPLE.  The two teeth are
the same instance read twice: without `hno` the conclusion is FALSE, and `hno` is precisely what this
witness violates — `transfer_canary_and_residual_at_one_instance` says that as a theorem, not as
prose, so a later edit that moves either side stops elaborating.

⚑ **THE REST HASH IS NOT WHERE THE CHEAT IS, and that is the point.**  `RH_fin Reference.refSponge`
is `Encodable.encode`, genuinely injective and genuinely NOT BabyBear-bounded — the strongest rest
hash the tree has.  The rest-frame gate therefore genuinely BITES here: it forces all eighteen
non-cell components frozen, and the forgery has to (and does) respect every one of them.  All the
lossiness is on the CELL side — `constantWide` collapses `wireCommitR8`, so `CH_faithful8` separates
no two openings.  A canary that had instead picked a weak `RH` would be refuting the statement by
disabling the hypothesis it is supposed to keep. -/

section TransferCanary

open Dregg2.Circuit.FinKernelState (FinKernelState finInit denote CanonMap SortedMap lookupList)
open Dregg2.Circuit.FinFrameHash (RH_fin)
open Dregg2.Circuit.Poseidon2Binding.Reference (refSponge)
open Dregg2.Verify.RestFrameFiniteSupportSuccessor (restHashIffFrameFin_satisfiable)

/-- A one-field balance record — the exact `Value` shape `kS0`/`forgedThirdCell` store. -/
private def balV (b : Int) : Value := Value.record [("balance", Value.int b)]

/-- **`kS0` AS A `FinKernelState`.**  Three stored cells, sorted keys, no stored default — so it is a
`CanonMap`, and `denote` of it is `kS0` on the nose. -/
private def finKS0 : FinKernelState :=
  { finInit with
    accounts := {0, 1, 2}
    cell := ⟨⟨[(0, balV 100), (1, balV 5), (2, balV 50)], by decide⟩, by
      intro p hp
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl <;> exact fun h => Value.noConfusion h⟩ }

/-- **`forgedThirdCell` AS A `FinKernelState`** — the same three keys, cell 2 minted to 999. -/
private def finForgedThirdCell : FinKernelState :=
  { finKS0 with
    cell := ⟨⟨[(0, balV 70), (1, balV 35), (2, balV 999)], by decide⟩, by
      intro p hp
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl <;> exact fun h => Value.noConfusion h⟩ }

theorem denote_finKS0 : denote finKS0 = kS0 := by
  have hcell : ∀ c, (denote finKS0).cell c = kS0.cell c := by
    intro c
    by_cases h0 : c = 0
    · subst h0; rfl
    · by_cases h1 : c = 1
      · subst h1; rfl
      · by_cases h2 : c = 2
        · subst h2; rfl
        · simp [denote, finKS0, kS0, CanonMap.get, SortedMap.get, SortedMap.lookup,
            lookupList, h0, h1, h2, Ne.symm h0, Ne.symm h1, Ne.symm h2]
          rfl
  ext1 <;> first | rfl | (funext c; exact hcell c)

theorem denote_finForgedThirdCell : denote finForgedThirdCell = forgedThirdCell := by
  have hcell : ∀ c, (denote finForgedThirdCell).cell c = forgedThirdCell.cell c := by
    intro c
    by_cases h0 : c = 0
    · subst h0; rfl
    · by_cases h1 : c = 1
      · subst h1; rfl
      · by_cases h2 : c = 2
        · subst h2; rfl
        · simp [denote, finForgedThirdCell, finKS0, forgedThirdCell, kS0, CanonMap.get,
            SortedMap.get, SortedMap.lookup, lookupList, h0, h1, h2,
            Ne.symm h0, Ne.symm h1, Ne.symm h2]
          rfl
  ext1 <;> first | rfl | (funext c; exact hcell c)

/-- The forgery is inside the narrowed domain: both halves are `denote` images, so the
`FiniteRepresentable` envelope of the transfer twin is met, not dodged. -/
theorem finiteRepresentable_kS0 : FiniteRepresentable kS0 := ⟨finKS0, denote_finKS0⟩

theorem finiteRepresentable_forgedThirdCell : FiniteRepresentable forgedThirdCell :=
  ⟨finForgedThirdCell, denote_finForgedThirdCell⟩

theorem accountsWF_kS0 : AccountsWF kS0 := by
  intro c hc
  have h0 : c ≠ 0 := by rintro rfl; exact hc (by simp [kS0])
  have h1 : c ≠ 1 := by rintro rfl; exact hc (by simp [kS0])
  have h2 : c ≠ 2 := by rintro rfl; exact hc (by simp [kS0])
  simp [kS0, h0, h1, h2]

theorem accountsWF_forgedThirdCell : AccountsWF forgedThirdCell := by
  intro c hc
  have h0 : c ≠ 0 := by rintro rfl; exact hc (by simp [forgedThirdCell, kS0])
  have h1 : c ≠ 1 := by rintro rfl; exact hc (by simp [forgedThirdCell, kS0])
  have h2 : c ≠ 2 := by rintro rfl; exact hc (by simp [forgedThirdCell, kS0])
  simp [forgedThirdCell, kS0, h0, h1, h2]

/-- The rest-frame gate at the named inhabitant: the forgery freezes all eighteen non-cell
components, so `restHashIffFrameFin_satisfiable`'s REVERSE direction hands back the equal rest
hashes.  (The FORWARD direction is what makes the predicate content-bearing; this canary needs the
other one, which is why an inhabitant — not merely satisfiability-in-the-abstract — was required.) -/
private theorem restEq_forged :
    RH_fin refSponge kS0 = RH_fin refSponge forgedThirdCell :=
  (restHashIffFrameFin_satisfiable kS0 forgedThirdCell
      finiteRepresentable_kS0 finiteRepresentable_forgedThirdCell).mpr
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- The nine projection gates ACCEPT the minted-bystander forgery — `StateCommit`'s own `#guard`
(`satisfied transferCircuit (encodeT kS0 goodTurnS forgedThirdCell)`) as a `Prop`, since the transfer
twin's `satisfiedS` needs it as a term and not as a `#guard`. -/
private theorem htsat_forged :
    satisfied transferCircuit (encodeT kS0 goodTurnS forgedThirdCell) := by decide

/-- The conclusion the canary refutes: `forgedThirdCell` is NOT the spec post-state — its cell 2 holds
999 where the spec's debit/credit of `kS0` leaves 50. -/
theorem transferSpec_forgedThirdCell_false : ¬ TransferSpec kS0 goodTurnS forgedThirdCell := by
  rintro ⟨-, hcell, -⟩
  have h2 : balOf (forgedThirdCell.cell 2)
      = balOf (recTransfer kS0.cell goodTurnS.src goodTurnS.dst goodTurnS.amt 2) :=
    congrArg balOf (congrFun hcell 2)
  revert h2
  decide

/-- **THE SATISFYING ASSIGNMENT.**  At the lossy deployment the forgery satisfies the WHOLE
`stateCircuit` plus the root decomposition: nine transfer gates transported from `htsat_forged`,
`cSRestFrame` from `restEq_forged`, and `cSFrameReuse`/`cSMovedBind` because the constant
`compressN`/`compress` collapse both sides.  This is the assignment the header claimed the tree could
not build. -/
theorem satisfiedS_forgedThirdCell_at_lossy :
    satisfiedS (fun _ _ => (0 : Int)) (fun _ _ => (0 : Int))
      (encodeS (CH_faithful8 constantAuthorityFold8 constantWide rotatedContextDemoIroot)
        (RH_fin refSponge) (fun _ _ => (0 : Int)) (fun _ _ => (0 : Int))
        (fun _ => (0 : Int)) kS0 goodTurnS forgedThirdCell) := by
  have e0 := encodeS_agrees_encodeT
    (CH_faithful8 constantAuthorityFold8 constantWide rotatedContextDemoIroot)
    (RH_fin refSponge) (fun _ _ => (0 : Int)) (fun _ _ => (0 : Int)) (fun _ => (0 : Int))
    kS0 goodTurnS forgedThirdCell
  refine ⟨?_, ?_, ?_⟩
  · intro c hc
    unfold stateCircuit at hc
    rw [List.mem_append] at hc
    rcases hc with hc | hc
    · have hcT := htsat_forged c hc
      unfold transferCircuit at hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        · unfold Constraint.holds at hcT ⊢
          simp only [cTAuth, cTNonneg, cTAvail, cTDistinct, cTSrcLive, cTDstLive, cTDebit,
            cTCredit, cTConserve, Expr.eval,
            e0 vSrcPre (by decide), e0 vDstPre (by decide), e0 vSrcPost (by decide),
            e0 vDstPost (by decide), e0 vAmt (by decide), e0 vTAuth (by decide),
            e0 vTNonneg (by decide), e0 vTAvail (by decide), e0 vTDistinct (by decide),
            e0 vTSrcLive (by decide), e0 vTDstLive (by decide)] at hcT ⊢
          exact hcT
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact (srestframe_iff _ _ _ _ _ _ _ _).mpr restEq_forged
      · exact (sframereuse_iff _ _ _ _ _ _ _ _).mpr rfl
      · exact (smovedbind_iff _ _ _ _ _ _ _ _).mpr rfl
  · simp only [encS_vPreRoot]
    rfl
  · simp only [encS_vPostRoot]
    rfl

/-- **⚑⚑ TOOTH (LOAD-BEARING).** Delete the per-instance side condition from
`transfer_circuit_full_sound_faithful_of_noColl` and the statement is FALSE — not weaker, FALSE — with
EVERYTHING ELSE still in place: the `RestHashIffFrameFin RH` carrier stays INSIDE the quantifier
(dropping it would refute a stronger statement and say nothing about the real one), and so do
`AccountsWF` and `FiniteRepresentable` on both states.  At the lossy eight-lane deployment
`StateCommit`'s minted-bystander forgery satisfies the whole full-state circuit while failing
`TransferSpec`.  So `hno` is carrying the argument at the transfer layer, and
`transferFaithfulColl_refutable` names — at this very triple — the collision it demands. -/
theorem transfer_circuit_full_sound_faithful_unconditional_false :
    ¬ (∀ (fold8 : AuthorityFold8) (permW : List Int → List Int) (ctx : RotatedContextProvider)
        (cmb compress : Int → Int → Int) (compressN : List Int → Int)
        (RH : RecordKernelState → Int),
        RestHashIffFrameFin RH →
        ∀ (k : RecordKernelState) (t : Turn) (k' : RecordKernelState),
        AccountsWF k → AccountsWF k' → FiniteRepresentable k → FiniteRepresentable k' →
        satisfiedS cmb compress
          (encodeS (CH_faithful8 fold8 permW ctx) RH cmb compress compressN k t k') →
        TransferSpec k t k') := by
  intro hall
  exact transferSpec_forgedThirdCell_false
    (hall constantAuthorityFold8 constantWide rotatedContextDemoIroot
      (fun _ _ => 0) (fun _ _ => 0) (fun _ => 0) (RH_fin refSponge)
      restHashIffFrameFin_satisfiable kS0 goodTurnS forgedThirdCell
      accountsWF_kS0 accountsWF_forgedThirdCell
      finiteRepresentable_kS0 finiteRepresentable_forgedThirdCell
      satisfiedS_forgedThirdCell_at_lossy)

/-- **⚑⚑ THE ACCEPTANCE TEST FOR THE CANARY.**  Prose that two teeth are "at the same instance" rots;
this does not.  At ONE deployment (`constantAuthorityFold8` / `constantWide` /
`rotatedContextDemoIroot`, all-zero outer primitives) and ONE triple (`kS0` / `goodTurnS` /
`forgedThirdCell`): the witness SATISFIES the full-state circuit, FAILS `TransferSpec`, and TRIPS
`TransferFaithfulColl`.  So the statement refuted above differs from
`transfer_circuit_full_sound_faithful_of_noColl` by `hno` ALONE, and `hno` is false exactly where the
conclusion is.  If a later edit moves either tooth to a different instance, this stops elaborating. -/
theorem transfer_canary_and_residual_at_one_instance :
    satisfiedS (fun _ _ => (0 : Int)) (fun _ _ => (0 : Int))
        (encodeS (CH_faithful8 constantAuthorityFold8 constantWide rotatedContextDemoIroot)
          (RH_fin refSponge) (fun _ _ => (0 : Int)) (fun _ _ => (0 : Int)) (fun _ => (0 : Int))
          kS0 goodTurnS forgedThirdCell)
      ∧ ¬ TransferSpec kS0 goodTurnS forgedThirdCell
      ∧ TransferFaithfulColl constantAuthorityFold8 constantWide rotatedContextDemoIroot
          (fun _ _ => (0 : Int)) (fun _ => (0 : Int)) kS0 forgedThirdCell goodTurnS :=
  ⟨satisfiedS_forgedThirdCell_at_lossy, transferSpec_forgedThirdCell_false,
    transferFaithfulColl_refutable⟩

end TransferCanary

#assert_axioms plus4_collision
#assert_axioms constantAuthorityFold_collision
#assert_axioms constantAuthorityFold8_collision
#assert_axioms constantWide_width8
#assert_axioms constantWide_collision
#assert_axioms no_free_decode_gap
-- teeth for the per-instance residual: SATISFIABLE / REFUTABLE / NOT PROVABLE / LOAD-BEARING.
#assert_axioms noFaithfulCommitColl_diag
#assert_axioms wireCommitR8_constantWide
#assert_axioms CH_faithful8_constantWide_const
#assert_axioms faithfulCommitColl_refutable
#assert_axioms noFaithfulCommitColl_not_provable
#assert_axioms recStateCommit_binds_kernel_faithful_unconditional_false
-- teeth for the NARROWED `FaithfulBreak` and for the transfer residual (2026-08-01).
#assert_axioms noFaithfulLeafBreak_diag
#assert_axioms noFaithfulBreak_diag
#assert_axioms faithfulLeafBreak_refutable
#assert_axioms faithfulBreak_refutable
#assert_axioms noFaithfulBreak_not_provable
#assert_axioms faithfulBreak_sharper_than_global
#assert_axioms noTransferFaithfulColl_of_spec
#assert_axioms transferFaithfulColl_refutable
#assert_axioms noTransferFaithfulColl_not_provable
#assert_axioms commit_binds_nonce_faithful_unconditional_false
-- ⚑⚑ the LOAD-BEARING canary for the transfer twin (2026-08-01, third pass): the header's
-- "no inhabitant of `RestHashIffFrameFin`" blocker was false, and this is the discharge.
#assert_axioms denote_finKS0
#assert_axioms denote_finForgedThirdCell
#assert_axioms finiteRepresentable_kS0
#assert_axioms finiteRepresentable_forgedThirdCell
#assert_axioms accountsWF_kS0
#assert_axioms accountsWF_forgedThirdCell
#assert_axioms transferSpec_forgedThirdCell_false
#assert_axioms satisfiedS_forgedThirdCell_at_lossy
#assert_axioms transfer_circuit_full_sound_faithful_unconditional_false
#assert_axioms transfer_canary_and_residual_at_one_instance

/-! ## 5. The honest floor.

`AuthorityDigestCollision fold` and the three Poseidon collision disjuncts are *findable-collision*
events, not impossibility premises.  The legacy scalar fold is only lane zero and is concretely weak;
the deployed rotated path must use the eight-lane authority group and `wireCommitR8`.

⚑ **THE ROUTING PIN THAT POINTED AT A REFUTED FLOOR IS DELETED (2026-07-28).** This section carried
`abbrev CollisionResistant := HashFloorHonesty.CollisionResistant`, a re-export naming that def "the
proper advantage carrier". That def is now DELETED — it was `HashCRHardQuant F ⊤` under a name that
hid the `⊤`, and `FloorGames.hashCRHardQuant_top_false_of_compressing` refutes it for every
compressing family, i.e. for the eight-lane authority digest this file is about. The alias had NO
Lean consumer anywhere in the tree; it existed to point a reader somewhere, and where it pointed was
wrong. The honest carrier for adaptive/birthday collision finding is
`Crypto.FloorGames.HashCRHardQuant F Eff` with `Eff` named, or better
`Crypto.RomQueryFloor.birthday_bound`, which is PROVED and carries no assumption at all. -/

abbrev CollisionFinder := Dregg2.Circuit.HashFloorHonesty.CollisionFinder
noncomputable abbrev collisionAdv := Dregg2.Circuit.HashFloorHonesty.collisionAdv

/-- What the existing `OodRomBound.RomUniform` floor honestly supplies for hashing: a fresh uniform
squeeze hits any fixed target with probability exactly `1 / |F|`.  This is the fixed-target leg used
inside collision reductions; adaptive/birthday collision finding belongs to the query-counted
`Crypto.RomQueryFloor.birthday_bound`, not to a false injectivity statement and not to the refuted
unrestricted-class collision floor. -/
theorem romUniform_fixed_target_hit {Ω F : Type*} [Fintype Ω] [Fintype F] [DecidableEq F]
    (draw : Ω → F) (hrom : Dregg2.Circuit.OodRomBound.RomUniform draw) (target : F) :
    winProb (fun ω => decide (draw ω = target)) = 1 / (Fintype.card F : ℝ) := by
  rw [hrom (fun x => decide (x = target))]
  unfold winProb
  have hfilter : Finset.univ.filter (fun x : F => decide (x = target) = true) = {target} := by
    ext x
    simp
  rw [hfilter, Finset.card_singleton]
  norm_num

#assert_axioms romUniform_fixed_target_hit

end Dregg2.Circuit.CommitFaithfulRegrounded
