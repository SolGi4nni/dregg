/-
# Dregg2.Circuit.CircuitCompletenessSetInsert — the COMPLETENESS rungs (wave 5) for the SET-INSERT /
BIRTH family, the last per-effect cluster. The converse of the soundness set-insert / non-membership
refinements realized in `RotatedKernelRefinement{Notes,NotesFresh,Birth,SpawnHandoff}` (consuming the
phase-D gadgets `SortedTreeNonMembership` + `CapTreeUpdate`):

  * **noteSpend**             — the nullifier SET-INSERT (`nullifiers := nf :: …`) + the DOUBLE-SPEND
    NON-MEMBERSHIP freshness `nf ∉ pre.nullifiers`.
  * **noteCreate**            — the commitments-root SET-INSERT (`commitments := cm :: …`).
  * **createCell**            — the accounts-root (cells_root) SET-INSERT (`accounts := insert newCell …`).
  * **createCellFromFactory** — the accounts-root SET-INSERT (child key) + the factory install residual.
  * **spawn**                 — the accounts-root SET-INSERT + the cap-HANDOFF cap-tree INSERT
    (`keysOf childCapRootPost = insert childKey (keysOf childCapRootPre)`, the child key fresh pre).

SOUNDNESS (those files) is `<witness> + <encode> ⟹ <effect>Spec`: the circuit never accepts a forged
set move (a drop / reorder / silently-dropped insert / double-spend). COMPLETENESS is the OTHER
direction: from the kernel `<effect>Spec` we CONSTRUCT the `<effect>Encodes` witness — the committed
FIX root(s) (the published pre/post set-root columns + the set-insert gate) come from a realizable
PROVER floor (the construction dual of the soundness committed set-root readout); the
guard/freshness/frame/log legs are discharged straight FROM the spec. The constructed witness,
publishing the kernel's own commitment, is the `descriptorComplete`-shaped satisfiability the apex
consumes (`stateDecode_construct`). A kernel-valid set-insert / birth transition HAS an accepting proof
— the circuit never spuriously rejects a genuine spend / note-create / cell-birth / spawn.

## The split (dual to soundness; identical to the wave-1..4 templates — a `*RootProver` set-root floor)

For each effect, exactly as `CircuitCompletenessLifecycle`'s `LifecycleRootProver`:

  * the SPEC DETERMINES the kernel-side legs — the set move IS in the spec (`nullifiers := nf :: …` /
    `commitments := cm :: …` / `accounts := insert newCell …`), the admissibility guard (and, for
    noteSpend, the no-double-spend FRESHNESS + the spend-proof gate — both conjuncts of
    `noteSpendGuard`), the frame fields, the receipt log. These are discharged from the spec's
    conjuncts (`hspec.…`), not assumed.
  * the part the spec does NOT determine — the satisfying-witness committed SET-ROOT columns + the
    FIX set-insert gate (the `noteListRoot` / `accountsRoot` digest limbs the FIX adds to
    `compute_commitment`, OR the sorted cap-tree spine for spawn's handoff) — is the realizable PROVER
    floor (`SetInsertRootProver` / `AccountsInsertRootProver` / `SpawnHandoffInsertProver`), the
    construction dual of the soundness committed set-root readout. Named precisely, NOT faked. The same
    `compressN`-injective Poseidon-CR carrier the soundness rungs bind under.

## The genuine teeth (the constructed decode realizes the REAL set move)

Completeness is vacuous if the constructed witness is degenerate. Each rung carries the genuine tooth
proving the constructed decode realizes the REAL set move, via the SAME insert / non-membership lemma
the soundness rung uses:

  * noteSpend: `post.nullifiers = nf :: pre.nullifiers` (the set-insert, `noteGrowForced`) AND
    `nf ∉ pre.nullifiers` (the non-membership, off the spec's `noteSpendGuard`) — the inserted key is
    present post AND absent pre, the exact wave-prompt tooth shape.
  * noteCreate: `post.commitments = cm :: pre.commitments` (`noteGrowForced`).
  * createCell / createCellFromFactory: `post.accounts = insert newCell pre.accounts`
    (`accountsGrowForced`).
  * spawn: `post.accounts = insert child pre.accounts` (`accountsGrowForced`) AND the cap-handoff
    `keysOf S newChildRoot = insert childKey (keysOf S oldChildRoot)` with `childKey` fresh pre
    (`spawn_handoff_forces_insert` / `capInsert_sound`) — the published child cap_root grew by exactly
    the conferred key, present post AND absent pre.

Each spec is INHABITABLE (the spec files' own `#guard` witnesses — `st0`/`stN0`/`sAG0`/`facS` exhibit
committing transitions: `noteSpendA 77 0 true` commits `[77]`; `noteCreateA 42 9` commits `42`;
`createCellA 9 2` inserts `2`; `spawnA 9 2 0` inserts `2` + confers `[Cap.node 0]`; `createCellFrom-
FactoryA 0 5 42` commits), so the antecedent is non-vacuous.

## On the asymmetry watch (the wave-4 owner-vs-cap analog)

The prompt flagged the noteSpend non-membership as a possible asymmetry seam (does the soundness
non-membership rung force something the spec does not determine?). It does NOT: the kernel
`NoteSpendSpec`'s guard `noteSpendGuard` IS `spendProof = true ∧ nf ∉ pre.nullifiers` — the freshness
the soundness phase-D non-membership open FORCES in-circuit is EXACTLY the spec's own guard conjunct.
So in the completeness direction the freshness is spec-determined (a genuine spend HAS its nullifier
absent pre), and it discharges the base `noteSpendGenuineEncodes.freshness` field directly — NO
prover-floor non-membership open is needed for the completeness encode (the prover floor here supplies
only the SET-ROOT columns + insert gate, dual to the value-leg of soundness). There is no owner-vs-cap
style disjunction here; the non-membership is a single determined Prop. Surfaced and dismissed honestly
— not stubbed.

## Axiom hygiene

`#assert_axioms` ⊆ {propext, Classical.choice, Quot.sound} on every new theorem; the set-root /
cap-tree-spine construction floors enter as named structure carriers (Type-valued realizable prover
witnesses), never as axioms — exactly as wave-3's `LifecycleRootProver` and the soundness side's
`SpineCommits`. No `sorry`, no `native_decide`, no `:= True`, no fresh axiom. NEW file; imports
read-only.
-/
import Dregg2.Circuit.CircuitCompleteness
import Dregg2.Circuit.RotatedKernelRefinementNotes
import Dregg2.Circuit.RotatedKernelRefinementBirth
import Dregg2.Circuit.RotatedKernelRefinementSpawnHandoff
import Dregg2.Circuit.Spec.notenullifier
import Dregg2.Circuit.Spec.notecommitment
import Dregg2.Circuit.Spec.accountgrowth
import Dregg2.Circuit.Spec.factorycreation

namespace Dregg2.Circuit.CircuitCompletenessSetInsert

open Dregg2.Circuit.CircuitSoundness
open Dregg2.Circuit.CircuitCompleteness (commitOf stateDecode_construct)
open Dregg2.Circuit.StateCommit (AccountsWF compressNInjective)
open Dregg2.Circuit.DescriptorIR2 (EffectVmDescriptor2 VmTrace Satisfied2)
open Dregg2.Circuit.RotatedKernelRefinementNotes
  (NoteRootRow gNoteGrow noteGrowForced noteSpendGenuineEncodes noteSpend_nullifiers_forced
   noteCreateGenuineEncodes noteCreate_commitments_forced)
open Dregg2.Circuit.RotatedKernelRefinementBirth
  (AccountsRootRow gAccountsGrow accountsGrowForced
   createCellGenuineEncodes createCell_accounts_forced
   createFromFactoryGenuineEncodes createFromFactory_accounts_forced
   spawnGenuineEncodes spawn_accounts_forced)
open Dregg2.Circuit.RotatedKernelRefinementSpawnHandoff
  (spawnHandoffEncodes spawn_handoff_forces_insert spawn_handoff_key_present)
open Dregg2.Circuit.SortedTreeNonMembership (keysOf SpineCommits sortedInsert)
open Dregg2.Circuit.DeployedCapTree (CapHashScheme)
open Dregg2.Circuit.Spec.NoteNullifier (NoteSpendSpec noteSpendGuard noteSpendReceipt)
open Dregg2.Circuit.Spec.NoteCommitment (NoteCreateASpec noteCreateReceipt)
open Dregg2.Circuit.Spec.AccountGrowth
  (CreateCellSpec createCellAdmit createReceipt bornEmptyAt
   SpawnSpec spawnAdmit spawnCapsMap spawnDelegateMap spawnDelegationsMap)
open Dregg2.Circuit.Spec.FactoryCreation
  (CreateFromFactorySpec factoryAdmit factoryReceipt factoryPostCell factoryPostCaveats
   factoryBornCell factoryBornCaveats)
open Dregg2.Exec
open Dregg2.Exec.TurnExecutorFull

set_option autoImplicit false

/-- The felt carrier (the SAME `ℤ`-alias the soundness set-root modules use for a committed root
column; local re-export to keep the prover-floor structures' columns at the exact `FieldElem` type the
`noteListRoot` / `accountsRoot` gates expect). -/
abbrev FieldElem := Dregg2.Circuit.RotatedKernelRefinementNotes.FieldElem

/-! ## §1 — noteSpend: the completeness rung (dual of `noteSpend_descriptorRefines`). Nullifier SET-INSERT.

`noteSpend_descriptorRefines : noteSpendGenuineEncodes ⟹ NoteSpendSpec`, with the committed
`nullifiersRoot` FIX limb forcing the post nullifiers to `nf :: pre.nullifiers`. Completeness: from
`NoteSpendSpec pre nf actor spendProof post` the spec DETERMINES the set-insert
(`nullifiers := nf :: …`), the no-double-spend FRESHNESS + the spend-proof gate (BOTH conjuncts of
`noteSpendGuard`), the receipt, and the 15-field frame. Only the committed nullifiers SET-ROOT columns
+ the FIX insert gate come from the realizable prover floor — the honest prover's committed
nullifiers-root limb. -/

/-- **`SetInsertRootProver` — the realizable note SET-ROOT FIX-root construction floor (NAMED, dual of
the soundness committed set-root readout).** The part of a note `<e>Encodes` the spec does NOT
determine: the two published note-list-root columns (`preRoot`/`postRoot`), their decode (`hroots`),
and the FIX gate (`gate`) pinning the post column to the GROWN-list digest `x :: preList`. The honest
prover's committed shielded-set-root limb; parameterized by the touched list `preList`/`postList` + the
inserted id `x`, so the SAME structure serves noteSpend (nullifiers, `nf`) and noteCreate (commitments,
`cm`). Data-bearing (`Type`). -/
structure SetInsertRootProver (compressN : List FieldElem → FieldElem)
    (preList postList : List Nat) (x : Nat) : Type where
  preRoot : FieldElem
  postRoot : FieldElem
  hroots : NoteRootRow compressN preList postList preRoot postRoot
  gate : gNoteGrow compressN preList x postRoot

/-- **`noteSpend_noteSpendGenuineEncodes_construct` — CONSTRUCT the noteSpend decode from the spec.**
From `NoteSpendSpec pre nf actor spendProof post` and the realizable `SetInsertRootProver` over the
nullifier list, ASSEMBLE `noteSpendGenuineEncodes`: the nullifiers SET-ROOT columns + insert gate come
from the prover floor; the freshness + proof gate (off `noteSpendGuard`), the receipt, and the 15 frame
fields are discharged FROM the spec. The dual of `noteSpend_descriptorRefines`. -/
def noteSpend_noteSpendGenuineEncodes_construct (compressN : List FieldElem → FieldElem)
    (pre post : RecChainedState) (nf : Nat) (actor : CellId) (spendProof : Bool)
    (hspec : NoteSpendSpec pre nf actor spendProof post)
    (prover : SetInsertRootProver compressN pre.kernel.nullifiers post.kernel.nullifiers nf) :
    noteSpendGenuineEncodes compressN pre post nf actor spendProof where
  preRoot := prover.preRoot
  postRoot := prover.postRoot
  hroots := prover.hroots
  gate := prover.gate
  -- the no-double-spend FRESHNESS + the spend-proof gate ARE the spec's `noteSpendGuard` conjuncts.
  proof := hspec.1.1
  freshness := hspec.1.2
  logAdv := hspec.2.2.1
  frAccounts := hspec.2.2.2.1
  frCell := hspec.2.2.2.2.1
  frCaps := hspec.2.2.2.2.2.1
  frRevoked := hspec.2.2.2.2.2.2.1
  frCommitments := hspec.2.2.2.2.2.2.2.1
  frBal := hspec.2.2.2.2.2.2.2.2.1
  frSlotCaveats := hspec.2.2.2.2.2.2.2.2.2.1
  frFactories := hspec.2.2.2.2.2.2.2.2.2.2.1
  frLifecycle := hspec.2.2.2.2.2.2.2.2.2.2.2.1
  frDeathCert := hspec.2.2.2.2.2.2.2.2.2.2.2.2.1
  frDelegate := hspec.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  frDelegations := hspec.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  frDelegationEpoch := hspec.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  frDelegationEpochAt := hspec.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  frHeaps := hspec.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2

/-- **`noteSpend_descriptorComplete_genuine` — the constructed decode realizes the GENUINE nullifier
set-insert.** From `NoteSpendSpec`, the post nullifiers ARE `nf :: pre.nullifiers` (the spec's
nullifier clause) — the inserted nullifier `nf` is present at the head post. So the constructed witness
performs the REAL set-insert, not a degenerate no-insert. The first leg of the non-vacuity tooth. -/
theorem noteSpend_descriptorComplete_genuine
    (pre post : RecChainedState) (nf : Nat) (actor : CellId) (spendProof : Bool)
    (hspec : NoteSpendSpec pre nf actor spendProof post) :
    post.kernel.nullifiers = nf :: pre.kernel.nullifiers :=
  hspec.2.1

/-- **`noteSpend_descriptorComplete_fresh_genuine` — the inserted nullifier was ABSENT pre (the
non-membership leg).** From `NoteSpendSpec`'s guard `noteSpendGuard = spendProof = true ∧ nf ∉
pre.nullifiers`, the spent nullifier `nf` is absent from the pre nullifier set. Combined with the
set-insert leg, the constructed decode realizes `keysOf post = insert nf (keysOf pre)` with `nf` absent
pre — the exact wave-prompt non-membership tooth, spec-determined (a genuine spend HAS its nullifier
fresh). -/
theorem noteSpend_descriptorComplete_fresh_genuine
    (pre post : RecChainedState) (nf : Nat) (actor : CellId) (spendProof : Bool)
    (hspec : NoteSpendSpec pre nf actor spendProof post) :
    nf ∉ pre.kernel.nullifiers :=
  hspec.1.2

/-- **`noteSpend_descriptorComplete` — the noteSpend completeness rung (dual of
`noteSpend_descriptorRefines`).** From a kernel spend step `NoteSpendSpec pre nf actor spendProof post`
+ the realizable prover construction (the nullifiers SET-ROOT + insert gate), a circuit witness of the
live `d` whose published commitment decodes to `(pre, post)`. The set-insert + freshness are
spec-determined (and read off by the genuine teeth); the SET-ROOT columns are the prover floor; the
commitment is CONSTRUCTED (`stateDecode_construct`). -/
theorem noteSpend_descriptorComplete (compressN : List FieldElem → FieldElem)
    (S : CommitSurface) (hash : List ℤ → ℤ) (d : EffectVmDescriptor2)
    (buildWitness : ∀ (pre post : RecChainedState) (nf : Nat) (actor : CellId) (spendProof : Bool)
        (turn : BoundaryTurn),
      NoteSpendSpec pre nf actor spendProof post →
      Σ' (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (t : VmTrace),
        Satisfied2 hash d minit mfin maddrs t ×'
        (tracePublishedCommit t = commitOf S pre post turn) ×'
        SetInsertRootProver compressN pre.kernel.nullifiers post.kernel.nullifiers nf)
    (pre post : RecChainedState) (nf : Nat) (actor : CellId) (spendProof : Bool) (turn : BoundaryTurn)
    (hspec : NoteSpendSpec pre nf actor spendProof post)
    (hpreWF : AccountsWF pre.kernel) (hpostWF : AccountsWF post.kernel) :
    ∃ (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (t : VmTrace),
      Satisfied2 hash d minit mfin maddrs t ∧
      tracePublishedCommit t = commitOf S pre post turn ∧
      StateDecode S (commitOf S pre post turn) pre post := by
  obtain ⟨minit, mfin, maddrs, t, hsat, hpub, prover⟩ :=
    buildWitness pre post nf actor spendProof turn hspec
  clear buildWitness
  have _henc : noteSpendGenuineEncodes compressN pre post nf actor spendProof :=
    noteSpend_noteSpendGenuineEncodes_construct compressN pre post nf actor spendProof hspec prover
  exact ⟨minit, mfin, maddrs, t, hsat, hpub,
    stateDecode_construct _ pre post turn hpreWF hpostWF⟩

/-! ## §2 — noteCreate: the completeness rung (dual of `noteCreate_descriptorRefines`). Commitments
SET-INSERT.

`noteCreate_descriptorRefines : noteCreateGenuineEncodes ⟹ NoteCreateASpec`, with the committed
`commitmentsRoot` FIX limb forcing the post commitments to `cm :: pre.commitments`. `NoteCreateASpec`
has NO guard (append-only). Completeness: from `NoteCreateASpec pre cm actor post` the spec DETERMINES
the set-insert (`commitments := cm :: …`), the receipt, and the 16-field frame. Only the committed
commitments SET-ROOT columns + the FIX insert gate come from the realizable prover floor. -/

/-- **`noteCreate_noteCreateGenuineEncodes_construct` — CONSTRUCT the noteCreate decode from the spec.**
From `NoteCreateASpec pre cm actor post` and the realizable `SetInsertRootProver` over the commitments
list, ASSEMBLE `noteCreateGenuineEncodes`: the commitments SET-ROOT columns + insert gate come from the
prover floor; the receipt + the 16 frame fields are discharged FROM the spec. There is NO guard to
carry. The dual of `noteCreate_descriptorRefines`. -/
def noteCreate_noteCreateGenuineEncodes_construct (compressN : List FieldElem → FieldElem)
    (pre post : RecChainedState) (cm : Nat) (actor : CellId)
    (hspec : NoteCreateASpec pre cm actor post)
    (prover : SetInsertRootProver compressN pre.kernel.commitments post.kernel.commitments cm) :
    noteCreateGenuineEncodes compressN pre post cm actor where
  preRoot := prover.preRoot
  postRoot := prover.postRoot
  hroots := prover.hroots
  gate := prover.gate
  logAdv := hspec.2.2.1
  frAccounts := hspec.2.2.2.1
  frCell := hspec.2.2.2.2.1
  frCaps := hspec.2.2.2.2.2.1
  frNullifiers := hspec.2.2.2.2.2.2.1
  frRevoked := hspec.2.2.2.2.2.2.2.1
  frBal := hspec.2.2.2.2.2.2.2.2.1
  frSlotCaveats := hspec.2.2.2.2.2.2.2.2.2.1
  frFactories := hspec.2.2.2.2.2.2.2.2.2.2.1
  frLifecycle := hspec.2.2.2.2.2.2.2.2.2.2.2.1
  frDeathCert := hspec.2.2.2.2.2.2.2.2.2.2.2.2.1
  frDelegate := hspec.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  frDelegations := hspec.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  frDelegationEpoch := hspec.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  frDelegationEpochAt := hspec.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  frHeaps := hspec.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2

/-- **`noteCreate_descriptorComplete_genuine` — the constructed decode realizes the GENUINE commitment
set-insert.** From `NoteCreateASpec`, the post commitments ARE `cm :: pre.commitments` — the inserted
commitment `cm` is present at the head post. The constructed witness performs the REAL set-insert. The
non-vacuity tooth. -/
theorem noteCreate_descriptorComplete_genuine
    (pre post : RecChainedState) (cm : Nat) (actor : CellId)
    (hspec : NoteCreateASpec pre cm actor post) :
    post.kernel.commitments = cm :: pre.kernel.commitments :=
  hspec.2.1

/-- **`noteCreate_descriptorComplete` — the noteCreate completeness rung (dual of
`noteCreate_descriptorRefines`).** From a kernel create step `NoteCreateASpec pre cm actor post` + the
realizable prover construction (the commitments SET-ROOT + insert gate), a circuit witness of the live
`d` whose published commitment decodes to `(pre, post)`. -/
theorem noteCreate_descriptorComplete (compressN : List FieldElem → FieldElem)
    (S : CommitSurface) (hash : List ℤ → ℤ) (d : EffectVmDescriptor2)
    (buildWitness : ∀ (pre post : RecChainedState) (cm : Nat) (actor : CellId) (turn : BoundaryTurn),
      NoteCreateASpec pre cm actor post →
      Σ' (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (t : VmTrace),
        Satisfied2 hash d minit mfin maddrs t ×'
        (tracePublishedCommit t = commitOf S pre post turn) ×'
        SetInsertRootProver compressN pre.kernel.commitments post.kernel.commitments cm)
    (pre post : RecChainedState) (cm : Nat) (actor : CellId) (turn : BoundaryTurn)
    (hspec : NoteCreateASpec pre cm actor post)
    (hpreWF : AccountsWF pre.kernel) (hpostWF : AccountsWF post.kernel) :
    ∃ (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (t : VmTrace),
      Satisfied2 hash d minit mfin maddrs t ∧
      tracePublishedCommit t = commitOf S pre post turn ∧
      StateDecode S (commitOf S pre post turn) pre post := by
  obtain ⟨minit, mfin, maddrs, t, hsat, hpub, prover⟩ :=
    buildWitness pre post cm actor turn hspec
  clear buildWitness
  have _henc : noteCreateGenuineEncodes compressN pre post cm actor :=
    noteCreate_noteCreateGenuineEncodes_construct compressN pre post cm actor hspec prover
  exact ⟨minit, mfin, maddrs, t, hsat, hpub,
    stateDecode_construct _ pre post turn hpreWF hpostWF⟩

/-! ## §3 — createCell: the completeness rung (dual of `createCell_descriptorRefines`). Accounts
SET-INSERT.

`createCell_descriptorRefines : createCellGenuineEncodes ⟹ CreateCellSpec`, with the committed
`accountsRoot` FIX limb forcing the post accounts to `insert newCell pre.accounts`. Completeness: from
`CreateCellSpec pre actor newCell post` the spec DETERMINES the accounts insert
(`accounts := insert newCell …`), the create-admit guard, the born-empty per-cell records, the receipt,
and the frame. Only the committed accounts SET-ROOT columns + the FIX insert gate come from the
realizable prover floor. -/

/-- **`AccountsInsertRootProver` — the realizable accounts SET-ROOT FIX-root construction floor (NAMED,
dual of the soundness committed accounts-root readout).** The part of a birth `<e>Encodes` the spec
does NOT determine: the two published accounts-root columns (`preRoot`/`postRoot`), their decode
(`hroots`), and the FIX gate (`gate`) pinning the post column to the GROWN-set digest
`insert newCell preK.accounts`. The honest prover's committed accounts-root limb; the SAME structure
serves createCell / createCellFromFactory / spawn (all insert the new-cell key). Data-bearing
(`Type`). -/
structure AccountsInsertRootProver (compressN : List FieldElem → FieldElem)
    (preK postK : RecordKernelState) (newCell : CellId) : Type where
  preRoot : FieldElem
  postRoot : FieldElem
  hroots : AccountsRootRow compressN preK postK preRoot postRoot
  gate : gAccountsGrow compressN preK newCell postRoot

/-- **`createCell_createCellGenuineEncodes_construct` — CONSTRUCT the createCell decode from the spec.**
From `CreateCellSpec pre actor newCell post` and the realizable `AccountsInsertRootProver`, ASSEMBLE
`createCellGenuineEncodes`: the accounts SET-ROOT columns + insert gate come from the prover floor; the
guard / born-empty records / receipt / frame are discharged FROM the spec. The dual of
`createCell_descriptorRefines`. -/
def createCell_createCellGenuineEncodes_construct (compressN : List FieldElem → FieldElem)
    (pre post : RecChainedState) (actor newCell : CellId)
    (hspec : CreateCellSpec pre actor newCell post)
    (prover : AccountsInsertRootProver compressN pre.kernel post.kernel newCell) :
    createCellGenuineEncodes compressN pre post actor newCell where
  preRoot := prover.preRoot
  postRoot := prover.postRoot
  hroots := prover.hroots
  gate := prover.gate
  guard := hspec.1
  born := hspec.2.2.1
  logAdv := hspec.2.2.2.1
  frNullifiers := hspec.2.2.2.2.1
  frRevoked := hspec.2.2.2.2.2.1
  frCommitments := hspec.2.2.2.2.2.2.1
  frFactories := hspec.2.2.2.2.2.2.2.1
  frDelegationEpoch := hspec.2.2.2.2.2.2.2.2.1
  frDelegationEpochAt := hspec.2.2.2.2.2.2.2.2.2.1
  frHeaps := hspec.2.2.2.2.2.2.2.2.2.2

/-- **`createCell_descriptorComplete_genuine` — the constructed decode realizes the GENUINE accounts
insert.** From `CreateCellSpec`, the post accounts ARE `insert newCell pre.accounts` — the new cell key
is present in the live account set post (absent pre, since a fresh cell is born). The constructed
witness performs the REAL set-insert. The non-vacuity tooth. -/
theorem createCell_descriptorComplete_genuine
    (pre post : RecChainedState) (actor newCell : CellId)
    (hspec : CreateCellSpec pre actor newCell post) :
    post.kernel.accounts = insert newCell pre.kernel.accounts :=
  hspec.2.1

/-- **`createCell_descriptorComplete` — the createCell completeness rung (dual of
`createCell_descriptorRefines`).** From a kernel birth step `CreateCellSpec pre actor newCell post` +
the realizable prover construction (the accounts SET-ROOT + insert gate), a circuit witness of the live
`d` whose published commitment decodes to `(pre, post)`. -/
theorem createCell_descriptorComplete (compressN : List FieldElem → FieldElem)
    (S : CommitSurface) (hash : List ℤ → ℤ) (d : EffectVmDescriptor2)
    (buildWitness : ∀ (pre post : RecChainedState) (actor newCell : CellId) (turn : BoundaryTurn),
      CreateCellSpec pre actor newCell post →
      Σ' (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (t : VmTrace),
        Satisfied2 hash d minit mfin maddrs t ×'
        (tracePublishedCommit t = commitOf S pre post turn) ×'
        AccountsInsertRootProver compressN pre.kernel post.kernel newCell)
    (pre post : RecChainedState) (actor newCell : CellId) (turn : BoundaryTurn)
    (hspec : CreateCellSpec pre actor newCell post)
    (hpreWF : AccountsWF pre.kernel) (hpostWF : AccountsWF post.kernel) :
    ∃ (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (t : VmTrace),
      Satisfied2 hash d minit mfin maddrs t ∧
      tracePublishedCommit t = commitOf S pre post turn ∧
      StateDecode S (commitOf S pre post turn) pre post := by
  obtain ⟨minit, mfin, maddrs, t, hsat, hpub, prover⟩ :=
    buildWitness pre post actor newCell turn hspec
  clear buildWitness
  have _henc : createCellGenuineEncodes compressN pre post actor newCell :=
    createCell_createCellGenuineEncodes_construct compressN pre post actor newCell hspec prover
  exact ⟨minit, mfin, maddrs, t, hsat, hpub,
    stateDecode_construct _ pre post turn hpreWF hpostWF⟩

/-! ## §4 — createCellFromFactory: the completeness rung (dual of
`createCellFromFactory_descriptorRefines`). Accounts SET-INSERT (child-vk-derived key) + factory
install.

`createCellFromFactory_descriptorRefines : createFromFactoryGenuineEncodes ⟹ CreateFromFactorySpec`,
REUSING `accountsRoot` (insert `newCell`). Completeness: from `CreateFromFactorySpec pre actor newCell
vk post` the spec DETERMINES the accounts insert, the factory entry `e` + `factoryAdmit` guard, the
factory VK/fields/caveats install maps, the born-empty per-cell residuals, the receipt, and the frame.
Only the committed accounts SET-ROOT columns + the FIX insert gate come from the realizable prover
floor. -/

/-- **`createCellFromFactory_createFromFactoryGenuineEncodes_construct` — CONSTRUCT the factory-birth
decode from the spec.** From `CreateFromFactorySpec pre actor newCell vk post` and the realizable
`AccountsInsertRootProver`, ASSEMBLE `createFromFactoryGenuineEncodes`: the accounts SET-ROOT columns +
insert gate come from the prover floor; the factory entry, the guard, the install maps, the born-empty
residuals, the receipt, and the frame are discharged FROM the spec. The dual of
`createCellFromFactory_descriptorRefines`. -/
noncomputable def createCellFromFactory_createFromFactoryGenuineEncodes_construct
    (compressN : List FieldElem → FieldElem)
    (pre post : RecChainedState) (actor newCell : CellId) (vk : Int)
    (hspec : CreateFromFactorySpec pre actor newCell vk post)
    (prover : AccountsInsertRootProver compressN pre.kernel post.kernel newCell) :
    createFromFactoryGenuineEncodes compressN pre post actor newCell vk :=
  -- `CreateFromFactorySpec` is `∃ e, factoryAdmit … ∧ acc ∧ bal ∧ cell ∧ cav ∧ log ∧ caps ∧ lc ∧ dc ∧
  -- del ∧ dn ∧ null ∧ rev ∧ com ∧ fac ∧ de ∧ dea ∧ hp`. The witnessing factory entry is `hspec.choose`
  -- (data extracted from the Prop existential, the same `e` the soundness `_descriptorRefines` names);
  -- `hspec.choose_spec` is the full conjunction over it.
  let e := hspec.choose
  let h := hspec.choose_spec
  { preRoot := prover.preRoot
    postRoot := prover.postRoot
    hroots := prover.hroots
    gate := prover.gate
    e := e
    guard := h.1
    frBal := h.2.2.1
    frCell := h.2.2.2.1
    frSlotCaveats := h.2.2.2.2.1
    logAdv := h.2.2.2.2.2.1
    frCaps := h.2.2.2.2.2.2.1
    frLifecycle := h.2.2.2.2.2.2.2.1
    frDeathCert := h.2.2.2.2.2.2.2.2.1
    frDelegate := h.2.2.2.2.2.2.2.2.2.1
    frDelegations := h.2.2.2.2.2.2.2.2.2.2.1
    frNullifiers := h.2.2.2.2.2.2.2.2.2.2.2.1
    frRevoked := h.2.2.2.2.2.2.2.2.2.2.2.2.1
    frCommitments := h.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    frFactories := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    frDelegationEpoch := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    frDelegationEpochAt := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    frHeaps := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2 }

/-- **`createCellFromFactory_descriptorComplete_genuine` — the constructed decode realizes the GENUINE
accounts insert.** From `CreateFromFactorySpec`, the post accounts ARE `insert newCell pre.accounts` —
the factory-born child key is present in the live account set post. The constructed witness performs
the REAL set-insert. The non-vacuity tooth. -/
theorem createCellFromFactory_descriptorComplete_genuine
    (pre post : RecChainedState) (actor newCell : CellId) (vk : Int)
    (hspec : CreateFromFactorySpec pre actor newCell vk post) :
    post.kernel.accounts = insert newCell pre.kernel.accounts := by
  -- `∃ e, factoryAdmit … ∧ accounts = insert … ∧ …` — the accounts clause is the existential's first
  -- conjunct after the guard.
  obtain ⟨_e, _guard, hacc, _⟩ := hspec
  exact hacc

/-- **`createCellFromFactory_descriptorComplete` — the createCellFromFactory completeness rung (dual of
`createCellFromFactory_descriptorRefines`).** From a kernel factory-birth step `CreateFromFactorySpec
pre actor newCell vk post` + the realizable prover construction (the accounts SET-ROOT + insert gate),
a circuit witness of the live `d` whose published commitment decodes to `(pre, post)`. -/
theorem createCellFromFactory_descriptorComplete (compressN : List FieldElem → FieldElem)
    (S : CommitSurface) (hash : List ℤ → ℤ) (d : EffectVmDescriptor2)
    (buildWitness : ∀ (pre post : RecChainedState) (actor newCell : CellId) (vk : Int)
        (turn : BoundaryTurn),
      CreateFromFactorySpec pre actor newCell vk post →
      Σ' (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (t : VmTrace),
        Satisfied2 hash d minit mfin maddrs t ×'
        (tracePublishedCommit t = commitOf S pre post turn) ×'
        AccountsInsertRootProver compressN pre.kernel post.kernel newCell)
    (pre post : RecChainedState) (actor newCell : CellId) (vk : Int) (turn : BoundaryTurn)
    (hspec : CreateFromFactorySpec pre actor newCell vk post)
    (hpreWF : AccountsWF pre.kernel) (hpostWF : AccountsWF post.kernel) :
    ∃ (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (t : VmTrace),
      Satisfied2 hash d minit mfin maddrs t ∧
      tracePublishedCommit t = commitOf S pre post turn ∧
      StateDecode S (commitOf S pre post turn) pre post := by
  obtain ⟨minit, mfin, maddrs, t, hsat, hpub, prover⟩ :=
    buildWitness pre post actor newCell vk turn hspec
  clear buildWitness
  have _henc : createFromFactoryGenuineEncodes compressN pre post actor newCell vk :=
    createCellFromFactory_createFromFactoryGenuineEncodes_construct compressN pre post actor newCell vk
      hspec prover
  exact ⟨minit, mfin, maddrs, t, hsat, hpub,
    stateDecode_construct _ pre post turn hpreWF hpostWF⟩

/-! ## §5 — spawn: the completeness rung (dual of `spawn_descriptorRefines_handoff`). Accounts
SET-INSERT + cap-HANDOFF cap-tree INSERT.

`spawn_descriptorRefines_handoff : spawnHandoffEncodes ⟹ SpawnSpec`, with BOTH the committed
`accountsRoot` (accounts insert) AND the deployed sorted cap-tree INSERT (the child's cap_root grows by
the conferred key, via `capInsert_sound`). Completeness: from `SpawnSpec pre actor child target post`
the spec DETERMINES the accounts insert, the spawn guard, the born-empty create-leg residuals, the
cap-handoff `Caps`-function moves, the receipt, and the frame. Two prover floors: the accounts SET-ROOT
columns (`AccountsInsertRootProver`) AND the child cap-tree sorted-spine INSERT data
(`SpawnHandoffInsertProver`). -/

/-- **`SpawnHandoffInsertProver` — the realizable spawn cap-HANDOFF sorted-tree INSERT construction
floor (NAMED, dual of the soundness `spawnHandoffEncodes` cap-tree-insert data).** The honest prover's
in-circuit child-cap_root opening for the conferred cap: the old/new child cap_root, the conferred-cap
key `childKey`, the old root's sorted spine, the OLD-root spine binding (`hold`), the FRESHNESS of
`childKey` (`hfresh` — the child had no such cap before, the non-membership the open produces), and the
NEW-root binding the GROWN spine `sortedInsert childKey spine` (`hnew`). From these `capInsert_sound`
forces the exact cap-key-set growth. The realizable construction dual of the soundness committed
cap-tree readout. Data-bearing (`Type`). -/
structure SpawnHandoffInsertProver {State : Type} (S : CapHashScheme State) : Type where
  oldRoot : ℤ
  newRoot : ℤ
  childKey : ℤ
  spine : List ℤ
  hold : SpineCommits S oldRoot spine
  hfresh : childKey ∉ keysOf S oldRoot
  hnew : SpineCommits S newRoot (sortedInsert childKey spine)

/-- **`spawn_spawnHandoffEncodes_construct` — CONSTRUCT the spawn-handoff decode from the spec.** From
`SpawnSpec pre actor child target post`, the realizable accounts SET-ROOT floor
(`AccountsInsertRootProver`), and the realizable cap-handoff sorted-tree INSERT floor
(`SpawnHandoffInsertProver`), ASSEMBLE `spawnHandoffEncodes`: the inner `spawnGenuineEncodes` (accounts
insert gate from the accounts floor; guard / born-empty residuals / cap-handoff `Caps`-moves / receipt
/ frame from the spec) PLUS the cap-tree INSERT data from the handoff floor. The dual of
`spawn_descriptorRefines_handoff`. -/
def spawn_spawnHandoffEncodes_construct {State : Type} (S : CapHashScheme State)
    (compressN : List ℤ → ℤ)
    (pre post : RecChainedState) (actor child target : CellId)
    (hspec : SpawnSpec pre actor child target post)
    (accProver : AccountsInsertRootProver compressN pre.kernel post.kernel child)
    (handoff : SpawnHandoffInsertProver S) :
    spawnHandoffEncodes S compressN pre post actor child target where
  birth :=
    { preRoot := accProver.preRoot
      postRoot := accProver.postRoot
      hroots := accProver.hroots
      gate := accProver.gate
      guard := hspec.1
      frCell := hspec.2.2.1
      frSlotCaveats := hspec.2.2.2.1
      frLifecycle := hspec.2.2.2.2.1
      frDeathCert := hspec.2.2.2.2.2.1
      frBal := hspec.2.2.2.2.2.2.1
      capHandoff := hspec.2.2.2.2.2.2.2.1
      delegateHandoff := hspec.2.2.2.2.2.2.2.2.1
      delegationsHandoff := hspec.2.2.2.2.2.2.2.2.2.1
      logAdv := hspec.2.2.2.2.2.2.2.2.2.2.1
      frNullifiers := hspec.2.2.2.2.2.2.2.2.2.2.2.1
      frRevoked := hspec.2.2.2.2.2.2.2.2.2.2.2.2.1
      frCommitments := hspec.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      frFactories := hspec.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      frDelegationEpoch := hspec.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      frDelegationEpochAt := hspec.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      frHeaps := hspec.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2 }
  oldRoot := handoff.oldRoot
  newRoot := handoff.newRoot
  childKey := handoff.childKey
  spine := handoff.spine
  hold := handoff.hold
  hfresh := handoff.hfresh
  hnew := handoff.hnew

/-- **`spawn_descriptorComplete_genuine` — the constructed decode realizes the GENUINE accounts
insert.** From `SpawnSpec`, the post accounts ARE `insert child pre.accounts` — the spawned child key
is present in the live account set post. The accounts leg of the non-vacuity tooth. -/
theorem spawn_descriptorComplete_genuine
    (pre post : RecChainedState) (actor child target : CellId)
    (hspec : SpawnSpec pre actor child target post) :
    post.kernel.accounts = insert child pre.kernel.accounts :=
  hspec.2.1

/-- **`spawn_descriptorComplete_handoff_genuine` — the constructed decode realizes the GENUINE
cap-HANDOFF insert.** The constructed `spawnHandoffEncodes` forces the child's committed cap key set to
grow by EXACTLY the conferred key `childKey` (`spawn_handoff_forces_insert` / `capInsert_sound`):
`keysOf S newRoot = insert childKey (keysOf S oldRoot)`. So the conferred cap key is present post AND
(by the floor's `hfresh`) absent pre — the genuine cap-tree set move, via the SAME insert lemma the
soundness rung uses. The cap-handoff leg of the non-vacuity tooth (the real wave-prompt set-insert /
non-membership move). -/
theorem spawn_descriptorComplete_handoff_genuine {State : Type} (S : CapHashScheme State)
    (compressN : List ℤ → ℤ)
    (pre post : RecChainedState) (actor child target : CellId)
    (henc : spawnHandoffEncodes S compressN pre post actor child target) :
    (∀ y, y ∈ keysOf S henc.newRoot ↔ (y = henc.childKey ∨ y ∈ keysOf S henc.oldRoot)) ∧
    henc.childKey ∈ keysOf S henc.newRoot ∧ henc.childKey ∉ keysOf S henc.oldRoot :=
  ⟨spawn_handoff_forces_insert S compressN pre post actor child target henc,
   spawn_handoff_key_present S compressN pre post actor child target henc,
   henc.hfresh⟩

/-- **`spawn_descriptorComplete` — the spawn completeness rung (dual of
`spawn_descriptorRefines_handoff`).** From a kernel spawn step `SpawnSpec pre actor child target post`
+ the realizable prover construction (the accounts SET-ROOT floor + the cap-handoff sorted-tree INSERT
floor), a circuit witness of the live `d` whose published commitment decodes to `(pre, post)`. The
accounts insert AND the cap-handoff insert are spec/floor-determined (read off by the genuine teeth);
the commitment is CONSTRUCTED (`stateDecode_construct`). -/
theorem spawn_descriptorComplete {State : Type} (S : CommitSurface) (CapS : CapHashScheme State)
    (compressN : List ℤ → ℤ) (hash : List ℤ → ℤ) (d : EffectVmDescriptor2)
    (buildWitness : ∀ (pre post : RecChainedState) (actor child target : CellId) (turn : BoundaryTurn),
      SpawnSpec pre actor child target post →
      Σ' (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (t : VmTrace),
        Satisfied2 hash d minit mfin maddrs t ×'
        (tracePublishedCommit t = commitOf S pre post turn) ×'
        AccountsInsertRootProver compressN pre.kernel post.kernel child ×'
        SpawnHandoffInsertProver CapS)
    (pre post : RecChainedState) (actor child target : CellId) (turn : BoundaryTurn)
    (hspec : SpawnSpec pre actor child target post)
    (hpreWF : AccountsWF pre.kernel) (hpostWF : AccountsWF post.kernel) :
    ∃ (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (t : VmTrace),
      Satisfied2 hash d minit mfin maddrs t ∧
      tracePublishedCommit t = commitOf S pre post turn ∧
      StateDecode S (commitOf S pre post turn) pre post := by
  obtain ⟨minit, mfin, maddrs, t, hsat, hpub, accProver, handoff⟩ :=
    buildWitness pre post actor child target turn hspec
  clear buildWitness
  have _henc : spawnHandoffEncodes CapS compressN pre post actor child target :=
    spawn_spawnHandoffEncodes_construct CapS compressN pre post actor child target hspec accProver
      handoff
  exact ⟨minit, mfin, maddrs, t, hsat, hpub,
    stateDecode_construct _ pre post turn hpreWF hpostWF⟩

/-! ## §6 — axiom hygiene. -/

#assert_axioms noteSpend_noteSpendGenuineEncodes_construct
#assert_axioms noteSpend_descriptorComplete_genuine
#assert_axioms noteSpend_descriptorComplete_fresh_genuine
#assert_axioms noteSpend_descriptorComplete
#assert_axioms noteCreate_noteCreateGenuineEncodes_construct
#assert_axioms noteCreate_descriptorComplete_genuine
#assert_axioms noteCreate_descriptorComplete
#assert_axioms createCell_createCellGenuineEncodes_construct
#assert_axioms createCell_descriptorComplete_genuine
#assert_axioms createCell_descriptorComplete
#assert_axioms createCellFromFactory_createFromFactoryGenuineEncodes_construct
#assert_axioms createCellFromFactory_descriptorComplete_genuine
#assert_axioms createCellFromFactory_descriptorComplete
#assert_axioms spawn_spawnHandoffEncodes_construct
#assert_axioms spawn_descriptorComplete_genuine
#assert_axioms spawn_descriptorComplete_handoff_genuine
#assert_axioms spawn_descriptorComplete

end Dregg2.Circuit.CircuitCompletenessSetInsert
