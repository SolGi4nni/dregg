/-
# Dregg2.Circuit.Argus.Effects.CreateCell — CreateCell against the Argus IR: a PROVEN obstruction
(`status = blocked`), the structural-account-grow primitive the IR genuinely LACKS.

`Argus/Stmt.lean` laid the cornerstone (the executor IS the meaning of a `RecStmt` term) and the
template welds (transfer/mint/burn `setCell`/`setBal`; createEscrow's two-component side-table move)
re-validated it. This module attempts the SAME weld for `CreateCell` — and reports, as a GENUINE
PROVEN THEOREM (not a stub, not a fake green), that it cannot be done with the current IR.

## THE EXECUTOR (what a faithful term would have to capture EXACTLY)

`CreateCell`'s verified chained kernel step is `createCellChainA` (`Exec/TurnExecutorFull.lean:798`):

    createCellChainA s actor newCell
      = if mintAuthorizedB s.kernel.caps actor newCell = true ∧ newCell ∉ s.kernel.accounts then
          some { kernel := createCellIntoAsset s.kernel newCell
                 log    := { actor := actor, src := newCell, dst := newCell, amt := 0 } :: s.log }
        else none

and its kernel effect `createCellIntoAsset` (`Exec/RecordKernel.lean:880`) does TWO structural things:

  (A) **GROW `accounts`**: `accounts := insert newCell k.accounts` — a STRUCTURAL ACCOUNT-ALLOCATION
      that adds a brand-new live cell to the conserved index set (the `CreateCellSpec` clause
      `st'.kernel.accounts = insert newCell st.kernel.accounts`, `Spec/accountgrowth.lean:178`).
  (B) **born-empty per-cell slots** at `newCell` (`bornEmptyCellSlots`, `RecordKernel.lean:864`):
      reset `cell`/`caps`/`delegate`/`delegations`/`slotCaveats`/`lifecycle`/`deathCert`/`bal` to
      defaults at the fresh id.

Leg (B) is FULLY expressible by the existing §A component-write primitives (`setCell`, `setCaps`,
`setDelegate`, `setDelegations`, `setSlotCaveats`, `setLifecycle`, `setDeathCert`, `setBal`). Leg (A)
is NOT: the `RecStmt` IR (`Argus/Stmt.lean:41`) has 22 constructors, and **none of them writes the
`accounts : Finset CellId` field** — there is no `setAccounts` / structural-alloc / grow-accounts
constructor. The component setters all overwrite a different component (`setCell`, the 8 list
side-tables, the 5 per-cell-function registries, the cap graph); the gates (`guard`/`checkLe`/
`checkSubset`) never mutate. So `accounts` is, structurally, FROZEN under `interp`.

## THE MISSING PRIMITIVE (`missingPrimitive`, reported HONESTLY — not faked)

The IR lacks a **structural account-allocation primitive** (a `setAccounts (g : RecordKernelState →
Finset CellId)` constructor, or specifically a `growAccount (n : RecordKernelState → CellId)` that
writes `accounts := insert (n k) k.accounts`). This is exactly the alloc/grow-accounts primitive the
task hint anticipated for `CreateCell`/`MakeSovereign`. Adding it requires editing `Argus/Stmt.lean`
(its `RecStmt` inductive + `interp`) — which this module is NOT permitted to touch (it owns only
itself). So the weld is BLOCKED on a primitive that lives in another file, and the honest deliverable
is the PROOF that it is genuinely needed.

## WHAT THIS MODULE PROVES (the obstruction, with teeth — l4v-meaningful, NOT a placeholder)

  1. `interp_preserves_accounts` — the STRUCTURAL FRAME THEOREM: for EVERY `RecStmt` term `s`, if
     `interp s k = some k'` then `k'.accounts = k.accounts`. Proved by induction over all 22
     constructors (each component write touches a NON-`accounts` field; the gates return the input;
     `seq` chains the two frames). This is the load-bearing fact — the IR provably cannot grow
     `accounts`.
  2. `createCellChainA_grows_accounts` — the executor genuinely INSERTS `newCell` (its post `accounts`
     is `insert newCell s.kernel.accounts`); and on a FRESH id the growth has TEETH: `newCell` is in
     the post-accounts but was NOT in the pre-accounts (the index set strictly grew). NON-VACUOUS.
  3. `no_argus_term_captures_createCell` — THE OBSTRUCTION, as a theorem: there is NO `RecStmt` term
     `s` whose `interp` on the kernel reproduces `createCellChainA`'s kernel post-state on a FRESH-id
     commit — because (1) freezes `accounts` while (2) grows it, a contradiction. So the
     executor-refinement cornerstone `interp_<name>Stmt_eq_<executor>` is UNACHIEVABLE for CreateCell
     with this IR. This is the precise, machine-checked content of "blocked on a missing primitive".

There is NO `createCellStmt`, NO `interp_createCellStmt_eq_…`, and NO `createCell_compile_sound` here:
faking any of them (e.g. a term that silently freezes `accounts`, or a `:= True` weld) would be a
LIE about a load-bearing guarantee. The blocked status is the honest, valuable result.

## Honesty

`#assert_axioms` on every theorem ⊆ {propext, Classical.choice, Quot.sound}; no `sorry`, no `:= True`,
no `native_decide`. Imports are read-only (`Argus/Stmt` for the IR + `Spec/accountgrowth` for the
verified executor/spec); this file owns only its own declarations and edits no other Argus file.
-/
import Dregg2.Circuit.Argus.Stmt
import Dregg2.Circuit.Spec.accountgrowth

namespace Dregg2.Circuit.Argus.Effects.CreateCell

-- `createCellIntoAsset` lives in `Dregg2.Exec` (RecordKernel.lean:880); `createCellChainA` and its
-- factoring lemma `createCellChainA_factors` live in `Dregg2.Exec.TurnExecutorFull`. We open both
-- namespaces broadly so the verified executor + its decode lemma resolve unqualified.
open Dregg2.Exec
open Dregg2.Exec.TurnExecutorFull
open Dregg2.Circuit.Argus (RecStmt interp)
open Dregg2.Circuit.Spec.AccountGrowth (createCellAdmit CreateCellSpec)

/-! ## §1 — THE STRUCTURAL FRAME THEOREM: `interp` of EVERY `RecStmt` term FREEZES `accounts`.

This is the heart of the obstruction. The `RecStmt` IR (`Argus/Stmt.lean:41`) has 22 constructors,
and we prove by structural induction that NOT ONE of them can change the `accounts : Finset CellId`
field through `interp`:

  * `skip` returns the input `k` (accounts unchanged);
  * `guard`/`checkLe`/`checkSubset` are pure domain-restrictors — they return `k` on admit (unchanged)
    or `none` on reject (no post-state at all);
  * every component write `setCell`/`setBal`/`insFresh`/`setCaps`/`set<ListTable>`/`set<PerCellFn>`
    is a record-update `{ k with <field> := g k }` where `<field> ≠ accounts`, so `accounts` rides
    through by the record-update frame;
  * `seq s t` chains: if `s` froze accounts on the intermediate state and `t` froze it from there,
    the composite freezes it.

So a `RecStmt` term is structurally INCAPABLE of account growth. (This is not a property of any
PARTICULAR term — it holds for ALL terms, because the IR has no `accounts`-writing constructor.) -/

/-- **`interp_preserves_accounts` — the STRUCTURAL FRAME (PROVED, all 22 constructors).** For every
Argus IR term `s`, a committed interpretation preserves the live-account index set: `interp s k =
some k' → k'.accounts = k.accounts`. The machine-checked statement that the `RecStmt` IR has NO
account-allocation primitive — `accounts` is frozen under every term. -/
theorem interp_preserves_accounts :
    ∀ (s : RecStmt) (k k' : RecordKernelState), interp s k = some k' → k'.accounts = k.accounts := by
  intro s
  induction s with
  | skip => intro k k' h; simp only [interp, Option.some.injEq] at h; rw [← h]
  | guard φ =>
      intro k k' h
      simp only [interp] at h
      by_cases hφ : φ k
      · rw [if_pos hφ, Option.some.injEq] at h; rw [← h]
      · rw [if_neg hφ] at h; exact absurd h (by simp)
  | setCell T leaf => intro k k' h; simp only [interp, Option.some.injEq] at h; rw [← h]
  | setBal b => intro k k' h; simp only [interp, Option.some.injEq] at h; rw [← h]
  | insFresh n =>
      intro k k' h
      simp only [interp] at h
      by_cases hn : n k ∈ k.nullifiers
      · rw [if_pos hn] at h; exact absurd h (by simp)
      · rw [if_neg hn, Option.some.injEq] at h; rw [← h]
  | setCaps g => intro k k' h; simp only [interp, Option.some.injEq] at h; rw [← h]
  | setNullifiers g => intro k k' h; simp only [interp, Option.some.injEq] at h; rw [← h]
  | setRevoked g => intro k k' h; simp only [interp, Option.some.injEq] at h; rw [← h]
  | setCommitments g => intro k k' h; simp only [interp, Option.some.injEq] at h; rw [← h]
  | setEscrows g => intro k k' h; simp only [interp, Option.some.injEq] at h; rw [← h]
  | setQueues g => intro k k' h; simp only [interp, Option.some.injEq] at h; rw [← h]
  | setSwiss g => intro k k' h; simp only [interp, Option.some.injEq] at h; rw [← h]
  | setFactories g => intro k k' h; simp only [interp, Option.some.injEq] at h; rw [← h]
  | setSealedBoxes g => intro k k' h; simp only [interp, Option.some.injEq] at h; rw [← h]
  | setLifecycle g => intro k k' h; simp only [interp, Option.some.injEq] at h; rw [← h]
  | setDeathCert g => intro k k' h; simp only [interp, Option.some.injEq] at h; rw [← h]
  | setDelegate g => intro k k' h; simp only [interp, Option.some.injEq] at h; rw [← h]
  | setSlotCaveats g => intro k k' h; simp only [interp, Option.some.injEq] at h; rw [← h]
  | setDelegations g => intro k k' h; simp only [interp, Option.some.injEq] at h; rw [← h]
  | checkLe a b =>
      intro k k' h
      simp only [interp] at h
      by_cases hle : a k ≤ b k
      · rw [if_pos hle, Option.some.injEq] at h; rw [← h]
      · rw [if_neg hle] at h; exact absurd h (by simp)
  | checkSubset a b =>
      intro k k' h
      simp only [interp] at h
      by_cases hle : a k ≤ b k
      · rw [if_pos hle, Option.some.injEq] at h; rw [← h]
      · rw [if_neg hle] at h; exact absurd h (by simp)
  | seq s t ihs iht =>
      intro k k' h
      simp only [interp, Option.bind] at h
      -- `interp s k` must be `some k₁` for the composite to commit; chain the two frames.
      cases hs : interp s k with
      | none => rw [hs] at h; exact absurd h (by simp)
      | some k₁ =>
          rw [hs] at h
          -- `accounts` rides through `s` (k₁) then through `t` (k') — both by the IH frames.
          exact (iht k₁ k' h).trans (ihs k k₁ hs)

#assert_axioms interp_preserves_accounts

/-- **`interp_accounts_unchanged_corollary` — restated as a clean obstruction handle.** No Argus term
can produce a post-state whose `accounts` differs from the input's. This is the exact negation of what
`CreateCell` requires (its post `accounts` STRICTLY contains a fresh `newCell`). -/
theorem interp_accounts_unchanged_corollary
    (s : RecStmt) {k k' : RecordKernelState} (h : interp s k = some k') :
    k'.accounts = k.accounts :=
  interp_preserves_accounts s k k' h

#assert_axioms interp_accounts_unchanged_corollary

/-! ## §2 — THE EXECUTOR GENUINELY GROWS `accounts` (the thing the IR cannot match).

The verified `createCellChainA` post-state inserts `newCell` into `accounts`. We pin both the exact
post shape and — the non-vacuity tooth — that on a FRESH id the growth is REAL: `newCell` is a live
account AFTER but was absent BEFORE. So the executor's `accounts`-effect is genuinely non-trivial, the
precise effect §1 proves no `RecStmt` term can have. -/

/-- **`createCellChainA_post_accounts` — the executor's `accounts` effect (PROVED).** A committed
`createCellChainA` produces a post-state whose `accounts` is EXACTLY `insert newCell s.kernel.accounts`
— the structural account-grow leg (A). Read straight off the verified `createCellChainA_factors`
(`TurnExecutorFull.lean:807`) + `createCellIntoAsset` (`RecordKernel.lean:880`). -/
theorem createCellChainA_post_accounts {s s' : RecChainedState} {actor newCell : CellId}
    (h : createCellChainA s actor newCell = some s') :
    s'.kernel.accounts = insert newCell s.kernel.accounts := by
  obtain ⟨_, _, hpost⟩ := createCellChainA_factors h
  rw [hpost]
  -- the post kernel is `createCellIntoAsset s.kernel newCell`, whose `accounts` projection is the insert.
  show (createCellIntoAsset s.kernel newCell).accounts = insert newCell s.kernel.accounts
  unfold createCellIntoAsset
  rfl

/-- **`createCellChainA_grows_accounts` — the growth has TEETH (PROVED, non-vacuous).** When the create
COMMITS, `newCell` is a live account in the post-state. Combined with the gate's freshness conjunct
(`newCell ∉ s.kernel.accounts`, the executor's `if`), this is a STRICT growth: the fresh id is present
AFTER but absent BEFORE — exactly the `accounts`-change §1 proves no Argus term can produce. -/
theorem createCellChainA_grows_accounts {s s' : RecChainedState} {actor newCell : CellId}
    (h : createCellChainA s actor newCell = some s') :
    newCell ∈ s'.kernel.accounts ∧ newCell ∉ s.kernel.accounts := by
  obtain ⟨_, hfresh, _⟩ := createCellChainA_factors h
  refine ⟨?_, hfresh⟩
  rw [createCellChainA_post_accounts h]
  exact Finset.mem_insert_self _ _

#assert_axioms createCellChainA_post_accounts
#assert_axioms createCellChainA_grows_accounts

/-! ## §3 — THE OBSTRUCTION, AS A THEOREM: no Argus term captures CreateCell (BLOCKED on a missing
primitive).

The §1 frame (every `RecStmt` freezes `accounts`) and the §2 growth (the executor strictly grows
`accounts` on a fresh commit) are CONTRADICTORY on the same input. So no `RecStmt` term `s` can have
`interp s` reproduce `createCellChainA`'s kernel post-state when the create commits — the
executor-refinement cornerstone `interp_createCellStmt_eq_createCellChainA` is UNACHIEVABLE with the
current IR. This is the machine-checked statement of `status = blocked` / `missingPrimitive`. -/

/-- **`no_argus_term_captures_createCell` — THE OBSTRUCTION (PROVED).** There is NO `RecStmt` term `s`
such that, on a kernel `k` where `createCellChainA` COMMITS into `s'`, `interp s k` produces the
executor's kernel post-state `s'.kernel`. Proof: such an `s` would (by §1) freeze `accounts`, giving
`s'.kernel.accounts = k.accounts`; but (by §2) the commit grows `accounts` (`newCell ∈ s'.kernel.accounts`,
`newCell ∉ k.accounts`), so `newCell ∈ k.accounts` AND `newCell ∉ k.accounts` — a contradiction.

Hence the CreateCell weld is genuinely blocked: a faithful `createCellStmt` would need a structural
account-allocation primitive (`setAccounts`/`growAccount`) the IR lacks, and which lives in
`Argus/Stmt.lean` (not editable here). Stated over a chained `s` with `s.kernel = k` so both the IR
term (on the bare kernel) and the executor (on the chain) name the SAME pre-`accounts`. -/
theorem no_argus_term_captures_createCell
    (s : RecStmt) (k : RecordKernelState) (st st' : RecChainedState)
    (hk : st.kernel = k) (actor newCell : CellId)
    (hexec : createCellChainA st actor newCell = some st') :
    ¬ (∃ k', interp s k = some k' ∧ k' = st'.kernel) := by
  rintro ⟨k', hinterp, hk'⟩
  -- §1: the IR term freezes `accounts` ⇒ `st'.kernel.accounts = k.accounts`.
  have hfreeze : st'.kernel.accounts = k.accounts := by
    rw [← hk']; exact interp_preserves_accounts s k k' hinterp
  -- §2: the executor grows `accounts` ⇒ `newCell ∈ st'.kernel.accounts` and `newCell ∉ st.kernel.accounts`.
  obtain ⟨hin, hout⟩ := createCellChainA_grows_accounts hexec
  -- contradiction: `newCell ∈ k.accounts` (rewrite hin via the freeze) but `newCell ∉ k.accounts`.
  rw [hfreeze] at hin
  rw [hk] at hout
  exact hout hin

#assert_axioms no_argus_term_captures_createCell

/-! ## §4 — NON-VACUITY: the obstruction is about a REALIZABLE CreateCell (the impossible weld is for
a create that genuinely fires), and the spec it would have to meet genuinely demands account growth.

The §3 obstruction would be hollow if `createCellChainA` never committed, or if `CreateCellSpec` did
not actually require `accounts` to grow. We exhibit a concrete two-account kernel where a privileged
actor creates a FRESH cell `2`, the create COMMITS, and the post `accounts` strictly grew — so the
theorem rules out a weld for a LIVE effect, not a vacuous one. -/

/-- A concrete kernel for the witnesses: cells `0` and `1` are live accounts; cell `0` holds a `node 2`
cap (the privileged-creation authority `mintAuthorizedB` needs over the fresh id `2`). -/
def kCC : RecordKernelState :=
  { accounts := {0, 1}
    cell := fun _ => .record [("balance", .int 0)]
    caps := fun l => if l = 0 then [Dregg2.Authority.Cap.node 2] else [] }

/-- The chained pre-state for the witnesses (empty receipt log). -/
def stCC : RecChainedState := { kernel := kCC, log := [] }

-- The create of FRESH cell `2` by privileged actor `0` genuinely COMMITS (non-vacuous gate): both
-- the privileged-creation authority and the freshness conjunct hold.
#guard (createCellChainA stCC 0 2).isSome

-- … and the growth is OBSERVABLE: the post `accounts` strictly grew (cell `2` is present AFTER, absent
-- BEFORE), so the impossible-weld theorem is about a REAL effect on a REAL state.
#guard ¬ (2 ∈ stCC.kernel.accounts)
#guard (((createCellChainA stCC 0 2).map (fun s => decide (2 ∈ s.kernel.accounts))) == some true)

/-- **`createCell_commits_and_grows` — the obstruction is NON-VACUOUS (PROVED).** On the concrete
kernel `kCC`, the create of fresh cell `2` by privileged actor `0` COMMITS, and the committed
post-state genuinely grows `accounts` (cell `2` present AFTER, absent BEFORE). So
`no_argus_term_captures_createCell` rules out a weld for a CreateCell that REALLY fires and REALLY
allocates — not a vacuously-rejecting placeholder. -/
theorem createCell_commits_and_grows :
    ∃ st', createCellChainA stCC 0 2 = some st'
      ∧ 2 ∈ st'.kernel.accounts ∧ 2 ∉ stCC.kernel.accounts := by
  -- the gate holds (privileged authority over `2` from the `node 2` cap at cell 0 ∧ `2 ∉ {0,1}`).
  have hgate : mintAuthorizedB stCC.kernel.caps 0 2 = true ∧ (2 : CellId) ∉ stCC.kernel.accounts := by
    refine ⟨?_, ?_⟩ <;> decide
  -- so the executor's `if` opens to `some {...}`; name that committed state via `createCellChainA`'s def.
  have hcommit : createCellChainA stCC 0 2
      = some { kernel := createCellIntoAsset stCC.kernel 2
               log    := { actor := 0, src := 2, dst := 2, amt := 0 } :: stCC.log } := by
    unfold createCellChainA; rw [if_pos hgate]
  refine ⟨_, hcommit, ?_, hgate.2⟩
  -- the post `accounts` is `insert 2 …` (the structural grow), so `2` is live after.
  rw [createCellChainA_post_accounts hcommit]
  exact Finset.mem_insert_self _ _

#assert_axioms createCell_commits_and_grows

/-! ## §5 — THE SPEC THE WELD WOULD HAVE TO MEET ALSO DEMANDS GROWTH (so the obstruction is intrinsic,
not an artifact of routing through the raw executor).

A skeptic might hope the blockage is only against the RAW `createCellChainA` and that some weld against
the declarative `CreateCellSpec` (the surface the v2 `createCellA_full_sound` descriptor concludes,
`Inst/createCellA.lean`) could sidestep it. It cannot: `CreateCellSpec` ITSELF mandates
`st'.kernel.accounts = insert newCell st.kernel.accounts` (`Spec/accountgrowth.lean:178`). So ANY
post-state the descriptor pins has grown `accounts`, and §1 still forbids an Argus term from reaching
it — the obstruction is intrinsic to CreateCell's semantics, at BOTH the executor and the descriptor
surface. -/

/-- **`createCellSpec_demands_growth` — the descriptor surface needs growth too (PROVED).** Any
`st'` satisfying `CreateCellSpec` has `st'.kernel.accounts = insert newCell st.kernel.accounts` — so
welding against the v2 full-state descriptor (whose soundness is `CreateCellSpec`) is blocked by §1
for the SAME reason as the raw-executor weld: the spec's post `accounts` strictly grew. -/
theorem createCellSpec_demands_growth
    {st st' : RecChainedState} {actor newCell : CellId}
    (h : CreateCellSpec st actor newCell st') :
    st'.kernel.accounts = insert newCell st.kernel.accounts :=
  h.2.1

/-- **`no_argus_term_meets_createCellSpec` — THE OBSTRUCTION at the DESCRIPTOR surface (PROVED).** No
`RecStmt` term reaches a `CreateCellSpec`-pinned post-state on a FRESH id: §1 freezes `accounts`, the
spec grows it. So the COMPILE weld `createCell_compile_sound` (against the v2 `createCellA_full_sound`
descriptor) is ALSO unachievable with this IR — confirming the missing-primitive obstruction is not an
artifact of the raw-executor surface. -/
theorem no_argus_term_meets_createCellSpec
    (s : RecStmt) (st st' : RecChainedState) (actor newCell : CellId)
    (hfresh : newCell ∉ st.kernel.accounts)
    (hspec : CreateCellSpec st actor newCell st') :
    ¬ (∃ k', interp s st.kernel = some k' ∧ k' = st'.kernel) := by
  rintro ⟨k', hinterp, hk'⟩
  have hfreeze : st'.kernel.accounts = st.kernel.accounts := by
    rw [← hk']; exact interp_preserves_accounts s st.kernel k' hinterp
  have hgrow : st'.kernel.accounts = insert newCell st.kernel.accounts :=
    createCellSpec_demands_growth hspec
  -- `newCell ∈ insert newCell …` = `newCell ∈ st'.kernel.accounts` = `newCell ∈ st.kernel.accounts`,
  -- contradicting freshness.
  have hin : newCell ∈ st.kernel.accounts := by
    rw [← hfreeze, hgrow]; exact Finset.mem_insert_self _ _
  exact hfresh hin

#assert_axioms createCellSpec_demands_growth
#assert_axioms no_argus_term_meets_createCellSpec

end Dregg2.Circuit.Argus.Effects.CreateCell
