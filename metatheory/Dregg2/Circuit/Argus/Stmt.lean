import Dregg2.Exec.RecordKernel
import Dregg2.Exec.TurnExecutorFull

/-!
# Argus — the state-transformer IR (the cornerstone)

The first word that cannot lie: a *reified* state transformer with **two
interpretations of one term**. `interp` runs it as the executor; a later
`compile` emits its circuit. Because both the executor and the circuit are
*derived from the same `RecStmt`*, they cannot drift — the per-effect
soundness obligation collapses from a bespoke proof to one generic theorem
over the term (the `effect_circuit_full_sound` back-end, fed by the term).

This file is the cornerstone only: the IR, its executable `interp` (the
worthwhile semantics — `insFresh` carries no-double-spend *inline*, where it
belongs), and the proof that `interp` of the transfer term **is** the verified
`recKExec`. That refinement is the whole bet in miniature: the executor is, by
construction, the meaning of the term.

`hole` (intents / coeffects) and `par` (jointturns / separation-⊗) are the
constructors reserved for the layers above; the asymmetric turn prologue/
epilogue (fee · nonce · receipt, conservation-modulo-burn) wraps this body.
-/

namespace Dregg2.Circuit.Argus

open Dregg2.Exec
-- `Caps` (= `Label → List Cap`) and `Cap` live in `Dregg2.Authority`; we open it so the
-- side-table write-primitives below can name them. NOTE (the autobind lesson): `Caps` would
-- otherwise bind as a fresh universe variable in a constructor signature, so we keep this open in
-- scope rather than leaving the identifier free.
open Dregg2.Authority (Caps Cap Auth)
-- The verified SUPPLY executors `recKMint`/`recKBurn` (and their single-cell credit `recCreditCell`)
-- live in `Dregg2.Exec.TurnExecutorFull`; §M refines the mint/burn IR terms against them verbatim.
open Dregg2.Exec.TurnExecutorFull (recKMint recKBurn recCreditCell)

/-- The Argus state-transformer IR, effect-body level. Each constructor is a
primitive whose circuit `compile_sound` case is proved **once**; a per-effect
term merely *assembles* primitives (data, farmable). `seq` is the composition
that — at the turn level — subsumes the manual `EffectCommit2/3/4/5` tower. -/
inductive RecStmt where
  | skip
  | guard    (φ : RecordKernelState → Bool)
  | setCell  (T : Finset CellId) (leaf : RecordKernelState → CellId → Value)
  | setBal   (b : RecordKernelState → CellId → AssetId → Int)
  | insFresh (n : RecordKernelState → Nat)
  -- §A — the COMPONENT WRITE-PRIMITIVES (the shapes the 56 effects touch beyond `cell`/`bal`).
  -- Each names one `RecordKernelState` component; its `interp` clause is the record-update that
  -- writes exactly that component (and nothing else). Together with `setCell`/`setBal` these let a
  -- per-effect body be WRITTEN for the whole fullness — the cap graph, every list side-table, and
  -- the scalar/option per-cell registries.
  -- The CAP GRAPH (`caps : Label → List Cap`): grant/revoke/attenuate write here.
  | setCaps        (g : RecordKernelState → Caps)
  -- The LIST side-tables, each `List X` for a distinct payload `X` (heterogeneous element types ⇒
  -- per-component constructors, the type-honest choice — a single generic setter would need a sum
  -- over the payloads, losing each clause's meaning):
  | setNullifiers  (g : RecordKernelState → List Nat)               -- spent-note nullifier SET
  | setRevoked     (g : RecordKernelState → List Nat)               -- revocation registry
  | setCommitments (g : RecordKernelState → List Nat)               -- note-commitment SET
  | setEscrows     (g : RecordKernelState → List EscrowRecord)      -- off-ledger escrow store
  | setQueues      (g : RecordKernelState → List QueueRecord)       -- FIFO queue side-table
  | setSwiss       (g : RecordKernelState → List SwissRecord)       -- CapTP export/GC registry
  | setFactories   (g : RecordKernelState → List (Nat × FactoryEntry))  -- published factory registry
  | setSealedBoxes (g : RecordKernelState → List SealedBoxRecord)   -- sealed-box holding store
  -- The PER-CELL FUNCTION registries (`CellId → …`): lifecycle / death-cert / delegate / per-cell
  -- caveats / per-cell delegation c-list snapshot.
  | setLifecycle   (g : RecordKernelState → CellId → Nat)           -- lifecycle discriminant
  | setDeathCert   (g : RecordKernelState → CellId → Nat)           -- death-certificate binding
  | setDelegate    (g : RecordKernelState → CellId → Option CellId) -- delegation parent pointer
  | setSlotCaveats (g : RecordKernelState → CellId → List SlotCaveat)   -- per-cell slot caveats
  | setDelegations (g : RecordKernelState → CellId → List Cap)      -- per-cell delegated c-list
  -- §B — the LATTICE/COMPARISON gate (a pure DOMAIN-RESTRICTOR, never mutates): commit iff
  -- `a k ≤ b k`. This is the in-band foundation of capability NON-AMPLIFICATION
  -- (`granted.rights ≤ held.rights`): a measured `≤` check, expressed as a guard over two state
  -- read-outs, that rejects (fails closed) when the ordering is violated.
  | checkLe        (a b : RecordKernelState → Int)
  -- §B′ — the FINITE-LATTICE subset gate (the FULL non-amplification primitive). `checkLe` compares
  -- two SCALAR `Int` read-outs with a TOTAL order, which is NECESSARY-but-NOT-SUFFICIENT for the cap
  -- rights order: cap rights live in `ExecAuth = Finset Auth` ordered by `⊆` (`Exec/Caps.lean:57`,
  -- `confRights`), a PARTIAL order where `{read}` and `{write}` are INCOMPARABLE. `checkSubset` is the
  -- domain-restrictor over THAT order: commit iff `a k ≤ b k` (the genuine `⊆` on `Finset Auth`),
  -- mutate nothing. It is the in-band shape of the FULL `granted.rights ⊆ held.rights` gate — it
  -- rejects (fails closed) BOTH a strict superset AND an incomparable pair, the thing `checkLe`'s
  -- cardinality scalar could never express (`checkLe_card_necessary_not_sufficient`).
  | checkSubset    (a b : RecordKernelState → ExecAuth)
  | seq      (s t : RecStmt)

/-- **`interp`** — the executable interpretation, i.e. the reference executor.
Each clause is the worthwhile semantics of its primitive. -/
def interp : RecStmt → RecordKernelState → Option RecordKernelState
  | .skip,           k => some k
  | .guard φ,        k => if φ k then some k else none
  | .setCell T leaf, k => some { k with cell := fun c => if c ∈ T then leaf k c else k.cell c }
  | .setBal b,       k => some { k with bal := b k }
  | .insFresh n,     k => if n k ∈ k.nullifiers then none
                          else some { k with nullifiers := n k :: k.nullifiers }
  -- §A — the component writes: each clause overwrites exactly its one component with `g k`, the
  -- worthwhile semantics of that write (the rest of the state is preserved by record-update).
  | .setCaps g,        k => some { k with caps := g k }
  | .setNullifiers g,  k => some { k with nullifiers := g k }
  | .setRevoked g,     k => some { k with revoked := g k }
  | .setCommitments g, k => some { k with commitments := g k }
  | .setEscrows g,     k => some { k with escrows := g k }
  | .setQueues g,      k => some { k with queues := g k }
  | .setSwiss g,       k => some { k with swiss := g k }
  | .setFactories g,   k => some { k with factories := g k }
  | .setSealedBoxes g, k => some { k with sealedBoxes := g k }
  | .setLifecycle g,   k => some { k with lifecycle := g k }
  | .setDeathCert g,   k => some { k with deathCert := g k }
  | .setDelegate g,    k => some { k with delegate := g k }
  | .setSlotCaveats g, k => some { k with slotCaveats := g k }
  | .setDelegations g, k => some { k with delegations := g k }
  -- §B — the lattice gate: a pure domain-restrictor (returns `k` unchanged on admit, `none` on
  -- reject). The in-band non-amplification check `granted ≤ held`.
  | .checkLe a b,      k => if a k ≤ b k then some k else none
  -- §B′ — the finite-lattice subset gate: the SAME pure-domain-restrictor shape, but over the genuine
  -- `Finset Auth` `⊆` (= `≤`) partial order. Commits (returns `k` unchanged) iff `a k ⊆ b k`; rejects
  -- (`none`) on a strict superset OR an incomparable pair. The FULL in-band non-amplification check.
  | .checkSubset a b,  k => if a k ≤ b k then some k else none
  | .seq s t,        k => (interp s k).bind (interp t)

/-- The transfer admissibility gate as a `Bool` — exactly `recKExec`'s `if`. -/
def transferGuard (turn : Turn) (k : RecordKernelState) : Bool :=
  authorizedB k.caps turn
    && decide (0 ≤ turn.amt)
    && decide (turn.amt ≤ balOf (k.cell turn.src))
    && decide (turn.src ≠ turn.dst)
    && decide (turn.src ∈ k.accounts)
    && decide (turn.dst ∈ k.accounts)

/-- The transfer effect as an IR term: gate, then move the two balances. -/
def transferStmt (turn : Turn) : RecStmt :=
  RecStmt.seq (RecStmt.guard (transferGuard turn))
    (RecStmt.setCell ({turn.src, turn.dst} : Finset CellId)
      (fun k c => recTransfer k.cell turn.src turn.dst turn.amt c))

/-- The `Bool` gate decodes to `recKExec`'s admissibility proposition. -/
theorem transferGuard_iff (turn : Turn) (k : RecordKernelState) :
    transferGuard turn k = true ↔
      (authorizedB k.caps turn = true ∧ 0 ≤ turn.amt
        ∧ turn.amt ≤ balOf (k.cell turn.src) ∧ turn.src ≠ turn.dst
        ∧ turn.src ∈ k.accounts ∧ turn.dst ∈ k.accounts) := by
  simp only [transferGuard, Bool.and_eq_true, decide_eq_true_eq]
  tauto

/-- The `setCell {src,dst}` map is exactly `recTransfer` (identity off the pair). -/
theorem transferCellMap_eq (turn : Turn) (k : RecordKernelState) :
    (fun c => if c ∈ ({turn.src, turn.dst} : Finset CellId)
                then recTransfer k.cell turn.src turn.dst turn.amt c else k.cell c)
      = recTransfer k.cell turn.src turn.dst turn.amt := by
  funext c
  unfold recTransfer
  by_cases h1 : c = turn.src
  · simp [h1]
  · by_cases h2 : c = turn.dst
    · simp [h2]
    · simp [Finset.mem_insert, Finset.mem_singleton, h1, h2]

/-- **The cornerstone.** `interp` of the transfer term IS the verified
executor `recKExec` — the same partial function, by construction. -/
theorem interp_transferStmt_eq_recKExec (turn : Turn) (k : RecordKernelState) :
    interp (transferStmt turn) k = recKExec k turn := by
  simp only [transferStmt, interp]
  unfold recKExec
  by_cases hg : transferGuard turn k = true
  · rw [if_pos hg]
    simp only [Option.bind, transferCellMap_eq]
    rw [if_pos ((transferGuard_iff turn k).mp hg)]
  · rw [if_neg hg]
    simp only [Option.bind]
    rw [if_neg (fun hp => hg ((transferGuard_iff turn k).mpr hp))]

#assert_axioms interp_transferStmt_eq_recKExec

/-! ## §M — THE PATTERN GENERALIZES: mint and burn as IR terms.

The cornerstone above is proven for ONE effect (transfer). The bet is that the executor-refinement
pattern is NOT transfer-special: any per-effect term assembled from the primitives has the executor
as its `interp` meaning. We validate that here for TWO more effects — `mint` and `burn` — reusing
the verified supply executors `recKMint`/`recKBurn` (`Exec/TurnExecutorFull.lean`) verbatim.

The shape is IDENTICAL to `transferStmt`: a `Bool` admissibility `guard`, then a `setCell` move on
the affected cell(s). Mint/burn touch ONE cell's `balance` field (`recCreditCell`), so the move is a
`setCell {cell}` — the SAME `setCell` primitive `transferStmt` uses (no new write-primitive needed).
That the move is `recCreditCell` is the single-cell analog of `transferCellMap_eq`. -/

/-- The mint admissibility gate as a `Bool` — exactly `recKMint`'s `if` (the privileged supply gate:
a `node`/`control` cap over `cell`, non-negative amount, live account). -/
def mintGuard (actor cell : CellId) (amt : Int) (k : RecordKernelState) : Bool :=
  mintAuthorizedB k.caps actor cell
    && decide (0 ≤ amt)
    && decide (cell ∈ k.accounts)

/-- The burn admissibility gate as a `Bool` — exactly `recKBurn`'s `if` (the supply gate PLUS
availability of `amt` in `cell`'s `balance` field). -/
def burnGuard (actor cell : CellId) (amt : Int) (k : RecordKernelState) : Bool :=
  mintAuthorizedB k.caps actor cell
    && decide (0 ≤ amt)
    && decide (amt ≤ balOf (k.cell cell))
    && decide (cell ∈ k.accounts)

/-- The mint effect as an IR term: gate, then CREDIT `cell`'s `balance` by `amt` (a single-cell
`setCell`). Mirrors `transferStmt` — gate, then move. -/
def mintStmt (actor cell : CellId) (amt : Int) : RecStmt :=
  RecStmt.seq (RecStmt.guard (mintGuard actor cell amt))
    (RecStmt.setCell ({cell} : Finset CellId)
      (fun k c => setBalance (k.cell c) (balOf (k.cell c) + amt)))

/-- The burn effect as an IR term: gate, then DEBIT `cell`'s `balance` by `amt` (credit `-amt`). The
post-cell move is `recCreditCell k.cell cell (-amt)`, exactly `recKBurn`'s. -/
def burnStmt (actor cell : CellId) (amt : Int) : RecStmt :=
  RecStmt.seq (RecStmt.guard (burnGuard actor cell amt))
    (RecStmt.setCell ({cell} : Finset CellId)
      (fun k c => setBalance (k.cell c) (balOf (k.cell c) + (-amt))))

/-- The mint `Bool` gate decodes to `recKMint`'s admissibility proposition. -/
theorem mintGuard_iff (actor cell : CellId) (amt : Int) (k : RecordKernelState) :
    mintGuard actor cell amt k = true ↔
      (mintAuthorizedB k.caps actor cell = true ∧ 0 ≤ amt ∧ cell ∈ k.accounts) := by
  simp only [mintGuard, Bool.and_eq_true, decide_eq_true_eq]
  tauto

/-- The burn `Bool` gate decodes to `recKBurn`'s admissibility proposition. -/
theorem burnGuard_iff (actor cell : CellId) (amt : Int) (k : RecordKernelState) :
    burnGuard actor cell amt k = true ↔
      (mintAuthorizedB k.caps actor cell = true ∧ 0 ≤ amt
        ∧ amt ≤ balOf (k.cell cell) ∧ cell ∈ k.accounts) := by
  simp only [burnGuard, Bool.and_eq_true, decide_eq_true_eq]
  tauto

/-- The `setCell {cell}` credit map is exactly `recCreditCell` (identity off the single cell) — the
single-cell analog of `transferCellMap_eq`. -/
theorem creditCellMap_eq (cell : CellId) (amt : Int) (k : RecordKernelState) :
    (fun c => if c ∈ ({cell} : Finset CellId)
                then setBalance (k.cell c) (balOf (k.cell c) + amt) else k.cell c)
      = recCreditCell k.cell cell amt := by
  funext c
  unfold recCreditCell
  by_cases h : c = cell
  · simp [h]
  · simp [Finset.mem_singleton, h]

/-- **The pattern generalizes (mint).** `interp` of the mint term IS the verified supply executor
`recKMint` — the same partial function, by construction, exactly as the transfer cornerstone. -/
theorem interp_mintStmt_eq_recKMint (actor cell : CellId) (amt : Int) (k : RecordKernelState) :
    interp (mintStmt actor cell amt) k = recKMint k actor cell amt := by
  simp only [mintStmt, interp]
  unfold recKMint
  by_cases hg : mintGuard actor cell amt k = true
  · rw [if_pos hg]
    simp only [Option.bind, creditCellMap_eq]
    rw [if_pos ((mintGuard_iff actor cell amt k).mp hg)]
  · rw [if_neg hg]
    simp only [Option.bind]
    rw [if_neg (fun hp => hg ((mintGuard_iff actor cell amt k).mpr hp))]

/-- **The pattern generalizes (burn).** `interp` of the burn term IS the verified supply executor
`recKBurn` — the same partial function, by construction. -/
theorem interp_burnStmt_eq_recKBurn (actor cell : CellId) (amt : Int) (k : RecordKernelState) :
    interp (burnStmt actor cell amt) k = recKBurn k actor cell amt := by
  simp only [burnStmt, interp]
  unfold recKBurn
  by_cases hg : burnGuard actor cell amt k = true
  · rw [if_pos hg]
    simp only [Option.bind, creditCellMap_eq]
    rw [if_pos ((burnGuard_iff actor cell amt k).mp hg)]
  · rw [if_neg hg]
    simp only [Option.bind]
    rw [if_neg (fun hp => hg ((burnGuard_iff actor cell amt k).mpr hp))]

#assert_axioms interp_mintStmt_eq_recKMint
#assert_axioms interp_burnStmt_eq_recKBurn

/-! ## §L — the lattice gate `checkLe` is a pure DOMAIN-RESTRICTOR (the non-amplification foundation).

`checkLe a b` commits IFF `a k ≤ b k`, leaving `k` UNCHANGED on admit. This is the in-band shape of
the capability non-amplification rule (`granted.rights ≤ held.rights`): a measured `≤` over two state
read-outs that fails closed when the order is violated, and — crucially — mutates nothing, so it
composes before any effect body exactly like `guard` (every executor keystone of the body lifts
through it for free). We pin its meaning + the never-mutates law. -/

/-- **`interp_checkLe` — PROVED.** `checkLe` commits iff `a k ≤ b k` and returns `k` unchanged on
admit; the foundation of the in-band `granted ≤ held` non-amplification gate. -/
@[simp] theorem interp_checkLe (a b : RecordKernelState → Int) (k : RecordKernelState) :
    interp (RecStmt.checkLe a b) k = if a k ≤ b k then some k else none := rfl

/-- **`checkLe_commit_unchanged` — PROVED (never mutates).** When `checkLe` commits, the post-state
IS the input — a pure domain restrictor (the `granted ≤ held` gate adds an admission side-condition
and changes nothing). -/
theorem checkLe_commit_unchanged {a b : RecordKernelState → Int} {k k' : RecordKernelState}
    (h : interp (RecStmt.checkLe a b) k = some k') : k' = k := by
  rw [interp_checkLe] at h
  by_cases hle : a k ≤ b k
  · rw [if_pos hle] at h; exact (Option.some.injEq _ _ ▸ h).symm
  · rw [if_neg hle] at h; exact absurd h (by simp)

/-- **`checkLe_admits_iff` — PROVED.** `checkLe` admits (is `some`) IFF the order holds — so it
genuinely REJECTS (fails closed) when `b k < a k` (amplification): non-vacuous, two-valued. -/
theorem checkLe_admits_iff (a b : RecordKernelState → Int) (k : RecordKernelState) :
    (interp (RecStmt.checkLe a b) k).isSome = true ↔ a k ≤ b k := by
  rw [interp_checkLe]
  by_cases hle : a k ≤ b k <;> simp [hle]

#assert_axioms interp_checkLe
#assert_axioms checkLe_commit_unchanged
#assert_axioms checkLe_admits_iff

/-! ## §L′ — the FINITE-LATTICE subset gate `checkSubset` is the FULL non-amplification primitive.

`checkLe` (§L) restricts on a TOTAL order over `Int` scalars, which — for the capability rights order —
is only the cardinality SHADOW: `granted ⊆ held ⟹ |granted| ≤ |held|`, but `|granted| ≤ |held|` does
NOT recover `granted ⊆ held` (two equal-cardinality rights sets can be incomparable, e.g. `{read}` vs
`{write}`). The genuine non-amplification carrier is `ExecAuth = Finset Auth` (`Exec/Caps.lean:57`,
`confRights`), ordered by `⊆` (= `≤`), a PARTIAL order. `checkSubset a b` is the domain-restrictor over
THAT order: it commits IFF `a k ≤ b k` (the genuine `Finset Auth` `⊆`), leaving `k` UNCHANGED on admit
exactly like `checkLe`/`guard` (mutates nothing — composes before any effect body for free), and — the
load-bearing gain — it REJECTS (fails closed) BOTH a strict superset AND an INCOMPARABLE pair. This is
the in-band shape of the FULL `granted.rights ⊆ held.rights` gate, the thing `checkLe` could never
express (`checkLe_card_necessary_not_sufficient` in the attenuate weld). The `Finset Auth` order is
decidable (`Auth` has `DecidableEq`), so the `if a k ≤ b k` is a genuine computable domain restriction. -/

/-- **`interp_checkSubset` — PROVED.** `checkSubset` commits iff `a k ≤ b k` over the genuine
`ExecAuth = Finset Auth` `⊆` order and returns `k` unchanged on admit; the in-band FULL
`granted.rights ⊆ held.rights` non-amplification gate (not the cardinality shadow `checkLe` carries). -/
@[simp] theorem interp_checkSubset (a b : RecordKernelState → ExecAuth) (k : RecordKernelState) :
    interp (RecStmt.checkSubset a b) k = if a k ≤ b k then some k else none := rfl

/-- **`checkSubset_commit_unchanged` — PROVED (never mutates).** When `checkSubset` commits, the
post-state IS the input — a pure domain restrictor, exactly like `checkLe` (the full subset gate adds an
admission side-condition over the rights lattice and changes nothing), so every executor keystone of the
gated body lifts through it for free. -/
theorem checkSubset_commit_unchanged {a b : RecordKernelState → ExecAuth} {k k' : RecordKernelState}
    (h : interp (RecStmt.checkSubset a b) k = some k') : k' = k := by
  rw [interp_checkSubset] at h
  by_cases hle : a k ≤ b k
  · rw [if_pos hle] at h; exact (Option.some.injEq _ _ ▸ h).symm
  · rw [if_neg hle] at h; exact absurd h (by simp)

/-- **`checkSubset_admits_iff` — PROVED.** `checkSubset` admits (is `some`) IFF the genuine subset order
holds — so it REJECTS (fails closed) on `¬ (a k ⊆ b k)`, which covers BOTH a strict superset AND an
incomparable pair (the partial-order reject the scalar `checkLe` cannot make): non-vacuous, two-valued. -/
theorem checkSubset_admits_iff (a b : RecordKernelState → ExecAuth) (k : RecordKernelState) :
    (interp (RecStmt.checkSubset a b) k).isSome = true ↔ a k ≤ b k := by
  rw [interp_checkSubset]
  by_cases hle : a k ≤ b k <;> simp [hle]

/-- A two-cell kernel for the §L′ non-vacuity witnesses (cell `0` Live; the rights read-outs below are
CONSTANT functions of `k`, so the base state only has to exist). -/
def kSub : RecordKernelState :=
  { accounts := {0, 1}, cell := fun _ => .record [("balance", .int 0)], caps := fun _ => [] }

-- `checkSubset` is GENUINELY a partial-order decider, three-way non-vacuous on CONSTANT rights read-outs:
-- ADMITS a real subset ({read} ⊆ {read,write}); REJECTS a strict superset ({read,write} ⊄ {read});
-- and — the thing `checkLe` could NEVER do — REJECTS an INCOMPARABLE pair ({read} vs {write}).
#guard ((interp (RecStmt.checkSubset (fun _ => ({Auth.read} : Finset Auth))
                  (fun _ => ({Auth.read, Auth.write} : Finset Auth))) kSub).isSome)             -- admit ⊆
#guard ((interp (RecStmt.checkSubset (fun _ => ({Auth.read, Auth.write} : Finset Auth))
                  (fun _ => ({Auth.read} : Finset Auth))) kSub).isNone)                          -- reject ⊋
#guard ((interp (RecStmt.checkSubset (fun _ => ({Auth.read} : Finset Auth))
                  (fun _ => ({Auth.write} : Finset Auth))) kSub).isNone)                         -- reject ∥

/-- **`checkSubset_decides_partial_order` — PROVED (the primitive captures the PARTIAL order faithfully).**
`checkSubset` admits a genuine subset, rejects a strict superset, AND — the load-bearing case `checkLe`'s
total `Int ≤` could never express — REJECTS an INCOMPARABLE pair (`{read}` vs `{write}`, neither ⊆ the
other). So the gate decides exactly `granted.rights ⊆ held.rights` over `Finset Auth`, the full
non-amplification order, not a scalar shadow of it. -/
theorem checkSubset_decides_partial_order :
    -- ADMITS a genuine subset …
    (interp (RecStmt.checkSubset (fun _ => ({Auth.read} : Finset Auth))
              (fun _ => ({Auth.read, Auth.write} : Finset Auth))) kSub).isSome = true
    -- … REJECTS a strict superset …
    ∧ (interp (RecStmt.checkSubset (fun _ => ({Auth.read, Auth.write} : Finset Auth))
                (fun _ => ({Auth.read} : Finset Auth))) kSub) = none
    -- … and REJECTS an INCOMPARABLE pair (the partial-order tooth `checkLe` cannot make), BOTH ways.
    ∧ (interp (RecStmt.checkSubset (fun _ => ({Auth.read} : Finset Auth))
                (fun _ => ({Auth.write} : Finset Auth))) kSub) = none
    ∧ (interp (RecStmt.checkSubset (fun _ => ({Auth.write} : Finset Auth))
                (fun _ => ({Auth.read} : Finset Auth))) kSub) = none := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> (rw [interp_checkSubset]) <;> decide

#assert_axioms interp_checkSubset
#assert_axioms checkSubset_commit_unchanged
#assert_axioms checkSubset_admits_iff
#assert_axioms checkSubset_decides_partial_order

/-! ## §C — the component writes do exactly what they say (frame + non-vacuity).

Each `set<Component>` clause writes precisely its one component to `g k` and is a genuine state
edit — `interp` always commits (`some`), the named component becomes `g k`, and a witnessing
instance shows the write is observable (not a no-op). We pin the two cap-graph / one
per-cell-lifecycle representatives + a list-table representative; the rest are definitionally the
same `{ k with <field> := g k }` shape (`interp` reduces by `rfl`). -/

/-- **`interp_setCaps` — PROVED.** Writing the cap graph overwrites `caps` with `g k` and touches
nothing else; the write the grant/revoke/attenuate effects assemble. -/
@[simp] theorem interp_setCaps (g : RecordKernelState → Caps) (k : RecordKernelState) :
    interp (RecStmt.setCaps g) k = some { k with caps := g k } := rfl

/-- **`interp_setLifecycle` — PROVED.** Writing the lifecycle registry overwrites `lifecycle` with
`g k` (the Live/Sealed/Destroyed transition write). -/
@[simp] theorem interp_setLifecycle (g : RecordKernelState → CellId → Nat) (k : RecordKernelState) :
    interp (RecStmt.setLifecycle g) k = some { k with lifecycle := g k } := rfl

/-- **`interp_setSwiss` — PROVED.** Writing the CapTP swiss-table overwrites `swiss` with `g k` (the
export/enliven/handoff/GC registry write). -/
@[simp] theorem interp_setSwiss (g : RecordKernelState → List SwissRecord) (k : RecordKernelState) :
    interp (RecStmt.setSwiss g) k = some { k with swiss := g k } := rfl

/-- A two-cell kernel for the §C non-vacuity witnesses (cell `0` Live, both live accounts). -/
def kC : RecordKernelState :=
  { accounts := {0, 1}, cell := fun _ => .record [("balance", .int 0)], caps := fun _ => [] }

-- The component writes are OBSERVABLE state edits, not no-ops:
-- setLifecycle to "everything Sealed (1)" genuinely changes cell 0's lifecycle 0 → 1.
#guard (((interp (RecStmt.setLifecycle (fun _ _ => 1)) kC).map (fun k => k.lifecycle 0)) == some 1)
#guard (kC.lifecycle 0 == 0)   -- before: Live
-- setSwiss to a one-entry registry grows the swiss-table from [] to length 1.
#guard (((interp (RecStmt.setSwiss (fun _ => [⟨7, 0, 0, [], 1, none⟩])) kC).map (fun k => k.swiss.length)) == some 1)
#guard (kC.swiss.length == 0)  -- before: empty

/-- **`setLifecycle_writes` — PROVED (the write lands, non-vacuously).** Sealing every cell flips
cell `0`'s lifecycle from Live (`0`) to Sealed (`1`): the component write is a real, observable
state edit (`interp` commits and the post-component is `g k`). -/
theorem setLifecycle_writes :
    (interp (RecStmt.setLifecycle (fun _ _ => 1)) kC).map (fun k => k.lifecycle 0) = some 1 := by
  rw [interp_setLifecycle]; rfl

/-- **`setCaps_writes` — PROVED.** Granting cell `0` a `node 1` cap lands in the cap graph: after the
write, cell `0` holds exactly `[Cap.node 1]`, where before it held none. The cap-graph component
write is observable (not a no-op) — the in-band shape grant/attenuate effects emit. -/
theorem setCaps_writes :
    (interp (RecStmt.setCaps (fun k => fun l => if l = 0 then [Cap.node 1] else k.caps l)) kC).map
        (fun k => k.caps 0) = some [Cap.node 1] := by
  rw [interp_setCaps]; rfl

#assert_axioms interp_setCaps
#assert_axioms interp_setLifecycle
#assert_axioms interp_setSwiss
#assert_axioms setLifecycle_writes
#assert_axioms setCaps_writes

/-! ## §E — THE SIDE-TABLE EFFECT: createEscrow as an IR term (TWO components + a list side-table).

The §M generalization (mint/burn) re-validated the refinement pattern, but every effect so far —
transfer, mint, burn — is SINGLE-COMPONENT: the body is one `setCell`/`setBal` move on the per-cell
state. `createEscrow` is the genuinely DIFFERENT shape, and the de-risk that matters before the
per-effect farm: the kernel step `createEscrowKAsset` (`RecordKernel.lean:1550`) touches **two**
`RecordKernelState` components at once —

  * it DEBITS the per-asset ledger `bal` at `(creator, asset)` by `amount`
    (`bal := recBalCreditCell k.bal creator asset (-amount)`), AND
  * it PREPENDS an unresolved `EscrowRecord` onto the `escrows` list side-table
    (`escrows := ⟨id, creator, recipient, amount, false, asset⟩ :: k.escrows`),

after a five-conjunct admissibility gate (authority · non-negativity · per-asset availability ·
creator-liveness · id-freshness). This is exactly the shape the §A component-write primitives were
built for: `setBal` writes the ledger, `setEscrows` writes the list. The term is therefore a
`seq (guard …) (seq (setBal …) (setEscrows …))` — gate, then the two component writes in sequence —
and the cornerstone is that `interp` of THIS term IS the verified kernel step `createEscrowKAsset`.

The refinement is the same two ingredients as transfer/mint/burn — a guard-decode lemma and the
component-map equalities — but the component leg is now TWO writes chained through `seq`. The
load-bearing fact the side-table shape exercises (and the single-cell effects never did): the second
write (`setEscrows`) reads its `g k₁` on the INTERMEDIATE state `k₁` produced by the first write
(`setBal`), and because `setBal` does not touch `escrows`, `k₁.escrows = k.escrows`, so the prepend
lands on the ORIGINAL list — matching `createEscrowRawAsset` exactly. -/

/-- The escrow-create admissibility gate as a `Bool` — exactly `createEscrowKAsset`'s `if` (the five
conjuncts: authority over the create-turn `actor: creator ⇒ recipient`, non-negative amount, the
amount available *in asset `asset`* on the per-asset ledger, the creator a live account, and the `id`
not already parked). -/
def createEscrowGuard (id : Nat) (actor creator recipient : CellId) (asset : AssetId) (amount : Int)
    (k : RecordKernelState) : Bool :=
  authorizedB k.caps { actor := actor, src := creator, dst := recipient, amt := amount }
    && decide (0 ≤ amount)
    && decide (amount ≤ k.bal creator asset)
    && decide (creator ∈ k.accounts)
    && decide (¬ (∃ r ∈ k.escrows, r.id = id))

/-- The unresolved `EscrowRecord` a create parks — the SAME literal `createEscrowRawAsset` installs
(`RecordKernel.lean:1525`). Stated here so the term's `setEscrows` leaf is the genuine parked record. -/
def escrowParked (id : Nat) (creator recipient : CellId) (asset : AssetId) (amount : Int) :
    EscrowRecord :=
  { id := id, creator := creator, recipient := recipient,
    amount := amount, resolved := false, asset := asset }

/-- **The createEscrow effect as an IR term: gate, then the TWO component writes.** Unlike
transfer/mint/burn (one move), the body is `seq (setBal <debit>) (setEscrows <prepend>)`: debit the
per-asset ledger at `(creator, asset)`, then prepend the unresolved record onto `escrows`. The two
component-write primitives `setBal`/`setEscrows` (§A) are exactly the shapes a multi-component effect
assembles — no new constructor needed. -/
def createEscrowStmt (id : Nat) (actor creator recipient : CellId) (asset : AssetId) (amount : Int) :
    RecStmt :=
  RecStmt.seq (RecStmt.guard (createEscrowGuard id actor creator recipient asset amount))
    (RecStmt.seq
      (RecStmt.setBal (fun k => recBalCreditCell k.bal creator asset (-amount)))
      (RecStmt.setEscrows (fun k => escrowParked id creator recipient asset amount :: k.escrows)))

/-- The escrow-create `Bool` gate decodes to `createEscrowKAsset`'s admissibility proposition (the five
conjuncts, in the SAME order the kernel `if` checks them). -/
theorem createEscrowGuard_iff (id : Nat) (actor creator recipient : CellId) (asset : AssetId)
    (amount : Int) (k : RecordKernelState) :
    createEscrowGuard id actor creator recipient asset amount k = true ↔
      (authorizedB k.caps { actor := actor, src := creator, dst := recipient, amt := amount } = true
        ∧ 0 ≤ amount ∧ amount ≤ k.bal creator asset ∧ creator ∈ k.accounts
        ∧ ¬ (∃ r ∈ k.escrows, r.id = id)) := by
  simp only [createEscrowGuard, Bool.and_eq_true, decide_eq_true_eq]
  tauto

/-- **The two-component move IS `createEscrowRawAsset`.** Running the body `seq (setBal …)
(setEscrows …)` on a state `k` produces exactly `createEscrowRawAsset k id creator recipient asset
amount` — the kernel's commit post-state. This is the SIDE-TABLE analog of `transferCellMap_eq` /
`creditCellMap_eq`, and the load-bearing step the single-cell effects never had: the `setEscrows`
prepend reads the intermediate state (post-`setBal`), whose `escrows` is still `k.escrows` (because
`setBal` writes only `bal`), so the record lands on the original list. -/
theorem createEscrowBody_eq (id : Nat) (creator recipient : CellId) (asset : AssetId) (amount : Int)
    (k : RecordKernelState) :
    interp (RecStmt.seq
        (RecStmt.setBal (fun k => recBalCreditCell k.bal creator asset (-amount)))
        (RecStmt.setEscrows (fun k => escrowParked id creator recipient asset amount :: k.escrows))) k
      = some (createEscrowRawAsset k id creator recipient asset amount) := by
  simp only [interp, Option.bind, escrowParked, createEscrowRawAsset]

/-- **The cornerstone (side-table).** `interp` of the createEscrow term IS the verified kernel step
`createEscrowKAsset` — the same partial function, by construction, exactly as the transfer/mint/burn
cornerstones, now over a TWO-component side-table effect. -/
theorem interp_createEscrowStmt_eq_createEscrowKAsset (id : Nat) (actor creator recipient : CellId)
    (asset : AssetId) (amount : Int) (k : RecordKernelState) :
    interp (createEscrowStmt id actor creator recipient asset amount) k
      = createEscrowKAsset k id actor creator recipient asset amount := by
  simp only [createEscrowStmt, interp]
  unfold createEscrowKAsset
  by_cases hg : createEscrowGuard id actor creator recipient asset amount k = true
  · -- ADMIT: the guard's `interp` fires (`some k`), the two-component body reduces (the `setBal` debit
    -- then the `setEscrows` prepend — whose `escrows` read is still `k.escrows`), giving exactly
    -- `createEscrowRawAsset`; the RHS `if` opens on the decoded 5-conjunct Prop.
    rw [if_pos hg, if_pos ((createEscrowGuard_iff id actor creator recipient asset amount k).mp hg)]
    simp only [Option.bind, escrowParked, createEscrowRawAsset]
  · -- REJECT: the guard fails ⇒ `none.bind _ = none`; the RHS `if` closes on the (negated) decoded Prop.
    rw [if_neg hg,
      if_neg (fun hp => hg ((createEscrowGuard_iff id actor creator recipient asset amount k).mpr hp))]
    simp only [Option.bind]

#assert_axioms interp_createEscrowStmt_eq_createEscrowKAsset

/-- **Non-vacuity (the side-table write is OBSERVABLE).** Running the createEscrow term on the §C
two-cell kernel (cell `0` Live, an empty `escrows`) with a `0`-amount lock of a fresh id grows the
`escrows` store from `[]` to length `1` — the two-component move genuinely touches the list side-table
(the prepend is real, not a no-op). The `0` amount keeps the gate's availability/non-negativity legs
trivially satisfied so the commit fires. -/
theorem createEscrowStmt_parks :
    (interp (createEscrowStmt 7 0 0 1 0 0) kC).map (fun k => k.escrows.length) = some 1 := by
  rw [interp_createEscrowStmt_eq_createEscrowKAsset]
  decide

#assert_axioms createEscrowStmt_parks

end Dregg2.Circuit.Argus
