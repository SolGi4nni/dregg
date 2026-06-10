/-
# Dregg2.Circuit.Argus.Effects.CreateCell — `CreateCell` welded into the Argus IR.

## THE STRUCTURAL-ALLOC PRIMITIVE: `allocCell`.

Every other `RecStmt` constructor FREEZES the `accounts : Finset CellId` index set, while `CreateCell`
STRICTLY GROWS it (`createCellIntoAsset` inserts the fresh id) — so capturing `createCellChainA`
requires a dedicated structural-alloc primitive. That primitive is `RecStmt.allocCell
(n : RecordKernelState → CellId)` (`Argus/Stmt.lean`), whose `interp` clause produces EXACTLY the
verified kernel allocator `createCellIntoAsset k (n k)` (grow `accounts := insert (n k) accounts` +
reset every born-empty per-cell slot at `n k`). It is the ONE `interp` clause that changes `accounts`,
and it is unconditional (the freshness + privileged-creation gate rides a preceding `guard`, the same
`seq (guard …) (move)` shape every other effect term uses).

## THE EXECUTOR (what the faithful term captures EXACTLY)

`createCellChainA` (`Exec/TurnExecutorFull.lean:798`):

    createCellChainA s actor newCell
      = if mintAuthorizedB s.kernel.caps actor newCell = true ∧ newCell ∉ s.kernel.accounts then
          some { kernel := createCellIntoAsset s.kernel newCell
                 log    := { actor := actor, src := newCell, dst := newCell, amt := 0 } :: s.log }
        else none

and `createCellIntoAsset` (`Exec/RecordKernel.lean:880`) does the TWO structural things `allocCell`
encapsulates: (A) **GROW `accounts`** by the fresh id, and (B) **reset born-empty per-cell slots** at
that id. `createCellStmt` is `seq (guard <gate>) (allocCell (fun _ => newCell))`: the gate is exactly
`createCellChainA`'s `if` (privileged creation authority ∧ freshness), then the structural allocation.

## WHAT THIS MODULE PROVES (mirroring `Effects/BalanceA.lean` — the full-state-weld template)

  1. `interp_createCellStmt_eq_createCellK` — THE CORNERSTONE (executor-refinement): `interp` of the
     createCell term IS the raw-kernel allocator (gate, then `createCellIntoAsset`) — possible
     exactly because `allocCell` grows `accounts`.
  2. `interp_createCellStmt_chained` — the cornerstone lifted to the chained `execFullA`/`createCellChainA`
     (clean — the `createCellA` arm has no extra dst-liveness gate, unlike balanceA).
  3. `createCell_compile_sound` — THE COMPILE WELD against `createCellA`'s OWN full-state v2 `Surface2`
     TRIPLE descriptor (`createCellE` / `createCellA_full_sound`, `Inst/createCellA.lean`): a satisfying
     witness of the circuit AGREES with the WHOLE post-state the IR term's executor produces — the full
     `CreateCellSpec` (all 18 components: `accounts` grown, `bal`/born-empty slots reset, `log` extended,
     every global side-table frozen). Honest full-state surface, DIRECTLY against the term.
  4. Non-vacuity teeth: a concrete create grows `accounts` (fresh id absent BEFORE, present
     AFTER); the gate REJECTS an unauthorized creation and a re-mint of a live id (fail-closed).

## Axiom hygiene

`#assert_axioms` on every headline theorem ⊆ {propext, Classical.choice, Quot.sound}; the whole-function
/ Poseidon-CR digest assumptions enter ONLY inside the reused `createCellA_full_sound` (its injectivity
hypotheses), never in the welded conclusion's statement. No `sorry`, no `:= True`, no `native_decide`.
Imports are read-only (`Argus/Stmt` for the IR + `Inst/createCellA` for the audited triple descriptor +
`Spec/accountgrowth` for the executor⟺spec corner); this file owns only its own declarations.
-/
import Dregg2.Circuit.Argus.Stmt
import Dregg2.Circuit.Inst.createCellA
import Dregg2.Circuit.Spec.accountgrowth
import Dregg2.Circuit.Emit.EffectVmEmitCreateCellFullState

namespace Dregg2.Circuit.Argus.Effects.CreateCell

open Dregg2.Exec
open Dregg2.Exec.TurnExecutorFull
open Dregg2.Circuit.Argus (RecStmt interp)
-- Broad opens mirroring `Inst/createCellA.lean` so the standalone-descriptor names resolve unqualified.
open Dregg2.Circuit.StateCommit (logHashInjective compressNInjective)
open Dregg2.Circuit.ListCommit (listLeafInjective)
open Dregg2.Circuit.EffectCommit2 (Surface2)
open Dregg2.Circuit.EffectCommit3 (satisfiedE2Triple encodeE2Triple)
open Dregg2.Circuit.BornEmptyCommit (BornEmptySideTables)
open Dregg2.Circuit.Spec.AccountGrowth
  (createCellAdmit CreateCellSpec createReceipt execCreateCellA_iff_spec)
open Dregg2.Circuit.Inst.CreateCellA
  (CreateCellArgs createCellE createCellA_full_sound RestIffNoAccountsBalBorn)

/-! ## §1 — The createCell effect as an Argus IR term (gate, then the `allocCell` structural allocation).

`createCellChainA` is `if <2-conjunct gate> then some { kernel := createCellIntoAsset … , log := … }
else none`. We capture its KERNEL action term-for-term: a `Bool` `guard` of the EXACT gate (privileged
creation authority ∧ freshness), then `allocCell (fun _ => newCell)` — the structural allocator whose
`interp` IS `createCellIntoAsset k newCell`. The contrast with transfer/balanceA is the move primitive:
NOT `setCell`/`setBal` (which freeze `accounts`), but `allocCell` (the ONLY primitive that grows it). -/

/-- The createCell admissibility gate as a `Bool` — exactly `createCellChainA`'s `if` (privileged
creation authority `mintAuthorizedB` over the fresh id ∧ the freshness conjunct `newCell ∉ accounts`).
This decodes to `createCellAdmit`. -/
def createCellGuard (actor newCell : CellId) (k : RecordKernelState) : Bool :=
  mintAuthorizedB k.caps actor newCell
    && decide (newCell ∉ k.accounts)

/-- `createCellAdmit` is a conjunction of two decidable propositions (a `Bool = true` and a `Finset`
non-membership), so the `if` in the cornerstone has a decision procedure. -/
instance (k : RecordKernelState) (actor newCell : CellId) :
    Decidable (createCellAdmit k actor newCell) := by
  unfold createCellAdmit; exact inferInstanceAs (Decidable (_ ∧ _))

/-- **The createCell effect as an IR term: gate, then the structural allocation.** Mirrors
`transferStmt`/`balanceAStmt` (gate, then move) but the move is the §A′ allocator `allocCell (fun _ =>
newCell)` — `interp`-equal to `createCellIntoAsset k newCell`, the genuine account-grow + born-empty
reset `createCellChainA` installs. The fresh id is a constant function `fun _ => newCell` (the id is
chosen by the caller, exactly as the executor takes `newCell` as a parameter). -/
def createCellStmt (actor newCell : CellId) : RecStmt :=
  RecStmt.seq (RecStmt.guard (createCellGuard actor newCell))
    (RecStmt.allocCell (fun _ => newCell))

/-! ## §2 — the cornerstone: `interp` of the createCell term IS the raw-kernel allocator. -/

/-- The createCell `Bool` gate decodes to `createCellAdmit` (the two conjuncts, in the SAME order the
kernel `if` checks them). The createCell analog of `transferGuard_iff`. -/
theorem createCellGuard_iff (actor newCell : CellId) (k : RecordKernelState) :
    createCellGuard actor newCell k = true ↔ createCellAdmit k actor newCell := by
  simp only [createCellGuard, createCellAdmit, Bool.and_eq_true, decide_eq_true_eq]

/-- **The cornerstone (structural allocation).** `interp` of the createCell term IS the raw-kernel
allocator: it commits to `createCellIntoAsset k newCell` exactly when the gate (`createCellAdmit`)
holds, and rejects otherwise — the same partial function `createCellChainA` runs on the kernel, by
construction. The §A′ allocator's `interp` (`some (createCellIntoAsset k
(n k))`) is what makes the post `accounts` STRICTLY GROW — the change no frozen-`accounts`
constructor can produce. -/
theorem interp_createCellStmt_eq_createCellK (actor newCell : CellId) (k : RecordKernelState) :
    interp (createCellStmt actor newCell) k
      = if createCellAdmit k actor newCell then some (createCellIntoAsset k newCell) else none := by
  simp only [createCellStmt, interp]
  by_cases hg : createCellGuard actor newCell k = true
  · -- ADMIT: the guard fires (`some k`), the `allocCell` clause installs `createCellIntoAsset k newCell`.
    rw [if_pos hg]
    simp only [Option.bind]
    rw [if_pos ((createCellGuard_iff actor newCell k).mp hg)]
  · -- REJECT: the guard fails ⇒ `none.bind _ = none`; the RHS `if` closes on the (negated) decoded gate.
    rw [if_neg hg]
    simp only [Option.bind]
    rw [if_neg (fun hp => hg ((createCellGuard_iff actor newCell k).mpr hp))]

#assert_axioms interp_createCellStmt_eq_createCellK

/-! ## §3 — Lifting the cornerstone to the CHAINED executor `createCellChainA` / `execFullA`.

The standalone createCell descriptor (§4) is keyed on the CHAINED executor `execFullA` / `createCellChainA`
over `RecChainedState` (kernel + receipt log). The §2 cornerstone is over the raw kernel allocation. Unlike
balanceA, the `createCellA` arm is CLEAN — `execFullA st (.createCellA …) = createCellChainA st …` (no extra
`acceptsEffects` dst-liveness gate). The chained layer is exactly the raw allocation PLUS the receipt-log
prepend, so the lift is an unconditional both-directions bridge. -/

/-- **`interp_createCellStmt_chained` — the IR term's executor, lifted to the chained `execFullA`
(both directions).** The unified action executor commits a `createCellA` turn into `st'` IFF the IR
term's `interp` commits on the kernel to `st'.kernel` AND `st'.log` is the creation receipt prepended.
So the Argus term's kernel meaning IS the chained executor the standalone descriptor speaks about (the
receipt-log update is the only chained-vs-raw delta — carried explicitly, not papered). -/
theorem interp_createCellStmt_chained (st : RecChainedState) (actor newCell : CellId)
    (st' : RecChainedState) :
    execFullA st (.createCellA actor newCell) = some st'
      ↔ interp (createCellStmt actor newCell) st.kernel = some st'.kernel
        ∧ st'.log = createReceipt actor newCell :: st.log := by
  -- `execFullA st (.createCellA …)` reduces to `createCellChainA st actor newCell` (the clean arm).
  show createCellChainA st actor newCell = some st' ↔ _
  rw [interp_createCellStmt_eq_createCellK]
  unfold createCellChainA createReceipt
  by_cases hg : createCellAdmit st.kernel actor newCell
  · -- ADMIT: both sides reduce to the same committed shape; an `Option`/structure congruence.
    rw [if_pos hg]
    obtain ⟨ha, hf⟩ := hg
    rw [if_pos (show mintAuthorizedB st.kernel.caps actor newCell = true ∧ newCell ∉ st.kernel.accounts
      from ⟨ha, hf⟩)]
    constructor
    · intro h
      simp only [Option.some.injEq] at h
      subst h
      exact ⟨rfl, rfl⟩
    · rintro ⟨hk, hl⟩
      simp only [Option.some.injEq] at hk
      -- reconstruct `st'` from its kernel (= `createCellIntoAsset …`) and log (= receipt :: log).
      obtain ⟨k', lg'⟩ := st'
      simp only at hk hl
      subst hk hl
      rfl
  · -- REJECT: the gate fails ⇒ both sides are `none`/unsatisfiable.
    rw [if_neg hg]
    rw [if_neg (fun hp => hg (show createCellAdmit st.kernel actor newCell from ⟨hp.1, hp.2⟩))]
    constructor
    · intro h; exact absurd h (by simp)
    · rintro ⟨hk, _⟩; exact absurd hk (by simp)

#assert_axioms interp_createCellStmt_chained

/-! ## §4 — THE COMPILE WELD: a satisfying witness of createCell's OWN standalone TRIPLE circuit agrees
with the FULL post-state the IR term's executor interpretation produces.

This welds against createCell's GENUINE standalone descriptor `createCellE …` (the v2 `Surface2` TRIPLE
circuit whose soundness is `createCellA_full_sound`, `Inst/createCellA.lean`). The executor side is
routed through §3 (`interp` ⟺ `execFullA`) and the independent `execCreateCellA_iff_spec` (executor ⟺
`CreateCellSpec`); the circuit side is the audited `createCellA_full_sound` (circuit ⟹ `CreateCellSpec`).
Both name the SAME `CreateCellSpec`, so they PROVABLY agree on the WHOLE 18-component state. -/

/-- The Argus circuit interpretation of a `createCell` term: createCell's OWN audited standalone v2
`Surface2` TRIPLE circuit step — the full-state arithmetization `satisfiedE2Triple S (createCellE …)
(encodeE2Triple …)` satisfied on the encoded `(st, args, st')` triple. Its soundness
`createCellA_full_sound` pins the complete `CreateCellSpec`. The `createCell`-keyed analog of
`balanceACircuit`. -/
def createCellCircuit (S : Surface2) (LE : CellId → ℤ) (cN : List ℤ → ℤ)
    (hN : compressNInjective cN) (hLE : listLeafInjective LE)
    (DBal : (CellId → AssetId → ℤ) → ℤ) (hDBal : Function.Injective DBal)
    (DSide : BornEmptySideTables → ℤ) (hDSide : Function.Injective DSide)
    (st : RecChainedState) (args : CreateCellArgs) (st' : RecChainedState) : Prop :=
  satisfiedE2Triple S (createCellE LE cN hN hLE DBal hDBal DSide hDSide)
    (encodeE2Triple S (createCellE LE cN hN hLE DBal hDBal DSide hDSide) st args st')

/-- **`createCellSpec_unique` — the spec pins a UNIQUE post-state.** Two chained states that BOTH satisfy
`CreateCellSpec st actor newCell ·` are equal. Rather than re-derive field-by-field, we route through the
PROVEN executor⟺spec corner `execCreateCellA_iff_spec`: each `CreateCellSpec` reconstructs the SAME
committed value `execFullA st (.createCellA actor newCell) = some ·`, and `some` is injective. This is
the sense in which `CreateCellSpec` is functional — it determines the post-state — so the circuit-side
and executor-side spec facts collapse to one welded post-state. -/
theorem createCellSpec_unique {st st₁ st₂ : RecChainedState} {actor newCell : CellId}
    (h₁ : CreateCellSpec st actor newCell st₁) (h₂ : CreateCellSpec st actor newCell st₂) :
    st₁ = st₂ := by
  have e₁ : execFullA st (.createCellA actor newCell) = some st₁ :=
    (execCreateCellA_iff_spec st actor newCell st₁).mpr h₁
  have e₂ : execFullA st (.createCellA actor newCell) = some st₂ :=
    (execCreateCellA_iff_spec st actor newCell st₂).mpr h₂
  exact Option.some.injEq _ _ ▸ (e₁.symm.trans e₂)

/-- **`createCell_compile_sound` — the welded soundness (createCell slice), against createCell's OWN
descriptor.**

Suppose, for the Argus createCell term `createCellStmt actor newCell` (with `args = ⟨actor, newCell⟩`):
  * the standalone createCell circuit `createCellCircuit S … st args st'` (= `createCellE`'s full-state
    v2 TRIPLE arithmetization satisfied on the encoded triple) holds, under the realizable
    whole-function / digest portals (`hRest`, `hLog`, and the injectivity hypotheses on `LE`/`cN`/`DBal`/
    `DSide`);
  * the IR term's EXECUTOR commits the chained step: `execFullA st (.createCellA actor newCell) = some
    st''` (`hexec`).

Then the chained post-state the circuit pins is EXACTLY the one the IR term's executor produces:
`st' = st''`. I.e. createCell's OWN circuit and the IR term AGREE on the WHOLE 18-component state
(`accounts` GROWN by `newCell`, `bal`/born-empty per-cell slots RESET at `newCell`, the creation
receipt prepended, every global side-table frozen) — the full `CreateCellSpec`, not a projection. So
the circuit the prover runs for createCell pins the complete state the IR term's executor produces. -/
theorem createCell_compile_sound
    (S : Surface2) (LE : CellId → ℤ) (cN : List ℤ → ℤ)
    (hN : compressNInjective cN) (hLE : listLeafInjective LE)
    (DBal : (CellId → AssetId → ℤ) → ℤ) (hDBal : Function.Injective DBal)
    (DSide : BornEmptySideTables → ℤ) (hDSide : Function.Injective DSide)
    (hRest : RestIffNoAccountsBalBorn S.RH) (hLog : logHashInjective S.LH)
    (st st' st'' : RecChainedState) (actor newCell : CellId)
    (hcirc : createCellCircuit S LE cN hN hLE DBal hDBal DSide hDSide
      st ⟨actor, newCell⟩ st')
    (hexec : execFullA st (.createCellA actor newCell) = some st'') :
    st' = st'' := by
  -- circuit side: createCell's OWN audited soundness forces the FULL `CreateCellSpec` on `(st, args, st')`.
  have hspec : CreateCellSpec st actor newCell st' :=
    createCellA_full_sound S LE cN hN hLE DBal hDBal DSide hDSide hRest hLog st ⟨actor, newCell⟩ st' hcirc
  -- executor side: the independent executor⟺spec corner turns the committed step into `CreateCellSpec`.
  have hspec' : CreateCellSpec st actor newCell st'' :=
    (execCreateCellA_iff_spec st actor newCell st'').mp hexec
  -- both states satisfy the SAME spec ⇒ they are the same state (the spec pins every component + the log).
  exact createCellSpec_unique hspec hspec'

#assert_axioms createCell_compile_sound

/-! ## §5 — NON-VACUITY: the IR term GROWS `accounts` (the very effect the old obstruction
proved no term could have), and the gate REJECTS forged inputs (fail-closed).

The cornerstone/weld would be hollow if createCell never committed, if the allocation were a no-op, or
if the gate admitted everything. A concrete kernel `kCC` (cells 0,1 live; cell 0 holds a `node 2`
creation cap over the fresh id 2) exercises a real allocation; the rejection lemmas show the gate fails
closed. The headline tooth: the fresh id is ABSENT before and PRESENT after — the structural growth the
old `interp_preserves_accounts` frame theorem proved impossible, now realized by `allocCell`. -/

/-- A concrete kernel for the witnesses: cells `0` and `1` are live accounts; cell `0` holds a `node 2`
cap (the privileged-creation authority `mintAuthorizedB` needs over the fresh id `2`). -/
def kCC : RecordKernelState :=
  { accounts := {0, 1}
    cell := fun _ => .record [("balance", .int 0)]
    caps := fun l => if l = 0 then [Dregg2.Authority.Cap.node 2] else [] }

-- The create of FRESH cell `2` by privileged actor `0` COMMITS (non-vacuous gate)…
#guard (interp (createCellStmt 0 2) kCC).isSome
-- …and the growth is OBSERVABLE: cell `2` is ABSENT before and PRESENT after (the structural alloc).
#guard ¬ (2 ∈ kCC.accounts)
#guard (((interp (createCellStmt 0 2) kCC).map (fun k => decide (2 ∈ k.accounts))) == some true)
-- …with a born-empty ledger column at the fresh id (asset 0 reads 0):
#guard (((interp (createCellStmt 0 2) kCC).map (fun k => k.bal 2 0)) == some 0)
-- An UNPRIVILEGED creation (actor 1, no `node 2` cap) is REJECTED:
#guard (interp (createCellStmt 1 2) kCC).isNone
-- A RE-MINT of a live id (cell 1 ∈ accounts) is REJECTED:
#guard (interp (createCellStmt 0 1) kCC).isNone

/-- **`createCellStmt_grows_accounts` — the IR term GROWS `accounts` (non-vacuous).**
On the concrete kernel `kCC`, the create of fresh cell `2` by privileged actor `0` COMMITS, and the
committed post-state has cell `2` as a live account (PRESENT after) while it was ABSENT before. This is
EXACTLY the `accounts`-change the module's former obstruction theorem proved no `RecStmt` term could
produce — now realized, because `allocCell` is the structural-alloc primitive the IR had lacked. -/
theorem createCellStmt_grows_accounts :
    ∃ k', interp (createCellStmt 0 2) kCC = some k'
      ∧ (2 : CellId) ∈ k'.accounts ∧ (2 : CellId) ∉ kCC.accounts := by
  refine ⟨createCellIntoAsset kCC 2, ?_, ?_, ?_⟩
  · rw [interp_createCellStmt_eq_createCellK, if_pos]
    -- the gate holds: privileged authority over `2` from the `node 2` cap at cell 0 ∧ `2 ∉ {0,1}`.
    exact (createCellGuard_iff 0 2 kCC).mp (by decide)
  · exact createCellIntoAsset_grows_accounts kCC 2
  · decide

#assert_axioms createCellStmt_grows_accounts

/-- **`createCellStmt_rejects_unauthorized` — fail-closed (no privileged creation cap).** A create whose
actor lacks the privileged creation authority over the fresh id does NOT commit — `interp` returns
`none`. No cell is allocated without the mint-grade cap. -/
theorem createCellStmt_rejects_unauthorized (actor newCell : CellId) (k : RecordKernelState)
    (hbad : mintAuthorizedB k.caps actor newCell = false) :
    interp (createCellStmt actor newCell) k = none := by
  rw [interp_createCellStmt_eq_createCellK, if_neg]
  rintro ⟨ha, _⟩; rw [hbad] at ha; exact absurd ha (by simp)

/-- **`createCellStmt_rejects_stale` — fail-closed (no re-minting a live id).** A create onto an id that
is ALREADY a live account does NOT commit — the freshness conjunct fails. No cell can be re-allocated
over an existing one. -/
theorem createCellStmt_rejects_stale (actor newCell : CellId) (k : RecordKernelState)
    (hbad : newCell ∈ k.accounts) :
    interp (createCellStmt actor newCell) k = none := by
  rw [interp_createCellStmt_eq_createCellK, if_neg]
  rintro ⟨_, hf⟩; exact hf hbad

#assert_axioms createCellStmt_rejects_unauthorized
#assert_axioms createCellStmt_rejects_stale

end Dregg2.Circuit.Argus.Effects.CreateCell
