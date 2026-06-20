/-
# Dregg2.Circuit.Emit.EffectVmEmitSpawn — the account-spawn effect `spawnA`, EMITTED onto the runnable
  EffectVM CHILD-cell row, with its (PARTIAL) full-state soundness and the connector to the validated
  universe-A `SpawnSpec` / `execSpawnA_iff_spec`.

## The "ONE circuit" thesis — and the HONEST PARTIAL boundary for a 5-component effect

`spawnA` (`Inst/spawnA.lean`, `Spec/accountgrowth.lean`) is a FIVE-component effect: it (1) grows the
`accounts` SET by `child`, (2) RESETS the child cell to born-empty (`cell child = default`, `bal child
a = 0`, `slotCaveats`/`lifecycle`/`deathCert` reset), (3) copies the held parent cap into `caps` at
`child` (`spawnCapsMap`), (4) initializes `delegate`/`delegations` at `child`, (5) prepends the creation
receipt to the log. Its validation `spawnA_full_sound ⇒ SpawnSpec` is DONE via the v2-QUINT framework.

The EffectVM row is a SINGLE-CELL window: it can pin the CHILD cell's per-cell EffectVM state
transition. Two `SpawnSpec` clauses project onto EffectVM CHILD-cell columns:

  * **born-empty balance** — `bal child a = 0` and `cell child = default` give the child's projected
    balance `balOf (cell child) = balOf default = 0`: the EffectVM child `bal_lo`/`bal_hi` columns are
    SET to `0`. (The born-empty child is the conservation-NEUTRAL fresh term.)
  * **authority handoff** — `caps child = spawnCapsMap …` gives the child's cap-table digest `D
    (spawnCapsMap …)`: the EffectVM child `cap_root` column MOVES to that digest.

The born-empty default also sets the child `nonce`/8 `fields`/`reserved` to `0` (`default = .int 0`,
whose `nonceOf`/`fieldOf` read `0`). So the descriptor pins the CHILD post-state: `bal_lo = bal_hi = 0`,
`nonce = 0`, `fields = 0`, `reserved = 0`, `cap_root = D(spawnCapsMap)` — and binds that whole child
post-state into `state_commit` (the anti-ghost tooth, reused from the transfer keystone).

`spawnVmDescriptor` emits exactly that per-CHILD-cell row.

## HONEST PARTIAL — the THREE unreachable components (IR gaps, flagged loudly)

The per-row CHILD-cell circuit CANNOT reach the following `SpawnSpec` components; they live ONLY in
universe-A's full-state portals (the SAME bar `spawnA_full_sound` uses), NOT in this per-row descriptor:

  * **`accounts` SET growth (`insert child …`)** — the EffectVM row layout has NO accounts-set column /
    no accounts-membership site. The `child ∈ accounts'` growth is reached only by universe-A's
    `accountsComponent` (the `compressN`/`listLeaf` injective digest portal). NOT pinned here.
  * **`delegate` / `delegations` side-tables at `child`** — no EffectVM columns; reached only by
    universe-A's `delegateComp`/`delegationsComp` `funcComponent` digests. NOT pinned here.
  * **the creation-receipt LOG growth** — no EffectVM log column; reached only by `logHashInjective`.
  * **cap-table HASH-SITE (inherited from `attenuateA`)** — `cap_root` is the SCALAR digest `D caps`,
    not re-derived in-circuit; the genuine-Merkle binding is universe-A's `Function.Injective D` portal.

So this module DELIVERS the child-cell born-empty-balance + cap-handoff per-row soundness + commitment
binding, and CONNECTS it to universe-A's `SpawnSpec`; it does NOT (and does not claim to) pin the
accounts-set growth, the delegate/delegations side-tables, or the log inside the per-row circuit. This
is an HONEST PARTIAL: a per-row beachhead for a 5-component effect, the three table/log components
flagged as IR gaps reached only through the validated full-state portals.

## Axiom hygiene

`#assert_axioms` ⊆ {propext, Classical.choice, Quot.sound} on every theorem. Poseidon2 CR enters ONLY as
the NAMED hypothesis `Poseidon2SpongeCR hash`; the cap-table digest ONLY as `Function.Injective D`. No
`sorry`, no `:= True`, no `native_decide`, no `rfl`-posing-as-bridge. Imports are read-only.
-/
import Dregg2.Circuit.Emit.EffectVmEmitTransferSound
import Dregg2.Circuit.Emit.EffectVmEmitRevokeDelegation
import Dregg2.Circuit.Poseidon2Binding
import Dregg2.Circuit.Spec.accountgrowth

namespace Dregg2.Circuit.Emit.EffectVmEmitSpawn

open Dregg2.Circuit
open Dregg2.Circuit.Emit.EffectVmEmit
open Dregg2.Circuit.Emit.EffectVmEmitTransfer
  (eSB eSA eSub transitionAll boundaryFirstPins transferHashSites)
open Dregg2.Circuit.Emit.EffectVmEmitTransferSound (CellState)
open Dregg2.Circuit.Poseidon2Binding (Poseidon2SpongeCR)
open Dregg2.Exec.CircuitEmit (EmittedExpr)
open Dregg2.Exec
open Dregg2.Exec.TurnExecutorFull
open Dregg2.Authority (Caps Cap)

set_option linter.unusedVariables false
set_option autoImplicit false

/-! ## §0 — Selector + param offsets for the spawn (child-cell born-empty) row. -/

namespace selSP
/-- The `spawnA` effect selector column. -/
def SPAWN : Nat := 6
end selSP

namespace paramSP
/-- The post child cap-table digest parameter (witness fills with `D (spawnCapsMap …)`). -/
def CAP_DIGEST_NEW : Nat := 5
end paramSP

/-- The `spawnA` selector as an expression. -/
def eSelSpawn : EmittedExpr := .var selSP.SPAWN

/-- The post-cap-digest param as an expression. -/
def eCapDigestNew : EmittedExpr := .var (prmCol paramSP.CAP_DIGEST_NEW)

/-! ## §1 — The spawn child-cell row gates.

The CHILD cell is RESET to born-empty (balance/nonce/fields/reserved → `0`) and its `cap_root` MOVES to
the spawn-caps digest. So the per-row gates SET the born-empty columns to `0` and MOVE `cap_root` to the
param — these are SET gates (`new_col - 0` and `new_cap_root - capDigest`), NOT freeze gates (the child
post-state is determined absolutely, not relative to its pre-state). -/

/-- Cap-root MOVE body: `new_cap_root - capDigestNew`. -/
def gCapMove : EmittedExpr := eSub (eSA state.CAP_ROOT) eCapDigestNew

/-- Balance-lo SET-TO-ZERO body: `new_bal_lo - 0 = new_bal_lo`. -/
def gBalLoZero : EmittedExpr := eSA state.BALANCE_LO
/-- Balance-hi SET-TO-ZERO body. -/
def gBalHiZero : EmittedExpr := eSA state.BALANCE_HI
/-- Nonce SET-TO-ZERO body (born-empty child nonce is `0`). -/
def gNonceZero : EmittedExpr := eSA state.NONCE
/-- Reserved SET-TO-ZERO body. -/
def gResZero : EmittedExpr := eSA state.RESERVED

/-- Field-`i` SET-TO-ZERO body (born-empty child field `i` is `0`). -/
def gFieldZero (i : Nat) : EmittedExpr := eSA (state.FIELD_BASE + i)

/-- The eight field-zero gates. -/
def gFieldZeroAll : List VmConstraint :=
  (List.range 8).map (fun i => VmConstraint.gate (gFieldZero i))

/-! ## §2 — The emitted descriptor. -/

/-- The `spawnA` AIR identity (the fingerprint binding). -/
def spawnVmAirName : String := "dregg-effectvm-spawnA-v2quint-childcell"

/-- The child-cell per-row gates: cap-root MOVE, balance/nonce/reserved SET-TO-ZERO, 8 fields zero. -/
def spawnRowGates : List VmConstraint :=
  [ .gate gCapMove, .gate gBalLoZero, .gate gBalHiZero, .gate gNonceZero
  , .gate gResZero ] ++ gFieldZeroAll

/-- The ordered GROUP-4 hash sites — DEFINITIONALLY the transfer keystone's (the born-empty columns +
moved `cap_root` are all absorbed). -/
def spawnHashSites : List VmHashSite := transferHashSites

/-- **`spawnVmDescriptor`** — the `spawnA` effect's CHILD-CELL concrete circuit: born-empty SET-TO-ZERO +
cap-root MOVE gates ++ transition continuity ++ the row-0 boundary pins, with the 4 ordered GROUP-4 hash
sites. No balance range checks (the child balance is the literal `0`). -/
def spawnVmDescriptor : EffectVmDescriptor :=
  { name := spawnVmAirName
  , traceWidth := EFFECT_VM_WIDTH
  , piCount := 42
  , constraints := spawnRowGates ++ transitionAll ++ boundaryFirstPins
  , hashSites := spawnHashSites
  , ranges := [] }

/-! ## §3 — The spawn child-cell ROW INTENT (the independent faithfulness target).

`SpawnRowIntent env` is the field-level born-empty + cap-handoff move: post `cap_root` IS the supplied
digest, and the balance limbs / nonce / reserved / 8 fields are SET TO `0`. The EffectVM-row projection
of `SpawnSpec`'s CHILD clauses (`bal child = 0` born-empty ⟹ child balance columns `0`; `caps child =
spawnCapsMap` ⟹ cap-DIGEST column). -/

/-- **`SpawnRowIntent env`** — post `cap_root` is the param digest, born-empty columns `0`. -/
def SpawnRowIntent (env : VmRowEnv) : Prop :=
  env.loc (saCol state.CAP_ROOT) = env.loc (prmCol paramSP.CAP_DIGEST_NEW)
  ∧ env.loc (saCol state.BALANCE_LO) = 0
  ∧ env.loc (saCol state.BALANCE_HI) = 0
  ∧ env.loc (saCol state.NONCE) = 0
  ∧ env.loc (saCol state.RESERVED) = 0
  ∧ (∀ i < 8, env.loc (saCol (state.FIELD_BASE + i)) = 0)

/-- The row is a `spawnA` row: `s_spawn = 1`, `s_noop = 0`. -/
def IsSpawnRow (env : VmRowEnv) : Prop :=
  env.loc selSP.SPAWN = 1 ∧ env.loc sel.NOOP = 0

/-! ## §4 — FAITHFULNESS: the emitted per-row gates ⟺ the intent. -/

/-- **`spawnRowGates_holds_iff`** — on a `spawnA` row, the emitted per-row gates all hold IFF
`SpawnRowIntent` holds. -/
theorem spawnRowGates_holds_iff (env : VmRowEnv) :
    (∀ c ∈ spawnRowGates, c.holdsVm env false false) ↔ SpawnRowIntent env := by
  unfold spawnRowGates gFieldZeroAll SpawnRowIntent
  constructor
  · intro h
    have hCap := h (.gate gCapMove) (by simp)
    have hLo := h (.gate gBalLoZero) (by simp)
    have hHi := h (.gate gBalHiZero) (by simp)
    have hNon := h (.gate gNonceZero) (by simp)
    have hRes := h (.gate gResZero) (by simp)
    have hFld : ∀ i, i < 8 → VmConstraint.holdsVm env false false (.gate (gFieldZero i)) := by
      intro i hi
      apply h
      simp only [List.mem_append, List.mem_map, List.mem_range]
      exact Or.inr ⟨i, hi, rfl⟩
    simp only [VmConstraint.holdsVm, gCapMove, gBalLoZero, gBalHiZero, gNonceZero, gResZero,
      eSA, eCapDigestNew, eSub, EmittedExpr.eval] at hCap hLo hHi hNon hRes
    refine ⟨by linarith [hCap], hLo, hHi, hNon, hRes, ?_⟩
    intro i hi
    have := hFld i hi
    simp only [VmConstraint.holdsVm, gFieldZero, eSA, EmittedExpr.eval] at this
    exact this
  · rintro ⟨hCap, hLo, hHi, hNon, hRes, hFld⟩ c hc
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, List.mem_map,
      List.mem_range] at hc
    rcases hc with (rfl | rfl | rfl | rfl | rfl) | ⟨i, hi, rfl⟩
    · simp only [VmConstraint.holdsVm, gCapMove, eSA, eCapDigestNew, eSub, EmittedExpr.eval]
      rw [hCap]; ring
    · simp only [VmConstraint.holdsVm, gBalLoZero, eSA, EmittedExpr.eval]; exact hLo
    · simp only [VmConstraint.holdsVm, gBalHiZero, eSA, EmittedExpr.eval]; exact hHi
    · simp only [VmConstraint.holdsVm, gNonceZero, eSA, EmittedExpr.eval]; exact hNon
    · simp only [VmConstraint.holdsVm, gResZero, eSA, EmittedExpr.eval]; exact hRes
    · simp only [VmConstraint.holdsVm, gFieldZero, eSA, EmittedExpr.eval]; exact hFld i hi

/-- **`spawnVm_faithful` — THE deliverable.** On a `spawnA` row, the emitted descriptor's per-row gates
hold IFF the born-empty + cap-handoff intent holds. -/
theorem spawnVm_faithful (env : VmRowEnv) :
    (∀ c ∈ spawnRowGates, c.holdsVm env false false) ↔ SpawnRowIntent env :=
  spawnRowGates_holds_iff env

/-! ## §5 — ANTI-GHOST (per-row). -/

/-- **Anti-ghost (cap-root tamper).** A row whose post-`cap_root` is NOT the supplied digest fails the
`gCapMove` gate (UNSAT). -/
theorem spawnVm_rejects_wrong_capRoot (env : VmRowEnv)
    (hwrong : env.loc (saCol state.CAP_ROOT) ≠ env.loc (prmCol paramSP.CAP_DIGEST_NEW)) :
    ¬ (VmConstraint.gate gCapMove).holdsVm env false false := by
  simp only [VmConstraint.holdsVm, gCapMove, eSA, eCapDigestNew, eSub, EmittedExpr.eval]
  intro h
  apply hwrong
  linarith

/-- **Anti-ghost (non-zero born balance).** A row whose child post-`bal_lo` is NOT `0` (a forged
non-empty born child) fails the `gBalLoZero` gate (UNSAT). -/
theorem spawnVm_rejects_nonzero_balance (env : VmRowEnv)
    (hwrong : env.loc (saCol state.BALANCE_LO) ≠ 0) :
    ¬ (VmConstraint.gate gBalLoZero).holdsVm env false false := by
  simp only [VmConstraint.holdsVm, gBalLoZero, eSA, EmittedExpr.eval]
  exact hwrong

/-- **Anti-ghost (general).** A row whose post-state is NOT the intent move does NOT satisfy the per-row
gates. -/
theorem spawnVm_rejects_wrong_output (env : VmRowEnv) (hwrong : ¬ SpawnRowIntent env) :
    ¬ (∀ c ∈ spawnRowGates, c.holdsVm env false false) :=
  fun h => hwrong ((spawnVm_faithful env).mp h)

/-! ## §6 — The structured per-cell soundness (the keystone analog). -/

/-- **`SpawnRowEncodes env post capDigestNew`** — the row decodes the CHILD `state_after` block to a
`post` cell state with the post cap-digest carried in `param.CAP_DIGEST_NEW`. (No `pre` needed: the child
post-state is absolute, not relative.) -/
def SpawnRowEncodes (env : VmRowEnv) (post : CellState) (capDigestNew : ℤ) : Prop :=
  env.loc (prmCol paramSP.CAP_DIGEST_NEW) = capDigestNew
  ∧ env.loc (saCol state.BALANCE_LO) = post.balLo
  ∧ env.loc (saCol state.BALANCE_HI) = post.balHi
  ∧ env.loc (saCol state.NONCE) = post.nonce
  ∧ (∀ i : Fin 8, env.loc (saCol (state.FIELD_BASE + i.val)) = post.fields i)
  ∧ env.loc (saCol state.CAP_ROOT) = post.capRoot
  ∧ env.loc (saCol state.RESERVED) = post.reserved

/-- The per-cell spawn-child spec: the child's WHOLE post-state is born-empty (balance/nonce/fields/
reserved `0`) with `cap_root` set to the new cap-digest. The per-cell projection of universe-A's
`SpawnSpec` child clauses. -/
def SpawnChildSpec (post : CellState) (capDigestNew : ℤ) : Prop :=
  post.capRoot = capDigestNew
  ∧ post.balLo = 0
  ∧ post.balHi = 0
  ∧ post.nonce = 0
  ∧ (∀ i : Fin 8, post.fields i = 0)
  ∧ post.reserved = 0

/-- Under `SpawnRowEncodes`, `SpawnRowIntent` IS the structured per-cell `SpawnChildSpec`. -/
theorem intent_to_spawnChildSpec (env : VmRowEnv) (post : CellState) (capDigestNew : ℤ)
    (henc : SpawnRowEncodes env post capDigestNew) (hint : SpawnRowIntent env) :
    SpawnChildSpec post capDigestNew := by
  obtain ⟨hpDig, hsaLo, hsaHi, hsaN, hsaF, hsaCap, hsaRes⟩ := henc
  obtain ⟨hcap, hlo, hhi, hnon, hres, hfld⟩ := hint
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← hsaCap, ← hpDig]; exact hcap
  · rw [← hsaLo]; exact hlo
  · rw [← hsaHi]; exact hhi
  · rw [← hsaN]; exact hnon
  · intro i; rw [← hsaF i]; exact hfld i.val i.isLt
  · rw [← hsaRes]; exact hres

/-- **`spawnDescriptor_full_sound` — the structured (child-cell) soundness.** Satisfying the per-row
gates under the `SpawnRowEncodes` decoding forces the structured per-cell `SpawnChildSpec`. -/
theorem spawnDescriptor_full_sound (env : VmRowEnv) (post : CellState) (capDigestNew : ℤ)
    (henc : SpawnRowEncodes env post capDigestNew)
    (hgates : ∀ c ∈ spawnRowGates, c.holdsVm env false false) :
    SpawnChildSpec post capDigestNew :=
  intent_to_spawnChildSpec env post capDigestNew henc ((spawnVm_faithful env).mp hgates)

/-! ## §7 — THE ANTI-GHOST COMMITMENT TOOTH (whole child-state binding). -/

open Dregg2.Circuit.Emit.EffectVmEmitTransferSound
  (absorbedCols absorbed_determined_by_commit)

/-- `spawnHashSites` is DEFINITIONALLY the transfer keystone's `transferHashSites`. -/
theorem spawnHashSites_eq : spawnHashSites = transferHashSites := rfl

/-- **`spawnDescriptor_commit_binds_state` — the whole child-state tooth.** Two `spawnA` rows that
satisfy the hash-sites and publish equal `state_commit`s have identical absorbed columns — the born-empty
balance/nonce/fields and the moved `cap_root` all included. -/
theorem spawnDescriptor_commit_binds_state (hash : List ℤ → ℤ) (hCR : Poseidon2SpongeCR hash)
    (e₁ e₂ : VmRowEnv)
    (hs₁ : siteHoldsAll hash e₁ spawnHashSites)
    (hs₂ : siteHoldsAll hash e₂ spawnHashSites)
    (hcommit : e₁.loc (saCol state.STATE_COMMIT) = e₂.loc (saCol state.STATE_COMMIT)) :
    absorbedCols e₁ = absorbedCols e₂ := by
  rw [spawnHashSites_eq] at hs₁ hs₂
  exact absorbed_determined_by_commit hash hCR e₁ e₂ hs₁ hs₂ hcommit

/-! ## §8 — THE CONNECTOR — `capRootProj`/`balProj` to universe-A's `SpawnSpec`.

`capRootProj D k = D k.caps` reads the cap-table digest; `balProj k c = balOf (k.cell c)` reads the
child's conserved balance. A committed `SpawnSpec` makes the projected child post-`cap_root` EXACTLY `D
(spawnCapsMap …)` and the child post-balance `0` (born-empty) — the two column values the descriptor
pins. -/

open Dregg2.Circuit.Spec.AccountGrowth (SpawnSpec spawnCapsMap execSpawnA_iff_spec)

/-- **`capRootProj D k`** — the EffectVM `cap_root` column value for kernel state `k`: `D k.caps`. -/
def capRootProj (D : Caps → ℤ) (k : RecordKernelState) : ℤ := D k.caps

/-- The predicted post child cap-digest the descriptor's `param.CAP_DIGEST_NEW` carries. -/
def spawnCapDigestNew (D : Caps → ℤ) (k : RecordKernelState) (actor child target : CellId) : ℤ :=
  D (spawnCapsMap k actor child target)

/-- **`balProj k c`** — the EffectVM child-cell balance column value: `balOf (k.cell c)`. -/
def balProj (k : RecordKernelState) (c : CellId) : ℤ := balOf (k.cell c)

/-- **`unify_spawn_caps` — THE CAP CONNECTOR.** When universe-A's `SpawnSpec` holds, the projected post
cap-table digest is EXACTLY `spawnCapDigestNew D k actor child target` — the column move the descriptor
pins. So `SpawnChildSpec`'s `cap_root` clause IS universe-A's `caps`-clause, projected to the digest
column. -/
theorem unify_spawn_caps (D : Caps → ℤ)
    (s : RecChainedState) (actor child target : CellId) (s' : RecChainedState)
    (hspec : SpawnSpec s actor child target s') :
    capRootProj D s'.kernel = spawnCapDigestNew D s.kernel actor child target := by
  -- SpawnSpec's caps clause is `s'.kernel.caps = spawnCapsMap s.kernel actor child target`.
  obtain ⟨_, _, _, _, _, _, _, hcaps, _⟩ := hspec
  show D s'.kernel.caps = D (spawnCapsMap s.kernel actor child target)
  rw [hcaps]

/-- **`unify_spawn_balance` — THE BORN-EMPTY BALANCE CONNECTOR.** When `SpawnSpec` holds, the child cell
is born-empty (`cell child = default`), so the projected child balance is `balOf default = 0` — the
column value the descriptor's `gBalLoZero` gate pins. So `SpawnChildSpec`'s `balLo = 0` clause IS
universe-A's born-empty `cell child = default` clause, projected to the balance column. -/
theorem unify_spawn_balance (s : RecChainedState) (actor child target : CellId) (s' : RecChainedState)
    (hspec : SpawnSpec s actor child target s') :
    balProj s'.kernel child = 0 := by
  -- SpawnSpec's cell clause is `s'.kernel.cell = fun c => if c = child then default else …`.
  obtain ⟨_, _, hcell, _⟩ := hspec
  show balOf (s'.kernel.cell child) = 0
  rw [hcell]
  simp only [if_pos rfl]
  rfl

/-- **`unify_spawn_via_exec` — the runnable column moves inherit the VALIDATED guarantee.** Chaining
universe-A's `execSpawnA_iff_spec` (a committed executor spawn ⟹ `SpawnSpec`) with the two connectors: a
committed `spawnA` forces the projected child post-`cap_root` to the spawn-caps digest AND the child
post-balance to `0` — the EXACT column values the runnable descriptor pins. So the runnable child-cell
moves are universe-A's validated `caps`/born-empty transitions, not a fourth spec. -/
theorem unify_spawn_via_exec (D : Caps → ℤ)
    (s : RecChainedState) (actor child target : CellId) (s' : RecChainedState)
    (h : execFullA s (.spawnA actor child target) = some s') :
    capRootProj D s'.kernel = spawnCapDigestNew D s.kernel actor child target
    ∧ balProj s'.kernel child = 0 :=
  ⟨unify_spawn_caps D s actor child target s' ((execSpawnA_iff_spec s actor child target s').mp h),
   unify_spawn_balance s actor child target s' ((execSpawnA_iff_spec s actor child target s').mp h)⟩

/-! ## §9 — NON-VACUITY: a concrete spawn child-cell row that satisfies the intent, and ones that do not. -/

/-- A concrete `spawnA` child row: `cap_root → 77` (the handoff digest), balance/nonce/fields/reserved
all `0` (born-empty). -/
def spawnGoodRow : VmRowEnv where
  loc := fun v =>
    if v = selSP.SPAWN then 1
    else if v = saCol state.CAP_ROOT then 77
    else if v = prmCol paramSP.CAP_DIGEST_NEW then 77
    else 0
  nxt := fun _ => 0
  pub := fun _ => 0

/-- `spawnGoodRow` is a genuine `spawnA` row. -/
theorem spawnGoodRow_isSpawnRow : IsSpawnRow spawnGoodRow := by
  unfold IsSpawnRow spawnGoodRow
  constructor <;> norm_num [selSP.SPAWN, sel.NOOP, saCol, prmCol, STATE_AFTER_BASE, PARAM_BASE,
    STATE_BEFORE_BASE, NUM_EFFECTS, STATE_SIZE, NUM_PARAMS, state.CAP_ROOT, paramSP.CAP_DIGEST_NEW]

/-- Evaluate `spawnGoodRow.loc` at a column given as a LITERAL `Nat` not in the named set `{6, 87, 73}`
(selector `6`, post-`cap_root` `87`, cap-digest param `73`) — returns the `else 0` default. -/
theorem spawnGoodRow_loc_default (n : Nat) (h6 : n ≠ 6) (h87 : n ≠ 87) (h73 : n ≠ 73) :
    spawnGoodRow.loc n = 0 := by
  show (if n = selSP.SPAWN then (1:ℤ)
    else if n = saCol state.CAP_ROOT then 77
    else if n = prmCol paramSP.CAP_DIGEST_NEW then 77 else 0) = 0
  have c1 : (selSP.SPAWN : Nat) = 6 := rfl
  have c2 : saCol state.CAP_ROOT = 87 := by
    unfold saCol STATE_AFTER_BASE PARAM_BASE STATE_BEFORE_BASE NUM_EFFECTS STATE_SIZE NUM_PARAMS
      state.CAP_ROOT; rfl
  have c3 : prmCol paramSP.CAP_DIGEST_NEW = 73 := by
    unfold prmCol PARAM_BASE STATE_BEFORE_BASE NUM_EFFECTS STATE_SIZE paramSP.CAP_DIGEST_NEW; rfl
  rw [c1, c2, c3, if_neg h6, if_neg h87, if_neg h73]

/-- **NON-VACUITY (witness TRUE).** `spawnGoodRow` REALIZES the spawn child intent: post `cap_root = 77`
= the param digest, balance/nonce/reserved/fields all `0` (born-empty). -/
theorem spawnGoodRow_realizes_intent : SpawnRowIntent spawnGoodRow := by
  have hsacap : saCol state.CAP_ROOT = 87 := by
    unfold saCol STATE_AFTER_BASE PARAM_BASE STATE_BEFORE_BASE NUM_EFFECTS STATE_SIZE NUM_PARAMS
      state.CAP_ROOT; rfl
  have hprm : prmCol paramSP.CAP_DIGEST_NEW = 73 := by
    unfold prmCol PARAM_BASE STATE_BEFORE_BASE NUM_EFFECTS STATE_SIZE paramSP.CAP_DIGEST_NEW; rfl
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- post cap_root (87 → 77) = cap-digest param (73 → 77)
    show spawnGoodRow.loc (saCol state.CAP_ROOT) = spawnGoodRow.loc (prmCol paramSP.CAP_DIGEST_NEW)
    rw [hsacap, hprm]; rfl
  · show spawnGoodRow.loc (saCol state.BALANCE_LO) = 0
    exact spawnGoodRow_loc_default (saCol state.BALANCE_LO) (by decide) (by decide) (by decide)
  · show spawnGoodRow.loc (saCol state.BALANCE_HI) = 0
    exact spawnGoodRow_loc_default (saCol state.BALANCE_HI) (by decide) (by decide) (by decide)
  · show spawnGoodRow.loc (saCol state.NONCE) = 0
    exact spawnGoodRow_loc_default (saCol state.NONCE) (by decide) (by decide) (by decide)
  · show spawnGoodRow.loc (saCol state.RESERVED) = 0
    exact spawnGoodRow_loc_default (saCol state.RESERVED) (by decide) (by decide) (by decide)
  · intro i hi8
    show spawnGoodRow.loc (saCol (state.FIELD_BASE + i)) = 0
    have hsaI : saCol (state.FIELD_BASE + i) = 79 + i := by
      unfold saCol STATE_AFTER_BASE PARAM_BASE STATE_BEFORE_BASE NUM_EFFECTS STATE_SIZE NUM_PARAMS
        state.FIELD_BASE; omega
    rw [hsaI]
    exact spawnGoodRow_loc_default (79 + i) (by omega) (by omega) (by omega)

/-- A forged spawn row: `spawnGoodRow` with the child post-`bal_lo` tampered to `999 ≠ 0` (a non-empty
born child — the kind of ghost the born-empty gate forbids). -/
def spawnBadBalRow : VmRowEnv where
  loc := fun v => if v = saCol state.BALANCE_LO then 999 else spawnGoodRow.loc v
  nxt := spawnGoodRow.nxt
  pub := spawnGoodRow.pub

/-- **NON-VACUITY (witness FALSE / concrete anti-ghost).** `spawnBadBalRow`'s child post-`bal_lo` is NOT
`0`, so the `gBalLoZero` gate REJECTS it — a concrete UNSAT (no forged non-empty born child). -/
theorem spawnBadBalRow_rejected : ¬ (VmConstraint.gate gBalLoZero).holdsVm spawnBadBalRow false false := by
  apply spawnVm_rejects_nonzero_balance
  show (if saCol state.BALANCE_LO = saCol state.BALANCE_LO then (999:ℤ)
    else spawnGoodRow.loc (saCol state.BALANCE_LO)) ≠ 0
  rw [if_pos rfl]; decide

/-! ## §10 — Axiom-hygiene tripwires (the honesty tripwire). -/

#guard spawnVmDescriptor.constraints.length == 13 + 14 + 4  -- 13 gates + 14 transitions + 4 first
#guard spawnVmDescriptor.hashSites.length == 4
#guard spawnVmDescriptor.traceWidth == 188

#assert_axioms spawnRowGates_holds_iff
#assert_axioms spawnVm_faithful
#assert_axioms spawnVm_rejects_wrong_capRoot
#assert_axioms spawnVm_rejects_nonzero_balance
#assert_axioms spawnVm_rejects_wrong_output
#assert_axioms intent_to_spawnChildSpec
#assert_axioms spawnDescriptor_full_sound
#assert_axioms spawnDescriptor_commit_binds_state
#assert_axioms unify_spawn_caps
#assert_axioms unify_spawn_balance
#assert_axioms unify_spawn_via_exec
#assert_axioms spawnGoodRow_realizes_intent
#assert_axioms spawnBadBalRow_rejected

/-! ## §RT — the RUNTIME-RECONCILED cutover descriptor (v3): the ACTING cell's passthrough + nonce-TICK
row (GRADUATED into the descriptor cutover).

THE RUNTIME GROUND TRUTH. The running prover runs `spawn_with_delegation` (selector 32) as a member of
the **Stage-3 passthrough batch** (`effect_vm/trace.rs`: the arm parks `spawn_hash[0]` into `params[0]`
and does `new_state.nonce += 1`). Every economic state-block column of the ACTING (parent) cell is
FROZEN; the global nonce gate TICKS the nonce by 1. The CHILD cell's born-empty + cap-handoff block —
the §1–§9 descriptor above (`spawnVmDescriptor`, the v2-QUINT CHILD face) — is OFF-ROW content for THIS
row: the child reset + `spawnCapsMap` handoff is the executor's guarantee (`spawnA_full_sound`, the §
connectors), bound through `effects_hash`, NOT a column move on the parent's row. The pre-v3 cutover
registered the CHILD-face descriptor against selector 32, which the runtime hand-AIR row (the PARENT's
row) cannot satisfy — the documented lifecycle/birth divergence. This v3 emits the runtime actor row
directly: the validated frozen-frame + nonce-tick template (`revokeRowGates`, proven faithful in
`EffectVmEmitRevokeDelegation`) + the spawn selector binding. Both faces stay verified; the WIRE
descriptor is the actor row. -/

open Dregg2.Circuit.Emit.EffectVmEmitRevokeDelegation
  (revokeRowGates RevokeRowIntent revokeVm_faithful intent_to_cellSpec RevokeCellSpec
   RowEncodesRevoke gBalLoFreeze goodRevokeRow goodRevokeRow_realizes_intent
   badRevokeRow badRevokeRow_rejected)
open Dregg2.Circuit.Emit.EffectVmEmitTransfer
  (eSelNoop gBalHi gNonce gCapPass gResPass gFieldPass gFieldPassAll
   boundaryLastPins boundaryLast_pins)

/-- The `spawn_with_delegation` selector column index (runtime `sel::SPAWN_WITH_DELEGATION = 32`). -/
def SEL_SPAWN_RT : Nat := 32

/-- The v3 (runtime-reconciled) `spawn` AIR identity. -/
def spawnActorVmAirName : String := "dregg-effectvm-spawnA-v3-actorrow"

/-- **`spawnActorVmDescriptor`** — the `spawn_with_delegation` ACTOR-row circuit, RECONCILED onto the
runtime hand-AIR: the shared frozen-frame + nonce-TICK gates ++ transition continuity ++ the 7 boundary
PI pins ++ the selector-binding gate, with the 4 ordered GROUP-4 hash sites and the 2 balance-limb
range checks. Body structurally identical to the validated `revokeDelegation-v2` template; only the
name and the selector gate differ. The born-empty CHILD face stays `spawnVmDescriptor` (§2). -/
def spawnActorVmDescriptor : EffectVmDescriptor :=
  { name := spawnActorVmAirName
  , traceWidth := EFFECT_VM_WIDTH
  , piCount := 42
  , constraints := revokeRowGates ++ transitionAll ++ boundaryFirstPins ++ boundaryLastPins
                     ++ selectorGates SEL_SPAWN_RT
  , hashSites := transferHashSites
  , ranges := [ ⟨saCol state.BALANCE_LO, 30⟩, ⟨saCol state.BALANCE_HI, 30⟩ ] }

/-- **Faithfulness (inherited from the shared template).** The actor row's per-row gates hold IFF the
frozen-frame + nonce-tick intent holds. Non-vacuity rides with the template (`goodRevokeRow` /
`badRevokeRow`). -/
theorem spawnActor_faithful (env : VmRowEnv) :
    (∀ c ∈ revokeRowGates, c.holdsVm env false false) ↔ RevokeRowIntent env :=
  revokeVm_faithful env

/-- **`spawnActor_full_sound`** — the v3 descriptor's row soundness: a satisfying row, decoded, pins
the full per-cell frozen-frame + nonce-tick post-state AND publishes its commit as `NEW_COMMIT`. -/
theorem spawnActor_full_sound (hash : List ℤ → ℤ) (env : VmRowEnv)
    (pre post : CellState) (hnoop : env.loc sel.NOOP = 0)
    (henc : RowEncodesRevoke env pre post)
    (hgatesat : satisfiedVm hash spawnActorVmDescriptor env true false)
    (hsat : satisfiedVm hash spawnActorVmDescriptor env true true) :
    RevokeCellSpec pre post ∧ post.commit = env.pub pi.NEW_COMMIT := by
  obtain ⟨hcs, _⟩ := hsat
  obtain ⟨hcsT, _⟩ := hgatesat
  have hgates' : ∀ c ∈ revokeRowGates, c.holdsVm env false false := by
    intro c hc
    have hmem : c ∈ spawnActorVmDescriptor.constraints := by
      unfold spawnActorVmDescriptor
      simp only [List.mem_append]
      exact Or.inl (Or.inl (Or.inl (Or.inl hc)))
    have := hcsT c hmem
    unfold Dregg2.Circuit.Emit.EffectVmEmitRevokeDelegation.revokeRowGates gFieldPassAll at hc
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, List.mem_map,
      List.mem_range] at hc
    rcases hc with (rfl | rfl | rfl | rfl | rfl) | ⟨i, hi, rfl⟩ <;>
      simpa only [VmConstraint.holdsVm] using this
  have hint := (revokeVm_faithful env).mp hgates'
  refine ⟨intent_to_cellSpec env pre post hnoop henc hint, ?_⟩
  have hlast : ∀ c ∈ boundaryLastPins, c.holdsVm env false true := by
    intro c hc
    have hmem : c ∈ spawnActorVmDescriptor.constraints := by
      unfold spawnActorVmDescriptor
      simp only [List.mem_append]
      exact Or.inl (Or.inr hc)
    have hh := hcs c hmem
    unfold boundaryLastPins at hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl <;>
      · simp only [VmConstraint.holdsVm] at hh ⊢
        exact hh
  have hpin := (boundaryLast_pins env hlast).1
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, hsaC, _, _⟩ := henc
  rw [← hsaC]; exact hpin

#guard spawnActorVmDescriptor.constraints.length == 13 + 14 + 4 + 3 + 1
#guard spawnActorVmDescriptor.hashSites.length == 4
#guard spawnActorVmDescriptor.traceWidth == 188

#assert_axioms spawnActor_faithful
#assert_axioms spawnActor_full_sound

end Dregg2.Circuit.Emit.EffectVmEmitSpawn
