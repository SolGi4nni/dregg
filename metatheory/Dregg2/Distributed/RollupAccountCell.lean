/-
# `Dregg2.Distributed.RollupAccountCell` — the dregg-L1 ROLLUP ACCOUNT as a REAL CELL, advanced by a REAL TURN.

`Dregg2.Distributed.SelfSettlement` proves *when* a child settlement is accepted (`SettleAccepts`),
*what the L1 then holds* (`applySettle`), and that the held root IS the child's genuine whole-history
fold (`settled_root_is_child_final_fold`). Every one of those theorems is about an ABSTRACT
`RollupAccount` structure. Nothing persisted it, and nothing ran.

This module lands the account half: `RollupAccount` as a **`RecordKernelState` cell**, keyed by the
child's GENESIS ROOT, advanced by a turn the **shipped executor** (`execFullTurnA`) actually runs,
with the account's laws enforced by the cell's factory-installed `slotCaveats` — the same
`stateStepDev` → `stateStepGuarded` → `caveatsAdmit` path every `setFieldA` in the tree goes through.

## What now RUNS (and what still only proves)

**RUNS.** The account cell, its five slots, and the settlement's ACCOUNT WRITE. `settleTurn` is a
`List FullActionA` that `execFullTurnA` executes; `#guard`s below run it on a concrete registered
account and read the committed root back out. Three of `SettleAccepts`' seven legs are enforced BY
THE EXECUTOR on that turn, as slot caveats rather than as a hypothesis:

  * `genesis_ok` — `.immutable childGenesisSlot`. The registered child genesis is the account's
    cryptographic identity and it is **frozen for the cell's whole life**; a settlement that tries to
    re-home the account to a different chain is REFUSED by the executor
    (`rollup_genesis_cannot_be_rehomed`, unconditional).
  * the Nomad law — `.monotonic rootSetSlot`. The presence flag can go `0 → 1` and never back
    (`rollup_root_flag_cannot_unset`), and `readAccount` reads a `0` flag as `none` **regardless of
    what the root slot holds**, so an unset account cannot read as "proven"
    (`readAccount_unset_proves_nothing`) and a settled one cannot be un-proven.
  * who may settle — `.senderAuthorized latestRootSlot [settlerActor]`. A stranger's write of the
    root is REFUSED (`rollup_unauthorized_settler_refused`).

The bridge to the proved model is `readAccount_settle_is_applySettle`: the cell, decoded, IS the
`RollupAccount` that `settled_root_is_child_final_fold` quantifies over. Compose the two and the
field element sitting in slot `latest_root` of a real cell is the child chain's genuine folded final
root.

**STILL ONLY PROVES — and the reason is exactly one thing.** Two of `SettleAccepts`' legs are NOT
executor-enforced here:

  * `engine` / `root_ok` — the child aggregate's recursion proof verifying. The account write is a
    `setFieldA`, and a `setFieldA` carries no proof argument. Making the executor REFUSE a settlement
    whose child proof does not verify needs a `FullActionA` constructor carrying the verification
    shadow (the shape `noteSpendA`'s `spendProof : Bool` already has), which is the blocked step.
  * `monotone` — the STRICT height advance. The caveat vocabulary has `.monotonic` (`old ≤ new`) and
    `.monotonicSeq` (`new = old + 1`); it has **no strict-`<` caveat**, and a settlement height jumps
    by the child's turn count, not by one. So `rollup_height_cannot_regress` is real and
    executor-enforced, but a REPLAY at the SAME height is admitted by the caveat gate. `SettleAccepts.
    monotone` remains an effect-level gate. This is a measured limit of the caveat surface, not an
    oversight: see `rollup_replay_at_same_height_is_admitted`, which EXHIBITS it rather than leaving
    it to be discovered.

So: the account is real, the write is real, the identity pin and the Nomad law are executor-enforced,
and the child-proof gate is not. That is the honest state.

## Substrate (HOUSE LAW #1)

No AIR is authored here and none is extended. The write is `setFieldA`, whose descriptor, deployed
registry position and apex closure already exist; this module adds a cell layout and turns, not
constraints. The settlement's own constraint set is `Circuit/Emit/SelfSettlementEmit.lean`
(`dregg-self-settlement-v1`), Lean-authored and byte-pinned, and Rust's job is to call it.

`#assert_axioms`-clean, no `sorry`, no `native_decide`.

⚑ **ROOT IMPORT REQUIRED — this module is an ORPHAN until it is added.** Its pins run in no CI target
until `metatheory/Dregg2.lean` carries:

```
import Dregg2.Distributed.RollupAccountCell
```

This is the SAME failure `docs/DREGG-IN-DREGG-BUILD.md` records twice (F-B1: `SelfSettlement`'s 20
pins shipped uncompiled). Reported, not hidden.
-/
import Dregg2.Exec.TurnExecutorFull
import Dregg2.Distributed.SelfSettlement

namespace Dregg2.Distributed.RollupAccountCell

open Dregg2.Exec
open Dregg2.Exec.TurnExecutorFull
open Dregg2.Exec.EffectsState (caveatsAdmit fieldOf stateStepDev_caveat_violation_fails)

/-! ## §1 — the account CELL: five of a `Value`'s eight developer slots.

A `RecordKernelState` cell is `cell : CellId → Value` and a `Value` carries eight developer field
slots. `RollupAccount` is four fields, and the `Option ℤ` root needs a presence flag, so the account
occupies FIVE — none of them one of the four protocol-managed slots
(`nonce`/`permissions`/`verification_key`/`program`), so a developer `setFieldA` may write them and
`stateStepDev`'s reserved-slot gate is not in the way. -/

/-- The L1 cell holding one child chain's rollup account. -/
abbrev rollupCell : CellId := 0

/-- The cell authorized to settle into `rollupCell` (the `.senderAuthorized` member). -/
abbrev settlerActor : CellId := 0

/-- A cell that holds no authority to settle — the impostor of the refusal tooth. -/
abbrev strangerActor : CellId := 1

/-- `RollupAccount.childId` — the NOMINAL child identity. Frozen (it is not the identity that
matters, but re-labelling an account is still not a settlement's business). -/
abbrev childIdSlot : FieldName := "child_id"

/-- `RollupAccount.childGenesis` — the child chain's REGISTERED GENESIS ROOT, its **cryptographic**
identity. `.immutable`: fixed at registration, frozen for the cell's whole life. -/
abbrev childGenesisSlot : FieldName := "child_genesis"

/-- `RollupAccount.latestRoot`'s VALUE. Written only by an authorized settler. -/
abbrev latestRootSlot : FieldName := "latest_root"

/-- `RollupAccount.latestRoot`'s PRESENCE flag (`0` = `none`, the Nomad default). `.monotonic`, so
a settled account can never be driven back to "nothing proven". -/
abbrev rootSetSlot : FieldName := "latest_root_set"

/-- `RollupAccount.latestHeight` — the child `num_turns` at which `latestRoot` was settled. -/
abbrev latestHeightSlot : FieldName := "latest_height"

/-- **The caveats a rollup-account factory installs on every minted account cell.** These are what
make the account's laws EXECUTOR-ENFORCED rather than asserted: the two identity slots are frozen,
the presence flag and the height only ever climb, and only the designated settler writes the root. -/
def rollupCaveats : List SlotCaveat :=
  [ .immutable childIdSlot
  , .immutable childGenesisSlot
  , .monotonic rootSetSlot
  , .monotonic latestHeightSlot
  , .senderAuthorized latestRootSlot [settlerActor] ]

/-! ## §2 — DECODE: the cell IS the `RollupAccount` the settlement theorems quantify over. -/

/-- **`readAccount k c`** — decode cell `c` of kernel `k` as a `SelfSettlement.RollupAccount`.

The presence flag is consulted FIRST: a `0` flag decodes to `latestRoot = none` **whatever the root
slot holds**. That is the Nomad law by construction at the cell layer — there is no `0`-that-reads-as-
proven, and no stale root can be resurrected by clearing a flag (which `.monotonic` forbids anyway). -/
def readAccount (k : RecordKernelState) (c : CellId) : SelfSettlement.RollupAccount :=
  { childId      := fieldOf childIdSlot (k.cell c)
  , childGenesis := fieldOf childGenesisSlot (k.cell c)
  , latestRoot   := if fieldOf rootSetSlot (k.cell c) = 0 then none
                    else some (fieldOf latestRootSlot (k.cell c))
  , latestHeight := (fieldOf latestHeightSlot (k.cell c)).toNat }

/-- **`readAccount_unset_proves_nothing` (THE NOMAD LAW, at the cell).** An account whose presence
flag is `0` attests NOTHING — no root, whatever the root slot happens to contain. The cell-layer twin
of `SelfSettlement.unset_account_proves_nothing`. -/
theorem readAccount_unset_proves_nothing (k : RecordKernelState) (c : CellId)
    (h : fieldOf rootSetSlot (k.cell c) = 0) :
    (readAccount k c).latestRoot = none := by
  simp [readAccount, h]

/-- **`readAccount_settle_is_applySettle` (THE BRIDGE).** A cell whose slots hold a settled account
decodes to EXACTLY `SelfSettlement.applySettle acc s` — the abstract account that
`settled_root_is_child_final_fold` proves holds the child's genuine whole-history fold.

Composed with that lemma: the field element sitting in the `latest_root` slot of a real cell, written
by a real turn, **is** `foldedFinalRoot … g steps`. The L2 commitment is on the L1, in a cell. -/
theorem readAccount_settle_is_applySettle
    (Proof : Type) (acc : SelfSettlement.RollupAccount) (s : SelfSettlement.SettleChildChain Proof)
    (k : RecordKernelState) (c : CellId)
    (hid   : fieldOf childIdSlot (k.cell c) = acc.childId)
    (hgen  : fieldOf childGenesisSlot (k.cell c) = acc.childGenesis)
    (hflag : fieldOf rootSetSlot (k.cell c) = 1)
    (hroot : fieldOf latestRootSlot (k.cell c) = s.finalizedRoot)
    (hh    : (fieldOf latestHeightSlot (k.cell c)).toNat = s.newHeight) :
    readAccount k c = SelfSettlement.applySettle Proof acc s := by
  simp only [readAccount, SelfSettlement.applySettle, hid, hgen, hflag, hroot, hh,
    if_neg (by decide : ¬ ((1 : Int) = 0))]

/-! ## §3 — the settlement's ACCOUNT WRITE as a REAL TURN.

`applySettle` commits the root and advances the height, preserving the registration. As a turn that
is three developer field writes, run left-to-right, all-or-nothing by `execFullTurnA`. -/

/-- **`settleTurn root height`** — the turn a settlement runs against the account cell: write the
finalized child root, raise the presence flag, advance the height. All-or-nothing. -/
def settleTurn (root height : Int) : List FullActionA :=
  [ .setFieldA settlerActor rollupCell latestRootSlot root
  , .setFieldA settlerActor rollupCell rootSetSlot 1
  , .setFieldA settlerActor rollupCell latestHeightSlot height ]

/-- **`registerTurn`** — the REGISTRATION turn: fix the child's nominal id and its genesis root. It
runs once, on a cell whose two identity slots are still at `0`; after it, `.immutable` freezes both. -/
def registerTurn (childId genesis : Int) : List FullActionA :=
  [ .setFieldA settlerActor rollupCell childIdSlot childId
  , .setFieldA settlerActor rollupCell childGenesisSlot genesis ]

/-- A settlement moves no value: every action is a `setFieldA`, whose per-asset delta is `0`. -/
theorem settleTurn_delta_zero (root height : Int) (b : AssetId) :
    turnLedgerDeltaAsset (settleTurn root height) b = 0 := by
  simp only [settleTurn, turnLedgerDeltaAsset, ledgerDeltaAsset, List.map, List.sum_cons,
    List.sum_nil, add_zero, zero_add]

/-- **`settle_conserves`** — a committed settlement is balance-neutral in every asset. Settling a
child chain moves a commitment, never value. -/
theorem settle_conserves (s s' : RecChainedState) (root height : Int) (b : AssetId)
    (h : execFullTurnA s (settleTurn root height) = some s') :
    recTotalAsset s'.kernel b = recTotalAsset s.kernel b := by
  have := execFullTurnA_conserves_per_asset s s' (settleTurn root height) b h
    (settleTurn_delta_zero root height b)
  exact this

/-! ## §4 — the EXECUTOR-ENFORCED teeth.

Each is a refusal by the shipped `stateStepDev` → `stateStepGuarded` → `caveatsAdmit` path. The
first is unconditional (it derives the caveat refusal from the installed caveat list); the rest take
the caveat verdict as a hypothesis, in the shape `Apps/GovernedNamespace` uses, and §5's `#guard`s
witness that the hypothesis is REAL on a registered account. -/

/-- The account's caveats REFUSE any write of the genesis slot other than the registered value —
derived from `rollupCaveats` itself, not assumed. -/
theorem genesis_caveat_refuses (k : RecordKernelState) (actor : CellId) (g' : Int)
    (hcav : k.slotCaveats rollupCell = rollupCaveats)
    (hne : g' ≠ fieldOf childGenesisSlot (k.cell rollupCell)) :
    caveatsAdmit k childGenesisSlot actor rollupCell g' = false := by
  simp only [caveatsAdmit, hcav, rollupCaveats, childIdSlot, childGenesisSlot, rootSetSlot,
    latestHeightSlot, latestRootSlot, SlotCaveat.field, SlotCaveat.eval]
  simpa using hne

/-- **`rollup_genesis_cannot_be_rehomed` (THE IDENTITY TOOTH, unconditional).** On a cell carrying
the rollup-account caveats, a turn that tries to write a DIFFERENT child genesis root is REFUSED by
the executor. The account cannot be re-pointed at a chain it did not register — so a freshly
fabricated child chain has nowhere to settle, and the account is keyed by CRYPTOGRAPHIC identity, by
construction and by the executor. The cell-layer twin of
`SelfSettlement.fabricated_genesis_cannot_settle`. -/
theorem rollup_genesis_cannot_be_rehomed (s : RecChainedState) (g' : Int)
    (hcav : s.kernel.slotCaveats rollupCell = rollupCaveats)
    (hne : g' ≠ fieldOf childGenesisSlot (s.kernel.cell rollupCell)) :
    execFullTurnA s [.setFieldA settlerActor rollupCell childGenesisSlot g'] = none := by
  have hnone := stateStepDev_caveat_violation_fails s childGenesisSlot settlerActor rollupCell g'
    (genesis_caveat_refuses s.kernel settlerActor g' hcav hne)
  simp only [execFullTurnA, execFullA, hnone]

/-- **`rollup_height_cannot_regress`.** A settlement claiming a height BELOW the settled one is
refused: `.monotonic latestHeightSlot` is checked by the executor on the write. (A replay at the
SAME height is NOT refused here — see `rollup_replay_at_same_height_is_admitted`.) -/
theorem rollup_height_cannot_regress (s : RecChainedState) (h' : Int)
    (hcav : caveatsAdmit s.kernel latestHeightSlot settlerActor rollupCell h' = false) :
    execFullTurnA s [.setFieldA settlerActor rollupCell latestHeightSlot h'] = none := by
  have hnone := stateStepDev_caveat_violation_fails s latestHeightSlot settlerActor rollupCell h' hcav
  simp only [execFullTurnA, execFullA, hnone]

/-- **`rollup_root_flag_cannot_unset` (THE NOMAD TOOTH).** The presence flag is `.monotonic`, so a
settled account cannot be driven back to "nothing proven". An adversary cannot clear the flag and
have a stale root slot read as unset — or a fresh one read as proven. -/
theorem rollup_root_flag_cannot_unset (s : RecChainedState) (v : Int)
    (hcav : caveatsAdmit s.kernel rootSetSlot settlerActor rollupCell v = false) :
    execFullTurnA s [.setFieldA settlerActor rollupCell rootSetSlot v] = none := by
  have hnone := stateStepDev_caveat_violation_fails s rootSetSlot settlerActor rollupCell v hcav
  simp only [execFullTurnA, execFullA, hnone]

/-- **`rollup_unauthorized_settler_refused`.** `.senderAuthorized latestRootSlot [settlerActor]` is
checked by the executor: a cell outside the authorized set cannot write the settled root. -/
theorem rollup_unauthorized_settler_refused (s : RecChainedState) (actor : CellId) (root : Int)
    (hcav : caveatsAdmit s.kernel latestRootSlot actor rollupCell root = false) :
    execFullTurnA s [.setFieldA actor rollupCell latestRootSlot root] = none := by
  have hnone := stateStepDev_caveat_violation_fails s latestRootSlot actor rollupCell root hcav
  simp only [execFullTurnA, execFullA, hnone]

/-- **`rollup_replay_at_same_height_is_admitted` (THE MEASURED LIMIT, stated as a fact).** The caveat
vocabulary has no strict-`<` member, so `.monotonic latestHeightSlot` ADMITS a re-write at the height
already settled. A replayed settlement is therefore refused by `SettleAccepts.monotone` and NOT by
the executor. This is the gap the missing `FullActionA` constructor would close; it is exhibited here
rather than left to be discovered. -/
theorem rollup_replay_at_same_height_is_admitted (k : RecordKernelState)
    (hcav : k.slotCaveats rollupCell = rollupCaveats) :
    caveatsAdmit k latestHeightSlot settlerActor rollupCell
      (fieldOf latestHeightSlot (k.cell rollupCell)) = true := by
  simp only [caveatsAdmit, hcav, rollupCaveats, childIdSlot, childGenesisSlot, rootSetSlot,
    latestHeightSlot, latestRootSlot, SlotCaveat.field, SlotCaveat.eval]
  simp

/-! ## §5 — NON-VACUITY: a REGISTERED account, and the settlement turn RUNNING on it.

`acct0` is a real chained state: cell 0 carries the rollup-account slots and `rollupCaveats`, cell 1
is a stranger. The `#guard`s below RUN `execFullTurnA` — the shipped executor — and read the
committed root back out of the cell. This is the difference between "the settlement proves" and "the
settlement's account write runs". -/

/-- The child chain's registered genesis root (its cryptographic identity). -/
abbrev demoGenesis : Int := 777

/-- A registered, not-yet-settled rollup account: genesis pinned, flag `0` (Nomad default). -/
def acct0 : RecChainedState :=
  { kernel :=
      { accounts := {0, 1}
        cell := fun c => if c = 0 then
                  .record [("balance", .int 0), (childIdSlot, .int 42),
                           (childGenesisSlot, .int demoGenesis), (latestRootSlot, .int 0),
                           (rootSetSlot, .int 0), (latestHeightSlot, .int 0)]
                else .record [("balance", .int 0)]
        caps := fun _ => []
        bal := fun c a => if c = 0 then (if a = 0 then 100 else 0)
                          else if c = 1 then (if a = 0 then 5 else 0) else 0
        slotCaveats := fun c => if c = 0 then rollupCaveats else [] }
    log := [] }

-- A FRESH account attests NOTHING: the Nomad default, read off the real cell.
#guard (readAccount acct0.kernel rollupCell).latestRoot == none
#guard (readAccount acct0.kernel rollupCell).childGenesis == demoGenesis

-- THE SETTLEMENT'S ACCOUNT WRITE RUNS on the shipped executor.
#guard (execFullTurnA acct0 (settleTurn 31337 9)).isSome

-- …and the committed cell holds the child's root, at the settled height, still registered.
#guard ((execFullTurnA acct0 (settleTurn 31337 9)).map
        (fun s => let a := readAccount s.kernel rollupCell
                  (a.childId, a.childGenesis, a.latestRoot, a.latestHeight))) ==
       some ((42 : Int), demoGenesis, some (31337 : Int), (9 : Nat))

-- Balance-neutral: settling moves a commitment, never value.
#guard ((execFullTurnA acct0 (settleTurn 31337 9)).map
        (fun s => recTotalAsset s.kernel 0)) == some 105

-- THE IDENTITY TOOTH BITES: a settlement cannot re-home the account to another chain.
#guard (caveatsAdmit acct0.kernel childGenesisSlot settlerActor rollupCell 999) == false
#guard ((execFullTurnA acct0
          [.setFieldA settlerActor rollupCell childGenesisSlot 999]).isSome) == false

-- THE NOMINAL ID IS FROZEN TOO.
#guard ((execFullTurnA acct0 [.setFieldA settlerActor rollupCell childIdSlot 43]).isSome) == false

-- A STRANGER CANNOT SETTLE.
#guard (caveatsAdmit acct0.kernel latestRootSlot strangerActor rollupCell 31337) == false
#guard ((execFullTurnA acct0
          [.setFieldA strangerActor rollupCell latestRootSlot 31337]).isSome) == false

-- …and the authorized settler CAN (the tooth is not vacuous by refusing everyone).
#guard (caveatsAdmit acct0.kernel latestRootSlot settlerActor rollupCell 31337)

/-- A SETTLED account: flag raised, height 9. -/
def acct1 : RecChainedState :=
  { acct0 with kernel :=
      { acct0.kernel with
        cell := fun c => if c = 0 then
                  .record [("balance", .int 0), (childIdSlot, .int 42),
                           (childGenesisSlot, .int demoGenesis), (latestRootSlot, .int 31337),
                           (rootSetSlot, .int 1), (latestHeightSlot, .int 9)]
                else .record [("balance", .int 0)] } }

-- THE NOMAD TOOTH BITES: a settled account cannot be driven back to "nothing proven".
#guard (caveatsAdmit acct1.kernel rootSetSlot settlerActor rollupCell 0) == false
#guard ((execFullTurnA acct1 [.setFieldA settlerActor rollupCell rootSetSlot 0]).isSome) == false

-- HEIGHT REGRESSION REFUSED…
#guard (caveatsAdmit acct1.kernel latestHeightSlot settlerActor rollupCell 4) == false
#guard ((execFullTurnA acct1 (settleTurn 999 4)).isSome) == false

-- …and a genuine advance COMMITS.
#guard ((execFullTurnA acct1 (settleTurn 424242 20)).map
        (fun s => let a := readAccount s.kernel rollupCell
                  (a.childId, a.childGenesis, a.latestRoot, a.latestHeight))) ==
       some ((42 : Int), demoGenesis, some (424242 : Int), (20 : Nat))

-- ⚑ THE MEASURED LIMIT, EXECUTED: a REPLAY at the ALREADY-SETTLED height is ADMITTED by the caveat
-- surface. `SettleAccepts.monotone` is what refuses it, and that leg is NOT executor-enforced until
-- the settlement has its own `FullActionA` constructor.
#guard (caveatsAdmit acct1.kernel latestHeightSlot settlerActor rollupCell 9)
#guard ((execFullTurnA acct1 (settleTurn 999 9)).isSome)

/-! ## §6 — axiom-hygiene pins. -/

#assert_axioms readAccount_unset_proves_nothing
#assert_axioms readAccount_settle_is_applySettle
#assert_axioms settleTurn_delta_zero
#assert_axioms settle_conserves
#assert_axioms genesis_caveat_refuses
#assert_axioms rollup_genesis_cannot_be_rehomed
#assert_axioms rollup_height_cannot_regress
#assert_axioms rollup_root_flag_cannot_unset
#assert_axioms rollup_unauthorized_settler_refused
#assert_axioms rollup_replay_at_same_height_is_admitted

end Dregg2.Distributed.RollupAccountCell
