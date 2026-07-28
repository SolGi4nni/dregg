/-
# Dregg2.Spec.GlobalValueConservation — `Value_a`, no-overlap by construction, and the
composition of the SIX local conservation invariants into one global statement.

**The gap this addresses** (named 2026-07-28): "we believe global conservation holds, and
nobody has proved it." Global conservation is an emergent property of SIX DISJOINT LOCAL
INVARIANTS plus a pairwise-interaction proof nobody had written. This file writes it — as far
as it can honestly be written today — and is explicit about the one place it cannot.

**Substrate, said out loud.** This is SPEC-LEVEL Lean, in the register of
`Dregg2.Spec.Conservation` (which this file imports and extends): a reasoning model over an
abstract ledger with abstract index types, not an `@[export]`-ed decision procedure and not an
AIR. The one object cited below that IS a circuit — `Dregg2.Circuit.CrossCellConservation` /
`CrossCellConserveDecision` / `CrossCellConserveRefine` — is CITED, never restated; nothing
here re-derives or "translation-validates" a Rust AIR. The disjointness fact in §4 is a claim
about `turn/src/executor/apply.rs` at HEAD, checked by reading (grep evidence cited), and used
here as an explicit HYPOTHESIS, not proved in Lean — formalizing the 36-arm `apply_effect`
dispatch itself would be exactly the Rust-shaped-drift this repo's law forbids applied to the
executor instead of the circuit.

## The six invariants, re-verified at HEAD (real `file:line`, not inherited from the brief)

1. **Per-cell non-negativity floor** — a FAMILY, one per DEBITING balance-mutating handler,
   same shape (`current − amount`, floored at `0`, overflow-checked on credit), not one site —
   and, corrected on a re-read (not inherited from the brief's line numbers), it does NOT cover
   every balance-mutating handler:
   - `Action::balance_change`: `turn/src/executor/execute_tree.rs:1008-1028`
     (`checked_add` against `BalanceChangeUnderflow`/`BalanceOverflow` — this ONE path is
     signed-delta, not debit/credit-shaped, so its "floor" is the `new_bal ≥ 0 ∨ delta ≥ 0`
     disjunction at `:1009`).
   - `Effect::Transfer`: the SOURCE leg floors at zero, `apply.rs:646-655`
     (`InsufficientBalance`); the destination leg is credit-only, `:705-708` (overflow, no
     floor needed).
   - `Effect::Burn`: the HOLDER leg floors at zero, `apply.rs:3618-3629`
     (`cm.state.debit_balance(amount)`); the well's credit leg (`:3700-3708`) is credit-only.
   - `Effect::Mint`: **has NO floored leg.** The well's debit (`apply.rs:3927`,
     `well.state.well_debit_balance(amount)`) is DELIBERATELY negative-capable — the well
     carries `−supply` and must be able to go MORE negative — so it is overflow-checked only,
     never floored; the recipient's credit (`:3942`) needs no floor either. A prior draft of
     this file claimed a symmetric "well debit floor" for mint; there isn't one, and there
     should not be — re-verified against `apply.rs:3915-3936` before writing this sentence.
   A floor is NOT a conservation law — it forbids negative balances (where one applies at
   all), it does not force `Σδ=0`.

2. **Scalar asset-blind `excess == 0`** — `turn/src/executor/execute.rs:1256`
   (`if excess != 0 { … TurnError::ExcessNotZero }`), fed by
   `execute_tree.rs:1038` (`*excess = excess.checked_sub(delta)…`). Proves `Σ_turn δ = 0`
   across EVERY asset combined — necessary, not sufficient (a cross-asset teleport nets to
   zero here; caught only by #3).

3. **Per-asset `Σδ = 0` — THE ONE VERIFIED GATE.** `execute.rs:1296` calls
   `Executor::check_per_asset_conservation_by_asset_id` (`atomic.rs:509-530`), which (a) calls
   `dregg_circuit::block_conservation::assert_asset_classes_injective` (refuses two distinct
   32-byte asset ids folding to one class — `atomic.rs:513`, the wrapper
   `refuse_colliding_asset_classes` at `atomic.rs:427-442`), then (b) folds via
   `fold_token_id_to_asset` and delegates to `check_per_asset_conservation_by_asset`
   (`atomic.rs:603-663`), which on a native release build routes to
   `conservation_oracle::installed_conservation_oracle().conserves(&rows)` — backed by the
   Lean `@[export dregg_cross_cell_conserves]`
   (`Dregg2.Circuit.CrossCellConserveDecision.conservesFFI`), proved the faithful runtime
   image of the committed AIR boundary by
   `CrossCellConserveRefine.decision_conserves_iff_air_boundary` (`CrossCellConserveRefine.lean:93`).
   **Fail-closed** if no oracle is installed on native release (`atomic.rs:655-658`,
   `Err(ConservationGateUnavailable)`, the Rust fallback not even compiled). The only member of
   the six that is Lean-DECIDED at runtime, not merely Lean-inspired.

4. **Note-value conservation** — `turn/src/executor/finalize.rs:159-189`
   (`check_note_conservation`, dispatching Cleartext / Committed / Mixed / Empty via
   `detect_commitment_mode`). Cleartext: per-`asset_type` `Σinputs = Σoutputs` within the turn
   (`:169-180`). Mixed: a HARD REFUSAL (`:186`, `Err((0,0,0))`) — a refusal, not a proof of
   non-interaction; see §6.

5. **Shielded Pedersen conservation** — `apply.rs:487-489` dispatches
   `Effect::ShieldedTransfer` to `apply_shielded_transfer` (`apply.rs:1793-1904`), whose real
   gates (the STARK join, `Σ C_in = Σ C_out`, range proofs) live OUTSIDE this crate in the
   injected `ShieldedTransferVerifier`. The handler itself touches **no cell, no `&mut
   Ledger`** (confirmed by its signature, `apply.rs:1793-1798`) — only `note_nullifiers`
   (`:1828-1857`) and `note_shielded` (`:1882-1890`).

6. **The `was_burn` disclosure walk** — `turn/src/executor/mod.rs:75-91`
   (`effect_is_burn`/`tree_has_burn_effect`), consumed at `finalize.rs:896` to set the
   receipt's `was_burn` flag. DISCLOSURE bookkeeping (what the receipt SAYS happened), not
   itself a conservation check — a burn's actual `Σδ=0` is #1/#3, the well-paired
   holder↔well move at `apply.rs:3542-3711`.

## §4 The exhaustive disjointness fact (the load-bearing hypothesis below)

Every `fn apply_*` handler in `turn/src/executor/apply.rs` was read. Balance-mutating handlers
(`set_balance`/`debit_balance`/`credit_balance`) and note-domain-mutating handlers
(`.note_nullifiers`/`.note_commitments`/`.note_shielded`/`.bridged_nullifiers` `.lock()`) are
LINE-DISJOINT:

  balance:  `apply_transfer` (712-723), `apply_burn` (3618-3708), `apply_mint` (3900s-3950),
            `execute_tree.rs`'s `Action::balance_change` path (1031-1033)
  notes:    `apply_note_spend` (1593, 1710), `apply_shielded_transfer` (1828, 1882),
            `apply_note_create` (2293), `apply_bridge_mint` (`bridged_nullifiers` only,
            2456-2470 — credits NO cell, inserts NO note commitment; its own conservation
            entry, `finalize.rs:534-550`, folds it in as a self-balancing no-op)

No `apply_*` function appears in both lists. `apply_exercise_via_capability` (2500-2767)
recurses into `inner_effects` through the SAME dispatch, so it inherits the property
structurally. This is used below as `EffectSite` — a classifier with exactly the shape the
Rust dispatch has, cited, not re-derived.

## §5 What is (and is not) namespace-comparable

* **Balances and notes share NO namespace.** A cell's asset is a 32-byte `AssetId` folded
  (lossily, ~31 bits) by `fold_token_id_to_asset` (`block_conservation.rs:171`) for the
  balance-conservation partition; a note's asset is a free-form `u64` `asset_type` chosen by
  whoever builds the effect (`action.rs:1119,1139`), never derived from any cell's `asset()`
  (verified: zero co-occurrences of `fold_token_id_to_asset` with `asset_type` anywhere in
  `turn/src`/`cell/src`). Modeled below as `AssetId`/`AssetType` — two UNRELATED types; no
  coercion is declared between them, which is the point.
* **Shielded notes are TYPE-DISJOINT from cleartext/committed notes in the real system**:
  `ShieldedNoteCommitment` is a distinct newtype from `NoteCommitment`
  (`cell/src/note.rs:33-44`: "prevents a hiding shielded commitment from ever being fed to a
  cleartext-value leaf, and vice versa, AT THE TYPE LEVEL"), its own accumulator
  (`ShieldedNoteSet` vs `CommitmentSet`). Modeled below with a genuinely separate `Shielded`
  index type: disjointness by TYPE, the strongest available kind.
* **Cleartext and committed notes are NOT type-disjoint** — both live in the same
  `NoteCommitment`/`CommitmentSet`; only a PER-TURN refusal (`finalize.rs:186`,
  `NoteCommitmentMode::Mixed ⇒ Err`) keeps one turn's notes from mixing modes. Modeled below
  with ONE `NoteId` type and a TOTAL `mode` function (a note's mode is fixed at creation and
  never both); the composition theorem for this pair is stated over ADMITTED (non-Mixed)
  turns — a SCOPE restriction, not a stronger claim. See §6's honesty note.
-/
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Dregg2.Spec.Conservation

namespace Dregg2.Spec.GlobalValueConservation

open scoped BigOperators

/-! ## §1 — Types, abstract and `DecidableEq`.

`AssetId` (cell currency) and `AssetType` (note label) are DECLARED SEPARATE — no coercion
between them exists in the real system (§5), and none is introduced here. `Shielded` is a
type genuinely distinct from `NoteId` (§5, the real `ShieldedNoteCommitment` newtype). -/

variable {Cell NoteId Shielded AssetId AssetType : Type*}
variable [DecidableEq Cell] [DecidableEq NoteId] [DecidableEq Shielded]
variable [DecidableEq AssetId] [DecidableEq AssetType]

/-- A note's mode, fixed at creation (mirrors: whether the creating `NoteCreate` effect
carried a `value_commitment`, §5). Exactly two constructors — a note is never both. -/
inductive NoteMode where
  | Cleartext
  | Committed
  deriving DecidableEq, Repr

/-- **The ledger state.** Balances keyed by `Cell`, each holding exactly ONE `AssetId`
(`cellAsset` — the real `birth_asset` invariant, `apply.rs:1083-1088`, cited not re-derived).
Notes keyed by `NoteId` with a TOTAL `noteMode` (a note cannot be both cleartext and
committed — a fact about the function, see §5's honesty note on what this does and does not
prove). Shielded objects keyed by the SEPARATE type `Shielded`. -/
structure LedgerState (Cell NoteId Shielded AssetId AssetType : Type*) where
  liveCells : Finset Cell
  cellAsset : Cell → AssetId
  balance : Cell → ℤ
  liveNotes : Finset NoteId
  noteMode : NoteId → NoteMode
  noteAsset : NoteId → AssetType
  clearValue : NoteId → ℤ
  liveShielded : Finset Shielded
  shieldedAsset : Shielded → AssetType

/-! ## §2 — An `Opening`: the ghost cleartext value of a committed/shielded object.

Mirrors `Dregg2.Spec.Conservation`'s `h : Cleartext →+ Commitment` parameter (the
`committed_iff_cleartext` section): the private channels' value is NEVER computable from
`LedgerState` alone — that is what "committed"/"shielded" MEANS. An `Opening` is the
reasoning-time witness that consistent openings exist; nothing executable computes one. -/

/-- A chosen (reasoning-time only) opening of every committed/shielded object to its ghost
`ℤ` value. -/
structure Opening (NoteId Shielded : Type*) where
  openNote : NoteId → ℤ
  openShielded : Shielded → ℤ

/-! ## §3 — Per-channel state totals, each keyed by its OWN namespace. -/

/-- Total balance of asset `a` across every live cell holding it. -/
def valueBal (s : LedgerState Cell NoteId Shielded AssetId AssetType) (a : AssetId) : ℤ :=
  ∑ c ∈ s.liveCells.filter (fun c => s.cellAsset c = a), s.balance c

/-- The live notes labelled `b`, of EITHER mode (the set §6 splits). -/
def notesOf (s : LedgerState Cell NoteId Shielded AssetId AssetType) (b : AssetType) :
    Finset NoteId :=
  s.liveNotes.filter (fun n => s.noteAsset n = b)

/-- Total CLEARTEXT-note value of label `b`. -/
def valueClear (s : LedgerState Cell NoteId Shielded AssetId AssetType) (b : AssetType) : ℤ :=
  ∑ n ∈ (notesOf s b).filter (fun n => s.noteMode n = .Cleartext), s.clearValue n

/-- Total COMMITTED-note GHOST value of label `b`, under opening `op`. -/
def valueCommit (op : Opening NoteId Shielded)
    (s : LedgerState Cell NoteId Shielded AssetId AssetType) (b : AssetType) : ℤ :=
  ∑ n ∈ (notesOf s b).filter (fun n => s.noteMode n = .Committed), op.openNote n

/-- Total SHIELDED GHOST value of label `b`, under opening `op`. Indexed over `Shielded`, a
type genuinely distinct from `NoteId` — no filter needed to keep it apart from the other
three sums; the type system already does it. -/
def valueShield (op : Opening NoteId Shielded)
    (s : LedgerState Cell NoteId Shielded AssetId AssetType) (b : AssetType) : ℤ :=
  ∑ m ∈ s.liveShielded.filter (fun m => s.shieldedAsset m = b), op.openShielded m

/-! ## §4 — `Value_a`: the four channels, once each, no overlap BY CONSTRUCTION.

The no-overlap argument has three DIFFERENT strengths, matched to what is actually true of
the real system (§5) — this is deliberate, not uniform for tidiness:

1. `valueBal` vs the three note/shielded sums: disjoint because they are sums over
   DIFFERENT TYPES (`Cell` vs `NoteId`/`Shielded`) — a type error, not a side condition, to
   even ask whether a cell "is" a note.
2. `valueShield` vs `valueClear`/`valueCommit`: disjoint for the SAME type-level reason
   (`Shielded ≠ NoteId`), matching the real `ShieldedNoteCommitment`/`NoteCommitment` newtype
   split.
3. `valueClear` vs `valueCommit`: disjoint because `noteMode` is a TOTAL FUNCTION — proved
   below (`clear_committed_disjoint`), not assumed. This is the one honest exception: the
   underlying `NoteId` universe is SHARED, and the proof is exactly as strong as "no note has
   two modes", which is real (a mode is fixed at note creation) but weaker than a type wall —
   see §6. -/

omit [DecidableEq Cell] [DecidableEq NoteId] [DecidableEq Shielded] [DecidableEq AssetId] in
theorem clear_committed_disjoint
    (s : LedgerState Cell NoteId Shielded AssetId AssetType) (b : AssetType) :
    Disjoint ((notesOf s b).filter (fun n => s.noteMode n = .Cleartext))
             ((notesOf s b).filter (fun n => s.noteMode n = .Committed)) := by
  rw [Finset.disjoint_left]
  intro n hn1 hn2
  simp only [Finset.mem_filter] at hn1 hn2
  rw [hn1.2] at hn2
  exact absurd hn2.2 (by decide)

omit [DecidableEq Cell] [DecidableEq Shielded] [DecidableEq AssetId] in
theorem notesOf_eq_union
    (s : LedgerState Cell NoteId Shielded AssetId AssetType) (b : AssetType) :
    notesOf s b = (notesOf s b).filter (fun n => s.noteMode n = .Cleartext) ∪
                  (notesOf s b).filter (fun n => s.noteMode n = .Committed) := by
  ext n
  simp only [Finset.mem_union, Finset.mem_filter]
  constructor
  · intro hn
    cases h : s.noteMode n with
    | Cleartext => exact Or.inl ⟨hn, rfl⟩
    | Committed => exact Or.inr ⟨hn, rfl⟩
  · rintro (⟨hn, _⟩ | ⟨hn, _⟩) <;> exact hn

omit [DecidableEq Cell] [DecidableEq Shielded] [DecidableEq AssetId] in
/-- **THE NO-OVERLAP THEOREM for notes.** `valueClear + valueCommit` (under any opening) is
EXACTLY the total over `notesOf s b` read back through the (mode-dependent) per-note value —
i.e. every live note of label `b` is counted EXACTLY ONCE, whichever mode it is in. Proved
from `noteMode`'s totality (`notesOf_eq_union`) and the disjointness it forces
(`clear_committed_disjoint`), via `Finset.sum_union` — not asserted. -/
theorem valueClear_add_valueCommit_eq_notesOf_readback
    (op : Opening NoteId Shielded) (s : LedgerState Cell NoteId Shielded AssetId AssetType)
    (b : AssetType) :
    valueClear s b + valueCommit op s b
      = ∑ n ∈ notesOf s b,
          (if s.noteMode n = .Cleartext then s.clearValue n else op.openNote n) := by
  unfold valueClear valueCommit
  conv_rhs => rw [notesOf_eq_union s b]
  rw [Finset.sum_union (clear_committed_disjoint s b)]
  congr 1
  · apply Finset.sum_congr rfl
    intro n hn
    simp only [Finset.mem_filter] at hn
    simp [hn.2]
  · apply Finset.sum_congr rfl
    intro n hn
    simp only [Finset.mem_filter] at hn
    simp [hn.2]

/-- **`Value_a`** — the total conserved quantity for balance-asset `a`, given a CHOSEN
correspondence `corr : AssetId → AssetType` naming which note label counts as "the same
economic asset" as `a`, and an opening `op` for the private channels.

⚠ **`corr` IS THE HONEST GAP, not a modeling convenience.** The deployed protocol supplies NO
such function: no code anywhere in `turn/src`/`cell/src` maps a 32-byte `AssetId` to a note
`asset_type` (§5). `Value_a` is therefore PARAMETRIC in `corr`; a different choice gives a
different "conserved total" over the SAME real ledger, and nothing in the protocol picks one
out. §6 states exactly what does and does not survive this. -/
def Value (corr : AssetId → AssetType) (op : Opening NoteId Shielded)
    (s : LedgerState Cell NoteId Shielded AssetId AssetType) (a : AssetId) : ℤ :=
  valueBal s a + valueClear s (corr a) + valueCommit op s (corr a) + valueShield op s (corr a)

/-! ## §5 — Effect sites: the abstract classifier witnessing §4's disjointness fact.

`EffectSite` is NOT a port of the real 36-variant `Effect` (that would be exactly the
"translation validation" this repo's law forbids). It is the SMALLEST abstract vocabulary
that can witness the shape the Rust dispatch actually has (§ "the exhaustive disjointness
fact"): every constructor names EXACTLY the channel it may move value in, by TYPE — there is
no constructor whose fields mention two channels' state at once, mirroring that no
`apply_*` handler's body mentions two channels' mutation calls at once. -/

/-- The one channel (of four) a step may move value in — `Neutral` for the twenty-odd
effects (`SetField`, `GrantCapability`, `Promise`, …) that move no conserved quantity at
all (mirrors `LinearityClass.Neutral`, §1 of `Dregg2.Spec.Conservation`). -/
inductive Channel where
  | balance
  | clearNote
  | committedNote
  | shielded
  | neutral
  deriving DecidableEq, Repr

/-- **The single-channel hypothesis for one step.** `chan` names which of the four channels
(or none) a step touches; whichever of `balance_inv`/`clear_inv`/`committed_inv`/`shielded_inv`
matches `chan` is that channel's OWN local invariant (one of #1-#6) already having been
discharged elsewhere — this file does not re-derive #1-#6, it consumes them. A step with
`chan = .neutral` touches no `Value` summand at all. -/
structure Step where
  pre : LedgerState Cell NoteId Shielded AssetId AssetType
  post : LedgerState Cell NoteId Shielded AssetId AssetType
  chan : Channel
  /-- The touched channel's own asset label (an `AssetId` if `chan = .balance`, else an
  `AssetType`) is irrelevant to the composition proof below — `Value corr op` is checked at
  a FIXED `a`, and whichever channel `corr a` does not name is untouched by hypothesis. -/
  balance_inv : chan = .balance → ∀ a, valueBal post a = valueBal pre a
  clear_inv : chan = .clearNote → ∀ b, valueClear post b = valueClear pre b
  committed_inv : chan = .committedNote →
    ∀ (op : Opening NoteId Shielded) b, valueCommit op post b = valueCommit op pre b
  shielded_inv : chan = .shielded →
    ∀ (op : Opening NoteId Shielded) b, valueShield op post b = valueShield op pre b
  /-- The disjointness fact (§4 of the header): a step touching channel `chan` leaves EVERY
  OTHER channel's totals pointwise unchanged. This is the Lean encoding of "no `apply_*`
  handler mutates two channels" — a HYPOTHESIS here, cited from the Rust reading, not
  proved from a ported `Effect` type. -/
  balance_untouched : chan ≠ .balance → ∀ a, valueBal post a = valueBal pre a
  clear_untouched : chan ≠ .clearNote → ∀ b, valueClear post b = valueClear pre b
  committed_untouched : chan ≠ .committedNote →
    ∀ (op : Opening NoteId Shielded) b, valueCommit op post b = valueCommit op pre b
  shielded_untouched : chan ≠ .shielded →
    ∀ (op : Opening NoteId Shielded) b, valueShield op post b = valueShield op pre b

omit [DecidableEq Cell] [DecidableEq NoteId] [DecidableEq Shielded] in
/-- Every channel of a `Step` is pointwise unchanged, whichever channel it named — the
`chan = c` case from the local invariant, every other case from `_untouched`. Packages the
eight fields of `Step` into the four equalities the composition theorem needs. -/
theorem Step.all_channels_unchanged (st : Step (Cell:=Cell) (NoteId:=NoteId) (Shielded:=Shielded) (AssetId:=AssetId) (AssetType:=AssetType))
    (op : Opening NoteId Shielded) (a : AssetId) (b : AssetType) :
    valueBal st.post a = valueBal st.pre a ∧
    valueClear st.post b = valueClear st.pre b ∧
    valueCommit op st.post b = valueCommit op st.pre b ∧
    valueShield op st.post b = valueShield op st.pre b := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rcases eq_or_ne st.chan .balance with h | h
    · exact st.balance_inv h a
    · exact st.balance_untouched h a
  · rcases eq_or_ne st.chan .clearNote with h | h
    · exact st.clear_inv h b
    · exact st.clear_untouched h b
  · rcases eq_or_ne st.chan .committedNote with h | h
    · exact st.committed_inv h op b
    · exact st.committed_untouched h op b
  · rcases eq_or_ne st.chan .shielded with h | h
    · exact st.shielded_inv h op b
    · exact st.shielded_untouched h op b

omit [DecidableEq Cell] [DecidableEq NoteId] [DecidableEq Shielded] in
/-- **THE COMPOSITION THEOREM.** A single-channel step (§ `Step`) leaves `Value corr op`
unchanged at every asset `a` — the four channels compose into one conserved total, GIVEN
each channel's own invariant (consumed, not re-proved) and the disjointness hypothesis (cited
from the Rust reading, §4 of the header). This is the theorem the brief asked for: what six
local `Δ_c = 0` facts, plus "each effect touches exactly one channel", buy you globally. -/
theorem Value_conserved_of_step (st : Step (Cell:=Cell) (NoteId:=NoteId) (Shielded:=Shielded) (AssetId:=AssetId) (AssetType:=AssetType))
    (corr : AssetId → AssetType) (op : Opening NoteId Shielded) (a : AssetId) :
    Value corr op st.post a = Value corr op st.pre a := by
  obtain ⟨hbal, hclear, hcommit, hshield⟩ := st.all_channels_unchanged op a (corr a)
  unfold Value
  rw [hbal, hclear, hcommit, hshield]

/-! ## §6 — The four named pairs, addressed explicitly. -/

/-! ### (balance, shielded) — CLOSED, by TYPE. Not merely by hypothesis: `Shielded ≠ NoteId`
and `valueBal`/`valueShield` are sums over `Cell`/`Shielded` respectively, so a `.balance`
step's `shielded_untouched` obligation is not even a claim ABOUT overlap — there is no shared
index for the two sums to overlap ON. `Value_conserved_of_step` already covers it; this
remark records the STRENGTH of the closure (type-level, not merely a checked hypothesis). -/

/-! ### (balance, supply) — CLOSED BY COLLAPSE, not by a new proof. Since 2026-07-28
(`07472176c`) the deployed supply model has NO separate supply channel: a mint/burn is a
holder↔issuer-well MOVE, and the well IS an ordinary `Cell` in the SAME `AssetId`
(`apply.rs:3542-3711` for burn, the mint dual). So "supply" is not a fifth summand of `Value`
— it is two rows of `valueBal` that already cancel under invariant #3 (the well's debit and
the holder's credit are both folded into the SAME per-asset `Σδ=0` check). The witness below
is the mint-shaped two-cell move, verified to conserve `valueBal` by the SAME mechanism as an
ordinary transfer (no new machinery). -/

section MintIsBalance

/-- A minimal concrete two-cell ledger (holder = `0`, well = `1`), single asset, no notes, no
shielded objects — just enough state to exhibit the mint/burn well-pairing pattern. -/
private def demoState (holderBal wellBal : ℤ) :
    LedgerState (Fin 2) (Fin 0) (Fin 0) (Fin 1) (Fin 1) where
  liveCells := {0, 1}
  cellAsset := fun _ => 0
  balance := fun c => if c = 0 then holderBal else wellBal
  liveNotes := ∅
  noteMode := fun n => n.elim0
  noteAsset := fun n => n.elim0
  clearValue := fun n => n.elim0
  liveShielded := ∅
  shieldedAsset := fun m => m.elim0

/-- **POLE 1 (HOLDS).** A mint/burn-shaped move — holder credited `amt`, the issuer WELL
debited the SAME `amt`, same asset — conserves `valueBal`. This is exactly what
`apply_mint`/`apply_burn`'s well-pairing does (§6); no machinery beyond invariant #3 is
needed for (balance, supply). -/
theorem mint_shaped_move_conserves_valueBal (amt : ℤ) :
    valueBal (demoState (100 + amt) (0 - amt)) 0 = valueBal (demoState 100 0) 0 := by
  unfold valueBal demoState
  simp [Finset.sum_pair (show (0 : Fin 2) ≠ 1 by decide)]

/-- **POLE 2 (FAILS).** Drop the well-pairing — credit the holder without debiting the well
— and `valueBal` visibly changes for any nonzero `amt`. This is exactly the UNDISCLOSED mint
invariant #3 exists to refuse; the theorem above is not vacuous. -/
theorem undisclosed_credit_breaks_valueBal (amt : ℤ) (hamt : amt ≠ 0) :
    valueBal (demoState (100 + amt) 0) 0 ≠ valueBal (demoState 100 0) 0 := by
  unfold valueBal demoState
  simp [Finset.sum_pair (show (0 : Fin 2) ≠ 1 by decide)]
  omega

end MintIsBalance

/-! ### (cleartext, committed notes) — CLOSED FOR ADMITTED TURNS, by REFUSAL, not by a proof
of non-interaction. `valueClear_add_valueCommit_eq_notesOf_readback` (§4) is unconditional —
it holds for ANY `LedgerState`, because `noteMode` is total BY THE TYPE OF THE FUNCTION. What
it does NOT do, and what the real system does not do either, is prove that a turn attempting
to mix modes could not be CONSTRUCTED — `finalize.rs:186` REFUSES such a turn
(`NoteCommitmentMode::Mixed ⇒ Err`), it does not witness that no state reachable from a
well-typed `Step` sequence could arise from mixed-mode intent. The distinction: `noteMode` is
total because in THIS FILE every `NoteId` already has exactly one mode by construction of the
type `NoteId → NoteMode` — the real question ("could an attacker submit a turn that tries to
spend a note as if it had the other mode") is answered by the REFUSAL (`Mixed ⇒ Err`), a
different and weaker mechanism than a type wall, and this file does not model turn admission
so it cannot strengthen that. Recorded here so a reader does not mistake
`clear_committed_disjoint` for more than it is. -/

/-! ### (balance, notes) — NO LIVE COUNTEREXAMPLE FOUND; a DEFINITIONAL gap remains,
precisely where the brief said to look.

**What was checked.** Every `apply_*` handler in `turn/src/executor/apply.rs` was read
(§4 of the header). Balance-mutation and note-mutation code are LINE-DISJOINT: no effect
handler both moves a balance and moves a note. Concretely: `Effect::BridgeMint`
(`apply.rs:2335-2481`) — the one effect whose OWN doc comment (`action.rs:1182-1188`) claims
to "credit the value to the receiving cell" — does no such thing; it verifies a STARK and
inserts one `bridged_nullifiers` entry, touching no cell and no note commitment, and its
conservation-collector entry (`finalize.rs:534-550`) makes it a self-balancing no-op (adds
`portable_proof.value` to BOTH inputs and outputs under its own `asset_type`). So: within the
CURRENT 36-effect vocabulary, `Step.balance_untouched`/`clear_untouched` are not merely
assumed — they are TRUE of every real handler, checked by exhaustive reading. There is no turn
that conserves `valueBal` and `valueClear` independently and fails to conserve their sum,
because nothing moves both.

**What remains open, and it is a real one.** `Value_a` (§4) required a CHOSEN `corr : AssetId
→ AssetType` to even be stated, because the protocol supplies none (§5). This is not a gap in
the proof technique — it is that "the total value of economic asset X, counting its balance-
form and its note-form together" is not currently an expression the protocol can state, let
alone conserve. The moment any future effect (a wrap/unwrap, a bridge, a "deposit balance as a
note" verb — `EXECUTED-PATH-SYMMETRY-2026-07-26.md` already flags token issuance /
launchpad / house-via-factory as roadmapped) introduces a MOVE between the two namespaces
without a matching acceptance into `Value`'s corr-indexed sum on BOTH legs, `Step`'s
disjointness hypothesis for that effect is FALSE, `Value_conserved_of_step` does not apply to
it, and the composition breaks by exactly the shape the brief anticipated: a lossy ~31-bit
fold on one side (`fold_token_id_to_asset`) and a free `u64` on the other admit an attacker-
or product-chosen `corr` that merges two unrelated ledgers into "one asset" for accounting
purposes while the protocol enforces conservation on neither leg of that identification. This
is a PROTOCOL-DESIGN gap (no channel-crossing verb exists to even be unsound YET), not a proof
gap — recorded per the brief's own instruction: "that is a defect in the protocol, not in the
proof — say so loudly." -/

/-! ## Axiom hygiene — pin the clean keystones. No `sorry`, no `axiom`, no `native_decide`. -/

#assert_axioms clear_committed_disjoint
#assert_axioms notesOf_eq_union
#assert_axioms valueClear_add_valueCommit_eq_notesOf_readback
#assert_axioms Step.all_channels_unchanged
#assert_axioms Value_conserved_of_step
#assert_axioms mint_shaped_move_conserves_valueBal
#assert_axioms undisclosed_credit_breaks_valueBal

end Dregg2.Spec.GlobalValueConservation
