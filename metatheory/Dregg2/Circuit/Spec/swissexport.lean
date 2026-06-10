/-
# Dregg2.Circuit.Spec.swissexport — INDEPENDENT full-state spec + executor⟺spec for the
  dregg2 swiss-export effect family (`exportSturdyRefA`).

This leaf module is the `Transfer.lean` reference pattern (`TransferSpec` + `recKExec_iff_spec` +
`recTransfer_correct`) carried to the swiss-table CapTP EXPORT arm of `execFullA`:

  * `exportSturdyRefA sw actor exporter target rights` ⟶ `swissExportChainA s sw actor exporter target rights`
      — MINT a fresh sturdy ref: insert a `SwissRecord` keyed by swiss number `sw`, pointing at
        `target`, carrying the exported `rights`, with `refcount := 1` and no bound cert. GATED on
        a THREE-way admissibility conjunction:
          (A1) AUTHORITY — `stateAuthB s.kernel.caps actor exporter` (the actor holds authority over
               the exporting cell, read off the committed c-list);
          (A2) FRESHNESS — `findSwiss s.kernel.swiss sw = none` (the swiss number is NOT already in
               use — no duplicate export, `apply.rs:3879`);
          (A3) NON-AMPLIFICATION — `rightsNarrowerOrEqual rights (heldAuths s.kernel exporter)` (the
               exported `rights` are `⊆` the rights the exporter GENUINELY holds, read off the
               ADVERSARY-UNCONTROLLABLE committed state `k.caps exporter` — NOT a caller-supplied
               `held` parameter. This is the soundness fix: a bare-authority actor cannot mint a
               sturdy ref carrying rights its cell never held, `apply.rs:3917`).
        Fail-closed on any of the three. On commit it prepends the new `SwissRecord` to `kernel.swiss`
        and prepends an authority receipt `{ actor, src := exporter, dst := exporter, amt := 0 }` to
        the log.

We state an INDEPENDENT declarative full-state spec — the THREE-way admissibility guard ∧ the EXACT
post-state on the touched components (`kernel.swiss` + `log`) ∧ EVERY OTHER `RecChainedState` field
LITERALLY unchanged (the FRAME). `RecChainedState` has TWO fields: `kernel : RecordKernelState` and
`log : List Turn`. The kernel has SEVENTEEN fields — `accounts cell caps escrows nullifiers revoked
commitments bal queues swiss slotCaveats factories lifecycle deathCert delegate delegations
sealedBoxes` — so the FRAME enumerates the SIXTEEN non-`swiss` kernel fields plus the kernel↔kernel
`swiss` rewrite, plus the `log` head-cons. NO frame clause names the executor
(`execFullA`/`swissExportChainA`/`swissExportK`); the post-`swiss` clause uses only the pure data
constructor `SwissRecord.mk` consed onto the pre-state `swiss` list, so the spec is genuinely
independent of the executor it validates.

The `→` direction of `export_iff_spec` VALIDATES the executor against the independent spec: all 17
kernel fields + the log are checked, so had the arm silently mutated `bal`/`nullifiers`/`caps`/…
a frame clause would make the proof FAIL. (None do — see `frameGaps = []` in the run report.)
-/
import Dregg2.Exec.TurnExecutorFull

namespace Dregg2.Circuit.Spec.SwissExport

open Dregg2.Exec
open Dregg2.Exec.TurnExecutorFull
open Dregg2.Exec.EffectsState (stateAuthB)
open Dregg2.Authority (Caps Cap Auth)

/-! ## §1 — the admissibility guard `exportSturdyRefA` checks (the THREE-way conjunction).

`execFullA s (.exportSturdyRefA sw actor exporter target rights)`
  `= swissExportChainA s sw actor exporter target rights`, which is

    if stateAuthB s.kernel.caps actor exporter = true then
      match swissExportK s.kernel sw exporter target rights with
      | some k' => some { kernel := k', log := authReceipt :: s.log }
      | none    => none
    else none

and `swissExportK k sw exporter target rights` itself is

    match findSwiss k.swiss sw with
    | some _ => none
    | none   => if rightsNarrowerOrEqual rights (heldAuths k exporter)
                then some { k with swiss := newRecord :: k.swiss } else none

so the whole arm commits IFF all THREE of authority, freshness, non-amplification hold. -/

/-- **The receipt row** a committed export prepends to the log (the chainlink): an authority receipt
binding the `actor`, with `src = dst = exporter` and `amt = 0` (a swiss export moves a REFERENCE, not
balance). Stated as DATA, independent of the executor. -/
def exportReceipt (actor exporter : CellId) : Turn :=
  { actor := actor, src := exporter, dst := exporter, amt := 0 }

/-- **The freshly-minted swiss record** a committed export inserts: keyed by `sw`, minted by
`exporter`, pointing at `target`, carrying the exported `rights`, with `refcount := 1` (one live ref)
and no bound cert. Stated as DATA (the pure `SwissRecord.mk`), independent of the executor. -/
def exportRecord (sw : Nat) (exporter target : CellId) (rights : List Auth) : SwissRecord :=
  { swiss := sw, exporter := exporter, target := target, rights := rights, refcount := 1, cert := none }

/-- **The admissibility guard `exportSturdyRefA` checks**, as a `Prop`: the THREE-way conjunction of
AUTHORITY (the actor holds authority over the exporting cell), FRESHNESS (the swiss number is not
already in use), and NON-AMPLIFICATION (the exported `rights` are `⊆` the exporter's GENUINELY-held
rights, read off the committed c-list — NOT a caller-supplied bound). Stated INDEPENDENTLY (over the
pre-state's `caps`/`swiss`), NOT by referencing the executor. -/
def ExportGuard (s : RecChainedState) (sw : Nat) (actor exporter : CellId) (rights : List Auth) : Prop :=
  stateAuthB s.kernel.caps actor exporter = true
  ∧ findSwiss s.kernel.swiss sw = none
  ∧ rightsNarrowerOrEqual rights (heldAuths s.kernel exporter) = true

/-! ## §2 — the post-state helper validated DECLARATIVELY (the `recTransfer_correct` analog). -/

/-- **`exportRecord_correct`** — the inserted record validated DECLARATIVELY (not trusted): the
freshly-minted swiss record carries EXACTLY the export's data — its `swiss` key is `sw`, its target
is `target`, its exported `rights` are the requested `rights`, its `refcount` is `1` (one live ref),
and no cert is bound yet. So the spec's `kernel.swiss = exportRecord … :: k.swiss` clause genuinely
encodes the correct insertion, rather than blindly trusting the constructor. -/
theorem exportRecord_correct (sw : Nat) (exporter target : CellId) (rights : List Auth) :
    (exportRecord sw exporter target rights).swiss = sw
    ∧ (exportRecord sw exporter target rights).exporter = exporter
    ∧ (exportRecord sw exporter target rights).target = target
    ∧ (exportRecord sw exporter target rights).rights = rights
    ∧ (exportRecord sw exporter target rights).refcount = 1
    ∧ (exportRecord sw exporter target rights).cert = none := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- **`exportRecord_lookup`** — after the export, the new entry is the one `findSwiss` returns for
`sw` (it is the head of the consed list, and the pre-state had no entry for `sw` by FRESHNESS). This
pins that the spec's inserted record is the LIVE entry for `sw`, the load-bearing fact a later
enliven/handoff/drop reads. -/
theorem exportRecord_lookup (ss : List SwissRecord) (sw : Nat) (exporter target : CellId)
    (rights : List Auth) :
    findSwiss (exportRecord sw exporter target rights :: ss) sw
      = some (exportRecord sw exporter target rights) := by
  unfold findSwiss exportRecord
  simp only [List.find?_cons, beq_self_eq_true]

/-! ## §3 — FULL-STATE SEMANTIC SPEC (the INDEPENDENT reference) + executor⟺spec. -/

/-- **The full-state declarative spec of a committed `exportSturdyRefA`** — the INDEPENDENT reference
semantics. The THREE-way guard holds; the post-state's `kernel.swiss` is the fresh record consed onto
the pre-state's swiss list (see `exportRecord_correct`/`exportRecord_lookup`); the log gains exactly
the authority receipt; and every one of the SIXTEEN non-`swiss` kernel fields is unchanged. No frame
clause mentions the executor. -/
def ExportSpec (s : RecChainedState) (sw : Nat) (actor exporter target : CellId) (rights : List Auth)
    (s' : RecChainedState) : Prop :=
  ExportGuard s sw actor exporter rights
  ∧ s'.kernel.swiss = exportRecord sw exporter target rights :: s.kernel.swiss
  ∧ s'.log = exportReceipt actor exporter :: s.log
  -- THE FRAME: the sixteen non-`swiss` kernel fields, all LITERALLY unchanged.
  ∧ s'.kernel.accounts = s.kernel.accounts
  ∧ s'.kernel.cell = s.kernel.cell
  ∧ s'.kernel.caps = s.kernel.caps
  ∧ s'.kernel.nullifiers = s.kernel.nullifiers
  ∧ s'.kernel.revoked = s.kernel.revoked
  ∧ s'.kernel.commitments = s.kernel.commitments
  ∧ s'.kernel.bal = s.kernel.bal
  ∧ s'.kernel.slotCaveats = s.kernel.slotCaveats
  ∧ s'.kernel.factories = s.kernel.factories
  ∧ s'.kernel.lifecycle = s.kernel.lifecycle
  ∧ s'.kernel.deathCert = s.kernel.deathCert
  ∧ s'.kernel.delegate = s.kernel.delegate
  ∧ s'.kernel.delegations = s.kernel.delegations
  ∧ s'.kernel.sealedBoxes = s.kernel.sealedBoxes
  ∧ s'.kernel.delegationEpoch = s.kernel.delegationEpoch
  ∧ s'.kernel.delegationEpochAt = s.kernel.delegationEpochAt

/-- **`export_iff_spec` — EXECUTOR ⟺ SPEC (FULL state, both directions).** The full executor
`execFullA` commits an `exportSturdyRefA sw actor exporter target rights` into `s'` IFF `s'` is
EXACTLY the spec'd full post-state. The `→` direction VALIDATES the arm against the independent spec —
all 17 kernel fields + the log are checked, so had the arm silently mutated any of them the
corresponding frame clause would make this proof FAIL; the `←` reconstructs the committed state from
the spec. This is the executor corner of the spec⟺executor⟺circuit triangle for swiss-export. -/
theorem export_iff_spec (s : RecChainedState) (sw : Nat) (actor exporter target : CellId)
    (rights : List Auth) (s' : RecChainedState) :
    execFullA s (.exportSturdyRefA sw actor exporter target rights) = some s'
      ↔ ExportSpec s sw actor exporter target rights s' := by
  simp only [execFullA, swissExportChainA, swissExportK]
  by_cases hauth : stateAuthB s.kernel.caps actor exporter = true
  · rw [if_pos hauth]
    -- split on the FRESHNESS lookup (`findSwiss`): an existing entry fails closed.
    cases hf : findSwiss s.kernel.swiss sw with
    | some e =>
      -- swiss number already in use ⇒ `swissExportK` is `none` ⇒ the arm is `none`.
      constructor
      · intro h; exact absurd h (by simp)
      · rintro ⟨⟨_, hfresh, _⟩, _⟩
        -- the spec's FRESHNESS clause contradicts the existing entry.
        rw [hf] at hfresh; exact absurd hfresh (by simp)
    | none =>
      -- split on NON-AMPLIFICATION.
      by_cases hr : rightsNarrowerOrEqual rights (heldAuths s.kernel exporter) = true
      · rw [if_pos hr]
        constructor
        · intro h
          simp only [Option.some.injEq] at h
          subst h
          refine ⟨⟨hauth, hf, hr⟩, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
        · rintro ⟨_, hsw, hlog, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16⟩
          -- reconstruct `s'` from its (kernel field-by-field) + log spec.
          obtain ⟨k', log'⟩ := s'
          obtain ⟨acc, cell, caps, nul, rev, com, bal, sw', sc, fac, lc, dc, dg, dgs, sb, dge, dgea⟩ := k'
          simp only [exportRecord, exportReceipt] at hsw hlog h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16
          subst hsw hlog h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16
          rfl
      · -- non-amplification fails ⇒ `none`.
        rw [if_neg hr]
        constructor
        · intro h; exact absurd h (by simp)
        · rintro ⟨⟨_, _, hr'⟩, _⟩; exact absurd hr' hr
  · -- authority fails ⇒ the whole arm is `none`.
    rw [if_neg hauth]
    constructor
    · intro h; exact absurd h (by simp)
    · rintro ⟨⟨hauth', _, _⟩, _⟩; exact absurd hauth' hauth

/-! ## §4 — corollaries: the headline facts read off the spec.

These extract the load-bearing properties from the executor⟺spec equivalence (so they hold of the
REAL committed step), the swiss-export analogs of `Transfer.lean`'s post-state facts. -/

/-- **`export_spec_inserts`** — from a committed `exportSturdyRefA`, the fresh swiss record (carrying
EXACTLY the export's `sw`/`target`/`rights`, `refcount = 1`, no cert) is now the LIVE entry that
`findSwiss` returns for `sw`. Read off the spec's `swiss` clause + `exportRecord_lookup`. This is the
semantic content "the sturdy ref now exists and is bound to its data". -/
theorem export_spec_inserts (s : RecChainedState) (sw : Nat) (actor exporter target : CellId)
    (rights : List Auth) (s' : RecChainedState)
    (h : execFullA s (.exportSturdyRefA sw actor exporter target rights) = some s') :
    findSwiss s'.kernel.swiss sw = some (exportRecord sw exporter target rights) := by
  have hspec := (export_iff_spec s sw actor exporter target rights s').mp h
  rw [hspec.2.1]; exact exportRecord_lookup s.kernel.swiss sw exporter target rights

/-- **`export_spec_non_amplifying`** — from a committed `exportSturdyRefA`, the exported `rights` are
genuinely `⊆` the exporter's REAL committed rights `heldAuths s.kernel exporter` (the CapTP
non-amplification gate: a sturdy ref cannot grant authority the exporter never held). Read off the
spec's guard. The bound is over the ADVERSARY-UNCONTROLLABLE committed c-list, NOT a prover-supplied
parameter — so it cannot be inflated by a lying prover. -/
theorem export_spec_non_amplifying (s : RecChainedState) (sw : Nat) (actor exporter target : CellId)
    (rights : List Auth) (s' : RecChainedState)
    (h : execFullA s (.exportSturdyRefA sw actor exporter target rights) = some s') :
    rightsNarrowerOrEqual rights (heldAuths s.kernel exporter) = true := by
  have hspec := (export_iff_spec s sw actor exporter target rights s').mp h
  exact hspec.1.2.2

/-- **`export_spec_balance_neutral`** — from a committed `exportSturdyRefA`, the per-asset ledger
`bal` and the live-account set are UNCHANGED (the swiss table moves REFERENCES, not balance ⇒
conservation-trivial). Read directly off the spec's frame clauses. -/
theorem export_spec_balance_neutral (s : RecChainedState) (sw : Nat) (actor exporter target : CellId)
    (rights : List Auth) (s' : RecChainedState)
    (h : execFullA s (.exportSturdyRefA sw actor exporter target rights) = some s') :
    s'.kernel.bal = s.kernel.bal ∧ s'.kernel.accounts = s.kernel.accounts := by
  have hspec := (export_iff_spec s sw actor exporter target rights s').mp h
  exact ⟨hspec.2.2.2.2.2.2.2.2.2.1, hspec.2.2.2.1⟩

/-- **`export_spec_authorized`** — from a committed `exportSturdyRefA`, the actor held authority over
the exporting cell. Read off the spec's guard (the executor-side `swissExportChainA_authorized`
analog, but routed through the INDEPENDENT spec). -/
theorem export_spec_authorized (s : RecChainedState) (sw : Nat) (actor exporter target : CellId)
    (rights : List Auth) (s' : RecChainedState)
    (h : execFullA s (.exportSturdyRefA sw actor exporter target rights) = some s') :
    stateAuthB s.kernel.caps actor exporter = true := by
  have hspec := (export_iff_spec s sw actor exporter target rights s').mp h
  exact hspec.1.1

/-! ## §5 — non-vacuity: the THREE gates are each REAL (a bad export is REJECTED).

A spec that accepts bad inputs is worthless. Here we EXHIBIT that each of the three guard conjuncts
genuinely gates: violating authority, freshness, or non-amplification each makes `execFullA` return
`none` — the forged/unauthorized/duplicate/amplifying export cannot commit. These are the soundness
content matching `Transfer.lean`'s `rejects_*`. -/

/-- **`export_rejects_unauthorized` — PROVED.** An `exportSturdyRefA` over a pre-state where the actor
does NOT hold authority over the exporting cell (`stateAuthB … ≠ true`) is REJECTED (`= none`). An
unauthorized export cannot commit. -/
theorem export_rejects_unauthorized (s : RecChainedState) (sw : Nat) (actor exporter target : CellId)
    (rights : List Auth) (hbad : stateAuthB s.kernel.caps actor exporter ≠ true) :
    execFullA s (.exportSturdyRefA sw actor exporter target rights) = none := by
  simp only [execFullA, swissExportChainA]
  rw [if_neg hbad]

/-- **`export_rejects_duplicate` — PROVED.** An `exportSturdyRefA` over a pre-state where the swiss
number `sw` is ALREADY in use (`findSwiss … = some e`, FRESHNESS violated) is REJECTED (`= none`). No
duplicate export — the swiss number space is collision-free by construction. -/
theorem export_rejects_duplicate (s : RecChainedState) (sw : Nat) (actor exporter target : CellId)
    (rights : List Auth) (e : SwissRecord) (hbad : findSwiss s.kernel.swiss sw = some e) :
    execFullA s (.exportSturdyRefA sw actor exporter target rights) = none := by
  simp only [execFullA, swissExportChainA, swissExportK]
  by_cases hauth : stateAuthB s.kernel.caps actor exporter = true
  · rw [if_pos hauth, hbad]
  · rw [if_neg hauth]

/-- **`export_rejects_amplifying` — PROVED.** An `exportSturdyRefA` over a pre-state where the
exported `rights` are NOT `⊆` the exporter's genuinely-held rights (`rightsNarrowerOrEqual … ≠ true`,
NON-AMPLIFICATION violated) is REJECTED (`= none`) — provided the prior two gates would otherwise
pass. A bare-authority actor cannot mint a sturdy ref carrying rights its cell never held: the
capability-amplification hole is closed. -/
theorem export_rejects_amplifying (s : RecChainedState) (sw : Nat) (actor exporter target : CellId)
    (rights : List Auth) (hfresh : findSwiss s.kernel.swiss sw = none)
    (hbad : rightsNarrowerOrEqual rights (heldAuths s.kernel exporter) ≠ true) :
    execFullA s (.exportSturdyRefA sw actor exporter target rights) = none := by
  simp only [execFullA, swissExportChainA, swissExportK]
  by_cases hauth : stateAuthB s.kernel.caps actor exporter = true
  · rw [if_pos hauth, hfresh, if_neg hbad]
  · rw [if_neg hauth]

/-- **`export_no_spec_when_unauthorized` — corollary.** When authority fails, NO post-state satisfies
the spec via the executor (the `↔` collapses to `none = some s'`, impossible). -/
theorem export_no_spec_when_unauthorized (s : RecChainedState) (sw : Nat)
    (actor exporter target : CellId) (rights : List Auth) (s' : RecChainedState)
    (hbad : stateAuthB s.kernel.caps actor exporter ≠ true) :
    ¬ execFullA s (.exportSturdyRefA sw actor exporter target rights) = some s' := by
  rw [export_rejects_unauthorized s sw actor exporter target rights hbad]; simp

/-! ## §6 — Axiom-hygiene tripwires.

Whitelist exactly `{propext, Classical.choice, Quot.sound}` — no `sorryAx`/`admit`/`axiom`/
`native_decide`. -/

#assert_axioms exportRecord_correct
#assert_axioms exportRecord_lookup
#assert_axioms export_iff_spec
#assert_axioms export_spec_inserts
#assert_axioms export_spec_non_amplifying
#assert_axioms export_spec_balance_neutral
#assert_axioms export_spec_authorized
#assert_axioms export_rejects_unauthorized
#assert_axioms export_rejects_duplicate
#assert_axioms export_rejects_amplifying
#assert_axioms export_no_spec_when_unauthorized

end Dregg2.Circuit.Spec.SwissExport
