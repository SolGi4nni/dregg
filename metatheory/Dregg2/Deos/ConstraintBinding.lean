/-
# Dregg2.Deos.ConstraintBinding — a DECLARED capacity caveat cannot be OMITTED
(the soundness core of the house-capacity in-circuit welds: the manifest is no longer
prover-optional once the declared constraint-set is bound into committed state).

## The gap this closes

The §6 weld rungs (`SealedEscrow.lean`, `StandingObligation.lean`, `Vault.lean`) prove that
**if** a `SettleEscrow` / `DischargeObligation` / `VaultDeposit` manifest entry is PRESENT, its
re-evaluation FORCES the capacity invariant (atomicity / on-schedule / no-dilution). What they do
NOT establish is that the entry must be present at all: the slot-caveat manifest
(`circuit/src/effect_vm/verify.rs::verify_slot_caveat_manifest`) iterates the prover-published
`count` entries and re-evaluates each, but a forger who simply OMITS the entry (publishes
`count = 0`, or a manifest with no tag-17 entry) leaves the verifier nothing to check. The gate is
prover-OPTIONAL — the load-bearing soundness gap named in
`docs/deos/VK-EPOCH-CONSTRAINT-BINDING-DESIGN.md`.

## The fix, as a theorem

The closure binds each cell's DECLARED constraint-set into the cell's COMMITTED state (already true:
`cell/src/commitment.rs::compute_authority_digest_felt` folds `cell.program` — hence its
`state_constraints` — into `record_digest`, the `B_AUTHORITY_DIGEST` limb of the ~124-bit wide
commit a light client binds). A verifier that RE-DERIVES the required capacity tags from the
committed declaration and DEMANDS each is covered (present AND its gate re-evaluates true) cannot be
fooled by omission. This module is the Lean rung for that:

  * `verifierAccepts required m` — accept iff EVERY required tag is `covers`ed (present and
    satisfied). The omission-PROOF gate.
  * `omission_rejected` / `unsatisfied_rejected` — a manifest that omits a required tag, OR presents
    it with a failing gate, is REJECTED. The forger cannot drop the entry, nor present a hollow one.
  * `omission_caught_under_binding` — **THE SOUNDNESS CORE.** Under the declaration-commitment
    collision-resistance floor (`DeclCommitBinds`: equal commitments ⟹ equal required tags), a
    forger who presents an ALTERNATE declaration (e.g. one requiring nothing) to dodge coverage must
    publish a declaration whose commitment matches the committed one — and CR then forces the SAME
    required tags. So a turn on a capacity cell that omits its declared entry is rejected, whatever
    declaration the prover presents. Omission is caught, not prover-optional.
  * The escrow BRIDGE (`honest_settle_covers` / `partial_settle_not_covered`) ties the abstract
    `satisfied` bit to the genuine §6 `SealedEscrow.SettleGate` — so this is concretely about the
    sealed-escrow weld, reusing its proven `settle_passes_gate` / `partial_settle_rejected` teeth,
    not a free-floating list lemma.

## Axiom hygiene

`#assert_all_clean` at the close. The only named hypothesis is the declaration-commitment binding
`DeclCommitBinds` (the authority-digest collision-resistance floor, the SAME shape as the
`Poseidon2SpongeCR` floor the heap/cap roots carry) — never an axiom. No core edit.
-/
import Dregg2.Deos.SealedEscrow

namespace Dregg2.Deos.ConstraintBinding

/-! ## §1 — the manifest and the required-tag set. -/

/-- A slot-caveat manifest type-tag (the `pi::SLOT_CAVEAT_TAG_*` value). -/
abbrev Tag := Nat

/-- The sealed-escrow atomic-swap tag (`SLOT_CAVEAT_TAG_SETTLE_ESCROW = 17`). -/
def tagSettleEscrow : Tag := 17
/-- The standing-obligation per-period discharge tag (`SLOT_CAVEAT_TAG_DISCHARGE_OBLIGATION = 18`). -/
def tagDischargeObligation : Tag := 18
/-- The share-vault no-dilution deposit tag (`SLOT_CAVEAT_TAG_VAULT_DEPOSIT = 19`). -/
def tagVaultDeposit : Tag := 19

/-- A prover-supplied manifest entry: its tag and whether the verifier's off-AIR re-evaluation of
its gate (the §6 `SettleGate`/`DischargeGate`/`VaultDepositGate`) SUCCEEDS against the bound
state-before/state-after views. The `satisfied` bit is the verifier's verdict, NOT a free claim —
the escrow bridge below pins it to the genuine gate. -/
structure Entry where
  /-- The entry's manifest type-tag. -/
  tag : Tag
  /-- Whether the gate re-evaluation succeeded. -/
  satisfied : Bool
deriving DecidableEq, Repr

/-- The prover-chosen slot-caveat manifest. -/
abbrev Manifest := List Entry

/-- A required tag is **covered** by the manifest iff some present entry carries that tag AND its
gate re-evaluation succeeded. Presence alone is NOT enough — a present-but-failing entry (a partial
settle) does not cover. -/
def covers (m : Manifest) (t : Tag) : Prop :=
  ∃ e ∈ m, e.tag = t ∧ e.satisfied = true

instance (m : Manifest) (t : Tag) : Decidable (covers m t) := by
  unfold covers; infer_instance

/-- **The omission-proof verifier gate.** Accept iff EVERY required tag (re-derived from the
committed declaration) is covered. A manifest that omits a required entry — or presents it
unsatisfied — is rejected. -/
def verifierAccepts (required : List Tag) (m : Manifest) : Prop :=
  ∀ t ∈ required, covers m t

instance (required : List Tag) (m : Manifest) : Decidable (verifierAccepts required m) := by
  unfold verifierAccepts; infer_instance

/-! ## §2 — the teeth: omission and hollow-entry are caught. -/

/-- **THE OMISSION TOOTH.** A manifest that contains NO entry for a required tag is REJECTED — the
verifier demands coverage. A forger cannot drop the declared capacity entry. -/
theorem omission_rejected (t : Tag) (required : List Tag) (hreq : t ∈ required)
    (m : Manifest) (homit : ∀ e ∈ m, e.tag ≠ t) :
    ¬ verifierAccepts required m := by
  intro hacc
  obtain ⟨e, hem, hetag, _⟩ := hacc t hreq
  exact homit e hem hetag

/-- **THE HOLLOW-ENTRY TOOTH.** A manifest whose only entries for a required tag have a FAILING gate
(`satisfied = false` — e.g. a partial settle, an early discharge, a diluting deposit) is REJECTED.
Presenting the entry with a hollow verdict does not satisfy coverage. -/
theorem unsatisfied_rejected (t : Tag) (required : List Tag) (hreq : t ∈ required)
    (m : Manifest) (hunsat : ∀ e ∈ m, e.tag = t → e.satisfied = false) :
    ¬ verifierAccepts required m := by
  intro hacc
  obtain ⟨e, hem, hetag, hsat⟩ := hacc t hreq
  have hfalse := hunsat e hem hetag
  rw [hfalse] at hsat
  exact absurd hsat (by decide)

/-- **HONEST ACCEPT** (non-vacuity). A manifest covering the single required tag with a satisfied
entry is accepted — the gate is not vacuously unsatisfiable. -/
theorem honest_accepts (t : Tag) :
    verifierAccepts [t] [⟨t, true⟩] := by
  intro s hs
  rw [List.mem_singleton] at hs
  subst s
  exact ⟨⟨t, true⟩, List.mem_singleton.mpr rfl, rfl, rfl⟩

/-! ## §3 — THE SOUNDNESS CORE: the required set is fixed by the COMMITTED declaration.

`required` above is the re-derived required-tag set. The closure is that it is re-derived from the
cell's COMMITTED declaration, not chosen by the prover. We model a declared constraint-set `Decl`, a
commitment `declCommit : Decl → C` (the authority-digest fold), and the re-derivation
`requiredTags : Decl → List Tag`. The `DeclCommitBinds` floor — equal commitments ⟹ equal required
tags — is the collision-resistance of the authority digest (the SAME shape as the `Poseidon2SpongeCR`
floor the heap and cap roots carry; here over the program byte-fold). With it, a forger cannot escape
coverage by swapping in a hollow declaration. -/

/-- **The declaration-commitment binding floor.** Two declarations with the SAME commitment re-derive
the SAME required tags. The collision-resistance of `compute_authority_digest_felt` over the program
field (equal authority digests ⟹ equal declared `state_constraints` ⟹ equal required tags). Stated as
a named hypothesis, never an axiom — the analog of `Poseidon2SpongeCR`. -/
def DeclCommitBinds {Decl C : Type} (declCommit : Decl → C) (requiredTags : Decl → List Tag) : Prop :=
  ∀ d d' : Decl, declCommit d = declCommit d' → requiredTags d = requiredTags d'

/-- **THE SOUNDNESS CORE.** A turn on a capacity cell whose COMMITTED declaration requires tag `t`
is REJECTED if the manifest omits `t` — WHATEVER declaration the prover presents, so long as it hits
the committed declaration's commitment (which the ~124-bit wide commit forces). The forger cannot
dodge by presenting a hollow declaration: `DeclCommitBinds` makes the presented declaration's
required tags equal the committed one's, and then `omission_rejected` bites. This is the gate made
omission-proof, not prover-optional. -/
theorem omission_caught_under_binding {Decl C : Type}
    (declCommit : Decl → C) (requiredTags : Decl → List Tag)
    (hbinds : DeclCommitBinds declCommit requiredTags)
    (committed presented : Decl)
    (hcommit : declCommit presented = declCommit committed)
    (t : Tag) (hreq : t ∈ requiredTags committed)
    (m : Manifest) (homit : ∀ e ∈ m, e.tag ≠ t) :
    ¬ verifierAccepts (requiredTags presented) m := by
  -- The presented declaration's required tags equal the committed one's (CR floor).
  rw [hbinds presented committed hcommit]
  -- Now `t` is required by the committed declaration; omission rejects.
  exact omission_rejected t (requiredTags committed) hreq m homit

/-- The hollow-declaration corollary in its starkest form: a forger that presents a declaration
requiring NOTHING (`requiredTags presented = []`) to dodge coverage cannot also match the committed
commitment when the committed declaration genuinely requires `t` — the two facts are contradictory
under the binding floor. So the empty-declaration dodge is impossible. -/
theorem hollow_declaration_impossible {Decl C : Type}
    (declCommit : Decl → C) (requiredTags : Decl → List Tag)
    (hbinds : DeclCommitBinds declCommit requiredTags)
    (committed presented : Decl)
    (hcommit : declCommit presented = declCommit committed)
    (t : Tag) (hreq : t ∈ requiredTags committed)
    (hhollow : requiredTags presented = []) :
    False := by
  have heq := hbinds presented committed hcommit
  rw [hhollow] at heq
  -- heq : [] = requiredTags committed, but t ∈ requiredTags committed.
  rw [← heq] at hreq
  exact List.not_mem_nil hreq

/-! ## §4 — THE ESCROW BRIDGE: the abstract `satisfied` bit IS the §6 `SettleGate`.

The `satisfied` bit is the verifier's verdict; here we pin it to the genuine sealed-escrow gate so
this rung is concretely about the SettleEscrow weld, reusing `SealedEscrow`'s proven teeth. -/

open Dregg2.Deos.SealedEscrow
open Dregg2.Substrate.Heap
open Dregg2.Circuit.Poseidon2Binding (Poseidon2SpongeCR)

/-- The manifest entry the projection emits for a sealed-escrow transition: tag 17, with the
verifier's verdict `decide (SettleGate before after)` as its `satisfied` bit. -/
def settleEntry (hash : List ℤ → ℤ) (before after : FeltHeap) : Entry :=
  ⟨tagSettleEscrow, decide (SettleGate hash before after)⟩

/-- **HONEST SETTLE IS COVERED.** The genuine kernel transition (both legs `Ready`, then `settle`)
produces a covered tag-17 entry: the entry is present and its gate verdict is `true` (by the §6
`settle_passes_gate`). So an honest escrow turn passes coverage. -/
theorem honest_settle_covers (hash : List ℤ → ℤ) (hsd : SlotsDistinct hash) (h : FeltHeap)
    (hready : Ready hash h) :
    covers [settleEntry hash h (settle hash h)] tagSettleEscrow := by
  refine ⟨settleEntry hash h (settle hash h), List.mem_singleton.mpr rfl, rfl, ?_⟩
  show decide (SettleGate hash h (settle hash h)) = true
  simp only [decide_eq_true_eq]
  exact settle_passes_gate hash hsd h hready

/-- **PARTIAL SETTLE IS NOT COVERED.** A forged partial settle (leg B left `Deposited`) produces a
tag-17 entry whose gate verdict is `false` (by the §6 `partial_settle_rejected`), so it does NOT
cover — coverage then rejects the turn via `unsatisfied_rejected`. The half-open trade cannot be
laundered through the manifest. -/
theorem partial_settle_not_covered (hash : List ℤ → ℤ) (before after : FeltHeap)
    (hpartial : boundStatus hash after Side.B = some stDeposited) :
    ¬ covers [settleEntry hash before after] tagSettleEscrow := by
  rintro ⟨e, he, _hetag, hsat⟩
  rw [List.mem_singleton] at he
  subst he
  simp only [settleEntry, decide_eq_true_eq] at hsat
  exact partial_settle_rejected hash before after hpartial hsat

/-- **THE ESCROW OMISSION TOOTH (concrete).** A cell whose committed declaration requires the
sealed-escrow tag (17) and whose manifest omits any tag-17 entry is REJECTED — the concrete escrow
instance of `omission_rejected`. A forged settlement that drops the atomicity gate cannot pass. -/
theorem escrow_omission_rejected (required : List Tag) (hreq : tagSettleEscrow ∈ required)
    (m : Manifest) (homit : ∀ e ∈ m, e.tag ≠ tagSettleEscrow) :
    ¬ verifierAccepts required m :=
  omission_rejected tagSettleEscrow required hreq m homit

/-! ## §5 — NON-VACUITY TEETH (`#guard`): coverage BITES, both polarities. -/

section Witnesses

-- Required-set = [17]. A manifest covering it (present + satisfied) ACCEPTS.
#guard decide (verifierAccepts [tagSettleEscrow] [⟨tagSettleEscrow, true⟩])
-- OMISSION: the empty manifest does NOT cover a required tag (count = 0 forger).
#guard !decide (verifierAccepts [tagSettleEscrow] [])
-- OMISSION: a manifest with the WRONG tag (e.g. a bare Monotonic, tag 6) does not cover 17.
#guard !decide (verifierAccepts [tagSettleEscrow] [⟨6, true⟩])
-- HOLLOW: the tag-17 entry is PRESENT but its gate FAILED (satisfied = false) — rejected.
#guard !decide (verifierAccepts [tagSettleEscrow] [⟨tagSettleEscrow, false⟩])
-- Multiple required tags (escrow + discharge): all must be covered.
#guard decide (verifierAccepts [tagSettleEscrow, tagDischargeObligation]
  [⟨tagSettleEscrow, true⟩, ⟨tagDischargeObligation, true⟩])
-- ...dropping one (omitting the discharge entry) rejects.
#guard !decide (verifierAccepts [tagSettleEscrow, tagDischargeObligation]
  [⟨tagSettleEscrow, true⟩])

-- THE ESCROW BRIDGE, both polarities, computed on the reference sponge.
private def both : FeltHeap := deposit refSponge (deposit refSponge [] Side.A 100) Side.B 250
private def settled : FeltHeap := settle refSponge both
-- HONEST: the genuine settle transition is covered.
#guard decide (covers [settleEntry refSponge both settled] tagSettleEscrow)
-- PARTIAL: leg A consumed, leg B still deposited — the entry's gate fails, NOT covered.
private def partialA : FeltHeap := hset refSponge both escrowColl (statusKey Side.A) stConsumed
#guard !decide (covers [settleEntry refSponge both partialA] tagSettleEscrow)

end Witnesses

/-! ## §6 — Axiom hygiene. -/

#assert_all_clean [
  omission_rejected,
  unsatisfied_rejected,
  honest_accepts,
  omission_caught_under_binding,
  hollow_declaration_impossible,
  honest_settle_covers,
  partial_settle_not_covered,
  escrow_omission_rejected
]

end Dregg2.Deos.ConstraintBinding
