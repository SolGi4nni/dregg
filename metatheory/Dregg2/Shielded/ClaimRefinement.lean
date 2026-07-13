/-
# Dregg2.Shielded.ClaimRefinement — the shielded pool's EffectVM side-structure `_refines_` obligation.

This module discharges the **Lean refinement obligation** the shielded pool owes as an effect-VM
plugin — the `S_claim_refines` theorem the side-structure ABI requires
(`docs/deos/EFFECTVM-SIDESTRUCTURE-ABI.md §3.6, §4.1, §5`). The ABI states every side-structure that
contributes a claim to a turn must prove its committed claim REFINES a sound effect-VM step:

    theorem S_claim_refines (turn) (claim) (k k')
        (hbound : boundInTurn claim turn)     -- the fold connected the teeth (circuit ⇒ this hyp)
        (hstep  : recKExec k turn = some k') : -- the composite turn committed
      ConservesOn S k k' ∧ AuthorizedOn S k turn ∧ NullifierFreshOn S k turn

The shielded-spend claim (the marquee side-structure) is the 3-felt uni-STARK PI
`[nullifier, merkle_root, value_binding]` (`circuit-prove/src/shielded/spend_circuit.rs:135-147`).
Its two halves plug in at DIFFERENT grades (ABI §4.1):

  * **PROVED half — membership + nullifier** (THIS theorem). A valid shielded spend
    (the note commitment is a MEMBER of the tree committed at `merkleRoot`, AND its `nullifier` is
    FRESH) refines a sound VM step: it is AUTHORIZED (spends a REAL committed note the spender
    controls — the circuit's C3/C6 membership + value-theft tooth,
    `spend_circuit.rs:213-253`) and preserves NO-DOUBLE-SPEND (the fresh nullifier joins the set and
    can never be re-spent — composed with the deployed nullifier-persistence discipline).

  * **ATTESTED residual — per-asset conservation** (NOT this theorem, named §ATTESTED below). The
    hidden Σvᵢ_in = Σvᵢ_out over the `value_binding` lane rides the OFF-AIR Pedersen/Ristretto
    Schnorr-excess + Bulletproof range proof (`shielded/mod.rs:29-41`) — the wrong curve to fold as
    a BabyBear STARK leaf. It is discharged in the circuit at ATTESTED grade, not proved here. The
    plugin's remaining obligation to lift it to PROVED is the value-commitments-in-AIR weld
    (ABI §4.1(c), `DREGGFI-VISION.md §7`). This module claims NOTHING about conservation over the
    hidden notes; it proves only membership + nullifier.

## What is REUSED (composed, not re-proved)
  * `ShieldedValue.unshieldK` — the deployed shielded-spend verb over the REAL kernel
    (`Exec/ShieldedValue.lean §6`): find the note by nullifier, spend the nullifier (fail-closed
    on double-spend), transfer the note's own value pool → dst.
  * `ShieldedValue.unshield_value_binding` — the committed step spent a REAL inventory note whose
    value moved (the membership witness the AUTHORIZED half rides).
  * `RecordKernel.note_spend_inserts` / `note_no_double_spend` / `recKExecAsset_shape` — the
    deployed nullifier-set anti-replay (the NO-DOUBLE-SPEND half). The O(1)-root refinement of the
    SAME discipline is `Exec.NullifierAccumulator.present_no_witness` / `spend_then_no_rewitness`
    (a spent nullifier admits no re-witness); the concrete list-nullifier gate proved here is what
    that accumulator commits to.

## Honesty (do not launder — ABI §3.6)
`#assert_axioms` clean ≠ hypothesis-free. The keystone's ONLY hypotheses are `hbound` (the circuit
fold provided the membership teeth) and `hstep` (the shielded turn committed). Its conclusion is a
REAL law (authorized-membership + fresh→spent→never-re-spendable), not a tautology — witnessed
non-vacuous BOTH polarities in §NON-VACUITY (a concrete valid spend refines; a forged note and a
re-used nullifier are REFUSED). Here `merkleRoot` binds a leaf set through a reference fold
(`refTreeRoot`, a linear rolling-hash stand-in like `ShieldedValue.refVC`) — kept so the refinement
threading stays structural. The REAL Poseidon2 tree (root-binds-set under `Poseidon2SpongeCR`, so a
forged committed set forces a collision) and the REAL group Pedersen (binding = DLog) that RETIRE
these two toys are proved in `Dregg2.Shielded.RealCrypto` and composed at rung 3
(`Market.shielded_ring_clears_real_crypto`).
-/
import Dregg2.Exec.ShieldedValue

namespace Dregg2.Shielded

open Dregg2.Exec
open Dregg2.Exec.ShieldedValue

set_option autoImplicit false

/-! ## §1 — the shielded-spend claim, faithful to `spend_circuit.rs`'s 3-felt PI. -/

/-- **`ShieldedSpendClaim`** — the committed claim the shielded-spend uni-STARK exposes, exactly
`[nullifier, merkle_root, value_binding]` (`spend_circuit.rs:135-147`, `PUBLIC_INPUT_COUNT = 3`):

  * `nullifier`    — the revealed spend nullifier (PI[0], `hash_fact(leaf, key[0..4])`, C4);
  * `merkleRoot`   — the note-commitment tree root the leaf proves membership under (PI[1], C3/C6);
  * `valueBinding` — the hiding Poseidon2 commitment `hash_fact(value,[randomness,0,0])` linking the
                     STARK leaf value to the OFF-AIR Pedersen value leg (PI[2], C7). Its conservation
                     content is ATTESTED (§ATTESTED), not constrained by the PROVED refinement. -/
structure ShieldedSpendClaim where
  /-- PI[0]: the revealed nullifier. -/
  nullifier    : Nat
  /-- PI[1]: the note-commitment tree root membership is proved under. -/
  merkleRoot   : Nat
  /-- PI[2]: the hiding value-binding commitment (ATTESTED — the Pedersen link). -/
  valueBinding : Nat
  deriving Repr

/-- A **reference note-commitment tree root**: a left-fold hash STAND-IN over the leaf set (`Nat`
arithmetic, NOT the deployed 4-ary Poseidon2 tree — the linear analog of `ShieldedValue.refVC`).
Faithful to the STRUCTURE the refinement needs — the root is a function of the committed leaf set,
so "a leaf is a member of the tree at `root`" is `leaf ∈ leaves ∧ root = refTreeRoot leaves`, exactly
the circuit's C3 chain (`current` hashes up the path to `merkle_root`). -/
def refTreeRoot (leaves : List Nat) : Nat := leaves.foldl (fun acc x => acc * 31 + x + 1) 7

/-- **`MerkleTreeCommits root leaves`** — the committed note-commitment tree root binds exactly this
leaf set (the realizable fold up the 4-ary path, `spend_circuit.rs` C3/C6). The membership carrier;
a HYPOTHESIS the spend witness supplies (the circuit's membership proof — the §3.6 `hbound` teeth),
never an axiom. -/
abbrev MerkleTreeCommits (root : Nat) (leaves : List Nat) : Prop := root = refTreeRoot leaves

/-- **`MemberAtRoot root leaf leaves`** — `leaf` is a MEMBER of the tree committed at `root`: it is
one of the committed leaves AND `root` genuinely commits to that leaf set. This is the shielded
plugin's AUTHORIZATION notion — you may spend a note iff it is a committed member whose full preimage
you know (the C6 value-theft tooth), the shielded analog of `recKExec_authorized`. -/
abbrev MemberAtRoot (root leaf : Nat) (leaves : List Nat) : Prop :=
  leaf ∈ leaves ∧ MerkleTreeCommits root leaves

/-- **`RootBindsInventory root s`** — the `hbound` teeth for a whole pool state: the claim's
`merkleRoot` commits to the pool's committed note-commitment set (`s.kernel.commitments`), and every
inventory note's commitment is one of those committed leaves. The shielded-spend circuit's membership
proof supplies this (C3/C6); it is what the in-circuit fold connects. -/
abbrev RootBindsInventory (root : Nat) (s : ShieldedState) : Prop :=
  MerkleTreeCommits root s.kernel.commitments ∧
    ∀ n ∈ s.notes, n.cm ∈ s.kernel.commitments

/-! ## §2 — peel lemmas over the deployed `unshieldK` (public composition, no re-proof). -/

/-- A committed `unshieldK` peeled to its nullifier-set facts, using ONLY public kernel lemmas: the
spent note was found, its nullifier was FRESH pre-step, and the post-state's nullifier set is exactly
the fresh nullifier consed on (the transfer leg leaves `nullifiers` untouched, `recKExecAsset_shape`).
The private `ShieldedValue.unshieldK_committed` establishes the same shape internally; this re-derives
only the nullifier facts the refinement needs, from public lemmas. -/
theorem unshield_peel (poolOf : AssetId → CellId) {s s' : ShieldedState} {nf : Nat} {dst : CellId}
    (h : unshieldK poolOf s nf dst = some s') :
    (∃ n, s.notes.find? (fun m => m.nf == nf) = some n)
      ∧ nf ∉ s.kernel.nullifiers
      ∧ s'.kernel.nullifiers = nf :: s.kernel.nullifiers
      ∧ s'.notes = s.notes := by
  unfold unshieldK at h
  cases hfind : s.notes.find? (fun m => m.nf == nf) with
  | none => rw [hfind] at h; exact absurd h (by simp)
  | some n =>
      rw [hfind] at h
      cases hns : noteSpendNullifier s.kernel nf with
      | none => rw [hns] at h; exact absurd h (by simp)
      | some k₁ =>
          rw [hns] at h
          rw [Option.map_eq_some_iff] at h
          obtain ⟨k₂, hk₂, hs'⟩ := h
          have hfresh : nf ∉ s.kernel.nullifiers := by
            intro hin
            rw [note_no_double_spend s.kernel nf hin] at hns
            simp at hns
          have hk₁ : k₁ = { s.kernel with nullifiers := nf :: s.kernel.nullifiers } := by
            unfold noteSpendNullifier at hns
            rw [if_neg hfresh] at hns
            simp only [Option.some.injEq] at hns
            exact hns.symm
          have e1 : k₂.nullifiers = k₁.nullifiers := by rw [recKExecAsset_shape hk₂]
          subst hs'
          exact ⟨⟨n, rfl⟩, hfresh, by rw [e1, hk₁], rfl⟩

/-- **`unshield_no_rewitness` — the composed anti-replay over `unshieldK`.** After a committed
shielded spend of `nf`, a SECOND spend of the same `nf` fails-closed: the note is still in the
inventory (notes are not removed) but the nullifier now sits in the spent set, so
`note_no_double_spend` refuses. The concrete-list mirror of `NullifierAccumulator.spend_then_no_rewitness`. -/
theorem unshield_no_rewitness (poolOf : AssetId → CellId) {s s' : ShieldedState} {nf : Nat}
    {dst : CellId} (h : unshieldK poolOf s nf dst = some s') (dst' : CellId) :
    unshieldK poolOf s' nf dst' = none := by
  obtain ⟨⟨n, hfind⟩, hfresh, hnulls, hnotes⟩ := unshield_peel poolOf h
  have hin : nf ∈ s'.kernel.nullifiers := by rw [hnulls]; exact List.mem_cons_self ..
  unfold unshieldK
  rw [hnotes, hfind, note_no_double_spend s'.kernel nf hin]

/-! ## §3 — THE KEYSTONE: the shielded-spend claim REFINES a sound effect-VM step. -/

/-- **`shielded_spend_claim_refines` — the shielded pool's ABI `S_claim_refines` obligation (PROVED
half).** Given the circuit's membership teeth (`hbound : RootBindsInventory claim.merkleRoot s`) and
a committed shielded spend of `claim.nullifier` (`hstep : unshieldK poolOf s claim.nullifier dst =
some s'`), the claim refines a SOUND effect-VM step:

  * **(a) AUTHORIZED** — the step consumed a REAL committed note that is a MEMBER of the tree at
    `merkleRoot`, and moved EXACTLY that note's value to `dst`: `∃ n ∈ s.notes, n.nf =
    claim.nullifier ∧ MemberAtRoot claim.merkleRoot n.cm s.kernel.commitments ∧ (dst credited
    n.value)`. Membership IS the shielded authorization (you can only spend a committed note whose
    preimage you know — the C6 value-theft tooth); the value delta shows the step genuinely spent it.

  * **(b) NO-DOUBLE-SPEND** — the nullifier was FRESH before, joins the spent set, and can NEVER be
    re-spent: `claim.nullifier ∉ s.kernel.nullifiers ∧ claim.nullifier ∈ s'.kernel.nullifiers ∧
    ∀ dst', unshieldK poolOf s' claim.nullifier dst' = none`. This is the ABI §5 nullifier-invariant
    obligation, composed from the deployed nullifier-set anti-replay.

The composite turn's receipt then inherits both — the shielded plugin cannot violate the VM's
no-forgery / no-double-spend invariants (ABI §5). Conservation over the hidden notes is the ATTESTED
residual (§ATTESTED), deliberately absent from this conclusion. -/
theorem shielded_spend_claim_refines (poolOf : AssetId → CellId) (claim : ShieldedSpendClaim)
    {s s' : ShieldedState} {dst : CellId}
    (hbound : RootBindsInventory claim.merkleRoot s)
    (hstep  : unshieldK poolOf s claim.nullifier dst = some s') :
    (∃ n ∈ s.notes, n.nf = claim.nullifier ∧
        MemberAtRoot claim.merkleRoot n.cm s.kernel.commitments ∧
        s'.kernel.bal dst n.asset = s.kernel.bal dst n.asset + n.value)
    ∧ (claim.nullifier ∉ s.kernel.nullifiers ∧
        claim.nullifier ∈ s'.kernel.nullifiers ∧
        ∀ dst', unshieldK poolOf s' claim.nullifier dst' = none) := by
  -- (a) membership + value delta from the committed step (the spend consumed a real note):
  obtain ⟨n, hmem, hnf, hbal, _⟩ := unshield_value_binding poolOf hstep
  obtain ⟨hroot, hcmInv⟩ := hbound
  -- (b) nullifier facts from the public peel:
  obtain ⟨_, hfresh, hnulls, _⟩ := unshield_peel poolOf hstep
  refine ⟨⟨n, hmem, hnf, ⟨hcmInv n hmem, hroot⟩, hbal⟩, hfresh, ?_, ?_⟩
  · rw [hnulls]; exact List.mem_cons_self ..
  · exact fun dst' => unshield_no_rewitness poolOf hstep dst'

/-! ## §ATTESTED — the per-asset conservation residual (named, NOT proved here). -/

/-- **The TRANSPARENT-ledger conservation the shielded spend preserves** — the pool→dst legs balance
(`ShieldedValue.unshieldK_preserves_exact`): the transparent `ExactConservation` survives every
committed shield/unshield. This is the LEDGER-visible half.

**The HIDDEN per-asset Σvᵢ_in = Σvᵢ_out over the `value_binding` lane is NOT this theorem and NOT
proved in this module.** It rides the off-AIR Pedersen/Ristretto Schnorr-excess + Bulletproof range
proof (`shielded/mod.rs:29-41`), discharged in the circuit at **ATTESTED** grade. The value-side
carrier already in tree is `ShieldedValue.created_value_conservation` (Σ commitments = commit(Σ value)
via `commit_hom`), which is itself gated on the Pedersen `binding` §8 carrier. Lifting conservation
from ATTESTED to PROVED is the plugin's remaining obligation: the value-commitments-in-AIR weld
(ABI §4.1(c)). The PROVED refinement above claims NOTHING about it. -/
theorem shielded_spend_preserves_transparent_conservation (poolOf : AssetId → CellId)
    {s s' : ShieldedState} {nf : Nat} {dst : CellId}
    (h : unshieldK poolOf s nf dst = some s') (hex : ExactConservation s.kernel) :
    ExactConservation s'.kernel :=
  unshieldK_preserves_exact poolOf h hex

/-! ## §NON-VACUITY — the refinement is load-bearing, BOTH polarities (ABI §3.6 audit). -/

/-- The demo pool registry (every asset's pool is cell 3 — `ShieldedValue.poolDemo`). -/
def poolDemo : AssetId → CellId := fun _ => 3

/-- A concrete committed pool state: cell 2 holds 1 of asset 0, the pool (cell 3) holds 3 of asset 0,
backed by ONE inventory note (`commit(3,2) = 5` under `refVC`, nullifier 99), whose commitment 5 is a
committed leaf. The genuine post-shield shape of the `ShieldedValue.sShielded` roundtrip. -/
def demoState : ShieldedState :=
  { kernel :=
      { accounts := {2, 3}
        cell := fun _ => Value.record [("balance", Value.int 0)]
        caps := fun _ => []
        bal := fun c a => if c = 3 ∧ a = 0 then 3 else if c = 2 ∧ a = 0 then 1 else 0
        commitments := [5]
        nullifiers := [] }
    notes := [{ cm := 5, nf := 99, asset := 0, value := 3 }] }

/-- The valid spend claim for `demoState`'s note: nullifier 99, membership under the tree root of the
committed leaf set `[5]`, value-binding 5 (the Pedersen commitment — ATTESTED). -/
def demoClaim : ShieldedSpendClaim :=
  { nullifier := 99, merkleRoot := refTreeRoot [5], valueBinding := 5 }

/-- **TRUE POLE — a concrete valid spend REFINES.** The member-note + fresh-nullifier spend commits,
is AUTHORIZED (spends the real committed member note, crediting `dst` its value), and is
NO-DOUBLE-SPEND (nullifier fresh → spent). The keystone is not vacuous: its hypotheses are
inhabited by a real committed step. -/
theorem demo_valid_spend_refines :
    ∃ s', unshieldK poolDemo demoState demoClaim.nullifier 2 = some s'
      ∧ (∃ n ∈ demoState.notes, n.nf = demoClaim.nullifier ∧
           MemberAtRoot demoClaim.merkleRoot n.cm demoState.kernel.commitments ∧
           s'.kernel.bal 2 n.asset = demoState.kernel.bal 2 n.asset + n.value)
      ∧ demoClaim.nullifier ∉ demoState.kernel.nullifiers
      ∧ demoClaim.nullifier ∈ s'.kernel.nullifiers := by
  have hsome : (unshieldK poolDemo demoState demoClaim.nullifier 2).isSome := by decide
  obtain ⟨s', hs'⟩ := Option.isSome_iff_exists.mp hsome
  have hb : RootBindsInventory demoClaim.merkleRoot demoState := by
    refine ⟨rfl, ?_⟩; decide
  obtain ⟨hauth, hfresh, hin, _⟩ := shielded_spend_claim_refines poolDemo demoClaim hb hs'
  exact ⟨s', hs', hauth, hfresh, hin⟩

-- The concrete outcomes (`#guard`), including the FALSE poles — the teeth REFUSE:
-- a member commitment IS a member at the root; a non-member (forged) leaf is NOT:
#guard decide (MemberAtRoot demoClaim.merkleRoot 5 demoState.kernel.commitments)
#guard decide (¬ MemberAtRoot demoClaim.merkleRoot 999 demoState.kernel.commitments)
-- the valid spend commits, moving EXACTLY the note's value (dst 2: 1 → 4, pool 3 → 0):
#guard (unshieldK poolDemo demoState 99 2).isSome
#guard ((unshieldK poolDemo demoState 99 2).map fun s => (s.kernel.bal 2 0, s.kernel.bal 3 0))
        == some (4, 0)
#guard ((unshieldK poolDemo demoState 99 2).map fun s => s.kernel.nullifiers) == some [99]
-- FALSE POLE (forged note): a nullifier with NO committed note is REFUSED at the find? gate:
#guard (unshieldK poolDemo demoState 12345 2).isNone
-- FALSE POLE (double-spend): the same nullifier cannot be unshielded twice:
#guard ((unshieldK poolDemo demoState 99 2).bind fun s => unshieldK poolDemo s 99 2).isNone

/-! ## §AXIOM HYGIENE — the keystone + peels pinned to the kernel axioms only. -/

#assert_axioms unshield_peel
#assert_axioms unshield_no_rewitness
#assert_axioms shielded_spend_claim_refines
#assert_axioms shielded_spend_preserves_transparent_conservation
#assert_axioms demo_valid_spend_refines

end Dregg2.Shielded
