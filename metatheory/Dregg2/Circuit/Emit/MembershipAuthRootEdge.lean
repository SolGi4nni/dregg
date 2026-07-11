/-
# Dregg2.Circuit.Emit.MembershipAuthRootEdge — the MEMBERSHIP carrier's third edge (ROOT leg).

## The deployment model — GROUNDED (cited)

`StateConstraint::SenderAuthorized { AuthorizedSet::PublicRoot { set_root_index } }` is a
**CAVEAT, not an effect with its own rotated descriptor**. `turn/src/executor/mod.rs:326` maps it
to a `SlotCaveatEntry { type_tag = pi::SLOT_CAVEAT_TAG_SENDER_AUTHORIZED, slot_index =
set_root_index, params = 0 }` — it rides the CAVEAT MANIFEST on whatever effect's turn carries the
precondition (the SAME "dsl rides custom + the manifest" pattern). So there is NO committed
membership BASE descriptor — STEP-3's finding is CORRECT and EXPECTED, not a gap. The membership
relation is checked ENTIRELY OFF-AIR by
`turn/src/executor/membership_verifier.rs::MerkleMembershipStarkVerifier` — a standalone
`dregg_circuit::dsl::membership` Poseidon2-Merkle STARK whose public inputs are `[leaf, root]` with
`leaf = compress_member(ctx.sender)` (`membership_verifier.rs:154`) and
`root = root_felt_from_slot(cell.slot[set_root_index])` (`membership_verifier.rs:91/155`).

The two off-AIR legs a pure light client never witnesses (`MembershipBackingAttack.lean`):
  (a) the SENDER LEAF — `leaf = compress_member(sender_pk)` (§A: an unbacked `sender_leaf`);
  (b) the AUTHORIZED ROOT — `root` = the cell's published set-root at `set_root_index`
      (§A′: an injected root).

## What this edge BUILDS — the ROOT leg (b), NON-VACUOUS

`effFieldsReadOpenV3` (`CarrierOctetGates` §3) forces the published authorized-root tooth EQUAL to
the fields-map value at the declared `set_root_index`, membership-authenticated under the committed
BEFORE ~124-bit `fields_root` block. `root_felt_from_slot` reads the authorized root as exactly that
slot felt, and the caveat manifest pins `key = set_root_index` (`mod.rs:328`), so pinning the read's
`idxCol` to that manifest key column authenticates the root at the EXACT slot the `SenderAuthorized`
caveat names. This REFUTES `MembershipBackingAttack.§A′` (the injected-root forgery): a `root` tooth
that is NOT the committed fields value at the caveat slot is UNSAT for a ledgerless client. The
`idxCol`/`rootTeethCol` columns stay PARAMETRIC (the gate discipline — the big-bang regen pins them
+ row-0-PI the tooth).

## What this edge does NOT build — the SENDER leg (a) is a STOP, named precisely

The sender leaf `compress_member(ctx.sender)` CANNOT be bound non-vacuously against the deployed
rotated trace. The ONE committed pubkey octet is `B_PUBKEY_OCTET` (limbs 104..=111,
`circuit/src/effect_vm/trace_rotated.rs:174`), which carries
`canonical_32_to_felts_8(cell.public_key())` — the OPERATED CELL's OWNER key, unconditionally every
turn. But `SenderAuthorized` compresses `ctx.sender = parent_pk` (`execute_tree.rs:986`), the turn
ACTOR, which is NOT the operated cell's owner (the whole point of the caveat is to authorize OTHER
senders — `integration_sender_authorized_air.rs` fires `member`/`intruder` senders against a cell
they do not own). The turn-identity ACTOR (PI[39], `trace_rotated.rs:2322`) is a SINGLE cap-identity
felt, not a compressible 32-byte pubkey octet. Firing `withMembershipPubkeyCompress` over
`B_PUBKEY_OCTET` would bind the WRONG party's key — the owner while claiming the sender — a LAUNDERED
vacuity the ANTI-VACUITY LAW forbids. The sender leg needs a NEW committed SENDER-pubkey octet in
the rotated trace (a producer fill + geometry change, the twin of the STEP-2 owner-octet fill but
keyed on `ctx.sender`); until that lands, `withMembershipPubkeyCompress` (SAT — `compress_member` IS
the chip-native `node8` compress, `commit/src/typed.rs:606`) has no CORRECT octet to bind. THAT is
the named sender-leg seam.

## Remaining terminal seams
  * the in-AIR Poseidon2 Merkle-path (`sender_leaf ∈ committee-under-root`, the `MerkleHash` TID_P2
    lookup) — `circuit-prove::membership_leaf_adapter::prove_membership_leaf` binds the TUPLE, NOT
    the path (its own module doc names the path as the residual);
  * the deployed-leg PI EXPOSURE of `(sender_leaf, authorized_root)` at fixed slots — a VK-moving
    descriptor change (the big-bang regen rider).

`MembershipBackingAttack.lean` STANDS: the deployed AIR alone still admits §A (the sender leg is a
STOP) — and §A′ until this root edge is wired. The fold tooth does NOT yet fully bite membership, so
no `MembershipBindingFromFold` flip is claimed here.

## Axiom hygiene
`#assert_axioms` ⊆ {propext, Classical.choice, Quot.sound}; Poseidon2 CR only through the named
`ChipTableSoundN`. NEW file; all imports read-only.
-/
import Dregg2.Circuit.Emit.CarrierOctetGates

namespace Dregg2.Circuit.Emit.MembershipAuthRootEdge

open Dregg2.Circuit.DescriptorIR2 (EffectVmDescriptor2 Satisfied2 ChipTableSoundN VmTrace envAt)
open Dregg2.Circuit.DeployedFieldsTree (Fields8Scheme)
open Dregg2.Circuit.Emit.CarrierOctetGates
  (effFieldsReadOpenV3 effFieldsReadOpenV3_forces_read8 effFieldsReadOpenV3_rejects_nonmember
   fieldsReadAt8)
open Dregg2.Circuit.Emit.FieldsOpenEmit (fieldsPermOut)

set_option autoImplicit false

/-- **`withMembershipAuthRoot base name idxCol rootTeethCol`** — the membership ROOT-leg third edge:
the caveat-carrying rotated `base` COMPOSED with the fields-read-open appendix that authenticates the
published authorized-root tooth (`rootTeethCol`) as the fields-map value at the `SenderAuthorized`
caveat's `set_root_index` (`idxCol`, pinned by the regen to the manifest entry key) under the
committed BEFORE `fields_root`. Membership has NO own base descriptor (it is a caveat), so `base` is
PARAMETRIC — the regen supplies the concrete caveat-carrying descriptor. -/
def withMembershipAuthRoot (base : EffectVmDescriptor2) (name : String)
    (idxCol rootTeethCol : Nat) : EffectVmDescriptor2 :=
  effFieldsReadOpenV3 base name idxCol rootTeethCol

/-- **THE MEMBERSHIP ROOT KEYSTONE.** A `Satisfied2` of the root edge TRACE-FORCES the published
authorized-root tooth EQUAL to the fields-map value at the declared `set_root_index`,
membership-authenticated under the committed BEFORE ~124-bit `fields_root`. A forged authorized-root
(any value NOT under the committed fields root at that slot) is UNSAT for a ledgerless client —
`MembershipBackingAttack.§A′` (the injected root) is refuted. -/
theorem withMembershipAuthRoot_forces (S8 : Fields8Scheme)
    (base : EffectVmDescriptor2) (name : String) (idxCol rootTeethCol : Nat)
    (hash : List ℤ → ℤ) (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ)
    (t : VmTrace)
    (hChip : ChipTableSoundN (fieldsPermOut S8) (t.tf .poseidon2))
    (hsat : Satisfied2 hash (withMembershipAuthRoot base name idxCol rootTeethCol)
      minit mfin maddrs t)
    (i : Nat) (hi : i < t.rows.length) (hnotlast : i + 1 ≠ t.rows.length)
    (hcells : ∀ col : Nat, 0 ≤ (envAt t i).loc col ∧ (envAt t i).loc col < 2013265921) :
    fieldsReadAt8 S8
      (Dregg2.Circuit.Emit.EffectVmEmitRotationV3.beforeFieldsRootCols (envAt t i))
      ((envAt t i).loc idxCol) ((envAt t i).loc rootTeethCol) :=
  effFieldsReadOpenV3_forces_read8 S8 base name idxCol rootTeethCol hash minit mfin maddrs t
    hChip hsat i hi hnotlast hcells

/-- **TOOTH — `withMembershipAuthRoot_rejects_injected_root`.** The membership analog of
`MembershipBackingAttack.deployed_admits_injected_root`, now REFUTED under the root edge: if NO path
authenticates the published `(set_root_index, authorized_root)` pair under the committed fields root,
the descriptor is UNSAT. -/
theorem withMembershipAuthRoot_rejects_injected_root (S8 : Fields8Scheme)
    (base : EffectVmDescriptor2) (name : String) (idxCol rootTeethCol : Nat)
    (hash : List ℤ → ℤ) (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ)
    (t : VmTrace)
    (hChip : ChipTableSoundN (fieldsPermOut S8) (t.tf .poseidon2))
    (i : Nat) (hi : i < t.rows.length) (hnotlast : i + 1 ≠ t.rows.length)
    (hcells : ∀ col : Nat, 0 ≤ (envAt t i).loc col ∧ (envAt t i).loc col < 2013265921)
    (hnon : ¬ fieldsReadAt8 S8
      (Dregg2.Circuit.Emit.EffectVmEmitRotationV3.beforeFieldsRootCols (envAt t i))
      ((envAt t i).loc idxCol) ((envAt t i).loc rootTeethCol)) :
    ¬ Satisfied2 hash (withMembershipAuthRoot base name idxCol rootTeethCol) minit mfin maddrs t :=
  effFieldsReadOpenV3_rejects_nonmember S8 base name idxCol rootTeethCol hash minit mfin maddrs t
    hChip i hi hnotlast hcells hnon

#assert_axioms withMembershipAuthRoot_forces
#assert_axioms withMembershipAuthRoot_rejects_injected_root

end Dregg2.Circuit.Emit.MembershipAuthRootEdge
