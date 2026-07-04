/-
# Dregg2.Circuit.Emit.CarrierOctetGates — the v12 PER-CARRIER GATE KEYSTONES (big-bang parallel lane).

The three reusable in-AIR gate families the four v12-walled carriers need, written against the
announced v12 geometry (NUM_PRE_LIMBS 88→112, B_SPAN 119→151, the three zeroed octets
child_vk8@88..95 · contract_hash8@96..103 · pubkey8@104..111 — `docs/deos/V12-GEOMETRY-EPOCH-PLAN.md`),
BUILT AGAINST monolith checkpoint `85170b24c` (STEP 1b — all Emit consumers green at B_SPAN = 151).

  1. **THE OCTET-EQUALITY GATE** (`octetTeethGates` / `withOctetTeeth`) — the perms/VK-weld shape
     (`permsVKWeldGate`, EffectVmEmitRotationV3 §5.PV) generalized to an 8-limb GROUP: 8 unconditional
     `eqGate`s forcing 8 published TAIL teeth columns == the committed octet limbs of a rotated block
     (BEFORE / AFTER / BOTH — parametric `blockBase`). Instantiated for the factory `child_vk8` teeth
     (octet @ `B_CHILD_VK8`; hatchery-invariant RIDES the same octet, `invariant_digest === child_vk`)
     and the hatchery-contract `contract_hash8` teeth (@ `B_CONTRACT_HASH8`). Direct equality — the
     material is already the 32B hash's 8 limbs, no hash gate needed (plan §4).

  2. **THE COMPRESS GATE** (sovereign `withSovereignKeyCommit` + membership
     `withMembershipPubkeyCompress`) — in-AIR Poseidon2 compression of the committed pubkey octet
     (@ `B_PUBKEY8`) == the teeth felts the executor checks, via the SAME wide chip lookups every
     8-felt keystone rides (`chipLookupTupleN` / `chip_lookup_sound_N`, the `HeapOpenEmit`/
     `CapOpenEmit` emission pattern). Parametric over the chip absorb `A : List ℤ → Digest8`
     (`descriptor_ir2::chip_absorb_all_lanes` — the ONE deployed Poseidon2 chip).

  3. **THE FIELDS-ROOT READ-OPEN** (`effFieldsReadOpenV3`) — membership's `authorized_root` anchor:
     the EXISTING fields-open read appendix (`FieldsOpenEmit.fieldsOpenConstraints`, `effFieldsOpenV3`)
     plus welds binding the appendix root group to the committed BEFORE `fields_root` block (limb
     `B_FIELDS_ROOT` = 36 + completions — `beforeRootWeldsF`, reused verbatim), the read leaf's addr
     to a declared `set_root_index` column, and the read leaf's VALUE to the published root-teeth
     column. Forcing: `Satisfied2` ⟹ the teeth felt IS a fields-map value membership-authenticated
     under the committed ~124-bit `fields_root` (`fieldsReadAt8`). NOT geometry (plan §1 / O3).

## ⚑ THE EXECUTOR-COMPRESS VERDICT (verified at `85170b24c`, do not fudge)

  * **sovereign — MATCH.** `proof_verify.rs:2548 pubkey_to_witness_key_commit` =
    `commit/src/typed.rs::canonical_32_to_felts_4`: 8 limbs via `canonical_32_to_felts_8`
    (**30-bit packing**: `lo | mid1<<8 | mid2<<16 | (hi&0x3F)<<24` per 4-byte group), then FOUR
    `hash_4_to_1` compressions over the interleave quads `[0,1,2,3] · [4,5,6,7] · [0,4,2,6] ·
    [1,5,3,7]` (`quadIdx`). `hash_4_to_1(x) = perm(st[0..4]=x, st[4]=4, 0…)[0]` is EXACTLY the
    deployed chip's arity-4 row (`chip_absorb_all_lanes(4, x)[0]` — `st[4] = arity` for arity 4,
    lanes 7.. zero-padded). So the KEY_COMMIT teeth (4 felts, `columns.rs::WITNESS_KEY_COMMIT_0..3`
    = aux offsets 23..26, ABSOLUTE cols 113..=116 = AUX_BASE + offset, row-0-pinned to PI) are FOUR arity-4 chip lookups over the committed octet —
    `withSovereignKeyCommit` realizes the executor's function EXACTLY. ⚑ The STEP-2 producer fill
    of the pubkey octet must therefore be `canonical_32_to_felts_8(pubkey)` (the 30-bit form).

  * **membership — MISMATCH (named, not fudged).** `membership_verifier.rs:67 compress` =
    `poseidon2::hash_many(BabyBear::encode_hash(pk))`: (i) `encode_hash` = **full 32-bit LE limbs**
    (`field.rs:212`, mod-p lossy) — a DIFFERENT limb decomposition from sovereign's 30-bit
    `canonical_32_to_felts_8`, so ONE committed pubkey octet cannot serve both executors' functions
    as-is; (ii) `hash_many` over 8 limbs is a **rate-4 TWO-permutation sponge** (`poseidon2.rs:377`
    — `st[4] = len` tag, absorb 4, permute, absorb 4, permute, squeeze `st[0]`), which NO deployed
    chip arity computes: the chip is single-permutation per row, its non-{7,11,16} arities seed
    `st[4]=tag, st[5..7]=0` and DROP inputs 4..6 (`chip_absorb_all_lanes`), and a two-lookup chain
    is impossible because the capacity lanes 8..15 of the intermediate state are unexposed.
    `withMembershipPubkeyCompress` therefore realizes the CHIP-NATIVE injective 1-felt compress —
    the arity-16 `node8` row over `pubkey8 ‖ 0⁸` (every limb genuinely seeded, the same lane every
    cap/heap/fields node rides) — and the WIRING step owes the executor re-alignment:
    `membership_verifier.rs::compress` (+ its twins `apply.rs::compress`, SDK `bytes_to_babybear`,
    and the membership-STARK leaf domain) must move to the chip-native form (or a hash_many chip
    capability must be added) BEFORE the gate goes live. Firing the gate against the misaligned
    executor would bind teeth the executor never checks — the fail-open law forbids it.

## Offsets — ALL derived from the canonical constants (never literals)

`B_CARRIER_OCTETS := B_IROOT − 24` (the three octets are the LAST 24 pre-iroot limbs);
`B_CHILD_VK8 / B_CONTRACT_HASH8 / B_PUBKEY8 := B_CARRIER_OCTETS + 0/8/16`;
`BEFORE_BLOCK_BASE := EFFECT_VM_WIDTH`; `AFTER_BLOCK_BASE := EFFECT_VM_WIDTH + B_SPAN`.
`#guard`s pin them to the announced 88/96/104 and tie `AFTER_BLOCK_OFF == B_SPAN`.

## Scope (the big-bang contract)

NO descriptor wiring, NO registry touch, NO regen here — the big-bang regen (the coordinating
lane) wires these fragments into the carrier descriptors, bumps `public_input_count`, and row-0
pins the teeth columns to TAIL PIs. Teeth/param column indices are PARAMETRIC (`teethPiLo`,
`idxCol`, `rootTeethCol`) for exactly that reason. Every forcing lemma is TRACE-FORCED — derived
from `Satisfied2`'s row constraints, never from `henc`'s `SpineCommits`.

## Axiom hygiene

`#assert_axioms` ⊆ {propext, Classical.choice, Quot.sound}; Poseidon2 CR enters ONLY through the
named chip-soundness hypotheses (`ChipTableSoundN`), exactly as in `FieldsOpenEmit`/`HeapOpenEmit`.
-/
import Dregg2.Circuit.DeployedCapOpen
import Dregg2.Circuit.DeployedFieldsTree
import Dregg2.Circuit.Emit.EffectVmEmitRotationV3
import Dregg2.Circuit.Emit.CapOpenEmit
import Dregg2.Circuit.Emit.FieldsOpenEmit

namespace Dregg2.Circuit.Emit.CarrierOctetGates

open Dregg2.Exec.CircuitEmit (EmittedExpr)
open Dregg2.Circuit.Emit.EffectVmEmit (VmRowEnv EFFECT_VM_WIDTH VmConstraint)
open Dregg2.Circuit.DescriptorIR2
  (Table TraceFamily Lookup VmConstraint2 EffectVmDescriptor2 ChipTableSoundN Satisfied2
   chipLookupTupleN chip_lookup_sound_N CHIP_RATE VmTrace envAt)
open Dregg2.Circuit.DeployedCapOpen (DEPTH digestCols digestCols_map groupVal pathOf8)
open Dregg2.Circuit.DeployedCapTree (Digest8)
open Dregg2.Circuit.DeployedFieldsTree (Fields8Scheme)
open Dregg2.Circuit.DeployedFieldsTree.Fields8Scheme (fieldsLeafDigest8 recomposeUp8)
open Dregg2.Circuit.CapMerkleGeneric (StepG)
open Dregg2.Circuit.Emit.CapOpenEmit (capOpenCols eqGate eqGate_eval CAP_OPEN_SPAN)
open Dregg2.Circuit.Emit.FieldsOpenEmit
  (fieldsOpenConstraints effFieldsOpenV3 effFieldsOpenV3_core fieldsOpen_recompose8
   FieldsMembershipCore fieldsPermOut fieldsLeafPairOf beforeRootWeldsF)

set_option autoImplicit false

/-! ## §0 — the v12 octet geometry, derived from the canonical constants. -/

/-- The base of the three v12 carrier-material octets: the LAST 24 pre-iroot limbs
(LITERAL 88 since v13: the fields[0..7] completion lanes 112..167 + pad 168 ride PAST the
carrier octets, so the octet base no longer tracks `B_IROOT`). -/
def B_CARRIER_OCTETS : Nat := 88

/-- The factory `child_vk8` octet base (in-block limb offset; M1 of the v12 plan). The
hatchery-invariant carrier RIDES this same octet (`invariant_digest === child_vk`). -/
def B_CHILD_VK8 : Nat := B_CARRIER_OCTETS

/-- The hatchery-contract `contract_hash8` octet base (M2). -/
def B_CONTRACT_HASH8 : Nat := B_CARRIER_OCTETS + 8

/-- The sovereign/membership `pubkey8` octet base (M3 — raw key limbs, NOT a pre-hashed fold, so
the in-AIR compress gate can recompute the teeth; plan O2). -/
def B_PUBKEY8 : Nat := B_CARRIER_OCTETS + 16

/-- The rotated BEFORE block base (the v1 spine is `EFFECT_VM_WIDTH` wide; blocks append after). -/
def BEFORE_BLOCK_BASE : Nat := EFFECT_VM_WIDTH

/-- The rotated AFTER block base — derived from `B_SPAN`, never the literal. -/
def AFTER_BLOCK_BASE : Nat :=
  EFFECT_VM_WIDTH + Dregg2.Circuit.Emit.EffectVmEmitRotationV3.B_SPAN

-- Self-test pins: the derived offsets equal the announced v12 layout, and the monolith's
-- AFTER-block offset is exactly B_SPAN (so `AFTER_BLOCK_BASE` matches every group-col reader).
#guard B_CARRIER_OCTETS == 88
#guard B_CHILD_VK8 == 88
#guard B_CONTRACT_HASH8 == 96
#guard B_PUBKEY8 == 104
-- v13: the fields completion lanes (112..167) + pad (168) ride between the carrier octets and
-- the iroot, so the octets end 57 limbs BEFORE it (104 + 8 + 56 + 1 = 169 = B_IROOT).
#guard B_PUBKEY8 + 8 + 56 + 1 == Dregg2.Circuit.Emit.EffectVmEmitRotationV3.B_IROOT
#guard Dregg2.Circuit.Emit.EffectVmEmitRotationV3.AFTER_BLOCK_OFF
    == Dregg2.Circuit.Emit.EffectVmEmitRotationV3.B_SPAN
#guard AFTER_BLOCK_BASE == EFFECT_VM_WIDTH + Dregg2.Circuit.Emit.EffectVmEmitRotationV3.AFTER_BLOCK_OFF

/-- The 8-felt column GROUP of an octet in the block based at `blockBase` (contiguous limbs
`octetBase .. octetBase+7`, unlike the roots' scattered completion limbs — the octets are
v12-native, laid contiguously). -/
def octetGroupCol (blockBase octetBase : Nat) : Fin 8 → Nat :=
  fun i => blockBase + octetBase + i.val

/-- The committed octet read off the row env as a `Digest8`. -/
def octetVals (env : VmRowEnv) (blockBase octetBase : Nat) : Digest8 :=
  groupVal env (octetGroupCol blockBase octetBase)

/-! ## §1 — THE OCTET-EQUALITY GATE (factory · hatchery-contract · hatchery-invariant).

The perms/VK weld (`permsVKWeldGate`) pins ONE committed authority sub-limb to ONE declared
column; the octet gate is its 8-limb GROUP form: 8 unconditional `eqGate`s pinning the published
teeth columns (row-0-PI-pinned by the regen, like the KEY_COMMIT teeth) to the committed octet
limbs. Unconditional per-descriptor — the v12 primary layout gives each material a fixed home so
each carrier's gate needs no selector (plan §2c: "each gate is unconditional per-descriptor,
which is more auditable under the anti-vacuity discipline"). -/

/-- The 8 octet-teeth equality gates: `teethPiLo + i == blockBase + octetBase + i` for `i < 8`. -/
def octetTeethGates (blockBase octetBase teethPiLo : Nat) : List VmConstraint2 :=
  (List.finRange 8).map (fun i =>
    VmConstraint2.base (.gate (eqGate (teethPiLo + i.val) (octetGroupCol blockBase octetBase i))))

/-- **`withOctetTeeth base blockBase octetBase teethPiLo`** — a descriptor PLUS the octet-teeth
weld. Constraints-only (the teeth columns are caller-owned — existing teeth cols or new TAIL
columns the regen widens for); sites/ranges/tables untouched, so every existing keystone composes
verbatim. -/
def withOctetTeeth (base : EffectVmDescriptor2) (blockBase octetBase teethPiLo : Nat) :
    EffectVmDescriptor2 :=
  { base with constraints := base.constraints ++ octetTeethGates blockBase octetBase teethPiLo }

/-- Every octet-teeth gate is a constraint of the welded descriptor. -/
theorem withOctetTeeth_mem (base : EffectVmDescriptor2) (blockBase octetBase teethPiLo : Nat)
    (i : Fin 8) :
    VmConstraint2.base (.gate (eqGate (teethPiLo + i.val) (octetGroupCol blockBase octetBase i)))
      ∈ (withOctetTeeth base blockBase octetBase teethPiLo).constraints := by
  show _ ∈ base.constraints ++ octetTeethGates blockBase octetBase teethPiLo
  exact List.mem_append_right _ (List.mem_map.mpr ⟨i, List.mem_finRange i, rfl⟩)

/-- **The generalized forcing** — any descriptor CONTAINING the octet-teeth gates forces, on every
active (non-last) row of a `Satisfied2` witness, every published tooth column EQUAL to its
committed octet limb. Stated over a `⊆`-hypothesis so single-block, both-block, and composed
descriptors all consume it. TRACE-FORCED (from `Satisfied2.rowConstraints`, never `henc`). -/
theorem octetTeethGates_force (hash : List ℤ → ℤ) (d : EffectVmDescriptor2)
    (blockBase octetBase teethPiLo : Nat)
    (hsub : ∀ c ∈ octetTeethGates blockBase octetBase teethPiLo, c ∈ d.constraints)
    (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (t : VmTrace)
    (hsat : Satisfied2 hash d minit mfin maddrs t)
    (i : Nat) (hi : i < t.rows.length) (hnotlast : i + 1 ≠ t.rows.length) :
    ∀ k : Fin 8, (envAt t i).loc (teethPiLo + k.val)
      = octetVals (envAt t i) blockBase octetBase k := by
  intro k
  have hlastf : (i + 1 == t.rows.length) = false := by
    simp only [beq_eq_false_iff_ne]; exact hnotlast
  have hin : VmConstraint2.base
      (.gate (eqGate (teethPiLo + k.val) (octetGroupCol blockBase octetBase k)))
      ∈ octetTeethGates blockBase octetBase teethPiLo :=
    List.mem_map.mpr ⟨k, List.mem_finRange k, rfl⟩
  have h := hsat.rowConstraints i hi _ (hsub _ hin)
  simp only [VmConstraint2.holdsAt, VmConstraint.holdsVm, hlastf] at h
  exact (eqGate_eval _ _ (envAt t i)).mp (by simpa using h)

/-- **`withOctetTeeth_forces`** — the single-block instantiation of the generalized forcing. -/
theorem withOctetTeeth_forces (hash : List ℤ → ℤ) (base : EffectVmDescriptor2)
    (blockBase octetBase teethPiLo : Nat)
    (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (t : VmTrace)
    (hsat : Satisfied2 hash (withOctetTeeth base blockBase octetBase teethPiLo) minit mfin maddrs t)
    (i : Nat) (hi : i < t.rows.length) (hnotlast : i + 1 ≠ t.rows.length) :
    ∀ k : Fin 8, (envAt t i).loc (teethPiLo + k.val)
      = octetVals (envAt t i) blockBase octetBase k :=
  octetTeethGates_force hash _ blockBase octetBase teethPiLo
    (fun _ hc => List.mem_append_right _ hc) minit mfin maddrs t hsat i hi hnotlast

/-- **TOOTH — `withOctetTeeth_rejects_forged`.** A row whose published tooth diverges from the
committed octet limb (a forged `child_vk` / `contract_hash` exposure) does NOT satisfy the welded
descriptor — UNSAT for a ledgerless client, no trusted post-cell. -/
theorem withOctetTeeth_rejects_forged (hash : List ℤ → ℤ) (base : EffectVmDescriptor2)
    (blockBase octetBase teethPiLo : Nat)
    (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (t : VmTrace)
    (i : Nat) (hi : i < t.rows.length) (hnotlast : i + 1 ≠ t.rows.length) (k : Fin 8)
    (hforged : (envAt t i).loc (teethPiLo + k.val)
      ≠ octetVals (envAt t i) blockBase octetBase k) :
    ¬ Satisfied2 hash (withOctetTeeth base blockBase octetBase teethPiLo) minit mfin maddrs t :=
  fun hsat => hforged
    (withOctetTeeth_forces hash base blockBase octetBase teethPiLo minit mfin maddrs t hsat
      i hi hnotlast k)

/-- **`withOctetTeethBoth`** — the BOTH-blocks weld: the same teeth pinned to the octet in the
BEFORE **and** AFTER blocks (transitively forcing before == after octet continuity through the
teeth — the completion-freeze shape for a value-turn carrier context). -/
def withOctetTeethBoth (base : EffectVmDescriptor2) (octetBase teethPiLo : Nat) :
    EffectVmDescriptor2 :=
  withOctetTeeth (withOctetTeeth base BEFORE_BLOCK_BASE octetBase teethPiLo)
    AFTER_BLOCK_BASE octetBase teethPiLo

/-- Both-blocks forcing: the teeth equal the BEFORE octet AND the AFTER octet (hence the two
committed octets agree). -/
theorem withOctetTeethBoth_forces (hash : List ℤ → ℤ) (base : EffectVmDescriptor2)
    (octetBase teethPiLo : Nat)
    (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (t : VmTrace)
    (hsat : Satisfied2 hash (withOctetTeethBoth base octetBase teethPiLo) minit mfin maddrs t)
    (i : Nat) (hi : i < t.rows.length) (hnotlast : i + 1 ≠ t.rows.length) :
    ∀ k : Fin 8,
      (envAt t i).loc (teethPiLo + k.val) = octetVals (envAt t i) BEFORE_BLOCK_BASE octetBase k
      ∧ (envAt t i).loc (teethPiLo + k.val) = octetVals (envAt t i) AFTER_BLOCK_BASE octetBase k := by
  intro k
  constructor
  · exact octetTeethGates_force hash _ BEFORE_BLOCK_BASE octetBase teethPiLo
      (fun _ hc => by
        show _ ∈ (withOctetTeeth base BEFORE_BLOCK_BASE octetBase teethPiLo).constraints
          ++ octetTeethGates AFTER_BLOCK_BASE octetBase teethPiLo
        exact List.mem_append_left _ (List.mem_append_right _ hc))
      minit mfin maddrs t hsat i hi hnotlast k
  · exact octetTeethGates_force hash _ AFTER_BLOCK_BASE octetBase teethPiLo
      (fun _ hc => List.mem_append_right _ hc) minit mfin maddrs t hsat i hi hnotlast k

/-! ### §1a — the carrier instantiations.

  * **factory** — `child_vk8` teeth on the CreateCellFromFactory descriptor: the 8 published TAIL
    teeth == the committed `effective_vk` limbs (the STEP-2 fill; kills the `child_vk_derived`
    misnomer's laundering). AFTER-block by default (the child's installed authority is
    post-state material); the regen picks via `blockBase` if the producer fills both.
  * **hatchery-invariant** — RIDES the SAME gate + octet (`invariant_digest === child_vk`,
    WELD-STATE §3): no separate keystone, instantiate `withFactoryChildVkTeeth` on its leg.
  * **hatchery-contract** — `contract_hash8` teeth on the hatchery-mint descriptor. -/

/-- Factory: the `child_vk8` octet-teeth weld (AFTER block — the child's installed authority). -/
def withFactoryChildVkTeeth (base : EffectVmDescriptor2) (teethPiLo : Nat) :
    EffectVmDescriptor2 :=
  withOctetTeeth base AFTER_BLOCK_BASE B_CHILD_VK8 teethPiLo

/-- Factory forcing: the 8 published child-vk teeth ARE the committed `child_vk8` octet. The
hatchery-invariant carrier consumes this SAME lemma on its leg (`invariant_digest === child_vk`). -/
theorem withFactoryChildVkTeeth_forces (hash : List ℤ → ℤ) (base : EffectVmDescriptor2)
    (teethPiLo : Nat)
    (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (t : VmTrace)
    (hsat : Satisfied2 hash (withFactoryChildVkTeeth base teethPiLo) minit mfin maddrs t)
    (i : Nat) (hi : i < t.rows.length) (hnotlast : i + 1 ≠ t.rows.length) :
    ∀ k : Fin 8, (envAt t i).loc (teethPiLo + k.val)
      = octetVals (envAt t i) AFTER_BLOCK_BASE B_CHILD_VK8 k :=
  withOctetTeeth_forces hash base AFTER_BLOCK_BASE B_CHILD_VK8 teethPiLo
    minit mfin maddrs t hsat i hi hnotlast

/-- Hatchery-contract: the `contract_hash8` octet-teeth weld (AFTER block — the attested
contract of the hatchery-mint row). -/
def withHatcheryContractTeeth (base : EffectVmDescriptor2) (teethPiLo : Nat) :
    EffectVmDescriptor2 :=
  withOctetTeeth base AFTER_BLOCK_BASE B_CONTRACT_HASH8 teethPiLo

/-- Hatchery-contract forcing: the 8 published contract-hash teeth ARE the committed
`contract_hash8` octet. -/
theorem withHatcheryContractTeeth_forces (hash : List ℤ → ℤ) (base : EffectVmDescriptor2)
    (teethPiLo : Nat)
    (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (t : VmTrace)
    (hsat : Satisfied2 hash (withHatcheryContractTeeth base teethPiLo) minit mfin maddrs t)
    (i : Nat) (hi : i < t.rows.length) (hnotlast : i + 1 ≠ t.rows.length) :
    ∀ k : Fin 8, (envAt t i).loc (teethPiLo + k.val)
      = octetVals (envAt t i) AFTER_BLOCK_BASE B_CONTRACT_HASH8 k :=
  withOctetTeeth_forces hash base AFTER_BLOCK_BASE B_CONTRACT_HASH8 teethPiLo
    minit mfin maddrs t hsat i hi hnotlast

#assert_axioms octetTeethGates_force
#assert_axioms withOctetTeeth_forces
#assert_axioms withOctetTeeth_rejects_forged
#assert_axioms withOctetTeethBoth_forces
#assert_axioms withFactoryChildVkTeeth_forces
#assert_axioms withHatcheryContractTeeth_forces

-- Self-tests: shape + a biting eval pair (holds on an agreeing assignment, BITES on a forged one).
#guard (octetTeethGates 0 0 100).length == 8
private def octetTestGood : Nat → ℤ := fun n => if n ≥ 100 then ((n - 100 : Nat) : ℤ) else (n : ℤ)
private def octetTestForged : Nat → ℤ := fun n => if n == 100 then 99 else octetTestGood n
#guard (octetTeethGates 0 0 100).all (fun c =>
  match c with
  | .base (.gate g) => g.eval octetTestGood == 0
  | _ => false)
#guard (octetTeethGates 0 0 100).any (fun c =>
  match c with
  | .base (.gate g) => g.eval octetTestForged != 0
  | _ => false)

/-! ## §2 — THE COMPRESS GATE (sovereign KEY_COMMIT · membership sender-leaf).

Parametric over the ONE deployed chip absorb `A : List ℤ → Digest8`
(`descriptor_ir2::chip_absorb_all_lanes` — the same carrier `Cap8Scheme`/`Heap8Scheme`/
`Fields8Scheme` package as `chipAbsorb8`). The lookups are the standard wide tuples
(`chipLookupTupleN`), so `chip_lookup_sound_N` forces every digest lane; the teeth welds then pin
the executor-checked felts to lane 0. See the module-doc EXECUTOR-COMPRESS VERDICT: sovereign is
an EXACT match (4 × arity-4 = `hash_4_to_1` interleave); membership is chip-native `node8`
(arity-16, `pubkey8 ‖ 0⁸`) with the executor re-alignment NAMED as owed at wiring. -/

/-- The wide permutation output of a chip absorb (the `capPermOut`/`fieldsPermOut` shape). -/
def permOutOf (A : List ℤ → Digest8) : List ℤ → List ℤ := fun xs => List.ofFn (A xs)

/-! ### §2a — sovereign: the 4-felt KEY_COMMIT interleave (`canonical_32_to_felts_4`). -/

/-- The `canonical_32_to_felts_4` interleave matrix (`commit/src/typed.rs:586`): quad `q`'s `j`-th
input limb. Rows: `[0,1,2,3] · [4,5,6,7] · [0,4,2,6] · [1,5,3,7]`. -/
def quadIdx (q j : Fin 4) : Fin 8 :=
  match q.val, j.val with
  | 0, 0 => 0 | 0, 1 => 1 | 0, 2 => 2 | 0, 3 => 3
  | 1, 0 => 4 | 1, 1 => 5 | 1, 2 => 6 | 1, 3 => 7
  | 2, 0 => 0 | 2, 1 => 4 | 2, 2 => 2 | 2, 3 => 6
  | 3, 0 => 1 | 3, 1 => 5 | 3, 2 => 3 | 3, 3 => 7
  | _, _ => 0

-- The matrix IS the executor's interleave (all four rows pinned).
#guard decide ((List.finRange 4).map (quadIdx 0) = ([0, 1, 2, 3] : List (Fin 8)))
#guard decide ((List.finRange 4).map (quadIdx 1) = ([4, 5, 6, 7] : List (Fin 8)))
#guard decide ((List.finRange 4).map (quadIdx 2) = ([0, 4, 2, 6] : List (Fin 8)))
#guard decide ((List.finRange 4).map (quadIdx 3) = ([1, 5, 3, 7] : List (Fin 8)))

/-- Quad `q`'s 4 input column expressions, read off the committed octet. -/
def quadCols (blockBase octetBase : Nat) (q : Fin 4) : List EmittedExpr :=
  (List.finRange 4).map (fun j => EmittedExpr.var (octetGroupCol blockBase octetBase (quadIdx q j)))

theorem quadCols_eval (blockBase octetBase : Nat) (q : Fin 4) (env : VmRowEnv) :
    (quadCols blockBase octetBase q).map (·.eval env.loc)
      = (List.finRange 4).map
          (fun j => octetVals env blockBase octetBase (quadIdx q j)) := by
  simp [quadCols, EmittedExpr.eval, octetVals, groupVal, List.map_map, Function.comp_def]

/-- **The executor's KEY_COMMIT function over the committed octet** — quad `q`'s single squeezed
felt: `A (interleave q oct) 0`. At `A := chip_absorb_all_lanes` this IS
`canonical_32_to_felts_4(pubkey)[q]` (arity-4 chip row ≡ `hash_4_to_1`, verified — module doc). -/
def keyCommitSpec (A : List ℤ → Digest8) (oct : Digest8) (q : Fin 4) : ℤ :=
  A ((List.finRange 4).map (fun j => oct (quadIdx q j))) 0

/-- The 4 × 8 appendix digest-column groups (quad `q`, lane `i`) based at `dgBase`. -/
def keyCommitDigestCol (dgBase : Nat) (q : Fin 4) : Fin 8 → Nat :=
  fun i => dgBase + 8 * q.val + i.val

/-- Quad `q`'s wide chip lookup: absorb the 4 interleaved octet columns, output = the 8 bound
digest columns (the whole permutation block — the standard wide-tuple emission). -/
def keyCommitLookup (blockBase octetBase dgBase : Nat) (q : Fin 4) : Lookup :=
  { table := .poseidon2
  , tuple := chipLookupTupleN (quadCols blockBase octetBase q)
      (digestCols (keyCommitDigestCol dgBase q)) }

/-- The sovereign key-commit constraint fragment: 4 chip lookups + 4 teeth welds
(`teethPiLo + q == lane 0 of quad q's digest group`). -/
def keyCommitConstraints (blockBase octetBase dgBase teethPiLo : Nat) : List VmConstraint2 :=
  ((List.finRange 4).map (fun q =>
      VmConstraint2.lookup (keyCommitLookup blockBase octetBase dgBase q)))
  ++ ((List.finRange 4).map (fun q =>
      VmConstraint2.base (.gate (eqGate (teethPiLo + q.val) (keyCommitDigestCol dgBase q 0)))))

/-- The key-commit appendix span: 4 quads × 8 digest lanes. -/
def KEY_COMMIT_SPAN : Nat := 32

/-- **`withSovereignKeyCommit base teethPiLo`** — a descriptor WIDENED by the key-commit appendix:
the 4 published KEY_COMMIT teeth (`SOVEREIGN_WITNESS_KEY_COMMIT`, `columns.rs` aux offsets 23..26 = ABSOLUTE cols 113..=116,
row-0-pinned to PI) are forced equal to the in-AIR `canonical_32_to_felts_4` of the committed
BEFORE-block pubkey octet (the OPERATED cell's owner key — `before_cell.public_key()`). -/
def withSovereignKeyCommit (base : EffectVmDescriptor2) (teethPiLo : Nat) :
    EffectVmDescriptor2 :=
  { base with
    traceWidth  := base.traceWidth + KEY_COMMIT_SPAN
    constraints := base.constraints
      ++ keyCommitConstraints BEFORE_BLOCK_BASE B_PUBKEY8 base.traceWidth teethPiLo }

/-- **The generalized key-commit forcing** — any descriptor containing the fragment forces, under
the chip-table soundness, every published KEY_COMMIT tooth EQUAL to the executor's compress of the
committed octet: `teeth[q] = A (interleave q (committed pubkey8)) 0`. -/
theorem keyCommitConstraints_force (A : List ℤ → Digest8) (hash : List ℤ → ℤ)
    (d : EffectVmDescriptor2) (blockBase octetBase dgBase teethPiLo : Nat)
    (hsub : ∀ c ∈ keyCommitConstraints blockBase octetBase dgBase teethPiLo, c ∈ d.constraints)
    (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (t : VmTrace)
    (hChip : ChipTableSoundN (permOutOf A) (t.tf .poseidon2))
    (hsat : Satisfied2 hash d minit mfin maddrs t)
    (i : Nat) (hi : i < t.rows.length) (hnotlast : i + 1 ≠ t.rows.length) :
    ∀ q : Fin 4, (envAt t i).loc (teethPiLo + q.val)
      = keyCommitSpec A (octetVals (envAt t i) blockBase octetBase) q := by
  intro q
  set e := envAt t i with he
  have hlastf : (i + 1 == t.rows.length) = false := by
    simp only [beq_eq_false_iff_ne]; exact hnotlast
  -- the lookup forces the digest group to the genuine permutation output of the quad.
  have hlkin : VmConstraint2.lookup (keyCommitLookup blockBase octetBase dgBase q)
      ∈ keyCommitConstraints blockBase octetBase dgBase teethPiLo := by
    refine List.mem_append_left _ ?_
    exact List.mem_map.mpr ⟨q, List.mem_finRange q, rfl⟩
  have hlk := hsat.rowConstraints i hi _ (hsub _ hlkin)
  have hmem : (chipLookupTupleN (quadCols blockBase octetBase q)
      (digestCols (keyCommitDigestCol dgBase q))).map (·.eval e.loc) ∈ t.tf .poseidon2 := by
    simpa [VmConstraint2.holdsAt, Lookup.holdsAt, keyCommitLookup] using hlk
  have hlen : (quadCols blockBase octetBase q).length ≤ CHIP_RATE := by
    simp [quadCols, CHIP_RATE]
  have hforce := chip_lookup_sound_N (permOutOf A) (t.tf .poseidon2) hChip e.loc
    (quadCols blockBase octetBase q) (digestCols (keyCommitDigestCol dgBase q)) hlen hmem
  rw [digestCols_map, quadCols_eval] at hforce
  have hreal : permOutOf A ((List.finRange 4).map
      (fun j => octetVals e blockBase octetBase (quadIdx q j)))
      = List.ofFn (A ((List.finRange 4).map
          (fun j => octetVals e blockBase octetBase (quadIdx q j)))) := rfl
  rw [hreal] at hforce
  have hgrp := List.ofFn_inj.mp hforce
  have hlane0 : e.loc (keyCommitDigestCol dgBase q 0)
      = keyCommitSpec A (octetVals e blockBase octetBase) q := by
    have := congrFun hgrp 0
    simpa [groupVal, keyCommitSpec] using this
  -- the weld pins the tooth to lane 0.
  have hwin : VmConstraint2.base (.gate (eqGate (teethPiLo + q.val)
      (keyCommitDigestCol dgBase q 0)))
      ∈ keyCommitConstraints blockBase octetBase dgBase teethPiLo := by
    refine List.mem_append_right _ ?_
    exact List.mem_map.mpr ⟨q, List.mem_finRange q, rfl⟩
  have hw := hsat.rowConstraints i hi _ (hsub _ hwin)
  simp only [VmConstraint2.holdsAt, VmConstraint.holdsVm, hlastf] at hw
  have hweld := (eqGate_eval _ _ e).mp (by simpa using hw)
  rw [hweld, hlane0]

/-- **`withSovereignKeyCommit_forces` — THE SOVEREIGN KEYSTONE.** A `Satisfied2` of the welded
descriptor, under the chip soundness, forces the 4 published KEY_COMMIT teeth EQUAL to
`canonical_32_to_felts_4` (at `A := chip_absorb_all_lanes`) of the committed BEFORE pubkey octet —
a forged owner key is UNSAT for a ledgerless client (P1 + P2 together, no laundered vacuity). -/
theorem withSovereignKeyCommit_forces (A : List ℤ → Digest8) (hash : List ℤ → ℤ)
    (base : EffectVmDescriptor2) (teethPiLo : Nat)
    (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (t : VmTrace)
    (hChip : ChipTableSoundN (permOutOf A) (t.tf .poseidon2))
    (hsat : Satisfied2 hash (withSovereignKeyCommit base teethPiLo) minit mfin maddrs t)
    (i : Nat) (hi : i < t.rows.length) (hnotlast : i + 1 ≠ t.rows.length) :
    ∀ q : Fin 4, (envAt t i).loc (teethPiLo + q.val)
      = keyCommitSpec A (octetVals (envAt t i) BEFORE_BLOCK_BASE B_PUBKEY8) q :=
  keyCommitConstraints_force A hash _ BEFORE_BLOCK_BASE B_PUBKEY8 base.traceWidth teethPiLo
    (fun _ hc => List.mem_append_right _ hc) minit mfin maddrs t hChip hsat i hi hnotlast

/-- **TOOTH — `withSovereignKeyCommit_rejects_forged`.** A row whose published KEY_COMMIT tooth is
NOT the compress of the committed pubkey octet (a forged sovereign key) is UNSAT. -/
theorem withSovereignKeyCommit_rejects_forged (A : List ℤ → Digest8) (hash : List ℤ → ℤ)
    (base : EffectVmDescriptor2) (teethPiLo : Nat)
    (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (t : VmTrace)
    (hChip : ChipTableSoundN (permOutOf A) (t.tf .poseidon2))
    (i : Nat) (hi : i < t.rows.length) (hnotlast : i + 1 ≠ t.rows.length) (q : Fin 4)
    (hforged : (envAt t i).loc (teethPiLo + q.val)
      ≠ keyCommitSpec A (octetVals (envAt t i) BEFORE_BLOCK_BASE B_PUBKEY8) q) :
    ¬ Satisfied2 hash (withSovereignKeyCommit base teethPiLo) minit mfin maddrs t :=
  fun hsat => hforged
    (withSovereignKeyCommit_forces A hash base teethPiLo minit mfin maddrs t hChip hsat
      i hi hnotlast q)

/-- **THE PEEL — `Satisfied2 (withSovereignKeyCommit base teethPiLo) ⟹ Satisfied2 base`.** The
key-commit compose only APPENDS constraints (4 chip lookups + 4 teeth-weld gates) and widens
`traceWidth` (which `Satisfied2` never reads): the inner constraints stay members
(`List.mem_append_left`), the sites / ranges are the record-update-inherited `base` fields, and the
appended fragment contributes NO mem/map op — so every existing per-effect soundness lemma lifts to
the composed descriptor by peeling the compose first. The `withSovereignKeyCommit` analog of
`effFieldsWriteV3_satisfied2_strips_to_base` (the deployed-refusal precedent); the missing lemma the
big-bang registry re-key needed. -/
theorem satisfied2_of_withSovereignKeyCommit (hash : List ℤ → ℤ)
    (base : EffectVmDescriptor2) (teethPiLo : Nat)
    (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (t : VmTrace)
    (h : Satisfied2 hash (withSovereignKeyCommit base teethPiLo) minit mfin maddrs t) :
    Satisfied2 hash base minit mfin maddrs t := by
  have hmapOps : Dregg2.Circuit.DescriptorIR2.mapOpsOf (withSovereignKeyCommit base teethPiLo)
      = Dregg2.Circuit.DescriptorIR2.mapOpsOf base := by
    simp [Dregg2.Circuit.DescriptorIR2.mapOpsOf, withSovereignKeyCommit, keyCommitConstraints,
      List.filterMap_append, List.filterMap_map]
  have hmemOps : Dregg2.Circuit.DescriptorIR2.memOpsOf (withSovereignKeyCommit base teethPiLo)
      = Dregg2.Circuit.DescriptorIR2.memOpsOf base := by
    simp [Dregg2.Circuit.DescriptorIR2.memOpsOf, withSovereignKeyCommit, keyCommitConstraints,
      List.filterMap_append, List.filterMap_map]
  have hmemLog : Dregg2.Circuit.DescriptorIR2.memLog (withSovereignKeyCommit base teethPiLo) t
      = Dregg2.Circuit.DescriptorIR2.memLog base t := by
    simp [Dregg2.Circuit.DescriptorIR2.memLog, hmemOps]
  have hmapLog : Dregg2.Circuit.DescriptorIR2.mapLog (withSovereignKeyCommit base teethPiLo) t
      = Dregg2.Circuit.DescriptorIR2.mapLog base t := by
    simp [Dregg2.Circuit.DescriptorIR2.mapLog, hmapOps]
  exact
    { rowConstraints := fun i hi c hc =>
        h.rowConstraints i hi c (by
          show c ∈ base.constraints
            ++ keyCommitConstraints BEFORE_BLOCK_BASE B_PUBKEY8 base.traceWidth teethPiLo
          exact List.mem_append_left _ hc)
      rowHashes := h.rowHashes
      rowRanges := h.rowRanges
      memAddrsNodup := h.memAddrsNodup
      memClosed := by have := h.memClosed; rwa [hmemLog] at this
      memDisciplined := by have := h.memDisciplined; rwa [hmemLog] at this
      memBalanced := by have := h.memBalanced; rwa [hmemLog] at this
      memTableFaithful := by have := h.memTableFaithful; rwa [hmemLog] at this
      mapTableFaithful := by have := h.mapTableFaithful; rwa [hmapLog] at this }

#assert_axioms satisfied2_of_withSovereignKeyCommit

/-! ### §2b — membership: the 1-felt sender-leaf compress (chip-native `node8` form).

⚑ NAMED MISMATCH (module doc): the executor's `membership_verifier.rs::compress` is TODAY
`hash_many(encode_hash(pk))` — a rate-4 two-permutation sponge over 32-bit limbs that NO deployed
chip arity computes. This gate realizes the CHIP-NATIVE injective compress — the arity-16 `node8`
row over `pubkey8 ‖ 0⁸` (every committed limb genuinely seeded; the same lane every keystone
rides) — and the wiring step OWES the executor re-alignment (compress + its `apply.rs`/SDK twins +
the membership-STARK leaf domain) before the gate goes live. Do NOT wire against the misaligned
executor (fail-open law). -/

/-- The arity-16 `node8`-form input block: the 8 committed octet columns ‖ 8 literal zeros. -/
def pubkeyNode8Inputs (blockBase octetBase : Nat) : List EmittedExpr :=
  ((List.finRange 8).map (fun i => EmittedExpr.var (octetGroupCol blockBase octetBase i)))
    ++ List.replicate 8 (EmittedExpr.const 0)

theorem pubkeyNode8Inputs_eval (blockBase octetBase : Nat) (env : VmRowEnv) :
    (pubkeyNode8Inputs blockBase octetBase).map (·.eval env.loc)
      = List.ofFn (octetVals env blockBase octetBase) ++ List.replicate 8 0 := by
  simp only [pubkeyNode8Inputs, List.map_append, List.map_map]
  rfl

/-- **The chip-native 1-felt pubkey compress** — lane 0 of the arity-16 `node8` absorb over
`oct ‖ 0⁸`. The executor-side function membership must re-align to (or a `hash_many` chip
capability added) at wiring time — see the module-doc verdict. -/
def pubkeyCompress1Spec (A : List ℤ → Digest8) (oct : Digest8) : ℤ :=
  A (List.ofFn oct ++ List.replicate 8 0) 0

/-- The 8 appendix digest columns of the compress lookup, based at `dgBase`. -/
def pubkeyCompressDigestCol (dgBase : Nat) : Fin 8 → Nat := fun i => dgBase + i.val

/-- The compress chip lookup: absorb `pubkey8 ‖ 0⁸` (arity 16 = the `node8` full-seed row — every
committed limb enters the state), output = the 8 bound digest columns. -/
def pubkeyCompressLookup (blockBase octetBase dgBase : Nat) : Lookup :=
  { table := .poseidon2
  , tuple := chipLookupTupleN (pubkeyNode8Inputs blockBase octetBase)
      (digestCols (pubkeyCompressDigestCol dgBase)) }

/-- The membership compress fragment: 1 chip lookup + 1 leaf-teeth weld. -/
def pubkeyCompressConstraints (blockBase octetBase dgBase leafTeethCol : Nat) :
    List VmConstraint2 :=
  [ VmConstraint2.lookup (pubkeyCompressLookup blockBase octetBase dgBase)
  , VmConstraint2.base (.gate (eqGate leafTeethCol (pubkeyCompressDigestCol dgBase 0))) ]

/-- The compress appendix span: one 8-lane digest group. -/
def PUBKEY_COMPRESS_SPAN : Nat := 8

/-- **`withMembershipPubkeyCompress base leafTeethCol`** — a descriptor WIDENED by the compress
appendix: the published sender-leaf tooth == the in-AIR compress of the committed BEFORE-block
pubkey octet (the turn actor's key — plan O1(a): one turn-level `pubkey8`, absorbed per block). -/
def withMembershipPubkeyCompress (base : EffectVmDescriptor2) (leafTeethCol : Nat) :
    EffectVmDescriptor2 :=
  { base with
    traceWidth  := base.traceWidth + PUBKEY_COMPRESS_SPAN
    constraints := base.constraints
      ++ pubkeyCompressConstraints BEFORE_BLOCK_BASE B_PUBKEY8 base.traceWidth leafTeethCol }

/-- **The generalized compress forcing** — any descriptor containing the fragment forces, under
the chip soundness, the published leaf tooth EQUAL to the chip-native compress of the committed
octet. -/
theorem pubkeyCompressConstraints_force (A : List ℤ → Digest8) (hash : List ℤ → ℤ)
    (d : EffectVmDescriptor2) (blockBase octetBase dgBase leafTeethCol : Nat)
    (hsub : ∀ c ∈ pubkeyCompressConstraints blockBase octetBase dgBase leafTeethCol,
      c ∈ d.constraints)
    (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (t : VmTrace)
    (hChip : ChipTableSoundN (permOutOf A) (t.tf .poseidon2))
    (hsat : Satisfied2 hash d minit mfin maddrs t)
    (i : Nat) (hi : i < t.rows.length) (hnotlast : i + 1 ≠ t.rows.length) :
    (envAt t i).loc leafTeethCol
      = pubkeyCompress1Spec A (octetVals (envAt t i) blockBase octetBase) := by
  set e := envAt t i with he
  have hlastf : (i + 1 == t.rows.length) = false := by
    simp only [beq_eq_false_iff_ne]; exact hnotlast
  have hlkin : VmConstraint2.lookup (pubkeyCompressLookup blockBase octetBase dgBase)
      ∈ pubkeyCompressConstraints blockBase octetBase dgBase leafTeethCol :=
    List.mem_cons_self
  have hlk := hsat.rowConstraints i hi _ (hsub _ hlkin)
  have hmem : (chipLookupTupleN (pubkeyNode8Inputs blockBase octetBase)
      (digestCols (pubkeyCompressDigestCol dgBase))).map (·.eval e.loc) ∈ t.tf .poseidon2 := by
    simpa [VmConstraint2.holdsAt, Lookup.holdsAt, pubkeyCompressLookup] using hlk
  have hlen : (pubkeyNode8Inputs blockBase octetBase).length ≤ CHIP_RATE := by
    simp [pubkeyNode8Inputs, List.length_append, List.length_map, List.length_finRange,
      CHIP_RATE]
  have hforce := chip_lookup_sound_N (permOutOf A) (t.tf .poseidon2) hChip e.loc
    (pubkeyNode8Inputs blockBase octetBase) (digestCols (pubkeyCompressDigestCol dgBase))
    hlen hmem
  rw [digestCols_map, pubkeyNode8Inputs_eval] at hforce
  have hreal : permOutOf A (List.ofFn (octetVals e blockBase octetBase) ++ List.replicate 8 0)
      = List.ofFn (A (List.ofFn (octetVals e blockBase octetBase) ++ List.replicate 8 0)) := rfl
  rw [hreal] at hforce
  have hgrp := List.ofFn_inj.mp hforce
  have hlane0 : e.loc (pubkeyCompressDigestCol dgBase 0)
      = pubkeyCompress1Spec A (octetVals e blockBase octetBase) := by
    have := congrFun hgrp 0
    simpa [groupVal, pubkeyCompress1Spec] using this
  have hwin : VmConstraint2.base (.gate (eqGate leafTeethCol (pubkeyCompressDigestCol dgBase 0)))
      ∈ pubkeyCompressConstraints blockBase octetBase dgBase leafTeethCol := by
    simp [pubkeyCompressConstraints]
  have hw := hsat.rowConstraints i hi _ (hsub _ hwin)
  simp only [VmConstraint2.holdsAt, VmConstraint.holdsVm, hlastf] at hw
  have hweld := (eqGate_eval _ _ e).mp (by simpa using hw)
  rw [hweld, hlane0]

/-- **`withMembershipPubkeyCompress_forces` — THE MEMBERSHIP-SENDER KEYSTONE.** A `Satisfied2` of
the welded descriptor forces the published sender-leaf tooth EQUAL to the chip-native compress of
the committed pubkey octet — a forged sender key is UNSAT (modulo the NAMED executor
re-alignment, module doc). -/
theorem withMembershipPubkeyCompress_forces (A : List ℤ → Digest8) (hash : List ℤ → ℤ)
    (base : EffectVmDescriptor2) (leafTeethCol : Nat)
    (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (t : VmTrace)
    (hChip : ChipTableSoundN (permOutOf A) (t.tf .poseidon2))
    (hsat : Satisfied2 hash (withMembershipPubkeyCompress base leafTeethCol) minit mfin maddrs t)
    (i : Nat) (hi : i < t.rows.length) (hnotlast : i + 1 ≠ t.rows.length) :
    (envAt t i).loc leafTeethCol
      = pubkeyCompress1Spec A (octetVals (envAt t i) BEFORE_BLOCK_BASE B_PUBKEY8) :=
  pubkeyCompressConstraints_force A hash _ BEFORE_BLOCK_BASE B_PUBKEY8 base.traceWidth
    leafTeethCol (fun _ hc => List.mem_append_right _ hc) minit mfin maddrs t hChip hsat
    i hi hnotlast

/-- **TOOTH — `withMembershipPubkeyCompress_rejects_forged`.** -/
theorem withMembershipPubkeyCompress_rejects_forged (A : List ℤ → Digest8) (hash : List ℤ → ℤ)
    (base : EffectVmDescriptor2) (leafTeethCol : Nat)
    (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (t : VmTrace)
    (hChip : ChipTableSoundN (permOutOf A) (t.tf .poseidon2))
    (i : Nat) (hi : i < t.rows.length) (hnotlast : i + 1 ≠ t.rows.length)
    (hforged : (envAt t i).loc leafTeethCol
      ≠ pubkeyCompress1Spec A (octetVals (envAt t i) BEFORE_BLOCK_BASE B_PUBKEY8)) :
    ¬ Satisfied2 hash (withMembershipPubkeyCompress base leafTeethCol) minit mfin maddrs t :=
  fun hsat => hforged
    (withMembershipPubkeyCompress_forces A hash base leafTeethCol minit mfin maddrs t hChip hsat
      i hi hnotlast)

#assert_axioms keyCommitConstraints_force
#assert_axioms withSovereignKeyCommit_forces
#assert_axioms withSovereignKeyCommit_rejects_forged
#assert_axioms pubkeyCompressConstraints_force
#assert_axioms withMembershipPubkeyCompress_forces
#assert_axioms withMembershipPubkeyCompress_rejects_forged

-- Self-tests: tuple shapes (the 25-wide chip tuple: 1 arity + CHIP_RATE inputs + 8 lanes),
-- fragment sizes, and a concrete keyCommitSpec evaluation (the [0,4,2,6] interleave bites).
#guard (keyCommitLookup 0 104 900 0).tuple.length == 25
#guard (pubkeyCompressLookup 0 104 900).tuple.length == 25
#guard (keyCommitConstraints 0 104 900 950).length == 8
#guard (pubkeyCompressConstraints 0 104 900 950).length == 2
#guard (pubkeyNode8Inputs 0 104).length == 16
#guard decide (keyCommitSpec (fun xs _ => xs.sum) (fun i => (i.val : ℤ)) 2 = 12)
#guard decide (keyCommitSpec (fun xs _ => xs.sum) (fun i => (i.val : ℤ)) 3 = 16)
#guard decide (pubkeyCompress1Spec (fun xs _ => xs.sum) (fun i => (i.val : ℤ)) = 28)

/-! ## §3 — THE FIELDS-ROOT READ-OPEN (membership `authorized_root`).

NOT geometry (plan O3): `fields_root` (limb `B_FIELDS_ROOT` = 36 + completions) is ALREADY a
committed-faithful 8-felt root; the authorized-set root is a fields-map VALUE under it. The gate
is the EXISTING fields-open READ appendix (`fieldsOpenConstraints` — leaf lookup, 16 shared
`node8` levels, dir booleanity, root pin) plus three welds: the appendix root group == the
committed BEFORE `fields_root` block (`beforeRootWeldsF`, reused verbatim), the read leaf's addr
== the declared `set_root_index` column, and the read leaf's VALUE == the published root-teeth
column. -/

/-- **`fieldsReadAt8 S8 root k v`** — the faithful 8-felt fields-map READ: some path
membership-authenticates the `(k, v)` leaf under the ~124-bit `root`. The read twin of
`fieldsWritesTo8`. -/
def fieldsReadAt8 (S8 : Fields8Scheme) (root : Digest8) (k v : ℤ) : Prop :=
  ∃ path : List (StepG Digest8),
    recomposeUp8 S8 (fieldsLeafDigest8 S8 (k, v)) path = root

/-- The three read-open welds: 8 before-root pins (reused `beforeRootWeldsF`) + the key bind
(`leaf 0 == idxCol`, the declared `set_root_index` column) + the value expose (`leaf 1 ==
rootTeethCol`, the published authorized-root tooth). -/
def fieldsReadOpenWelds (w idxCol rootTeethCol : Nat) : List VmConstraint2 :=
  beforeRootWeldsF w
  ++ [ VmConstraint2.base (.gate (eqGate ((capOpenCols w).leaf 0) idxCol))
     , VmConstraint2.base (.gate (eqGate ((capOpenCols w).leaf 1) rootTeethCol)) ]

/-- **`effFieldsReadOpenV3 base name idxCol rootTeethCol`** — the fields-open READ descriptor:
`effFieldsOpenV3` (the read appendix, width `+CAP_OPEN_SPAN`) plus the read-open welds. -/
def effFieldsReadOpenV3 (base : EffectVmDescriptor2) (name : String)
    (idxCol rootTeethCol : Nat) : EffectVmDescriptor2 :=
  { effFieldsOpenV3 base name with
    constraints := (effFieldsOpenV3 base name).constraints
      ++ fieldsReadOpenWelds base.traceWidth idxCol rootTeethCol }

/-- Every read-open weld is a constraint of the descriptor. -/
theorem effFieldsReadOpenV3_weldMem (base : EffectVmDescriptor2) (name : String)
    (idxCol rootTeethCol : Nat) (c : VmConstraint2)
    (hc : c ∈ fieldsReadOpenWelds base.traceWidth idxCol rootTeethCol) :
    c ∈ (effFieldsReadOpenV3 base name idxCol rootTeethCol).constraints :=
  List.mem_append_right _ hc

/-- A `Satisfied2` of the read-open descriptor strips to a `Satisfied2` of the bare
`effFieldsOpenV3` — the welds are all `.base (.gate …)`, contributing no map/mem op. -/
theorem effFieldsReadOpenV3_strips_to_fieldsOpen (hash : List ℤ → ℤ)
    (base : EffectVmDescriptor2) (name : String) (idxCol rootTeethCol : Nat)
    (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (t : VmTrace)
    (h : Satisfied2 hash (effFieldsReadOpenV3 base name idxCol rootTeethCol)
      minit mfin maddrs t) :
    Satisfied2 hash (effFieldsOpenV3 base name) minit mfin maddrs t := by
  have hmapOps : Dregg2.Circuit.DescriptorIR2.mapOpsOf
        (effFieldsReadOpenV3 base name idxCol rootTeethCol)
      = Dregg2.Circuit.DescriptorIR2.mapOpsOf (effFieldsOpenV3 base name) := by
    simp [Dregg2.Circuit.DescriptorIR2.mapOpsOf, effFieldsReadOpenV3, fieldsReadOpenWelds,
      Dregg2.Circuit.Emit.FieldsOpenEmit.beforeRootWeldsF,
      List.filterMap_append, List.filterMap_map]
  have hmemOps : Dregg2.Circuit.DescriptorIR2.memOpsOf
        (effFieldsReadOpenV3 base name idxCol rootTeethCol)
      = Dregg2.Circuit.DescriptorIR2.memOpsOf (effFieldsOpenV3 base name) := by
    simp [Dregg2.Circuit.DescriptorIR2.memOpsOf, effFieldsReadOpenV3, fieldsReadOpenWelds,
      Dregg2.Circuit.Emit.FieldsOpenEmit.beforeRootWeldsF,
      List.filterMap_append, List.filterMap_map]
  have hmemLog : Dregg2.Circuit.DescriptorIR2.memLog
        (effFieldsReadOpenV3 base name idxCol rootTeethCol) t
      = Dregg2.Circuit.DescriptorIR2.memLog (effFieldsOpenV3 base name) t := by
    simp [Dregg2.Circuit.DescriptorIR2.memLog, hmemOps]
  have hmapLog : Dregg2.Circuit.DescriptorIR2.mapLog
        (effFieldsReadOpenV3 base name idxCol rootTeethCol) t
      = Dregg2.Circuit.DescriptorIR2.mapLog (effFieldsOpenV3 base name) t := by
    simp [Dregg2.Circuit.DescriptorIR2.mapLog, hmapOps]
  exact
    { rowConstraints := fun i hi c hc =>
        h.rowConstraints i hi c (by
          show c ∈ (effFieldsOpenV3 base name).constraints
            ++ fieldsReadOpenWelds base.traceWidth idxCol rootTeethCol
          exact List.mem_append_left _ hc)
      rowHashes := h.rowHashes
      rowRanges := h.rowRanges
      memAddrsNodup := h.memAddrsNodup
      memClosed := by have := h.memClosed; rwa [hmemLog] at this
      memDisciplined := by have := h.memDisciplined; rwa [hmemLog] at this
      memBalanced := by have := h.memBalanced; rwa [hmemLog] at this
      memTableFaithful := by have := h.memTableFaithful; rwa [hmemLog] at this
      mapTableFaithful := by have := h.mapTableFaithful; rwa [hmapLog] at this }

/-- Any read-open weld gate forces `eval = 0` on an active (non-last) row. -/
theorem fieldsReadOpen_gate_forces (base : EffectVmDescriptor2) (name : String)
    (idxCol rootTeethCol : Nat) (hash : List ℤ → ℤ)
    (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (t : VmTrace)
    (hsat : Satisfied2 hash (effFieldsReadOpenV3 base name idxCol rootTeethCol)
      minit mfin maddrs t)
    (i : Nat) (hi : i < t.rows.length) (hnotlast : i + 1 ≠ t.rows.length)
    (g : EmittedExpr)
    (hin : VmConstraint2.base (.gate g)
      ∈ fieldsReadOpenWelds base.traceWidth idxCol rootTeethCol) :
    g.eval (envAt t i).loc = 0 := by
  have hlastf : (i + 1 == t.rows.length) = false := by
    simp only [beq_eq_false_iff_ne]; exact hnotlast
  have h := hsat.rowConstraints i hi _
    (effFieldsReadOpenV3_weldMem base name idxCol rootTeethCol _ hin)
  simp only [VmConstraint2.holdsAt, VmConstraint.holdsVm, hlastf] at h
  simpa using h

/-- **`effFieldsReadOpenV3_forces_read8` — THE MEMBERSHIP-ROOT KEYSTONE.** A `Satisfied2` of the
read-open descriptor TRACE-FORCES: the published root-teeth felt IS the fields-map value at the
declared `set_root_index`, membership-authenticated under the committed BEFORE ~124-bit
`fields_root` block. A forged authorized-root tooth (any value NOT under the committed fields
root at that key) is UNSAT for a ledgerless client. -/
theorem effFieldsReadOpenV3_forces_read8 (S8 : Fields8Scheme)
    (base : EffectVmDescriptor2) (name : String) (idxCol rootTeethCol : Nat)
    (hash : List ℤ → ℤ) (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ)
    (t : VmTrace)
    (hChip : ChipTableSoundN (fieldsPermOut S8) (t.tf .poseidon2))
    (hsat : Satisfied2 hash (effFieldsReadOpenV3 base name idxCol rootTeethCol)
      minit mfin maddrs t)
    (i : Nat) (hi : i < t.rows.length) (hnotlast : i + 1 ≠ t.rows.length) :
    fieldsReadAt8 S8
      (Dregg2.Circuit.Emit.EffectVmEmitRotationV3.beforeFieldsRootCols (envAt t i))
      ((envAt t i).loc idxCol) ((envAt t i).loc rootTeethCol) := by
  set e := envAt t i with he
  -- the read core (leaf lookup, node lookups, dir booleanity, root pin) via the strip.
  have hstrip := effFieldsReadOpenV3_strips_to_fieldsOpen hash base name idxCol rootTeethCol
    minit mfin maddrs t hsat
  have hcore : FieldsMembershipCore t.tf (capOpenCols base.traceWidth) e :=
    effFieldsOpenV3_core base name hash minit mfin maddrs t hstrip i hi hnotlast
  have hrec := fieldsOpen_recompose8 S8 t.tf (capOpenCols base.traceWidth) e hChip hcore
  -- weld: the appendix root group IS the committed BEFORE fields-root block.
  have hroot : groupVal e (capOpenCols base.traceWidth).capRoot
      = Dregg2.Circuit.Emit.EffectVmEmitRotationV3.beforeFieldsRootCols e := by
    funext k
    have hin : VmConstraint2.base (.gate (eqGate ((capOpenCols base.traceWidth).capRoot k)
        (Dregg2.Circuit.Emit.EffectVmEmitRotationV3.fieldsRootGroupCol EFFECT_VM_WIDTH k)))
        ∈ fieldsReadOpenWelds base.traceWidth idxCol rootTeethCol := by
      refine List.mem_append_left _ ?_
      exact List.mem_map.mpr ⟨k, List.mem_finRange k, rfl⟩
    have := (eqGate_eval _ _ e).mp
      (fieldsReadOpen_gate_forces base name idxCol rootTeethCol hash minit mfin maddrs t hsat
        i hi hnotlast _ hin)
    simpa [groupVal, Dregg2.Circuit.Emit.EffectVmEmitRotationV3.beforeFieldsRootCols] using this
  -- weld: the read leaf's addr is the declared set_root_index column.
  have hidx : e.loc ((capOpenCols base.traceWidth).leaf 0) = e.loc idxCol := by
    have hin : VmConstraint2.base (.gate (eqGate ((capOpenCols base.traceWidth).leaf 0) idxCol))
        ∈ fieldsReadOpenWelds base.traceWidth idxCol rootTeethCol := by
      refine List.mem_append_right _ ?_
      simp
    exact (eqGate_eval _ _ e).mp
      (fieldsReadOpen_gate_forces base name idxCol rootTeethCol hash minit mfin maddrs t hsat
        i hi hnotlast _ hin)
  -- weld: the read leaf's value is the published root-teeth column.
  have hval : e.loc ((capOpenCols base.traceWidth).leaf 1) = e.loc rootTeethCol := by
    have hin : VmConstraint2.base (.gate (eqGate ((capOpenCols base.traceWidth).leaf 1)
        rootTeethCol))
        ∈ fieldsReadOpenWelds base.traceWidth idxCol rootTeethCol := by
      refine List.mem_append_right _ ?_
      simp
    exact (eqGate_eval _ _ e).mp
      (fieldsReadOpen_gate_forces base name idxCol rootTeethCol hash minit mfin maddrs t hsat
        i hi hnotlast _ hin)
  -- assemble the read.
  have hpair : fieldsLeafPairOf (capOpenCols base.traceWidth) e
      = (e.loc idxCol, e.loc rootTeethCol) := by
    unfold Dregg2.Circuit.Emit.FieldsOpenEmit.fieldsLeafPairOf
    rw [hidx, hval]
  rw [hpair, hroot] at hrec
  exact ⟨pathOf8 (capOpenCols base.traceWidth) e DEPTH, hrec⟩

/-- **TOOTH — `effFieldsReadOpenV3_rejects_nonmember`.** If NO path authenticates the published
`(set_root_index, root-teeth)` pair under the committed fields root, the descriptor is UNSAT. -/
theorem effFieldsReadOpenV3_rejects_nonmember (S8 : Fields8Scheme)
    (base : EffectVmDescriptor2) (name : String) (idxCol rootTeethCol : Nat)
    (hash : List ℤ → ℤ) (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ)
    (t : VmTrace)
    (hChip : ChipTableSoundN (fieldsPermOut S8) (t.tf .poseidon2))
    (i : Nat) (hi : i < t.rows.length) (hnotlast : i + 1 ≠ t.rows.length)
    (hnon : ¬ fieldsReadAt8 S8
      (Dregg2.Circuit.Emit.EffectVmEmitRotationV3.beforeFieldsRootCols (envAt t i))
      ((envAt t i).loc idxCol) ((envAt t i).loc rootTeethCol)) :
    ¬ Satisfied2 hash (effFieldsReadOpenV3 base name idxCol rootTeethCol) minit mfin maddrs t :=
  fun hsat => hnon
    (effFieldsReadOpenV3_forces_read8 S8 base name idxCol rootTeethCol hash minit mfin maddrs t
      hChip hsat i hi hnotlast)

#assert_axioms effFieldsReadOpenV3_strips_to_fieldsOpen
#assert_axioms fieldsReadOpen_gate_forces
#assert_axioms effFieldsReadOpenV3_forces_read8
#assert_axioms effFieldsReadOpenV3_rejects_nonmember

-- Self-tests: the weld fragment carries exactly 8 root pins + 2 binds.
#guard (fieldsReadOpenWelds 500 1 2).length == 10

end Dregg2.Circuit.Emit.CarrierOctetGates
