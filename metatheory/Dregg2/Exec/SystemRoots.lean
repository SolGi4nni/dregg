/-
# Dregg2.Exec.SystemRoots — STAGE 3 of the record-layer upgrade: the dedicated
`system_roots` sub-block (Option C1 of `_RECORD-LAYER-UPGRADE.md` §C).

`_RECORD-LAYER-UPGRADE.md` §C + `_IR-EXTENSION-DESIGN.md` §A/§E. The IR-extension's only error was its
HOME for the side-table roots: it stole the user `fields[1..7]` cells (`_IR-EXTENSION-DESIGN.md:138-143`),
colliding with app data (`subscription` is 8/8-full; `governed-namespace` wants its own slots 6,7).
STAGE 0–2 already FREED the user namespace: keys `≥ 8` overflow onto `FieldsMap.fieldsRoot`. STAGE 3
gives the side-table roots their OWN namespace so they never collide with user fields again.

This module is the dedicated home (the reconciliation of `_IR-EXTENSION-DESIGN.md` onto a separate
namespace). It supplies, in ONE place:

  * **The kernel-owned root INDICES** (`systemRoot` namespace): each side-table gets its OWN fixed
    index in the `system_roots` sub-block —
    `ESCROW · QUEUE · REFCOUNT · STURDYREF · DELEG · NULLIFIER · COMMIT · SEALED_BOXES`. This is the
    home that makes the per-effect side-table descriptors (`EffectVmEmitCreateEscrow` etc.) BINDABLE:
    their root-update gate writes index `i`, never a user `fields[j]`. The reconciliation note
    (`_RECORD-LAYER-UPGRADE.md:246-250`) re-targets each emit file's root from `FIELD_BASE+i` onto
    `SYSTEM_ROOT_BASE+i` — these are those constants.

  * **`systemRoots`** — the kernel-owned `[FieldElem; N_SYSTEM_ROOTS]` sub-block, modelled as a total
    function `Fin N_SYSTEM_ROOTS → FieldElem` (the Lean mirror of the Rust `[FieldElement; 8]`).
    `emptySystemRoots` is the all-empty-tree-sentinel default a legacy cell carries.

  * **`systemRootsDigest`** — the SINGLE committed root over the 8 side-table roots, a `ListCommit`-style
    injective `compressN` sponge over the ordered root cells. This is the carrier the circuit absorbs
    into `state_commit` by the same GROUP-4 hash-site mechanism `fields_root` uses (`_RECORD-LAYER-
    UPGRADE.md:227-232`): one column / one absorb input, width-neutral. Apps NEVER address it.

  * **`cellCommitS`** — the canonical cell commitment EXTENDED to absorb `systemRootsDigest` as ONE
    more limb (mirroring how STAGE 1's `RecordCommit.cellCommit` absorbs `fieldsRoot`). The anti-ghost
    tooth + legacy no-op are PROVED over it:
      - `cellCommitS_binds_systemRoots` — equal commitments ⇒ equal `systemRootsDigest` ⇒
        (off the digest injectivity) the SAME 8 side-table roots. Tampering ANY side-table root
        (escrow drop, nullifier omission, …) FLIPS its root ⇒ flips the digest ⇒ flips the commitment
        ⇒ UNSAT against the pinned `state_commit`. This is the per-effect anti-ghost tooth the coverage
        memos demand, lifted to ALL 8 side-tables at once.
      - `legacy_commitS_absorbs_empty_roots` — a LEGACY cell (all-sentinel `system_roots`)
        commits BYTE-IDENTICALLY to the empty-roots reference: the absorbed digest is the fixed
        `emptySystemRootsDigest` constant, cell-INDEPENDENT, so folding it in is a uniform no-op.
        Legacy cells/commitments are UNCHANGED (strictly additive backward-compat).

  * the VACUITY GUARD (`_RECORD-LAYER-UPGRADE.md` §D.4): pos + neg `#guard`s, no `native_decide` — a
    populated-side-table cell's commitment DIFFERS from the empty reference (load-bearing), a tampered
    root MOVES it (anti-ghost), and two cells with the SAME roots commit IDENTICALLY (completeness).
    A `systemRootsDigest := 0` stub would collapse the positive guard — forbidden.

Pure, computable, `#guard`-able (no `native_decide`). Reuses `Circuit.ListCommit.listDigest` /
`compressNInjective` (the already-built injective accumulator portal) — never a new axiom.
`#assert_axioms` whitelists `{propext, Classical.choice, Quot.sound}`.
-/
import Dregg2.Circuit.ListCommit

namespace Dregg2.Exec.SystemRoots

open Dregg2.Circuit.StateCommit (compressNInjective)
open Dregg2.Circuit.ListCommit

/-! ## §1 — the kernel-owned root INDICES (the dedicated home).

Each side-table gets its OWN fixed index in the `system_roots` sub-block. These mirror the Rust
`state::system_root::*` constants and the `_IR-EXTENSION-DESIGN.md` §E close-plan's root assignments,
re-targeted off the user `fields[1..7]` onto this dedicated namespace (`_RECORD-LAYER-UPGRADE.md`
Option C1). Distinct, kernel-only, never reachable by a `SetField` (which addresses user keys only). -/

namespace systemRoot
/-- `escrows` list digest (createEscrow / refund / release / bridge-park). -/
def ESCROW       : Nat := 0
/-- `queues` table digest. FIFO order intrinsic. (F2a: the queue verb family dissolved into
the factory cells; the kernel `queues` table + this root die in F2b with the VK rotation.) -/
def QUEUE        : Nat := 1
/-- refcount table digest (dropRef GC); was the running prover's `fields[3]` mirror. -/
def REFCOUNT     : Nat := 2
/-- `swiss` sturdyref table digest (export / enliven / handoff / drop); was `fields[4]`. -/
def STURDYREF    : Nat := 3
/-- `delegations` keyed-map digest (refresh / revoke delegation epoch). -/
def DELEG        : Nat := 4
/-- `nullifiers` accumulator digest (noteSpend append; non-membership via spend-proof PI). -/
def NULLIFIER    : Nat := 5
/-- `commitments` accumulator digest (noteCreate append). -/
def COMMIT       : Nat := 6
/-- `sealedBoxes` store digest (seal / unseal / createSealPair); its OWN home, not folded
into `cap_root` (the §E note shared it with the c-list root under duress; STAGE 3 frees it). -/
def SEALED_BOXES : Nat := 7
end systemRoot

/-- **`N_SYSTEM_ROOTS`** — the size of the dedicated `system_roots` sub-block (`= 8`, one per
side-table). Parallel to (and disjoint from) the 8 user `fields[0..7]` and the `fields_root` map. -/
def N_SYSTEM_ROOTS : Nat := 8

/-! ## §2 — the `system_roots` sub-block + its committed digest (`systemRootsDigest`).

The Lean mirror of the Rust `system_roots: [FieldElement; 8]`: a total map `Fin 8 → FieldElem`.
Each index holds ONE side-table's root, mutated ONLY by that side-table's kernel transition (escrow /
queue / nullifier / …), NEVER by a user `SetField`. The committed `systemRootsDigest` is the single
`listDigest` sponge over the 8 ordered roots — the ONE column the circuit absorbs. -/

/-- A field element (the same `ℤ`-carrier `ListCommit`/`StateCommit` use for a Poseidon felt). -/
abbrev FieldElem := ℤ

/-- **`SysRoots`** — the kernel-owned side-table-root sub-block: a total function from the fixed
root index to its committed `FieldElem`. The Lean mirror of the Rust `[FieldElement; N_SYSTEM_ROOTS]`. -/
abbrev SysRoots := Fin N_SYSTEM_ROOTS → FieldElem

/-- **`rootList sr`** — the 8 side-table roots as an ORDERED list (index 0..7), the input the
`systemRootsDigest` sponge commits. Order is fixed by the kernel-owned index assignment (§1), so the
digest is order-canonical (a swap of two side-tables' roots is a DIFFERENT digest). Uses `List.ofFn`
(definitionally `(finRange n).map sr`), so the digest binds the WHOLE function via `List.ofFn_inj`. -/
def rootList (sr : SysRoots) : List FieldElem :=
  List.ofFn sr

/-- **`systemRootsDigest compressN sr`** — the SINGLE committed root over the `system_roots` sub-block:
the `ListCommit.listDigest` over `rootList sr` under the identity leaf (the roots are ALREADY field
elements — each side-table's own `listDigest`/`keyedDigest` produced them). This is the one column the
circuit carries; the GROUP-4 site absorbs it into `state_commit` exactly as it absorbs `fields_root`
(`_RECORD-LAYER-UPGRADE.md` §C). -/
def systemRootsDigest (compressN : List FieldElem → FieldElem) (sr : SysRoots) : FieldElem :=
  listDigest id compressN (rootList sr)

/-- **`emptySystemRoots`** — the all-empty-tree-sentinel sub-block a LEGACY cell carries (every
side-table empty). The Lean mirror of the Rust `[FIELD_ZERO; N_SYSTEM_ROOTS]` default. -/
def emptySystemRoots : SysRoots := fun _ => 0

/-- **`emptySystemRootsDigest compressN`** — the FIXED `systemRootsDigest` of an empty sub-block: a
cell-INDEPENDENT constant. A legacy cell carries exactly this, so absorbing it into a commitment is a
uniform no-op (the STAGE 3 backward-compat keystone, next section). -/
def emptySystemRootsDigest (compressN : List FieldElem → FieldElem) : FieldElem :=
  systemRootsDigest compressN emptySystemRoots

/-! ## §3 — injectivity: `systemRootsDigest` binds the WHOLE sub-block (anti-ghost foundation). -/

/-- **`systemRootsDigest_binds`.** Equal digests force the SAME ordered root list. Off the
single realizable `compressN`-injectivity carrier (`ListCommit.ListDigestBindsList` with the identity
leaf, which is trivially injective). So tampering ANY side-table root — a dropped escrow, an omitted
nullifier, a reordered queue — produces a DIFFERENT `systemRootsDigest`: the anti-ghost foundation. -/
theorem systemRootsDigest_binds (compressN : List FieldElem → FieldElem)
    (hN : compressNInjective compressN) (sr sr' : SysRoots)
    (h : systemRootsDigest compressN sr = systemRootsDigest compressN sr') :
    rootList sr = rootList sr' :=
  ListDigestBindsList id compressN hN (fun _ _ h => h) _ _ h

/-- **`systemRootsDigest_binds_fn`.** Equal digests force the WHOLE sub-block FUNCTION equal.
`rootList = List.ofFn`, and `List.ofFn_inj` says `ofFn sr = ofFn sr' → sr = sr'`. So if the committed
digest is fixed, the entire `system_roots` sub-block is pinned. -/
theorem systemRootsDigest_binds_fn (compressN : List FieldElem → FieldElem)
    (hN : compressNInjective compressN) (sr sr' : SysRoots)
    (h : systemRootsDigest compressN sr = systemRootsDigest compressN sr') :
    sr = sr' := by
  have hlist : rootList sr = rootList sr' := systemRootsDigest_binds compressN hN sr sr' h
  exact List.ofFn_inj.mp hlist

/-- **`systemRootsDigest_binds_pointwise`.** Equal digests force EVERY side-table root equal
(pointwise at each kernel index `i`). The per-index anti-ghost statement: if the committed digest is
fixed, NO side-table root can be tampered. Combined with the commitment absorption (§4), this is the
3-corner anti-ghost tooth for all 8 side-tables. -/
theorem systemRootsDigest_binds_pointwise (compressN : List FieldElem → FieldElem)
    (hN : compressNInjective compressN) (sr sr' : SysRoots)
    (h : systemRootsDigest compressN sr = systemRootsDigest compressN sr') (i : Fin N_SYSTEM_ROOTS) :
    sr i = sr' i :=
  congrFun (systemRootsDigest_binds_fn compressN hN sr sr' h) i

/-! ## §4 — the canonical cell commitment EXTENDED to absorb `systemRootsDigest`.

We extend the STAGE-1 commitment model (`RecordCommit.cellCommit`) with ONE more absorbed limb — the
`systemRootsDigest` — at a fixed position (mirroring a Rust `hasher.update(&system_roots_digest)`
right after the `fields_root` absorb). The `rest` prefix abstracts every OTHER limb (identity, mode,
nonce, balance, fixed fields, …, `fields_root`); STAGE 3 changes NONE of it. -/

section Surface
variable (compressN : List FieldElem → FieldElem)

/-- **`cellCommitS compressN rest sr`** — the canonical cell commitment with the `system_roots`
sub-block digest absorbed as ONE extra limb: the sponge over `rest ++ [systemRootsDigest sr]`. -/
def cellCommitS (rest : List FieldElem) (sr : SysRoots) : FieldElem :=
  compressN (rest ++ [systemRootsDigest compressN sr])

/-- **`legacyReferenceCommitS compressN rest`** — the commitment of a LEGACY cell with the EMPTY
sub-block digest folded in by hand: the sponge over `rest ++ [emptySystemRootsDigest]`. A
cell-INDEPENDENT constant in the system-roots slot — the no-op fold (the Rust
`legacy_reference_commitment` analog for `system_roots`). -/
def legacyReferenceCommitS (rest : List FieldElem) : FieldElem :=
  compressN (rest ++ [emptySystemRootsDigest compressN])

/-- **`cellCommitS_binds_systemRoots` (the anti-ghost tooth).** Equal canonical commitments
(over the SAME `rest`) force the SAME `systemRootsDigest`. Off the `compressN`-injectivity carrier:
the sponge binds its input list, the shared `rest` cancels, the singleton digest limbs are equal.
Combined with `systemRootsDigest_binds_pointwise`, this is the per-side-table anti-ghost tooth:
two cells with the SAME commitment have the SAME 8 side-table roots, so tampering ANY of them
provably MOVES the commitment. A `systemRootsDigest := 0` stub would make this vacuous — forbidden. -/
theorem cellCommitS_binds_systemRoots
    (hN : compressNInjective compressN) (rest : List FieldElem) (sr sr' : SysRoots)
    (h : cellCommitS compressN rest sr = cellCommitS compressN rest sr') :
    systemRootsDigest compressN sr = systemRootsDigest compressN sr' := by
  unfold cellCommitS at h
  have hlist : rest ++ [systemRootsDigest compressN sr]
      = rest ++ [systemRootsDigest compressN sr'] := hN _ _ h
  have := List.append_cancel_left hlist
  simpa using this

/-- **`cellCommitS_binds_roots_pointwise` (corollary).** Equal commitments force EVERY
side-table root equal. The full chain: equal commitment ⇒ equal digest
(`cellCommitS_binds_systemRoots`) ⇒ equal roots pointwise (`systemRootsDigest_binds_pointwise`). This
is "the canonical commitment binds the whole side-table state" — the soundness statement STAGE 3
buys for ALL 8 side-tables. -/
theorem cellCommitS_binds_roots_pointwise
    (hN : compressNInjective compressN) (rest : List FieldElem) (sr sr' : SysRoots)
    (h : cellCommitS compressN rest sr = cellCommitS compressN rest sr') (i : Fin N_SYSTEM_ROOTS) :
    sr i = sr' i :=
  systemRootsDigest_binds_pointwise compressN hN sr sr'
    (cellCommitS_binds_systemRoots compressN hN rest sr sr' h) i

/-- **`legacy_commitS_absorbs_empty_roots` (the backward-compat keystone).** A LEGACY cell
(all-sentinel `system_roots`, i.e. every side-table empty) has a canonical commitment BYTE-IDENTICAL
to the empty-roots reference. Its `systemRootsDigest` is the FIXED `emptySystemRootsDigest` constant,
independent of the cell, so the absorbed limb is the same constant for every legacy cell: folding it
in changes nothing. This is the STAGE 3 strictly-additive guarantee — legacy cells/commitments are
UNCHANGED (the Rust `legacy_cells_share_system_roots_contribution` test's Lean shadow). -/
theorem legacy_commitS_absorbs_empty_roots (rest : List FieldElem) :
    cellCommitS compressN rest emptySystemRoots = legacyReferenceCommitS compressN rest := rfl

/-- **`legacy_commitsS_agree` (corollary).** ANY two LEGACY cells (both with an all-sentinel
`system_roots` sub-block, `sr = sr' = emptySystemRoots`) commit IDENTICALLY over the same `rest`: the
absorbed digest is the same fixed constant for both, so the absorption does not distinguish legacy
cells (uniform no-op). Stated for two hypothesised-legacy sub-blocks to make the no-op
load-bearing (not a syntactic `x = x`). -/
theorem legacy_commitsS_agree (rest : List FieldElem) (sr sr' : SysRoots)
    (hsr : sr = emptySystemRoots) (hsr' : sr' = emptySystemRoots) :
    cellCommitS compressN rest sr = cellCommitS compressN rest sr' := by
  rw [hsr, hsr']

end Surface

/-! ## §5 — VACUITY GUARD (`_RECORD-LAYER-UPGRADE.md` §D.4): pos + neg, no `native_decide`.

Concrete computable instances over the same toy CR sponge the §FieldsMap/§RecordCommit guards use. A
POSITIVE guard: a populated-side-table cell's commitment DIFFERS from the legacy reference (the
absorption is load-bearing). A NO-OP guard: a legacy (all-empty) cell's commitment EQUALS the
empty-roots reference. An ANTI-GHOST guard: tampering ONE side-table root MOVES the commitment. A
`systemRootsDigest := 0` stub would collapse the positive/anti-ghost guards. -/

-- A concrete commitment sponge (the same toy injective Horner fold the sibling modules use).
private def cNC : List Int → Int := fun xs => xs.foldl (fun acc x => acc * 1000003 + x) (xs.length : Int)
private def restC : List Int := [7, 11, 13]

-- A legacy sub-block (all side-tables empty) and one with a populated escrow + nullifier root.
private def legacyRoots : SysRoots := emptySystemRoots
private def populatedRoots : SysRoots := fun i =>
  if i = (⟨systemRoot.ESCROW, by decide⟩ : Fin N_SYSTEM_ROOTS) then 1234
  else if i = (⟨systemRoot.NULLIFIER, by decide⟩ : Fin N_SYSTEM_ROOTS) then 42
  else 0
-- A TAMPERED sub-block: same as populated but the escrow root flipped (an attacker dropping an escrow).
private def tamperedRoots : SysRoots := fun i =>
  if i = (⟨systemRoot.ESCROW, by decide⟩ : Fin N_SYSTEM_ROOTS) then 9999
  else if i = (⟨systemRoot.NULLIFIER, by decide⟩ : Fin N_SYSTEM_ROOTS) then 42
  else 0

-- NO-OP: a legacy (all-empty) sub-block's commitment EQUALS the empty-roots reference (byte-identical).
#guard decide (cellCommitS cNC restC legacyRoots = legacyReferenceCommitS cNC restC)

-- POSITIVE (load-bearing): a POPULATED sub-block's commitment DIFFERS from the legacy reference
-- (the absorbed digest is non-constant — a `:= 0` stub would make these EQUAL: forbidden).
#guard decide (cellCommitS cNC restC populatedRoots = legacyReferenceCommitS cNC restC) == false

-- ANTI-GHOST: tampering ONE side-table root (escrow drop) MOVES the commitment.
#guard decide (cellCommitS cNC restC populatedRoots = cellCommitS cNC restC tamperedRoots) == false

-- The digest itself distinguishes them (the carrier is committing the sub-block):
#guard decide (systemRootsDigest cNC populatedRoots = systemRootsDigest cNC tamperedRoots) == false
#guard decide (systemRootsDigest cNC legacyRoots = emptySystemRootsDigest cNC)

-- COMPLETENESS dual: two cells with the SAME side-table roots commit IDENTICALLY.
#guard decide (cellCommitS cNC restC populatedRoots
             = cellCommitS cNC restC (fun i =>
                 if i = (⟨systemRoot.ESCROW, by decide⟩ : Fin N_SYSTEM_ROOTS) then 1234
                 else if i = (⟨systemRoot.NULLIFIER, by decide⟩ : Fin N_SYSTEM_ROOTS) then 42
                 else 0))

-- The 8 kernel indices are DISTINCT (the dedicated home assigns each side-table its own column):
#guard [systemRoot.ESCROW, systemRoot.QUEUE, systemRoot.REFCOUNT, systemRoot.STURDYREF,
        systemRoot.DELEG, systemRoot.NULLIFIER, systemRoot.COMMIT, systemRoot.SEALED_BOXES].dedup.length == 8
-- … and all in-range for the sub-block:
#guard [systemRoot.ESCROW, systemRoot.QUEUE, systemRoot.REFCOUNT, systemRoot.STURDYREF,
        systemRoot.DELEG, systemRoot.NULLIFIER, systemRoot.COMMIT, systemRoot.SEALED_BOXES].all
        (· < N_SYSTEM_ROOTS)

#assert_axioms systemRootsDigest_binds
#assert_axioms systemRootsDigest_binds_fn
#assert_axioms systemRootsDigest_binds_pointwise
#assert_axioms cellCommitS_binds_systemRoots
#assert_axioms cellCommitS_binds_roots_pointwise
#assert_axioms legacy_commitS_absorbs_empty_roots
#assert_axioms legacy_commitsS_agree

end Dregg2.Exec.SystemRoots
