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
      - `cellCommitS_binds_systemRoots_or_collides` — equal commitments ⇒ equal `systemRootsDigest` ⇒
        the SAME 8 side-table roots, OR a NAMED collision of the deployed sponge at a pair a total
        extractor returns. Tampering ANY side-table root (escrow drop, nullifier omission, …) FLIPS its
        root ⇒ flips the digest ⇒ flips the commitment ⇒ UNSAT against the pinned `state_commit`, unless
        the prover holds that collision. This is the per-effect anti-ghost tooth the coverage memos
        demand, lifted to ALL 8 side-tables at once.
      - `legacy_commitS_absorbs_empty_roots` — a LEGACY cell (all-sentinel `system_roots`)
        commits BYTE-IDENTICALLY to the empty-roots reference: the absorbed digest is the fixed
        `emptySystemRootsDigest` constant, cell-INDEPENDENT, so folding it in is a uniform no-op.
        Legacy cells/commitments are UNCHANGED (strictly additive backward-compat).

  * the VACUITY GUARD (`_RECORD-LAYER-UPGRADE.md` §D.4): pos + neg `#guard`s, no `native_decide` — a
    populated-side-table cell's commitment DIFFERS from the empty reference (load-bearing), a tampered
    root MOVES it (anti-ghost), and two cells with the SAME roots commit IDENTICALLY (completeness).
    A `systemRootsDigest := 0` stub would collapse the positive guard — forbidden.

Pure, computable, `#guard`-able (no `native_decide`). Reuses `Circuit.ListCommit.listDigest` and the
`Circuit.Poseidon2Binding.SpongeColl` extraction spine — never a new axiom.
`#assert_axioms` whitelists `{propext, Classical.choice, Quot.sound}`.

⚑ **THE INJECTIVITY FLOOR IS GONE FROM EVERY BINDING STATEMENT HERE (07-20).** `systemRootsDigest_binds`,
`_binds_fn`, `_binds_pointwise`, `cellCommitS_binds_systemRoots` and `cellCommitS_binds_roots_pointwise`
each carried `StateCommit.compressNInjective` — the same proposition as `Poseidon2SpongeCR`, which
`HashFloorHonesty` REFUTES at the deployed BabyBear parameters. At the deployed sponge they were
vacuously true and bound nothing. They are DELETED and replaced by extraction-as-data forms
(`…_or_collides`) that assume nothing about the sponge and name the colliding pair a total extractor
returns (`rootsCollFind`/`RootsColl`, `cellCommitSCollFind`/`CellCommitSColl`). §3′ proves the strength
relation BOTH ways as standalone bridges — every deleted theorem is recovered as exactly its injective
special case (`…_of_injective`), and the collision disjunct is refutable there (`…_refutable_of_injective`)
while being genuinely inhabited at a degenerate sponge (`badRootsSponge_has_rootsColl`).
-/
import Dregg2.Circuit.ListCommit
import Dregg2.Circuit.Poseidon2Binding

namespace Dregg2.Exec.SystemRoots

open Dregg2.Circuit.StateCommit (compressNInjective)
open Dregg2.Circuit.ListCommit
open Dregg2.Circuit.Poseidon2Binding (SpongeColl)

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

/-! ## §3 — the digest BINDS the WHOLE sub-block — or hands back the colliding pair.

⚑ **WHAT THIS SECTION USED TO ASSUME, AND WHY IT SAID NOTHING.** `systemRootsDigest_binds`,
`_binds_fn` and `_binds_pointwise` each carried `StateCommit.compressNInjective compressN`. That
predicate is literally `∀ xs ys, compressN xs = compressN ys → xs = ys` — the same proposition as
`Poseidon2Binding.Poseidon2SpongeCR`, and FALSE at the deployed BabyBear parameters:
`HashFloorHonesty.compressNInjective_false_of_finite_range` / `poseidon2SpongeCR_false_babyBear`
refute it by pigeonhole (the infinite `List ℤ` domain compressed into a bounded field). So the three
theorems, and every consumer that instantiated them at the deployed sponge, were VACUOUSLY TRUE
exactly where they were supposed to bind the deployed side-table state. They are DELETED — not kept
beside the new forms, which would be the same sin in additive dress.

The replacement assumes NOTHING. The roots peel is a TOTAL FUNCTION (`rootsCollFind`) that either
proves the ordered root lists equal or hands back the SPECIFIC pair of lists at which the deployed
sponge actually collides. `RootsColl` is a predicate about THAT pair — deliberately NOT
`∃ xs ys, collision`, which pigeonhole makes unconditionally true at deployed parameters and which
would therefore bind nothing at all. The `_of_injective` bridges below recover each deleted statement
as EXACTLY its injective special case, so nothing genuinely proved was given up; what was given up is
the pretence that the deployed sponge satisfies the hypothesis. -/

/-- **`systemRootsDigest_eq_hash_rootList`** — the digest is ONE sponge application over the ordered
root list (`listDigest` under the identity leaf encoder). Definitional: the deployed absorption,
unfolded so the extraction spine applies directly to the roots leg. -/
theorem systemRootsDigest_eq_hash_rootList (compressN : List FieldElem → FieldElem) (sr : SysRoots) :
    systemRootsDigest compressN sr = compressN (rootList sr) := by
  simp [systemRootsDigest, listDigest]

/-- **`rootsCollFind sr sr'`** — the TOTAL extractor for the roots leg: the SPECIFIC pair of lists at
which two `system_roots` sub-blocks sharing a digest must have collided. The sponge absorbs the ordered
root list directly (one application, no inner group), so the peel is the pair of root lists itself —
still a total function of the inputs, still a pair the caller can name and inspect. -/
def rootsCollFind (sr sr' : SysRoots) : List FieldElem × List FieldElem :=
  (rootList sr, rootList sr')

/-- **`RootsColl compressN sr sr'`** — the pair `rootsCollFind` RETURNS is a GENUINE collision of the
deployed sponge: DISTINCT ordered root lists with the SAME digest. The named disjunct every cured
statement below carries in place of the refuted injectivity floor.

This is the ONE definition of the roots-leg collision in the tree: `Circuit.Emit.EffectVmFullStateRunnable`
(and through it the ~40 per-tag wide keystones) `export`s this name rather than carrying a parallel copy. -/
def RootsColl (compressN : List FieldElem → FieldElem) (sr sr' : SysRoots) : Prop :=
  SpongeColl compressN (rootsCollFind sr sr')

/-- **⚑ A REFLEXIVE INSTANCE CANNOT HAVE COLLIDED — AT ANY SPONGE.** A collision needs DISTINCT
inputs, and the extractor fed a sub-block against itself returns a pair of identical lists. So a
consumer applied at `sr = sr'` MUST land in the binding branch, with NO injectivity hypothesis
anywhere. This is what lets a non-vacuity witness be discharged HONESTLY: the keystone audit shows the
keystone fires INTO the binding branch rather than escaping through the disjunct, and it needs no toy
sponge to do so. -/
theorem rootsColl_irrefl (compressN : List FieldElem → FieldElem) (sr : SysRoots) :
    ¬ RootsColl compressN sr sr := by
  rintro ⟨hne, _⟩
  exact hne rfl

/-- **EXACT-PROP SKELETON — ⚑ NOT THE HEADLINE BINDING ANY MORE (see
`Dregg2.Exec.SystemRootsBindingReduction`).** Equal digests EITHER force the SAME ordered root list, OR
the pair `rootsCollFind` returns is a genuine collision of the deployed sponge.

⚑ **WHY THIS IS NO LONGER THE EXPORTED CLAIM.** A bare `binds ∨ collides` quantifies over SOLUTIONS,
and at deployed BabyBear parameters a sponge collision EXISTS by pigeonhole — so the disjunction is
satisfiable through the `collides` branch with `binds` never holding.  Cryptographic hardness
quantifies over EFFICIENT ADVERSARIES.  The exported binding of the eight consensus roots is now the
REDUCTION `SystemRootsBindingReduction.sysRoots_binds_from_polyTime` (forgery as a `Game`, extractor as
a map of adversaries, unconditional advantage inequality, `hEff` discharged by `poly_time` at
`Eff := IsPolyTime`).  This theorem is RETAINED as the deterministic skeleton that reduction's win
relation rests on, and as the base of the `_of_injective` strength bridges below — the same demotion
`Market.WideCommitBoundary` applied to `stateDecode8_pre_faithful`. So tampering ANY side-table root — a dropped escrow, an omitted
nullifier, a reordered queue — either moves the digest or COSTS the prover a named sponge collision.

⚑ **STRENGTH, stated honestly.** As a FORMULA this is weaker than the deleted equality. As CONTENT AT
DEPLOYED PARAMETERS it is strictly stronger, because the deleted premise is unsatisfiable by the real
compressing sponge: the old theorem said nothing about the deployed system and this one holds OF it. -/
theorem systemRootsDigest_binds_or_collides (compressN : List FieldElem → FieldElem)
    (sr sr' : SysRoots)
    (h : systemRootsDigest compressN sr = systemRootsDigest compressN sr') :
    rootList sr = rootList sr' ∨ RootsColl compressN sr sr' := by
  by_cases hne : rootList sr = rootList sr'
  · exact Or.inl hne
  · refine Or.inr ⟨hne, ?_⟩
    show compressN (rootList sr) = compressN (rootList sr')
    rw [← systemRootsDigest_eq_hash_rootList compressN sr,
      ← systemRootsDigest_eq_hash_rootList compressN sr']
    exact h

/-- **EXACT-PROP SKELETON — ⚑ NOT THE HEADLINE (see `SystemRootsBindingReduction`).** Equal
digests force the WHOLE sub-block FUNCTION equal, or hand back the collision.  The whole-function
projection of the SAME binding as `systemRootsDigest_binds_or_collides`; the exported claim is the
reduction `sysRoots_binds_from_polyTime` (all three projections are ONE forgery game). `rootList = List.ofFn`,
and `List.ofFn_inj` says `ofFn sr = ofFn sr' → sr = sr'`. -/
theorem systemRootsDigest_binds_fn_or_collides (compressN : List FieldElem → FieldElem)
    (sr sr' : SysRoots)
    (h : systemRootsDigest compressN sr = systemRootsDigest compressN sr') :
    sr = sr' ∨ RootsColl compressN sr sr' := by
  rcases systemRootsDigest_binds_or_collides compressN sr sr' h with hlist | hcoll
  · exact Or.inl (List.ofFn_inj.mp hlist)
  · exact Or.inr hcoll

/-- **EXACT-PROP SKELETON — ⚑ NOT THE HEADLINE (see `SystemRootsBindingReduction`).**
Equal digests force EVERY side-table root equal (pointwise at each kernel index), or hand back the
collision.  The per-index projection of the same binding; the exported anti-ghost claim for all eight
side-tables is `SystemRootsBindingReduction.sysRoots_binds_from_polyTime` (whose forgery game is won
by exactly a sub-block pair differing at SOME kernel index —
`SystemRootsBindingReduction.sysRoots_forgery_is_break`).  Retained here as the win relation's
deterministic skeleton: if the committed digest
is fixed, NO side-table root can be tampered without a named sponge collision. Combined with the
commitment absorption (§4), this is the 3-corner anti-ghost tooth for all 8 side-tables. -/
theorem systemRootsDigest_binds_pointwise_or_collides (compressN : List FieldElem → FieldElem)
    (sr sr' : SysRoots)
    (h : systemRootsDigest compressN sr = systemRootsDigest compressN sr') :
    (∀ i : Fin N_SYSTEM_ROOTS, sr i = sr' i) ∨ RootsColl compressN sr sr' := by
  rcases systemRootsDigest_binds_fn_or_collides compressN sr sr' h with hfn | hcoll
  · exact Or.inl (fun i => congrFun hfn i)
  · exact Or.inr hcoll

/-! ### §3′ — the STRENGTH RELATION, proved BOTH ways as STANDALONE bridges.

Deliberately NOT hypotheses on any deployed statement: a theorem carrying `compressNInjective` would be
right back where this repair started. They exist so the claim "nothing genuinely proved was given up"
is itself machine-checked, and so the disjunction is visibly not a free pass. -/

/-- **⚑ THE NO-STRENGTH-LOST TOOTH (`_binds`).** The deleted `systemRootsDigest_binds` is EXACTLY the
injective special case of its cured form — same statement, same hypotheses, derived rather than
assumed. -/
theorem systemRootsDigest_binds_of_injective (compressN : List FieldElem → FieldElem)
    (hN : compressNInjective compressN) (sr sr' : SysRoots)
    (h : systemRootsDigest compressN sr = systemRootsDigest compressN sr') :
    rootList sr = rootList sr' := by
  rcases systemRootsDigest_binds_or_collides compressN sr sr' h with hlist | ⟨hne, himg⟩
  · exact hlist
  · exact absurd (hN _ _ himg) hne

/-- **⚑ THE NO-STRENGTH-LOST TOOTH (`_binds_fn`).** The deleted `systemRootsDigest_binds_fn`, recovered. -/
theorem systemRootsDigest_binds_fn_of_injective (compressN : List FieldElem → FieldElem)
    (hN : compressNInjective compressN) (sr sr' : SysRoots)
    (h : systemRootsDigest compressN sr = systemRootsDigest compressN sr') :
    sr = sr' :=
  List.ofFn_inj.mp (systemRootsDigest_binds_of_injective compressN hN sr sr' h)

/-- **⚑ THE NO-STRENGTH-LOST TOOTH (`_binds_pointwise`).** The deleted
`systemRootsDigest_binds_pointwise` — the one with consumers across the note/delegation emit families —
recovered verbatim as the injective special case. -/
theorem systemRootsDigest_binds_pointwise_of_injective (compressN : List FieldElem → FieldElem)
    (hN : compressNInjective compressN) (sr sr' : SysRoots)
    (h : systemRootsDigest compressN sr = systemRootsDigest compressN sr') (i : Fin N_SYSTEM_ROOTS) :
    sr i = sr' i :=
  congrFun (systemRootsDigest_binds_fn_of_injective compressN hN sr sr' h) i

/-- **(CANARY — the collision disjunct is REFUTABLE, so the disjunction is not a free pass.)** At an
injective sponge the extracted pair is NOT a collision, so a cured statement cannot discharge itself by
taking the right branch: the binding half has to do the work. A disjunction whose right side were always
available would carry no more content than `True` — precisely the free pass an `∃ collision`
formulation would have handed over. -/
theorem rootsColl_refutable_of_injective (compressN : List FieldElem → FieldElem)
    (hN : compressNInjective compressN) (sr sr' : SysRoots) :
    ¬ RootsColl compressN sr sr' := by
  rintro ⟨hne, himg⟩
  exact hne (hN _ _ himg)

/-- **(CANARY — the collision branch is REACHABLE.)** A degenerate sponge genuinely collides on two
DISTINCT sub-blocks, so `RootsColl` is not accidentally empty either. Both branches of the cured
disjunction are live across sponges — which is what makes it informative rather than a disguised
equality with extra syntax. -/
def onesSystemRoots : SysRoots := fun _ => 1

theorem badRootsSponge_has_rootsColl :
    RootsColl (fun _ => 0) emptySystemRoots onesSystemRoots := by
  refine ⟨?_, rfl⟩
  show rootList emptySystemRoots ≠ rootList onesSystemRoots
  intro h
  have hfn : emptySystemRoots = onesSystemRoots := List.ofFn_inj.mp h
  have h0 := congrFun hfn (⟨0, by decide⟩ : Fin N_SYSTEM_ROOTS)
  simp [emptySystemRoots, onesSystemRoots] at h0

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

/-- **`cellCommitSCollFind compressN rest sr sr'`** — the TOTAL extractor for the COMMITMENT leg: the
specific pair of absorbed lists at which two cells sharing a `cellCommitS` must have collided. A total
function of the inputs, exactly like `rootsCollFind` one level down. -/
def cellCommitSCollFind (rest : List FieldElem) (sr sr' : SysRoots) :
    List FieldElem × List FieldElem :=
  (rest ++ [systemRootsDigest compressN sr], rest ++ [systemRootsDigest compressN sr'])

/-- **`CellCommitSColl compressN rest sr sr'`** — the pair `cellCommitSCollFind` RETURNS is a GENUINE
collision of the deployed commitment sponge. The named disjunct replacing the deleted
`compressNInjective` carrier at the commitment layer. -/
def CellCommitSColl (rest : List FieldElem) (sr sr' : SysRoots) : Prop :=
  SpongeColl compressN (cellCommitSCollFind compressN rest sr sr')

/-- **⚑ A REFLEXIVE INSTANCE CANNOT HAVE COLLIDED at the commitment layer either** — sponge-agnostic,
no injectivity hypothesis. The commitment-leg twin of `rootsColl_irrefl`. -/
theorem cellCommitSColl_irrefl (rest : List FieldElem) (sr : SysRoots) :
    ¬ CellCommitSColl compressN rest sr sr := by
  rintro ⟨hne, _⟩
  exact hne rfl

/-- **EXACT-PROP SKELETON — ⚑ NOT THE HEADLINE (see `SystemRootsBindingReduction`).** Equal
canonical commitments (over the SAME `rest`) EITHER force the SAME `systemRootsDigest`, OR hand back the
specific pair of absorbed lists at which the deployed sponge collides.  The exported commitment-layer
binding is the reduction `SystemRootsBindingReduction.cellCommitS_binds_from_polyTime`. The shared `rest` cancels and the
singleton digest limbs are compared; nothing is assumed about the sponge.

The old form carried `compressNInjective compressN`, which the deployed BabyBear sponge REFUTES — so it
said nothing about the deployed commitment. A `systemRootsDigest := 0` stub would still make the binding
branch vacuous, and the §5 guards forbid it. -/
theorem cellCommitS_binds_systemRoots_or_collides
    (rest : List FieldElem) (sr sr' : SysRoots)
    (h : cellCommitS compressN rest sr = cellCommitS compressN rest sr') :
    systemRootsDigest compressN sr = systemRootsDigest compressN sr'
    ∨ CellCommitSColl compressN rest sr sr' := by
  unfold cellCommitS at h
  by_cases hne : rest ++ [systemRootsDigest compressN sr]
      = rest ++ [systemRootsDigest compressN sr']
  · refine Or.inl ?_
    have := List.append_cancel_left hne
    simpa using this
  · exact Or.inr ⟨hne, h⟩

/-- **EXACT-PROP SKELETON — ⚑ NOT THE HEADLINE (see `SystemRootsBindingReduction`).** Equal
commitments force EVERY side-table root equal, or name a collision of the deployed sponge — at the
commitment layer (`CellCommitSColl`) or at the roots digest (`RootsColl`).

⚑ **THIS THREE-WAY DISJUNCTION HAS TWO ESCAPE BRANCHES**, which is the shirk compounded.  The exported
form is `SystemRootsBindingReduction.cellRoots_binds_from_polyTime`: ONE forgery game, TWO extracted
finders, the standard UNION BOUND, ONE floor — the two escapes become two ADDED advantages that the
floor kills, and their sum is negligible. The full chain, now TRUE of the deployed
sponge: equal commitment ⇒ equal digest ⇒ equal roots pointwise. This is "the canonical commitment binds
the whole side-table state" — the soundness statement STAGE 3 buys for ALL 8 side-tables, at deployed
parameters instead of under a refuted hypothesis. -/
theorem cellCommitS_binds_roots_pointwise_or_collides
    (rest : List FieldElem) (sr sr' : SysRoots)
    (h : cellCommitS compressN rest sr = cellCommitS compressN rest sr') :
    (∀ i : Fin N_SYSTEM_ROOTS, sr i = sr' i)
    ∨ CellCommitSColl compressN rest sr sr' ∨ RootsColl compressN sr sr' := by
  rcases cellCommitS_binds_systemRoots_or_collides compressN rest sr sr' h with hdig | hcoll
  · rcases systemRootsDigest_binds_pointwise_or_collides compressN sr sr' hdig with hpt | hrcoll
    · exact Or.inl hpt
    · exact Or.inr (Or.inr hrcoll)
  · exact Or.inr (Or.inl hcoll)

/-- **⚑ THE NO-STRENGTH-LOST TOOTH (commitment layer).** The deleted `cellCommitS_binds_systemRoots` is
EXACTLY the injective special case. Standalone bridge, never a hypothesis on a deployed statement. -/
theorem cellCommitS_binds_systemRoots_of_injective
    (hN : compressNInjective compressN) (rest : List FieldElem) (sr sr' : SysRoots)
    (h : cellCommitS compressN rest sr = cellCommitS compressN rest sr') :
    systemRootsDigest compressN sr = systemRootsDigest compressN sr' := by
  rcases cellCommitS_binds_systemRoots_or_collides compressN rest sr sr' h with hdig | ⟨hne, himg⟩
  · exact hdig
  · exact absurd (hN _ _ himg) hne

/-- **⚑ THE NO-STRENGTH-LOST TOOTH (commitment corollary).** The deleted
`cellCommitS_binds_roots_pointwise`, recovered verbatim. -/
theorem cellCommitS_binds_roots_pointwise_of_injective
    (hN : compressNInjective compressN) (rest : List FieldElem) (sr sr' : SysRoots)
    (h : cellCommitS compressN rest sr = cellCommitS compressN rest sr') (i : Fin N_SYSTEM_ROOTS) :
    sr i = sr' i :=
  systemRootsDigest_binds_pointwise_of_injective compressN hN sr sr'
    (cellCommitS_binds_systemRoots_of_injective compressN hN rest sr sr' h) i

/-- **(CANARY — the commitment-layer collision disjunct is REFUTABLE.)** At an injective sponge the
extracted pair is not a collision, so `cellCommitS_binds_*_or_collides` cannot discharge itself through
the escape. -/
theorem cellCommitSColl_refutable_of_injective
    (hN : compressNInjective compressN) (rest : List FieldElem) (sr sr' : SysRoots) :
    ¬ CellCommitSColl compressN rest sr sr' := by
  rintro ⟨hne, himg⟩
  exact hne (hN _ _ himg)

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

-- The roots-leg collision branch is REACHABLE (a degenerate sponge inhabits it) and IRREFLEXIVE
-- (`rootsColl_irrefl`), so the cured disjunction is two-valued rather than a free pass:
#guard decide (rootList emptySystemRoots = rootList onesSystemRoots) == false

#assert_axioms systemRootsDigest_eq_hash_rootList
#assert_axioms rootsColl_irrefl
#assert_axioms systemRootsDigest_binds_or_collides
#assert_axioms systemRootsDigest_binds_fn_or_collides
#assert_axioms systemRootsDigest_binds_pointwise_or_collides
#assert_axioms systemRootsDigest_binds_of_injective
#assert_axioms systemRootsDigest_binds_fn_of_injective
#assert_axioms systemRootsDigest_binds_pointwise_of_injective
#assert_axioms rootsColl_refutable_of_injective
#assert_axioms badRootsSponge_has_rootsColl
#assert_axioms cellCommitSColl_irrefl
#assert_axioms cellCommitS_binds_systemRoots_or_collides
#assert_axioms cellCommitS_binds_roots_pointwise_or_collides
#assert_axioms cellCommitS_binds_systemRoots_of_injective
#assert_axioms cellCommitS_binds_roots_pointwise_of_injective
#assert_axioms cellCommitSColl_refutable_of_injective
#assert_axioms legacy_commitS_absorbs_empty_roots
#assert_axioms legacy_commitsS_agree

end Dregg2.Exec.SystemRoots
