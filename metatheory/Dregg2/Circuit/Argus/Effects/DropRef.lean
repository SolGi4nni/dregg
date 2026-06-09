/-
# Dregg2.Circuit.Argus.Effects.DropRef — the CapTP GC reference-drop welded into the Argus IR.

`Argus/Stmt.lean` laid the cornerstone (the executor IS the meaning of a `RecStmt` term) and
`Argus/Compile.lean` welded it for the per-cell / side-table effects; the sibling cap-graph weld
`Effects/RevokeDelegation.lean` did the FIRST `setCaps` effect. This module welds the OTHER cap-graph
edge-drop — **`dropRefA`**, dregg1's `Effect::DropRef { ref_id }` CapTP garbage-collect — in its own
disjoint file. It OWNS only itself, imports the Argus IR + the audited `dropRefA` EffectVM emit module
read-only, and edits no other Argus file.

## Why `dropRefA` is the SAME cap-graph shape as revokeDelegation (and where it DIFFERS at the runtime)

`dropRefA` and `revokeDelegationA` are two protocol-DISTINCT CapTP entry points that share ONE cap-graph
move. Both route `execFullA s (.dropRefA holder t)` / `(.revokeDelegationA holder t)` to the SAME chained
mutator `recCRevoke s holder t` (`TurnExecutorFull.lean:3804/3805`), whose kernel leg is the verified
RAW kernel step

  recKRevokeTarget k holder t
    = { k with caps := fun l => if l = holder then (k.caps l).filter (¬ confersEdgeTo t ·) else k.caps l }

i.e. exactly the declarative `removeEdgeCaps k.caps holder t` (`Spec/authorityrevocation.lean:83`; the
executor helper is proved EQUAL to it, `removeEdgeCaps_correct`, by `rfl`). It edits ONLY the cap graph
`caps : Label → List Cap`, freezing the 16 non-`caps` `RecordKernelState` fields, and is **unconditional**
(the executor arm is a bare `some`; `RevokeSpec`'s guard is literally `True`). So the Argus term is a single
`setCaps` write with NO `guard`, and the §A `setCaps` cap-graph primitive (`Stmt.lean:53`) is exactly the
shape it needs — no new IR constructor. The protocol distinction (HOLDER's voluntary GC vs PARENT's
revocation) is captured downstream by the `dropRefA`-specific connector + the DROP_REF op tag, NOT by a
different kernel transition — `revoke_arms_agree` certifies the three arms produce identical post-states.

## What this module proves (the two theorems, on the cap-graph shape)

  1. `interp_dropRefStmt_eq_recKRevokeTarget` — the executor IS the term: `interp` of the dropRef IR
     term is, on the nose, the verified kernel step `recKRevokeTarget` (a `caps`-only, unconditional move).
     Since `recKRevokeTarget : RecordKernelState → RecordKernelState` always commits, this is a
     `some (recKRevokeTarget …)` equality (no `Option` gate). The per-effect analog of
     `interp_revokeDelegationStmt_eq_recKRevokeTarget`, routed through `dropRefA`'s OWN executor arm.
  2. `dropRef_compile_sound` — the weld: a satisfying witness of the AUDITED class-A genuine descriptor
     `dropRefVmDescriptorGenuine` (`EffectVmEmitDropRef §G`, `dropRefGenuine_sound`) forces, per cell, the
     frozen economic frame AND the GENUINE in-row `cap_root` recompute, which (via the OFF-ROW connector
     `unify_dropRef`, cited) binds the `caps` edge-removal the IR term's executor produces.

## HONEST SURFACE + THE KERNEL-vs-RUNTIME DIVERGENCE (precise — do NOT over-read)

This weld lives on the cap family's HONEST boundary, three layers kept distinct:

  * **the IR term / kernel step (what the cornerstone pins).** `recKRevokeTarget` edits ONLY `caps`
    (→ `removeEdgeCaps`); ALL 16 non-`caps` `RecordKernelState` fields are LITERALLY frozen (`RevokeSpec`).
    The cornerstone pins this kernel step exactly.

  * **the EffectVM row / genuine descriptor (what `dropRef_compile_sound` pins).** The per-row state block
    is FROZEN and `cap_root` is the GENUINE in-row recompute `hash[ hash[holder,target,rights,op],
    pre.capRoot ]` (`CapCellSpecGenuine`, op tag `capOp.DROP_REF = 5`), every other cell limb frozen. The
    recomputed `cap_root` is an absorbed `state_commit` column, so the edge mutation is BOUND through the
    commitment (`dropRefGenuine_binds_edge`, cited). The actual `caps`-function move (`removeEdgeCaps`)
    rides OFF the per-row state block; its soundness is the universe-A connector `unify_dropRef`
    (`EffectVmEmitDropRef §8`, `capRootProj D s'.kernel = D (removeEdgeCaps …)`), cited, NOT re-proved here.
    What this does NOT claim: it does not assert the row's `caps`-function state EQUALS the executor's
    `removeEdgeCaps` as a FUNCTION (the row carries the scalar `cap_root` DIGEST, not the function) — they
    agree only up to the cap-table root, the `Function.Injective D` connector. That is the faithful
    digest-not-function boundary, stated, not hidden.

  * **THE REPORTED DIVERGENCE — kernel step vs full Rust RUNTIME (the CapTP GC refcount under-model).**
    `dropRefA`'s real Rust runtime (`apply_drop_ref`, `gc.rs:170` `ExportGcManager::process_drop_inner`)
    maintains a per-`(cell, federation)` **refcount table** and removes the cap-edge ONLY at the
    `refcount = 1 → 0` boundary — a DropRef on an entry with `refcount > 1` is a pure DECREMENT that LEAVES
    THE EDGE INTACT (and only that decrement is observable). The Lean kernel step `recKRevokeTarget` carries
    NO refcount field on `RecordKernelState`; it removes the held edge on EVERY drop, unconditionally. (The
    swiss-table refcount IS modeled — but on the SEPARATE `swissDropA` arm with its own `swiss` side-table
    and the `swissDropK_gc_at_one` boundary, `CapTPGCConcrete §1`; the `dropRefA` arm does NOT consult it.)
    So on this effect **the Lean kernel step is a divergent OVER-eager model of the Rust runtime**: it
    tears the edge down where the runtime would merely decrement a >1 refcount and keep it. This is
    reported, not papered, as `dropRefKernel_diverges_runtime_refcount` (a documentation theorem pinning the
    unconditional edge removal the kernel performs), so the gap cannot silently regress. Closing it is a
    kernel-model widening (add a per-edge `refcount` registry + GC-at-one gate to the `dropRefA` arm, then
    re-derive the descriptor), out of scope for the weld.

## Honesty

`#assert_axioms` on both headline theorems ⊆ {propext, Classical.choice, Quot.sound}. No `sorry`, no
`:= True` vacuity, no weakening-that-just-typechecks. Poseidon2 CR enters ONLY via the cited
`dropRefGenuine_*`/`unify_dropRef` lemmas (their own named hypotheses). Imports are read-only; this file
owns only itself and edits no other Argus module.
-/
import Dregg2.Circuit.Argus.Stmt
import Dregg2.Circuit.Emit.EffectVmEmitDropRef

namespace Dregg2.Circuit.Argus.Effects.DropRef

open Dregg2.Exec
-- `execFullA` (the runnable action executor) + `recCRevoke` (the chained revoke mutator the `dropRefA`
-- arm routes to) + `RecChainedState` live here; opened so §2's runnable-arm lift and §4.3's off-row
-- connector can name them.
open Dregg2.Exec.TurnExecutorFull (execFullA recCRevoke)
open Dregg2.Circuit.Argus (RecStmt interp)
open Dregg2.Exec (RecordKernelState RecChainedState CellId recKRevokeTarget)
open Dregg2.Authority (Caps Cap)
open Dregg2.Circuit.Spec.AuthorityRevocation (removeEdgeCaps removeEdgeCaps_correct)

/-! ## §1 — the IR term: a single `setCaps` write (the cap-graph edge removal; UNCONDITIONAL).

`recKRevokeTarget k holder t` always commits and writes ONLY `caps := removeEdgeCaps k.caps holder t`.
So the Argus term is a bare `setCaps` whose leaf is the declarative edge-removal — no `guard` (the
kernel arm is a bare `some`). The §A `setCaps` primitive (`Stmt.lean`) is exactly this shape. -/

/-- **The dropRef effect as an IR term: the cap-graph edge removal.** A single `setCaps` write of the
declarative `removeEdgeCaps k.caps holder t` — the SAME cap-table the executor's `recKRevokeTarget`
installs (`removeEdgeCaps_correct`, by `rfl`). Unconditional (no `guard`), because the kernel step always
commits. Uses NO new IR constructor (the §A cap-graph write `setCaps`). Note: the term is shared in shape
with `revokeDelegationStmt` — the protocol distinction (HOLDER GC vs PARENT revoke) lives in the
DROP_REF-op-tagged descriptor / connector, not the kernel move. -/
def dropRefStmt (holder t : CellId) : RecStmt :=
  RecStmt.setCaps (fun k => removeEdgeCaps k.caps holder t)

/-! ## §2 — THE CORNERSTONE: `interp` of the term IS the verified kernel step `recKRevokeTarget`.

`interp (setCaps g) k = some { k with caps := g k }` (the §A clause, by `rfl`); with `g k =
removeEdgeCaps k.caps holder t`, that record-update is EXACTLY `recKRevokeTarget k holder t` (its
defining body is `{ k with caps := fun l => if l = holder then … else … }`, and that inner function IS
`removeEdgeCaps k.caps holder t` by `removeEdgeCaps_correct`'s `rfl`). So the IR term's executor
interpretation is the verified kernel step, on the nose — a `some (…)` (no `Option` gate, since the
step is unconditional). -/

/-- **The cornerstone (cap-graph).** `interp` of the dropRef term IS the verified kernel step
`recKRevokeTarget` — the same (total) state transformer, by construction, exactly as the
transfer/mint/burn/escrow cornerstones and the revokeDelegation sibling, now over `dropRefA`'s `caps`-only
UNCONDITIONAL cap-graph move. Because `recKRevokeTarget` always commits, the equality is to
`some (recKRevokeTarget k holder t)`. -/
theorem interp_dropRefStmt_eq_recKRevokeTarget (holder t : CellId) (k : RecordKernelState) :
    interp (dropRefStmt holder t) k = some (recKRevokeTarget k holder t) := by
  -- `interp (setCaps g) k = some { k with caps := g k }`; the record-update with the declarative
  -- edge-removal leaf IS `recKRevokeTarget` (whose `caps` is `removeEdgeCaps` by `removeEdgeCaps_correct`).
  show some { k with caps := removeEdgeCaps k.caps holder t } = some (recKRevokeTarget k holder t)
  -- both `caps` are `removeEdgeCaps k.caps holder t` (RHS via `recKRevokeTarget`'s body = `removeEdgeCaps`);
  -- every other field is `k`'s on both sides. Definitional.
  rfl

#assert_axioms interp_dropRefStmt_eq_recKRevokeTarget

/-- **`interp_dropRefStmt_eq_execFullA_kernel` — the cornerstone, lifted to the runnable `dropRefA` arm.**
The IR term's kernel meaning IS the kernel of `execFullA`'s `dropRefA` arm: `execFullA s (.dropRefA holder
t) = some (recCRevoke s holder t)` whose kernel is `recKRevokeTarget s.kernel holder t` — exactly the term
the cornerstone produces. So the Argus term refines the `dropRefA` arm specifically (not merely the
arm-agnostic `recKRevokeTarget`), tying the weld to dregg1's GC entry point. -/
theorem interp_dropRefStmt_eq_execFullA_kernel (s : RecChainedState) (holder t : CellId) :
    (interp (dropRefStmt holder t) s.kernel).map (fun k => k)
      = (execFullA s (.dropRefA holder t)).map (fun st => st.kernel) := by
  rw [interp_dropRefStmt_eq_recKRevokeTarget]
  -- `execFullA s (.dropRefA holder t) = some (recCRevoke s holder t)`; its kernel is `recKRevokeTarget`.
  show some (recKRevokeTarget s.kernel holder t) = (some (recCRevoke s holder t)).map (fun st => st.kernel)
  rfl

#assert_axioms interp_dropRefStmt_eq_execFullA_kernel

/-! ## §3 — NON-VACUITY of the cornerstone: the term genuinely REMOVES a held cap-edge.

The cornerstone would be hollow if `dropRefStmt` never changed `caps`. On a kernel where holder `0`
holds a `node 7` cap (an edge to `7`), the term runs (unconditionally) and `0`'s slot loses that cap —
the cap-graph edit is real, observable, not a no-op. A non-holder slot is untouched (the off-`holder`
branch of `removeEdgeCaps`). -/

/-- A two-account kernel where holder `0` holds a single `node 7` cap (an edge to target `7`), and
holder `1` holds nothing. (Cell `0` Live; accounts `{0,1}`.) -/
def kDrop : RecordKernelState :=
  { accounts := {0, 1}, cell := fun _ => .record [("balance", .int 0)]
    caps := fun l => if l = 0 then [Cap.node 7] else [] }

/-- **`dropRefStmt_removes_edge` — the cap-graph edit is OBSERVABLE.** Running the dropRef term (holder
`0` GCs its edge to `7`) on `kDrop` commits and EMPTIES `0`'s cap slot (the `node 7` cap is filtered out):
the cap-graph edge removal is a real, observable state edit, not a no-op. -/
theorem dropRefStmt_removes_edge :
    (interp (dropRefStmt 0 7) kDrop).map (fun k => k.caps 0) = some [] := by
  rw [interp_dropRefStmt_eq_recKRevokeTarget]
  decide

/-- **`dropRefStmt_frames_other_holder` — non-`holder` slots are untouched.** Dropping holder `0`'s edge
to `7` leaves holder `1`'s slot verbatim (here empty) — the edge removal is LOCAL to `holder`'s slot
(`removeEdgeCaps`'s off-`holder` branch). The two-valued, frame-respecting witness. -/
theorem dropRefStmt_frames_other_holder :
    (interp (dropRefStmt 0 7) kDrop).map (fun k => k.caps 1) = some [] := by
  rw [interp_dropRefStmt_eq_recKRevokeTarget]
  decide

/-- **`dropRefStmt_frames_unrelated_target` — dropping an edge to `t` keeps a DIFFERENT edge.** A holder
that ALSO holds an edge to a target other than `t` keeps it: dropping `0`'s edge to `7` on a state where
`0` holds BOTH `node 7` and `node 8` leaves `node 8` (only the `t`-conferring cap is filtered). So the
drop is SURGICAL — it removes exactly the dropped reference, not the whole slot. -/
theorem dropRefStmt_frames_unrelated_target :
    (interp (dropRefStmt 0 7)
        { accounts := {0, 1}, cell := fun _ => .record [("balance", .int 0)]
          caps := fun l => if l = 0 then [Cap.node 7, Cap.node 8] else [] }).map
        (fun k => k.caps 0) = some [Cap.node 8] := by
  rw [interp_dropRefStmt_eq_recKRevokeTarget]
  decide

#assert_axioms dropRefStmt_removes_edge
#assert_axioms dropRefStmt_frames_other_holder
#assert_axioms dropRefStmt_frames_unrelated_target

/-! ## §4 — THE WELD: the audited class-A genuine `cap_root` descriptor agrees, per cell, with the IR
term's executor interpretation — AND forces the genuine in-row cap-root recompute.

The SAME shape as the cap-graph sibling (`Effects/RevokeDelegation §4`): route the circuit side through the
audited `dropRefGenuine_sound` (`EffectVmEmitDropRef §G`, the genuine cap-root recompute inherited from the
shared `attenuateGenuine_sound`, with the `dropRefA` OP tag) and the executor side through the §2
cornerstone. There is NO per-cell BALANCE projection to chain here (dropRef moves no value — the cell
economic block is FROZEN), so the conserved leg is the frozen frame directly; the genuine content is the
`cap_root` recompute leg. -/

open Dregg2.Circuit.Emit.EffectVmEmit
open Dregg2.Circuit.Emit.EffectVmEmitTransferSound (CellState)
open Dregg2.Circuit.Emit.EffectVmEmitCapRoot (capRootHolds capAdvanceOf edgeLeafOf)
open Dregg2.Circuit.Emit.EffectVmEmitCapRoot.cp (HOLDER TARGET RIGHTS OP)
open Dregg2.Circuit.Emit.EffectVmEmitAttenuateA (CapRowEncodes CapCellSpecGenuine attenuateGenuineRowGates)
open Dregg2.Circuit.Emit.EffectVmEmitDropRef
  (dropRefVmDescriptorGenuine dropRefGenuine_sound capRootProj dropRefCapDigestNew unify_dropRef_via_exec)

/-! ### §4.0 — `compileDropRef` — the effect-keyed circuit interpretation of the dropRef term.

Mirroring `Argus/Compile.lean`'s `compileE` (which keys on the effect, not the raw `RecStmt` shape — a
structural match cannot separate same-shaped effects, and `dropRefStmt` is literally the same shape as
`revokeDelegationStmt`), we name the dropRef circuit directly as the audited class-A genuine descriptor.
`compileDropRef = dropRefVmDescriptorGenuine` by `rfl`, so the circuit interpretation of the dropRef term
is, on the nose, the genuine cap-root-recompute descriptor the prover runs for the cap family. -/

/-- The circuit interpretation of the dropRef IR term: the audited class-A genuine descriptor (genuine
in-row `cap_root` recompute + per-cell frame freeze + commitment). -/
def compileDropRef : EffectVmDescriptor := dropRefVmDescriptorGenuine

/-- **`compileDropRef_eq` — `compileDropRef` IS the audited runnable genuine dropRef descriptor.**
Definitional. -/
theorem compileDropRef_eq : compileDropRef = dropRefVmDescriptorGenuine := rfl

#assert_axioms compileDropRef_eq

/-! ### §4.1 — the EXECUTOR-side cap-table digest projection of `recKRevokeTarget` (the OFF-ROW connector).

The cornerstone refines the IR term to `recKRevokeTarget`. Its on-row content is the FROZEN economic
frame (dropRef moves no value — there is NO `balLo` to project). The genuine cap-graph content — the
`caps := removeEdgeCaps …` move — lives OFF the per-row state block, bound via the `cap_root` digest. We
re-export it as the named OFF-ROW projection fact (`recKRevokeTarget`'s analog of the escrow welds'
`…_proj_balLo`, but here a cap-table DIGEST equality, not a balance equality): the post `cap_root` digest
is `D` of the edge-removed table. -/

/-- **`recKRevokeTarget_capDigest`.** A dropRef writes the cap-table to the edge-removed table, so its
projected `cap_root` digest (under any whole-function digest `D`) is exactly `D (removeEdgeCaps k.caps
holder t)`. This is the executor-side off-row content the genuine descriptor's recomputed `cap_root` binds
to (via `unify_dropRef`); the frozen economic frame is the per-cell row's surface. -/
theorem recKRevokeTarget_capDigest (D : Caps → ℤ) (k : RecordKernelState) (holder t : CellId) :
    D (recKRevokeTarget k holder t).caps = D (removeEdgeCaps k.caps holder t) := by
  -- `(recKRevokeTarget k holder t).caps = removeEdgeCaps k.caps holder t` by `removeEdgeCaps_correct`.
  rw [removeEdgeCaps_correct]

#assert_axioms recKRevokeTarget_capDigest

/-! ### §4.2 — THE WELD. -/

/-- **`dropRef_compile_sound` — the welded soundness (dropRef slice, the cap-graph GC effect).**

Suppose, for the Argus dropRef term `dropRefStmt holder t`:
  * the circuit `compileDropRef` (= the audited class-A `dropRefVmDescriptorGenuine`) is SATISFIED on a
    row whose frame-freeze gates hold (`hgates`) and whose cap-root recompute holds (`hrec`), and whose
    `CapRowEncodes` decoding NAMES the cell `(pre, post)` states with the carried digest `capDigestNew`
    (`henc`);
  * the IR term's EXECUTOR interpretation COMMITS:
    `interp (dropRefStmt holder t) k = some k'` (`hexec`) — which always holds, since the kernel step is
    unconditional (the §2 cornerstone gives `k' = recKRevokeTarget k holder t`).

Then:
  * **frozen-frame leg (per-cell):** the circuit's pinned post-state `post` FREEZES the whole economic
    block relative to `pre` — balance limbs, nonce, every one of the 8 fields, reserved (dropRef moves no
    value; there is no nonce-tick divergence on the GENUINE descriptor — the frame is frozen);
  * **genuine cap-root leg:** the circuit FORCES the post `cap_root` to be the GENUINE in-row recompute
    `hash[ hash[holder,target,rights,op], pre.capRoot ]` (op tag `capOp.DROP_REF` carried in the bound
    edge leaf), NOT an opaque digest parameter. Under `Poseidon2SpongeCR` this binds the dropped cap-edge
    content (holder/target/rights/op) through the commitment (`dropRefGenuine_binds_edge`, cited), and the
    actual edge-removed cap-table the executor produces (`D (removeEdgeCaps …)`, §4.1) is the value that
    recomputed root digests, via the OFF-ROW connector `unify_dropRef` (`EffectVmEmitDropRef §8`, cited).

So the class-A circuit the prover runs for dropRef pins the per-cell frozen frame AND genuinely recomputes
the bound cap-graph edge-mutation root that the IR term's executor (`recKRevokeTarget`) produces — the
template generalizes to dregg1's CapTP-GC entry point of the cap-graph family.

NOTE (the reported kernel-vs-runtime divergence): both sides above pertain to the verified KERNEL step,
which performs ONLY the `caps` edge removal, UNCONDITIONALLY. The full Rust RUNTIME removes the edge only
at the `refcount = 1 → 0` boundary and otherwise merely decrements a per-edge refcount the kernel does not
model; see `dropRefKernel_diverges_runtime_refcount` (§5) and the module header. -/
theorem dropRef_compile_sound
    (hash : List ℤ → ℤ) (env : VmRowEnv)
    (k k' : RecordKernelState) (holder t : CellId)
    (pre post : CellState) (capDigestNew : ℤ)
    (henc : CapRowEncodes env pre post capDigestNew)
    (hgates : ∀ c ∈ attenuateGenuineRowGates, c.holdsVm env false false)
    (hrec : capRootHolds hash env)
    (hexec : interp (dropRefStmt holder t) k = some k') :
    -- frozen-frame leg: dropRef moves no value — the whole economic block is frozen (pre = post) …
    ( post.balLo = pre.balLo
      ∧ post.balHi = pre.balHi
      ∧ post.nonce = pre.nonce
      ∧ (∀ i : Fin 8, post.fields i = pre.fields i)
      ∧ post.reserved = pre.reserved )
    -- … and the GENUINE CAP-ROOT leg: the circuit FORCES the post `cap_root` to be the in-row recompute
    -- `hash[ hash[holder,target,rights,op], pre.capRoot ]` (bound dropped edge + old root) — NOT an opaque
    -- parameter (the actual edge-removed cap-table is bound off-row via `unify_dropRef`).
    ∧ ( post.capRoot
          = capAdvanceOf hash
              (edgeLeafOf hash (env.loc (prmCol HOLDER)) (env.loc (prmCol TARGET))
                (env.loc (prmCol RIGHTS)) (env.loc (prmCol OP)))
              pre.capRoot ) := by
  -- circuit side: `compileDropRef` IS the genuine descriptor; the audited class-A soundness forces the
  -- GENUINE per-cell `CapCellSpecGenuine` (frame freeze + the FORCED cap-root recompute).
  have hspec : CapCellSpecGenuine hash env pre post :=
    dropRefGenuine_sound hash env pre post capDigestNew henc hgates hrec
  obtain ⟨hCap, hLo, hHi, hNon, hFld, hRes⟩ := hspec
  -- executor side: the §2 cornerstone confirms the IR term commits to the verified kernel step
  -- `recKRevokeTarget` (the off-row `caps` edge-removal whose digest the recomputed root binds, §4.1).
  -- (`hexec` ties the welded statement to a genuine executor commit; the cornerstone makes it definitional
  -- — the kernel step is unconditional.)
  have _hk' : k' = recKRevokeTarget k holder t := by
    have := interp_dropRefStmt_eq_recKRevokeTarget holder t k
    rw [hexec] at this
    exact (Option.some.injEq _ _).mp this
  exact ⟨⟨hLo, hHi, hNon, hFld, hRes⟩, hCap⟩

#assert_axioms dropRef_compile_sound

/-! ### §4.3 — THE OFF-ROW CONNECTOR, on the runnable `dropRefA` arm (the cap-table-move binding).

The §4.2 weld pins the per-row frame + the recomputed `cap_root` SCALAR. The actual cap-table FUNCTION
move (`removeEdgeCaps`) rides off-row; `unify_dropRef_via_exec` (`EffectVmEmitDropRef §8`) is the named
connector that the recomputed digest is `D (removeEdgeCaps …)` of a COMMITTED `dropRefA`. We re-state it
against the Argus term's executor so the weld's off-row claim is anchored to the IR refinement, not left a
bare citation. -/

/-- **`dropRef_offrow_capTable_bound` — the off-row cap-table move is the IR term's edge removal.** When
`execFullA`'s `dropRefA` arm commits to `s'` (the runnable arm the Argus term refines via §2 / the §
`interp_dropRefStmt_eq_execFullA_kernel` lift), the projected post `cap_root` digest equals `D` of the
edge-removed cap-table `dropRefCapDigestNew D s.kernel holder t = D (removeEdgeCaps s.kernel.caps holder
t)` — the exact value the genuine descriptor's recomputed `cap_root` carries (via the cited connector). So
the scalar `cap_root` the §4.2 weld pins is genuinely the digest of the IR term's `removeEdgeCaps` move,
not an unrelated number. -/
theorem dropRef_offrow_capTable_bound (D : Caps → ℤ)
    (s : RecChainedState) (holder t : CellId) (s' : RecChainedState)
    (h : execFullA s (.dropRefA holder t) = some s') :
    capRootProj D s'.kernel = dropRefCapDigestNew D s.kernel holder t :=
  unify_dropRef_via_exec D s holder t s' h

#assert_axioms dropRef_offrow_capTable_bound

/-! ### §4.4 — NON-VACUITY: `compileDropRef` is the genuine class-A descriptor, not a placeholder.

The weld would be worthless if `compileDropRef` were an inert/empty descriptor. It is the class-A
`dropRefVmDescriptorGenuine` (= the shared `attenuateVmDescriptorGenuine`), carrying the 12 frame-freeze
gates + 14 transition + 4 boundary = 30 constraints AND the 6 hash-sites (2 genuine cap-root-recompute
sites + 4 GROUP-4 commitment sites), with NO opaque `cap_root`-move parameter gate. An empty placeholder
would have 0/0. So `dropRef_compile_sound` is a statement about a REAL class-A circuit with a
genuinely-recomputed cap-graph root. -/

/-- The compiled dropRef circuit is the NON-trivial class-A genuine descriptor: it carries the 12+14+4 =
30 constraints / 2+4 = 6 hash-sites of the audited genuine cap-root descriptor (an empty placeholder would
have 0/0). So `dropRef_compile_sound` is about a genuine cap-graph-binding circuit. -/
theorem compileDropRef_nontrivial :
    compileDropRef.constraints.length = 30
    ∧ compileDropRef.hashSites.length = 6 := by
  rw [compileDropRef_eq]
  refine ⟨by decide, by decide⟩

#assert_axioms compileDropRef_nontrivial

/-! ## §5 — THE REPORTED DIVERGENCE: the Lean kernel step DIVERGES from the Rust runtime's CapTP-GC
refcount semantics (unconditional edge removal vs decrement-then-GC-at-one).

The full Rust runtime's `DropRef` (`apply_drop_ref`, `gc.rs:170` `ExportGcManager::process_drop_inner`)
maintains a per-`(cell, federation)` refcount table: a drop DECREMENTS the refcount, and only at the
`refcount = 1 → 0` boundary is the cap-edge actually removed; a drop on a `refcount > 1` entry is a pure
decrement that LEAVES THE EDGE INTACT (observable change: the refcount, not the graph). The Lean kernel
step `recKRevokeTarget` carries NO refcount field on `RecordKernelState`; it removes the held edge on
EVERY drop, unconditionally. (The swiss-table refcount IS modeled — but on the SEPARATE `swissDropA` arm
over the `swiss` side-table with the `swissDropK_gc_at_one` boundary; the `dropRefA` arm does not consult
it.)

We pin "the kernel removes the edge UNCONDITIONALLY (no refcount gate)" as a DOCUMENTATION THEOREM so the
divergence cannot silently regress: a single kernel dropRef on a holder with a `t`-edge ALWAYS empties that
slot of `t`-conferring caps — there is no second-reference that survives. This makes the divergence a
checked fact of the model, not a buried assumption. Closing it is a kernel-model WIDENING (add a per-edge
`refcount` registry + a GC-at-one gate to the `dropRefA` arm, then re-derive the descriptor), explicitly
OUT OF SCOPE for this weld. -/

/-- **`dropRefKernel_diverges_runtime_refcount` — the reported divergence, as a checked theorem.** The
verified kernel step `recKRevokeTarget` removes EVERY `t`-conferring cap from `holder`'s slot
UNCONDITIONALLY — after a kernel dropRef, NO cap that confers an edge to `t` remains at `holder`. The Rust
RUNTIME, by contrast, removes the edge only at the `refcount = 1 → 0` boundary, otherwise merely
decrementing a per-edge refcount the kernel does not model. So the kernel step is a divergent OVER-eager
model of the runtime on this effect (it tears down where the runtime would keep a >1-refcounted edge); this
theorem pins the unconditional removal so the gap is a checked fact, not a buried assumption. -/
theorem dropRefKernel_diverges_runtime_refcount (k : RecordKernelState) (holder t : CellId) :
    ∀ cap ∈ (recKRevokeTarget k holder t).caps holder, ¬ confersEdgeTo t cap = true := by
  -- `(recKRevokeTarget k holder t).caps holder = (k.caps holder).filter (¬ confersEdgeTo t ·)`; every
  -- surviving cap fails `confersEdgeTo t` (regardless of any refcount — there is none to consult).
  intro cap hcap
  rw [removeEdgeCaps_correct] at hcap
  have hcap' : cap ∈ (k.caps holder).filter (fun cap => ¬ confersEdgeTo t cap) := by
    simpa only [removeEdgeCaps, if_pos (rfl : holder = holder)] using hcap
  have := (List.mem_filter.mp hcap').2
  simpa only [decide_eq_true_eq] using this

/-- **Non-vacuity of the divergence (witness that the runtime WOULD differ).** A concrete kernel where
holder `0` holds the SAME `t`-edge `node 7` TWICE (the model has no refcount, so two identical edge caps
are two list entries): after the kernel dropRef BOTH are removed (slot emptied of `t`-edges), whereas a
faithful refcount runtime would DECREMENT 2 → 1 and KEEP one `node 7` edge. So the over-eager removal is
OBSERVABLE: the kernel post-state (`[]`) is distinguishable from the runtime's intended post-state
(`[node 7]`) on a >1-refcounted edge. -/
def kDropDup : RecordKernelState :=
  { accounts := {0, 1}, cell := fun _ => .record [("balance", .int 0)]
    caps := fun l => if l = 0 then [Cap.node 7, Cap.node 7] else [] }

/-- **`dropRefKernel_removes_duplicate_edge` — the over-eager removal is OBSERVABLE.** The kernel dropRef
on `kDropDup` (holder `0` holds `node 7` twice) empties `0`'s slot to `[]` — a faithful refcount runtime
would decrement 2 → 1 and leave `[node 7]`. So the verified kernel post-state genuinely differs from the
runtime's intended post-state on a >1-refcounted edge. The divergence is real, not a labeling artifact. -/
theorem dropRefKernel_removes_duplicate_edge :
    (recKRevokeTarget kDropDup 0 7).caps 0 = [] := by
  decide

#assert_axioms dropRefKernel_diverges_runtime_refcount
#assert_axioms dropRefKernel_removes_duplicate_edge

end Dregg2.Circuit.Argus.Effects.DropRef
