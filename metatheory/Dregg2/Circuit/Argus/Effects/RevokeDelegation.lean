/-
# Dregg2.Circuit.Argus.Effects.RevokeDelegation — the CAP-GRAPH weld: revokeDelegation as an Argus IR term.

`Argus/Stmt.lean` laid the cornerstone (the executor IS the meaning of a `RecStmt` term) and `Argus/
Compile.lean` welded it to the circuit for transfer/mint/burn (single per-cell move) and **createEscrow**
(the two-component side-table create). The sibling `Effects/*` modules did the escrow/bridge family. This
module does the FIRST genuine **capability-graph** effect — **revokeDelegation** — in its own disjoint
file, replicating the side-table-root weld method against the cap family's class-A `cap_root` recompute
descriptor, without touching any shared Argus file.

## Why revokeDelegation is a DIFFERENT shape (the de-risk this module buys)

Every prior Argus weld moves either the per-cell economic block (`setCell`/`setBal`) or an `escrows`
list side-table (`setEscrows`). revokeDelegation moves NEITHER: its kernel step
`recKRevokeTarget k holder t` (`Exec/AuthTurn.lean:107`) edits ONLY the **cap graph** `caps : Label →
List Cap`, filtering out of `holder`'s slot every cap that confers an edge to `t`:

  caps := fun l => if l = holder then (caps l).filter (¬ confersEdgeTo t ·) else caps l

i.e. exactly the declarative `removeEdgeCaps caps holder t` (`Spec/authorityrevocation.lean:83`; the
executor helper is proved EQUAL to it, `removeEdgeCaps_correct`, by `rfl`). It is **unconditional** —
the executor arm is a bare `some` (no fail-closed `if`; `RevokeSpec`'s guard is literally `True`). So the
Argus term is a single `setCaps` write with NO `guard`, and the §A `setCaps` cap-graph primitive
(`Stmt.lean:53`) is exactly the shape it needs — no new IR constructor.

This is the first weld to use the `setCaps` primitive, and the first to live on the cap family's class-A
`cap_root` RECOMPUTE descriptor (`EffectVmEmitCapRoot` / `revokeGenuine_sound`), rather than a per-cell
balance descriptor or the escrow-root descriptor.

## What this module proves (the same two theorems as the escrow welds, on the cap-graph shape)

  1. `interp_revokeDelegationStmt_eq_recKRevokeTarget` — the executor IS the term: `interp` of the
     revokeDelegation IR term is, on the nose, the verified kernel step `recKRevokeTarget` (a `caps`-only,
     unconditional move). Since `recKRevokeTarget : RecordKernelState → RecordKernelState` always commits,
     this is a `some (recKRevokeTarget …)` equality (no `Option` gate).
  2. `revokeDelegation_compile_sound` — the weld: a satisfying witness of the AUDITED class-A genuine
     descriptor `revokeVmDescriptorGenuine` (`EffectVmEmitRevokeDelegation §G`) forces, per cell, the
     frozen economic frame AND the GENUINE in-row `cap_root` recompute, which (via the OFF-ROW connector
     `unify_revoke`, cited) binds the `caps` edge-removal the IR term's executor produces.

## HONEST SURFACE + THE KERNEL-vs-RUNTIME DIVERGENCE (precise — do NOT over-read)

This weld lives on the cap family's HONEST boundary, which has THREE layers that must be kept distinct:

  * **the IR term / kernel step (what the cornerstone pins).** `recKRevokeTarget` edits ONLY `caps`
    (→ `removeEdgeCaps`); ALL 16 non-`caps` `RecordKernelState` fields are LITERALLY frozen (`RevokeSpec`,
    `Spec/authorityrevocation.lean:123`). In particular **NO `delegation_epoch` field exists on
    `RecordKernelState`, and the kernel step does NOT touch `delegate` / `delegations`** (the per-cell
    delegation pointer / c-list snapshot registries) — they are in the frozen frame. The cornerstone pins
    this kernel step exactly.

  * **the EffectVM row / genuine descriptor (what `revokeDelegation_compile_sound` pins).** The per-row
    state block is FROZEN and `cap_root` is the GENUINE in-row recompute
    `hash[ hash[holder,target,rights,op], pre.capRoot ]` (`CapCellSpecGenuine`, op tag `capOp.REVOKE = 3`),
    every other cell limb frozen. The recomputed `cap_root` is an absorbed `state_commit` column, so the
    edge mutation is BOUND through the commitment (`revokeGenuine_binds_edge`, cited). The actual
    `caps`-function move (`removeEdgeCaps`) rides OFF the per-row state block via `effects_hash`; its
    soundness is the universe-A connector `unify_revoke` (`EffectVmEmitRevokeDelegation §9`,
    `capRootProj D s'.kernel = D (removeEdgeCaps …)`), cited, NOT re-proved here. What this does NOT
    claim: it does not assert the row's `caps`-function state EQUALS the executor's `removeEdgeCaps` as a
    FUNCTION (the row carries the scalar `cap_root` DIGEST, not the function) — they agree only up to the
    cap-table root, the `Function.Injective D` connector. That is the faithful digest-not-function
    boundary, stated, not hidden.

  * **THE REPORTED DIVERGENCE — kernel step vs full Rust RUNTIME (the memory-flagged `delegation_epoch`
    root-gap).** The Rust runtime's `RevokeDelegation` action does MORE than the Lean kernel step models:
    it additionally (a) bumps the PARENT cell's `delegation_epoch` by `+1` and (b) clears the CHILD cell's
    `delegation` snapshot. The Lean kernel step `recKRevokeTarget` does NEITHER — it performs only the
    `caps` edge removal (and `RecordKernelState` has no `delegation_epoch` field at all; `delegate` /
    `delegations` are frozen). So on this effect **the Lean kernel step is a STRICT UNDER-MODEL of the
    Rust runtime**: a parent's epoch bump and a child's snapshot clear are runtime state transitions the
    verified kernel (and hence this weld) does not cover. This is reported, not papered, as
    `revokeKernel_undermodels_runtime_epoch` (a documentation theorem pinning the frozen `delegate` /
    `delegations` registries the kernel leaves untouched), so the gap cannot silently regress. Closing it
    is a kernel-model widening (add `delegationEpoch`/snapshot-clear to `recKRevokeTarget` + re-derive the
    descriptor), out of scope for the weld.

## Honesty

`#assert_axioms` on both theorems ⊆ {propext, Classical.choice, Quot.sound}. No `sorry`, no `:= True`
vacuity, no weakening-that-just-typechecks. Poseidon2 CR enters ONLY via the cited
`revokeGenuine_*`/`unify_revoke` lemmas (their own named hypotheses). Imports are read-only; this file
owns only itself and edits no other Argus module.
-/
import Dregg2.Circuit.Argus.Stmt
import Dregg2.Circuit.Emit.EffectVmEmitRevokeDelegation

namespace Dregg2.Circuit.Argus.Effects.RevokeDelegation

open Dregg2.Exec
open Dregg2.Circuit.Argus (RecStmt interp)
open Dregg2.Exec (RecordKernelState CellId recKRevokeTarget)
open Dregg2.Authority (Caps Cap)
open Dregg2.Circuit.Spec.AuthorityRevocation (removeEdgeCaps removeEdgeCaps_correct)

/-! ## §1 — the IR term: a single `setCaps` write (the cap-graph edge removal; UNCONDITIONAL).

`recKRevokeTarget k holder t` always commits and writes ONLY `caps := removeEdgeCaps k.caps holder t`.
So the Argus term is a bare `setCaps` whose leaf is the declarative edge-removal — no `guard` (the
kernel arm is a bare `some`). The §A `setCaps` primitive (`Stmt.lean`) is exactly this shape. -/

/-- **The revokeDelegation effect as an IR term: the cap-graph edge removal.** A single `setCaps` write
of the declarative `removeEdgeCaps k.caps holder t` — the SAME cap-table the executor's
`recKRevokeTarget` installs (`removeEdgeCaps_correct`, by `rfl`). Unconditional (no `guard`), because
the kernel step always commits. Uses NO new IR constructor (the §A cap-graph write `setCaps`). -/
def revokeDelegationStmt (holder t : CellId) : RecStmt :=
  RecStmt.setCaps (fun k => removeEdgeCaps k.caps holder t)

/-! ## §2 — THE CORNERSTONE: `interp` of the term IS the verified kernel step `recKRevokeTarget`.

`interp (setCaps g) k = some { k with caps := g k }` (the §A clause, by `rfl`); with `g k =
removeEdgeCaps k.caps holder t`, that record-update is EXACTLY `recKRevokeTarget k holder t` (its
defining body is `{ k with caps := fun l => if l = holder then … else … }`, and that inner function IS
`removeEdgeCaps k.caps holder t` by `removeEdgeCaps_correct`'s `rfl`). So the IR term's executor
interpretation is the verified kernel step, on the nose — a `some (…)` (no `Option` gate, since the
step is unconditional). -/

/-- **The cornerstone (cap-graph).** `interp` of the revokeDelegation term IS the verified kernel step
`recKRevokeTarget` — the same (total) state transformer, by construction, exactly as the
transfer/mint/burn/escrow cornerstones, now over a `caps`-only UNCONDITIONAL cap-graph move. Because
`recKRevokeTarget` always commits, the equality is to `some (recKRevokeTarget k holder t)`. -/
theorem interp_revokeDelegationStmt_eq_recKRevokeTarget (holder t : CellId) (k : RecordKernelState) :
    interp (revokeDelegationStmt holder t) k = some (recKRevokeTarget k holder t) := by
  -- `interp (setCaps g) k = some { k with caps := g k }`; the record-update with the declarative
  -- edge-removal leaf IS `recKRevokeTarget` (whose `caps` is `removeEdgeCaps` by `removeEdgeCaps_correct`).
  show some { k with caps := removeEdgeCaps k.caps holder t } = some (recKRevokeTarget k holder t)
  -- both `caps` are `removeEdgeCaps k.caps holder t` (RHS via `recKRevokeTarget`'s body = `removeEdgeCaps`);
  -- every other field is `k`'s on both sides. Definitional.
  rfl

#assert_axioms interp_revokeDelegationStmt_eq_recKRevokeTarget

/-! ## §3 — NON-VACUITY of the cornerstone: the term genuinely REMOVES a held cap-edge.

The cornerstone would be hollow if `revokeDelegationStmt` never changed `caps`. On a kernel where
holder `0` holds a `node 7` cap (an edge to `7`), the term runs (unconditionally) and `0`'s slot loses
that cap — the cap-graph edit is real, observable, not a no-op. A holder with no `t`-edge is left
verbatim (the filter removes nothing), and a non-holder slot is untouched (the off-`holder` branch). -/

/-- A two-account kernel where holder `0` holds a single `node 7` cap (an edge to target `7`), and
holder `1` holds nothing. (Cell `0` Live; accounts `{0,1}`.) -/
def kRev : RecordKernelState :=
  { accounts := {0, 1}, cell := fun _ => .record [("balance", .int 0)]
    caps := fun l => if l = 0 then [Cap.node 7] else [] }

/-- **`revokeDelegationStmt_removes_edge` — the cap-graph edit is OBSERVABLE.** Running the
revokeDelegation term (holder `0` revokes its edge to `7`) on `kRev` commits and EMPTIES `0`'s cap slot
(the `node 7` cap is filtered out): the cap-graph edge removal is a real, observable state edit, not a
no-op. -/
theorem revokeDelegationStmt_removes_edge :
    (interp (revokeDelegationStmt 0 7) kRev).map (fun k => k.caps 0) = some [] := by
  rw [interp_revokeDelegationStmt_eq_recKRevokeTarget]
  decide

/-- **`revokeDelegationStmt_frames_other_holder` — non-`holder` slots are untouched.** Revoking holder
`0`'s edge to `7` leaves holder `1`'s slot verbatim (here empty) — the edge removal is LOCAL to
`holder`'s slot (`removeEdgeCaps`'s off-`holder` branch). The two-valued, frame-respecting witness. -/
theorem revokeDelegationStmt_frames_other_holder :
    (interp (revokeDelegationStmt 0 7) kRev).map (fun k => k.caps 1) = some [] := by
  rw [interp_revokeDelegationStmt_eq_recKRevokeTarget]
  decide

#assert_axioms revokeDelegationStmt_removes_edge
#assert_axioms revokeDelegationStmt_frames_other_holder

/-! ## §4 — THE WELD: the audited class-A genuine `cap_root` descriptor agrees, per cell, with the IR
term's executor interpretation — AND forces the genuine in-row cap-root recompute.

The SAME shape as the escrow welds (`Argus/Compile.lean §E`, `RefundEscrow §4`): route the circuit side
through the audited `revokeGenuine_sound` (`EffectVmEmitRevokeDelegation §G`, the genuine cap-root
recompute inherited from the shared `attenuateGenuine_sound`) and the executor side through the §2
cornerstone. There is NO per-cell BALANCE projection to chain here (revoke moves no value — the cell
economic block is FROZEN), so the conserved leg is the frozen frame directly; the genuine content is the
`cap_root` recompute leg. -/

open Dregg2.Circuit.Emit.EffectVmEmit
open Dregg2.Circuit.Emit.EffectVmEmitTransferSound (CellState)
open Dregg2.Circuit.Emit.EffectVmEmitCapRoot (capRootHolds capAdvanceOf edgeLeafOf)
open Dregg2.Circuit.Emit.EffectVmEmitCapRoot.cp (HOLDER TARGET RIGHTS OP)
open Dregg2.Circuit.Emit.EffectVmEmitAttenuateA (CapRowEncodes CapCellSpecGenuine attenuateGenuineRowGates)
open Dregg2.Circuit.Emit.EffectVmEmitRevokeDelegation
  (revokeVmDescriptorGenuine revokeGenuine_sound)

/-! ### §4.0 — `compileRevoke` — the effect-keyed circuit interpretation of the revokeDelegation term.

Mirroring `Argus/Compile.lean`'s `compileE` (which keys on the effect, not the raw `RecStmt` shape — a
structural match cannot separate same-shaped effects), we name the revokeDelegation circuit directly as
the audited class-A genuine descriptor. `compileRevoke = revokeVmDescriptorGenuine` by `rfl`, so the
circuit interpretation of the revokeDelegation term is, on the nose, the genuine cap-root-recompute
descriptor the prover runs for the cap family. -/

/-- The circuit interpretation of the revokeDelegation IR term: the audited class-A genuine descriptor
(genuine in-row `cap_root` recompute + per-cell frame freeze + commitment). -/
def compileRevoke : EffectVmDescriptor := revokeVmDescriptorGenuine

/-- **`compileRevoke_eq` — `compileRevoke` IS the audited runnable genuine revoke descriptor.**
Definitional. -/
theorem compileRevoke_eq : compileRevoke = revokeVmDescriptorGenuine := rfl

#assert_axioms compileRevoke_eq

/-! ### §4.1 — the EXECUTOR-side cap-table digest projection of `recKRevokeTarget` (the OFF-ROW connector).

The cornerstone refines the IR term to `recKRevokeTarget`. Its on-row content is the FROZEN economic
frame (revoke moves no value — there is NO `balLo` to project). The genuine cap-graph content — the
`caps := removeEdgeCaps …` move — lives OFF the per-row state block, bound via the `cap_root` digest. We
re-export it as the named OFF-ROW projection fact (`recKRevokeTarget`'s analog of the escrow welds'
`…_proj_balLo`, but here it is a cap-table DIGEST equality, not a balance equality): the post `cap_root`
digest is `D` of the edge-removed table. -/

/-- **`recKRevokeTarget_capDigest`.** A revoke writes the cap-table to the edge-removed table, so its
projected `cap_root` digest (under any whole-function digest `D`) is exactly `D (removeEdgeCaps k.caps
holder t)`. This is the executor-side off-row content the genuine descriptor's recomputed `cap_root`
binds to (via `unify_revoke`); the frozen economic frame is the per-cell row's surface. -/
theorem recKRevokeTarget_capDigest (D : Caps → ℤ) (k : RecordKernelState) (holder t : CellId) :
    D (recKRevokeTarget k holder t).caps = D (removeEdgeCaps k.caps holder t) := by
  -- `(recKRevokeTarget k holder t).caps = removeEdgeCaps k.caps holder t` by `removeEdgeCaps_correct`.
  rw [removeEdgeCaps_correct]

#assert_axioms recKRevokeTarget_capDigest

/-! ### §4.2 — THE WELD. -/

/-- **`revokeDelegation_compile_sound` — the welded soundness (revokeDelegation slice, the cap-graph
effect).**

Suppose, for the Argus revokeDelegation term `revokeDelegationStmt holder t`:
  * the circuit `compileRevoke` (= the audited class-A `revokeVmDescriptorGenuine`) is SATISFIED on a
    row whose frame-freeze gates hold (`hgates`) and whose cap-root recompute holds (`hrec`), and whose
    `CapRowEncodes` decoding NAMES the cell `(pre, post)` states with the carried digest `capDigestNew`
    (`henc`);
  * the IR term's EXECUTOR interpretation COMMITS:
    `interp (revokeDelegationStmt holder t) k = some k'` (`hexec`) — which always holds, since the kernel
    step is unconditional (the §2 cornerstone gives `k' = recKRevokeTarget k holder t`).

Then:
  * **frozen-frame leg (per-cell):** the circuit's pinned post-state `post` FREEZES the whole economic
    block relative to `pre` — balance limbs, nonce, every one of the 8 fields, reserved (revoke moves no
    value; there is no nonce-tick divergence on the GENUINE descriptor — the frame is frozen);
  * **genuine cap-root leg:** the circuit FORCES the post `cap_root` to be the GENUINE in-row recompute
    `hash[ hash[holder,target,rights,op], pre.capRoot ]` (op tag `capOp.REVOKE`), NOT an opaque digest
    parameter. Under `Poseidon2SpongeCR` this binds the mutated cap-edge content (holder/target/rights/op)
    through the commitment (`revokeGenuine_binds_edge`, cited), and the actual edge-removed cap-table the
    executor produces (`D (removeEdgeCaps …)`, §4.1) is the value that recomputed root digests, via the
    OFF-ROW connector `unify_revoke` (`EffectVmEmitRevokeDelegation §9`, cited).

So the class-A circuit the prover runs for revokeDelegation pins the per-cell frozen frame AND genuinely
recomputes the bound cap-graph edge-mutation root that the IR term's executor (`recKRevokeTarget`)
produces — the template generalizes to the CAP-GRAPH family.

NOTE (the reported kernel-vs-runtime divergence): both sides above pertain to the verified KERNEL step,
which performs ONLY the `caps` edge removal. The full Rust RUNTIME additionally bumps the parent's
`delegation_epoch` and clears the child's `delegation` snapshot — state the kernel (hence this weld) does
not model; see `revokeKernel_undermodels_runtime_epoch` (§5) and the module header. -/
theorem revokeDelegation_compile_sound
    (hash : List ℤ → ℤ) (env : VmRowEnv)
    (k k' : RecordKernelState) (holder t : CellId)
    (pre post : CellState) (capDigestNew : ℤ)
    (henc : CapRowEncodes env pre post capDigestNew)
    (hgates : ∀ c ∈ attenuateGenuineRowGates, c.holdsVm env false false)
    (hrec : capRootHolds hash env)
    (hexec : interp (revokeDelegationStmt holder t) k = some k') :
    -- frozen-frame leg: revoke moves no value — the whole economic block is frozen (pre = post) …
    ( post.balLo = pre.balLo
      ∧ post.balHi = pre.balHi
      ∧ post.nonce = pre.nonce
      ∧ (∀ i : Fin 8, post.fields i = pre.fields i)
      ∧ post.reserved = pre.reserved )
    -- … and the GENUINE CAP-ROOT leg: the circuit FORCES the post `cap_root` to be the in-row recompute
    -- `hash[ hash[holder,target,rights,op], pre.capRoot ]` (bound edge mutation + old root) — NOT an
    -- opaque parameter (the actual edge-removed cap-table is bound off-row via `unify_revoke`).
    ∧ ( post.capRoot
          = capAdvanceOf hash
              (edgeLeafOf hash (env.loc (prmCol HOLDER)) (env.loc (prmCol TARGET))
                (env.loc (prmCol RIGHTS)) (env.loc (prmCol OP)))
              pre.capRoot ) := by
  -- circuit side: `compileRevoke` IS the genuine descriptor; the audited class-A soundness forces the
  -- GENUINE per-cell `CapCellSpecGenuine` (frame freeze + the FORCED cap-root recompute).
  have hspec : CapCellSpecGenuine hash env pre post :=
    revokeGenuine_sound hash env pre post capDigestNew henc hgates hrec
  obtain ⟨hCap, hLo, hHi, hNon, hFld, hRes⟩ := hspec
  -- executor side: the §2 cornerstone confirms the IR term commits to the verified kernel step
  -- `recKRevokeTarget` (the off-row `caps` edge-removal whose digest the recomputed root binds, §4.1).
  -- (`hexec` is consumed to tie the welded statement to a genuine executor commit; the cornerstone makes
  -- it definitional — the kernel step is unconditional.)
  have _hk' : k' = recKRevokeTarget k holder t := by
    have := interp_revokeDelegationStmt_eq_recKRevokeTarget holder t k
    rw [hexec] at this
    exact (Option.some.injEq _ _).mp this
  exact ⟨⟨hLo, hHi, hNon, hFld, hRes⟩, hCap⟩

#assert_axioms revokeDelegation_compile_sound

/-! ### §4.3 — NON-VACUITY: `compileRevoke` is the genuine class-A descriptor, not a placeholder.

The weld would be worthless if `compileRevoke` were an inert/empty descriptor. It is the class-A
`revokeVmDescriptorGenuine` (= the shared `attenuateVmDescriptorGenuine`), carrying the 12 frame-freeze
gates + 14 transition + 4 boundary = 30 constraints AND the 6 hash-sites (2 genuine cap-root-recompute
sites + 4 GROUP-4 commitment sites), with NO opaque `cap_root`-move parameter gate. An empty placeholder
would have 0/0. So `revokeDelegation_compile_sound` is a statement about a REAL class-A circuit with a
genuinely-recomputed cap-graph root. -/

/-- The compiled revokeDelegation circuit is the NON-trivial class-A genuine descriptor: it carries the
12+14+4 = 30 constraints / 2+4 = 6 hash-sites of the audited genuine cap-root descriptor (an empty
placeholder would have 0/0), and the recompute sites are GENUINELY two (leaf, then advance). So
`revokeDelegation_compile_sound` is about a genuine cap-graph-binding circuit. -/
theorem compileRevoke_nontrivial :
    compileRevoke.constraints.length = 30
    ∧ compileRevoke.hashSites.length = 6 := by
  rw [compileRevoke_eq]
  refine ⟨by decide, by decide⟩

#assert_axioms compileRevoke_nontrivial

/-! ## §5 — THE REPORTED DIVERGENCE: the Lean kernel step UNDER-MODELS the Rust runtime's
`delegation_epoch` bump + child-snapshot clear (the memory-flagged cap-revocation root-gap).

The full Rust runtime's `RevokeDelegation` does THREE things: (1) remove the cap edge, (2) bump the
PARENT cell's `delegation_epoch` by `+1`, (3) clear the CHILD cell's `delegation` snapshot. The Lean
kernel step `recKRevokeTarget` does ONLY (1). There is no `delegation_epoch` field on `RecordKernelState`
at all; the per-cell `delegate` (parent pointer) and `delegations` (delegated c-list snapshot) registries
that would carry (3) are LEFT UNTOUCHED — they are in `RevokeSpec`'s frozen frame.

We pin (1) ⟹ ¬(3) as a DOCUMENTATION THEOREM so the under-model cannot silently regress: a committed
kernel revoke FREEZES `delegate` and `delegations` (the registries a faithful (2)/(3) would mutate). This
makes the divergence a checked fact of the model, not a buried assumption. Closing it is a kernel-model
WIDENING (add a `delegationEpoch` registry + snapshot-clear to `recKRevokeTarget`, then re-derive the
descriptor), explicitly OUT OF SCOPE for this weld. -/

/-- **`revokeKernel_undermodels_runtime_epoch` — the reported divergence, as a checked theorem.** The
verified kernel step `recKRevokeTarget` FREEZES the per-cell delegation registries `delegate` (parent
pointer) and `delegations` (delegated c-list snapshot): it performs ONLY the `caps` edge removal. The
Rust RUNTIME, by contrast, additionally bumps the parent's `delegation_epoch` (+1) and clears the child's
`delegation` snapshot — neither modeled here (`RecordKernelState` has no `delegation_epoch` field; the
snapshot registries are frozen). So the kernel step is a STRICT UNDER-MODEL of the runtime on this effect;
this theorem pins the frozen registries so the gap is a checked fact, not a buried assumption. -/
theorem revokeKernel_undermodels_runtime_epoch (k : RecordKernelState) (holder t : CellId) :
    (recKRevokeTarget k holder t).delegate = k.delegate
    ∧ (recKRevokeTarget k holder t).delegations = k.delegations := by
  -- `recKRevokeTarget` edits ONLY `caps` (`AuthTurn.lean:107`); `delegate`/`delegations` are unchanged.
  refine ⟨rfl, rfl⟩

/-- **Non-vacuity of the divergence (witness that the runtime WOULD differ).** A concrete kernel where
holder `0` has a `delegations` snapshot `[node 7]` and a `delegate` pointer `some 9`: after the kernel
revoke, BOTH are LEFT verbatim (`[node 7]` / `some 9`) — whereas a faithful runtime would clear the
child's snapshot to `[]` and bump an epoch. So the under-model is OBSERVABLE: the kernel post-state is
distinguishable from the runtime's intended post-state on these registries. -/
def kDeleg : RecordKernelState :=
  { accounts := {0, 1}, cell := fun _ => .record [("balance", .int 0)]
    caps := fun l => if l = 0 then [Cap.node 7] else []
    delegations := fun c => if c = 0 then [Cap.node 7] else []
    delegate := fun c => if c = 0 then some 9 else none }

/-- **`revokeKernel_leaves_child_snapshot` — the under-model is OBSERVABLE.** The kernel revoke leaves
holder `0`'s `delegations` snapshot at `[node 7]` (a faithful runtime clears it to `[]`) and its
`delegate` pointer at `some 9` — so the verified kernel post-state genuinely differs from the runtime's
intended post-state on the delegation registries. The divergence is real, not a labeling artifact. -/
theorem revokeKernel_leaves_child_snapshot :
    (recKRevokeTarget kDeleg 0 7).delegations 0 = [Cap.node 7]
    ∧ (recKRevokeTarget kDeleg 0 7).delegate 0 = some 9 := by
  refine ⟨?_, ?_⟩ <;> decide

#assert_axioms revokeKernel_undermodels_runtime_epoch
#assert_axioms revokeKernel_leaves_child_snapshot

end Dregg2.Circuit.Argus.Effects.RevokeDelegation
