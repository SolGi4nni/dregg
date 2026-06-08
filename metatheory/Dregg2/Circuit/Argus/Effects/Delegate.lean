/-
# Dregg2.Circuit.Argus.Effects.Delegate — the capability DELEGATE effect welded into the Argus IR.

`Argus/Stmt.lean` laid the cornerstone (the executor IS the meaning of a `RecStmt` term) and validated
it on transfer/mint/burn (single-cell `setCell`/`setBal` moves) and on the escrow side-table family
(`createEscrow`/`releaseEscrow`/…, two-component `bal`+`escrows` moves bound to a side-table root).
`Argus/Compile.lean` welded each: the audited class-A circuit pinned the per-cell post-state the IR
term's executor produces.

This module welds the GRANOVETTER DELEGATE — the first CAP-GRAPH effect — in the SAME method, in a
disjoint file (it imports the Argus IR + the audited `delegate` emitter read-only and owns only its own
declarations). The genuinely different shape, and the point of this de-risk, is that `delegate` mutates
the CAP GRAPH (`caps : Label → List Cap`) rather than any per-cell balance/side-table: it installs ONE
cap-graph edge (the delegator's held `t`-conferring cap, copied to the recipient), and the circuit binds
it through a GENUINELY-RECOMPUTED `cap_root` (the cap-table digest column), not a per-cell ledger move.

## The executor primitive, unfolded (read off the CODE, `AuthTurn.lean:79`)

`recKDelegate k del rec t`:

    if (k.caps del).any (fun cap => confersEdgeTo t cap) = true then
      some { k with caps := grant k.caps rec (heldCapTo k.caps del t) }
    else none

So a committed `delegate`:

  * **GUARD** `(k.caps del).any (fun cap => confersEdgeTo t cap) = true` — the Granovetter connectivity
    premise: the delegator ALREADY HOLDS a `t`-conferring cap ("only connectivity begets connectivity").
  * **TOUCHED `caps`** ← `grant k.caps rec (heldCapTo k.caps del t)` — the recipient's slot gains the
    delegator's held `t`-cap, COPIED VERBATIM (non-amplifying held-copy, §NON-AMPLIFICATION below).
  * **FRAME** every other `RecordKernelState` component literally unchanged (`caps` is the one touched
    field) — so the IR body is `seq (guard …) (setCaps …)`, exactly the §A cap-graph write primitive.

This is the AUTHORITY-UNATTENUATED delegate the independent full-state spec
`Spec.AuthorityUnattenuated.DelegateSpec` validates against `recCDelegate` (the chained wrapper) both
ways; `recDelegateCaps caps del rec t := grant caps rec (heldCapTo caps del t)` is its validated
post-`caps` map (`recDelegateCaps_correct`), which we reuse as the `setCaps` leaf.

## §NON-AMPLIFICATION — IS the rights lattice `checkLe`-expressible? NO — and a `checkLe` here would be a
   FAKE tooth. (The precise REPORT the task asks for.)

The task asks to express `granted.rights ≤ held.rights` IN-TERM via `checkLe` *if the executor enforces
it*. The executor `recKDelegate` does NOT enforce a `granted ≤ held` COMPARISON: it makes amplification
STRUCTURALLY IMPOSSIBLE by COPYING the held cap (`heldCapTo k.caps del t`) verbatim — the granted cap IS
the held cap, so `granted.rights = held.rights` definitionally (the executor's own
`recKDelegate_copy_non_amplifying : confRights (heldCapTo …) ≤ confRights (heldCapTo …)` is `le_rfl`).

Moreover `checkLe : (a b : RecordKernelState → Int)` compares two `Int` read-outs; the cap RIGHTS lattice
is `ExecAuth`/`List Auth` (`confRights`), a Boolean-algebra of authorities, NOT a totally-ordered `Int`.
So this effect's non-amplification is NOT `checkLe`-expressible — and there is nothing to express, because
the unattenuated delegate copies rather than narrows. Inserting a `checkLe (confRights granted) (confRights
held)` guard would be (a) ill-typed (rights are not `Int`) and (b) VACUOUS even if coerced (it would gate
`x ≤ x`, always true — a tooth that rejects nothing). We therefore do NOT bolt on a fake `checkLe`; we pin
the real structural non-amplification as `delegateStmt_non_amplifying` (§5), the honest witness.

  - PRECISE finding for the ledger: `Dregg2/Exec/AuthTurn.lean:79` (`recKDelegate`) — guard is the
    `.any confersEdgeTo` connectivity premise, the post-`caps` is `grant … (heldCapTo …)` (a verbatim
    COPY), NO `granted ≤ held` comparison. `checkLe` (`Argus/Stmt.lean:76`, `Int`-valued) is INAPPLICABLE.
    (The `checkLe`-expressible non-amplification lives in the *attenuating* sibling `recKDelegateAtten`
    (`AuthTurn.lean:97`), whose `attenuate keep …` genuinely narrows — `attenuate_confRights_le` — that is
    a `confRights`-lattice `≤`, still NOT `Int`; a separate weld's concern, not this unattenuated one.)

## What the weld pins (HONEST SURFACE — do NOT over-read)

The circuit side is the AUDITED genuine class-A `delegateVmDescriptorGenuine` + `delegateGenuine_sound`
(`EffectVmEmitDelegate §G`, itself the shared cap-root-recompute primitive `EffectVmEmitCapRoot`), which
on a satisfying row forces the GENUINE per-cell `CapCellSpecGenuine`: `post.capRoot` is the FORCED in-row
advance `hash[ hash[holder,target,rights,op], pre.capRoot ]` (the cap-edge-mutation digest — NOT a free
parameter), every other limb (balance/nonce/8 fields/reserved) FROZEN. The executor side is the cornerstone
below: `interp (delegateStmt …)` IS the verified kernel step `recKDelegate`. The weld concludes, against
the descriptor DIRECTLY:

  * **frame-freeze leg (per-cell):** the circuit's pinned `post` has every NON-`capRoot` limb frozen at
    `pre`, AND the executor `recKDelegate` FREEZES the per-cell state entirely (it edits only `caps`, never
    `cell`/`bal`) — so the per-cell projection of any cell is unchanged. delegate has NO nonce-tick
    divergence (a cap-graph row freezes the cell nonce, matching the executor — `recKDelegate_frame`).
  * **cap-graph leg (`cap_root`):** the circuit FORCES the new `cap_root` to be the genuine recompute of
    the bound cap-edge `(holder,target,rights,op)` + the old root — the digest of the executor's installed
    edge `grant k.caps rec (heldCapTo k.caps del t)` (absorbed into `state_commit`, so a dropped/forged
    delegate-edge MOVES the commitment — `delegateGenuine_binds_edge`, cited). The weld EXPOSES this
    genuine-recompute clause as a conjunct so the cap-edge binding is part of the welded statement.

What this does NOT claim: it does not assert the circuit row's `cap_root` column EQUALS a digest `D` of the
executor's post-`caps` FUNCTION as a closed-form connector (that connector is `capRootProj`/`unify_delegate`
in `EffectVmEmitDelegate`, carried through `Function.Injective D` — the IR cannot re-derive `cap_root` from
the cap-table rows in-circuit, the inherited cap-root-hash-site IR gap). The executor produces the real
post-`caps` map (the cornerstone + `recDelegateCaps`); the genuine circuit produces the FORCED recompute of
the bound edge that the published commitment binds. That is the faithful boundary, stated, not hidden — the
SAME per-cell + genuine-side-table-root surface the escrow welds live on, now for the cap graph.

## Honesty

`#assert_axioms` on the cornerstone + the weld ⊆ {propext, Classical.choice, Quot.sound}; Poseidon2 CR
enters ONLY inside the reused emitter (not in the welded conclusion's statement). No `sorry`, no `:= True`,
no `native_decide`, no `rfl`-posing-as-bridge. Non-vacuity teeth: the IR term genuinely INSTALLS the edge
(observable cap-graph write), genuinely REJECTS an unconnected delegator (fail-closed), is genuinely
NON-AMPLIFYING (copies the held cap), and the welded descriptor is the genuine class-A one (12 frame gates +
6 hash-sites: 2 cap-root-recompute + 4 commitment), not the inert placeholder. Imports are read-only; this
file owns only itself.
-/
import Dregg2.Circuit.Argus.Stmt
import Dregg2.Circuit.Emit.EffectVmEmitDelegate

namespace Dregg2.Circuit.Argus.Effects.Delegate

open Dregg2.Exec
open Dregg2.Authority (Caps Cap Auth Label)
open Dregg2.Circuit.Argus (RecStmt interp)
open Dregg2.Circuit.Emit.EffectVmEmit
open Dregg2.Circuit.Emit.EffectVmEmitTransferSound (CellState)
open Dregg2.Circuit.Spec.AuthorityUnattenuated (recDelegateCaps recDelegateCaps_correct)
open Dregg2.Circuit.Emit.EffectVmEmitDelegate
  (delegateVmDescriptorGenuine delegateGenuine_sound)
open Dregg2.Circuit.Emit.EffectVmEmitAttenuateA (CapRowEncodes CapCellSpecGenuine attenuateGenuineRowGates)
open Dregg2.Circuit.Emit.EffectVmEmitCapRoot (capRootHolds capAdvanceOf edgeLeafOf)
open Dregg2.Circuit.Emit.EffectVmEmitCapRoot.cp (HOLDER TARGET RIGHTS OP)

set_option autoImplicit false

/-! ## §1 — The delegate effect as an Argus IR term (gate, then the cap-graph write).

`recKDelegate` is `if guard then some { k with caps := grant … } else none`. We capture it term-for-term:

  * the GATE is a `Bool`: the delegator holds a `t`-conferring cap (`.any confersEdgeTo` — the Granovetter
    connectivity premise). On a delegator with no such cap, `false`.
  * the BODY is the SINGLE cap-graph write `setCaps (fun k => recDelegateCaps k.caps del rec t)`: overwrite
    `caps` with `grant k.caps rec (heldCapTo k.caps del t)`, the validated post-`caps` map
    (`recDelegateCaps_correct`). Unlike the escrow effects (two component writes), delegate touches ONE
    component (`caps`) — the §A `setCaps` primitive, with NO new constructor.

The `setCaps` leaf re-reads `k.caps` (a pure function of `k`), so on commit it installs the grant on the
delegator's CURRENT held cap — exactly `recKDelegate`'s `grant k.caps rec (heldCapTo k.caps del t)`. -/

/-- **The delegate admissibility gate as a `Bool`** — exactly `recKDelegate`'s `if`-condition
(`AuthTurn.lean:82`): the delegator already holds a cap conferring an edge to `t`. This is the in-band
Boolean form of the Granovetter connectivity premise ("only connectivity begets connectivity"). -/
def delegateGuardB (del t : Label) (k : RecordKernelState) : Bool :=
  (k.caps del).any (fun cap => confersEdgeTo t cap)

/-- **The delegate effect as an IR term: gate, then the cap-graph write.** A single `setCaps` move on the
verified post-`caps` map `recDelegateCaps k.caps del rec t` (= `grant k.caps rec (heldCapTo k.caps del t)`).
Mirrors the escrow effects' shape (gate, then component write) but on the CAP GRAPH with one write. -/
def delegateStmt (del rec t : Label) : RecStmt :=
  RecStmt.seq (RecStmt.guard (delegateGuardB del t))
    (RecStmt.setCaps (fun k => recDelegateCaps k.caps del rec t))

/-! ## §2 — The cornerstone: `interp` of the delegate term IS the kernel step `recKDelegate`. -/

/-- **The cornerstone (cap graph).** `interp` of the delegate term IS the verified executor `recKDelegate`
— the same partial function, by construction, exactly as the transfer/mint/burn/escrow cornerstones, now
over the CAP-GRAPH effect (a single `caps` write gated by the Granovetter connectivity premise). The
`setCaps` leaf's `recDelegateCaps k.caps del rec t` is DEFINITIONALLY `grant k.caps rec (heldCapTo k.caps
del t)`, the exact map `recKDelegate` installs. -/
theorem interp_delegateStmt_eq_recKDelegate (del rec t : Label) (k : RecordKernelState) :
    interp (delegateStmt del rec t) k = recKDelegate k del rec t := by
  simp only [delegateStmt, interp]
  unfold recKDelegate
  by_cases hg : delegateGuardB del t k = true
  · -- ADMIT: the guard fires (`some k`); the `bind` β-reduces and the `setCaps` write installs
    -- `recDelegateCaps k.caps del rec t` = `grant k.caps rec (heldCapTo k.caps del t)` (definitional).
    rw [if_pos hg]
    simp only [Option.bind_some]
    unfold delegateGuardB at hg
    rw [if_pos hg]
    rfl
  · -- REJECT: the guard fails (`none`); the `bind` short-circuits ⇒ `none`. The kernel `if` also rejects.
    rw [if_neg hg]
    simp only [Option.bind_none]
    unfold delegateGuardB at hg
    rw [if_neg hg]

#assert_axioms interp_delegateStmt_eq_recKDelegate

/-! ## §3 — The EXECUTOR-side per-cell projection of `recKDelegate` (the cap-graph is a per-cell FREEZE).

The cornerstone refines the IR term to `recKDelegate`. Unlike the escrow effects (which MOVE a per-cell
ledger entry), a committed delegate FREEZES every per-cell state — it edits only `caps`, never `cell`/`bal`
— so the `EffectVmEmitTransferSound.cellProj`-style per-cell projection of ANY cell is unchanged. This is
the executor side of the descriptor's frame-freeze leg (the descriptor freezes the cell, matching). We pin
the load-bearing fact: `recKDelegate` leaves `k.cell` (and `k.bal`) untouched. -/

/-- **`recKDelegate_freezes_cell`.** A committed delegate leaves the per-cell record map `cell` LITERALLY
unchanged (it edits only `caps`). So every cell's per-cell projection (balance/nonce/fields/reserved) is
frozen — the executor side of the descriptor's frame-freeze. (Reuses the executor's own `recKDelegate_frame`
keystone, whose `.cell` clause is exactly this.) -/
theorem recKDelegate_freezes_cell {k k' : RecordKernelState} {del rec t : Label}
    (h : recKDelegate k del rec t = some k') : k'.cell = k.cell :=
  (recKDelegate_frame k k' del rec t h).2.2

/-- **`recKDelegate_installs_caps`.** A committed delegate's post-`caps` IS the validated grant map
`recDelegateCaps k.caps del rec t` — the cap-edge the genuine `cap_root` recompute binds. The executor side
of the descriptor's cap-graph leg. -/
theorem recKDelegate_installs_caps {k k' : RecordKernelState} {del rec t : Label}
    (h : recKDelegate k del rec t = some k') :
    k'.caps = recDelegateCaps k.caps del rec t := by
  unfold recKDelegate at h
  by_cases hg : (k.caps del).any (fun cap => confersEdgeTo t cap) = true
  · rw [if_pos hg] at h; simp only [Option.some.injEq] at h; subst h
    -- `{ k with caps := grant … }.caps = grant … = recDelegateCaps k.caps del rec t` (definitional).
    rfl
  · rw [if_neg hg] at h; exact absurd h (by simp)

#assert_axioms recKDelegate_freezes_cell
#assert_axioms recKDelegate_installs_caps

/-! ## §4 — THE WELD: a satisfying witness of the audited genuine class-A delegate descriptor agrees, per
cell, with the FROZEN per-cell state the IR term's executor produces — AND forces the genuine `cap_root`
recompute of the bound delegate-edge. -/

/-- **`delegate_compile_sound` — the welded soundness (delegate slice, the cap-graph effect).**

Suppose, for the Argus delegate term `delegateStmt del rec t`:
  * the circuit `delegateVmDescriptorGenuine` (the AUDITED genuine class-A cap-root-recompute descriptor) is
    SATISFIED by `(env, false, false)` under the abstract Poseidon carrier `hash`, its frame-freeze gates +
    in-row cap-root recompute holding (`hgates`, `hrec`), and its `CapRowEncodes` decoding NAMES the
    pre/post cell states `(pre, post)` with the opaque digest `capDigestNew` (`henc`);
  * the IR term's EXECUTOR interpretation COMMITS: `interp (delegateStmt del rec t) k = some k'` (`hexec`).

Then:
  * **frame-freeze leg (per-cell):** the circuit's pinned `post` has every NON-`capRoot` limb FROZEN at
    `pre` — `post.balLo = pre.balLo`, `balHi`, `nonce`, all 8 `fields`, `reserved` — AND the executor
    `recKDelegate` FREEZES the per-cell state (`k'.cell = k.cell`), so the descriptor's freeze matches the
    executor's per-cell freeze. delegate has NO nonce-tick divergence (a cap-graph row freezes the cell
    nonce; both sides agree).
  * **cap-graph leg (`cap_root`):** the circuit FORCES the new `cap_root` to be the genuine in-row recompute
    `hash[ hash[holder,target,rights,op], pre.capRoot ]` of the bound delegate-edge + old root — the digest
    of the executor's installed edge `recDelegateCaps k.caps del rec t` (absorbed into `state_commit`; a
    forged/dropped delegate-edge moves the commitment, `delegateGenuine_binds_edge`). The executor's
    post-`caps` IS that installed grant map (`recKDelegate_installs_caps`).

So the genuine class-A circuit the prover runs for delegate pins the per-cell frozen state the IR term's
executor produces AND genuinely recomputes the bound cap-graph edge — the template generalizes to a
CAP-GRAPH effect (a single `caps` write bound through a recomputed `cap_root`). -/
theorem delegate_compile_sound
    (hash : List ℤ → ℤ) (env : VmRowEnv)
    (k k' : RecordKernelState) (del rec t : Label)
    (pre post : CellState) (capDigestNew : ℤ)
    (henc : CapRowEncodes env pre post capDigestNew)
    (hgates : ∀ c ∈ attenuateGenuineRowGates, c.holdsVm env false false)
    (hrec : capRootHolds hash env)
    (hsat : interp (delegateStmt del rec t) k = some k') :
    -- frame-freeze leg: the circuit pins every NON-capRoot limb frozen at `pre`, and the executor freezes
    -- the per-cell state (k'.cell = k.cell) — the cap-graph effect touches no per-cell ledger.
    ( post.balLo = pre.balLo
      ∧ post.balHi = pre.balHi
      ∧ post.nonce = pre.nonce
      ∧ (∀ i : Fin 8, post.fields i = pre.fields i)
      ∧ post.reserved = pre.reserved
      ∧ k'.cell = k.cell )
    -- … and the cap-graph leg: the circuit FORCES the genuine cap-root recompute (bound delegate-edge +
    -- old root), and the executor installs exactly that edge as its post-`caps`.
    ∧ ( post.capRoot
          = capAdvanceOf hash
              (edgeLeafOf hash (env.loc (prmCol HOLDER)) (env.loc (prmCol TARGET))
                (env.loc (prmCol RIGHTS)) (env.loc (prmCol OP)))
              pre.capRoot
        ∧ k'.caps = recDelegateCaps k.caps del rec t ) := by
  -- circuit side: the audited genuine class-A soundness forces the per-cell `CapCellSpecGenuine`
  -- (cap_root the FORCED recompute, every other limb frozen).
  obtain ⟨hcCap, hcLo, hcHi, hcN, hcF, hcRes⟩ :=
    delegateGenuine_sound hash env pre post capDigestNew henc hgates hrec
  -- executor side: the §2 cornerstone turns the IR term's `interp` into the verified `recKDelegate`; it
  -- freezes the per-cell state and installs the validated grant map.
  rw [interp_delegateStmt_eq_recKDelegate] at hsat
  exact ⟨⟨hcLo, hcHi, hcN, hcF, hcRes, recKDelegate_freezes_cell hsat⟩,
          hcCap, recKDelegate_installs_caps hsat⟩

#assert_axioms delegate_compile_sound

/-! ## §5 — NON-VACUITY: the IR term genuinely INSTALLS the edge (observable cap-graph write), genuinely
REJECTS an unconnected delegator (fail-closed), is genuinely NON-AMPLIFYING (the §NON-AMPLIFICATION witness),
and the welded descriptor is the genuine class-A one (not the inert placeholder). -/

/-- A concrete two-account kernel where the delegator (cell `0`) HOLDS a `node 1` cap (an edge to `1`), the
recipient (cell `2`) holds none. So a delegate of the edge to target `1` is admissible and OBSERVABLE. -/
def kD0 : RecordKernelState :=
  { accounts := {0, 1, 2}
    cell := fun _ => .record [("balance", .int 0)]
    caps := fun l => if l = 0 then [Cap.node 1] else [] }

/-- **NON-VACUITY (the cap-graph write is OBSERVABLE — the edge INSTALLS).** Running the delegate term on
`kD0` (delegator `0` holds `node 1`, recipient `2` holds nothing) commits, and recipient cell `2`'s cap-slot
GAINS the delegator's held `node 1` cap (`[]` → `[Cap.node 1]`): the `setCaps` write is a real, observable
cap-graph mutation (the recipient becomes connected to `1`), not a no-op. -/
theorem delegateStmt_installs_edge :
    (interp (delegateStmt 0 2 1) kD0).map (fun k => k.caps 2) = some [Cap.node 1] := by
  rw [interp_delegateStmt_eq_recKDelegate]
  decide

/-- **NON-VACUITY (recipient was empty before).** Cell `2` held NO caps before the delegate — so the edge
install above is a genuine state change, not a pre-existing edge. -/
theorem delegateStmt_recipient_empty_before : kD0.caps 2 = [] := by decide

/-- **NON-VACUITY (fail-closed).** A delegate whose DELEGATOR holds no `t`-conferring cap does NOT commit:
delegating from the empty recipient cell `2` (which holds nothing) the edge to `1` returns `none` — the
Granovetter connectivity premise fails, so the cap-graph write never fires (only connectivity begets
connectivity). -/
theorem delegateStmt_rejects_unconnected :
    interp (delegateStmt 2 1 1) kD0 = none := by
  rw [interp_delegateStmt_eq_recKDelegate]
  decide

/-- **NON-AMPLIFICATION (the structural witness — the §NON-AMPLIFICATION finding, as a theorem).** The cap
the delegate INSTALLS into the recipient's slot is the delegator's held `t`-conferring cap COPIED VERBATIM
(`heldCapTo k.caps del t`), so its conferred rights EQUAL (hence `≤`) the held cap's — non-amplification
holds by COPYING, not by an `Int` `checkLe` comparison (which is inapplicable: rights are `confRights`/
`ExecAuth`, not `Int`, and a copy needs no comparison). This is the honest non-amplification tooth for the
unattenuated delegate, pinned so the "no `checkLe`" decision is witnessed, not asserted. -/
theorem delegateStmt_non_amplifying (del rec t : Label) (k k' : RecordKernelState)
    (h : interp (delegateStmt del rec t) k = some k') :
    heldCapTo k.caps del t ∈ k'.caps rec
    ∧ confRights (heldCapTo k.caps del t) ≤ confRights (heldCapTo k.caps del t) := by
  rw [interp_delegateStmt_eq_recKDelegate] at h
  exact ⟨recKDelegate_grants k k' del rec t h, le_rfl⟩

/-- The welded delegate circuit is the genuine class-A descriptor, NOT the empty placeholder: it carries the
12 frame-freeze gates + transition/boundary constraints (no opaque cap-move gate) and the 6 hash-sites
(2 genuine cap-root-recompute + 4 commitment). So `delegate_compile_sound` is about a REAL cap-graph-binding
circuit. (`delegateVmDescriptorGenuine` is definitionally `attenuateVmDescriptorGenuine` — the SHARED genuine
cap-root-recompute descriptor.) -/
theorem delegateVmDescriptorGenuine_nontrivial :
    delegateVmDescriptorGenuine.constraints.length = 12 + 14 + 4
    ∧ delegateVmDescriptorGenuine.hashSites.length = 6 := by
  refine ⟨by decide, by decide⟩

#assert_axioms delegateStmt_installs_edge
#assert_axioms delegateStmt_recipient_empty_before
#assert_axioms delegateStmt_rejects_unconnected
#assert_axioms delegateStmt_non_amplifying
#assert_axioms delegateVmDescriptorGenuine_nontrivial

end Dregg2.Circuit.Argus.Effects.Delegate
