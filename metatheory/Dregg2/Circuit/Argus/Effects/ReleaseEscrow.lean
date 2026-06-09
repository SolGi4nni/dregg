/-
# Dregg2.Circuit.Argus.Effects.ReleaseEscrow — the releaseEscrow effect welded into the Argus IR.

`Argus/Stmt.lean` laid the cornerstone (the executor IS the meaning of a `RecStmt` term) and validated
it on transfer/mint/burn (single-cell moves) and `createEscrow` — the first SIDE-TABLE effect, a TWO
component move that INSERTS (debit `bal` + PREPEND an unresolved record onto `escrows`). `Argus/Compile.lean`
welded each: the audited class-A circuit pinned the per-cell post-state the IR term's executor produces.

This module welds the SETTLE sibling `releaseEscrow` in the SAME method, in a disjoint file (it imports
the Argus IR + the audited releaseEscrow emitter read-only and owns only its own declarations). The
genuinely different shape — and the point of the de-risk — is that `releaseEscrow` RESOLVES an EXISTING
record rather than inserting one:

  the kernel step `releaseEscrowKAsset` (`RecordKernel.lean:1565`)

    match k.escrows.find? (fun r => decide (r.id = id ∧ r.resolved = false)) with
    | some r => if r.recipient ∈ k.accounts ∧ cellLifecycleLive k r.recipient = true then
                  some (settleEscrowRawAsset k id r.recipient r.asset r.amount)
                else none
    | none   => none

  with `settleEscrowRawAsset k id target asset amount = { k with bal := recBalCreditCell k.bal target
  asset amount, escrows := markResolved k.escrows id }`,

so a committed release READS the parked record `r` (by id), CREDITS the recipient `+r.amount` at `r.asset`
(the parked value SETTLED — the honest contrast with refund/cancel, which credit the CREATOR), and
RESOLVES the holding-store (`markResolved` flips the first id-matching unresolved record). Its gate is a
`find?`-conditioned **settle-liveness** check (`META-FILL C`): the recipient must be a LIVE account
(crediting a dead cell would silently DESTROY value), unlike createEscrow's authority/availability/id
gate.

## THE IR-GRAMMAR FINDING (the most valuable bit): the FILTER-shaped `escrows` write FITS `setEscrows`.

createEscrow mutates `escrows` by a PREPEND (`record :: k.escrows`); releaseEscrow mutates it by a
FILTER/MAP (`markResolved k.escrows id` flips one element in place). One might expect the settle leg to
need a new list-FILTER IR primitive. It does NOT: the §A primitive `setEscrows (g : RecordKernelState →
List EscrowRecord)` takes an ARBITRARY list-producing function, so `g := fun k => markResolved k.escrows id`
is a direct, faithful instantiation — the SAME primitive createEscrow's prepend uses. So the IR grammar
already covers the settle list-shape; the template generalizes to a settle-leg with NO new constructor.

The ONE structural difference from createEscrow handled here: the credit's target/asset/amount and the
resolve all depend on the FOUND record `r`, recovered inside the gate. Because the `setBal`/`setEscrows`
leaves are `RecordKernelState → …` functions, each re-reads the SAME `find?` (a pure function of `k`), so
on commit they extract the same `r` the gate found — the term is faithful with the primitives as they are.

## What the weld pins (HONEST SURFACE — do NOT over-read)

The circuit side is the AUDITED CLASS-A `releaseEscrowVmDescriptorGenuine` + `releaseEscrowGenuine_sound`
(`EffectVmEmitReleaseEscrow §H`), which on a satisfying row forces (a) the per-cell `CellReleaseSpec` (the
recipient cell's `balLo` CREDIT by `amount`, the nonce FROZEN — release does NOT tick, every other limb
frozen) and (b) the GENUINE in-row escrow-root RECOMPUTE (`SYS_DIG_AFTER = hash[hash[record], SYS_DIG_BEFORE]`
with `resolved` the record's flag — the side-table digest FORCED, not a free step) and (c) the published
commit. The executor side is the §E-style cornerstone below: `interp (releaseEscrowStmt …)` IS the verified
kernel step `releaseEscrowKAsset`. The weld concludes, against the descriptor DIRECTLY:

  * **conserved leg (per-cell):** the circuit's pinned post-`balLo` (= pre + `amount`) equals the executor's
    settle-credited `bal r.recipient r.asset` at the FOUND record `r`, with the frozen frame
    (balHi/fields/capRoot/reserved) AND the FROZEN nonce agreeing. `cellProjRelease` projects ONLY the
    `(recipient, asset)` ledger entry into `balLo` (the other limbs are `0`, FROZEN), so this binds the
    CREDITED cell, exactly as transfer binds the SRC cell. release has NO nonce-tick divergence (both
    descriptor and executor freeze).
  * **side-table leg (the escrow record):** the circuit FORCES the new escrow-list root to be the genuine
    recompute of the bound record content + the old root — the digest the executor's `escrows :=
    markResolved k.escrows id` resolve commits to (absorbed into `state_commit`, so a forged/un-resolved
    record MOVES the commitment — `releaseEscrowGenuine_binds_record`, cited). The weld EXPOSES this clause.

What this does NOT claim: it does not assert the circuit row's `escrows` digest EQUALS the executor's
`markResolved k.escrows id` AS A LIST — the EffectVM row carries a DIGEST, not the list; they agree only up
to the side-table root (the `SystemRoots` digest connector). The executor produces the real resolved list
(the cornerstone + `markResolved`); the circuit produces the genuine root of it. That is the faithful
boundary, stated, not hidden.

## Honesty

`#assert_axioms` on both headline theorems ⊆ {propext, Classical.choice, Quot.sound}; Poseidon2 CR enters
ONLY inside the reused emitter (not in the welded conclusion's statement). No `sorry`, no `:= True`, no
`native_decide`. Imports are read-only; this file owns only itself.
-/
import Dregg2.Circuit.Argus.Stmt
import Dregg2.Circuit.Emit.EffectVmEmitReleaseEscrow
import Dregg2.Circuit.Emit.EffectVmEmitReleaseEscrowWide

namespace Dregg2.Circuit.Argus.Effects.ReleaseEscrow

open Dregg2.Exec
open Dregg2.Circuit.Argus (RecStmt interp)
open Dregg2.Circuit.Emit.EffectVmEmit
open Dregg2.Circuit.Emit.EffectVmEmitTransferSound (CellState)
open Dregg2.Circuit.Emit.EffectVmEmitReleaseEscrow
  (releaseEscrowVmDescriptorGenuine releaseEscrowGenuine_sound ReleaseParams CellReleaseSpec
   RowEncodesRelease cellProjRelease)

/-! ## §1 — The releaseEscrow effect as an Argus IR term (gate, then the TWO component writes).

`releaseEscrowKAsset` is `match find? | some r => if live then some (settle …) else none | none => none`.
We capture it term-for-term:

  * the GATE is a `Bool`: `find?` an unresolved id-matching record, then the settle-liveness check on its
    recipient. Both rejection cases of the kernel (`none` find, dead recipient) collapse to `false` exactly.
  * the BODY is `seq (setBal <credit>) (setEscrows <resolve>)`: credit the FOUND recipient `+amount` at the
    record's asset, then `markResolved` the holding-store. The credit's target/asset/amount read the SAME
    `find?` inside the `setBal` leaf — on commit it returns the same `r` the gate found.

`setEscrows`'s leaf is `fun k => markResolved k.escrows id` — the FILTER-shaped settle write, fitting the
existing list primitive directly (the IR-grammar finding in this file's header). -/

/-- The kernel's `find?` predicate for an UNRESOLVED record of this id (the exact predicate
`releaseEscrowKAsset` walks `escrows` with). -/
def findUnresolved (k : RecordKernelState) (id : Nat) : Option EscrowRecord :=
  k.escrows.find? (fun r => decide (r.id = id ∧ r.resolved = false))

/-- **The releaseEscrow admissibility gate as a `Bool`** — exactly `releaseEscrowKAsset`'s `match`/`if`:
an unresolved id-matching record is present (`find? = some r`) AND its recipient is a live account
(`r.recipient ∈ accounts ∧ cellLifecycleLive recipient`, the settle-liveness gate). On `find? = none`,
`false`. This is the in-band Boolean form of the kernel's two-stage admission (the credit-of-a-dead-cell
value-destruction guard). -/
def releaseEscrowGuard (id : Nat) (k : RecordKernelState) : Bool :=
  match findUnresolved k id with
  | some r => decide (r.recipient ∈ k.accounts ∧ cellLifecycleLive k r.recipient = true)
  | none   => false

/-- The settle-credit leaf: credit the FOUND record's recipient `+amount` at the record's asset (re-reading
`find?` inside the leaf — a pure function of `k`, so on commit it is the same `r` the gate found). On
`find? = none` (only reachable when the gate already rejected) the ledger is left unchanged — irrelevant to
the committed semantics. -/
def releaseCreditBal (id : Nat) (k : RecordKernelState) : CellId → AssetId → Int :=
  match findUnresolved k id with
  | some r => recBalCreditCell k.bal r.recipient r.asset r.amount
  | none   => k.bal

/-- **The releaseEscrow effect as an IR term: gate, then the TWO component writes.** Unlike transfer/mint/
burn (one move) and like createEscrow (two), the body is `seq (setBal <credit>) (setEscrows <resolve>)`:
credit the found recipient, then `markResolved` the holding-store. The two §A component-write primitives
`setBal`/`setEscrows` are exactly the shapes a multi-component settle effect assembles — `setEscrows`
carries the FILTER-shaped `markResolved` write with NO new constructor. -/
def releaseEscrowStmt (id : Nat) : RecStmt :=
  RecStmt.seq (RecStmt.guard (releaseEscrowGuard id))
    (RecStmt.seq
      (RecStmt.setBal (fun k => releaseCreditBal id k))
      (RecStmt.setEscrows (fun k => markResolved k.escrows id)))

/-! ## §2 — The cornerstone: `interp` of the releaseEscrow term IS the kernel step `releaseEscrowKAsset`. -/

/-- The releaseEscrow `Bool` gate decodes to `releaseEscrowKAsset`'s admission: an unresolved record is
found whose recipient is a live account. Stated as the `Option`-conditioned proposition the kernel `match`
opens on, so the cornerstone's case split lines up with the kernel body. -/
theorem releaseEscrowGuard_iff (id : Nat) (k : RecordKernelState) :
    releaseEscrowGuard id k = true ↔
      (∃ r, findUnresolved k id = some r
        ∧ r.recipient ∈ k.accounts ∧ cellLifecycleLive k r.recipient = true) := by
  unfold releaseEscrowGuard findUnresolved
  cases hfind : k.escrows.find? (fun r => decide (r.id = id ∧ r.resolved = false)) with
  | none => simp
  | some r =>
    simp only [decide_eq_true_eq]
    constructor
    · intro h; exact ⟨r, rfl, h.1, h.2⟩
    · rintro ⟨r', hr', hrec, hlive⟩
      -- the case split already rewrote the existential witness's `find?` to `some r`, so `hr' : some r
      -- = some r'` forces `r = r'`.
      cases hr'; exact ⟨hrec, hlive⟩

/-- **The cornerstone (settle side-table).** `interp` of the releaseEscrow term IS the verified kernel step
`releaseEscrowKAsset` — the same partial function, by construction, exactly as the transfer/mint/burn/
createEscrow cornerstones, now over a TWO-component SETTLE side-table effect (read + credit + resolve). -/
theorem interp_releaseEscrowStmt_eq_releaseEscrowKAsset (id : Nat) (k : RecordKernelState) :
    interp (releaseEscrowStmt id) k = releaseEscrowKAsset k id := by
  -- the IR side is `(if guard then some k else none).bind (setBal credit) .bind (setEscrows resolve)`.
  simp only [releaseEscrowStmt, interp]
  by_cases hg : releaseEscrowGuard id k = true
  · -- ADMIT: the guard fires (`some k`); the `bind` β-reduces `a := k`, so the `setBal` credit leaf
    -- and the kernel body both read `k.escrows.find? = some r` for the SAME found record.
    rw [if_pos hg]
    obtain ⟨r, hfind, hrec, hlive⟩ := (releaseEscrowGuard_iff id k).mp hg
    unfold releaseEscrowKAsset releaseCreditBal findUnresolved at *
    simp only [Option.bind_some, hfind, settleEscrowRawAsset]
    rw [if_pos ⟨hrec, hlive⟩]
  · -- REJECT: the guard fails (`none`); the `bind` short-circuits ⇒ `none`. The kernel body also
    -- returns `none` (no live unresolved record), by the contrapositive of `releaseEscrowGuard_iff`.
    rw [if_neg hg, Option.bind_none]
    unfold releaseEscrowKAsset
    cases hfind : k.escrows.find? (fun r => decide (r.id = id ∧ r.resolved = false)) with
    | none => rfl
    | some r =>
      by_cases hlive : r.recipient ∈ k.accounts ∧ cellLifecycleLive k r.recipient = true
      · exact absurd ((releaseEscrowGuard_iff id k).mpr ⟨r, hfind, hlive.1, hlive.2⟩) hg
      · show none = if r.recipient ∈ k.accounts ∧ cellLifecycleLive k r.recipient = true
                      then _ else none
        rw [if_neg hlive]

#assert_axioms interp_releaseEscrowStmt_eq_releaseEscrowKAsset

/-! ## §3 — The EXECUTOR-side per-cell projection of `releaseEscrowKAsset` (the `recKMint_proj_balLo`
analogue, for the settle credit).

The cornerstone refines the IR term to the kernel step `releaseEscrowKAsset`. We need its per-cell
projection onto `cellProjRelease …bal recipient asset` — a committed release CREDITS the recipient cell's
projected `(recipient, asset)` ledger entry by exactly the FOUND record's `amount` (`cellProjRelease.balLo`
reads the per-asset entry, the measure `recBalCreditCell … (+amount)` moves). The frozen frame
(balHi/nonce/fields/capRoot/reserved) is `0 = 0` on both projections (definitional). -/

/-- **`releaseEscrowKAsset_proj_balLo`.** A committed kernel release credits the found record's recipient
cell's projected `(recipient, asset)` ledger entry by exactly the parked `amount` (the value settled). The
per-cell conserved leg the weld pins, witnessed by the found record `r`. -/
theorem releaseEscrowKAsset_proj_balLo {k k' : RecordKernelState} {id : Nat}
    (h : releaseEscrowKAsset k id = some k') :
    ∃ r, findUnresolved k id = some r
      ∧ (cellProjRelease k'.bal r.recipient r.asset).balLo
          = (cellProjRelease k.bal r.recipient r.asset).balLo + r.amount := by
  unfold releaseEscrowKAsset at h
  cases hfind : k.escrows.find? (fun r => decide (r.id = id ∧ r.resolved = false)) with
  | none => simp only [hfind] at h; exact absurd h (by simp)
  | some r =>
    simp only [hfind] at h
    by_cases hlive : r.recipient ∈ k.accounts ∧ cellLifecycleLive k r.recipient = true
    · rw [if_pos hlive] at h
      simp only [Option.some.injEq] at h; subst h
      refine ⟨r, hfind, ?_⟩
      show recBalCreditCell k.bal r.recipient r.asset r.amount r.recipient r.asset
            = k.bal r.recipient r.asset + r.amount
      unfold recBalCreditCell; rw [if_pos ⟨rfl, rfl⟩]
    · rw [if_neg hlive] at h; exact absurd h (by simp)

#assert_axioms releaseEscrowKAsset_proj_balLo

/-! ## §4 — THE WELD: a satisfying witness of the audited class-A releaseEscrow descriptor agrees, per
cell, with the post-state the IR term's executor interpretation produces — AND forces the genuine
escrow-root recompute. -/

/-- **`releaseEscrow_compile_sound` — the welded soundness (releaseEscrow slice, a SETTLE side-table effect).**

Suppose, for the Argus releaseEscrow term `releaseEscrowStmt id`:
  * the circuit `releaseEscrowVmDescriptorGenuine` (the AUDITED class-A genuine-root descriptor) is SATISFIED
    by `(env, true, true)` under the abstract Poseidon carrier `hash`, and its `RowEncodesRelease` decoding
    NAMES the post-state record `post` over a recipient-cell projection `pre` with the `⟨amount⟩` param block
    (`henc`);
  * the IR term's EXECUTOR interpretation COMMITS: `interp (releaseEscrowStmt id) k = some k'` (`hexec`).

Then there is a FOUND record `r` (`findUnresolved k id = some r`, the holding-store entry the release
settles) such that, when the descriptor's encoded cell IS the recipient cell's pre-projection
(`pre = cellProjRelease k.bal r.recipient r.asset`) crediting `r.amount`:
  * **conserved leg (per-cell):** the circuit's pinned `post` AGREES with the executor's settle-credited
    recipient-cell projection `cellProjRelease k'.bal r.recipient r.asset` — the conserved `balLo` (credited
    by `r.amount`) AND the whole frozen frame (balHi/fields/capRoot/reserved) AND the FROZEN nonce. release
    has NO nonce-tick divergence (the descriptor freezes the cell nonce, matching the executor —
    `cellProjRelease` sends `nonce` to `0` on both sides).
  * **side-table leg:** the circuit FORCES the new escrow-list root carrier to be the genuine in-row recompute
    `hash[ hash[id,creator,recipient,amount,asset,resolved], old_root ]` of the bound record + old root — the
    digest the executor's `escrows := markResolved k.escrows id` resolve commits to (absorbed into
    `state_commit`, so the resolved record is bound; see `releaseEscrowGenuine_binds_record`).

So the class-A circuit the prover runs for releaseEscrow pins the per-cell settled state the IR term's
executor produces AND genuinely recomputes the bound `escrows` side-table root — the template generalizes
to a SETTLE side-table effect (read + credit + resolve), reusing the FILTER-shaped `setEscrows` write. -/
theorem releaseEscrow_compile_sound
    (hash : List ℤ → ℤ) (env : VmRowEnv)
    (k k' : RecordKernelState) (id : Nat) (amount : ℤ)
    (post : CellState)
    (hsat : satisfiedVm hash releaseEscrowVmDescriptorGenuine env true true)
    (hexec : interp (releaseEscrowStmt id) k = some k')
    (henc : ∃ r, findUnresolved k id = some r ∧ r.amount = amount ∧
      RowEncodesRelease env (cellProjRelease k.bal r.recipient r.asset) ⟨amount⟩ post) :
    ∃ r, findUnresolved k id = some r ∧
      -- conserved leg: the credited recipient cell's projection agrees on balLo + the whole frozen frame …
      ( post.balLo = (cellProjRelease k'.bal r.recipient r.asset).balLo
        ∧ post.balHi = (cellProjRelease k'.bal r.recipient r.asset).balHi
        ∧ (∀ i, post.fields i = (cellProjRelease k'.bal r.recipient r.asset).fields i)
        ∧ post.capRoot = (cellProjRelease k'.bal r.recipient r.asset).capRoot
        ∧ post.reserved = (cellProjRelease k'.bal r.recipient r.asset).reserved
        ∧ post.nonce = (cellProjRelease k'.bal r.recipient r.asset).nonce )
      -- … and the SIDE-TABLE leg: the circuit FORCES the genuine escrow-list-root recompute (bound record +
      -- old root), absorbed into `state_commit`.
      ∧ ( env.loc Dregg2.Circuit.Emit.EffectVmEmitEscrowRoot.SYS_DIG_AFTER
            = Dregg2.Circuit.Emit.EffectVmEmitEscrowRoot.advanceOf hash
                (Dregg2.Circuit.Emit.EffectVmEmitEscrowRoot.leafOf hash
                  (env.loc (prmCol Dregg2.Circuit.Emit.EffectVmEmitEscrowRoot.ep.ID))
                  (env.loc (prmCol Dregg2.Circuit.Emit.EffectVmEmitEscrowRoot.ep.CREATOR))
                  (env.loc (prmCol Dregg2.Circuit.Emit.EffectVmEmitEscrowRoot.ep.RECIPIENT))
                  (env.loc (prmCol Dregg2.Circuit.Emit.EffectVmEmitEscrowRoot.AMOUNT))
                  (env.loc (prmCol Dregg2.Circuit.Emit.EffectVmEmitEscrowRoot.ep.ASSET))
                  (env.loc (prmCol Dregg2.Circuit.Emit.EffectVmEmitEscrowRoot.ep.RESOLVED)))
                (env.loc Dregg2.Circuit.Emit.EffectVmEmitEscrowRoot.SYS_DIG_BEFORE) ) := by
  obtain ⟨r, hfind, hamt, hrenc⟩ := henc
  -- executor side: the §2 cornerstone turns the IR term's `interp` into the verified kernel step
  -- `releaseEscrowKAsset`; its per-cell projection gives the credited balLo (the frozen limbs are `0 = 0`).
  rw [interp_releaseEscrowStmt_eq_releaseEscrowKAsset] at hexec
  obtain ⟨r', hfind', heLo⟩ := releaseEscrowKAsset_proj_balLo hexec
  -- the found record is unique (`find?` is a function), so `r' = r`.
  rw [hfind] at hfind'; cases hfind'
  -- circuit side: the audited class-A soundness forces the per-cell `CellReleaseSpec` + the genuine root.
  subst hamt
  obtain ⟨hcs, hroot, _hcommit⟩ :=
    releaseEscrowGenuine_sound hash env (cellProjRelease k.bal r.recipient r.asset) post ⟨r.amount⟩ hrenc hsat
  obtain ⟨hcLo, hcHi, hcN, hcF, hcCap, hcRes⟩ := hcs
  refine ⟨r, hfind, ⟨?_, hcHi.trans rfl, fun i => (hcF i).trans rfl, hcCap.trans rfl, hcRes.trans rfl,
    hcN.trans rfl⟩, hroot⟩
  -- balLo: circuit pins post = pre + amount; executor credits the projected entry by amount.
  rw [hcLo, heLo]

#assert_axioms releaseEscrow_compile_sound

/-! ## §5 — NON-VACUITY: the IR term genuinely RESOLVES (the settle write is observable), and the welded
descriptor is the genuine class-A one (not the empty placeholder).

The cornerstone could be hollow if releaseEscrow never committed, or if the `setEscrows` resolve were a
no-op. Here a concrete chained-free kernel `kR0` parks ONE unresolved live-recipient escrow (id 7, recipient
cell 1, amount 30, asset 0); running the term resolves it — the record's `resolved` flag flips `false → true`
(the FILTER write is real, not a no-op) and the recipient's `(1,0)` ledger entry rises by 30. And the welded
descriptor carries the 34 per-row gates + 6 hash-sites (2 genuine escrow-recompute + 4 commitment), distinct
from the inert placeholder. -/

/-- A concrete kernel parking ONE unresolved escrow: id 7, creator 0, recipient 1 (a live account), amount
30, asset 0. Cells 0 and 1 are live accounts; lifecycle defaults Live. -/
def kR0 : RecordKernelState :=
  { accounts := {0, 1}
    cell := fun _ => .record [("balance", .int 0)]
    caps := fun _ => []
    escrows := [{ id := 7, creator := 0, recipient := 1, amount := 30, resolved := false, asset := 0 }] }

/-- **NON-VACUITY (the settle write is OBSERVABLE — the record RESOLVES).** Running the releaseEscrow term
on `kR0` commits, and the parked record's `resolved` flag flips `false → true`: the `markResolved` FILTER
write is a real, observable holding-store mutation (the record LEAVES the unresolved set), not a no-op. -/
theorem releaseEscrowStmt_resolves :
    (interp (releaseEscrowStmt 7) kR0).map
        (fun k => (k.escrows.head?.map (fun r => r.resolved)).getD false) = some true := by
  rw [interp_releaseEscrowStmt_eq_releaseEscrowKAsset]
  decide

/-- **NON-VACUITY (the settle CREDIT is OBSERVABLE).** The committed release raises recipient cell `1`'s
per-asset `(1, 0)` ledger entry from `0` to `30` — the parked value genuinely settles to the recipient. -/
theorem releaseEscrowStmt_credits :
    (interp (releaseEscrowStmt 7) kR0).map (fun k => k.bal 1 0) = some 30 := by
  rw [interp_releaseEscrowStmt_eq_releaseEscrowKAsset]
  decide

/-- **NON-VACUITY (fail-closed).** A release of a NON-existent id (`99`) does NOT commit — the term returns
`none` (the gate's `find?` is `none`), so the settle write never fires on a missing record. -/
theorem releaseEscrowStmt_rejects_missing :
    interp (releaseEscrowStmt 99) kR0 = none := by
  rw [interp_releaseEscrowStmt_eq_releaseEscrowKAsset]
  decide

/-- The welded releaseEscrow circuit is the genuine class-A descriptor, NOT the empty placeholder: it carries
the 34 per-row constraints (credit + frame freeze + transition/boundary) and the 6 hash-sites (2 genuine
escrow-root-recompute + 4 commitment). So `releaseEscrow_compile_sound` is about a REAL side-table-binding
circuit. -/
theorem releaseEscrowDescriptorGenuine_nontrivial :
    releaseEscrowVmDescriptorGenuine.constraints.length = 34
    ∧ releaseEscrowVmDescriptorGenuine.hashSites.length = 6
    ∧ releaseEscrowVmDescriptorGenuine.ranges.length = 2 := by
  refine ⟨by decide, by decide, by decide⟩

#assert_axioms releaseEscrowStmt_resolves
#assert_axioms releaseEscrowStmt_credits
#assert_axioms releaseEscrowStmt_rejects_missing
#assert_axioms releaseEscrowDescriptorGenuine_nontrivial

/-! ## §6 — FULL-STATE on the RUNNABLE descriptor (the magnesium breadth — bind ALL 17 fields).

§4 welds the AUDITED class-A descriptor (`releaseEscrowVmDescriptorGenuine`, raw-`96` carrier).
`EffectVmEmitReleaseEscrowWide.releaseEscrow_runnable_full_sound` lifts the SAME per-row gates through the
generic `runnable_full_sound` over the WIDE descriptor `releaseEscrowVmDescriptorWide` (dedicated
`sysRootsDigestCol`, `wideHashSites`, widened width): a satisfying row binds the FULL 17-field post-state
(per-cell CREDIT to the recipient AND the `escrows` digest advance), the generic anti-ghost giving:
tamper ANY absorbed state-block column OR ANY of the 8 side-table roots ⇒ UNSAT.

This section welds THAT full-state crown to the SAME executor cornerstone (§2 + the §3 projection). Since
slashObligation is the dispatch-alias of this descriptor (`Argus/Effects/SlashObligation.lean`), it
inherits the full-state binding through the SAME wide circuit. -/

open Dregg2.Circuit.Emit.EffectVmEmitReleaseEscrowWide
  (releaseEscrowVmDescriptorWide releaseEscrow_runnable_full_sound)
open Dregg2.Circuit.Emit.EffectVmEmitEscrowFamilyWide (ESCROW_STEP_PARAM)
open Dregg2.Exec.SystemRoots (SysRoots systemRootsDigest)

/-- **`releaseEscrow_runnable_full_state` — THE FULL-STATE WELD (releaseEscrow / slashObligation).**

Suppose, for the Argus releaseEscrow term:
  * the WIDE RUNNABLE descriptor `releaseEscrowVmDescriptorWide` is SATISFIED by `(env, true, true)`, its
    `RowEncodesRelease` decoding NAMES `post` over a recipient-cell projection `pre` with `⟨amount⟩`, the
    dedicated digest carriers are pinned to the `systemRootsDigest` of the pre/post sub-blocks
    (`hAfter`/`hBefore`) with the accumulator `step` (`hStep`);
  * the IR term's EXECUTOR interpretation COMMITS (`hexec`).

Then there is a FOUND record `r` such that, when the descriptor's encoded cell IS the recipient cell's
pre-projection crediting `r.amount`, the circuit's pinned `post` AGREES with the executor's settle-credited
recipient-cell projection `cellProjRelease k'.bal r.recipient r.asset` on EVERY limb AND the WIDE descriptor
binds the `escrows` side-table digest advance. So the circuit the prover RUNS pins the per-cell state the
executor produces AND the full side-table digest — all 17 fields. -/
theorem releaseEscrow_runnable_full_state
    (hash : List ℤ → ℤ) (env : VmRowEnv)
    (k k' : RecordKernelState) (id : Nat) (amount : ℤ)
    (post : CellState) (preRoots postRoots : SysRoots) (step : ℤ)
    (hrow : Dregg2.Circuit.Emit.EffectVmEmitReleaseEscrow.IsReleaseEscrowRow env)
    (hAfter : env.loc Dregg2.Circuit.Emit.EffectVmEmit.sysRootsDigestCol
                = systemRootsDigest hash postRoots)
    (hBefore : env.loc Dregg2.Circuit.Emit.EffectVmEmit.sysRootsDigestColBefore
                = systemRootsDigest hash preRoots)
    (hStep : env.loc (Dregg2.Circuit.Emit.EffectVmEmit.prmCol ESCROW_STEP_PARAM) = step)
    (hsat : satisfiedVm hash releaseEscrowVmDescriptorWide env true true)
    (hexec : interp (releaseEscrowStmt id) k = some k')
    (henc : ∃ r, findUnresolved k id = some r ∧ r.amount = amount ∧
      RowEncodesRelease env (cellProjRelease k.bal r.recipient r.asset) ⟨amount⟩ post) :
    ∃ r, findUnresolved k id = some r ∧
      ( post.balLo = (cellProjRelease k'.bal r.recipient r.asset).balLo
        ∧ post.balHi = (cellProjRelease k'.bal r.recipient r.asset).balHi
        ∧ (∀ i, post.fields i = (cellProjRelease k'.bal r.recipient r.asset).fields i)
        ∧ post.capRoot = (cellProjRelease k'.bal r.recipient r.asset).capRoot
        ∧ post.reserved = (cellProjRelease k'.bal r.recipient r.asset).reserved
        ∧ post.nonce = (cellProjRelease k'.bal r.recipient r.asset).nonce )
      ∧ systemRootsDigest hash postRoots = systemRootsDigest hash preRoots + step := by
  obtain ⟨r, hfind, hamt, hrenc⟩ := henc
  -- executor side: the §2 cornerstone + §3 projection give the credited balLo for the FOUND record.
  rw [interp_releaseEscrowStmt_eq_releaseEscrowKAsset] at hexec
  obtain ⟨r', hfind', heLo⟩ := releaseEscrowKAsset_proj_balLo hexec
  rw [hfind] at hfind'; cases hfind'
  subst hamt
  -- circuit side: the WIDE full-state crown forces the per-cell `CellReleaseSpec` + the digest advance.
  obtain ⟨hcs, hdig⟩ :=
    releaseEscrow_runnable_full_sound ⟨r.amount⟩ hash preRoots step env
      (cellProjRelease k.bal r.recipient r.asset) post postRoots hrow hrenc hAfter hBefore hStep hsat
  obtain ⟨hcLo, hcHi, hcN, hcF, hcCap, hcRes⟩ := hcs
  refine ⟨r, hfind, ⟨?_, hcHi.trans rfl, fun i => (hcF i).trans rfl, hcCap.trans rfl, hcRes.trans rfl,
    hcN.trans rfl⟩, hdig⟩
  rw [hcLo, heLo]

#assert_axioms releaseEscrow_runnable_full_state

end Dregg2.Circuit.Argus.Effects.ReleaseEscrow
