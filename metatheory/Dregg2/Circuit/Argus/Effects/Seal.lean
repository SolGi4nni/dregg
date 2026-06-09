/-
# Dregg2.Circuit.Argus.Effects.Seal — the SEAL-BOX effect `sealA` welded into the Argus IR.

`Argus/Stmt.lean` laid the cornerstone (the executor IS the meaning of a `RecStmt` term) and validated
it on transfer/mint/burn/createEscrow; `Effects/BalanceA.lean` then welded a per-asset move against the
v2 `Surface2` full-state descriptor. This module welds the genuinely DIFFERENT **capability-routing,
LIST-side-table** primitive `sealA` (the seal-box effect), in a disjoint file (it imports the Argus IR
+ the audited `sealA` v2 instance + the seal-box spec read-only, and owns only its own declarations).

`sealA` is the seal-box constructor of the FULL op-set executor `execFullA`
(`execFullA s (.sealA pid actor payload) = sealChainA s pid actor payload`,
`TurnExecutorFull.lean:3866`). The verified chained kernel mutator is `sealChainA`
(`TurnExecutorFull.lean:1854`):

    sealChainA s pid actor payload
      = if (s.kernel.caps actor).any (holdsSealCapFor pid) = true ∧ payload ∈ s.kernel.caps actor
        then some { kernel := { s.kernel with
                                sealedBoxes := ⟨pid, actor, payload⟩ :: s.kernel.sealedBoxes },
                    log    := ⟨actor, actor, actor, 0⟩ :: s.log }
        else none

so a committed seal PREPENDS one `SealedBoxRecord ⟨pid, actor, payload⟩` onto the holding-store
`sealedBoxes` (the §A `setSealedBoxes` list write — NOT `setCell`/`setBal`), prepends a disclosing
receipt to the log, and freezes the 16 non-`sealedBoxes` kernel fields (INCLUDING `caps` — the sealer's
c-list is unchanged, the cap is COPIED into the box, the FRAME-GAP the spec flags). That is the
structural contrast with every prior weld: transfer/balanceA touch the per-cell/per-asset value tables;
seal touches the `sealedBoxes` LIST side-table via the `setSealedBoxes` primitive, with NO new
constructor needed.

## THE DESCRIPTOR (a FULL-STATE Surface2 weld, the strong surface BalanceA prefers).

`sealA` carries its OWN genuine standalone circuit⟺spec crown jewel in the v2 EffectCommit2 / `Surface2`
universe (`Dregg2/Circuit/Inst/sealA.lean`): `sealE` (the `EffectSpec2` whose touched component is the
WHOLE `sealedBoxes` list, a `listComponent` FULL-list digest — so a drop/reorder of a prior box is
REJECTED, not merely "grew by one") and `sealA_full_sound : satisfiedE2 … (sealE …) … ⟹ SealSpec` — a
FULL 18-component (17 kernel fields + receipt `log`) declarative post-state soundness, whose executor
corner is the independent `execFullA_seal_iff_spec` (`Spec/sealboxoperations.lean`). So — exactly like
BalanceA — this module welds the FULL-STATE `Surface2` `sealA_full_sound` DIRECTLY against the Argus
term, concluding the WHOLE `SealSpec` agreement (strictly stronger than a per-cell EffectVM weld).

The HONEST chained-vs-kernel contrast carried explicitly (the task's `divergence` field, NOT papered):
the Argus `RecStmt`/`interp` runs on the bare `RecordKernelState`, so the cornerstone (§2) pins the
KERNEL fragment of the seal — the `sealedBoxes` prepend — and is then LIFTED (§3) to the chained
`execFullA`/`sealChainA` over `RecChainedState`, where the chained layer adds exactly the **receipt-log
prepend** (`sealReceipt actor :: s.log`). That log-prepend is the kernel-vs-runtime divergence, carried
as an explicit equality leg in the §3 lift (`interp_sealStmt_chained`) — the chained executor's `log`
is the Argus-kernel post plus one disclosing receipt row, exactly as `BalanceA`'s §3 carries the
`acceptsEffects` dst-liveness + the `t :: log` prepend.

## Honesty

`#assert_axioms` on every headline theorem ⊆ {propext, Classical.choice, Quot.sound}; the Poseidon-CR /
list-digest assumptions enter ONLY inside the reused `sealA_full_sound` (its `compressNInjective cN` +
`listLeafInjective LE` + `RestIffNoSealedBoxes`/`logHashInjective` portal hypotheses), not in the welded
conclusion's statement. No `sorry`, no `:= True`, no `native_decide`. Imports are read-only; this file
owns only itself. Build: `lake build Dregg2.Circuit.Argus.Effects.Seal`.
-/
import Dregg2.Circuit.Argus.Stmt
import Dregg2.Circuit.Inst.sealA
import Dregg2.Circuit.Spec.sealboxoperations

namespace Dregg2.Circuit.Argus.Effects.Seal

open Dregg2.Exec
open Dregg2.Exec.TurnExecutorFull
open Dregg2.Circuit.Argus (RecStmt interp)
open Dregg2.Authority (Cap Auth)
-- Broad opens mirroring `Inst/sealA.lean` / `Effects/BalanceA.lean` so the standalone-descriptor names
-- resolve unqualified: `logHashInjective` in `StateCommit`; `Surface2`/`satisfiedE2`/`encodeE2` in
-- `EffectCommit2`; the FULL-state `SealSpec` + executor corner + the box-payload teeth in the seal
-- spec; the v2 `sealA` descriptor (`sealE`/`sealA_full_sound`/`RestIffNoSealedBoxes`/the list carriers)
-- in `Inst.SealA`. (`compressNInjective`/`listLeafInjective` are `StateCommit`/`ListCommit` carriers.)
open Dregg2.Circuit.StateCommit (logHashInjective compressNInjective)
open Dregg2.Circuit.ListCommit (listLeafInjective)
open Dregg2.Circuit.EffectCommit2 (Surface2 satisfiedE2 encodeE2)
open Dregg2.Circuit.Spec.SealBoxOperations
  (SealSpec sealAdmitGuard sealedBoxPrepend sealReceipt execFullA_seal_iff_spec seal_box_binds_payload)
open Dregg2.Circuit.Inst.SealA (SealArgs sealE sealA_full_sound RestIffNoSealedBoxes)

/-! ## §1 — The sealA effect as an Argus IR term (gate, then the `setSealedBoxes` list write).

`sealChainA`'s kernel content is `if <2-conjunct guard> then { k with sealedBoxes := ⟨pid,actor,payload⟩
:: k.sealedBoxes }`. We capture it term-for-term over the bare `RecordKernelState`: a `Bool` `guard` of
the EXACT 2 conjuncts (the actor genuinely HOLDS the sealer cap for `pid` AND HOLDS the `payload` cap it
seals — a confined-cap gate, read off the committed c-list), then a `setSealedBoxes` whose leaf prepends
the box `⟨pid, actor, payload⟩`. The contrast with every prior weld is the move primitive: `setSealedBoxes`
(rewrites the `sealedBoxes` LIST side-table) over the box prepend, NOT `setCell`/`setBal`. -/

/-- The sealA admissibility gate as a `Bool` — exactly `sealChainA`'s `if` (the 2 conjuncts: the actor
HOLDS the sealer cap for `pid`, read off the committed `caps`, AND HOLDS the `payload` cap it is sealing).
This is the kernel-level gate; the chained `sealChainA` over `RecChainedState` checks the SAME conjuncts
(it reads `s.kernel.caps`), so the lift in §3 needs no extra guard leg — only the receipt-log prepend. -/
def sealGuard (pid : Nat) (actor : CellId) (payload : Cap) (k : RecordKernelState) : Bool :=
  (k.caps actor).any (fun c => holdsSealCapFor pid c) && decide (payload ∈ k.caps actor)

/-- The unresolved `SealedBoxRecord` a seal parks — the SAME literal `sealChainA` installs, and the SAME
declarative head `sealedBoxPrepend` names (`Spec/sealboxoperations.lean`). Stated here so the term's
`setSealedBoxes` leaf is the genuine bound box. -/
def boxParked (pid : Nat) (actor : CellId) (payload : Cap) : SealedBoxRecord :=
  { pairId := pid, sealer := actor, payload := payload }

/-- **The sealA effect as an IR term: gate, then the `sealedBoxes` LIST write.** Mirrors the side-table
shape of `createEscrowStmt` (gate, then a component write) but the component is the `sealedBoxes` list
via the §A `setSealedBoxes` primitive — the holding-store prepend — NOT `setBal`/`setEscrows`. The
`setSealedBoxes` leaf is `⟨pid, actor, payload⟩ :: k.sealedBoxes`, EXACTLY the post-`sealedBoxes`
`sealChainA` installs. (The receipt-log prepend `sealChainA` ALSO does lives at the chained layer, off
the bare `RecordKernelState` the IR mutates — carried in §3 as the explicit divergence leg.) -/
def sealStmt (pid : Nat) (actor : CellId) (payload : Cap) : RecStmt :=
  RecStmt.seq (RecStmt.guard (sealGuard pid actor payload))
    (RecStmt.setSealedBoxes (fun k => boxParked pid actor payload :: k.sealedBoxes))

/-! ## §2 — The cornerstone: `interp` of the sealA term IS the KERNEL fragment of `sealChainA`.

The Argus `interp` runs on the bare `RecordKernelState`. `sealChainA`'s kernel post is exactly
`{ k with sealedBoxes := ⟨pid,actor,payload⟩ :: k.sealedBoxes }` under the 2-conjunct guard. We pin that
the IR term commits to PRECISELY that kernel state (or rejects in lock-step). This is the per-asset-style
cornerstone (`interp_balanceAStmt_eq_recKExecAsset`) for the seal-box, over the `sealedBoxes` list. -/

/-- The kernel fragment of a committed `sealChainA`: the `sealedBoxes` prepend on the bare kernel,
nothing else (the 16 non-`sealedBoxes` fields frozen). This is `sealChainA`'s `s.kernel`-post, named
declaratively so the cornerstone target is the genuine kernel move (no `sealChainA` term in the body). -/
def sealKernel (pid : Nat) (actor : CellId) (payload : Cap) (k : RecordKernelState) :
    Option RecordKernelState :=
  if (k.caps actor).any (fun c => holdsSealCapFor pid c) = true ∧ payload ∈ k.caps actor then
    some { k with sealedBoxes := boxParked pid actor payload :: k.sealedBoxes }
  else none

/-- The sealA `Bool` gate decodes to `sealChainA`'s 2-conjunct admissibility proposition (the SAME
conjuncts the kernel `if` checks). The seal analog of `balanceAGuard_iff`. -/
theorem sealGuard_iff (pid : Nat) (actor : CellId) (payload : Cap) (k : RecordKernelState) :
    sealGuard pid actor payload k = true ↔
      ((k.caps actor).any (fun c => holdsSealCapFor pid c) = true ∧ payload ∈ k.caps actor) := by
  simp only [sealGuard, Bool.and_eq_true, decide_eq_true_eq]

/-- **The cornerstone (seal-box, kernel fragment).** `interp` of the sealA term IS the kernel step
`sealKernel` — the same partial function, by construction, exactly as the transfer/balanceA cornerstones,
now over the `sealedBoxes` LIST side-table via `setSealedBoxes`/the box prepend (NOT the per-cell
`setCell`/`setBal`). The executor IS the meaning of the term. -/
theorem interp_sealStmt_eq_sealKernel (pid : Nat) (actor : CellId) (payload : Cap)
    (k : RecordKernelState) :
    interp (sealStmt pid actor payload) k = sealKernel pid actor payload k := by
  simp only [sealStmt, interp]
  unfold sealKernel
  by_cases hg : sealGuard pid actor payload k = true
  · -- ADMIT: the guard's `interp` fires (`some k`); the `setSealedBoxes` write installs the box prepend,
    -- exactly the post-`sealedBoxes` `sealChainA` commits. The RHS `if` opens on the decoded 2-conjunct.
    rw [if_pos hg]
    simp only [Option.bind]
    rw [if_pos ((sealGuard_iff pid actor payload k).mp hg)]
  · -- REJECT: the guard fails ⇒ `none.bind _ = none`; the RHS `if` closes on the (negated) decoded Prop.
    rw [if_neg hg]
    simp only [Option.bind]
    rw [if_neg (fun hp => hg ((sealGuard_iff pid actor payload k).mpr hp))]

#assert_axioms interp_sealStmt_eq_sealKernel

/-! ## §3 — Lifting the cornerstone to the CHAINED executor `sealChainA` / `execFullA`.

The standalone seal descriptor (§4) is keyed on the CHAINED executor `execFullA` / `sealChainA` over
`RecChainedState` (kernel + receipt log) — the arm `execFullA s (.sealA pid actor payload) = sealChainA
s pid actor payload`. The §2 cornerstone is over the bare KERNEL step `sealKernel`. The chained layer is
exactly `sealKernel` PLUS the receipt-log prepend `sealReceipt actor :: s.log` (a `⟨actor,actor,actor,0⟩`
self-disclosing row). We bridge faithfully, CARRYING that log-prepend as an explicit equality leg — the
honest kernel-vs-chained (kernel-vs-runtime) divergence, NOT papered. -/

/-- **`interp_sealStmt_chained` — the IR term's executor, lifted to the chained `execFullA`.** When the
§2 cornerstone commits on the kernel (`interp (sealStmt pid actor payload) st.kernel = some k'`), the
unified action executor `execFullA st (.sealA pid actor payload)` commits to the chained state
`⟨k', sealReceipt actor :: st.log⟩`. So the Argus term's kernel meaning lifts to the chained executor the
standalone descriptor speaks about, with the receipt-log prepend made EXPLICIT — the one place the
chained runtime does more than the bare-kernel Argus term (the carried divergence). -/
theorem interp_sealStmt_chained
    (st : RecChainedState) (pid : Nat) (actor : CellId) (payload : Cap) (k' : RecordKernelState)
    (hexec : interp (sealStmt pid actor payload) st.kernel = some k') :
    execFullA st (.sealA pid actor payload)
      = some { kernel := k', log := sealReceipt actor :: st.log } := by
  -- the §2 cornerstone turns the IR term into the kernel step `sealKernel`.
  rw [interp_sealStmt_eq_sealKernel] at hexec
  -- `execFullA st (.sealA …)` reduces to `sealChainA st …`; unfold both and split on the SAME 2-conjunct
  -- guard. On admit, `sealKernel` named the kernel post as `some k'`, and the chained post adds exactly
  -- the receipt row; on reject both are `none` (contradicting `hexec`).
  show sealChainA st pid actor payload = some { kernel := k', log := sealReceipt actor :: st.log }
  unfold sealChainA sealKernel boxParked at *
  by_cases hg : (st.kernel.caps actor).any (fun c => holdsSealCapFor pid c) = true
      ∧ payload ∈ st.kernel.caps actor
  · rw [if_pos hg] at hexec ⊢
    simp only [Option.some.injEq] at hexec
    -- `hexec : { st.kernel with sealedBoxes := … } = k'`; rewrite the kernel post, the log row is
    -- `sealReceipt actor` by definition (`⟨actor, actor, actor, 0⟩`).
    rw [← hexec]
    rfl
  · rw [if_neg hg] at hexec
    exact absurd hexec (by simp)

#assert_axioms interp_sealStmt_chained

/-! ## §4 — THE COMPILE WELD: a satisfying witness of sealA's OWN standalone circuit agrees with the FULL
post-state the IR term's executor interpretation produces.

This welds against sealA's GENUINE standalone descriptor `sealCircuitStep S (sealE LE cN hN hLE)` (the v2
`Surface2` circuit whose soundness is `sealA_full_sound`), exactly the BalanceA pattern. The executor
side is routed through §3 (`interp` ⟹ `execFullA`) and the independent `execFullA_seal_iff_spec`
(executor ⟺ `SealSpec`); the circuit side is the audited `sealA_full_sound` (circuit ⟹ `SealSpec`). Both
name the SAME `SealSpec`, so they PROVABLY agree on the WHOLE 18-component state (the `sealedBoxes`
prepend + all 16 frozen kernel fields + the receipt log) — strictly stronger than a per-cell weld. -/

/-- The Argus circuit interpretation of a `sealA` term: sealA's OWN audited standalone v2 `Surface2`
circuit step — the full-state arithmetization `satisfiedE2 S (sealE …) (encodeE2 …)` satisfied on the
encoded `(st, args, st')` triple, with `args := ⟨pid, actor, payload⟩` (DEFINITIONALLY the
`EffectRefinement` hub's `effect2CircuitStep`, inlined here so this module imports only `Inst.sealA`).
Its soundness `sealA_full_sound` pins the complete `SealSpec`. The `sealA`-keyed analog of `BalanceA`'s
`balanceACircuit`, in the descriptor universe where sealA carries its OWN genuine full-list-digest
circuit. -/
def sealCircuit (S : Surface2) (LE : SealedBoxRecord → ℤ) (cN : List ℤ → ℤ)
    (hN : compressNInjective cN) (hLE : listLeafInjective LE)
    (st : RecChainedState) (pid : Nat) (actor : CellId) (payload : Cap) (st' : RecChainedState) :
    Prop :=
  satisfiedE2 S (sealE LE cN hN hLE)
    (encodeE2 S (sealE LE cN hN hLE) st ({ pid := pid, actor := actor, payload := payload } : SealArgs) st')

/-- **`sealSpec_unique` — the spec pins a UNIQUE post-state.** Two chained states that BOTH satisfy
`SealSpec st pid actor payload ·` are equal. Rather than re-derive this field-by-field, we route through
the PROVEN executor⟺spec corner `execFullA_seal_iff_spec`: each `SealSpec` reconstructs the SAME committed
value `execFullA st (.sealA pid actor payload) = some ·`, and `some` is injective. This is exactly the
sense in which `SealSpec` is functional — it determines the post-state — so the circuit-side and
executor-side spec facts collapse to one welded post-state. -/
theorem sealSpec_unique {st st₁ st₂ : RecChainedState} {pid : Nat} {actor : CellId} {payload : Cap}
    (h₁ : SealSpec st pid actor payload st₁) (h₂ : SealSpec st pid actor payload st₂) : st₁ = st₂ := by
  have e₁ : execFullA st (.sealA pid actor payload) = some st₁ :=
    (execFullA_seal_iff_spec st pid actor payload st₁).mpr h₁
  have e₂ : execFullA st (.sealA pid actor payload) = some st₂ :=
    (execFullA_seal_iff_spec st pid actor payload st₂).mpr h₂
  exact Option.some.injEq _ _ ▸ (e₁.symm.trans e₂)

/-- **`seal_compile_sound` — the welded soundness (sealA slice), against sealA's OWN descriptor.**

Suppose, for the Argus sealA term `sealStmt pid actor payload`:
  * the standalone sealA circuit `sealCircuit S LE cN hN hLE st pid actor payload st'` (= `sealE`'s
    full-state v2 arithmetization satisfied on the encoded triple) holds, under the realizable
    portals (`hRest : RestIffNoSealedBoxes S.RH` — the `sealedBoxes`-omitting injective rest hash —
    and `hLog : logHashInjective S.LH` — the growing log; the list-component carriers `hN`/`hLE` are
    consumed by `sealE`);
  * the IR term's EXECUTOR interpretation COMMITS on the kernel: `interp (sealStmt pid actor payload)
    st.kernel = some k'` (`hexec`).

Then the chained post-state the circuit pins is EXACTLY the chained post-state the IR term's executor
produces: `st' = { kernel := k', log := sealReceipt actor :: st.log }`. I.e. sealA's OWN circuit and the
IR term AGREE on the WHOLE 18-component state (the `sealedBoxes` head box `⟨pid, actor, payload⟩`, every
other kernel field — INCLUDING `caps`, the copied-not-moved FRAME-GAP — frozen) AND the receipt log
(grown by exactly the `sealReceipt actor` row — the §3 carried kernel-vs-chained divergence). So the
circuit the prover runs for sealA pins the complete state the IR term's executor produces. -/
theorem seal_compile_sound
    (S : Surface2) (LE : SealedBoxRecord → ℤ) (cN : List ℤ → ℤ)
    (hN : compressNInjective cN) (hLE : listLeafInjective LE)
    (hRest : RestIffNoSealedBoxes S.RH) (hLog : logHashInjective S.LH)
    (st st' : RecChainedState) (pid : Nat) (actor : CellId) (payload : Cap) (k' : RecordKernelState)
    (hcirc : sealCircuit S LE cN hN hLE st pid actor payload st')
    (hexec : interp (sealStmt pid actor payload) st.kernel = some k') :
    st' = { kernel := k', log := sealReceipt actor :: st.log } := by
  -- circuit side: sealA's OWN audited soundness forces the FULL `SealSpec` on `(st, ⟨pid,actor,payload⟩, st')`.
  have hspec : SealSpec st pid actor payload st' :=
    sealA_full_sound S LE cN hN hLE hRest hLog st
      ({ pid := pid, actor := actor, payload := payload } : SealArgs) st' hcirc
  -- executor side: the §3 chained lift gives `execFullA st (.sealA …) = some ⟨k', sealReceipt :: log⟩`,
  -- and the independent executor⟺spec corner turns THAT into `SealSpec st pid actor payload ⟨k', …⟩`.
  have hspec' : SealSpec st pid actor payload { kernel := k', log := sealReceipt actor :: st.log } :=
    (execFullA_seal_iff_spec st pid actor payload _).mp
      (interp_sealStmt_chained st pid actor payload k' hexec)
  -- both states satisfy the SAME spec ⇒ they are the same state (the spec pins every kernel field + log).
  exact sealSpec_unique hspec hspec'

#assert_axioms seal_compile_sound

/-! ## §5 — NON-VACUITY: the IR term genuinely SEALS (the box binds the real cap, observable), the welded
circuit's conclusion is the genuine standalone descriptor (the box-payload tooth), and the gate REJECTS
forged inputs (fail-closed on cap-not-held / payload-not-held).

The cornerstone/weld would be hollow if sealA never committed, if the box write were a no-op, or if the
gate admitted everything. A concrete kernel `kS1` (cell 0 holds the sealer cap for pair 5 + a payload cap
`node 42`) exercises a real seal; the rejection lemmas show each guard leg fails closed. -/

/-- A concrete kernel for the witnesses: cells 0 and 1 are live accounts; cell 0 holds the sealer cap for
pair `5` (`sealerCap 5 = endpoint 5 [grant]`) AND a payload `Cap.node 42` (the cap it will seal — you can
only seal a cap you genuinely hold); nobody else holds anything. Empty box store. -/
def kS1 : RecordKernelState :=
  { accounts := {0, 1}
    cell := fun _ => .record [("balance", .int 0)]
    caps := fun l => if l = 0 then [sealerCap 5, Cap.node 42] else [] }

/-- **NON-VACUITY (the SEAL is OBSERVABLE).** A committed seal of `node 42` into pair `5` GROWS the
holding-store from `[]` to length `1` — the `setSealedBoxes` write genuinely touches the `sealedBoxes`
list side-table (the prepend is real, not a no-op). -/
theorem sealStmt_parks :
    (interp (sealStmt 5 0 (Cap.node 42)) kS1).map (fun k => k.sealedBoxes.length) = some 1 := by
  rw [interp_sealStmt_eq_sealKernel]
  decide

/-- **NON-VACUITY (the box BINDS the REAL cap).** The committed seal's HEAD box binds EXACTLY the sealed
`payload` (`node 42`, keyed by pair `5`, sealed by cell `0`) — the box carries a genuine capability, not
a flag (the cap `unseal` will recover and grant). This is the kernel-level shadow of the spec's
`seal_box_binds_payload` tooth, exhibited directly on the Argus term. -/
theorem sealStmt_box_binds_payload :
    (interp (sealStmt 5 0 (Cap.node 42)) kS1).map (fun k => k.sealedBoxes.head?)
      = some (some { pairId := 5, sealer := 0, payload := Cap.node 42 }) := by
  rw [interp_sealStmt_eq_sealKernel]
  decide

/-- **NON-VACUITY (the FRAME-GAP, observable).** The committed seal leaves the sealer's own c-list
UNCHANGED — cell `0` still holds `node 42` after sealing it (the cap is COPIED into the box, not moved
out of `caps`). The `setSealedBoxes` write touches ONLY `sealedBoxes`, confirming the spec's
`seal_preserves_caps` frame on the Argus term (the copied-not-moved double-spend surface, made concrete). -/
theorem sealStmt_preserves_sealer_caps :
    (interp (sealStmt 5 0 (Cap.node 42)) kS1).map (fun k => (k.caps 0).contains (Cap.node 42))
      = some true := by
  rw [interp_sealStmt_eq_sealKernel]
  decide

/-- **NON-VACUITY (fail-closed: sealer cap not held).** Sealing under a pair the actor holds NO sealer
cap for (here cell `1`, which holds nothing) does NOT commit — the term returns `none` (the held-sealer-cap
leg fails). No box is created. -/
theorem sealStmt_rejects_no_seal_cap :
    interp (sealStmt 5 1 (Cap.node 42)) kS1 = none := by
  rw [interp_sealStmt_eq_sealKernel]
  decide

/-- **NON-VACUITY (fail-closed: payload not held).** Sealing a cap the actor does NOT hold (here cell `0`
sealing `node 999`, which it never holds) does NOT commit — the held-payload leg fails. You cannot seal a
capability you do not possess; the box payload stays a confined held cap. -/
theorem sealStmt_rejects_unheld_payload :
    interp (sealStmt 5 0 (Cap.node 999)) kS1 = none := by
  rw [interp_sealStmt_eq_sealKernel]
  decide

#assert_axioms sealStmt_parks
#assert_axioms sealStmt_box_binds_payload
#assert_axioms sealStmt_preserves_sealer_caps
#assert_axioms sealStmt_rejects_no_seal_cap
#assert_axioms sealStmt_rejects_unheld_payload

end Dregg2.Circuit.Argus.Effects.Seal
