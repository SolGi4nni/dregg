/-
# Dregg2.Circuit.Argus.Effects.Unseal — the SEAL-BOX UNSEAL effect `unsealA` welded into the Argus IR.

`Argus/Stmt.lean` laid the cornerstone (the executor IS the meaning of a `RecStmt` term) and validated
it on transfer/mint/burn/createEscrow; `Effects/BalanceA.lean` lifted the template to a FULL-STATE
`Surface2` weld concluding the WHOLE 17-field post-state. This module welds the genuinely DIFFERENT
CAPABILITY-MOVE effect `unsealA` (the cap-recovering arm of the seal-box family), in a disjoint file (it
imports the Argus IR + the audited seal-box-operations spec + the v2 `unsealA` instance read-only and
owns only its own declarations).

`unsealA` opens the sealed box bound for `pid` and GRANTS the recovered `box.payload` cap into
`recipient`'s c-list. The verified executor is the CHAINED mutator `unsealChainA`
(`TurnExecutorFull.lean:1869`), reached as the `.unsealA` arm of the full op-set executor
(`execFullA s (.unsealA pid actor recipient) = unsealChainA s pid actor recipient`, by `rfl`):

    unsealChainA s pid actor recipient
      = if (s.kernel.caps actor).any (holdsSealCapFor pid) = true then
          match findSealedBox s.kernel.sealedBoxes pid with
          | some box => some { kernel := { s.kernel with caps := grant s.kernel.caps recipient box.payload },
                               log    := ⟨actor, recipient, recipient, 0⟩ :: s.log }
          | none     => none
        else none

so a committed unseal writes ONE kernel component — the cap table `caps` (`grant box.payload` to
`recipient`) — prepends an `unsealReceipt` to the log, and FREEZES the 16 non-`caps` kernel fields
(INCLUDING `sealedBoxes` — the box is NOT consumed). Because it touches `caps`, the IR body's move is
the §A `setCaps` primitive (the SAME primitive grant/attenuate effects emit) — NOT `setCell`/`setBal`.

## TWO STRUCTURAL FACTS this effect exercises (read these — they are the honest surface).

  1. **NO RAW-KERNEL STEP.** Unlike transfer/mint/burn/createEscrow (each has a
     `RecordKernelState → Option RecordKernelState` raw-kernel step the Argus cornerstone refines), the
     ONLY executor for unseal is the CHAINED `unsealChainA` over `RecChainedState` (kernel + receipt log)
     — the bare-kernel layer never defined an `unsealK`. So the Argus `RecStmt` term (which produces a
     `RecordKernelState`, no log) captures the KERNEL PROJECTION of `unsealChainA`, and the chained lift
     `interp_unsealStmt_chained` carries the `unsealReceipt` log-prepend as the EXPLICIT kernel-vs-runtime
     divergence (exactly as `BalanceA.interp_balanceAStmt_chained` carries the chained layer's extras).
     This is the genuine divergence, carried not papered: the IR term builds the post-`caps` kernel; the
     runtime ALSO prepends the receipt row.

  2. **THE BOX IS AN ARGUMENT.** The box's identity feeds BOTH the guard (existential `findSealedBox … =
     some box`) and the post-`caps` (`grant … box.payload`), so — exactly as `Inst/unsealA.lean`'s
     `UnsealArgs` and `Spec.SealBoxOperations.UnsealSpec` are parametrized by `box` — the IR term and the
     weld carry `box` with the `hbox : findSealedBox k.sealedBoxes pid = some box` hypothesis the spec
     corner `execFullA_unseal_iff_spec` itself requires. The `setCaps` leaf grants `box.payload`; on the
     no-box branch the guard already rejects, so the payload is never read off a missing box.

## THE WELD SURFACE — FULL-STATE `Surface2` (the stronger surface, like BalanceA).

`unsealA` carries its OWN standalone full-state circuit⟺spec crown jewel: `unsealE` (the `EffectSpec2`
whose touched component is the WHOLE `caps` function, a `funcComponent` full-function digest) and
`unsealA_full_sound : satisfiedE2 … (unsealE D hD) … ⟹ UnsealSpec` (`Inst/unsealA.lean`), a FULL 18-field
declarative post-state soundness (all 17 kernel fields + the receipt log), keyed on the CHAINED executor
via the independent `execFullA_unseal_iff_spec` (`Spec/sealboxoperations.lean`). So this module is the
FULL-STATE weld (PREFER per the task brief), NOT the per-cell EffectVM one:

  (1) **Cornerstone (executor-refinement, kernel):** `interp_unsealStmt_eq_unsealChainA_kernel` — the IR
      term's `interp` IS the kernel `unsealChainA` commits, using `setCaps`/`grant`. New, standalone.

  (2) **Chained lift:** `interp_unsealStmt_chained` — given the box found and the guard, the IR term's
      kernel meaning lifts to `execFullA st (.unsealA …) = some ⟨k', unsealReceipt :: st.log⟩` (the
      log-prepend carried explicitly).

  (3) **Compile weld against unsealA's OWN standalone descriptor:** `unseal_compile_sound` welds the
      audited `unsealA_full_sound` (circuit ⟹ `UnsealSpec`) DIRECTLY against the IR term, routing the
      executor side through (2) + `execFullA_unseal_iff_spec` (executor ⟺ `UnsealSpec`). Both name the
      SAME `UnsealSpec`, so they PROVABLY agree on the WHOLE 18-component post-state — strictly stronger
      than a per-cell weld.

## Honesty

`#assert_axioms` on every headline theorem ⊆ {propext, Classical.choice, Quot.sound}; the Poseidon-CR /
whole-function-digest assumption enters ONLY inside the reused `unsealA_full_sound` (its
`Function.Injective D` hypothesis), not in the welded conclusion's statement. No `sorry`, no `:= True`,
no `native_decide`. Imports are read-only; this file owns only itself.
-/
import Dregg2.Circuit.Argus.Stmt
import Dregg2.Circuit.Inst.unsealA

namespace Dregg2.Circuit.Argus.Effects.Unseal

open Dregg2.Exec
open Dregg2.Exec.TurnExecutorFull
open Dregg2.Circuit.Argus (RecStmt interp)
open Dregg2.Authority (Caps Cap)
-- The audited standalone full-state descriptor for `unsealA` (the v2 `Surface2` one) and its spec corner:
open Dregg2.Circuit.StateCommit (logHashInjective)
open Dregg2.Circuit.EffectCommit2 (Surface2 satisfiedE2 encodeE2)
open Dregg2.Circuit.Spec.SealBoxOperations
  (UnsealSpec unsealAdmitGuard grantedCaps unsealReceipt execFullA_unseal_iff_spec
   unseal_grants_sealed_cap unseal_preserves_box_store)
open Dregg2.Circuit.Inst.UnsealA (UnsealArgs RestIffNoCaps unsealE unsealA_full_sound)

/-! ## §1 — The unseal effect as an Argus IR term (gate, then the `setCaps` cap-grant).

`unsealChainA`'s kernel commit is `{ k with caps := grant k.caps recipient box.payload }` under the
guard `(k.caps actor).any (holdsSealCapFor pid) = true ∧ findSealedBox k.sealedBoxes pid = some box`.
We capture it term-for-term: a `Bool` `guard` of the EXACT two conjuncts (held-unsealer-cap ∧
box-exists), then a `setCaps` whose leaf is `grant k.caps recipient box.payload`. The contrast with
transfer/balanceA is the move primitive: `setCaps` (rewrites the WHOLE cap table) over `grant`, NOT
`setCell`/`setBal` over a balance move. -/

/-- The unseal admissibility gate as a `Bool` — exactly `unsealChainA`'s `if` PLUS the `findSealedBox`
match arm, decoded over the carried `box`: the actor genuinely HOLDS the unsealer cap for `pid`
(`holdsSealCapFor`, read off the COMMITTED c-list, adversary-uncontrollable) AND the box bound under
`pid` is `box` (`findSealedBox … = some box`). This is `unsealAdmitGuard`'s two conjuncts as a `Bool`. -/
def unsealGuard (pid : Nat) (actor : CellId) (box : SealedBoxRecord) (k : RecordKernelState) : Bool :=
  (k.caps actor).any (fun c => holdsSealCapFor pid c)
    && decide (findSealedBox k.sealedBoxes pid = some box)

/-- **The unseal effect as an IR term: gate, then GRANT the recovered cap.** Mirrors `balanceAStmt`
(gate, then move) but the move is `setCaps` over `grant` — the recovered `box.payload` cap prepended to
`recipient`'s c-list slot, every other holder verbatim — NOT a balance move. The `setCaps` leaf is
`grant k.caps recipient box.payload`, EXACTLY the post-cap-table `unsealChainA` installs. The box is
carried as an argument (it feeds both the guard's existential and this leaf), as in `UnsealArgs`. -/
def unsealStmt (pid : Nat) (actor recipient : CellId) (box : SealedBoxRecord) : RecStmt :=
  RecStmt.seq (RecStmt.guard (unsealGuard pid actor box))
    (RecStmt.setCaps (fun k => grant k.caps recipient box.payload))

/-! ## §2 — The cornerstone: `interp` of the unseal term IS the KERNEL `unsealChainA` commits. -/

/-- The unseal `Bool` gate decodes to `unsealAdmitGuard`'s admissibility proposition (the two conjuncts:
held-unsealer-cap ∧ box-exists), against the carried `box`. The seal-box analog of `balanceAGuard_iff`. -/
theorem unsealGuard_iff (pid : Nat) (actor : CellId) (box : SealedBoxRecord) (k : RecordKernelState) :
    unsealGuard pid actor box k = true ↔
      ((k.caps actor).any (fun c => holdsSealCapFor pid c) = true
        ∧ findSealedBox k.sealedBoxes pid = some box) := by
  simp only [unsealGuard, Bool.and_eq_true, decide_eq_true_eq]

/-- **The cornerstone (cap-table kernel).** `interp` of the unseal term IS the KERNEL `unsealChainA`
commits — `some { k with caps := grant k.caps recipient box.payload }` exactly when the guard admits, and
`none` exactly when it rejects — by construction, exactly as the transfer/balanceA cornerstones, now over
the whole cap table via `setCaps`/`grant` (NOT a balance move). This is the per-effect executor-refinement
at the kernel layer: the IR term IS the meaning of the executor's kernel commit. The chained `unsealChainA`
ALSO prepends the receipt log (the runtime divergence) — lifted in §3. -/
theorem interp_unsealStmt_eq_unsealChainA_kernel (pid : Nat) (actor recipient : CellId)
    (box : SealedBoxRecord) (k : RecordKernelState) :
    interp (unsealStmt pid actor recipient box) k
      = if (k.caps actor).any (fun c => holdsSealCapFor pid c) = true
            ∧ findSealedBox k.sealedBoxes pid = some box
          then some { k with caps := grant k.caps recipient box.payload }
          else none := by
  simp only [unsealStmt, interp]
  by_cases hg : unsealGuard pid actor box k = true
  · -- ADMIT: the guard's `interp` fires (`some k`); the `setCaps` move installs `grant … box.payload`,
    -- exactly the post-cap-table `unsealChainA` commits. The RHS `if` opens on the decoded conjunction.
    rw [if_pos hg]
    simp only [Option.bind]
    rw [if_pos ((unsealGuard_iff pid actor box k).mp hg)]
  · -- REJECT: the guard fails ⇒ `none.bind _ = none`; the RHS `if` closes on the (negated) conjunction.
    rw [if_neg hg]
    simp only [Option.bind]
    rw [if_neg (fun hp => hg ((unsealGuard_iff pid actor box k).mpr hp))]

#assert_axioms interp_unsealStmt_eq_unsealChainA_kernel

/-! ## §3 — Lifting the cornerstone to the CHAINED executor `unsealChainA` / `execFullA`.

The standalone unseal descriptor (§4) is keyed on the CHAINED executor `execFullA` / `unsealChainA` over
`RecChainedState` (kernel + receipt log) — the arm `execFullA s (.unsealA pid actor recipient) =
unsealChainA s pid actor recipient`. The §2 cornerstone is over the KERNEL commit. The chained layer is
exactly that kernel commit PLUS the receipt-log prepend `unsealReceipt actor recipient :: s.log`. We
bridge faithfully, carrying the box-found hypothesis (the existential the guard decodes against) — the
log-prepend is the EXPLICIT kernel-vs-runtime divergence, NOT papered. -/

/-- **`interp_unsealStmt_chained` — the IR term's executor, lifted to the chained `execFullA`.** When the
box bound under `pid` is `box` (`hbox`, the existential the guard decodes against) and the §2 cornerstone
commits on the kernel (`interp (unsealStmt …) st.kernel = some k'`), the unified action executor
`execFullA st (.unsealA pid actor recipient)` commits to the chained state `⟨k', unsealReceipt actor
recipient :: st.log⟩`. So the Argus term's kernel meaning lifts to the chained executor the standalone
descriptor speaks about, with the receipt-log prepend (the runtime layer's addition over the bare kernel)
carried EXPLICITLY in the post-state — the honest kernel-vs-runtime divergence. -/
theorem interp_unsealStmt_chained
    (st : RecChainedState) (pid : Nat) (actor recipient : CellId) (box : SealedBoxRecord)
    (k' : RecordKernelState)
    (hbox : findSealedBox st.kernel.sealedBoxes pid = some box)
    (hexec : interp (unsealStmt pid actor recipient box) st.kernel = some k') :
    execFullA st (.unsealA pid actor recipient)
      = some { kernel := k', log := unsealReceipt actor recipient :: st.log } := by
  -- the §2 cornerstone turns the IR term into the kernel commit; the box-found hyp resolves the `if`.
  rw [interp_unsealStmt_eq_unsealChainA_kernel] at hexec
  -- `execFullA st (.unsealA …)` reduces to `unsealChainA st pid actor recipient`.
  show unsealChainA st pid actor recipient = some { kernel := k', log := unsealReceipt actor recipient :: st.log }
  unfold unsealChainA
  by_cases hg : (st.kernel.caps actor).any (fun c => holdsSealCapFor pid c) = true
  · -- the guard's held-cap conjunct holds AND the box is `box`; both `if`/`match` open, and `hexec`
    -- (now `if <conj> then some {…caps…} else none = some k'`, with the conjunction TRUE) names `k'`.
    rw [if_pos hg, hbox]
    rw [if_pos ⟨hg, hbox⟩] at hexec
    simp only [Option.some.injEq] at hexec
    subst hexec
    rfl
  · -- held-cap conjunct fails ⇒ the kernel `if` is FALSE, so `hexec : none = some k'` is absurd.
    rw [if_neg (fun hc => hg hc.1)] at hexec
    exact absurd hexec (by simp)

#assert_axioms interp_unsealStmt_chained

/-! ## §4 — THE COMPILE WELD: a satisfying witness of unsealA's OWN standalone circuit agrees with the
FULL post-state the IR term's executor interpretation produces.

This welds against unsealA's GENUINE standalone descriptor `unsealCircuitStep S (unsealE D hD)` (the v2
`Surface2` circuit whose soundness is `unsealA_full_sound`), NOT a per-cell EffectVM row — see the
descriptor investigation in this file's header. The executor side is routed through §3 (`interp` ⟹
`execFullA`) and the independent `execFullA_unseal_iff_spec` (executor ⟺ `UnsealSpec`); the circuit side
is the audited `unsealA_full_sound` (circuit ⟹ `UnsealSpec`). Both name the SAME `UnsealSpec`, so they
PROVABLY agree on the WHOLE 18-component state (all 17 kernel fields + the receipt log) — strictly
stronger than a per-cell weld. -/

/-- The Argus circuit interpretation of an `unsealA` term: unsealA's OWN audited standalone v2 `Surface2`
circuit step — the full-state arithmetization `satisfiedE2 S (unsealE D hD) (encodeE2 …)` satisfied on
the encoded `(st, args, st')` triple (DEFINITIONALLY the `EffectRefinement` hub's
`effect2CircuitStep S (unsealE D hD) st args st'`, inlined here so this module imports only `Inst.unsealA`).
Its soundness `unsealA_full_sound` pins the complete `UnsealSpec`. The `unsealA`-keyed analog of
`BalanceA.balanceACircuit`, in the descriptor universe where unsealA carries its OWN genuine full-state
circuit (the cap-table whole-function digest). -/
def unsealCircuit (S : Surface2) (D : Caps → ℤ) (hD : Function.Injective D)
    (st : RecChainedState) (args : UnsealArgs) (st' : RecChainedState) : Prop :=
  satisfiedE2 S (unsealE D hD) (encodeE2 S (unsealE D hD) st args st')

/-- **`unsealSpec_unique` — the spec pins a UNIQUE post-state.** Two chained states that BOTH satisfy
`UnsealSpec st pid actor recipient box ·` are equal. Rather than re-derive this field-by-field, we route
through the PROVEN executor⟺spec corner `execFullA_unseal_iff_spec` (against the box found, `hbox`): each
`UnsealSpec` reconstructs the SAME committed value `execFullA st (.unsealA pid actor recipient) = some ·`,
and `some` is injective. This is exactly the sense in which `UnsealSpec` is functional — it determines the
post-state — so the circuit-side and executor-side spec facts collapse to one welded post-state. -/
theorem unsealSpec_unique {st st₁ st₂ : RecChainedState} {pid : Nat} {actor recipient : CellId}
    {box : SealedBoxRecord} (hbox : findSealedBox st.kernel.sealedBoxes pid = some box)
    (h₁ : UnsealSpec st pid actor recipient box st₁) (h₂ : UnsealSpec st pid actor recipient box st₂) :
    st₁ = st₂ := by
  have e₁ : execFullA st (.unsealA pid actor recipient) = some st₁ :=
    (execFullA_unseal_iff_spec st pid actor recipient box st₁ hbox).mpr h₁
  have e₂ : execFullA st (.unsealA pid actor recipient) = some st₂ :=
    (execFullA_unseal_iff_spec st pid actor recipient box st₂ hbox).mpr h₂
  exact Option.some.injEq _ _ ▸ (e₁.symm.trans e₂)

/-- **`unseal_compile_sound` — the welded soundness (unseal slice), against unsealA's OWN descriptor.**

Suppose, for the Argus unseal term `unsealStmt pid actor recipient box`:
  * the standalone unseal circuit `unsealCircuit S D hD st ⟨pid, actor, recipient, box⟩ st'` (= `unsealE`'s
    full-state v2 arithmetization satisfied on the encoded triple) holds, under the realizable
    whole-function digest portals (`hRest : RestIffNoCaps S.RH`, `hLog : logHashInjective S.LH`,
    `hD : Function.Injective D`);
  * the box bound under `pid` is `box` (`hbox`, the existential the guard decodes against);
  * the IR term's EXECUTOR interpretation COMMITS on the kernel:
    `interp (unsealStmt pid actor recipient box) st.kernel = some k'` (`hexec`).

Then the chained post-state the circuit pins is EXACTLY the chained post-state the IR term's executor
produces: `st' = { kernel := k', log := unsealReceipt actor recipient :: st.log }`. I.e. unsealA's OWN
circuit and the IR term AGREE on the WHOLE 17-field RecordKernelState (`caps` granted `box.payload` to
`recipient`, every other field frozen — INCLUDING `sealedBoxes`, the box not consumed) AND the receipt
log — the full `UnsealSpec`, not a per-cell projection. So the circuit the prover runs for unseal pins the
complete state the IR term's executor produces, with the receipt-log prepend (the runtime divergence)
explicit in the agreed post-state. -/
theorem unseal_compile_sound
    (S : Surface2) (D : Caps → ℤ) (hD : Function.Injective D)
    (hRest : RestIffNoCaps S.RH) (hLog : logHashInjective S.LH)
    (st st' : RecChainedState) (pid : Nat) (actor recipient : CellId) (box : SealedBoxRecord)
    (k' : RecordKernelState)
    (hcirc : unsealCircuit S D hD st ⟨pid, actor, recipient, box⟩ st')
    (hbox : findSealedBox st.kernel.sealedBoxes pid = some box)
    (hexec : interp (unsealStmt pid actor recipient box) st.kernel = some k') :
    st' = { kernel := k', log := unsealReceipt actor recipient :: st.log } := by
  -- circuit side: unsealA's OWN audited soundness forces the FULL `UnsealSpec` on `(st, args, st')`.
  have hspec : UnsealSpec st pid actor recipient box st' :=
    unsealA_full_sound S D hD hRest hLog st ⟨pid, actor, recipient, box⟩ st' hcirc
  -- executor side: the §3 chained lift gives `execFullA st (.unsealA …) = some ⟨k', unsealReceipt :: log⟩`,
  -- and the independent executor⟺spec corner turns THAT into `UnsealSpec st … ⟨k', unsealReceipt :: log⟩`.
  have hspec' : UnsealSpec st pid actor recipient box { kernel := k', log := unsealReceipt actor recipient :: st.log } :=
    (execFullA_unseal_iff_spec st pid actor recipient box _ hbox).mp
      (interp_unsealStmt_chained st pid actor recipient box k' hbox hexec)
  -- both states satisfy the SAME spec ⇒ they are the same state (the spec pins every kernel field + log).
  exact unsealSpec_unique hbox hspec hspec'

#assert_axioms unseal_compile_sound

/-! ## §5 — NON-VACUITY: the IR term genuinely GRANTS the cap (cap-movement observable), the welded
circuit is the genuine standalone descriptor (not a placeholder), and the gate REJECTS forged inputs
(fail-closed).

The cornerstone/weld would be hollow if unseal never committed, if the grant were a no-op, or if the
gate admitted everything. A concrete kernel `kU0` (cells 0,1,2 live; cell 0 holds the unsealer cap for
pair 5; a box under pid 5 binds payload `Cap.node 42`) exercises a real cap-grant; the rejection lemmas
show each guard leg fails closed. -/

/-- A concrete kernel for the witnesses: cells 0,1,2 are live accounts (lifecycle defaults Live), cell 0
holds the unsealer cap for pair `5` (`unsealerCap 5 = endpoint 5 [reply]`, which `holdsSealCapFor 5`
accepts), and the holding-store binds ONE box under pid `5` carrying payload `Cap.node 42`. Cell 1 holds
no cap (it will RECEIVE the unsealed payload); cell 2 holds nothing (its unseal attempt fails closed). -/
def kU0 : RecordKernelState :=
  { accounts := {0, 1, 2}
    cell := fun _ => .record [("balance", .int 0)]
    caps := fun c => if c = 0 then [unsealerCap 5] else []
    sealedBoxes := [{ pairId := 5, sealer := 0, payload := Cap.node 42 }] }

/-- The box the store binds under pid `5` (the witness box). -/
def boxU0 : SealedBoxRecord := { pairId := 5, sealer := 0, payload := Cap.node 42 }

/-- `findSealedBox` finds `boxU0` under pid `5` in `kU0` (so the carried `box` is genuinely the bound one). -/
theorem kU0_finds_box : findSealedBox kU0.sealedBoxes 5 = some boxU0 := by decide

/-- **NON-VACUITY (the cap-GRANT is OBSERVABLE).** The committed unseal (actor 0, recipient 1) lands the
box's `Cap.node 42` payload in cell `1`'s c-list — the value genuinely ARRIVES at the recipient (the
`setCaps`/`grant` move is real, not a no-op). Cell 1 held NO cap before. -/
theorem unsealStmt_grants_cap :
    (interp (unsealStmt 5 0 1 boxU0) kU0).map (fun k => (k.caps 1).contains (Cap.node 42)) = some true := by
  rw [interp_unsealStmt_eq_unsealChainA_kernel]
  decide

/-- **NON-VACUITY (the box is NOT consumed — the proven frame-gap).** After the unseal, the holding-store
still binds the box under pid `5` (`sealedBoxes` frozen) — the box may be unsealed REPEATEDLY. This is the
`UnsealSpec`/`unseal_preserves_box_store` frame fact, exhibited on the IR term's kernel. -/
theorem unsealStmt_preserves_box :
    (interp (unsealStmt 5 0 1 boxU0) kU0).map (fun k => findSealedBox k.sealedBoxes 5) = some (some boxU0) := by
  rw [interp_unsealStmt_eq_unsealChainA_kernel]
  decide

/-- **NON-VACUITY (other holders untouched).** A holder other than the recipient — cell `2` — keeps its
(empty) c-list verbatim across the unseal: only the recipient's slot grows. The `grant` writes ONLY
`recipient`'s slot. -/
theorem unsealStmt_preserves_other_holder :
    (interp (unsealStmt 5 0 1 boxU0) kU0).map (fun k => k.caps 2) = some [] := by
  rw [interp_unsealStmt_eq_unsealChainA_kernel]
  decide

/-- **NON-VACUITY (fail-closed: cap-not-held).** An unseal whose ACTOR (cell `2`) does NOT hold the
unsealer cap for pair `5` does NOT commit — the term returns `none` (the held-unsealer-cap leg of the
guard fails). No cap is conjured. -/
theorem unsealStmt_rejects_cap_not_held :
    interp (unsealStmt 5 2 1 boxU0) kU0 = none := by
  rw [interp_unsealStmt_eq_unsealChainA_kernel]
  decide

/-- **NON-VACUITY (fail-closed: absent box).** An unseal of a pair (`99`) with NO box in the holding-store
does NOT commit — the term returns `none` (the box-exists leg of the guard fails: `findSealedBox … = some
boxU0` is false when nothing is bound under `99`). The cap must genuinely have been sealed first. -/
theorem unsealStmt_rejects_absent_box :
    interp (unsealStmt 99 0 1 boxU0) kU0 = none := by
  rw [interp_unsealStmt_eq_unsealChainA_kernel]
  decide

#assert_axioms kU0_finds_box
#assert_axioms unsealStmt_grants_cap
#assert_axioms unsealStmt_preserves_box
#assert_axioms unsealStmt_preserves_other_holder
#assert_axioms unsealStmt_rejects_cap_not_held
#assert_axioms unsealStmt_rejects_absent_box

end Dregg2.Circuit.Argus.Effects.Unseal
