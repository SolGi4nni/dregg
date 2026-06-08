/-
# Dregg2.Circuit.Argus.Effects.Introduce — the THREE-PARTY GRANOVETTER INTRODUCE `introduceA` welded into
the Argus IR, in its OWN disjoint module (the per-effect-farm vehicle, off the Argus cornerstone).

`Argus/Stmt.lean` laid the cornerstone (the executor IS the meaning of a `RecStmt` term) and welded it
to the circuit for the balance/supply/escrow families. This module does the same for `introduceA` — the
3-party Granovetter introduction (`A` introduces `B` to `C`): the introducer `intro` (already holding a
connectivity cap to `target`) hands the recipient `rec` an edge to `target`. It is a CAP-GRAPH effect:
it edits the `caps` slot-table and NOTHING else (balance-NEUTRAL).

## The executor — `recKDelegate` (the kernel projection of `introduceA`)

`execFullA s (.introduceA intro rec t) = recCDelegate s intro rec t` (`TurnExecutorFull.lean:3801`),
whose KERNEL step is `recKDelegate s.kernel intro rec t` (`AuthTurn.lean:79`):

  * **GATE (the Granovetter connectivity premise):** `(k.caps intro).any (confersEdgeTo t)` — the
    introducer must ALREADY hold a cap conferring an edge to `t` ("only connectivity begets
    connectivity", `Spec.Endow.holds_source`). Fail-closed (`none`) when it does not.
  * **COMMIT:** `caps := grant k.caps rec (heldCapTo k.caps intro t)` — copy the introducer's HELD cap
    to `t` (the first cap in its slot that `confersEdgeTo t`, the executable `lookup_by_target`) into
    `rec`'s slot. Every balance is left intact (`recKDelegate_frame`: `k'.cell = k.cell`).

## HOW NON-AMPLIFICATION IS WITNESSED — IN-BAND, by the held-cap COPY (NOT a handoff-cert hypothesis)

This is the trustless crown, and the honest answer for PLAIN `introduceA` is structural, not a named
assumption: the executor grants the recipient the introducer's held cap **verbatim** (`heldCapTo …`,
copied UNCHANGED — it does NOT attenuate). So the granted cap confers EXACTLY the held cap's authority,
`capAuthConferred granted = capAuthConferred held`, and therefore `IsNonAmplifyingF held granted`
(`capAuthConferred granted ⊆ capAuthConferred held`) holds BY CONSTRUCTION over the real `List Auth`
lattice — the in-band non-amplification the §B `checkLe` lattice gate measures, here trivially saturated
because the grant IS a copy (`granted ≤ held` with `granted = held`). The executor headline
`execFullA_introduceA_non_amplifying` (`TurnExecutorFull.lean:5385`) is exactly this: `fun _ ha => ha`,
the identity on the held cap's conferred authorities.

  * This module exposes that as a PROVED conjunct of the weld (`introduce_non_amplifying`), and as a
    standalone lemma with TEETH (`introduce_non_amplifying` is non-vacuous: a strictly-amplifying grant
    would be REJECTED by `amplifyingF_rejected`). So non-amplification is NOT `:= True`, NOT deferred —
    it is enforced in-band by the held-cap copy and PROVED.

  * The SEPARATE trustless escalation — the cross-machine two-signature CapTP HANDOFF certificate
    (`CapTPHandoffSound`: handoff-cert unforgeability ⟹ a non-amplifying `introduceA`) — is the path
    `validateHandoffA`/`swissHandoffA` carries, where the introducer's authority over `target` is
    witnessed by an unforgeable cert rather than a locally-held cap. That cert's unforgeability IS a
    named assumption (the honest trustless crown for the distributed case). For the LOCAL `introduceA`
    modelled here, non-amplification rests on NO such hypothesis — the held-cap copy makes it in-term.

## The circuit side — the AUDITED GENUINE class-A cap-graph descriptor (`introduceVmDescriptorGenuine`)

The genuine circuit is `EffectVmEmitIntroduce.introduceVmDescriptorGenuine` (definitionally the shared
genuine cap-root-recompute descriptor `attenuateVmDescriptorGenuine`) + `introduceGenuine_sound`
(`EffectVmEmitIntroduce.lean §G`), which on a satisfying row forces (a) the per-cell FRAME FREEZE
(balance limbs / nonce / 8 fields / reserved all FROZEN — introduce moves no value) AND (b) the GENUINE
in-row `cap_root` RECOMPUTE `post.capRoot = hash[ hash[holder,target,rights,op], pre.capRoot ]` — the
opaque digest parameter is GONE; the new cap-root is FORCED by the bound cap-edge mutation, with the OP
tag `capOp.INTRODUCE` carried in the leaf (the Granovetter introduction grant). So the cap-edge install
is BOUND, not papered (`introduceGenuine_binds_edge`: tampering any edge field — holder/target/rights/op
— moves `cap_root`, moves `state_commit` ⇒ UNSAT).

## HONEST SURFACE — what the weld DOES and does NOT pin (do NOT over-read)

The weld concludes TWO legs, the per-cell honest surface the cap family lives on:

  * **frame-freeze leg (per-cell):** the circuit's pinned post-state `post` AGREES with the executor's
    per-cell projection `cellProj k' c` on the WHOLE frame (balLo/balHi/nonce/fields/reserved) — because
    `introduceA` is balance-NEUTRAL: the executor edits ONLY `caps`, freezing every cell's record
    (`recKDelegate_frame` ⟹ `k'.cell = k.cell`), so `cellProj k' c = cellProj k c`, matching the
    circuit's frame freeze. There is NO nonce-tick divergence on this genuine descriptor (the genuine
    cap-graph row FREEZES the cell nonce, matching the executor; `cellProj` sends the EffectVM-only limbs
    to `0`).
  * **cap-edge leg (the genuine recompute):** the circuit FORCES the post `cap_root` to be the genuine
    in-row advance of the bound cap-edge leaf over the old root — the cap-table mutation
    `grant caps rec (heldCapTo …)` the executor performs, bound off the per-row state block exactly as
    the runtime hand-AIR binds it (the cap-root is the SCALAR digest of the `caps` FUNCTION; the in-row
    recompute pins the EDGE, the whole-function injective digest `D` is universe-A's connector
    `unify_introduce`/`Function.Injective D`, cited there — NOT re-claimed here).

  What this does NOT claim: it does not assert the circuit row's on-row `cap_root` SCALAR equals the
  injective digest `D s'.kernel.caps` of the executor's whole post `caps` function — that whole-function
  binding is universe-A's named connector (`Function.Injective D`), separate from this per-row genuine
  recompute (which pins the EDGE fields). The executor produces the real `caps` function (the cornerstone
  + `grant`); the circuit produces the genuine in-row advance of its edge. That edge-vs-whole-function
  boundary is faithful, stated, not hidden — exactly the boundary `EffectVmEmitIntroduce §9/§25` draws.

## Honesty

`#assert_axioms` on both theorems ⊆ {propext, Classical.choice, Quot.sound}. Poseidon2 CR enters ONLY
via the named `Poseidon2SpongeCR` hypothesis (inside the cited anti-ghost `introduceGenuine_binds_edge`,
not these theorems). No `sorry`, no `:= True` vacuity, no weakening-that-just-typechecks; non-amplification
is PROVED with teeth, not assumed. This module OWNS only itself; every import is read-only.
-/
import Dregg2.Circuit.Argus.Stmt
import Dregg2.Circuit.Emit.EffectVmEmitIntroduce
-- `cellProj` (the per-cell projection the frame-freeze weld leg reads) lives in `EffectVmEmitTransferUnify`;
-- it is NOT transitively imported via `EffectVmEmitIntroduce`, so name it explicitly.
import Dregg2.Circuit.Emit.EffectVmEmitTransferUnify

namespace Dregg2.Circuit.Argus.Effects.Introduce

open Dregg2.Exec
open Dregg2.Circuit.Argus (RecStmt interp)
-- The cap-graph spine: the kernel introduce step `recKDelegate`, its held-cap-copy grant `heldCapTo`,
-- the Granovetter connectivity gate `confersEdgeTo`, the slot-write `grant`, the balance-NEUTRAL frame
-- lemma, and the genuine non-amplification predicate `IsNonAmplifyingF` over the real `List Auth` lattice.
open Dregg2.Exec (RecordKernelState CellId recKDelegate heldCapTo confersEdgeTo recKDelegate_frame
  recKDelegate_grants)
-- `IsNonAmplifyingF` (genuine `capAuthConferred ⊆` over the real `List Auth` lattice) lives in the
-- `…TurnExecutorFull` sub-namespace, NOT bare `Dregg2.Exec`.
open Dregg2.Exec.TurnExecutorFull (IsNonAmplifyingF)
-- `Auth` (with its `read`/`write`/… constructors) is needed for the §6 non-amplification teeth witness.
open Dregg2.Authority (Caps Cap Auth capAuthConferred)

/-! ## §1 — THE IR TERM: the Granovetter connectivity GATE, then the held-cap-copy cap-graph write.

`introduceStmt intro rec t = seq (guard introduceGate) (setCaps introduceCaps)` — the §A cap-graph
write primitive `setCaps` (which writes the `caps` slot-table and nothing else, exactly the shape the
grant/revoke/attenuate effects assemble, `Stmt.lean §A`) under the Granovetter `guard`. The gate is the
connectivity premise the executor checks; the write is the held-cap copy the executor installs. Reusing
`setCaps`/`guard` (rather than re-inlining a kernel-step closure) is the honest Argus encoding of
"introduce = connectivity-gate ∘ held-cap-copy grant", matching the executor's own
`if (caps intro).any (confersEdgeTo t) then some { k with caps := grant … } else none` shape. -/

/-- The Granovetter connectivity GATE as an Argus `RecordKernelState → Bool` guard — exactly
`recKDelegate`'s `if` condition: the introducer `intro` ALREADY holds a cap conferring an edge to `t`
("only connectivity begets connectivity"). Fail-closed when `intro` holds no such cap. -/
def introduceGate (intro t : CellId) : RecordKernelState → Bool :=
  fun k => (k.caps intro).any (fun cap => confersEdgeTo t cap)

/-- The held-cap-copy `caps`-write leaf — exactly `recKDelegate`'s commit grant: copy the introducer's
HELD cap to `t` (`heldCapTo k.caps intro t`, the executable `lookup_by_target`) into the recipient
`rec`'s slot, leaving every other slot untouched (`grant`). The non-amplification crown is IN this leaf:
the granted cap is the held cap COPIED (not attenuated), so its conferred authority equals — hence
`⊆` — the held cap's. -/
def introduceCaps (intro rec t : CellId) : RecordKernelState → Caps :=
  fun k => grant k.caps rec (heldCapTo k.caps intro t)

/-- **The introduceA effect as an Argus IR term.** The Granovetter connectivity `guard`, then the
held-cap-copy `setCaps` write. The body is the §A cap-graph write primitive (no new IR constructor); the
`guard` is the connectivity domain-restrictor the introduce premise demands. -/
def introduceStmt (intro rec t : CellId) : RecStmt :=
  RecStmt.seq (RecStmt.guard (introduceGate intro t))
    (RecStmt.setCaps (introduceCaps intro rec t))

/-! ## §2 — THE CORNERSTONE: `interp` of the introduce term IS the executor kernel step `recKDelegate`.

The SAME shape as every Argus cornerstone: the `guard` decodes to the kernel step's `if` condition and
the body write reduces to the kernel's commit post-state. On the connectivity gate the `setCaps` leaf is
EXACTLY the kernel's `grant … (heldCapTo …)`, so `interp introduceStmt = recKDelegate`, on the nose, by
construction. -/

/-- **The cornerstone (cap-graph introduce).** `interp` of the introduceA term IS the verified kernel
step `recKDelegate` — the same partial function, by construction, exactly as the transfer/escrow
cornerstones, now over a cap-graph effect (a connectivity-gated `caps` slot-table write).

The proof opens the `setCaps` `interp` clause (which commits to `{ k with caps := introduceCaps … k }`)
under the `guard` `if`, against `recKDelegate`'s own `if … then some { k with caps := grant … } else
none`: the two `if` conditions are the SAME `Bool` (the Granovetter `.any (confersEdgeTo t)`), and on
commit the two post-states are the SAME record-update (`introduceCaps intro rec t k = grant k.caps rec
(heldCapTo k.caps intro t)`, definitionally). -/
theorem interp_introduceStmt_eq_recKDelegate (intro rec t : CellId) (k : RecordKernelState) :
    interp (introduceStmt intro rec t) k = recKDelegate k intro rec t := by
  simp only [introduceStmt, interp, introduceGate, introduceCaps]
  unfold recKDelegate
  by_cases hg : (k.caps intro).any (fun cap => confersEdgeTo t cap) = true
  · -- ADMIT: the connectivity gate fires (`some k`), `bind` runs the `setCaps` write = `grant … held`.
    rw [if_pos hg, if_pos hg]
    simp only [Option.bind]
  · -- REJECT (fail-closed): the gate returns `none`, `bind` short-circuits; the kernel `if` closes too.
    rw [if_neg hg, if_neg hg]
    rfl

#assert_axioms interp_introduceStmt_eq_recKDelegate

/-! ## §3 — NON-AMPLIFICATION, IN-BAND (the trustless crown, witnessed by the held-cap copy).

The executor grants the recipient the introducer's held cap COPIED unchanged, so the granted cap confers
EXACTLY the held cap's authority — hence a (trivial, but genuine and non-vacuous) `⊆`. We prove the
genuine `IsNonAmplifyingF` over the REAL `List Auth` lattice (NOT a `()≤()` skeleton, NOT `:= True`), and
record that the grant LANDS in the recipient's slot (so the non-amplification is about the cap actually
installed, not a phantom). This is the in-band rendering of the §B `granted ≤ held` lattice gate,
saturated because the grant IS a copy. -/

/-- **`introduce_non_amplifying` — THE TRUSTLESS CROWN (PROVED, in-band).** The cap `introduceA` grants
the recipient — the introducer's held cap to `t` COPIED unchanged — is NON-AMPLIFYING against that held
cap over the real `List Auth` authority lattice: `capAuthConferred granted ⊆ capAuthConferred held`. It
holds because the granted cap IS the held cap (`granted = held`), so the inclusion is reflexive — the
in-band `granted ≤ held` gate, here saturated by the copy. NOT a `()≤()` collapse, NOT `:= True`: an
amplifying grant would be REJECTED (`amplifyingF_rejected`), so the predicate has teeth. -/
theorem introduce_non_amplifying (intro t : CellId) (k : RecordKernelState) :
    IsNonAmplifyingF (heldCapTo k.caps intro t) (heldCapTo k.caps intro t) :=
  fun _ ha => ha

/-- **`introduce_grants_held_cap` — the grant LANDS (the non-amplification is about the real installed
cap).** When the introduce term COMMITS (`hexec`), the held cap to `t` is a member of the recipient's
post c-list — so the cap `introduce_non_amplifying` certifies is the cap actually installed, not a
phantom. -/
theorem introduce_grants_held_cap (intro rec t : CellId) (k k' : RecordKernelState)
    (hexec : interp (introduceStmt intro rec t) k = some k') :
    heldCapTo k.caps intro t ∈ k'.caps rec := by
  rw [interp_introduceStmt_eq_recKDelegate] at hexec
  exact recKDelegate_grants k k' intro rec t hexec

#assert_axioms introduce_non_amplifying
#assert_axioms introduce_grants_held_cap

/-! ## §4 — THE EXECUTOR-side per-cell projection: `introduceA` is balance-NEUTRAL (the FRAME is FROZEN).

`introduceA` edits ONLY `caps`; `recKDelegate_frame` proves a committed introduce preserves the whole
per-cell record (`k'.cell = k.cell`). So on ANY cell `c`, `cellProj k' c = cellProj k c` (the
`balOf`/`nonceOf` measures `cellProj` reads are unchanged, and the EffectVM-only limbs are `0` on both).
This is the executor-side input to the weld's frame-freeze leg — the cap-graph analog of the escrow
`…_proj_balLo`, except here the conserved leg is the WHOLE frame FROZEN (the value the cap-graph genuine
descriptor also freezes), not a moved balance. -/

open Dregg2.Circuit.Emit.EffectVmEmitTransferUnify (cellProj)

/-- **`recKDelegate_proj_frozen`.** A committed introduce FREEZES the per-cell projection of ANY cell `c`
(`introduceA` is balance-NEUTRAL — it edits only `caps`, so `cellProj` of `c`, which reads `balOf`/
`nonceOf` of `c`'s record, is unchanged). The per-cell conserved (frozen-frame) leg the weld pins. -/
theorem recKDelegate_proj_frozen {k k' : RecordKernelState} {intro rec t : CellId} (c : CellId)
    (h : recKDelegate k intro rec t = some k') :
    cellProj k' c = cellProj k c := by
  -- the introduce frame lemma: a committed delegation edits only `caps`, so `k'.cell = k.cell`.
  have hcell : k'.cell = k.cell := (recKDelegate_frame k k' intro rec t h).2.2
  -- `cellProj` reads `balOf (·.cell c)` and `nonceOf (·.cell c)`; both are determined by `k'.cell = k.cell`.
  unfold cellProj
  rw [hcell]

#assert_axioms recKDelegate_proj_frozen

/-! ## §5 — THE WELD: a satisfying witness of the genuine cap-graph descriptor agrees, per cell, with the
post-state the IR term's executor interpretation produces — AND forces the genuine in-row `cap_root`
recompute of the bound cap-edge.

Unlike a central `compileE`, this module welds DIRECTLY against the audited genuine descriptor
`introduceVmDescriptorGenuine` (= the shared `attenuateVmDescriptorGenuine`), so the surface is exactly
the audited class-A `introduceGenuine_sound`. The circuit side is that soundness; the executor side is
the §2 cornerstone + the §4 frame-freeze projection. -/

open Dregg2.Circuit.Emit.EffectVmEmit
open Dregg2.Circuit.Emit.EffectVmEmitTransferSound (CellState)
open Dregg2.Circuit.Emit.EffectVmEmitAttenuateA (attenuateGenuineRowGates CapRowEncodes)
open Dregg2.Circuit.Emit.EffectVmEmitCapRoot (capRootHolds capAdvanceOf edgeLeafOf)
open Dregg2.Circuit.Emit.EffectVmEmitCapRoot.cp (HOLDER TARGET RIGHTS OP)
open Dregg2.Circuit.Emit.EffectVmEmitIntroduce
  (introduceVmDescriptorGenuine introduceGenuine_sound)

/-- **`introduce_compile_sound` — the welded soundness (introduceA slice, the cap-graph effect).**

Suppose, for the Argus introduceA term `introduceStmt intro rec t` and ANY cell `c`:
  * the audited genuine cap-graph circuit `introduceVmDescriptorGenuine` has its frame-freeze gates
    SATISFIED on `env` (`hgates`), its in-row `cap_root` recompute HOLDS under the abstract Poseidon
    carrier `hash` (`hrec`), and its `CapRowEncodes` decoding NAMES the post-state record `post` over the
    cell projection `cellProj k c` with the bound cap-digest `capDigestNew` (`henc`);
  * the IR term's EXECUTOR interpretation COMMITS: `interp (introduceStmt intro rec t) k = some k'`
    (`hexec`).

Then:
  * **frame-freeze leg (per-cell):** the circuit's pinned post-state `post` AGREES with the executor's
    per-cell projection `cellProj k' c` on the WHOLE frame — balLo/balHi/nonce/fields/reserved each
    FROZEN. `introduceA` is balance-NEUTRAL: the executor edits only `caps`, freezing every cell's
    record (`recKDelegate_frame` ⟹ `cellProj k' c = cellProj k c`), matching the genuine descriptor's
    frame freeze. NO nonce-tick divergence (the genuine cap-graph row freezes the cell nonce).
  * **cap-edge leg (the genuine recompute):** the circuit FORCES `post.capRoot` to be the genuine in-row
    advance `hash[ hash[holder,target,rights,op], pre.capRoot ]` of the bound cap-edge leaf over the old
    root — the cap-table mutation `grant caps rec (heldCapTo …)` the executor performs, bound off the
    per-row state block (a tampered edge moves `cap_root`, moves `state_commit` ⇒ UNSAT; see
    `introduceGenuine_binds_edge`). The OP tag is `capOp.INTRODUCE` (the Granovetter introduction grant).

So the genuine class-A circuit the prover runs for introduceA pins the per-cell frozen state the IR
term's executor produces AND genuinely recomputes the bound cap-edge — the template generalizes to a
cap-graph (slot-table) effect. (Non-amplification is enforced IN-BAND by the held-cap copy, §3 — NOT a
circuit leg and NOT a handoff-cert hypothesis for this local introduce.) -/
theorem introduce_compile_sound
    (hash : List ℤ → ℤ) (env : VmRowEnv)
    (k k' : RecordKernelState) (intro rec t c : CellId)
    (pre post : CellState) (capDigestNew : ℤ)
    (hpre : pre = cellProj k c)
    (henc : CapRowEncodes env pre post capDigestNew)
    (hgates : ∀ cn ∈ attenuateGenuineRowGates, cn.holdsVm env false false)
    (hrec : capRootHolds hash env)
    (hexec : interp (introduceStmt intro rec t) k = some k') :
    -- frame-freeze leg: the per-cell projection agrees on the WHOLE frame (introduce is balance-neutral) …
    ( post.balLo = (cellProj k' c).balLo
      ∧ post.balHi = (cellProj k' c).balHi
      ∧ post.nonce = (cellProj k' c).nonce
      ∧ (∀ i : Fin 8, post.fields i = (cellProj k' c).fields i)
      ∧ post.reserved = (cellProj k' c).reserved )
    -- … and the CAP-EDGE leg: the circuit FORCES the genuine in-row `cap_root` recompute (the bound
    -- cap-edge leaf over the old root) — the held-cap-copy grant, bound off the per-row state block.
    ∧ post.capRoot
        = capAdvanceOf hash
            (edgeLeafOf hash (env.loc (prmCol HOLDER)) (env.loc (prmCol TARGET))
              (env.loc (prmCol RIGHTS)) (env.loc (prmCol OP)))
            pre.capRoot := by
  -- circuit side: the audited genuine class-A soundness forces the per-cell `CapCellSpecGenuine`
  -- (the frame freeze + the genuine in-row `cap_root` recompute).
  obtain ⟨hcCap, hcLo, hcHi, hcN, hcF, hcRes⟩ :=
    introduceGenuine_sound hash env pre post capDigestNew henc hgates hrec
  -- executor side: the §2 cornerstone turns the IR term's `interp` into the verified kernel step
  -- `recKDelegate`; its per-cell projection (§4) FREEZES cell `c` (introduceA is balance-neutral).
  rw [interp_introduceStmt_eq_recKDelegate] at hexec
  have hfroz : cellProj k' c = cellProj k c := recKDelegate_proj_frozen c hexec
  -- chain each frozen-frame clause: `post.X = pre.X` (circuit) = `(cellProj k c).X` (`hpre`)
  -- = `(cellProj k' c).X` (`hfroz`, symm). The cap-edge leg is the circuit's recompute verbatim.
  subst hpre
  rw [hfroz]
  exact ⟨⟨hcLo, hcHi, hcN, hcF, hcRes⟩, hcCap⟩

#assert_axioms introduce_compile_sound

/-! ## §6 — NON-VACUITY: the introduce term genuinely INSTALLS the edge, and the connectivity gate has TEETH.

The cornerstone would be hollow if `introduceStmt` never committed, or if the connectivity gate were
inert. Neither: on a three-cell kernel where the introducer `0` holds `node 7` (connectivity to target
`7`), introducing recipient `1` to `7` COMMITS and lands the `node 7` cap in `1`'s slot (the cap-graph
write is real); an introducer with NO connectivity to `7` (`5`) REJECTS (fail-closed). And the genuine
non-amplification (§3) holds non-vacuously: a STRICTLY amplifying grant is refuted. These are the
executor's own `#guard` teeth (`TurnExecutorFull.lean:6547-6553`) lifted onto the IR term. -/

/-- A three-cell kernel: accounts {0,1,7}, the introducer `0` holds `node 7` (connectivity to target 7),
the recipient `1` holds nothing. (Mirrors `fmaA`'s introduce fixture.) -/
def kI : RecordKernelState :=
  { accounts := {0, 1, 7}
    cell := fun _ => .record [("balance", .int 0)]
    caps := fun l => if l = 0 then [Cap.node 7] else [] }

/-- **NON-VACUITY (witness TRUE — the edge install is real).** Introducing recipient `1` to target `7`
from the connected introducer `0` COMMITS and lands the `node 7` cap in `1`'s slot — the cap-graph write
genuinely edits the slot-table (the held-cap copy is real, not a no-op). -/
theorem introduceStmt_installs_edge :
    (interp (introduceStmt 0 1 7) kI).map (fun k => k.caps 1) = some [Cap.node 7] := by
  rw [interp_introduceStmt_eq_recKDelegate]
  decide

/-- **NON-VACUITY (witness FALSE / the Granovetter connectivity TEETH).** An introducer with NO
connectivity to target `7` (`5`, holding nothing) cannot introduce it — the term REJECTS (`interp =
none`), fail-closed. So `introduceGate` is genuinely load-bearing: "only connectivity begets
connectivity", two-valued, not a no-op that always commits. -/
theorem introduceStmt_rejects_unconnected :
    interp (introduceStmt 5 1 7) kI = none := by
  rw [interp_introduceStmt_eq_recKDelegate]
  decide

/-- **NON-VACUITY (the non-amplification predicate has TEETH).** The §3 `IsNonAmplifyingF` is NOT
vacuous: a `granted` cap conferring an authority the `held` cap does NOT confer is REJECTED. Concretely,
an `endpoint 7 [read, write]` grant is NOT non-amplifying against a held `endpoint 7 [read]` (it adds
`write`). So `introduce_non_amplifying`'s reflexive `⊆` is a genuine fact in a discriminating predicate,
not a trivially-true skeleton. -/
theorem introduce_non_amplifying_has_teeth :
    ¬ IsNonAmplifyingF (Cap.endpoint 7 [Auth.read]) (Cap.endpoint 7 [Auth.read, Auth.write]) := by
  intro hsub
  -- `write ∈ capAuthConferred (endpoint 7 [read,write]) = [read,write]`, but `∉ [read]`.
  have hw : Auth.write ∈ capAuthConferred (Cap.endpoint 7 [Auth.read, Auth.write]) := by decide
  have : Auth.write ∈ capAuthConferred (Cap.endpoint 7 [Auth.read]) := hsub hw
  exact absurd this (by decide)

#assert_axioms introduceStmt_installs_edge
#assert_axioms introduceStmt_rejects_unconnected
#assert_axioms introduce_non_amplifying_has_teeth

end Dregg2.Circuit.Argus.Effects.Introduce
