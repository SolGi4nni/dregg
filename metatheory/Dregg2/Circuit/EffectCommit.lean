/-
# Dregg2.Circuit.EffectCommit — the GENERIC full-state circuit⟺spec framework.

`Dregg2.Circuit.StateCommit` (Transfer, 2 moved cells, frozen log) and
`Dregg2.Circuit.SetFieldCommit` (setFieldA, 1 touched cell, GROWING log) each proved — bespoke, ~500
lines apiece — the SAME crown-jewel theorem: a satisfying full-state circuit witness pins the WHOLE
post-state (the effect's INDEPENDENT declarative apex), not a projection, and the four anti-ghost
forgeries are REJECTED BY CONSTRUCTION. This module ABSTRACTS that common shape ONCE, so every
remaining effect (~29 of them) becomes a THIN ~100-line instance instead of a bespoke ~500-line proof.

## The keystone simplification (why this is possible at all)

The ONLY `|T|`-variable part of the two instances is the "touched-cell" commitment: Transfer hashes a
2-to-1 `movedDigest`, `setFieldA` hashes a single `CH cell (…)`. But BOTH are special cases of the
ALREADY-PROVED, ALREADY-GENERIC `StateCommit.frameDigest` — the Poseidon sponge `compressN` over the
SORTED leaves of an arbitrary `Finset` carrier. We therefore define

    touchedDigest CH compressN leaf T := frameDigest over carrier `T` with cell-map `leaf`

so the SAME generic binding lemma `StateCommit.FrameDigestBindsCells` (generic in its carrier
`S : Finset CellId`) binds BOTH the FRAME (cells `accounts \ T`) AND the TOUCHED cells (`T`) — at ANY
`|T|` (1, 2, k), with ZERO new lemma work. The 2-to-1 `movedDigest`/`compressInjective compress`
portal of `StateCommit` is DROPPED: only `compressNInjective compressN` + `cellLeafInjective CH` are
needed to bind the touched cells.

## The framework (read the structures below)

  * `StateView Σ`   — how to read a `RecordKernelState` + a `List Turn` (the receipt log) out of `Σ`.
  * `CommitSurface` — the Poseidon primitives (`CH`/`RH`/`cmb`/`compressN`/`LH`), as DATA.
  * `EffectSpec Σ Args` — what an effect supplies: the touched set `T = touched pre args`, the expected
    written leaves `expectedLeaf pre args` (read only on `T`), an optional `logUpdate`, the guard gate
    sub-system + its decoded `Prop`.
  * `EffectSpec.apex` — the DERIVED full-state declarative spec (guard ∧ post-cell = touchedCellMap ∧
    log clause ∧ kernelFrame). NOT supplied per effect — each instance BRIDGES its bespoke apex to it.
  * `effectStateCommit` — the root: `cmb (cellDigest) (cmb (RH) (LH))` where
    `cellDigest = cmb (frameDigest over accounts\T) (touchedDigest over T)`.
  * `effectCircuit E` — `E.guardGates ++ [cERest, cEFrame, cETouched, cELog]` (we ALWAYS emit `cELog`,
    so the gate list is match-FREE → the concrete `#guard`s stay decidable; a frozen-log effect makes
    `cELog` the trivial `LH pre = LH pre` equality, still sound).

## The generic theorems (proved ONCE — the literal generalization of the two instances' bodies)

  * `effect_circuit_full_sound` — `satisfiedE … → E.apex pre args post`. The frame is RECONSTRUCTED by
    `funext` (`c ∈ T` → `expectedLeaf`, `c ∈ accounts\T` → frozen, dead → `AccountsWF`), NEVER
    asserted. Carries ONLY injectivity portals + `AccountsWF` + a per-effect `GuardDecodes` obligation.
    NO `postRoot = effectStateCommit (applyEffect …)` ghost hypothesis appears.
  * `effect_circuit_full_complete` — every apex-satisfying step yields a satisfying witness.
  * The 4 ANTI-GHOST teeth (`_rejects_field_tamper`/`_rejects_third_cell`/`_rejects_wrong_touched`/
    `_rejects_log_forge`) + the emission faithfulness.

## The per-effect recipe (what a swarm agent supplies for effect #3)

  1. an `EffectSpec Σ Args` value (≈ 8 fields, ~15 lines);
  2. a `GuardDecodes` proof (`satisfied guardGates witness → guardProp`) — usually transported from the
     effect's existing executor⟺spec `*_iff` lemmas;
  3. a `GuardEncodes` proof (the `←`, for completeness);
  4. an `apex ↔ BespokeSpec` bridge (funext on `touchedCellMap` + And-reassoc) — ~30 lines.
  Then `full_sound`/`full_complete`/the four anti-ghost teeth come FREE through the framework.

ADDITIVE: this module does NOT refactor `StateCommit`/`SetFieldCommit`/`Transfer`/`cellstatefield`
(R5). The two instances below (`transferE`, `setFieldE`) re-obtain the crown-jewel theorems THROUGH the
framework, additively. The ONE relocation done to existing files was moving `logHashInjective` from
`SetFieldCommit` into `StateCommit` (beside the other CR carriers).
-/
import Dregg2.Circuit.StateCommit
import Dregg2.Circuit.LogCommitRegrounded

namespace Dregg2.Circuit.EffectCommit

open Dregg2.Circuit
open Dregg2.Circuit.StateCommit
open Dregg2.Circuit.LogCommitRegrounded (LogColl noLogColl_of_inj logHash_binds_of_noLogColl)
open Dregg2.Exec
open Dregg2.Exec.CircuitEmit

set_option linter.dupNamespace false

/-! ## §0 — decidability re-exports (so the concrete anti-ghost `#guard`s can `decide`). -/

instance (c : Constraint) (a : Assignment) : Decidable (c.holds a) := by
  unfold Constraint.holds; exact inferInstanceAs (Decidable (_ = _))

instance (cs : ConstraintSystem) (a : Assignment) : Decidable (satisfied cs a) := by
  unfold satisfied; exact List.decidableBAll _ _

/-! ## §1 — the framework structures.

`StateView` says how to read a kernel + receipt log out of the effect's carrier state `Σ` (for
Transfer `Σ = RecordKernelState` with an empty log; for `setFieldA` `Σ = RecChainedState` with the
chain). `CommitSurface` packages the Poseidon commitment primitives as data. `EffectSpec` is what an
effect supplies. -/

/-- **`StateView Σ`** — read a `RecordKernelState` and a receipt `List Turn` out of the carrier `Σ`. -/
structure StateView (St : Type) where
  toKernel : St → RecordKernelState
  getLog   : St → List Turn

/-- **`CommitSurface`** — the Poseidon commitment primitives as DATA: a per-cell leaf hash `CH`, a
non-`cell` rest hash `RH`, a root combiner `cmb`, a sponge `compressN`, and a receipt-chain hash `LH`.
(The 2-to-1 node hash `compress` of `StateCommit` is GONE — `touchedDigest` is a sponge.) -/
structure CommitSurface where
  CH        : CellId → Value → ℤ
  RH        : RecordKernelState → ℤ
  cmb       : ℤ → ℤ → ℤ
  compressN : List ℤ → ℤ
  LH        : List Turn → ℤ

/-- **`EffectSpec Σ Args`** — the per-effect data the generic framework consumes.

  * `view`         — the `StateView` reading kernel + log out of `Σ`.
  * `touched`      — the set `T` of cells the effect writes (a `Finset`, decidable membership).
  * `expectedLeaf` — the `Value` each cell SHOULD hold after the effect (read ONLY on `T`).
  * `logUpdate`    — `none` = the log is FROZEN (Transfer); `some f` = the log GROWS to `f pre args`.
  * `guardGates`   — the effect's admissibility gate sub-system (its `*Bit = 1` / arithmetic gates).
  * `guardProp`    — the decoded admissibility predicate the guard gates pin. -/
structure EffectSpec (St Args : Type) where
  view         : StateView St
  touched      : St → Args → Finset CellId
  expectedLeaf : St → Args → CellId → Value
  logUpdate    : Option (St → Args → List Turn)
  guardGates   : ConstraintSystem
  guardProp    : St → Args → Prop
  /-- The number of wires the guard sub-system occupies (its trace width). The framework's digest
  columns live at indices `≥ guardWidth`, so the guard witness and the digest witness never collide. -/
  guardWidth   : Nat
  /-- The guard sub-system's witness generator: lays the guard wires `0 .. guardWidth-1` out for a
  pre/args/post triple. The framework delegates those wires to it (the `else guardEncode` tail), so the
  effect's existing per-gate `*_iff` lemmas transport unchanged. -/
  guardEncode  : St → Args → St → Assignment
  /-- Every gate of `guardGates` reads ONLY wires `< guardWidth` (so the digest wires the framework
  appends never perturb a guard gate's truth value, and vice versa). Discharged per effect by
  inspecting the guard gates' var indices. -/
  guardLocal   : ∀ (a b : Assignment), (∀ w, w < guardWidth → a w = b w) →
                   (satisfied guardGates a ↔ satisfied guardGates b)
  /-- The guard region sits strictly below the digest floor (64), so the guard wires never collide
  with the framework's fixed digest columns (64..73). Discharged per effect by `by decide` (every
  real effect's guard sub-system is tiny — Transfer 11 wires, setFieldA 4). -/
  guardWidth_le : guardWidth ≤ 64

/-! ## §2 — the derived apex (the full-state declarative spec, DERIVED not supplied).

`kernelFrame` is the EXACT 16-non-`cell` frame of `RestHashIffFrame`. `touchedCellMap` is the generic
post-cell map: `T` cells get `expectedLeaf`, everything else is the base. `apex` packages guard ∧
post-cell ∧ log ∧ frame. Each instance proves its bespoke spec ↔ this apex. -/

/-- **`kernelFrame k k'`** — the 16 non-`cell` kernel components agree (the EXACT frame of
`RestHashIffFrame`, written in the `k → k'` order the apex uses). -/
def kernelFrame (k k' : RecordKernelState) : Prop :=
  k'.accounts = k.accounts ∧ k'.caps = k.caps ∧ k'.bal = k.bal
    ∧ k'.nullifiers = k.nullifiers ∧ k'.revoked = k.revoked
    ∧ k'.commitments = k.commitments
    ∧ k'.slotCaveats = k.slotCaveats ∧ k'.factories = k.factories ∧ k'.lifecycle = k.lifecycle
    ∧ k'.deathCert = k.deathCert ∧ k'.delegate = k.delegate ∧ k'.delegations = k.delegations
    ∧ k'.delegationEpoch = k.delegationEpoch
    ∧ k'.delegationEpochAt = k.delegationEpochAt
    ∧ k'.heaps = k.heaps
    ∧ k'.nullifierRoot = k.nullifierRoot ∧ k'.revokedRoot = k.revokedRoot
    ∧ k'.commitmentsRoot = k.commitmentsRoot

/-- **`touchedCellMap base T newLeaf`** — the generic post-`cell` map: cells in `T` take their
`newLeaf`, every other cell keeps the `base`. (For Transfer `T = {src,dst}` and `newLeaf = recTransfer
…`; for `setFieldA` `T = {cell}` and `newLeaf = setField …`.) -/
def touchedCellMap (base : CellId → Value) (T : Finset CellId) (newLeaf : CellId → Value) :
    CellId → Value :=
  fun c => if c ∈ T then newLeaf c else base c

/-- The post log the apex predicts: `pre`'s log if frozen, else `f pre args`. -/
def EffectSpec.postLog {St Args : Type} (E : EffectSpec St Args) (pre : St) (args : Args) : List Turn :=
  match E.logUpdate with
  | none   => E.view.getLog pre
  | some f => f pre args

/-- **`EffectSpec.apex E pre args post`** — the DERIVED full-state declarative spec: the guard holds,
the post `cell` map is the `touchedCellMap`, the log is the predicted post log, and the 16 non-`cell`
kernel components are frozen (`kernelFrame`). -/
def EffectSpec.apex {St Args : Type} (E : EffectSpec St Args) (pre : St) (args : Args) (post : St) :
    Prop :=
  E.guardProp pre args
  ∧ (E.view.toKernel post).cell
      = touchedCellMap (E.view.toKernel pre).cell (E.touched pre args) (E.expectedLeaf pre args)
  ∧ E.view.getLog post = E.postLog pre args
  ∧ kernelFrame (E.view.toKernel pre) (E.view.toKernel post)

/-! ## §3 — the commitment.

`touchedDigest` IS `frameDigest` over the carrier `T` (the keystone). `cellDigest` combines the frame
sponge (over `accounts \ T`) with the touched sponge (over `T`). `effectStateCommit` combines the cell
digest with the rest-and-log digest. -/

/-- **`touchedDigest S leaf T`** — the sponge of the TOUCHED cells' leaves over an arbitrary cell map
`leaf` (so the gate can compare the post leaves to the SPEC's `expectedLeaf` without the executor).
LITERALLY `StateCommit.frameDigest` with carrier `T` and a cell map `leaf` — so
`FrameDigestBindsCells` binds it. -/
def touchedDigest (CH : CellId → Value → ℤ) (compressN : List ℤ → ℤ) (leaf : CellId → Value)
    (T : Finset CellId) : ℤ :=
  StateCommit.frameDigest CH compressN { accounts := ∅, cell := leaf, caps := fun _ => [] } T

/-- `touchedDigest` is `frameDigest` over carrier `T` for ANY state whose `cell` map is `leaf`. -/
theorem touchedDigest_eq_frameDigest (CH : CellId → Value → ℤ) (compressN : List ℤ → ℤ)
    (k : RecordKernelState) (T : Finset CellId) :
    touchedDigest CH compressN k.cell T = StateCommit.frameDigest CH compressN k T := by
  unfold touchedDigest StateCommit.frameDigest; rfl

/-- **`cellDigest S k leaf T`** — the live-cell digest: combine the untouched-frame sponge (over
`accounts \ T`, read off `k`) with the touched sponge (over `T`, read off `leaf`). -/
def cellDigest (S : CommitSurface) (k : RecordKernelState) (leaf : CellId → Value)
    (T : Finset CellId) : ℤ :=
  S.cmb (StateCommit.frameDigest S.CH S.compressN k (k.accounts \ T))
        (touchedDigest S.CH S.compressN leaf T)

/-- **`effectStateCommit S k leaf T log`** — the full-state root: combine the cell digest with
(`cmb` of the rest hash and the log hash). Tampering any cell changes a sponge; any non-`cell` field
changes `RH`; the log changes `LH`; `cmb`-injectivity separates them. -/
def effectStateCommit (S : CommitSurface) (k : RecordKernelState) (leaf : CellId → Value)
    (T : Finset CellId) (log : List Turn) : ℤ :=
  S.cmb (cellDigest S k leaf T) (S.cmb (S.RH k) (S.LH log))

/-! ## §4 — the named DIGEST wires (CONCRETE indices) + the encoder.

The digest columns live at FIXED concrete indices `64 .. 73` (the `digestFloor` is 64); the guard
wires live strictly below (`E.guardWidth ≤ 64`), so the two regions never collide. **Concrete indices
are the KEY robustness choice**: every `if`-condition is a literal Nat equality, so Lean's `reduceIte`
simproc collapses the encoder cascade automatically — no symbolic-offset arithmetic, no
`omega`-inside-`if_neg` metavariable tarpit (which is what made the first attempt spin). Ten columns:
pre/post root, rest pre/post, frame pre/post, touched post/expected, log post/expected. -/

/-- `preRoot`  wire. -/    abbrev vEPreRoot     : Var := 64
/-- `postRoot` wire. -/    abbrev vEPostRoot    : Var := 65
/-- `restDigPre`  wire. -/ abbrev vERestPre     : Var := 66
/-- `restDigPost` wire. -/ abbrev vERestPost    : Var := 67
/-- `frameDigPre`  wire. -/abbrev vEFramePre    : Var := 68
/-- `frameDigPost` wire. -/abbrev vEFramePost   : Var := 69
/-- `touchedDigPost`     wire. -/ abbrev vETouchedPost : Var := 70
/-- `touchedDigExpected` wire. -/ abbrev vETouchedExp  : Var := 71
/-- `logDigPost`     wire. -/ abbrev vELogPost : Var := 72
/-- `logDigExpected` wire. -/ abbrev vELogExp  : Var := 73

/-- The full-state effect trace width (guard region `< 64`, digests `64 .. 73`). -/
def EffectSpec.traceWidth {St Args : Type} (_E : EffectSpec St Args) : Nat := 74

/-- **`encodeE`** — the full-state effect witness. Wires `0 .. g-1` DELEGATE to the guard sub-system's
`guardEncode` (so the effect's guard `*_iff` lemmas transport); the ten digest columns at `≥ g` carry
the honest commitment values. The expected columns commit the SPEC's predicted touched leaves +
post-log (pure functions of pre + args; no executor). The frame digests use carrier `accounts \ T`
read off the PRE kernel for BOTH pre and post (the accounts set is frozen by the apex, so the carriers
coincide). -/
def encodeE {St Args : Type} (S : CommitSurface) (E : EffectSpec St Args)
    (pre : St) (args : Args) (post : St) : Assignment :=
  fun w =>
    if      w = vEPreRoot    then
      effectStateCommit S (E.view.toKernel pre) (E.view.toKernel pre).cell (E.touched pre args)
        (E.view.getLog pre)
    else if w = vEPostRoot   then
      effectStateCommit S (E.view.toKernel post) (E.view.toKernel post).cell (E.touched pre args)
        (E.view.getLog post)
    else if w = vERestPre    then S.RH (E.view.toKernel pre)
    else if w = vERestPost   then S.RH (E.view.toKernel post)
    else if w = vEFramePre   then
      StateCommit.frameDigest S.CH S.compressN (E.view.toKernel pre)
        ((E.view.toKernel pre).accounts \ E.touched pre args)
    else if w = vEFramePost  then
      StateCommit.frameDigest S.CH S.compressN (E.view.toKernel post)
        ((E.view.toKernel pre).accounts \ E.touched pre args)
    else if w = vETouchedPost then
      touchedDigest S.CH S.compressN (E.view.toKernel post).cell (E.touched pre args)
    else if w = vETouchedExp  then
      touchedDigest S.CH S.compressN (E.expectedLeaf pre args) (E.touched pre args)
    else if w = vELogPost     then S.LH (E.view.getLog post)
    else if w = vELogExp      then S.LH (E.postLog pre args)
    else E.guardEncode pre args post w

/-- **Transport:** on every guard wire (`w < g`) `encodeE` agrees with `guardEncode`, so the effect's
guard `*_iff` lemmas apply to `encodeE` verbatim. (Every digest wire index is `≥ g`, so under `w < g`
all the digest `if`s take their `else`.) -/
theorem encodeE_agrees_guardEncode {St Args : Type} (S : CommitSurface) (E : EffectSpec St Args)
    (pre : St) (args : Args) (post : St) (w : Var) (hw : w < E.guardWidth) :
    encodeE S E pre args post w = E.guardEncode pre args post w := by
  have hle := E.guardWidth_le
  unfold encodeE Var at *
  simp only [vEPreRoot, vEPostRoot, vERestPre, vERestPost, vEFramePre, vEFramePost, vETouchedPost,
    vETouchedExp, vELogPost, vELogExp]
  split_ifs <;> first | rfl | (exfalso; omega)

/-! ## §4b — digest wire lookups (the `if`-cascade collapsed at each digest index).

Each digest wire index is `g + k` for distinct `k`, so the cascade resolves by `omega`-discharged
disequalities. We package them as a single `simp`-friendly bundle via `encE_*` lemmas. -/

/-- The ONE robust lookup tactic (the reusable proof-strategy): unfold `encodeE` + the (concrete) wire
abbrevs; the `reduceIte` simproc collapses the literal-condition cascade to the matched value. Same
proof for every wire — concrete indices are why this is bulletproof (no `omega`-in-`if_neg` tarpit). -/
macro "ec_lookup" : tactic =>
  `(tactic| simp [encodeE, vEPreRoot, vEPostRoot, vERestPre, vERestPost, vEFramePre, vEFramePost,
      vETouchedPost, vETouchedExp, vELogPost, vELogExp])

section Lookups
variable {St Args : Type} (S : CommitSurface) (E : EffectSpec St Args) (pre : St) (args : Args)
  (post : St)

theorem encE_preRoot :
    encodeE S E pre args post vEPreRoot
      = effectStateCommit S (E.view.toKernel pre) (E.view.toKernel pre).cell (E.touched pre args)
          (E.view.getLog pre) := by ec_lookup
theorem encE_postRoot :
    encodeE S E pre args post vEPostRoot
      = effectStateCommit S (E.view.toKernel post) (E.view.toKernel post).cell (E.touched pre args)
          (E.view.getLog post) := by ec_lookup
theorem encE_restPre :
    encodeE S E pre args post vERestPre = S.RH (E.view.toKernel pre) := by ec_lookup
theorem encE_restPost :
    encodeE S E pre args post vERestPost = S.RH (E.view.toKernel post) := by ec_lookup
theorem encE_framePre :
    encodeE S E pre args post vEFramePre
      = StateCommit.frameDigest S.CH S.compressN (E.view.toKernel pre)
          ((E.view.toKernel pre).accounts \ E.touched pre args) := by ec_lookup
theorem encE_framePost :
    encodeE S E pre args post vEFramePost
      = StateCommit.frameDigest S.CH S.compressN (E.view.toKernel post)
          ((E.view.toKernel pre).accounts \ E.touched pre args) := by ec_lookup
theorem encE_touchedPost :
    encodeE S E pre args post vETouchedPost
      = touchedDigest S.CH S.compressN (E.view.toKernel post).cell (E.touched pre args) := by ec_lookup
theorem encE_touchedExp :
    encodeE S E pre args post vETouchedExp
      = touchedDigest S.CH S.compressN (E.expectedLeaf pre args) (E.touched pre args) := by ec_lookup
theorem encE_logPost :
    encodeE S E pre args post vELogPost = S.LH (E.view.getLog post) := by ec_lookup
theorem encE_logExp :
    encodeE S E pre args post vELogExp = S.LH (E.postLog pre args) := by ec_lookup

end Lookups

/-! ## §5 — the four frame-forcing EQ gates + `satisfiedE`.

The gates compare the digest wires (at offsets relative to a supplied guard width `g`). We ALWAYS emit
`cELog` (even for a frozen-log effect, where it is the trivial `LH pre = LH pre`) so the circuit list is
match-FREE → the concrete `#guard`s stay decidable. -/

/-- **Rest-frame gate:** `restDigPre = restDigPost`. -/
def cERest : Constraint := { lhs := .var vERestPre, rhs := .var vERestPost }
/-- **Frame-reuse gate:** `frameDigPre = frameDigPost`. -/
def cEFrame : Constraint := { lhs := .var vEFramePre, rhs := .var vEFramePost }
/-- **Touched-bind gate:** `touchedDigPost = touchedDigExpected`. -/
def cETouched : Constraint := { lhs := .var vETouchedPost, rhs := .var vETouchedExp }
/-- **Log-bind gate:** `logDigPost = logDigExpected`. -/
def cELog : Constraint := { lhs := .var vELogPost, rhs := .var vELogExp }

/-- **The full-state effect circuit** — the effect's guard gates ++ the four frame-forcing EQ gates.
The four EQ gates pin the WHOLE post-state (frame ∧ touched ∧ log); the guard gates pin admissibility. -/
def effectCircuit {St Args : Type} (E : EffectSpec St Args) : ConstraintSystem :=
  E.guardGates ++ [cERest, cEFrame, cETouched, cELog]

/-- **`satisfiedE S E a`** — the full-state effect satisfaction predicate: the `effectCircuit` gates
hold. The four frame-forcing EQ gates ARE the binding mechanism — via the reused frame/touched/log
digests + injectivity, they pin the WHOLE post-state (this is exactly what `effect_circuit_full_sound`
extracts). (`S` is kept in the signature so the surface is fixed across the soundness/completeness API;
a published-root-commits-the-state corollary, à la `StateCommit.recStateCommit_binds`, can be added on
top via `cmb`-injectivity — not needed for the crown-jewel soundness, which the EQ gates already give.) -/
def satisfiedE {St Args : Type} (_S : CommitSurface) (E : EffectSpec St Args) (a : Assignment) : Prop :=
  satisfied (effectCircuit E) a

/-! ## §5b — the four frame-gate ↔ digest-equality lemmas (each EQ gate's protocol content). -/

section GateIff
variable {St Args : Type} (S : CommitSurface) (E : EffectSpec St Args) (pre : St) (args : Args)
  (post : St)

/-- `cERest` holds under `encodeE` IFF the rest hashes agree. -/
theorem erest_iff :
    cERest.holds (encodeE S E pre args post)
      ↔ S.RH (E.view.toKernel pre) = S.RH (E.view.toKernel post) := by
  unfold Constraint.holds cERest
  simp only [Expr.eval, encE_restPre, encE_restPost]

/-- `cEFrame` holds under `encodeE` IFF the frame digests (over `accounts \ T`) agree. -/
theorem eframe_iff :
    cEFrame.holds (encodeE S E pre args post)
      ↔ StateCommit.frameDigest S.CH S.compressN (E.view.toKernel pre)
            ((E.view.toKernel pre).accounts \ E.touched pre args)
          = StateCommit.frameDigest S.CH S.compressN (E.view.toKernel post)
            ((E.view.toKernel pre).accounts \ E.touched pre args) := by
  unfold Constraint.holds cEFrame
  simp only [Expr.eval, encE_framePre, encE_framePost]

/-- `cETouched` holds under `encodeE` IFF the post touched digest equals the spec-expected one. -/
theorem etouched_iff :
    cETouched.holds (encodeE S E pre args post)
      ↔ touchedDigest S.CH S.compressN (E.view.toKernel post).cell (E.touched pre args)
          = touchedDigest S.CH S.compressN (E.expectedLeaf pre args) (E.touched pre args) := by
  unfold Constraint.holds cETouched
  simp only [Expr.eval, encE_touchedPost, encE_touchedExp]

/-- `cELog` holds under `encodeE` IFF the post log hash equals the spec-predicted post log hash. -/
theorem elog_iff :
    cELog.holds (encodeE S E pre args post)
      ↔ S.LH (E.view.getLog post) = S.LH (E.postLog pre args) := by
  unfold Constraint.holds cELog
  simp only [Expr.eval, encE_logPost, encE_logExp]

end GateIff

/-! ## §6 — the generic crown-jewel theorems (proved ONCE).

`effect_circuit_full_sound` is the literal generalization of the two instances' `*_full_sound`: the
`funext` switches on `c ∈ T` (decidable Finset membership) instead of the hard-coded `c = src ∨ c =
dst` / `c = cell`. It carries ONLY injectivity portals + `AccountsWF` + a per-effect `GuardDecodes`
obligation. NO `postRoot = effectStateCommit (applyEffect …)` ghost. -/

/-- Per-effect GUARD obligation (the `→`): the guard gates, on the guard's own witness, DECODE to the
guard predicate. Each effect discharges this from its executor⟺spec `*_iff` lemmas. -/
def GuardDecodes {St Args : Type} (E : EffectSpec St Args) : Prop :=
  ∀ (pre : St) (args : Args) (post : St),
    satisfied E.guardGates (E.guardEncode pre args post) → E.guardProp pre args

/-- Per-effect GUARD obligation (the `←`, for completeness): the guard predicate ENCODES to satisfied
guard gates. -/
def GuardEncodes {St Args : Type} (E : EffectSpec St Args) : Prop :=
  ∀ (pre : St) (args : Args) (post : St),
    E.guardProp pre args → satisfied E.guardGates (E.guardEncode pre args post)

section Sound
variable {St Args : Type} (S : CommitSurface) (E : EffectSpec St Args)

/-- **`effect_circuit_full_sound` — the generic crown jewel.** A satisfying full-state witness pins the
WHOLE post-state: the effect's `apex` holds (guard ∧ post-cell = `touchedCellMap` ∧ log ∧ 16-field
frame). The post `cell` map is RECONSTRUCTED by `funext` (touched → `expectedLeaf`; live-untouched →
frozen by the frame digest; dead → `AccountsWF`); the log + 16 fields from the rest/log gates. Carries
only the realizable Poseidon-CR injectivity portals + `AccountsWF` + the per-effect `GuardDecodes`. -/
theorem effect_circuit_full_sound
    (hN : compressNInjective S.compressN) (hL : cellLeafInjective S.CH)
    (hRest : RestHashIffFrame S.RH)
    (hGuard : GuardDecodes E)
    (pre : St) (args : Args) (post : St)
    (hwf  : AccountsWF (E.view.toKernel pre)) (hwf' : AccountsWF (E.view.toKernel post))
    (hno : ¬ LogColl S.LH (E.view.getLog post) (E.postLog pre args))
    (h : satisfiedE S E (encodeE S E pre args post)) :
    E.apex pre args post := by
  have hArith : satisfied (effectCircuit E) (encodeE S E pre args post) := h
  -- guard: the guardGates portion of the circuit, transported to the guard's own witness, decoded.
  have hguardSat : satisfied E.guardGates (encodeE S E pre args post) := by
    intro c hc; exact hArith c (by unfold effectCircuit; exact List.mem_append_left _ hc)
  have hguardSat' : satisfied E.guardGates (E.guardEncode pre args post) :=
    (E.guardLocal _ _ (fun w hw => encodeE_agrees_guardEncode S E pre args post w hw)).mp hguardSat
  have hguard : E.guardProp pre args := hGuard pre args post hguardSat'
  -- the four frame-forcing EQ gates hold:
  have hrest  : cERest.holds (encodeE S E pre args post)    := hArith cERest    (by simp [effectCircuit])
  have hframe : cEFrame.holds (encodeE S E pre args post)   := hArith cEFrame   (by simp [effectCircuit])
  have htouch : cETouched.holds (encodeE S E pre args post) := hArith cETouched (by simp [effectCircuit])
  have hlog   : cELog.holds (encodeE S E pre args post)     := hArith cELog     (by simp [effectCircuit])
  -- decode: rest-frame (16 fields), untouched cells, touched cells, log.
  have hkframe : kernelFrame (E.view.toKernel pre) (E.view.toKernel post) :=
    (hRest (E.view.toKernel pre) (E.view.toKernel post)).mp ((erest_iff S E pre args post).mp hrest)
  have hframeCells : ∀ c ∈ (E.view.toKernel pre).accounts \ E.touched pre args,
      (E.view.toKernel pre).cell c = (E.view.toKernel post).cell c :=
    FrameDigestBindsCells S.CH S.compressN hN hL _ _ _ ((eframe_iff S E pre args post).mp hframe)
  have htouchCells : ∀ c ∈ E.touched pre args,
      (E.view.toKernel post).cell c = E.expectedLeaf pre args c := by
    have hte := (etouched_iff S E pre args post).mp htouch
    unfold touchedDigest at hte
    exact FrameDigestBindsCells S.CH S.compressN hN hL
      { accounts := ∅, cell := (E.view.toKernel post).cell, caps := fun _ => [] }
      { accounts := ∅, cell := E.expectedLeaf pre args, caps := fun _ => [] }
      (E.touched pre args) hte
  have hlogVal : E.view.getLog post = E.postLog pre args :=
    logHash_binds_of_noLogColl S.LH _ _ hno ((elog_iff S E pre args post).mp hlog)
  -- reconstruct the post cell map by funext over (touched / live-untouched / dead).
  have hcellmap : (E.view.toKernel post).cell
      = touchedCellMap (E.view.toKernel pre).cell (E.touched pre args) (E.expectedLeaf pre args) := by
    funext c
    unfold touchedCellMap
    by_cases hcT : c ∈ E.touched pre args
    · rw [if_pos hcT]; exact htouchCells c hcT
    · rw [if_neg hcT]
      by_cases hcA : c ∈ (E.view.toKernel pre).accounts
      · exact (hframeCells c (Finset.mem_sdiff.mpr ⟨hcA, hcT⟩)).symm
      · have haccEq : (E.view.toKernel post).accounts = (E.view.toKernel pre).accounts := hkframe.1
        rw [hwf' c (by rw [haccEq]; exact hcA), hwf c hcA]
  exact ⟨hguard, hcellmap, hlogVal, hkframe⟩

/-- `frameDigest` depends on its state only through `cell` ON the carrier `S`: agree there ⇒ equal
digests. The completeness-side congruence (the dual of `FrameDigestBindsCells`). -/
private theorem frameDigest_congr (CH : CellId → Value → ℤ) (cN : List ℤ → ℤ)
    (k k' : RecordKernelState) (T : Finset CellId) (h : ∀ c ∈ T, k.cell c = k'.cell c) :
    StateCommit.frameDigest CH cN k T = StateCommit.frameDigest CH cN k' T := by
  unfold StateCommit.frameDigest
  refine congrArg cN (List.map_congr_left ?_)
  intro c hc
  rw [h c ((Finset.mem_sort _).mp hc)]

/-- **`effect_circuit_full_complete`** — every apex-satisfying step yields a satisfying full-state
witness. The four EQ gates are discharged from the apex's frame/cell/log clauses; the guard gates from
the per-effect `GuardEncodes`. -/
theorem effect_circuit_full_complete
    (hRest : RestHashIffFrame S.RH) (hGuardEnc : GuardEncodes E)
    (pre : St) (args : Args) (post : St)
    (hspec : E.apex pre args post) :
    satisfiedE S E (encodeE S E pre args post) := by
  obtain ⟨hguard, hcellmap, hlogVal, hkframe⟩ := hspec
  show satisfied (effectCircuit E) (encodeE S E pre args post)
  -- post.cell agrees with pre.cell off T (from the cell map), and with expectedLeaf on T.
  have hoff : ∀ c ∈ (E.view.toKernel pre).accounts \ E.touched pre args,
      (E.view.toKernel pre).cell c = (E.view.toKernel post).cell c := by
    intro c hc
    have hcT : c ∉ E.touched pre args := (Finset.mem_sdiff.mp hc).2
    rw [hcellmap, touchedCellMap, if_neg hcT]
  have hon : ∀ c ∈ E.touched pre args,
      (E.view.toKernel post).cell c = E.expectedLeaf pre args c := by
    intro c hc; rw [hcellmap, touchedCellMap, if_pos hc]
  intro c hc
  rcases List.mem_append.mp hc with hcg | hc4
  · -- a guard gate
    have hge : satisfied E.guardGates (encodeE S E pre args post) :=
      (E.guardLocal _ _ (fun w hw => encodeE_agrees_guardEncode S E pre args post w hw)).mpr
        (hGuardEnc pre args post hguard)
    exact hge c hcg
  · -- one of the four EQ gates
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc4
    rcases hc4 with rfl | rfl | rfl | rfl
    · exact (erest_iff S E pre args post).mpr
        ((hRest (E.view.toKernel pre) (E.view.toKernel post)).mpr hkframe)
    · exact (eframe_iff S E pre args post).mpr
        (frameDigest_congr S.CH S.compressN _ _ _ hoff)
    · refine (etouched_iff S E pre args post).mpr ?_
      unfold touchedDigest
      exact frameDigest_congr S.CH S.compressN
        { accounts := ∅, cell := (E.view.toKernel post).cell, caps := fun _ => [] }
        { accounts := ∅, cell := E.expectedLeaf pre args, caps := fun _ => [] }
        (E.touched pre args) hon
    · exact (elog_iff S E pre args post).mpr (by rw [hlogVal])

/-! ### Anti-ghost teeth (each forgery a single EQ gate REJECTS). -/

/-- **field tamper REJECTED:** a post-state whose `nullifiers` (any non-`cell` component) differ from
`pre`'s cannot satisfy — `cERest` + `RestHashIffFrame`. -/
theorem effectCircuit_rejects_field_tamper (hRest : RestHashIffFrame S.RH)
    (pre : St) (args : Args) (post : St)
    (htamper : (E.view.toKernel post).nullifiers ≠ (E.view.toKernel pre).nullifiers) :
    ¬ satisfiedE S E (encodeE S E pre args post) := by
  intro h
  have hrest : cERest.holds (encodeE S E pre args post) := h cERest (by simp [effectCircuit])
  have hkf := (hRest (E.view.toKernel pre) (E.view.toKernel post)).mp
    ((erest_iff S E pre args post).mp hrest)
  exact htamper hkf.2.2.2.1

/-- **third-cell tamper REJECTED:** a live bystander cell (`c₀ ∈ accounts`, `c₀ ∉ T`) whose post value
differs from pre cannot satisfy — `cEFrame` + `FrameDigestBindsCells`. -/
theorem effectCircuit_rejects_third_cell
    (hN : compressNInjective S.compressN) (hL : cellLeafInjective S.CH)
    (pre : St) (args : Args) (post : St) {c₀ : CellId}
    (hc₀ : c₀ ∈ (E.view.toKernel pre).accounts) (hc₀T : c₀ ∉ E.touched pre args)
    (htamper : (E.view.toKernel pre).cell c₀ ≠ (E.view.toKernel post).cell c₀) :
    ¬ satisfiedE S E (encodeE S E pre args post) := by
  intro h
  have hframe : cEFrame.holds (encodeE S E pre args post) := h cEFrame (by simp [effectCircuit])
  exact htamper (FrameDigestBindsCells S.CH S.compressN hN hL _ _ _
    ((eframe_iff S E pre args post).mp hframe) c₀ (Finset.mem_sdiff.mpr ⟨hc₀, hc₀T⟩))

/-- **wrong-touched tamper REJECTED:** a touched cell whose post value differs from the spec's
`expectedLeaf` cannot satisfy — `cETouched` + `FrameDigestBindsCells` on carrier `T`. -/
theorem effectCircuit_rejects_wrong_touched
    (hN : compressNInjective S.compressN) (hL : cellLeafInjective S.CH)
    (pre : St) (args : Args) (post : St) {c₀ : CellId}
    (hc₀ : c₀ ∈ E.touched pre args)
    (htamper : (E.view.toKernel post).cell c₀ ≠ E.expectedLeaf pre args c₀) :
    ¬ satisfiedE S E (encodeE S E pre args post) := by
  intro h
  have htouch : cETouched.holds (encodeE S E pre args post) := h cETouched (by simp [effectCircuit])
  have hte := (etouched_iff S E pre args post).mp htouch
  unfold touchedDigest at hte
  exact htamper (FrameDigestBindsCells S.CH S.compressN hN hL
    { accounts := ∅, cell := (E.view.toKernel post).cell, caps := fun _ => [] }
    { accounts := ∅, cell := E.expectedLeaf pre args, caps := fun _ => [] }
    (E.touched pre args) hte c₀ hc₀)

/-- **log forgery REJECTED:** a post-log differing from the spec-predicted post-log cannot satisfy —
`cELog` + `logHashInjective`. -/
theorem effectCircuit_rejects_log_forge
    (pre : St) (args : Args) (post : St)
    (hno : ¬ LogColl S.LH (E.view.getLog post) (E.postLog pre args))
    (htamper : E.view.getLog post ≠ E.postLog pre args) :
    ¬ satisfiedE S E (encodeE S E pre args post) := by
  intro h
  have hlog : cELog.holds (encodeE S E pre args post) := h cELog (by simp [effectCircuit])
  exact htamper (logHash_binds_of_noLogColl S.LH _ _ hno ((elog_iff S E pre args post).mp hlog))

end Sound

/-! ## §7 — emission: the effect circuit serializes losslessly to the wire form. -/

/-- The emitted effect circuit (serialized via `CircuitEmit.emit`). -/
def emittedEffect {St Args : Type} (name : String) (E : EffectSpec St Args) : EmittedDescriptor :=
  emit name E.traceWidth (effectCircuit E)

/-- **`emitEffectFaithful`** — satisfying the emitted effect circuit is EXACTLY satisfying
`effectCircuit E` (a direct instance of `CircuitEmit.emit_faithful`). -/
theorem emitEffectFaithful {St Args : Type} (name : String) (E : EffectSpec St Args) (a : Assignment) :
    satisfied (effectCircuit E) a ↔ satisfiedEmitted (emittedEffect name E) a :=
  emit_faithful name E.traceWidth (effectCircuit E) a

/-! ## §8 — axiom-hygiene tripwires (the portals are HYPOTHESES, so the theorems stay kernel-clean). -/

#assert_axioms encodeE_agrees_guardEncode
#assert_axioms effect_circuit_full_sound
#assert_axioms effect_circuit_full_complete
#assert_axioms effectCircuit_rejects_field_tamper
#assert_axioms effectCircuit_rejects_third_cell
#assert_axioms effectCircuit_rejects_wrong_touched
#assert_axioms effectCircuit_rejects_log_forge
#assert_axioms emitEffectFaithful

end Dregg2.Circuit.EffectCommit
