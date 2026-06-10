/-
# Dregg2.Circuit.EffectCommit2 — the v2 GENERIC full-state circuit⟺spec framework for NON-CELL effects.

`Dregg2.Circuit.EffectCommit` (v1) abstracted the crown jewel for effects that touch the `cell`
function-field: a satisfying full-state witness pins the WHOLE post-state (`effect_circuit_full_sound`),
carrying only realizable Poseidon-CR portals + `AccountsWF` + a per-effect `GuardDecodes`. But ~25 of
the remaining effects touch a NON-`cell` component instead — a function-field (`bal`/`caps`) or a `List`
side-table (`nullifiers`/`commitments`/`escrows`/`queues`/`swiss`/`revoked`). v2 GENERALIZES "the
touched thing is a cell" to "the touched thing is ONE `ActiveComponent`" (this SINGLE-component version;
multi-component — escrow = `bal`+`escrows` — is a DEFERRED follow-up).

## The keystone simplification (why a single uniform `ActiveComponent` works)

v1's touched-cell binding was a `frameDigest`/`FrameDigestBindsCells` instance. v2 reads BOTH carriers
through ONE interface, `ActiveComponent`:

  * `digest   : RecordKernelState → ℤ`             — the component's honest commitment, read off the kernel.
  * `expected : St → Args → ℤ`                     — the SPEC's predicted commitment (pure in pre+args).
  * `postClause : St → Args → RecordKernelState → Prop` — the declarative post-shape of the component.
  * `binds  : digest post = expected pre args → postClause pre args post`   (the soundness direction).
  * `encodes : postClause pre args post → digest post = expected pre args`  (the completeness direction).

Two smart constructors build one:
  * `listComponent` (off `ListCommit.ListDigestBindsList`)  — a `List`-side-table; `postClause` is FULL
    list equality (a drop/reorder of an existing entry is REJECTED, not just "grew by the new entry").
  * `funcComponent` (off any injective whole-value digest)  — a function-field (`bal`/`caps`);
    `postClause` is FULL function equality `read post = expectedVal pre args`.
  * `keyedComponent` (off `KeyedCommit.KeyedDigestBindsKeys`) — the FINITE-CARRIER, pointwise variant
    (`∀ k ∈ S, leaf-of-post k = expected k`), for effects whose spec is genuinely keyed-pointwise.

`binds` does ALL the |touched|-variable work, so v2's soundness needs NO `funext`-over-cells: the
component's `postClause` drops out of `binds` directly. The 15-or-16 untouched non-`cell` fields are
frozen by a `restFrame` portal (`RestIffNo*`, the v1 `RestHashIffFrame` with the touched field omitted),
and the log by `logHashInjective`. This is the literal generalization of v1's soundness body.

## The assumption ledger (carried Prop hypotheses — NEVER `axiom`)

ASSUMED on the keystones: a per-effect `RestIffNo*` portal (the rest hash binds the untouched fields,
the touched field omitted — a realizable injective rest hash) + `logHashInjective LH` + the per-effect
`GuardDecodes`. The component's `binds`/`encodes` are FIELDS of the `ActiveComponent`, discharged by the
smart constructors FROM the realizable Poseidon-CR set (`compressNInjective` + an injective leaf/value
encoder), exactly the v1 bar. NO `AccountsWF` is needed (the touched thing is not the cell map). NO
`postRoot = effectStateCommit (applyEffect …)` ghost appears.

ADDITIVE: imports `EffectCommit`/`ListCommit`/`KeyedCommit`/`StateCommit` + the two validating specs;
edits none of them.
-/
import Dregg2.Circuit.EffectCommit
import Dregg2.Circuit.ListCommit
import Dregg2.Circuit.KeyedCommit
import Dregg2.Circuit.Spec.supplycreation
import Dregg2.Circuit.Spec.notenullifier

namespace Dregg2.Circuit.EffectCommit2

open Dregg2.Circuit
open Dregg2.Circuit.StateCommit
open Dregg2.Circuit.EffectCommit (StateView)
open Dregg2.Circuit.ListCommit
open Dregg2.Circuit.KeyedCommit
open Dregg2.Exec
open Dregg2.Exec.CircuitEmit

set_option linter.dupNamespace false

/-! ## §0 — decidability re-exports (so the concrete `#guard`s can `decide`). -/

instance (c : Constraint) (a : Assignment) : Decidable (c.holds a) := by
  unfold Constraint.holds; exact inferInstanceAs (Decidable (_ = _))

instance (cs : ConstraintSystem) (a : Assignment) : Decidable (satisfied cs a) := by
  unfold satisfied; exact List.decidableBAll _ _

/-! ## §1 — the `RestIffNo*` portals (the v1 `RestHashIffFrame` minus one touched field).

Each is the realizable injective-rest-hash portal for an effect that touches ONE non-`cell` field: the
rest hash binds the OTHER 15 (or 16, if the touched field is `bal`/a list) components, OMITTING the
touched one. Carried Prop hypotheses (realizable — a Poseidon hash of a canonical serialization of the
named fields), never axioms. We provide the two the validating targets need; the swarm adds one per
touched field (1-line mirrors). -/

/-- **`RestIffNoBal RH`** — the rest hash binds the 15 non-`cell`-non-`bal` components (BIDIRECTIONAL),
omitting `bal` (the touched field of mint/burn/bridgeMint/balanceA). -/
def RestIffNoBal (RH : RecordKernelState → ℤ) : Prop :=
  ∀ k k' : RecordKernelState, RH k = RH k' ↔
    (k'.accounts = k.accounts ∧ k'.cell = k.cell ∧ k'.caps = k.caps
      ∧ k'.nullifiers = k.nullifiers ∧ k'.revoked = k.revoked
      ∧ k'.commitments = k.commitments ∧ k'.swiss = k.swiss
      ∧ k'.slotCaveats = k.slotCaveats ∧ k'.factories = k.factories ∧ k'.lifecycle = k.lifecycle
      ∧ k'.deathCert = k.deathCert ∧ k'.delegate = k.delegate ∧ k'.delegations = k.delegations
      ∧ k'.sealedBoxes = k.sealedBoxes
      ∧ k'.delegationEpoch = k.delegationEpoch
      ∧ k'.delegationEpochAt = k.delegationEpochAt)

/-- **`RestIffNoNullifiers RH`** — the rest hash binds the 15 non-`cell`-non-`nullifiers` components
(BIDIRECTIONAL), omitting `nullifiers` (the touched field of `noteSpendA`). -/
def RestIffNoNullifiers (RH : RecordKernelState → ℤ) : Prop :=
  ∀ k k' : RecordKernelState, RH k = RH k' ↔
    (k'.accounts = k.accounts ∧ k'.cell = k.cell ∧ k'.caps = k.caps
      ∧ k'.bal = k.bal ∧ k'.revoked = k.revoked
      ∧ k'.commitments = k.commitments ∧ k'.swiss = k.swiss
      ∧ k'.slotCaveats = k.slotCaveats ∧ k'.factories = k.factories ∧ k'.lifecycle = k.lifecycle
      ∧ k'.deathCert = k.deathCert ∧ k'.delegate = k.delegate ∧ k'.delegations = k.delegations
      ∧ k'.sealedBoxes = k.sealedBoxes
      ∧ k'.delegationEpoch = k.delegationEpoch
      ∧ k'.delegationEpochAt = k.delegationEpochAt)

/-! ## §2 — the `ActiveComponent` interface + the two/three smart constructors.

An `ActiveComponent St Args` reads ONE non-`cell` component as a digest, predicts it, and (the load-
bearing pair) binds/encodes its declarative post-shape. The smart constructors instantiate it FROM the
realizable Poseidon-CR carriers — the per-effect crypto work happens HERE, once per shape, not per
effect. -/

/-- **`ActiveComponent St Args`** — the shape-agnostic touched-component interface. -/
structure ActiveComponent (St Args : Type) where
  /-- The component's honest commitment, read off the post kernel. -/
  digest    : RecordKernelState → ℤ
  /-- The SPEC's predicted commitment (a pure function of pre + args; no executor). -/
  expected  : St → Args → ℤ
  /-- The declarative post-shape the component pins (e.g. `post.bal = recBalCredit …`). -/
  postClause : St → Args → RecordKernelState → Prop
  /-- SOUNDNESS: equal digests force the declarative post-shape. -/
  binds     : ∀ (pre : St) (args : Args) (post : RecordKernelState),
                digest post = expected pre args → postClause pre args post
  /-- COMPLETENESS: the declarative post-shape forces equal digests. -/
  encodes   : ∀ (pre : St) (args : Args) (post : RecordKernelState),
                postClause pre args post → digest post = expected pre args

/-- **`listComponent`** — an `ActiveComponent` for a `List`-side-table field `read : RKS → List α`,
whose digest is the `ListCommit.listDigest` sponge. `binds` is `ListDigestBindsList` (FULL list
equality — a drop/reorder of an existing entry is REJECTED); `encodes` is `listDigest_congr`. The
crypto carriers (`compressNInjective` + an injective leaf) are consumed HERE. -/
def listComponent {St Args : Type} {α : Type}
    (read : RecordKernelState → List α) (LE : α → ℤ) (cN : List ℤ → ℤ)
    (hN : compressNInjective cN) (hLE : listLeafInjective LE)
    (expectedList : St → Args → List α) : ActiveComponent St Args where
  digest    := fun k => listDigest LE cN (read k)
  expected  := fun pre args => listDigest LE cN (expectedList pre args)
  postClause := fun pre args post => read post = expectedList pre args
  binds     := fun pre args post h => ListDigestBindsList LE cN hN hLE _ _ h
  encodes   := fun pre args post h => listDigest_congr LE cN h

/-- **`funcComponent`** — an `ActiveComponent` for a FUNCTION-field `read : RKS → β` whose digest is an
injective whole-value hash `D : β → ℤ` (realizable — a Poseidon Merkle over the field's canonical
serialization, the same CR bar as `cellLeafInjective`/`listLeafInjective`). `binds`/`encodes` are plain
injectivity. Used for `bal`/`caps` (the post-shape is FULL function equality). -/
def funcComponent {St Args β : Type}
    (read : RecordKernelState → β) (D : β → ℤ) (hD : Function.Injective D)
    (expectedVal : St → Args → β) : ActiveComponent St Args where
  digest    := fun k => D (read k)
  expected  := fun pre args => D (expectedVal pre args)
  postClause := fun pre args post => read post = expectedVal pre args
  binds     := fun pre args post h => hD h
  encodes   := fun pre args post h => congrArg D h

/-- **`keyedComponent`** — an `ActiveComponent` for a keyed function-field over a FIXED finite carrier
`S : Finset κ` (args-independent, so it fits the args-free `digest : RKS → ℤ` interface), whose digest
is the `KeyedCommit.keyedDigest` sponge of the leaf reading `KL : RKS → κ → ℤ`. `binds` is
`KeyedDigestBindsKeys` — POINTWISE on the carrier (`∀ k ∈ S, KL post k = KLexp pre args k`); `encodes`
is `keyedDigest_congr`. For effects whose spec is genuinely keyed-pointwise over a fixed key set
(`expectedVal` may still depend on pre+args; the CARRIER is what must be fixed). -/
def keyedComponent {St Args : Type} {κ : Type} [LinearOrder κ]
    (KL : RecordKernelState → κ → ℤ) (cN : List ℤ → ℤ) (hN : compressNInjective cN)
    (S : Finset κ) (KLexp : St → Args → κ → ℤ) : ActiveComponent St Args where
  digest    := fun k => keyedDigest (KL k) cN S
  expected  := fun pre args => keyedDigest (KLexp pre args) cN S
  postClause := fun pre args post => ∀ k ∈ S, KL post k = KLexp pre args k
  binds     := fun pre args post h => KeyedDigestBindsKeys (KL post) (KLexp pre args) cN hN S h
  encodes   := fun pre args post h => keyedDigest_congr cN S h

/-! ## §3 — `EffectSpec2` (the per-effect data) + the `CommitSurface` it commits over.

We reuse v1's `EffectCommit.StateView` (read kernel + log out of `St`) and `StateCommit`'s `RH`/`LH`
(the rest hash + log hash, as a small `Surface2` of just the two carriers the v2 framework needs — the
component carries its OWN digest internally, so the cell-leaf `CH`/`compressN` live inside the
`ActiveComponent`, not in this surface). The guard fields are VERBATIM v1. -/

/-- **`Surface2`** — the two commitment carriers the v2 framework references directly: the rest hash
`RH` and the log hash `LH`. (The component's sponge/leaf live inside its `ActiveComponent`.) -/
structure Surface2 where
  RH : RecordKernelState → ℤ
  LH : List Turn → ℤ

/-- **`EffectSpec2 St Args`** — the per-effect data for a SINGLE-component non-`cell` effect.

  * `view`      — the `StateView` reading kernel + log out of `St`.
  * `active`    — the ONE touched non-`cell` `ActiveComponent`.
  * `logUpdate` — `none` = frozen log; `some f` = the log GROWS to `f pre args`.
  * `restFrame` — the declarative frame on the UNTOUCHED non-`cell` fields (an effect-specific Prop,
    e.g. `RestIffNoBal`'s 15-field conjunction); bound by the per-effect `RestIffNo*` portal.
  * the guard sub-system fields, VERBATIM v1 (`guardGates`/`guardProp`/`guardWidth`/`guardEncode`/
    `guardLocal`/`guardWidth_le`). -/
structure EffectSpec2 (St Args : Type) where
  view         : StateView St
  active       : ActiveComponent St Args
  logUpdate    : Option (St → Args → List Turn)
  restFrame    : RecordKernelState → RecordKernelState → Prop
  guardGates   : ConstraintSystem
  guardProp    : St → Args → Prop
  guardWidth   : Nat
  guardEncode  : St → Args → St → Assignment
  guardLocal   : ∀ (a b : Assignment), (∀ w, w < guardWidth → a w = b w) →
                   (satisfied guardGates a ↔ satisfied guardGates b)
  guardWidth_le : guardWidth ≤ 64

/-! ## §4 — the derived apex (the full-state declarative spec, DERIVED not supplied). -/

/-- The post log the apex predicts: `pre`'s log if frozen, else `f pre args`. -/
def EffectSpec2.postLog {St Args : Type} (E : EffectSpec2 St Args) (pre : St) (args : Args) :
    List Turn :=
  match E.logUpdate with
  | none   => E.view.getLog pre
  | some f => f pre args

/-- **`EffectSpec2.apex E pre args post`** — the DERIVED full-state declarative spec: the guard holds,
the touched component's `postClause` holds, the log is the predicted post log, and the untouched
non-`cell` fields are frozen (`restFrame`). NO `funext`-over-cells: the component clause IS the
component's `postClause`. -/
def EffectSpec2.apex {St Args : Type} (E : EffectSpec2 St Args) (pre : St) (args : Args) (post : St) :
    Prop :=
  E.guardProp pre args
  ∧ E.active.postClause pre args (E.view.toKernel post)
  ∧ E.view.getLog post = E.postLog pre args
  ∧ E.restFrame (E.view.toKernel pre) (E.view.toKernel post)

/-! ## §5 — the named DIGEST wires (CONCRETE indices) + the encoder.

The digest columns live at FIXED concrete indices `64 .. 71` (guard wires `< 64`, so the two regions
never collide). Concrete indices are the robustness choice — `reduceIte` collapses the literal-condition
cascade automatically (no `omega`-in-`if_neg` tarpit). Eight columns: pre/post root, rest pre/post,
component post/expected, log post/expected. -/

/-- `preRoot`  wire. -/        abbrev vE2PreRoot  : Var := 64
/-- `postRoot` wire. -/        abbrev vE2PostRoot : Var := 65
/-- `restDigPre`  wire. -/     abbrev vE2RestPre  : Var := 66
/-- `restDigPost` wire. -/     abbrev vE2RestPost : Var := 67
/-- `compDigPost`     wire. -/ abbrev vE2CompPost : Var := 68
/-- `compDigExpected` wire. -/ abbrev vE2CompExp  : Var := 69
/-- `logDigPost`     wire. -/  abbrev vE2LogPost  : Var := 70
/-- `logDigExpected` wire. -/  abbrev vE2LogExp   : Var := 71

/-- The full-state effect trace width (guard region `< 64`, digests `64 .. 71`). -/
def EffectSpec2.traceWidth {St Args : Type} (_E : EffectSpec2 St Args) : Nat := 72

/-- **`effectStateCommit2`** — the v2 full-state root: `cmb`-style combine the component digest with
(`RH`-then-`LH`). We keep it as a single opaque sum of the three digests (the EQ gates are the binding
mechanism; the root is for the published-root corollary, not the crown-jewel soundness). -/
def effectStateCommit2 {St Args : Type} (S : Surface2) (E : EffectSpec2 St Args)
    (k : RecordKernelState) (log : List Turn) : ℤ :=
  E.active.digest k + S.RH k + S.LH log

/-- **`encodeE2`** — the full-state effect witness. Wires `0 .. g-1` DELEGATE to the guard sub-system's
`guardEncode`; the eight digest columns at `≥ 64` carry the honest commitment values. The expected
columns commit the SPEC's predicted component + post-log (pure in pre+args; no executor). -/
def encodeE2 {St Args : Type} (S : Surface2) (E : EffectSpec2 St Args)
    (pre : St) (args : Args) (post : St) : Assignment :=
  fun w =>
    if      w = vE2PreRoot  then
      effectStateCommit2 S E (E.view.toKernel pre) (E.view.getLog pre)
    else if w = vE2PostRoot then
      effectStateCommit2 S E (E.view.toKernel post) (E.view.getLog post)
    else if w = vE2RestPre  then S.RH (E.view.toKernel pre)
    else if w = vE2RestPost then S.RH (E.view.toKernel post)
    else if w = vE2CompPost then E.active.digest (E.view.toKernel post)
    else if w = vE2CompExp  then E.active.expected pre args
    else if w = vE2LogPost  then S.LH (E.view.getLog post)
    else if w = vE2LogExp   then S.LH (E.postLog pre args)
    else E.guardEncode pre args post w

/-- **Transport:** on every guard wire (`w < g`) `encodeE2` agrees with `guardEncode`. -/
theorem encodeE2_agrees_guardEncode {St Args : Type} (S : Surface2) (E : EffectSpec2 St Args)
    (pre : St) (args : Args) (post : St) (w : Var) (hw : w < E.guardWidth) :
    encodeE2 S E pre args post w = E.guardEncode pre args post w := by
  have hle := E.guardWidth_le
  unfold encodeE2 Var at *
  simp only [vE2PreRoot, vE2PostRoot, vE2RestPre, vE2RestPost, vE2CompPost, vE2CompExp, vE2LogPost,
    vE2LogExp]
  split_ifs <;> first | rfl | (exfalso; omega)

/-! ### §5b — digest wire lookups (the `if`-cascade collapsed at each digest index). -/

/-- The ONE robust lookup tactic (concrete indices ⇒ `reduceIte` collapses the cascade). -/
macro "ec2_lookup" : tactic =>
  `(tactic| simp [encodeE2, vE2PreRoot, vE2PostRoot, vE2RestPre, vE2RestPost, vE2CompPost, vE2CompExp,
      vE2LogPost, vE2LogExp])

section Lookups
variable {St Args : Type} (S : Surface2) (E : EffectSpec2 St Args) (pre : St) (args : Args) (post : St)

theorem enc2_restPre :
    encodeE2 S E pre args post vE2RestPre = S.RH (E.view.toKernel pre) := by ec2_lookup
theorem enc2_restPost :
    encodeE2 S E pre args post vE2RestPost = S.RH (E.view.toKernel post) := by ec2_lookup
theorem enc2_compPost :
    encodeE2 S E pre args post vE2CompPost = E.active.digest (E.view.toKernel post) := by ec2_lookup
theorem enc2_compExp :
    encodeE2 S E pre args post vE2CompExp = E.active.expected pre args := by ec2_lookup
theorem enc2_logPost :
    encodeE2 S E pre args post vE2LogPost = S.LH (E.view.getLog post) := by ec2_lookup
theorem enc2_logExp :
    encodeE2 S E pre args post vE2LogExp = S.LH (E.postLog pre args) := by ec2_lookup

end Lookups

/-! ## §6 — the three frame-forcing EQ gates + `satisfiedE2`.

We ALWAYS emit `cE2Log` (frozen-log effects make it the trivial `LH pre = LH pre`) so the gate list is
match-FREE → the concrete `#guard`s stay decidable. -/

/-- **Rest-frame gate:** `restDigPre = restDigPost`. -/
def cE2RestF : Constraint := { lhs := .var vE2RestPre, rhs := .var vE2RestPost }
/-- **Component-bind gate:** `compDigPost = compDigExpected`. -/
def cE2Bind  : Constraint := { lhs := .var vE2CompPost, rhs := .var vE2CompExp }
/-- **Log-bind gate:** `logDigPost = logDigExpected`. -/
def cE2Log   : Constraint := { lhs := .var vE2LogPost, rhs := .var vE2LogExp }

/-- **The full-state v2 effect circuit** — the guard gates ++ the three frame-forcing EQ gates. The
three EQ gates pin the WHOLE post-state (rest-frame ∧ component ∧ log); the guard gates pin
admissibility. -/
def effectCircuit2 {St Args : Type} (E : EffectSpec2 St Args) : ConstraintSystem :=
  E.guardGates ++ [cE2RestF, cE2Bind, cE2Log]

/-- **`satisfiedE2 S E a`** — the full-state v2 satisfaction predicate. -/
def satisfiedE2 {St Args : Type} (_S : Surface2) (E : EffectSpec2 St Args) (a : Assignment) : Prop :=
  satisfied (effectCircuit2 E) a

/-! ### §6b — the three frame-gate ↔ digest-equality lemmas. -/

section GateIff
variable {St Args : Type} (S : Surface2) (E : EffectSpec2 St Args) (pre : St) (args : Args) (post : St)

/-- `cE2RestF` holds under `encodeE2` IFF the rest hashes agree. -/
theorem e2rest_iff :
    cE2RestF.holds (encodeE2 S E pre args post)
      ↔ S.RH (E.view.toKernel pre) = S.RH (E.view.toKernel post) := by
  unfold Constraint.holds cE2RestF
  simp only [Expr.eval, enc2_restPre, enc2_restPost]

/-- `cE2Bind` holds under `encodeE2` IFF the post component digest equals the spec-expected one. -/
theorem e2bind_iff :
    cE2Bind.holds (encodeE2 S E pre args post)
      ↔ E.active.digest (E.view.toKernel post) = E.active.expected pre args := by
  unfold Constraint.holds cE2Bind
  simp only [Expr.eval, enc2_compPost, enc2_compExp]

/-- `cE2Log` holds under `encodeE2` IFF the post log hash equals the spec-predicted post log hash. -/
theorem e2log_iff :
    cE2Log.holds (encodeE2 S E pre args post)
      ↔ S.LH (E.view.getLog post) = S.LH (E.postLog pre args) := by
  unfold Constraint.holds cE2Log
  simp only [Expr.eval, enc2_logPost, enc2_logExp]

end GateIff

/-! ## §7 — the generic crown-jewel theorems (proved ONCE).

`effect2_circuit_full_sound` is the literal generalization of v1's `effect_circuit_full_sound`, with the
touched-cell `funext` REPLACED by the component's `binds` (which delivers the `postClause` directly).
The frame is bound by the per-effect `RestIffNo*` portal, carried as the `→`/`←` of `restFrame` over the
rest hash. NO `AccountsWF`, NO cell `funext`. -/

/-- Per-effect GUARD obligation (the `→`): the guard gates, on the guard's own witness, decode. -/
def GuardDecodes2 {St Args : Type} (E : EffectSpec2 St Args) : Prop :=
  ∀ (pre : St) (args : Args) (post : St),
    satisfied E.guardGates (E.guardEncode pre args post) → E.guardProp pre args

/-- Per-effect GUARD obligation (the `←`, for completeness). -/
def GuardEncodes2 {St Args : Type} (E : EffectSpec2 St Args) : Prop :=
  ∀ (pre : St) (args : Args) (post : St),
    E.guardProp pre args → satisfied E.guardGates (E.guardEncode pre args post)

/-- Per-effect REST-FRAME portal (the `→`): equal rest hashes force the untouched-field frame. The
soundness side of the per-effect `RestIffNo*`. -/
def RestFrameDecodes2 {St Args : Type} (S : Surface2) (E : EffectSpec2 St Args) : Prop :=
  ∀ k k' : RecordKernelState, S.RH k = S.RH k' → E.restFrame k k'

/-- Per-effect REST-FRAME portal (the `←`, for completeness): the frame forces equal rest hashes. -/
def RestFrameEncodes2 {St Args : Type} (S : Surface2) (E : EffectSpec2 St Args) : Prop :=
  ∀ k k' : RecordKernelState, E.restFrame k k' → S.RH k = S.RH k'

section Sound
variable {St Args : Type} (S : Surface2) (E : EffectSpec2 St Args)

/-- **`effect2_circuit_full_sound` — the generic v2 crown jewel.** A satisfying full-state witness pins
the WHOLE post-state: the effect's `apex` holds (guard ∧ component `postClause` ∧ log ∧ frame). The
component `postClause` comes from `E.active.binds` fed the `cE2Bind` digest equality (NO `funext`); the
frame from the `RestIffNo*` portal; the log from `logHashInjective`. Carries only the per-effect
`RestFrameDecodes2` + `logHashInjective` + `GuardDecodes2` (the component's `binds`/`encodes` are FIELDS,
discharged by its smart constructor). -/
theorem effect2_circuit_full_sound
    (hRestF : RestFrameDecodes2 S E) (hLog : logHashInjective S.LH)
    (hGuard : GuardDecodes2 E)
    (pre : St) (args : Args) (post : St)
    (h : satisfiedE2 S E (encodeE2 S E pre args post)) :
    E.apex pre args post := by
  have hArith : satisfied (effectCircuit2 E) (encodeE2 S E pre args post) := h
  -- guard:
  have hguardSat : satisfied E.guardGates (encodeE2 S E pre args post) := by
    intro c hc; exact hArith c (by unfold effectCircuit2; exact List.mem_append_left _ hc)
  have hguardSat' : satisfied E.guardGates (E.guardEncode pre args post) :=
    (E.guardLocal _ _ (fun w hw => encodeE2_agrees_guardEncode S E pre args post w hw)).mp hguardSat
  have hguard : E.guardProp pre args := hGuard pre args post hguardSat'
  -- the three frame-forcing EQ gates hold:
  have hrest : cE2RestF.holds (encodeE2 S E pre args post) := hArith cE2RestF (by simp [effectCircuit2])
  have hbind : cE2Bind.holds (encodeE2 S E pre args post)  := hArith cE2Bind  (by simp [effectCircuit2])
  have hlog  : cE2Log.holds (encodeE2 S E pre args post)   := hArith cE2Log   (by simp [effectCircuit2])
  -- decode: rest-frame, component postClause, log.
  have hframe : E.restFrame (E.view.toKernel pre) (E.view.toKernel post) :=
    hRestF _ _ ((e2rest_iff S E pre args post).mp hrest)
  have hcomp : E.active.postClause pre args (E.view.toKernel post) :=
    E.active.binds pre args (E.view.toKernel post) ((e2bind_iff S E pre args post).mp hbind)
  have hlogVal : E.view.getLog post = E.postLog pre args :=
    hLog _ _ ((e2log_iff S E pre args post).mp hlog)
  exact ⟨hguard, hcomp, hlogVal, hframe⟩

/-- **`effect2_circuit_full_complete`** — every apex-satisfying step yields a satisfying full-state
witness. The three EQ gates are discharged from the apex's component/frame/log clauses; the guard gates
from `GuardEncodes2`. -/
theorem effect2_circuit_full_complete
    (hRestF : RestFrameEncodes2 S E) (hGuardEnc : GuardEncodes2 E)
    (pre : St) (args : Args) (post : St)
    (hspec : E.apex pre args post) :
    satisfiedE2 S E (encodeE2 S E pre args post) := by
  obtain ⟨hguard, hcomp, hlogVal, hframe⟩ := hspec
  show satisfied (effectCircuit2 E) (encodeE2 S E pre args post)
  intro c hc
  rcases List.mem_append.mp hc with hcg | hc3
  · -- a guard gate
    have hge : satisfied E.guardGates (encodeE2 S E pre args post) :=
      (E.guardLocal _ _ (fun w hw => encodeE2_agrees_guardEncode S E pre args post w hw)).mpr
        (hGuardEnc pre args post hguard)
    exact hge c hcg
  · -- one of the three EQ gates
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc3
    rcases hc3 with rfl | rfl | rfl
    · exact (e2rest_iff S E pre args post).mpr (hRestF _ _ hframe)
    · exact (e2bind_iff S E pre args post).mpr (E.active.encodes pre args (E.view.toKernel post) hcomp)
    · exact (e2log_iff S E pre args post).mpr (by rw [hlogVal])

/-! ### Anti-ghost teeth (each forgery a single EQ gate REJECTS). -/

/-- **frame tamper REJECTED:** a post-state whose untouched-frame predicate FAILS against `pre` cannot
satisfy — `cE2RestF` + the `RestIffNo*` portal force `E.restFrame pre post`. -/
theorem effectCircuit2_rejects_frame_tamper (hRestF : RestFrameDecodes2 S E)
    (pre : St) (args : Args) (post : St)
    (htamper : ¬ E.restFrame (E.view.toKernel pre) (E.view.toKernel post)) :
    ¬ satisfiedE2 S E (encodeE2 S E pre args post) := by
  intro h
  have hrest : cE2RestF.holds (encodeE2 S E pre args post) := h cE2RestF (by simp [effectCircuit2])
  exact htamper (hRestF _ _ ((e2rest_iff S E pre args post).mp hrest))

/-- **wrong-component REJECTED:** a post-state whose touched component VIOLATES its `postClause` cannot
satisfy — `cE2Bind` + `active.binds` contrapositive. A wrong post-list / wrong-keyed-value is rejected. -/
theorem effectCircuit2_rejects_wrong_component
    (pre : St) (args : Args) (post : St)
    (htamper : ¬ E.active.postClause pre args (E.view.toKernel post)) :
    ¬ satisfiedE2 S E (encodeE2 S E pre args post) := by
  intro h
  have hbind : cE2Bind.holds (encodeE2 S E pre args post) := h cE2Bind (by simp [effectCircuit2])
  exact htamper (E.active.binds pre args (E.view.toKernel post) ((e2bind_iff S E pre args post).mp hbind))

/-- **log forgery REJECTED:** a post-log differing from the spec-predicted post-log cannot satisfy —
`cE2Log` + `logHashInjective`. -/
theorem effectCircuit2_rejects_log_forge (hLog : logHashInjective S.LH)
    (pre : St) (args : Args) (post : St)
    (htamper : E.view.getLog post ≠ E.postLog pre args) :
    ¬ satisfiedE2 S E (encodeE2 S E pre args post) := by
  intro h
  have hlog : cE2Log.holds (encodeE2 S E pre args post) := h cE2Log (by simp [effectCircuit2])
  exact htamper (hLog _ _ ((e2log_iff S E pre args post).mp hlog))

end Sound

/-! ## §8 — emission. -/

/-- The emitted v2 effect circuit (serialized via `CircuitEmit.emit`). -/
def emittedEffect2 {St Args : Type} (name : String) (E : EffectSpec2 St Args) : EmittedDescriptor :=
  emit name E.traceWidth (effectCircuit2 E)

/-- **`emitEffect2Faithful`** — satisfying the emitted v2 effect circuit is EXACTLY satisfying
`effectCircuit2 E`. -/
theorem emitEffect2Faithful {St Args : Type} (name : String) (E : EffectSpec2 St Args)
    (a : Assignment) :
    satisfied (effectCircuit2 E) a ↔ satisfiedEmitted (emittedEffect2 name E) a :=
  emit_faithful name E.traceWidth (effectCircuit2 E) a

/-! ## §9 — axiom-hygiene tripwires. -/

#assert_axioms encodeE2_agrees_guardEncode
#assert_axioms e2rest_iff
#assert_axioms e2bind_iff
#assert_axioms e2log_iff
#assert_axioms effect2_circuit_full_sound
#assert_axioms effect2_circuit_full_complete
#assert_axioms effectCircuit2_rejects_frame_tamper
#assert_axioms effectCircuit2_rejects_wrong_component
#assert_axioms effectCircuit2_rejects_log_forge
#assert_axioms emitEffect2Faithful

end Dregg2.Circuit.EffectCommit2
