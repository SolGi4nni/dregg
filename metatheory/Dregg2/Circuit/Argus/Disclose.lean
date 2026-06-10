/-
# Dregg2.Circuit.Argus.Disclose — welding the Argus IR to the DISCLOSE protocol layer (the privacy dial).

The Argus cornerstone (`Argus/Stmt.lean`) makes the executor the meaning of a `RecStmt` term: a
per-effect term's `interp` IS the verified executor / kernel transition. The per-effect welds
(`Argus/Effects/*.lean`) pin each effect's *whole post-state*. What those welds produce is **Q** —
the Argus-produced `RecordKernelState`, the cell records a turn writes.

This module welds that produced state to the **Q-PROJECTION FAMILY** — the privacy dial. The dial
governs *what a verifier learns from Q*: not the whole produced state, but a **projection** of it,
tuned by a disclosure tier `{trusted, selective, private}`. We REUSE three existing layer modules
VERBATIM — we do NOT re-derive their soundness:

  * **`Dregg2.Privacy`** — the field-visibility projection `project : State → FieldVisibility → Obs`
    and its hiding law `field_projection_hides_private` (the public view is independent of private
    fields). This is the projection mechanism; the dial is a family of `FieldVisibility` masks over it.
  * **`Dregg2.Authority.SelectiveDisclosure`** — the credential `observerView` (disclosed subset ⊕
    proven predicates), the same `Privacy.project` idiom at the presentation layer.
  * **`Dregg2.Apps.VerificationToolkit`** — `app_commit_iff_admit` (a guarded write commits IFF the
    app's admission predicate holds). This is the userspace `Verify` the dial rides: the disclosed Q is
    what a verifier checks the app invariant against.

## What this file PROVES — the connection (the Argus-produced state IS what the dial projects)

  1. **`DiscloseAt` is the Q-projection family** (§2). Read an Argus cell record as a
     `Privacy.State FieldName Int` (`cellView`, the field-wise `fieldOf` read), and project it through a
     tier's `FieldVisibility` mask. The three tiers `{trusted, selective, private}` are concrete masks.

  2. **`DiscloseAt` IS A PROJECTION of Q** (§3) — the load-bearing connection:
       * **idempotent** (`disclose_idempotent`): re-disclosing a disclosed view changes nothing — a
         genuine projection (its image is a fixed sub-lattice of Q).
       * **hides private fields** (`disclose_hides_private`): the disclosed view is INDEPENDENT of the
         private fields of the Argus output — directly `Privacy.field_projection_hides_private`, lifted
         onto the Argus cell. So two Argus states agreeing on the public fields are indistinguishable.
       * **the dial is a refinement chain** (`disclose_refines`): `trusted ⊒ selective ⊒ private` — each
         coarser tier reveals a SUBSET of what the finer one does (the privacy lattice order).
       * **`private` = the greatest lower bound** (`private_is_glb`): the private tier collapses EVERY
         Argus state to the SAME (empty) view — the ⊥ of the dial, information-theoretic hiding of the
         whole produced state. Non-vacuous: `trusted` is above it (`trusted_separates`).

  3. **The projection is OF THE ARGUS OUTPUT** (§4) — threading the cornerstone. A committed Argus
     transfer (`interp (transferStmt turn) k = some k'`, = `recKExec` by the cornerstone) produces a Q
     whose **trusted disclosure REVEALS the proven post-balance** (`disclose_transfer_reveals_balance`)
     and whose **private disclosure HIDES it** (`disclose_transfer_private_hides`) — the dial projects
     the *genuine verified post-state*, not a stand-in. This is the weld: the layer talks about the
     state the Argus term provably produced.

  4. **Userspace `Verify` rides Q** (§5) — the bridge to `VerificationToolkit`. An Argus `setFieldStmt`
     commit IS a `stateStepGuarded` commit (the `SetField` weld), so `app_commit_iff_admit` fires: the
     committed Q satisfies the app's admission predicate (`disclose_app_invariant_rides_Q`, `Q ⟹
     app_invariant`), AND the selective disclosure of Q reveals exactly the gated slot the verifier
     checks (`disclose_app_reveals_gated_slot`). So the verifier reads the disclosed Q and confirms the
     userspace invariant — the dial and the app admission decide the same committed transitions.

## SCOPE — what connects vs the named GAP (do NOT over-read)

  * **CONNECTS.** The Argus-produced `RecordKernelState` (the cornerstone/weld output) IS the object
    the dial projects: every theorem here is stated over `interp (…Stmt …) k` (or the chained executor),
    routed through the *existing* `interp_transferStmt_eq_recKExec` / `SetField` weld / `app_commit_iff_
    admit` — never re-deriving them. The projection LAWS (idempotent / hides-private / refinement / GLB)
    are the `Privacy.project` laws lifted onto the Argus cell, PROVED, non-vacuous.

  * **THE NAMED GAP — the *computational* hiding is a §8 portal, NOT proved here.** `Privacy.lean`'s
    own header is explicit: `project` proves **information-theoretic** field hiding (the public view is a
    function only of the public fields). The COMPUTATIONAL indistinguishability of the REAL on-chain
    transcript — that a PPT verifier observing the published commitment/STARK cannot recover a private
    field — is the cryptographic obligation carried by `Crypto/Primitives.lean::CryptoPrimitives` /
    `CryptoKernel.collisionHard` / the EffectVM commitment binding, and is NEVER discharged in this Lean
    weld. Concretely: this module proves the dial is a faithful projection of the Argus *Lean state* and
    that the verifier's view collapses on the private tier; it does NOT prove the ZK circuit leaks
    nothing. That boundary is the SAME one `Privacy.lean` §8 / `SelectiveDisclosure.lean` §8 declare —
    the projection is honest at the state layer, the crypto advantage bound stays the named portal.

`#assert_axioms` on the keystone (`disclose_hides_private`) ⊆ {propext, Classical.choice, Quot.sound};
no `sorry`, no `:= True`, no vacuity. Imports are READ-ONLY; this file OWNS only its own declarations
(it does not edit Stmt/Compile/Guard/Turn/Policy/RecordKernel or any Effects/* — it imports them).
-/
import Dregg2.Circuit.Argus.Stmt
import Dregg2.Circuit.Argus.Effects.SetField
import Dregg2.Privacy
import Dregg2.Authority.SelectiveDisclosure
import Dregg2.Apps.VerificationToolkit

namespace Dregg2.Circuit.Argus.Disclose

open Dregg2.Exec
open Dregg2.Circuit.Argus (RecStmt interp transferStmt transferGuard interp_transferStmt_eq_recKExec)
-- The privacy projection mechanism (the dial rides this) — `project`, the field-visibility masks, and
-- the information-theoretic hiding law. REUSED, not re-derived.
open Dregg2.Privacy (Visibility FieldVisibility State Obs project field_projection_hides_private)
-- The single-cell field read (`fieldOf f (k.cell c)`), the measure the cell-view projects.
open Dregg2.Exec.EffectsState (fieldOf setField stateStep stateStepGuarded)

set_option autoImplicit false

/-! ## §1 — Q: the Argus-produced cell record, read as a `Privacy.State`.

The Argus cornerstone / per-effect welds produce a `RecordKernelState`. The privacy dial does not
project the whole kernel; it projects what a verifier learns about a CELL — the per-field record a
turn writes. `cellView k c` reads cell `c`'s record (an Argus output) as a `Privacy.State FieldName
Int`: the field-wise scalar read `fieldOf f (k.cell c)`, the SAME measure `balOf`/`nonceOf`/the
`SetField` weld use. This is the bridge object — the Argus Q in the language the dial speaks. -/

/-- **`cellView k c`** — the Argus-produced cell `c`, read as a `Privacy.State FieldName Int`: each
field name maps to its scalar value `fieldOf f (k.cell c)`. The whole post-state `k` is the Argus Q;
this is its per-cell projection into the field-visibility world the dial projects further. -/
def cellView (k : RecordKernelState) (c : CellId) : State FieldName Int :=
  fun f => fieldOf f (k.cell c)

/-- `cellView` reads back exactly the cell's field scalar (definitional — the bridge does not reshape
the value, it only re-types the field read as a `Privacy.State`). -/
@[simp] theorem cellView_apply (k : RecordKernelState) (c : CellId) (f : FieldName) :
    cellView k c f = fieldOf f (k.cell c) := rfl

/-! ## §2 — The Q-PROJECTION FAMILY: the `{trusted, selective, private}` privacy dial.

A disclosure tier is a `FieldVisibility FieldName` — a per-field `pub`/`priv` mask (`Privacy.lean`
tier 1). The dial is the family of three canonical masks:

  * **`trusted`** — EVERY field public. The verifier is fully trusted; the disclosed view is all of Q.
  * **`selective sel`** — exactly the fields in the predicate `sel` are public, the rest private. The
    selective-disclosure tier (a chosen subset travels, the `SelectiveDisclosure` `disclose` mask).
  * **`sovereign`** — EVERY field private (the fully-private tier; `private` is a Lean keyword). The
    verifier learns NOTHING; the disclosed view is `⊥`.

`DiscloseAt tier k c` is then `project (cellView k c) tier` — the verifier's view of the Argus cell at
that tier. This is the dial: ONE Argus Q, a family of projections of it indexed by trust. -/

/-- The disclosure tier — the dial setting. `trusted` reveals all, `sovereign` reveals none,
`selective` reveals a chosen field subset (the `Privacy.FieldVisibility` mask the tier induces, §2.1). -/
inductive Tier where
  /-- Fully trusted verifier: every field public. -/
  | trusted
  /-- Selective disclosure: exactly the `sel`-true fields public, the rest withheld. -/
  | selective (sel : FieldName → Bool)
  /-- Fully private ("sovereign" — every field withheld); the verifier learns nothing. The constructor
  is named `sovereign` because `private` is a Lean keyword, and it is the dregg vocabulary for a
  fully-self-owned/withheld cell view. -/
  | sovereign

/-- **`Tier.mask`** — the `FieldVisibility` a tier induces (the dial setting as a per-field mask).
`trusted` is the constant `pub`; `sovereign` the constant `priv`; `selective sel` is `pub` exactly on
the `sel`-true fields. The bridge from the dial to the `Privacy.project` mechanism. -/
def Tier.mask : Tier → FieldVisibility FieldName
  | .trusted       => fun _ => Visibility.pub
  | .selective sel => fun f => if sel f then Visibility.pub else Visibility.priv
  | .sovereign     => fun _ => Visibility.priv

/-- **`DiscloseAt tier k c`** — what a verifier at disclosure `tier` learns from the Argus-produced
cell `c`: project `cellView k c` (the Argus Q) through the tier's mask. The Q-projection family — one
produced state, a dial of projections of it. -/
def DiscloseAt (tier : Tier) (k : RecordKernelState) (c : CellId) : Obs FieldName Int :=
  project (cellView k c) tier.mask

/-- `DiscloseAt` unfolds to a `project` of the cell-view under the tier mask (the definitional bridge
the projection laws below read off). -/
@[simp] theorem discloseAt_eq (tier : Tier) (k : RecordKernelState) (c : CellId) :
    DiscloseAt tier k c = project (cellView k c) tier.mask := rfl

/-! ## §3 — `DiscloseAt` IS A PROJECTION OF Q (the load-bearing layer connection).

A *projection* of the Argus state must satisfy the projection laws: it lands in a fixed sub-lattice
(idempotent), it is determined only by the revealed coordinates (hides the rest), and the dial settings
form a refinement order with `private` at the bottom (reveals nothing). We prove all four, lifting the
`Privacy.project` laws onto the Argus cell-view. -/

/-! ### §3.1 — IDEMPOTENT: re-disclosing a disclosed view changes nothing.

A projection `π` satisfies `π ∘ π = π`. Here `DiscloseAt tier` projects an Argus cell to an `Obs`;
projecting the *same mask* again (over the `Obs`-derived state where absent fields read `0`) lands the
same view. We state idempotence the way it bites for a privacy dial: applying the tier's mask twice to
the underlying cell-view is the single application — the disclosed view is a FIXED POINT of its own
tier, i.e. its image is a sub-lattice of Q closed under the projection. -/

/-- The view-state of a disclosure: the `Obs` read back as a `State` (absent/private fields read `0`,
the public ones their disclosed value). The carrier on which "re-disclose" acts. -/
def viewState (o : Obs FieldName Int) : State FieldName Int := fun f => (o f).getD 0

/-- **`disclose_idempotent` (a genuine projection).** Disclosing the Argus cell at a tier,
then RE-disclosing the result at the SAME tier, yields the SAME view: `DiscloseAt` is idempotent. So
its image is a fixed sub-lattice of Q — the defining property of a projection (what the verifier learns
is closed under re-projection; disclosing twice reveals nothing new). -/
theorem disclose_idempotent (tier : Tier) (k : RecordKernelState) (c : CellId) :
    project (viewState (DiscloseAt tier k c)) tier.mask = DiscloseAt tier k c := by
  funext f
  simp only [DiscloseAt, project, viewState]
  -- on a public field the inner `project` already revealed `cellView k c f`, so the outer read is the
  -- same `some`; on a private field both layers are `none`. `split` on the mask value closes both.
  split <;> rfl

/-! ### §3.2 — HIDES PRIVATE FIELDS (the keystone): the disclosed view is independent of the
private fields of the Argus output.

This is the headline projection property — the verifier learns the public part of Q and provably
NOTHING about the private part. It is EXACTLY `Privacy.field_projection_hides_private`, lifted onto the
Argus cell-view: two Argus-produced states whose cells agree on every PUBLIC field have the SAME
disclosed view, whatever their private fields. We REUSE the layer's proof — no re-derivation. -/

/-- **`disclose_hides_private` (THE KEYSTONE).** If two Argus-produced states `k`, `k'` have
cells whose PUBLIC fields agree (every `f` with `tier.mask f = pub` reads the same scalar), their
disclosures at that tier are EQUAL — independent of the private fields. So the dial reveals the public
projection of Q and hides the rest: the load-bearing connection, the `Privacy.project` hiding law
riding the Argus output. Reuses `field_projection_hides_private` verbatim. -/
theorem disclose_hides_private (tier : Tier) (k k' : RecordKernelState) (c : CellId)
    (hpub : ∀ f, tier.mask f = Visibility.pub → fieldOf f (k.cell c) = fieldOf f (k'.cell c)) :
    DiscloseAt tier k c = DiscloseAt tier k' c :=
  field_projection_hides_private tier.mask (cellView k c) (cellView k' c) hpub

/-! ### §3.3 — THE DIAL IS A REFINEMENT CHAIN: `trusted ⊒ selective ⊒ private`.

The dial settings are partially ordered by "reveals at least as much": `t₁ ⊑ t₂` iff every field
`t₁` makes public, `t₂` also makes public (so `t₂`'s view determines `t₁`'s). On the canonical masks
this is the chain `private ⊑ selective sel ⊑ trusted`: `private` reveals ∅, `trusted` reveals all, and
any `selective` sits between. We pin the two strict steps a privacy dial cares about. -/

/-- `t₁ ⊑ t₂` — `t₂` reveals at least every field `t₁` reveals (so `t₂`'s disclosure refines `t₁`'s).
Pointwise on the masks: `pub` under `t₁` ⟹ `pub` under `t₂`. -/
def Tier.RevealsLE (t₁ t₂ : Tier) : Prop :=
  ∀ f, t₁.mask f = Visibility.pub → t₂.mask f = Visibility.pub

/-- **`private_le_selective`.** `private ⊑ selective sel` for ANY `sel`: the private tier
reveals nothing, so it trivially reveals no more than a selective tier. The bottom step of the dial. -/
theorem private_le_selective (sel : FieldName → Bool) :
    Tier.RevealsLE .sovereign (.selective sel) := by
  intro f hf; simp only [Tier.mask] at hf; exact absurd hf (by simp)

/-- **`selective_le_trusted`.** `selective sel ⊑ trusted` for ANY `sel`: the trusted tier
reveals every field, so it reveals at least every field a selective tier does. The top step. Together
with `private_le_selective` this is the dial chain `private ⊑ selective ⊑ trusted`. -/
theorem selective_le_trusted (sel : FieldName → Bool) :
    Tier.RevealsLE (.selective sel) .trusted := by
  intro f _; rfl

/-- **`disclose_refines` (a coarser tier's view is determined by a finer tier's).** If `t₁ ⊑
t₂`, then on a field `t₁` reveals, `t₁`'s disclosed value EQUALS `t₂`'s — so the coarser disclosure is
a restriction of the finer one. The information-monotonicity of the dial: turning the dial toward
`trusted` only ever ADDS revealed fields, never changes or hides an already-revealed one. -/
theorem disclose_refines {t₁ t₂ : Tier} (hle : Tier.RevealsLE t₁ t₂)
    (k : RecordKernelState) (c : CellId) (f : FieldName) (hf : t₁.mask f = Visibility.pub) :
    DiscloseAt t₁ k c f = DiscloseAt t₂ k c f := by
  simp only [DiscloseAt, project]
  rw [hf, hle f hf]

/-! ### §3.4 — `private` IS THE GREATEST LOWER BOUND (⊥): it collapses EVERY Argus state to one view.

The bottom of the dial reveals nothing: at `private`, the disclosed view is the constant `none` —
INDEPENDENT of the Argus output entirely. So every produced Q (every reachable post-state, however the
effects moved balances/fields) collapses to the SAME view — perfect (information-theoretic) hiding of
the whole cell. This is the GLB: no tier reveals less, and it forgets all of Q. -/

/-- **`private_collapses_all` (⊥ — the GLB of the dial).** At the `private` tier, the
disclosure of ANY Argus-produced cell is the constant empty view `fun _ => none` — independent of `k`,
`c`, and every field. So every produced state collapses to ONE view: the private tier is the greatest
lower bound of the dial (reveals nothing about Q). -/
theorem private_collapses_all (k : RecordKernelState) (c : CellId) :
    DiscloseAt .sovereign k c = (fun _ => none) := by
  funext f; simp only [DiscloseAt, project, Tier.mask]

/-- **`private_is_glb` (the GLB law).** ANY two Argus states have the SAME private
disclosure of ANY two cells — the private tier is the bottom element: it forgets the whole produced Q
(and is the lower bound below `private_le_selective`/`selective_le_trusted`). -/
theorem private_is_glb (k k' : RecordKernelState) (c c' : CellId) :
    DiscloseAt .sovereign k c = DiscloseAt .sovereign k' c' := by
  rw [private_collapses_all, private_collapses_all]

/-! ## §4 — THE WELD: the dial projects the GENUINE VERIFIED ARGUS OUTPUT.

§3 proved `DiscloseAt` is a projection; this section proves it is a projection OF THE ARGUS Q — the
state the cornerstone provably produces. We thread `interp (transferStmt turn) k = some k'` (= `recKExec`
by `interp_transferStmt_eq_recKExec`) into the dial: the verified post-balance the transfer writes is
exactly what the `trusted` disclosure reveals, and exactly what the `private` disclosure hides. The
layer talks about the Argus output, not a stand-in. -/

/-- The post-state cell `c` of a committed Argus transfer reads back the verified post-balance: this is
the cornerstone (`interp = recKExec`) projected onto cell `c`'s `balance` field. The bridge fact the
weld reads — a committed Argus transfer's Q has a determinate `balance` at each affected cell. -/
theorem transfer_post_balance {turn : Turn} {k k' : RecordKernelState}
    (h : interp (transferStmt turn) k = some k') :
    fieldOf balanceField (k'.cell turn.src)
      = balOf (recTransfer k.cell turn.src turn.dst turn.amt turn.src) := by
  -- the cornerstone turns the IR term into the verified `recKExec`; `recKExec`'s commit case (the only
  -- way it returns `some`) pins `k'.cell = recTransfer …`. `split` opens its `if` on the actual Prop.
  rw [interp_transferStmt_eq_recKExec, recKExec] at h
  split at h
  · -- ADMIT: `h : some { k with cell := recTransfer … } = some k'`, so `k'.cell turn.src` is the move;
    -- `fieldOf balanceField` IS `balOf` (both read `(·.scalar balanceField).getD 0`).
    simp only [Option.some.injEq] at h
    subst h
    rfl
  · exact absurd h (by simp)

/-- **`disclose_transfer_reveals_balance` (the dial reveals the VERIFIED output).** On a
committed Argus transfer (`interp (transferStmt turn) k = some k'`), the `trusted` disclosure of the
source cell reveals exactly the verified post-balance the transfer wrote: `DiscloseAt .trusted k'
turn.src "balance" = some (post-balance)`. So the dial projects the GENUINE state the Argus cornerstone
produces — the verifier at `trusted` learns the proven post-balance, not a placeholder. -/
theorem disclose_transfer_reveals_balance {turn : Turn} {k k' : RecordKernelState}
    (h : interp (transferStmt turn) k = some k') :
    DiscloseAt .trusted k' turn.src balanceField
      = some (balOf (recTransfer k.cell turn.src turn.dst turn.amt turn.src)) := by
  simp only [DiscloseAt, project, Tier.mask, cellView]
  rw [transfer_post_balance h]

/-- **`disclose_transfer_private_hides` (the dial HIDES the verified output).** On the SAME
committed Argus transfer, the `private` disclosure of the source cell reveals `none` for the balance —
the privacy dial hides the very post-balance `trusted` exposed. So the same Argus Q is fully revealed
or fully hidden by turning the dial, and the hiding is genuine over the verified output. -/
theorem disclose_transfer_private_hides {turn : Turn} {k k' : RecordKernelState}
    (_h : interp (transferStmt turn) k = some k') :
    DiscloseAt .sovereign k' turn.src balanceField = none := by
  -- the `sovereign` mask makes EVERY field private, so the disclosure is `none` — independent of `_h`
  -- (the hiding holds over WHATEVER Argus produced; `_h` names that `k'` is the committed output).
  simp only [DiscloseAt, project, Tier.mask]

/-- **`disclose_transfer_dial_is_two_valued` (the dial moves on the Argus output).**
On a committed Argus transfer, the `trusted` and `private` disclosures of the source balance DIFFER (one
is `some post-bal`, the other `none`). So the dial is non-vacuous over the verified Q: the privacy
setting changes what the verifier learns about the state the Argus term produced. -/
theorem disclose_transfer_dial_is_two_valued {turn : Turn} {k k' : RecordKernelState}
    (h : interp (transferStmt turn) k = some k') :
    DiscloseAt .trusted k' turn.src balanceField
      ≠ DiscloseAt .sovereign k' turn.src balanceField := by
  rw [disclose_transfer_reveals_balance h, disclose_transfer_private_hides h]
  simp

/-! ## §5 — USERSPACE `Verify` RIDES Q (the bridge to `VerificationToolkit`).

The dial decides what a verifier SEES; the toolkit's `app_commit_iff_admit` decides what an app
ADMITS. The connection: an Argus `setFieldStmt` commit IS a `stateStepGuarded` commit (the `SetField`
weld), so the toolkit fires — the committed Argus Q satisfies the app's admission predicate (`Q ⟹
app_invariant`), and the selective disclosure of Q reveals exactly the slot the app gated, which the
verifier reads to confirm the invariant. The dial and the app admission decide the SAME committed
transitions over the SAME Argus output. -/

open Dregg2.Apps.VerificationToolkit (AppSpec app_commit_iff_admit app_commit_field_written)

/-- The selective tier that reveals exactly ONE field `f` (the app's gated slot) and hides the rest —
the disclosure a verifier uses to read off the app invariant from Q without seeing the rest of the cell. -/
def onlyField (f : FieldName) : Tier := .selective (fun g => g == f)

/-- The `onlyField f` mask reveals `f` (public). The reduction the toolkit-ride proofs read off. -/
@[simp] theorem onlyField_mask_self (f : FieldName) : (onlyField f).mask f = Visibility.pub := by
  simp only [onlyField, Tier.mask, beq_self_eq_true, if_pos]

/-- The `onlyField f` mask hides any OTHER field `g ≠ f` (private). -/
theorem onlyField_mask_other {f g : FieldName} (hg : g ≠ f) :
    (onlyField f).mask g = Visibility.priv := by
  simp only [onlyField, Tier.mask]
  rw [if_neg (by simpa using hg)]

/-- **`disclose_app_invariant_rides_Q` (`Q ⟹ app_invariant`).** Suppose an Argus `setFieldStmt`
on the app's slot/cell commits at the chained executor — i.e. the toolkit's caveat-gated write
`stateStepGuarded` commits to `s'` (the `SetField` weld's executor surface). Then by the toolkit
`app_commit_iff_admit`, the app's admission predicate `sp.admit` held of the `(committed → new)`
transition: the committed Argus Q SATISFIES the userspace invariant. So a verifier who accepts the
Argus turn knows the app invariant rode along — the dial's Q carries the admission fact, not just the
balances. (Grid/program preconditions are the toolkit's, supplied; we REUSE its theorem, not re-derive.) -/
theorem disclose_app_invariant_rides_Q (sp : AppSpec) (s s' : RecChainedState)
    (hprog : s.kernel.slotCaveats sp.cell = sp.caveats) (actor : CellId) (new : Int)
    (hold : sp.committed s.kernel ∈ sp.oldRange) (hnew : new ∈ sp.newRange)
    (hcommit : stateStepGuarded s sp.slot actor sp.cell new = some s') :
    sp.admit (sp.committed s.kernel) new = true := by
  -- the commit makes `stateStepGuarded … = some s'`, hence `.isSome = true`; the toolkit IFF extracts
  -- BOTH the admission predicate AND the authority gate. We take the admission conjunct.
  have hsome : (stateStepGuarded s sp.slot actor sp.cell new).isSome = true := by
    rw [hcommit]; rfl
  exact ((app_commit_iff_admit sp s hprog actor new hold hnew).mp hsome).1

/-- **`disclose_app_reveals_gated_slot` (the verifier READS the invariant off Q).** After the
committed Argus `setFieldStmt`, the slot `sp.slot` reads back exactly the written value `new`
(`app_commit_field_written`, the toolkit's functional face), and the `onlyField sp.slot` selective
disclosure of the post-state cell REVEALS exactly that value: `DiscloseAt (onlyField sp.slot) s'.kernel
sp.cell sp.slot = some new`. So the verifier's selective view of Q exposes the gated slot — the
quantity `disclose_app_invariant_rides_Q` proved was admitted — and nothing else. The dial and the app
admission meet on the same committed field. -/
theorem disclose_app_reveals_gated_slot (sp : AppSpec) (s s' : RecChainedState)
    (actor : CellId) (new : Int)
    (hcommit : stateStepGuarded s sp.slot actor sp.cell new = some s') :
    DiscloseAt (onlyField sp.slot) s'.kernel sp.cell sp.slot = some new := by
  -- the toolkit functional face: the slot reads back the written value.
  have hwritten : fieldOf sp.slot (s'.kernel.cell sp.cell) = new :=
    app_commit_field_written sp s s' actor new hcommit
  -- `onlyField sp.slot` makes `sp.slot` public, so its disclosure is `some (fieldOf sp.slot …)`.
  simp only [DiscloseAt, project, cellView, onlyField_mask_self, hwritten]

/-- **`disclose_app_hides_other_slot` (selective view hides the rest of Q).** The SAME
`onlyField sp.slot` disclosure HIDES any OTHER field `g ≠ sp.slot` (reveals `none`): the verifier reading
the gated slot off Q learns nothing about the cell's other fields. The selective tier is
selective over the Argus output — `disclose_app_reveals_gated_slot` is not a "reveal everything" stub. -/
theorem disclose_app_hides_other_slot (sp : AppSpec) (k : RecordKernelState) (c : CellId)
    (g : FieldName) (hg : g ≠ sp.slot) :
    DiscloseAt (onlyField sp.slot) k c g = none := by
  simp only [DiscloseAt, project, onlyField_mask_other hg]

/-! ## §6 — NON-VACUITY: the dial projects, hides, and rides — on concrete Argus output.

The connection would be hollow if every disclosure were the same, if `private` were not actually below
`trusted`, or if the selective tier revealed everything. We exhibit a concrete Argus cell and check the
dial is three-valued, that the keystone hiding law has teeth (a private-field change is
invisible), and that the toolkit-ride reveals exactly the gated slot. -/

/-- A concrete Argus-produced cell record: `role = 2` (a public field), `secret = 9` (to be hidden). -/
def kDemo : RecordKernelState :=
  { accounts := {0}, caps := fun _ => [],
    cell := fun _ => .record [("role", .int 2), ("secret", .int 9)] }

/-- The SAME cell but with the PRIVATE field changed: `role = 2`, `secret = 42`. Public field agrees. -/
def kDemo' : RecordKernelState :=
  { accounts := {0}, caps := fun _ => [],
    cell := fun _ => .record [("role", .int 2), ("secret", .int 42)] }

/-- The selective tier revealing only `role` (hiding `secret`). -/
def roleOnly : Tier := onlyField "role"

-- The dial is GENUINELY THREE-VALUED on the Argus cell `role` field:
-- trusted reveals it, the role-only selective reveals it, private hides it.
#guard (DiscloseAt .trusted kDemo 0 "role" == some 2)
#guard (DiscloseAt roleOnly kDemo 0 "role" == some 2)
#guard (DiscloseAt .sovereign kDemo 0 "role" == none)
-- ...and the role-only selective HIDES `secret` (the verifier reading `role` learns nothing of it):
#guard (DiscloseAt roleOnly kDemo 0 "secret" == none)
#guard (DiscloseAt .trusted kDemo 0 "secret" == some 9)   -- trusted WOULD reveal it

/-- **`dial_three_valued` (the dial is non-vacuous, three-valued on Q).** On `kDemo`'s `role`
field the dial takes three distinct shapes: `trusted` reveals `some 2`, `private` hides (`none`), and
the role-only selective reveals `some 2` (= trusted on this field) while hiding `secret` (`none`, ≠
trusted's `some 9`). So the dial moves and the selective tier is partial. -/
theorem dial_three_valued :
    DiscloseAt .trusted kDemo 0 "role" = some 2
    ∧ DiscloseAt .sovereign kDemo 0 "role" = none
    ∧ DiscloseAt roleOnly kDemo 0 "secret" = none
    ∧ DiscloseAt .trusted kDemo 0 "secret" = some 9 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide

/-- **`disclose_hides_private_has_teeth` (the keystone bites, non-vacuously).** `kDemo` and
`kDemo'` AGREE on the public `role` field but DIFFER on the private `secret` field (`9` vs `42`). The
role-only selective disclosure is nonetheless EQUAL on both — the keystone `disclose_hides_private`
hides the private change (the views are indistinguishable), while a `trusted` disclosure WOULD
separate them (`some 9 ≠ some 42`). So the hiding is real, not a `True`-collapse. -/
theorem disclose_hides_private_has_teeth :
    DiscloseAt roleOnly kDemo 0 = DiscloseAt roleOnly kDemo' 0
    ∧ DiscloseAt .trusted kDemo 0 "secret" ≠ DiscloseAt .trusted kDemo' 0 "secret" := by
  refine ⟨?_, ?_⟩
  · -- the views agree: reuse the keystone — the public field `role` agrees, so the disclosures match.
    apply disclose_hides_private roleOnly kDemo kDemo' 0
    intro f hf
    -- only `role` is public under `roleOnly`; both cells carry `role = 2`.
    simp only [roleOnly, onlyField, Tier.mask] at hf
    by_cases hr : (f == "role") = true
    · have : f = "role" := by simpa using hr
      subst this; decide
    · rw [if_neg (by simpa using hr)] at hf; exact absurd hf (by simp)
  · -- trusted separates them: `secret` is `9` in `kDemo`, `42` in `kDemo'`.
    decide

/-! ## §7 — Axiom-hygiene tripwires.

Every keystone — the projection laws (idempotent / hides-private / refinement / GLB), the verified-output
weld (`trusted` reveals / `private` hides the Argus post-balance), the toolkit ride (`Q ⟹ app_invariant`
/ reveals-gated-slot), and the non-vacuity teeth — is `{propext, Classical.choice, Quot.sound}`-clean,
no `sorryAx`. The §8 COMPUTATIONAL hiding portal (the ZK transcript advantage bound) is NOT an axiom
these pins would catch — it is the named gap in the header, carried by `Crypto/Primitives.lean`, never
discharged here. -/

#assert_axioms disclose_idempotent
#assert_axioms disclose_hides_private
#assert_axioms private_le_selective
#assert_axioms selective_le_trusted
#assert_axioms disclose_refines
#assert_axioms private_collapses_all
#assert_axioms private_is_glb
#assert_axioms transfer_post_balance
#assert_axioms disclose_transfer_reveals_balance
#assert_axioms disclose_transfer_private_hides
#assert_axioms disclose_transfer_dial_is_two_valued
#assert_axioms disclose_app_invariant_rides_Q
#assert_axioms disclose_app_reveals_gated_slot
#assert_axioms disclose_app_hides_other_slot
#assert_axioms dial_three_valued
#assert_axioms disclose_hides_private_has_teeth

end Dregg2.Circuit.Argus.Disclose
