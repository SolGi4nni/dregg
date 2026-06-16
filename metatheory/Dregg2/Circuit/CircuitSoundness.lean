/-
# Dregg2.Circuit.CircuitSoundness — the APEX light-client unfoolability theorem.

This module is the **architectural backbone** of dregg's circuit-soundness story: it states, as a
green Lean skeleton, the exact shape a verifying light client gets for free, and it carries the
genuine remaining obligations as EXPLICIT hypotheses / typeclasses — never as `sorry`, `:= True`, or
a silent default.

## The target (what soundness means)

A light client verifies a rotated batch proof against the live VK and runs NOTHING else. Soundness:

  `verifyBatch vk pi π = accept  ⟹  ∃ a genuine kernel transition  s ⟶ s'  with
                                     pi.pre = stateCommit s  ∧  pi.post = stateCommit s'`.

The "genuine kernel transition" is the proved declarative kernel `ActionDispatch.fullActionStep`
(`⟺ execFullA` by `fullActionStep_exec_iff`), composed over a turn by `turnSpec`
(`⟺ execFullTurnA` by `execFullTurnA_iff_turnSpec`). The live circuit is `Satisfied2 hash d …` over
`EffectVmDescriptor2`, with descriptors drawn from the v3 registry
(`EffectVmEmitRotationV3.v3Registry`). The whole point of THIS module is to connect `Satisfied2` to
`turnSpec fullActionStep` faithfully.

## The three pieces (the prompt's mandate)

1. `StateDecode` — the FAITHFUL witness→kernel-state decode. It says the witness's PUBLISHED pre/post
   commitments equal `recStateCommit` of the kernel states they bind, over a fixed commitment surface
   (`CommitSurface`), and that those kernels are `AccountsWF`. Faithfulness is NOT assumed: it is a
   THEOREM (`stateDecode_pre_faithful` / `stateDecode_post_faithful`) — two states decoding the SAME
   published commitment have EQUAL kernels, by `recStateCommit_binds_kernel` (the named Poseidon CR
   set + the PROVED-preserved `AccountsWF`). It assumes NO kernel admissibility (no authority, no
   frame): the decode pins the kernel from the commitment alone.

   The cross-cell / cross-step FRAME is NOT a free field. A `StateDecodeChain` decodes a whole turn
   step-by-step, each step publishing its old/new commitment; `stateDecodeChain_frame_continuous`
   DERIVES that consecutive kernels coincide (`postᵢ = preᵢ₊₁`) from the published-commitment binding,
   so the frame is a CONSEQUENCE of the commitments, not an assumption.

2. `descriptorRefines d kstep` — the per-effect rung each effect discharges: any `Satisfied2` witness
   of descriptor `d` whose published commitments decode to `pre`/`post` forces `kstep pre post`. This
   is the genuine obligation per effect; this module CARRIES it (the registry-wide version is a
   hypothesis of the apex), it does not fake it.

3. `lightclient_unfoolable` — the apex. From a verifying batch (`verifyBatch vk pi π = accept`), the VK
   bound to the live registry (`vk = vkOfRegistry liveRegistry`), the named STARK-batch soundness
   carrier `[StarkSound]`, the named hash CR carrier `[Poseidon2SpongeCR]`, and the carried per-effect
   obligation, conclude a genuine kernel turn whose endpoints are the published commitments.

## Carried obligations ledger (every named-and-deferred premise; nothing laundered)

  * `[StarkSound vk pi π]` — the audited p3 batch-STARK soundness: `verifyBatch vk pi π = accept`
    yields, for the descriptor named in `pi`, a `Satisfied2` witness `t` whose published PI agree with
    `pi`. This is a REALIZABLE crypto/audit obligation (the FRI/p3 verify⟹∃witness extraction) that
    cannot be proved in Lean; it is introduced HERE as a clean named class, not assumed silently. The
    minimal honest interface (`StarkSound`, `verifyBatch`, `accept`, `vkOfRegistry`) is DEFINED in
    this module because none existed.

  * `[Poseidon2SpongeCR hash]` — Poseidon2-sponge collision-resistance (the existing carrier from
    `Poseidon2Binding`). The faithfulness of the decode rides on it (via `wireCommitR_binds` /
    `recStateCommit_binds_kernel`). REALIZABLE.

  * the `CommitSurface` CR fields (`compressInjective cmb/compress`, `compressNInjective compressN`,
    `cellLeafInjective CH`, `RestHashIffFrame RH`) — the standard Poseidon CR set the full-state root
    `recStateCommit` binds under. REALIZABLE; bundled, not free.

  * `hrefines : ∀ e, descriptorRefines (liveRegistry e) (fullActionStep-arm e)` — the per-effect
    refinement, CARRIED as an apex hypothesis. This is the rung the rest of the campaign discharges
    (one effect at a time) into `lightclient_unfoolable`. It is the genuine remaining work, named.

  * `WitnessDecodes hash R S pi` — the WITNESS→KERNEL-STATE EXISTENCE rung. A light client has only
    `(pi, π)`; it cannot supply `pre`/`post`. The hard fact is that the witness's published
    commitments are commitments of REAL well-formed kernel states — i.e. that SOME `pre`/`post` exist
    decoding `pi.toPublished`. This is the genuine surjectivity/realizability of the commitment surface
    on the published values a verifying witness pins; it CANNOT be proved by assuming the conclusion,
    so it is CARRIED explicitly (exactly like `StarkSound`), and the apex DERIVES the decode from it
    rather than hypothesizing a free `pre`/`post`/`hdecode`. REALIZABLE (every accepted trace's
    published roots ARE `recStateCommit` of the kernels the prover committed); named, not faked.

DERIVED (NOT carried — proved here from the above): the decode's faithfulness
(`stateDecode_*_faithful`), the frame continuity over a chain
(`stateDecodeChain_frame_continuous`), and the apex composition shape.
-/
import Dregg2.Circuit.StateCommit
import Dregg2.Circuit.ActionDispatch
import Dregg2.Circuit.DescriptorIR2
import Dregg2.Circuit.Poseidon2Binding

namespace Dregg2.Circuit.CircuitSoundness

open Dregg2.Circuit
open Dregg2.Circuit.DescriptorIR2 (EffectVmDescriptor2 VmTrace Satisfied2)
open Dregg2.Circuit.Poseidon2Binding (Poseidon2SpongeCR)
open Dregg2.Circuit.StateCommit
  (recStateCommit recStateCommit_binds_kernel AccountsWF
   compressInjective compressNInjective cellLeafInjective RestHashIffFrame)
open Dregg2.Circuit.ActionDispatch
  (fullActionStep turnSpec execFullTurnA_iff_turnSpec actionTag)
open Dregg2.Exec
open Dregg2.Exec.TurnExecutorFull (FullActionA execFullTurnA)

/-- The kernel boundary turn the full-state commitment is taken at (`recStateCommit`'s `Turn`). -/
abbrev BoundaryTurn := Dregg2.Exec.Turn

/-! ## §1 — the commitment surface (the genuine Poseidon CR carrier, bundled).

`CommitSurface` packages the five abstract commitment primitives `recStateCommit` is parametric in
(`CH RH cmb compress compressN`) together with the STANDARD Poseidon collision-resistance facts the
full-state-root binding needs. These are SECTION PARAMETERS in `StateCommit`, never axioms; bundling
them lets the apex carry "the surface is collision-resistant" as ONE named hypothesis. Each field is
REALIZABLE by a real Poseidon. -/

/-- A binding commitment surface for the full kernel state: the five primitives `recStateCommit`
runs over, plus the standard Poseidon CR set under which equal roots force equal kernels. -/
structure CommitSurface where
  /-- the per-cell leaf hash. -/
  CH        : CellId → Value → ℤ
  /-- the rest hash over the non-`cell` components. -/
  RH        : RecordKernelState → ℤ
  /-- the root combiner (cell-digest ⊕ rest-hash). -/
  cmb       : ℤ → ℤ → ℤ
  /-- the Merkle 2-to-1 node hash. -/
  compress  : ℤ → ℤ → ℤ
  /-- the sponge over a leaf list. -/
  compressN : List ℤ → ℤ
  /-- CR: the combiner is injective. -/
  cmbInj      : compressInjective cmb
  /-- CR: the node hash is injective. -/
  compInj     : compressInjective compress
  /-- CR: the sponge is injective. -/
  compNInj    : compressNInjective compressN
  /-- CR: the leaf hash binds the whole `Value`. -/
  leafInj     : cellLeafInjective CH
  /-- the rest hash is injective on the framed non-`cell` components. -/
  restFrame   : RestHashIffFrame RH

/-- The full-state commitment of a kernel under a surface, at a turn `t`. -/
def CommitSurface.commit (S : CommitSurface) (k : RecordKernelState) (t : Turn) : ℤ :=
  recStateCommit S.CH S.RH S.cmb S.compress S.compressN k t

/-- **The faithfulness engine (no admissibility).** Two kernels whose surface commitments AGREE (at
the same turn), both `AccountsWF`, are EQUAL. This is `recStateCommit_binds_kernel` repackaged: the
published commitment BINDS the kernel under the CR set — it uses NO authority gate, NO frame
assumption, only collision-resistance + the structural `AccountsWF`. This is exactly the faithfulness
the decode below rests on. -/
theorem CommitSurface.commit_binds (S : CommitSurface) (k k' : RecordKernelState)
    (t : Dregg2.Exec.Turn)
    (hwf : AccountsWF k) (hwf' : AccountsWF k')
    (h : S.commit k t = S.commit k' t) : k = k' := by
  apply recStateCommit_binds_kernel (CH := S.CH) (RH := S.RH) (cmb := S.cmb)
    (compress := S.compress) (compressN := S.compressN)
    S.cmbInj S.compInj S.compNInj S.leafInj S.restFrame k k' t hwf hwf'
  exact h

/-! ## §2 — `StateDecode`: the FAITHFUL witness→kernel-state decode.

`StateDecode S t pre post` says: the published OLD commitment (`pubPre`) equals the surface commitment
of `pre.kernel`, the published NEW commitment (`pubPost`) equals that of `post.kernel`, both kernels
are `AccountsWF`, and `pre`/`post` carry the turn the commitment is taken at. It DERIVES the kernel
from the commitment via `CommitSurface.commit` — it does NOT assume any kernel admissibility.

`pubPre`/`pubPost` are the witness's PUBLISHED public-input commitments (in the rotated layout, the PI
slots `d.piCount` / `d.piCount + 1` that `EffectVmEmitRotationV3.rotV3_publishes` pins to the row's
chained `wireCommitR` commit; `rotV3_binds_published` makes those PI BIND the decoded limbs under
`Poseidon2SpongeCR`). Here we keep the published commitment ABSTRACT (a single `ℤ` per boundary) — the
faithfulness we prove is exactly that the published commitment determines the kernel; the
limb-level decode (`wireCommitR`/`rotV3_binds_published`) is the per-descriptor bridge that supplies
`pubPre`/`pubPost`, carried by `descriptorRefines`. -/

/-- The published-commitment view of one circuit witness: the OLD and NEW state commitments the trace
publishes (the rotated PI slots), at the turn the commitment is parameterized by. -/
structure PublishedCommit where
  /-- the published OLD (pre) state commitment (rotated PI slot `d.piCount`). -/
  pubPre  : ℤ
  /-- the published NEW (post) state commitment (rotated PI slot `d.piCount + 1`). -/
  pubPost : ℤ
  /-- the turn the commitment is taken at (the boundary turn binding `recStateCommit`). -/
  turn    : BoundaryTurn

/-- A `PublishedCommit` is inhabited (a default boundary). Only used to let the abstract readout
`tracePublishedCommit` be `opaque` (which needs `Nonempty` of its codomain); carries no content. -/
instance : Inhabited PublishedCommit := ⟨⟨0, 0, ⟨0, 0, 0, 0⟩⟩⟩

/-- **`StateDecode`** — the faithful decode of a published commitment to its bound kernel states.

`pre`/`post` are the kernel states the published OLD/NEW commitments bind. Faithfulness is the THEOREM
`stateDecode_pre_faithful`/`stateDecode_post_faithful` below — it is NOT assumed here. No authority, no
frame: the decode pins the kernel from the commitment alone (via `CommitSurface.commit_binds`). -/
structure StateDecode (S : CommitSurface) (pc : PublishedCommit)
    (pre post : RecChainedState) : Prop where
  /-- the published OLD commitment IS the surface commitment of `pre.kernel`. -/
  preBinds  : pc.pubPre = S.commit pre.kernel pc.turn
  /-- the published NEW commitment IS the surface commitment of `post.kernel`. -/
  postBinds : pc.pubPost = S.commit post.kernel pc.turn
  /-- `pre`'s kernel is structurally well-formed (the binding's structural side-condition; PROVED
      preserved by the executor, `recKExec_preserves_AccountsWF` — not a crypto assumption). -/
  preWF     : AccountsWF pre.kernel
  /-- `post`'s kernel is structurally well-formed. -/
  postWF    : AccountsWF post.kernel

/-- **FAITHFULNESS (pre).** Two pre-states decoding the SAME published commitment have EQUAL kernels.
No admissibility used — pure commitment binding. -/
theorem stateDecode_pre_faithful (S : CommitSurface) (pc : PublishedCommit)
    {pre post pre' post' : RecChainedState}
    (h : StateDecode S pc pre post) (h' : StateDecode S pc pre' post') :
    pre.kernel = pre'.kernel :=
  S.commit_binds pre.kernel pre'.kernel pc.turn h.preWF h'.preWF
    (h.preBinds ▸ h'.preBinds ▸ rfl)

/-- **FAITHFULNESS (post).** Two post-states decoding the SAME published commitment have EQUAL
kernels. No admissibility used. -/
theorem stateDecode_post_faithful (S : CommitSurface) (pc : PublishedCommit)
    {pre post pre' post' : RecChainedState}
    (h : StateDecode S pc pre post) (h' : StateDecode S pc pre' post') :
    post.kernel = post'.kernel :=
  S.commit_binds post.kernel post'.kernel pc.turn h.postWF h'.postWF
    (h.postBinds ▸ h'.postBinds ▸ rfl)

/-! ## §3 — `descriptorRefines`: the per-effect rung.

For a descriptor `d` and a candidate kernel step relation `kstep`, `descriptorRefines d kstep` says:
ANY `Satisfied2` witness of `d` whose published commitments (`pc`) decode (via a faithful
`StateDecode`) to `pre`/`post` FORCES `kstep pre post`. This is the obligation each effect discharges
(its `Satisfied2` denotation entails its `fullActionStep` arm); the apex carries the registry-wide
family of these. The hash, surface, and memory boundary (`minit`/`mfin`/`maddrs`) are quantified — a
witness under ANY boundary that publishes commitments decoding to `pre`/`post` must induce the step. -/

/-- **`descriptorRefines d kstep`** — the per-effect refinement obligation: under the named hash CR
carrier (`Poseidon2SpongeCR hash` — the floor the per-descriptor published-PI↔limb binding
`EffectVmEmitRotationV3.rotV3_binds_published` consumes), every `Satisfied2` witness of `d` whose
published commitments decode to `pre`/`post` forces `kstep pre post`. The `Poseidon2SpongeCR`
antecedent is GENUINE — it is exactly what each effect's discharge needs to tie the published
commitment to the decoded kernel before invoking its `Satisfied2 ⟹ fullActionStep` keystone. -/
def descriptorRefines (S : CommitSurface) (hash : List ℤ → ℤ)
    (d : EffectVmDescriptor2) (kstep : RecChainedState → RecChainedState → Prop) : Prop :=
  Poseidon2SpongeCR hash →
  ∀ (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (t : VmTrace)
    (pc : PublishedCommit) (pre post : RecChainedState),
    Satisfied2 hash d minit mfin maddrs t →
    StateDecode S pc pre post →
    kstep pre post

/-! ## §4 — `StateDecodeChain`: decode a whole turn; the FRAME is DERIVED.

A turn is a list of actions; the circuit witnesses it as a list of per-step circuit witnesses, each
publishing its own OLD/NEW commitment. `StateDecodeChain` decodes the whole turn:

  * `pre₀` is the turn pre-state;
  * each step `i` has a witness with a faithful `StateDecode` to `(sᵢ, sᵢ₊₁)`;
  * the published NEW commitment of step `i` and the published OLD commitment of step `i+1` AGREE
    (the prover's chained-root column — `foldStepRoots` in `TurnCircuitCompose`).

The cross-step FRAME (that the post-state of one step IS the pre-state of the next) is then a
THEOREM, not an assumption: equal published commitments + faithfulness force `sᵢ₊₁.kernel = sᵢ₊₁.kernel`
across the seam. We state the per-seam continuity as `stateDecodeChain_frame_continuous`. -/

/-- A decoded turn step: the action, its descriptor, the published commitment, and the faithful
decode of that commitment to the step's `(pre, post)` kernels. -/
structure DecodedStep (S : CommitSurface) where
  /-- the kernel action this step runs. -/
  action  : FullActionA
  /-- the descriptor (from the live registry) the step's circuit witnesses. -/
  descr   : EffectVmDescriptor2
  /-- the published commitment view of the step's circuit witness. -/
  pc      : PublishedCommit
  /-- the step's pre/post chained states. -/
  pre     : RecChainedState
  /-- the step's post chained state. -/
  post    : RecChainedState
  /-- the faithful decode of `pc` to `(pre, post)`. -/
  decode  : StateDecode S pc pre post

/-- **Cross-step frame continuity is DERIVED, not assumed.** If two adjacent decoded steps publish the
SAME boundary commitment (`a.pc.pubPost = b.pc.pubPre`) at the same turn, and the post of `a` / the
pre of `b` are `AccountsWF`, then their kernels COINCIDE — the frame at the seam is forced by the
commitment binding, not a free hypothesis.

(The shared boundary commitment is the prover's chained-root column; equating it across the seam is
the `foldStepRoots` glue from `TurnCircuitCompose`. The `turn`-equality is the boundary-turn agreement
the layout pins.) -/
theorem stateDecodeChain_frame_continuous (S : CommitSurface) (a b : DecodedStep S)
    (hturn : a.pc.turn = b.pc.turn)
    (hseam : a.pc.pubPost = b.pc.pubPre) :
    a.post.kernel = b.pre.kernel := by
  have ha : a.pc.pubPost = S.commit a.post.kernel a.pc.turn := a.decode.postBinds
  have hb : b.pc.pubPre = S.commit b.pre.kernel b.pc.turn := b.decode.preBinds
  have : S.commit a.post.kernel a.pc.turn = S.commit b.pre.kernel b.pc.turn := by
    rw [← ha, ← hb, hseam]
  rw [hturn] at this
  exact S.commit_binds a.post.kernel b.pre.kernel b.pc.turn a.decode.postWF b.decode.preWF this

/-! ## §5 — the minimal honest STARK-batch interface.

None of `VerifyKey`, `verifyBatch`, `vkOfRegistry`, or the STARK-batch soundness existed. We define
the minimal HONEST interface here and SAY SO:

  * `VerifyKey` — an opaque verifying key (the committed registry the verifier is pinned to).
  * `vkOfRegistry` — the VK↔registry binding: the live registry's commitment IS the VK.
  * `BatchPublicInputs` — the public inputs a batch proof exposes: the descriptor name/effect index it
    claims, the published OLD/NEW commitments (= `pi.pre`/`pi.post`), and the boundary turn.
  * `Accept` — the verdict; `verifyBatch vk pi π` is `accept` exactly when the proof checks.
  * `StarkSound` — the AUDITED p3 batch-STARK soundness, as a named class: a verifying batch yields a
    `Satisfied2` witness of the CLAIMED descriptor whose published PI AGREE with `pi`. This is the FRI
    extraction obligation; REALIZABLE, audited, NOT provable in Lean — carried as a class, not faked.

`liveRegistry` is the effect→descriptor map; we keep it abstract (a function `EffectIdx →
EffectVmDescriptor2`) so the apex is parametric in it — the concrete binding to
`EffectVmEmitRotationV3.v3Registry` is a registry-lookup wrapper a downstream instance supplies. -/

/-- An effect index (the dispatcher's `actionTag` lives here). -/
abbrev EffectIdx := Nat

/-- The live effect→descriptor registry (abstract; the concrete instance is the v3 registry lookup). -/
abbrev Registry := EffectIdx → EffectVmDescriptor2

/-- An opaque verifying key — the committed object the light client is pinned to. -/
structure VerifyKey where
  /-- the registry commitment the VK certifies (kept structural; equality is what the apex needs). -/
  registryDigest : ℤ
deriving DecidableEq

/-- A registry-commitment hash (abstract surface digest of the whole registry). -/
opaque registryCommit : Registry → ℤ

/-- **The VK↔registry binding.** The VK of a registry commits exactly to that registry. -/
def vkOfRegistry (R : Registry) : VerifyKey := ⟨registryCommit R⟩

/-- The public inputs a batch proof exposes to the light client. -/
structure BatchPublicInputs where
  /-- the effect index (which registry descriptor the batch claims). -/
  effect : EffectIdx
  /-- the published pre-state commitment. -/
  pre    : ℤ
  /-- the published post-state commitment. -/
  post   : ℤ
  /-- the boundary turn the commitments are taken at. -/
  turn   : BoundaryTurn

/-- The verifier verdict. -/
inductive Verdict where
  | accept
  | reject
deriving DecidableEq, Inhabited

open Verdict

/-- A batch proof object (interface stub; its bytes are irrelevant to the apex — only the verifier
verdict and the `StarkSound` extraction matter). -/
structure BatchProof where
  /-- the opaque proof bytes (unconstrained — the apex reasons only via the verdict). -/
  bytes : List ℤ := []

/-- The (opaque) batch verifier: checks `π` against `vk` and `pi`. Its only SPECIFIED behaviour is via
the `StarkSound` class below — we make NO unjustified claim about its internals. -/
opaque verifyBatch : VerifyKey → BatchPublicInputs → BatchProof → Verdict

/-- The published-commitment view induced by a `BatchPublicInputs`. -/
def BatchPublicInputs.toPublished (pi : BatchPublicInputs) : PublishedCommit :=
  ⟨pi.pre, pi.post, pi.turn⟩

/-- **The published-commitment readout of a circuit witness.** A `VmTrace` exposes its rotated PI
slots `d.piCount` / `d.piCount + 1` (the chained `wireCommitR` old/new state commitments) and the
boundary turn. We keep this readout ABSTRACT here (a single `PublishedCommit` per trace) — exactly as
`verifyBatch` is opaque — because the limb-level readout (`EffectVmEmitRotationV3.rotV3_publishes`) is
the per-descriptor bridge. The `StarkSound` extraction below pins this readout to `pi.toPublished`, so
the witness `t` it returns genuinely publishes the light client's public inputs (not merely SOME
commitments). -/
opaque tracePublishedCommit : VmTrace → PublishedCommit

@[simp] theorem BatchPublicInputs.toPublished_pubPre (pi : BatchPublicInputs) :
    pi.toPublished.pubPre = pi.pre := rfl
@[simp] theorem BatchPublicInputs.toPublished_pubPost (pi : BatchPublicInputs) :
    pi.toPublished.pubPost = pi.post := rfl
@[simp] theorem BatchPublicInputs.toPublished_turn (pi : BatchPublicInputs) :
    pi.toPublished.turn = pi.turn := rfl

/-- **`StarkSound` — the audited p3 batch-STARK soundness carrier (NAMED, not faked).**

A verifying batch against the live registry's VK yields, for the descriptor the PI names
(`R pi.effect`), a `Satisfied2` witness `t` (over SOME boundary) whose published OLD/NEW commitments
are EXACTLY `pi.pre`/`pi.post`, at the turn `pi.turn` (i.e. `pi.toPublished`). This is the FRI/p3
verify⟹∃witness extraction: REALIZABLE and audited, but NOT provable in Lean — introduced as a clean
class so the apex carries it explicitly instead of assuming it silently. -/
class StarkSound (hash : List ℤ → ℤ) (R : Registry) : Prop where
  extract : ∀ (pi : BatchPublicInputs) (π : BatchProof),
    verifyBatch (vkOfRegistry R) pi π = accept →
    ∃ (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (t : VmTrace),
      Satisfied2 hash (R pi.effect) minit mfin maddrs t ∧
        tracePublishedCommit t = pi.toPublished

/-! ## §6 — the apex: `lightclient_unfoolable`.

The apex's ONLY data inputs are what a light client actually has: the public inputs `pi` and the proof
`π`. It does NOT take `pre`/`post` or a `StateDecode` as hypotheses — those would HIDE the hardest rung
(that the published commitments are commits of REAL kernel states), turning the theorem into a
conditional refinement rather than unfoolability. Instead the apex DERIVES the decode, from named
floors only, and CONCLUDES the existence of a genuine kernel boundary.

The floors:
  * `[StarkSound hash R]` — a verifying batch yields a `Satisfied2` witness of the CLAIMED descriptor
    whose published commitments ARE `pi.toPublished` (the strengthened extraction).
  * `Poseidon2SpongeCR hash` + the `CommitSurface` CR fields — the decode's faithfulness floor.
  * `hrefines` — the per-effect refinement rung (`Satisfied2 + StateDecode ⟹ kstep`).
  * `WitnessDecodes hash R S pi` — the NEW carried obligation: a witness publishing `pi` decodes to
    SOME `(pre, post)`. This is the genuinely-hard witness→kernel-state EXISTENCE rung; carried, not
    proved-by-assuming-the-conclusion.

Derivation chain: STARK extracts a witness `t` with `tracePublishedCommit t = pi.toPublished` →
`WitnessDecodes` produces `pre`/`post` with `StateDecode S pi.toPublished pre post` → `hrefines` turns
the witness + decode into `kstep pi.effect pre post` → the decode's binding re-exports `pi.pre`/`pi.post`
as the genuine endpoint commitments. The result is the honest headline: `(pi, π)` + named floors ⟹
∃ a real kernel transition committing to `pi`. The light client RAN NOTHING. -/

/-- **`WitnessDecodes hash R S pi` — the witness→kernel-state EXISTENCE rung (NAMED, not faked).**

Any `Satisfied2` witness of the claimed descriptor `R pi.effect` that PUBLISHES `pi.toPublished` (its
rotated PI old/new commitments equal `pi`'s) decodes to SOME `(pre, post)` via a faithful
`StateDecode`. This is the existence of REAL well-formed kernel states behind the published roots — the
surjectivity of the commitment surface on the values a verifying witness pins. A light client cannot
supply `pre`/`post`; this rung SUPPLIES them. It must NOT be discharged by assuming the apex's
conclusion — it is carried EXPLICITLY (exactly as `StarkSound` is), and the apex consumes it to derive
the decode. REALIZABLE (the prover committed to the kernels whose roots the trace publishes). -/
def WitnessDecodes (hash : List ℤ → ℤ) (R : Registry) (S : CommitSurface)
    (pi : BatchPublicInputs) : Prop :=
  ∀ (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (t : VmTrace),
    Satisfied2 hash (R pi.effect) minit mfin maddrs t →
    tracePublishedCommit t = pi.toPublished →
    ∃ pre post : RecChainedState, StateDecode S pi.toPublished pre post

theorem lightclient_unfoolable
    (hash : List ℤ → ℤ) (S : CommitSurface) (R : Registry)
    (hCR : Poseidon2SpongeCR hash) [StarkSound hash R]
    (kstep : EffectIdx → RecChainedState → RecChainedState → Prop)
    (hrefines : ∀ e, descriptorRefines S hash (R e) (kstep e))
    (pi : BatchPublicInputs) (π : BatchProof)
    (hwitdec : WitnessDecodes hash R S pi)
    (hacc : verifyBatch (vkOfRegistry R) pi π = accept) :
    ∃ pre post : RecChainedState,
      StateDecode S pi.toPublished pre post ∧
      kstep pi.effect pre post ∧
      pi.pre = S.commit pre.kernel pi.turn ∧
      pi.post = S.commit post.kernel pi.turn := by
  -- (1) strengthened STARK soundness extracts a Satisfied2 witness of the CLAIMED descriptor whose
  --     published commitments ARE `pi.toPublished`.
  obtain ⟨minit, mfin, maddrs, t, hsat, hpub⟩ :=
    (inferInstance : StarkSound hash R).extract pi π hacc
  -- (2) the carried witness→state EXISTENCE rung supplies the decoded kernel boundary `(pre, post)`.
  obtain ⟨pre, post, hdecode⟩ := hwitdec minit mfin maddrs t hsat hpub
  -- (3) the carried per-effect rung (fed the named hash CR carrier `hCR`) turns the circuit witness +
  --     the derived decode into the step.
  have hstep : kstep pi.effect pre post :=
    hrefines pi.effect hCR minit mfin maddrs t pi.toPublished pre post hsat hdecode
  -- (4) faithfulness re-exports the published commitments as the genuine endpoint commitments.
  refine ⟨pre, post, hdecode, hstep, ?_, ?_⟩
  · simpa using hdecode.preBinds
  · simpa using hdecode.postBinds

/-! ## §7 — the headline corollary: a genuine kernel TURN (forest-composition shape).

The natural downstream `kstep` is the dispatcher arm: a single committed `fullActionStep`. A turn is a
list of such steps composed by `turnSpec`, which `execFullTurnA_iff_turnSpec` identifies with the real
executor `execFullTurnA`. `lightclient_turn_unfoolable` packages the apex at this `kstep` over a
SINGLE-action turn, and re-exports it as a genuine `execFullTurnA` run — the "∃ genuine kernel
transition" headline. Multi-step composition chains these via `stateDecodeChain_frame_continuous`
(§4): the per-seam frame is DERIVED from the shared published commitments, so a chain of single-action
apexes folds into a whole-turn `turnSpec` exactly as `TurnCircuitCompose.turn_emitted_refines_exec_direct`
folds its per-step `hstep`. -/

/-- The single-action dispatcher arm: the published effect index names an action whose
`fullActionStep` holds between the decoded endpoints. -/
def dispatchArm (e : EffectIdx) (pre post : RecChainedState) : Prop :=
  ∃ fa : FullActionA, actionTag fa = e ∧ fullActionStep pre fa post

/-- **`lightclient_turn_unfoolable`** — the headline at the dispatcher arm. From a verifying batch and
the named floors (including the carried `WitnessDecodes` existence rung — the light client supplies NO
`pre`/`post`), there EXIST decoded endpoints and a genuine committed single-action kernel turn
(`execFullTurnA pre [fa] = some post`) whose endpoints are the published commitments. The per-effect
rung is carried as `hrefines` at `dispatchArm`. -/
theorem lightclient_turn_unfoolable
    (hash : List ℤ → ℤ) (S : CommitSurface) (R : Registry)
    (hCR : Poseidon2SpongeCR hash) [StarkSound hash R]
    (hrefines : ∀ e, descriptorRefines S hash (R e) (dispatchArm e))
    (pi : BatchPublicInputs) (π : BatchProof)
    (hwitdec : WitnessDecodes hash R S pi)
    (hacc : verifyBatch (vkOfRegistry R) pi π = accept) :
    ∃ pre post : RecChainedState,
      StateDecode S pi.toPublished pre post ∧
      (∃ fa : FullActionA, execFullTurnA pre [fa] = some post) ∧
      pi.pre = S.commit pre.kernel pi.turn ∧
      pi.post = S.commit post.kernel pi.turn := by
  obtain ⟨pre, post, hdecode, harm, hpre, hpost⟩ :=
    lightclient_unfoolable hash S R hCR dispatchArm hrefines pi π hwitdec hacc
  obtain ⟨fa, _htag, hstep⟩ := harm
  refine ⟨pre, post, hdecode, ⟨fa, ?_⟩, hpre, hpost⟩
  -- `fullActionStep pre fa post` ⟺ `turnSpec pre [fa] post` ⟺ `execFullTurnA pre [fa] = some post`.
  rw [execFullTurnA_iff_turnSpec]
  exact ⟨post, hstep, rfl⟩

/-! ## §8 — the WHOLE-TURN apex: composing the per-effect rung along a turn (FOREST shape).

§6/§7 land the apex on ONE effect. A turn is a LIST of effects, witnessed by a LIST of per-step circuit
witnesses, each publishing its own OLD/NEW commitment (the prover's chained-root column). This section
LIFTS the single-effect apex to a whole-turn statement: from the carried per-effect family `hrefines :
∀ e, descriptorRefines (R e) (dispatchArm e)` + the named floors, derive that a turn whose EVERY step's
circuit is satisfied yields a genuine `execFullTurnA s acts = some s'` over chained kernel states whose
ENDPOINTS commit to the published turn-level `(pre, post)`.

The composition is the §4 `DecodedStep` chain, folded:

  * `TurnDecodeChain` — a list of `DecodedStep`s threaded left-to-right so each step's post IS the next
    step's pre (`a.post = b.pre` as a FULL chained state — the executor's actual carried state), with
    the published seam commitments AGREEING across the boundary (`a.pc.pubPost = b.pc.pubPre`) at one
    boundary turn. The KERNEL half of the seam is then DERIVED — `stateDecodeChain_frame_continuous`
    proves the threaded kernels coincide from the published-commitment binding, so a prover who
    publishes a seam commitment disagreeing with the threaded kernel is REJECTED (the frame TOOTH). The
    chain is the §4 frame made whole-turn: not assumed, certified.

  * `turnDecodeChain_refines_turnSpec` — fold the per-step `descriptorRefines` (each step's circuit
    witness + faithful decode ⟹ its `dispatchArm`) along the chain into the declarative `turnSpec`,
    mirroring `TurnCircuitCompose.turn_emitted_refines_exec_direct`'s shape but landing on the ROTATED
    `dispatchArm` (not the universe-A `stepEmittedSat`).

  * `lightclient_turn_unfoolable_forest` — the whole-turn headline: a verified turn (every step's
    circuit satisfied, decoded, seam-published) + `hrefines` + floors ⟹ `∃ acts s s', execFullTurnA s
    acts = some s' ∧ turn-pre = commit s ∧ turn-post = commit s'`. Re-exported to `execFullForestG` by
    the existing `WholeTurnTriangle.execFullForestG_eq_execFullTurnG` lowering downstream.

### NEW carried obligation (named, added to the ledger — NOT laundered)

  * `seamFullState` (a field of `TurnDecodeChain`) — the FULL-state seam `a.post = b.pre`. The
    commitment surface commits ONLY the `RecChainedState.kernel` (`recStateCommit` takes a
    `RecordKernelState`), so the published seam binds the KERNEL half of `a.post = b.pre`
    (DERIVED, the tooth) but NOT the `log` (receipt-chain) half. The executor `execFullTurnA` threads
    the FULL state; thus the log-continuity of the seam is the genuine residue the commitments cannot
    certify. It is carried EXPLICITLY as a chain field (the prover threads the real executor state, so
    `a.post = b.pre` holds by construction of an honest run; a verifier obtains it from the same
    chained-root column that ties the kernels, EXTENDED to the uncommitted log column). REALIZABLE
    (the honest prover's post IS the next pre); named, not assumed silently. The kernel half is
    re-derived as the frame TOOTH (`turnDecodeChain_seam_kernel_derived`) so the commitment binding
    stays load-bearing on the part it covers. -/

/-- **`TurnDecodeChain S start steps fin`** — a whole-turn decode: a list of §4 `DecodedStep`s threaded
left-to-right from `start` to `fin`, each step's circuit satisfied, with the published seam
commitments agreeing across boundaries. The frame's KERNEL half is DERIVED
(`turnDecodeChain_seam_kernel_derived`); the full-state `seam`/`headPre`/`lastPost` fields carry the
uncommitted `log` residue (the NAMED obligation). -/
structure TurnDecodeChain (hash : List ℤ → ℤ) (S : CommitSurface)
    (start fin : RecChainedState) where
  /-- the decoded per-step records (action, descriptor, published commitment, decode). -/
  steps     : List (DecodedStep S)
  /-- every step publishes a circuit witness `Satisfied2` of its descriptor (the per-step accept). -/
  sat       : ∀ d ∈ steps, ∃ (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (t : VmTrace),
                Satisfied2 hash d.descr minit mfin maddrs t ∧
                  tracePublishedCommit t = d.pc
  /-- the turn pre-state IS the first step's pre (or `start = fin` on an empty turn). -/
  headPre   : steps.head?.elim (start = fin) (fun d => start = d.pre)
  /-- the turn post-state IS the last step's post (full-state). -/
  lastPost  : steps.getLast?.elim (start = fin) (fun d => d.post = fin)
  /-- **the threaded seam (FULL-state):** each step's post IS the next step's pre. The KERNEL half is
      DERIVED from the published seam; the `log` half is the NAMED residue (see the ledger). -/
  seam      : List.IsChain (fun a b => a.post = b.pre) steps
  /-- the published seam commitments AGREE across each boundary (the prover's chained-root column). -/
  pubSeam   : List.IsChain (fun a b => a.pc.turn = b.pc.turn ∧ a.pc.pubPost = b.pc.pubPre) steps

/-- **The frame TOOTH (kernel half DERIVED, not assumed).** For every adjacent pair in a
`TurnDecodeChain`, the published seam commitments FORCE the threaded kernels to coincide
(`a.post.kernel = b.pre.kernel`) — `stateDecodeChain_frame_continuous` applied along the chain. So a
prover whose published seam commitment disagrees with the threaded kernel is REJECTED: the kernel half
of `seam` is certified by the commitment binding, not taken on faith. -/
theorem turnDecodeChain_seam_kernel_derived (hash : List ℤ → ℤ) (S : CommitSurface)
    {start fin : RecChainedState} (c : TurnDecodeChain hash S start fin) :
    List.IsChain (fun a b => a.post.kernel = b.pre.kernel) c.steps := by
  refine List.IsChain.imp ?_ c.pubSeam
  intro a b hpub
  exact stateDecodeChain_frame_continuous S a b hpub.1 hpub.2

/-- **The per-step refinement obligation over a decoded turn.** Each decoded step's descriptor is the
registry entry for SOME effect index `e`, and its circuit witness + faithful decode force `dispatchArm
e d.pre d.post` (i.e. an action of effect `e` carries the step). This is the per-step accept the
carried `descriptorRefines` family discharges — quantified over the chain's steps. -/
def StepsRefine (hash : List ℤ → ℤ) (S : CommitSurface) (R : Registry)
    {start fin : RecChainedState} (c : TurnDecodeChain hash S start fin) : Prop :=
  ∀ d ∈ c.steps, ∃ e : EffectIdx, d.descr = R e ∧ dispatchArm e d.pre d.post

/-- **Each step's `descriptorRefines` discharges `StepsRefine`.** Given the carried per-effect family
`hrefines` and the named hash CR carrier, the per-step circuit accepts (`c.sat`) + faithful decodes
(`d.decode`) force `dispatchArm e d.pre d.post` at every step whose descriptor is `R e`. This is the
registry-wide rung consumed step-by-step — the rotated analog of `step_emitted_refines_fullActionStep`.
The effect-index identification (`d.descr = R e`) is supplied by the witness layout (`hidx`). -/
theorem stepsRefine_of_descriptorRefines
    (hash : List ℤ → ℤ) (S : CommitSurface) (R : Registry)
    (hCR : Poseidon2SpongeCR hash)
    (hrefines : ∀ e, descriptorRefines S hash (R e) (dispatchArm e))
    {start fin : RecChainedState} (c : TurnDecodeChain hash S start fin)
    (hidx : ∀ d ∈ c.steps, ∃ e : EffectIdx, d.descr = R e) :
    StepsRefine hash S R c := by
  intro d hd
  obtain ⟨e, hde⟩ := hidx d hd
  obtain ⟨minit, mfin, maddrs, t, hsat, hpub⟩ := c.sat d hd
  refine ⟨e, hde, ?_⟩
  -- the carried rung for descriptor `R e`, fed the named CR carrier, the witness, and the decode.
  have hsat' : Satisfied2 hash (R e) minit mfin maddrs t := hde ▸ hsat
  exact hrefines e hCR minit mfin maddrs t d.pc d.pre d.post hsat' d.decode

/-- **Fold `StepsRefine` along the threaded chain into `turnSpec`.** A `TurnDecodeChain` whose every
step refines (`StepsRefine`) induces the declarative `turnSpec` from `start` to `fin` over SOME action
list (each action the `fa` the step's `dispatchArm` names). Mirrors `turn_emitted_refines_exec_direct`'s
per-step→turn fold; the full-state `seam` threads the actual executor state (kernel half certified by
the frame tooth), so the fold composes left-to-right with no gap. -/
theorem turnDecodeChain_refines_turnSpec
    (hash : List ℤ → ℤ) (S : CommitSurface) (R : Registry)
    {start fin : RecChainedState} (c : TurnDecodeChain hash S start fin)
    (href : StepsRefine hash S R c) :
    ∃ acts : List FullActionA, turnSpec start acts fin := by
  -- A clean list induction with every threaded hypothesis as an explicit `∀`/`→` argument, so the
  -- IH shape is exactly the recursion (`start := d.post`). The endpoints (`headPre`/`lastPost`), the
  -- full-state `seam`, and the per-step refinement are all threaded uniformly.
  unfold StepsRefine at href
  obtain ⟨steps, _sat, headPre, lastPost, seam, _pubSeam⟩ := c
  simp only at href headPre lastPost
  suffices key : ∀ (steps : List (DecodedStep S)) (start : RecChainedState),
      List.IsChain (fun a b => a.post = b.pre) steps →
      steps.head?.elim (start = fin) (fun d => start = d.pre) →
      steps.getLast?.elim (start = fin) (fun d => d.post = fin) →
      (∀ d ∈ steps, ∃ e : EffectIdx, d.descr = R e ∧ dispatchArm e d.pre d.post) →
      ∃ acts : List FullActionA, turnSpec start acts fin by
    exact key steps start seam headPre lastPost href
  clear seam headPre lastPost href _sat _pubSeam steps start
  intro steps
  induction steps with
  | nil =>
      -- empty turn: `start = fin`, the empty `turnSpec`.
      intro start _seam headPre _lastPost _href
      simp only [List.head?_nil, Option.elim_none] at headPre
      exact ⟨[], by simpa [turnSpec] using headPre⟩
  | cons d rest ih =>
      intro start seam headPre lastPost href
      -- head: `start = d.pre`; the head step refines to `dispatchArm e d.pre d.post`.
      simp only [List.head?_cons, Option.elim_some] at headPre
      obtain ⟨e, _hde, fa, _htag, hstep⟩ := href d List.mem_cons_self
      -- the seam gives `d.post = (head of rest).pre`; recurse from `d.post`.
      have hseamRest : List.IsChain (fun a b => a.post = b.pre) rest := seam.tail
      have hheadRest : rest.head?.elim (d.post = fin) (fun d' => d.post = d'.pre) := by
        cases rest with
        | nil => simpa using (by simpa using lastPost)
        | cons d' _ =>
            have hrel := (List.isChain_cons.mp seam).1 d' (by simp)
            simpa using hrel
      have hlastRest : rest.getLast?.elim (d.post = fin) (fun d' => d'.post = fin) := by
        cases rest with
        | nil => simpa using lastPost
        | cons d' rest' =>
            have heq : (d :: d' :: rest').getLast? = (d' :: rest').getLast? := by
              simp [List.getLast?_cons_cons]
            simpa [heq] using lastPost
      have hrefRest : ∀ d'' ∈ rest, ∃ e' : EffectIdx, d''.descr = R e' ∧
          dispatchArm e' d''.pre d''.post := fun d'' hd'' => href d'' (List.mem_cons_of_mem _ hd'')
      obtain ⟨acts, htail⟩ := ih d.post hseamRest hheadRest hlastRest hrefRest
      -- prepend `fa`: `fullActionStep start fa d.post` (subst `start = d.pre`), then the tail.
      subst headPre
      exact ⟨fa :: acts, d.post, hstep, htail⟩

/-! ### §8.1 — the turn-level endpoint commitments (DERIVED from the chain's first/last step).

The whole-turn headline must export the PUBLISHED turn-level `(pre, post)` as genuine commitments of
the executor's endpoint kernels (`start`/`fin`). The turn's published pre/post commitments are exactly
the head step's `pubPre` and the last step's `pubPost` (the two open ends of the prover's chained-root
column). `TurnEndpoints` says the turn-level published commitments AND turn are pinned to those open
ends; `turnDecodeChain_endpoints_commit` then DERIVES, from the head/last step decodes alone, that the
published turn-level pre/post ARE `S.commit start.kernel` / `S.commit fin.kernel` — the endpoint
commitments are forced by the same per-step binding the seams use, not assumed. -/

/-- **`TurnEndpoints`** — the turn-level published commitment view pinned to the chain's open ends. The
published turn-pre/turn-post commitments equal the head step's `pubPre` / the last step's `pubPost`
(the two unmatched ends of the prover's chained-root column), at the boundary turn `tp.turn`, which
agrees with the head/last step's commitment turn. On an EMPTY turn there is no step root to read, so the
degenerate branch carries the endpoint binding DIRECTLY (`tp.pubPre`/`tp.pubPost = S.commit start.kernel
tp.turn`, with `start = fin` so both endpoints commit to the same kernel) — named, not laundered. -/
structure TurnEndpoints (hash : List ℤ → ℤ) (S : CommitSurface)
    {start fin : RecChainedState} (c : TurnDecodeChain hash S start fin) where
  /-- the published turn-level pre/post commitment view (the light client's `pi.toPublished`). -/
  tp        : PublishedCommit
  /-- the published turn-pre commitment IS the head step's `pubPre` (the open OLD end); on the empty
      turn it directly binds `start.kernel` (no step root exists to derive it from). -/
  headOpen  : c.steps.head?.elim (tp.pubPre = S.commit start.kernel tp.turn)
                (fun d => tp.pubPre = d.pc.pubPre ∧ tp.turn = d.pc.turn)
  /-- the published turn-post commitment IS the last step's `pubPost` (the open NEW end); on the empty
      turn it directly binds `fin.kernel`. -/
  lastOpen  : c.steps.getLast?.elim (tp.pubPost = S.commit fin.kernel tp.turn)
                (fun d => tp.pubPost = d.pc.pubPost ∧ tp.turn = d.pc.turn)

/-- **The turn-level endpoint commitments are DERIVED (not assumed) on a non-empty turn.** Given the
chain's `headPre`/`lastPost` (which thread `start`/`fin` to the head/last step's `pre`/`post`) and the
`TurnEndpoints` pinning of the published turn-pre/turn-post to the open ends, the published turn-level
commitments ARE the surface commitments of the executor endpoints: `tp.pubPre = S.commit start.kernel
tp.turn` and `tp.pubPost = S.commit fin.kernel tp.turn`. On a non-empty turn the head/last step decodes
(`preBinds`/`postBinds`) FORCE the binding (same per-step rung the seams use); on the empty turn the
`TurnEndpoints` degenerate branch carries it directly. -/
theorem turnDecodeChain_endpoints_commit (hash : List ℤ → ℤ) (S : CommitSurface)
    {start fin : RecChainedState} (c : TurnDecodeChain hash S start fin)
    (te : TurnEndpoints hash S c) :
    te.tp.pubPre = S.commit start.kernel te.tp.turn ∧
      te.tp.pubPost = S.commit fin.kernel te.tp.turn := by
  obtain ⟨tp, headOpen, lastOpen⟩ := te
  -- The head step pins `start`; the last step pins `fin`. Both via the step decode's binding.
  refine ⟨?_, ?_⟩
  · -- pubPre = S.commit start.kernel tp.turn
    cases hsteps : c.steps with
    | nil =>
        -- empty turn: the degenerate `TurnEndpoints` branch binds `start.kernel` directly.
        rw [hsteps] at headOpen; simpa using headOpen
    | cons d rest =>
        have hhead : tp.pubPre = d.pc.pubPre ∧ tp.turn = d.pc.turn := by
          rw [hsteps] at headOpen; simpa using headOpen
        have hstart : start = d.pre := by
          have := c.headPre; rw [hsteps] at this; simpa using this
        rw [hhead.1, hhead.2, hstart]; exact d.decode.preBinds
  · -- pubPost = S.commit fin.kernel tp.turn
    cases hsteps : c.steps.getLast? with
    | none =>
        -- `getLast? = none ⟺ steps = []`; the degenerate branch binds `fin.kernel` directly.
        have hnil : c.steps = [] := List.getLast?_eq_none_iff.mp hsteps
        rw [hnil] at lastOpen; simpa using lastOpen
    | some dl =>
        have hlastOpen : tp.pubPost = dl.pc.pubPost ∧ tp.turn = dl.pc.turn := by
          rw [hsteps] at lastOpen; simpa using lastOpen
        have hfin : dl.post = fin := by
          have := c.lastPost; rw [hsteps] at this; simpa using this
        rw [hlastOpen.1, hlastOpen.2, ← hfin]; exact dl.decode.postBinds

/-! ### §8.2 — `lightclient_turn_unfoolable_forest`: the WHOLE-TURN apex.

The headline. A verified turn — a `TurnDecodeChain` (every step's circuit `Satisfied2`, decoded, the
published seams agreeing) + the per-step effect-index identification (`hidx`) + the turn-level endpoint
pinning (`TurnEndpoints`) — together with the named floors (`hCR` + the carried per-effect family
`hrefines`) yields a GENUINE executor run `execFullTurnA start acts = some fin` whose ENDPOINTS commit
to the published turn-level `(pre, post)`. The light client RAN NOTHING; it verified per-step accepts
and read the two open ends of the chained-root column.

The derivation:
  1. `stepsRefine_of_descriptorRefines` discharges the per-step `dispatchArm` from the carried
     `hrefines` family + the per-step circuit accepts (`c.sat`) + faithful decodes (`d.decode`);
  2. `turnDecodeChain_refines_turnSpec` folds those along the threaded (kernel-half-certified) chain
     into `∃ acts, turnSpec start acts fin`;
  3. `execFullTurnA_iff_turnSpec` lowers `turnSpec` to the real executor `execFullTurnA`;
  4. `turnDecodeChain_endpoints_commit` re-exports the published turn-level pre/post as the genuine
     endpoint commitments (`S.commit start.kernel` / `S.commit fin.kernel`).

`execFullForestG`: the natural tree-shaped run lowers to this linear `execFullTurnA` by the existing
`Exec.FullForestAuth.execFullForestG_eq_execFullTurnG` / `Spec.WholeTurnTriangle` bridge — a forest is
the pre-order lowering of its turns, so this whole-turn statement is the linear core the forest run
factors through. -/
theorem lightclient_turn_unfoolable_forest
    (hash : List ℤ → ℤ) (S : CommitSurface) (R : Registry)
    (hCR : Poseidon2SpongeCR hash)
    (hrefines : ∀ e, descriptorRefines S hash (R e) (dispatchArm e))
    {start fin : RecChainedState} (c : TurnDecodeChain hash S start fin)
    (hidx : ∀ d ∈ c.steps, ∃ e : EffectIdx, d.descr = R e)
    (te : TurnEndpoints hash S c) :
    ∃ (acts : List FullActionA) (s s' : RecChainedState),
      execFullTurnA s acts = some s' ∧
      te.tp.pubPre = S.commit s.kernel te.tp.turn ∧
      te.tp.pubPost = S.commit s'.kernel te.tp.turn := by
  -- (1) the carried per-effect family discharges the per-step `dispatchArm` over the whole chain.
  have href : StepsRefine hash S R c :=
    stepsRefine_of_descriptorRefines hash S R hCR hrefines c hidx
  -- (2) fold the per-step refinement along the threaded chain into the declarative `turnSpec`.
  obtain ⟨acts, hturn⟩ := turnDecodeChain_refines_turnSpec hash S R c href
  -- (3) lower `turnSpec` to the genuine executor run.
  have hexec : execFullTurnA start acts = some fin :=
    (execFullTurnA_iff_turnSpec start fin acts).mpr hturn
  -- (4) the published turn-level commitments ARE the endpoint commitments (derived; §8.1).
  obtain ⟨hpre, hpost⟩ := turnDecodeChain_endpoints_commit hash S c te
  exact ⟨acts, start, fin, hexec, hpre, hpost⟩

#assert_axioms CommitSurface.commit_binds
#assert_axioms stateDecode_pre_faithful
#assert_axioms stateDecode_post_faithful
#assert_axioms stateDecodeChain_frame_continuous
#assert_axioms lightclient_unfoolable
#assert_axioms lightclient_turn_unfoolable
#assert_axioms turnDecodeChain_seam_kernel_derived
#assert_axioms turnDecodeChain_refines_turnSpec
#assert_axioms turnDecodeChain_endpoints_commit
#assert_axioms lightclient_turn_unfoolable_forest

end Dregg2.Circuit.CircuitSoundness
