/-
# Dregg2.CatalogInstances — dregg1's three catalogs as derived Spec constructions.

Takes dregg1's three real catalogs and instantiates them as derived smart-constructors
over the small `Spec` primitives via the `Dregg2.Catalog` code-gen:

  * `StateConstraint` (`cell/src/program.rs:597`, ~29 variants)
  * `Authorization`  (`turn/src/action.rs`, ~10 variants)
  * `Effect`'s `LinearityClass` coloring (`turn/src/action.rs: Effect::linearity`, ~52 effects)

Generated (codegen emits Guard triple + auto-`#assert_axioms`):
  * §1 — `StateConstraintGuard.*` — `StateConstraint` variants as `Guard` smart-constructors.
  * §2 — `AuthorizationGuard.*`   — `Authorization` variants as `Guard` smart-constructors.

Hand-written (codegen emits Guard triples; these are not Guards):
  * §3 — `effectLinearity : EffectKind → LinearityClass`, faithfully mirroring
    `Effect::linearity` (exhaustive match, no default arm) + conservation obligations.
  * `AnyOf`/`Not` carry explicit `by` proofs (still generated, not the default `simp [name]`).

Discipline: no `axiom`/`admit`/`native_decide`/`sorry`. A planted `sorry` fails at
generation time. Module-wide pinned via `#assert_namespace_axioms Dregg2.CatalogInstances`.
-/
import Dregg2.Catalog
import Dregg2.Spec.Conservation

namespace Dregg2.CatalogInstances

open Dregg2.Spec Dregg2.Spec.Guard Dregg2.Laws Dregg2.Catalog

/-! ## §1 — `StateConstraint` as derived `Guard` smart-constructors (`cell/src/program.rs:597`).

dregg1's `StateConstraint` is a per-cell-program admissibility predicate. Each variant reads
request projections first-party, or routes authority/witness variants through the verify seam.
Request projections are modelled as `Request → Nat` field-readers. `AnyOf`/`Not` carry explicit
`by` proofs; the rest use the default `simp [name]`. -/

section StateConstraintCatalog
variable {Request : Type} {Statement : Type} {Witness : Type} [Verifiable Statement Witness]

catalog StateConstraintGuard where
  -- FieldEquals { index, value }: the field projection `f` equals the constant `value`.
  | fieldEquals (f : Request → Nat) (value : Nat) :=
      firstParty (fun req => decide (f req = value))
      ⊨ (f req = value)
  -- FieldGte { index, value }: `f ≥ value` (the `balance ≥ amount` precondition shape).
  | fieldGe (f : Request → Nat) (value : Nat) :=
      firstParty (fun req => decide (value ≤ f req))
      ⊨ (value ≤ f req)
  -- FieldLte { index, value }: `f ≤ value`.
  | fieldLe (f : Request → Nat) (value : Nat) :=
      firstParty (fun req => decide (f req ≤ value))
      ⊨ (f req ≤ value)
  -- FieldLteField { left_index, right_index }: one field ≤ another.
  | fieldLeField (lhs rhs : Request → Nat) :=
      firstParty (fun req => decide (lhs req ≤ rhs req))
      ⊨ (lhs req ≤ rhs req)
  -- WriteOnce { index }: the field, once written (≠ 0 sentinel), equals its prior write `prev`.
  -- Modelled as "the current value equals the recorded prior value `prev`" — first-party equality.
  | writeOnce (f : Request → Nat) (prev : Nat) :=
      firstParty (fun req => decide (f req = prev))
      ⊨ (f req = prev)
  -- Immutable { index }: the field equals its prior value `prev` (never changes). Same shape as
  -- WriteOnce at the predicate level (both are "current = pinned"); the legacy distinction is in
  -- WHEN the pin is taken, not in the admitted predicate.
  | immutable (f : Request → Nat) (prev : Nat) :=
      firstParty (fun req => decide (f req = prev))
      ⊨ (f req = prev)
  -- Monotonic { index }: the field is ≥ its prior value `prev` (non-decreasing).
  | monotonic (f : Request → Nat) (prev : Nat) :=
      firstParty (fun req => decide (prev ≤ f req))
      ⊨ (prev ≤ f req)
  -- StrictMonotonic { index }: the field is STRICTLY greater than its prior value `prev`.
  | strictMono (f : Request → Nat) (prev : Nat) :=
      firstParty (fun req => decide (prev < f req))
      ⊨ (prev < f req)
  -- SumEquals { indices, value }: Σ of the field projections = `value` (a conservation constraint,
  -- e.g. Σ inputs = Σ outputs). DERIVED over `firstParty` decidable equality of a `List.sum`.
  | sumEquals (fs : List (Request → Nat)) (value : Nat) :=
      firstParty (fun req => decide ((fs.map (fun f => f req)).sum = value))
      ⊨ ((fs.map (fun f => f req)).sum = value)
  -- SumEqualsAcross { left_indices, right_indices }: Σ of one field-group = Σ of another
  -- (cross-cell / two-sided conservation, e.g. Σ debits = Σ credits).
  | sumEqualsAcross (lefts rights : List (Request → Nat)) :=
      firstParty (fun req =>
        decide ((lefts.map (fun f => f req)).sum = (rights.map (fun f => f req)).sum))
      ⊨ ((lefts.map (fun f => f req)).sum = (rights.map (fun f => f req)).sum)
  -- FieldDelta { index, delta }: the field changed by exactly `delta` (post = `target`). Modelled
  -- as "the field projection equals the computed target value".
  | fieldDelta (f : Request → Nat) (target : Nat) :=
      firstParty (fun req => decide (f req = target))
      ⊨ (f req = target)
  -- FieldDeltaInRange { index, lo, hi }: the field lies in `[lo, hi]` (a bounded delta).
  | fieldDeltaInRange (f : Request → Nat) (lo hi : Nat) :=
      firstParty (fun req => decide (lo ≤ f req ∧ f req ≤ hi))
      ⊨ (lo ≤ f req ∧ f req ≤ hi)
  -- FieldGteHeight { index, offset }: the field ≥ the (request-supplied) chain height + offset.
  -- We model `height` as another request projection.
  | fieldGeHeight (f height : Request → Nat) (offset : Nat) :=
      firstParty (fun req => decide (height req + offset ≤ f req))
      ⊨ (height req + offset ≤ f req)
  -- FieldLteHeight { index, offset }: the field ≤ the chain height + offset.
  | fieldLeHeight (f height : Request → Nat) (offset : Nat) :=
      firstParty (fun req => decide (f req ≤ height req + offset))
      ⊨ (f req ≤ height req + offset)
  -- BoundedBy { index, witness_index }: the field ≤ a witness-supplied bound (also a projection).
  | boundedBy (f bound : Request → Nat) :=
      firstParty (fun req => decide (f req ≤ bound req))
      ⊨ (f req ≤ bound req)
  -- BoundDelta { index, max_delta }: |post − prev| ≤ max_delta, modelled (with `prev` a projection)
  -- as the field staying within `max_delta` above its prior — a one-sided rate bound.
  | boundDelta (f prev : Request → Nat) (maxDelta : Nat) :=
      firstParty (fun req => decide (f req ≤ prev req + maxDelta))
      ⊨ (f req ≤ prev req + maxDelta)
  -- RateLimit { index, max }: a per-window counter field stays ≤ `max`.
  | rateLimit (f : Request → Nat) (max : Nat) :=
      firstParty (fun req => decide (f req ≤ max))
      ⊨ (f req ≤ max)
  -- MonotonicSequence { seq_index }: the sequence field is ≥ its prior (in-order delivery / nonce).
  | monotonicSequence (f : Request → Nat) (prev : Nat) :=
      firstParty (fun req => decide (prev ≤ f req))
      ⊨ (prev ≤ f req)
  -- CapabilityUniqueness { cap_set_root_slot }: the cap-set root field equals a unique witness
  -- value — first-party equality against the recorded root.
  | capabilityUniqueness (root : Request → Nat) (expected : Nat) :=
      firstParty (fun req => decide (root req = expected))
      ⊨ (root req = expected)
  -- SenderAuthorized { set }: the invoker is authorized — the `AuthRequired ⊣ Authorization` site.
  -- DERIVED: a `witnessed` guard over the authorization statement (the authority oracle is one of
  -- the eight `Verifiable` instances behind the seam). Needs an explicit proof (witnessed shape).
  | senderAuthorized (s : Statement) :=
      witnessed s
      ⊨ (Discharged s (w s))
      by simp [StateConstraintGuard.senderAuthorized, admits_witnessed, Discharged]
  -- Witnessed { wp }: a generic witnessed-predicate constraint — discharged through the verify
  -- seam exactly like SenderAuthorized, but over an arbitrary witnessed-predicate statement.
  | witnessedPred (s : Statement) :=
      witnessed s
      ⊨ (Discharged s (w s))
      by simp [StateConstraintGuard.witnessedPred, admits_witnessed, Discharged]
  -- TemporalGate { ... }: a time-window membership check, routed through the verify seam (dregg1's
  -- temporal verifier is a `Verifiable` instance — cf. `Crypto.Temporal`). DERIVED: `witnessed`.
  | temporalGate (s : Statement) :=
      witnessed s
      ⊨ (Discharged s (w s))
      by simp [StateConstraintGuard.temporalGate, admits_witnessed, Discharged]
  -- PreimageGate { ... }: a hash-preimage knowledge check, routed through the verify seam.
  | preimageGate (s : Statement) :=
      witnessed s
      ⊨ (Discharged s (w s))
      by simp [StateConstraintGuard.preimageGate, admits_witnessed, Discharged]
  -- TemporalPredicate { ... }: a DFA/temporal-predicate acceptance check (dregg1's Dfa verifier,
  -- cf. `Crypto.Dfa`), routed through the verify seam.
  | temporalPredicate (s : Statement) :=
      witnessed s
      ⊨ (Discharged s (w s))
      by simp [StateConstraintGuard.temporalPredicate, admits_witnessed, Discharged]
  -- AllowedTransitions { transitions }: the (prev, post) pair lies in an allowed-transition set.
  -- Modelled as a first-party membership test against a decidable `allowed : Nat → Nat → Bool`
  -- predicate over the prior and current field projections.
  | allowedTransitions (prev post : Request → Nat) (allowed : Nat → Nat → Bool) :=
      firstParty (fun req => allowed (prev req) (post req))
      ⊨ (allowed (prev req) (post req) = true)
  -- AnyOf { constraints }: disjunctive — admits iff some alternative does. DERIVED over `any`
  -- (the OneOf coproduct). Recursive over a list of sub-guards; needs the `admits_any` structural
  -- characterization, so an explicit `by`.
  | anyOf (gs : List (Guard Request Statement)) :=
      any gs
      ⊨ (∃ g ∈ gs, admits g req w = true)
      by rw [StateConstraintGuard.anyOf]; exact admits_any gs req w
  -- Not (the negation primitive surfacing as a constraint): admits iff the inner guard does NOT.
  -- DERIVED over `gnot`. Needs the `admits_gnot` structural characterization.
  | gnot (g : Guard Request Statement) :=
      Guard.gnot g
      ⊨ (¬ admits g req w = true)
      by simp [StateConstraintGuard.gnot]

end StateConstraintCatalog

/-! ## §2 — `Authorization` as derived `Guard` smart-constructors (`turn/src/action.rs`).

dregg1's `Authorization` answers "who may invoke this object". Each auth kind is the same
structure as a state-constraint guard: first-party (decidable) or witnessed (verify seam).
`Signature`/`Bearer`/`Stealth`/`Token`/`Proof` are all `witnessed s`; `Unchecked` is `all []`;
`OneOf` is `any`. Generated as the same Guard triple. -/

section AuthorizationCatalog
variable {Request : Type} {Statement : Type} {Witness : Type} [Verifiable Statement Witness]

catalog AuthorizationGuard where
  -- Signature(pubkey, sig): a signature check — routed through the verify seam (the signature
  -- verifier is a `Verifiable` instance). DERIVED: `witnessed s`.
  | signature (s : Statement) :=
      witnessed s
      ⊨ (Discharged s (w s))
      by simp [AuthorizationGuard.signature, admits_witnessed, Discharged]
  -- Proof { ... }: a zk-proof authorization — verify seam.
  | proof (s : Statement) :=
      witnessed s
      ⊨ (Discharged s (w s))
      by simp [AuthorizationGuard.proof, admits_witnessed, Discharged]
  -- Breadstuff(commitment): a breadstuff (note-style) authorization commitment — verify seam.
  | breadstuff (s : Statement) :=
      witnessed s
      ⊨ (Discharged s (w s))
      by simp [AuthorizationGuard.breadstuff, admits_witnessed, Discharged]
  -- Bearer(BearerCapProof): a bearer-capability proof — verify seam (the macaroon/bearer verifier).
  | bearer (s : Statement) :=
      witnessed s
      ⊨ (Discharged s (w s))
      by simp [AuthorizationGuard.bearer, admits_witnessed, Discharged]
  -- Stealth { ... }: a stealth-address authorization — verify seam (one-time-address verifier).
  | stealth (s : Statement) :=
      witnessed s
      ⊨ (Discharged s (w s))
      by simp [AuthorizationGuard.stealth, admits_witnessed, Discharged]
  -- Token { ... }: a token-presentation authorization — verify seam.
  | token (s : Statement) :=
      witnessed s
      ⊨ (Discharged s (w s))
      by simp [AuthorizationGuard.token, admits_witnessed, Discharged]
  -- CapTpDelivered { ... }: a CapTP-delivery authorization (the cap arrived over a verified
  -- session) — verify seam.
  | capTpDelivered (s : Statement) :=
      witnessed s
      ⊨ (Discharged s (w s))
      by simp [AuthorizationGuard.capTpDelivered, admits_witnessed, Discharged]
  -- Unchecked: no authorization required — the NEUTRAL guard, always admits. DERIVED: `all []`
  -- (the top of the meet-semilattice / the empty conjunction).
  | unchecked :=
      all ([] : List (Guard Request Statement))
      ⊨ True
      by simp [AuthorizationGuard.unchecked]
  -- OneOf { auths }: disjunctive authorization — admits iff some alternative authorizes. DERIVED
  -- over `any` (the OneOf coproduct); needs the `admits_any` structural characterization.
  | oneOf (gs : List (Guard Request Statement)) :=
      any gs
      ⊨ (∃ g ∈ gs, admits g req w = true)
      by rw [AuthorizationGuard.oneOf]; exact admits_any gs req w

end AuthorizationCatalog

/-! ## §3 — `Effect`'s `LinearityClass` coloring (`turn/src/action.rs: Effect::linearity`).

Hand-written (not generated): the coloring is a total map `Effect → LinearityClass`, not a
`Guard`. Faithfully mirrors `Effect::linearity` (exhaustive match, no default arm); conservation
obligations derived from `Spec.Conservation`. `EffectKind` carries only the ~52 variant
discriminants — payloads do not affect linearity. -/

section EffectLinearity

/-- The dregg1 `Effect` variant tags (`turn/src/action.rs:760`, ~52 variants). We carry only the
discriminant — the payloads are irrelevant to the `LinearityClass` coloring, which dispatches on
the constructor alone. This is the catalog of effect kinds; the coloring below is the faithful
transcription of `Effect::linearity`. -/
inductive EffectKind where
  | setField | transfer | grantCapability | revokeCapability | emitEvent | incrementNonce
  | createCell | setPermissions | setVerificationKey | noteSpend | noteCreate | createSealPair
  | seal | unseal | spawnWithDelegation | refreshDelegation | revokeDelegation | bridgeMint
  | bridgeLock | bridgeFinalize | bridgeCancel | introduce | pipelinedSend | createObligation
  | fulfillObligation | slashObligation | createEscrow | releaseEscrow | refundEscrow
  | createCommittedEscrow | releaseCommittedEscrow | refundCommittedEscrow | exerciseViaCapability
  | makeSovereign | createCellFromFactory | queueAllocate | queueEnqueue | queueDequeue
  | queueResize | queueAtomicTx | queuePipelineStep | exportSturdyRef | enlivenRef | dropRef
  | refusal | validateHandoff | cellSeal | cellUnseal | cellDestroy | burn | attenuateCapability
  | receiptArchive
  deriving DecidableEq, Repr

open LinearityClass

/-- **The coloring map** — `Effect::linearity`, transcribed verbatim from `turn/src/action.rs:1675`.
Exhaustive `match`, NO default arm: a newly-added effect kind cannot compile until it answers its
color. This is the dregg1 `Effect::linearity` total map, derived onto the `Spec.Conservation`
`LinearityClass` primitive (the SAME six colors `Spec/Conservation.lean §1` proves the classifier
facts for). -/
def effectLinearity : EffectKind → LinearityClass
  -- Conservative: paired-delta resource moves (Σδ = 0).
  | .transfer | .createEscrow | .releaseEscrow | .refundEscrow
  | .createCommittedEscrow | .releaseCommittedEscrow | .refundCommittedEscrow
  | .noteSpend | .noteCreate | .createObligation | .fulfillObligation | .slashObligation
  | .queueEnqueue | .queueDequeue | .queueAtomicTx | .queuePipelineStep
  | .bridgeLock | .bridgeFinalize | .bridgeCancel => Conservative
  -- Monotonic: scalar counters / refcounts going up.
  | .incrementNonce | .exportSturdyRef | .enlivenRef | .validateHandoff | .refusal => Monotonic
  -- Terminal: one-way state transitions, no inverse.
  | .revokeCapability | .revokeDelegation | .dropRef | .cellDestroy | .makeSovereign
  | .receiptArchive | .attenuateCapability | .cellSeal | .cellUnseal => Terminal
  -- Generative: creates a resource ex nihilo (disclosed non-conservation).
  | .bridgeMint | .createCell | .createCellFromFactory | .spawnWithDelegation
  | .queueAllocate | .queueResize | .createSealPair | .seal | .unseal
  | .grantCapability | .introduce => Generative
  -- Annihilative: destroys a resource (disclosed non-conservation).
  | .burn => Annihilative
  -- Neutral: no resource delta; pure book-keeping.
  | .setField | .emitEvent | .setPermissions | .setVerificationKey | .refreshDelegation
  | .pipelinedSend | .exerciseViaCapability => Neutral

/-! ### §3.1 — Per-effect conservation obligations (the coincidence facts).

For each color, derived from `Spec.Conservation`'s proved classifier facts. Each pins a
representative effect to its obligation. -/

/-- A `transfer` is `Conservative`: its per-domain deltas must sum to `0` (it requires a paired
sibling). Mirrors `Effect::Transfer => Conservative`. -/
theorem transfer_conservative : effectLinearity .transfer = Conservative := rfl

/-- The `Conservative` color's obligation is exactly "requires a paired sibling" — derived from the
`Spec.Conservation` PROVED classifier `requires_paired_sibling_iff`. So a `transfer`'s legacy
obligation (Σδ = 0, paired) coincides with the `Conservation` law. -/
theorem transfer_requires_paired :
    (effectLinearity .transfer).requires_paired_sibling = true := by
  rw [transfer_conservative]; rfl

/-- A `bridgeMint` is `Generative`: a disclosed non-conservation (the minted amount is bound into
the receipt). Mirrors `Effect::BridgeMint => Generative`. -/
theorem bridgeMint_generative : effectLinearity .bridgeMint = Generative := rfl

/-- The `Generative` color's obligation is "disclosed non-conservation" — derived from
`is_disclosed_non_conservation_iff`. A mint legitimately breaks Σδ = 0, but its delta is FORCED
into the receipt. -/
theorem bridgeMint_discloses :
    (effectLinearity .bridgeMint).is_disclosed_non_conservation = true := by
  rw [bridgeMint_generative]; rfl

/-- A `burn` is `Annihilative`: also a disclosed non-conservation. Mirrors `Effect::Burn`. -/
theorem burn_annihilative : effectLinearity .burn = Annihilative := rfl

theorem burn_discloses :
    (effectLinearity .burn).is_disclosed_non_conservation = true := by
  rw [burn_annihilative]; rfl

/-- A `setField` is `Neutral`: it touches no conserved quantity (neither paired nor disclosed).
Mirrors `Effect::SetField => Neutral`. -/
theorem setField_neutral : effectLinearity .setField = Neutral := rfl

theorem setField_inert :
    (effectLinearity .setField).requires_paired_sibling = false ∧
    (effectLinearity .setField).is_disclosed_non_conservation = false := by
  rw [setField_neutral]; exact ⟨rfl, rfl⟩

/-- An `incrementNonce` is `Monotonic`: it may only grow (no paired sibling, not disclosed-breaking).
Mirrors `Effect::IncrementNonce => Monotonic`. -/
theorem incrementNonce_monotonic : effectLinearity .incrementNonce = Monotonic := rfl

/-- A `cellDestroy` is `Terminal`: one-way, no inverse. Mirrors `Effect::CellDestroy => Terminal`. -/
theorem cellDestroy_terminal : effectLinearity .cellDestroy = Terminal := rfl

/-- The coloring covers all six colors — every color is witnessed by at least one effect.
`paired` ⊥ `disclosed` (from `Spec.Conservation.paired_and_disclosed_exclusive`) keeps
the conserved and disclosed-broken regimes disjoint. -/
theorem effectLinearity_covers_all_colors :
    effectLinearity .transfer = Conservative ∧
    effectLinearity .incrementNonce = Monotonic ∧
    effectLinearity .cellDestroy = Terminal ∧
    effectLinearity .bridgeMint = Generative ∧
    effectLinearity .burn = Annihilative ∧
    effectLinearity .setField = Neutral :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- The conserved/disclosed regimes are disjoint on EVERY effect — inherited from
`Spec.Conservation.paired_and_disclosed_exclusive` applied at each effect's color. No effect both
requires a paired sibling and is a disclosed non-conservation. -/
theorem effect_paired_disclosed_exclusive (e : EffectKind) :
    ¬ ((effectLinearity e).requires_paired_sibling = true ∧
       (effectLinearity e).is_disclosed_non_conservation = true) :=
  LinearityClass.paired_and_disclosed_exclusive (effectLinearity e)

end EffectLinearity

/-! ## §4 — Axiom-hygiene tripwires for the hand-written §3 facts.

§1/§2 catalog entries are auto-pinned by the codegen. The hand-written §3 effect-coloring
facts are pinned here explicitly to match the same discipline. -/

#assert_axioms transfer_conservative
#assert_axioms transfer_requires_paired
#assert_axioms bridgeMint_generative
#assert_axioms bridgeMint_discloses
#assert_axioms burn_annihilative
#assert_axioms burn_discloses
#assert_axioms setField_neutral
#assert_axioms setField_inert
#assert_axioms incrementNonce_monotonic
#assert_axioms cellDestroy_terminal
#assert_axioms effectLinearity_covers_all_colors
#assert_axioms effect_paired_disclosed_exclusive

-- Blanket module-wide pin: every theorem under this namespace must rest only on the three
-- kernel axioms. Pure rejector; cannot close a goal.
#assert_namespace_axioms Dregg2.CatalogInstances

end Dregg2.CatalogInstances
