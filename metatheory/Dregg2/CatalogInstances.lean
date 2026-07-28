/-
# Dregg2.CatalogInstances — dregg1's three catalogs as derived Spec constructions.

Takes dregg1's three real catalogs and instantiates them as derived smart-constructors
over the small `Spec` primitives via the `Dregg2.Catalog` code-gen:

  * `StateConstraint` (`cell/src/program.rs:597`, ~29 variants)
  * `Authorization`  (`turn/src/action.rs`, ~10 variants)
  * `Effect`'s `LinearityClass` coloring (`turn/src/action.rs`'s `Effect` enum, 53 kinds)

⚠ **§3 HAS NO RUST TWIN, BY DESIGN.** It used to say it was "transcribed verbatim from
`Effect::linearity` (`turn/src/action.rs:1675`)". That function was DELETED on 2026-07-28
(HORIZONLOG B2): it had zero non-test callers, was never re-exported from the crate root, and
was a hand-maintained Rust twin of THIS theory — which the LAW (`ZERO Rust-authored AIRs`)
forbids. The coloring is authored HERE and nowhere else. The line number had also been wrong
for a long time, which is what a citation to a deleted function looks like from the inside.

⚠ **THE `rfl` TRIPWIRE ONLY FIRES ON LEAN EDITS.** `CatalogEffects §2`'s per-effect `rfl`s catch
a coloring change made *here*; nothing in them notices `turn/src/action.rs` gaining or losing an
`Effect` variant. That is how the catalog drifted in BOTH directions unobserved. The two-sided
check is `tests/src/effect_catalog_lean_rust_pin.rs`, which READS both this file's `EffectKind`
and the Rust `Effect` enum and pins their symmetric difference to an explicit, exact roster —
so an edit to EITHER side goes red. Add a kind here and you must account for it there.

Generated (codegen emits Guard triple + auto-`#assert_axioms`):
  * §1 — `StateConstraintGuard.*` — `StateConstraint` variants as `Guard` smart-constructors.
  * §2 — `AuthorizationGuard.*`   — `Authorization` variants as `Guard` smart-constructors.

Hand-written (codegen emits Guard triples; these are not Guards):
  * §3 — `effectLinearity : EffectKind → LinearityClass`, faithfully mirroring
    `Effect::linearity` (exhaustive match, no default arm) + conservation obligations.
  * `AnyOf`/`Not` carry explicit `by` proofs (still generated, not the default `simp [name]`).

A planted unproven hole fails at
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

/-! ## §3 — `Effect`'s `LinearityClass` coloring.

Hand-written (not generated): the coloring is a total map `EffectKind → LinearityClass`, not a
`Guard`. Exhaustive match, no default arm; conservation obligations derived from
`Spec.Conservation`. `EffectKind` carries only the variant discriminants — payloads do not affect
linearity. -/

section EffectLinearity

/-- The dregg1 `Effect` variant tags (`turn/src/action.rs`'s `pub enum Effect`). We carry only the
discriminant — the payloads are irrelevant to the `LinearityClass` coloring, which dispatches on
the constructor alone.

⚠ **APPEND-ONLY, like the Rust enum.** `Exec/FFI/Narrow.lean`'s `effectTag` and the marshalling
surface read this as an enumeration; the Rust `Effect` carries the same law for its positional
`postcard` discriminants ("PLACED LAST in the enum so its serde discriminant does NOT shift any
existing variant's index"). New kinds go at the END. -/
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
  -- APPENDED 2026-07-28: `Effect::Mint`, the cap-gated SUPPLY ENTRY. The catalog had NO `mint`
  -- kind at all while the deployed executor has had one — so the spec did not classify one of the
  -- two effects whose conservation matters most.
  | mint
  deriving DecidableEq, Repr

open LinearityClass

/-- **The coloring map.** Exhaustive `match`, NO default arm: a newly-added effect kind cannot
compile until it answers its color. Derived onto the `Spec.Conservation` `LinearityClass` primitive
(the SAME six colors `Spec/Conservation.lean §1` proves the classifier facts for), where the colors
mean exactly: `Conservative` ⇒ `requires_paired_sibling` (`Σδ = 0` in the domain, a matching
sibling delta); `Generative`/`Annihilative` ⇒ `is_disclosed_non_conservation` (the effect
legitimately BREAKS `Σδ = 0` and must bind the broken amount into the receipt). Those two are
mutually exclusive (`paired_and_disclosed_exclusive`), so each verb gets exactly one reading. -/
def effectLinearity : EffectKind → LinearityClass
  -- Conservative: paired-delta resource moves (Σδ = 0).
  | .transfer | .createEscrow | .releaseEscrow | .refundEscrow
  | .createCommittedEscrow | .releaseCommittedEscrow | .refundCommittedEscrow
  | .noteSpend | .noteCreate | .createObligation | .fulfillObligation | .slashObligation
  | .queueEnqueue | .queueDequeue | .queueAtomicTx | .queuePipelineStep
  | .bridgeLock | .bridgeCancel
  -- ⚑ THE SUPPLY PAIR — RECOLORED 2026-07-28, `.burn` FROM `Annihilative`.
  --
  -- `mint`/`burn` are TWO-SIDED ISSUER-MOVES against the asset's negative-capable WELL, so each is
  -- a paired debit/credit that conserves EXACTLY. `Annihilative` was a pre-well-model artifact and
  -- it was refuted on three independent sides:
  --
  --   1. **In Lean, by this tree's own kernel.** `Exec/IssuerMove.lean` proves
  --      `issuerBurnK_preserves_exact : ExactConservation k'` (burn = `src → issuerOf a`, the
  --      transfer with direction swapped), and `recKBurnAsset_is_issuerBurn` is the `rfl` receipt
  --      that the LIVE `.burnA` dispatch arm RUNS that mechanism. The one-sided law survives only
  --      as `recKBurnAssetLegacy`, whose whole purpose is to be the non-vacuity tooth that
  --      PROVABLY BREAKS `ExactConservation`. So `Annihilative` colored the live verb with the
  --      legacy mechanism's color.
  --   2. **In the ratified design.** `.docs-history-noclaude/SUPPLY-MODEL.md`: "Burn / self-redeem
  --      | holder → well (well toward 0, supply ↓) | conserves ✓". Supply is disclosed as a PAIRED
  --      LEDGER DELTA, never as a claim.
  --   3. **In the deployed executor.** `apply_burn` (`turn/src/executor/apply.rs`) debits the
  --      holder and credits `issuer_well_for(target)` — the well is a real cell in the ledger, so
  --      its delta is inside the per-asset `Σδ == 0` walk that `executor/atomic.rs`'s VERIFIED
  --      gate runs. `apply.rs` has exactly two `credit_balance` calls and both are the paired half
  --      of a supply move.
  --
  -- The reading `Annihilative` names — "supply is destroyed" — is true of the SUPPLY total, which
  -- is not one of `Spec.Conservation`'s four `Domain`s. In the `balance` domain, where the gate
  -- actually runs and where `requires_paired_sibling` is decided, a burn is a move.
  | .mint | .burn => Conservative
  -- Monotonic: scalar counters / refcounts going up.
  | .incrementNonce | .exportSturdyRef | .enlivenRef | .validateHandoff | .refusal => Monotonic
  -- Terminal: one-way state transitions, no inverse.
  | .revokeCapability | .revokeDelegation | .dropRef | .cellDestroy | .makeSovereign
  | .receiptArchive | .attenuateCapability | .cellSeal | .cellUnseal => Terminal
  -- Generative: creates a resource ex nihilo (disclosed non-conservation). `bridgeMint` is a
  -- DISCLOSED CROSS-CHAIN INFLOW: the value has no local paired source (it was spent on the other
  -- chain), so the local `Σδ` genuinely rises and the amount rides the receipt.
  | .bridgeMint | .createCell | .createCellFromFactory | .spawnWithDelegation
  | .queueAllocate | .queueResize | .createSealPair | .seal | .unseal
  | .grantCapability | .introduce => Generative
  -- Annihilative: destroys/removes a resource (disclosed non-conservation). `bridgeFinalize` is
  -- the exact dual of `bridgeMint` — a DISCLOSED CROSS-CHAIN OUTFLOW: the `Bridge` handler proves
  -- `delta = -amount` (the value leaves for the other chain, with no local well to receive it), so
  -- it is Annihilative, NOT Conservative. It is now the SOLE Annihilative kind, and that is the
  -- honest shape: a local burn has a counterparty, a cross-chain exit does not.
  | .bridgeFinalize => Annihilative
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

/-- A `bridgeFinalize` is `Annihilative`: a disclosed cross-chain OUTFLOW — the value leaves for
the other chain and there is no local sibling delta to pair against. Mirrors the `Bridge` handler's
`delta = -amount`. -/
theorem bridgeFinalize_annihilative : effectLinearity .bridgeFinalize = Annihilative := rfl

theorem bridgeFinalize_discloses :
    (effectLinearity .bridgeFinalize).is_disclosed_non_conservation = true := by
  rw [bridgeFinalize_annihilative]; rfl

/-! ### The supply pair — `mint`/`burn` are `Conservative` (recolored 2026-07-28).

⚑ Both were, or would have been, `Generative`/`Annihilative`. Both are two-sided issuer-moves
against the asset's negative-capable well, so both are paired and neither discloses a broken
`Σδ`. The reasoning is in the `effectLinearity` supply-pair comment; the refutations of the old
coloring are `Exec/IssuerMove.lean`'s `issuerBurnK_preserves_exact`, the ratified
`SUPPLY-MODEL.md`, and `apply.rs`'s holder→well `credit_balance`.

**These theorems are stated at BOTH poles on purpose.** A coloring fact of the form "the color is
X, therefore the X-obligation holds" is a `P → P` shape unless something exhibits the obligation
FAILING somewhere. So each supply verb carries the positive (`requires_paired_sibling = true`) AND
the negative (`is_disclosed_non_conservation = false`), and `bridgeFinalize` above carries the
opposite pair — the same two predicates come out `false`/`true` there. The predicates are
therefore proved NON-CONSTANT across the catalog, and no conjunct can be discharged by a tautology.
-/

/-- A `burn` is `Conservative`: a holder→well move, so its per-domain deltas sum to `0`. Mirrors
the deployed `Effect::Burn` / the verified `recKBurnAsset = issuerBurnK`. -/
theorem burn_conservative : effectLinearity .burn = Conservative := rfl

/-- A `mint` is `Conservative`: the dual well→holder move. Mirrors `Effect::Mint` /
`recKMintAsset = issuerMoveK`. -/
theorem mint_conservative : effectLinearity .mint = Conservative := rfl

/-- **Burn requires a paired sibling** (the positive pole) — its debit is only admissible matched
by the well's credit. -/
theorem burn_requires_paired :
    (effectLinearity .burn).requires_paired_sibling = true := by
  rw [burn_conservative]; rfl

/-- **Burn is NOT a disclosed non-conservation** (the negative pole, and the refutation of the old
coloring). By `conservative_discloses_nothing`, a `Conservative` receipt carries no disclosed
delta: a burn's amount is a ledger move, not a hole in `Σδ`. -/
theorem burn_not_disclosed :
    (effectLinearity .burn).is_disclosed_non_conservation = false := by
  rw [burn_conservative]; rfl

/-- **The old coloring is FALSE, stated as such** — not merely superseded. `effectLinearity .burn`
is provably not `Annihilative`, so a regression to it cannot be silent. -/
theorem burn_not_annihilative : effectLinearity .burn ≠ Annihilative := by decide

theorem mint_requires_paired :
    (effectLinearity .mint).requires_paired_sibling = true := by
  rw [mint_conservative]; rfl

theorem mint_not_disclosed :
    (effectLinearity .mint).is_disclosed_non_conservation = false := by
  rw [mint_conservative]; rfl

/-- **The two poles of `requires_paired_sibling`, side by side.** It HOLDS at the supply pair and
FAILS at the cross-chain exit — so `CatalogEffects.conservative_requires_paired`'s hypothesis is
satisfiable AND refutable over this very catalog, and the classifier is not the constant `true`. -/
theorem supply_paired_bridge_exit_not :
    (effectLinearity .burn).requires_paired_sibling = true ∧
    (effectLinearity .mint).requires_paired_sibling = true ∧
    (effectLinearity .bridgeFinalize).requires_paired_sibling = false ∧
    (effectLinearity .bridgeMint).requires_paired_sibling = false :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- The mirror-image statement for `is_disclosed_non_conservation`: FALSE at the supply pair, TRUE
at the two cross-chain flows. Together with the previous theorem this pins the recoloring as a
genuine reclassification of `burn` from one regime to the other, not a relabeling. -/
theorem supply_undisclosed_bridge_disclosed :
    (effectLinearity .burn).is_disclosed_non_conservation = false ∧
    (effectLinearity .mint).is_disclosed_non_conservation = false ∧
    (effectLinearity .bridgeFinalize).is_disclosed_non_conservation = true ∧
    (effectLinearity .bridgeMint).is_disclosed_non_conservation = true :=
  ⟨rfl, rfl, rfl, rfl⟩

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
    effectLinearity .bridgeFinalize = Annihilative ∧
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
#assert_axioms bridgeFinalize_annihilative
#assert_axioms bridgeFinalize_discloses
#assert_axioms burn_conservative
#assert_axioms mint_conservative
#assert_axioms burn_requires_paired
#assert_axioms burn_not_disclosed
#assert_axioms burn_not_annihilative
#assert_axioms mint_requires_paired
#assert_axioms mint_not_disclosed
#assert_axioms supply_paired_bridge_exit_not
#assert_axioms supply_undisclosed_bridge_disclosed
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
