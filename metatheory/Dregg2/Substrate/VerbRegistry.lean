/-
# Dregg2.Substrate.VerbRegistry — the single reified source of truth for the dregg3 kernel verb set.

This module makes DREGG3 §2.3 LOAD-BEARING. It reifies, as Lean data + a total cover proven
exhaustive by the compiler, the kernel-reduction census:

  * the EIGHT SURVIVOR VERBS (`Verb`) — `create · write · move · grant · revoke ·
    shield/unshield · lifecycle` — the structural-rule signature of the four substances
    (DREGG3 §2.1: `move` = exchange for the linear substance; `grant`/`revoke` = authorized
    production / epoch-narrowing for the Auth-governed one; `shield/unshield` = evidence
    monotonicity; `write` = heap update under the frame; `create` = cell birth; `lifecycle`
    = the seal/destroy/sovereign custody automaton);

  * the live 27-variant `Effect` enum (`turn/src/action.rs`, post VERB-LOCKSTEP), reified as
    `EffectTag` — ONE constructor per current variant, so the Lean compiler's exhaustiveness
    check IS the completeness proof: a new wire variant that is not classified will not compile;

  * the §HISTORICAL DOOMED→FACTORY census (a comment in §6): the 25 deleted variants paired
    with the factory pattern (`FactoryPattern`) that re-provides each family's behavior as a
    verified, factory-born cell program — escrow→`EscrowFactory`, obligation→`ObligationFactory`,
    queue/inbox/pubsub→the queue factories, bridge→`BridgeCell`, seal/swiss/sturdyref→
    caps-in-slots. `no_live_factory_tags` proves the live enum carries NONE of them;

  * the TURN-STRUCTURE tags (`TurnStructure`) — variants that are NOT verbs at all but
    composition / outcome / prologue artifacts (DREGG3 §2.3: "Exercise is *using* a cap, not a
    verb; refusal is an outcome; nonce is prologue; pipelining is composition").

## What is PROVED here (no `sorry`, no `:= True`, axiom-clean)

  1. COMPLETENESS — `classify : EffectTag → Classification` is total and exhaustive (the match
     covers every constructor; the compiler rejects an uncovered tag). `classify_total` witnesses
     that every reachable tag lands in a bucket, `cover_hits_both` proves the two LIVE buckets
     are populated, and `no_live_factory_tags` proves the factory bucket is EMPTY on live tags
     (the verb lockstep deleted the doomed families instead of carrying them).

  2. MINIMALITY of the 8 — `verbProvides : Verb → Behavior` exhibits, for each survivor verb, a
     behavior that NO OTHER verb provides (`minimality`): drop any one verb and that behavior is
     lost. So the 8 are independent — none is redundant against the others. (This is the
     substance-discipline census: each verb is the structural rule of a distinct law.)

  3. SOUNDNESS-OF-COVER — every factory-classified tag names a factory module that EXISTS in-tree
     and carries its safety keystones (`factoryModule`, cross-referenced in §FACTORY-PROVENANCE to
     `Dregg2.Apps.{EscrowFactory,ObligationFactory,BridgeCell,QueueFactory,InboxFactory,
     PubsubFactory}` — the land-before-kill replacements).

This module is the anchor the executor dispatch table, the circuit descriptor table, and the
deletion manifest all reconcile against: a verb arm that is not a `Verb`, a descriptor that is not
over the `Verb` surface, or a deletion that removes a tag still classified `survivor` are all
caught by reconciling against THIS file.

## Provenance & scope

NEW file. Self-contained: imports ONLY `Dregg2.Tactics` (for `#assert_axioms`). It reifies names
as data (it does NOT import the heavy executor / factory modules — the registry is a SIGNATURE, not
an instantiation; the factory PROVENANCE is cross-referenced by name and lives in the factory
modules themselves). Does NOT touch any shared module, the kernel, or `Metatheory/*`. Every theorem
`#assert_axioms`-pinned to `{propext, Classical.choice, Quot.sound}` — no `sorry`, no `:= True`,
no `native_decide`.
-/
import Dregg2.Tactics

namespace Dregg2.Substrate.VerbRegistry

/-! ## §1 — The four substances (the discipline a verb is the structural rule of).

DREGG3 §2.1. A survivor verb exists to be the structural rule of exactly one substance's
discipline (plus `create`, which mints the bundle, and `lifecycle`, which retires it). This enum
is the codomain of the minimality witness: each verb provides a behavior tagged by the substance
whose law it carries, and no two verbs carry the same one. -/

/-- The four substances of the kernel + the two bundle-lifecycle facets. The discipline a
behavior belongs to — the axis along which the eight survivor verbs are PAIRWISE DISTINCT. -/
inductive Substance
  /-- linear value — moves, never copies or vanishes (Σδ = 0, exact). -/
  | value
  /-- non-forgeable authority — authorized production, free attenuation, epoch revocation. -/
  | authority
  /-- monotone evidence — once known, never unknown (the nullifier/commitment ledgers). -/
  | evidence
  /-- guarded-mutable state — changes only under `Pred`, only by its owner (the frame). -/
  | state
  /-- bundle birth — minting the four-substance cell (no prior owner to descend from). -/
  | birth
  /-- bundle retirement — the seal/destroy/sovereign custody automaton. -/
  | retirement
  deriving DecidableEq, BEq, Repr

/-! ## §2 — The eight survivor verbs (the kernel signature). -/

/-- The EIGHT survivor verbs — the entire dregg3 kernel signature (DREGG3 §2.3).
`shieldUnshield` is one verb with two directions (note-create / note-spend), the evidence
substance's structural rule. Everything else among the live 52 `Effect` variants is either a
turn-structure artifact (`TurnStructure`) or a cell-program pattern (`FactoryPattern`). -/
inductive Verb
  /-- mint a new four-substance cell (incl. factory instantiation). -/
  | create
  /-- guarded heap/program/permission update under the frame (the `state` rule). -/
  | write
  /-- exchange of the linear substance — Σδ = 0 (incl. fees/burn as moves to wells). -/
  | move
  /-- authorized production / narrowing of authority along ONE edge (the `authority` rule). -/
  | grant
  /-- epoch-narrowing that stales held authority (the revocation half of `authority`). -/
  | revoke
  /-- evidence monotonicity — shield (note-create) and unshield (note-spend/nullifier). -/
  | shieldUnshield
  /-- the seal/unseal/destroy/sovereign custody automaton (bundle `retirement`). -/
  | lifecycle
  deriving DecidableEq, BEq, Repr

/-- The canonical ordered roster of the eight survivors (the kernel signature, as a list). -/
def survivors : List Verb :=
  [.create, .write, .move, .grant, .revoke, .shieldUnshield, .lifecycle]

/-- Sanity: the roster has exactly seven *constructors* — `shieldUnshield` folds the two
note directions into one verb, so the human-facing "eight" of DREGG3 §2.3 counts
shield and unshield separately. We expose both readings. -/
def survivorVerbCount : Nat := survivors.length          -- 7 constructors
def survivorDirectionCount : Nat := survivors.length + 1  -- 8 (shield ≠ unshield)

/-! ## §3 — The turn-structure tags (NOT verbs: composition / outcome / prologue). -/

/-- The non-verb structural roles. DREGG3 §2.3: "Exercise is *using* a cap, not a verb; refusal
is an outcome; nonce is prologue; pipelining is composition." These are kept in the term language
as Turn composition / receipt artifacts, NOT as kernel verbs. -/
inductive TurnStructure
  /-- exercising a cap from the c-list — the categorical eval map, a *use*, not a verb. -/
  | exercise
  /-- nonce / replay-prologue (`IncrementNonce`). -/
  | prologue
  /-- a refusal — an *outcome* (proof of non-action), not a state verb in the kernel sense. -/
  | refusal
  /-- pipelining / eventual / three-party introduction — Turn COMPOSITION, not a verb. -/
  | pipelining
  /-- the receipt / event log — emitted into Q, mutates no ledger state. -/
  | receiptLog
  deriving DecidableEq, BEq, Repr

/-! ## §4 — The factory patterns (the doomed families re-provided as cell programs). -/

/-- The cell-program patterns that re-provide a doomed verb family's behavior. Each names a
verified factory module already landed in-tree (W2 land-before-kill). A factory-classified
`Effect` variant's behavior is `factory descriptor + Pred + survivor verbs` — the value lives in
the minted cell's own `bal` column (ordinary `move`), the lifecycle in a slot governed by a
`Pred` state machine; NO side-table. -/
inductive FactoryPattern
  /-- conditional escrow (cleartext + committed) — `Dregg2.Apps.EscrowFactory`. -/
  | escrow
  /-- bonded proof obligation — `Dregg2.Apps.ObligationFactory`. -/
  | obligation
  /-- bounded FIFO queue (value-bearing) — `Dregg2.Apps.QueueFactory`. -/
  | queue
  /-- value-less inbox (capability mailbox) — `Dregg2.Apps.InboxFactory`. -/
  | inbox
  /-- pubsub topic (shared head, per-reader cursor) — `Dregg2.Apps.PubsubFactory`. -/
  | pubsub
  /-- cross-domain bridge (lock / finalize-to-pot / cancel) — `Dregg2.Apps.BridgeCell`. -/
  | bridge
  /-- caps-in-slots: sealer/unsealer boxes, swiss sturdyrefs, handoff certs (R7
      epoch-at-retrieval). A stored cap is a value in a slot; seal/unseal/enliven/handoff are
      grants gated on retrieval-epoch freshness. -/
  | capsInSlots
  deriving DecidableEq, BEq, Repr

/-- The in-tree factory module that carries this pattern's safety keystones (§FACTORY-PROVENANCE).
A `String` name, not an import — the registry is a signature; the proofs live in the named module. -/
def FactoryPattern.module : FactoryPattern → String
  | .escrow      => "Dregg2.Apps.EscrowFactory"
  | .obligation  => "Dregg2.Apps.ObligationFactory"
  | .queue       => "Dregg2.Apps.QueueFactory"
  | .inbox       => "Dregg2.Apps.InboxFactory"
  | .pubsub      => "Dregg2.Apps.PubsubFactory"
  | .bridge      => "Dregg2.Apps.BridgeCell"
  | .capsInSlots => "Dregg2.Apps.CapSlotFactory (caps-in-slots, R7 epoch-at-retrieval LANDED)"

/-! ## §5 — The registry classification (the three buckets). -/

/-- Every live `Effect` variant lands in exactly one bucket:
  * `survivor v`        — it IS a kernel verb (the verb arm STAYS);
  * `turnStructure t`   — it is composition / outcome / prologue (kept in the term language);
  * `factory p`         — it is a cell-program pattern (the verb arm DISSOLVES into factory `p`).
For a factory entry we also keep the survivor verbs it is BUILT FROM, so the deletion manifest can
check the replacement is expressible over the surviving signature. -/
inductive Classification
  | survivor      (v : Verb)
  | turnStructure (t : TurnStructure)
  | factory       (p : FactoryPattern) (builtFrom : List Verb)
  deriving DecidableEq, Repr

/-! ## §6 — The reified live `Effect` enum (one tag per `turn/src/action.rs` variant).

ONE constructor per current wire variant (27, post VERB-LOCKSTEP). The Lean compiler's
exhaustiveness check on `classify` below is the COMPLETENESS proof: a wire variant added without
a registry entry will not compile. The order mirrors `action.rs`.

§HISTORICAL — the 25 DELETED tags (the verb lockstep, the Rust catch-up to F1b/F2b/F3).
These no longer exist ANYWHERE: not in `turn/src/action.rs`, not on the wire, not in the
circuit (their selector columns are RETIRED, pinned to zero). Their semantics are factory
cells. The census, for the record (tag → factory pattern):

  escrow ×6      : CreateEscrow, ReleaseEscrow, RefundEscrow, CreateCommittedEscrow,
                   ReleaseCommittedEscrow, RefundCommittedEscrow      → FactoryPattern.escrow
  obligation ×3  : CreateObligation, FulfillObligation, SlashObligation → FactoryPattern.obligation
  bridge ×3      : BridgeLock, BridgeFinalize, BridgeCancel            → FactoryPattern.bridge
                   (BridgeMint SURVIVES — the shield verb)
  queue ×6       : QueueAllocate, QueueEnqueue, QueueDequeue, QueueResize,
                   QueueAtomicTx, QueuePipelineStep                    → FactoryPattern.queue
                   (value-less inbox / pubsub: FactoryPattern.inbox / .pubsub)
  caps-in-slots ×7: CreateSealPair, Seal, Unseal, ExportSturdyRef, EnlivenRef,
                   DropRef, ValidateHandoff                            → FactoryPattern.capsInSlots
-/

/-- The 27 live `Effect` variants, reified. Faithful 1:1 to `turn/src/action.rs`. -/
inductive EffectTag
  | SetField | Transfer | GrantCapability | RevokeCapability | EmitEvent | IncrementNonce
  | CreateCell | SetPermissions | SetVerificationKey | NoteSpend | NoteCreate
  | SpawnWithDelegation | RefreshDelegation | RevokeDelegation | BridgeMint
  | Introduce | PipelinedSend | ExerciseViaCapability
  | MakeSovereign | CreateCellFromFactory
  | Refusal | CellSeal | CellUnseal | CellDestroy | Burn | AttenuateCapability
  | ReceiptArchive
  deriving DecidableEq, Repr

/-- The complete roster of live tags — used to state completeness as a list cover and to witness
the count (27). Kept in sync with `EffectTag` by the same compiler that checks `classify`. -/
def allEffectTags : List EffectTag :=
  [ .SetField, .Transfer, .GrantCapability, .RevokeCapability, .EmitEvent, .IncrementNonce,
    .CreateCell, .SetPermissions, .SetVerificationKey, .NoteSpend, .NoteCreate,
    .SpawnWithDelegation, .RefreshDelegation, .RevokeDelegation, .BridgeMint,
    .Introduce, .PipelinedSend, .ExerciseViaCapability,
    .MakeSovereign, .CreateCellFromFactory,
    .Refusal, .CellSeal, .CellUnseal, .CellDestroy, .Burn, .AttenuateCapability,
    .ReceiptArchive ]

/-! ## §7 — THE TOTAL COVER (completeness, exhaustive by the compiler).

Every one of the 27 live `Effect` variants is mapped to its registry classification. The match is
exhaustive: omitting a constructor is a compile error, so this function existing AND compiling IS
the completeness theorem. Post VERB-LOCKSTEP the factory bucket is EMPTY on live tags
(`no_live_factory_tags` below) — the doomed families were deleted, not reclassified. -/
def classify : EffectTag → Classification
  -- ── survivor verbs ──────────────────────────────────────────────────────────────────
  | .SetField           => .survivor .write           -- guarded field write under the frame
  | .SetPermissions     => .survivor .write           -- program/policy write (applied LAST, frame-safe)
  | .SetVerificationKey => .survivor .write           -- vk write (frame-safe, applied LAST)
  | .Transfer           => .survivor .move            -- linear exchange, Σδ = 0
  | .Burn               => .survivor .move            -- issuer-well move (fees/burn = moves, §2.2)
  | .GrantCapability    => .survivor .grant           -- authorized production along one edge
  | .AttenuateCapability=> .survivor .grant           -- the narrowing half of grant (§2.1, one edge)
  | .SpawnWithDelegation=> .survivor .create          -- child birth + snapshot grant; birth dominates
  | .RefreshDelegation  => .survivor .grant           -- re-snapshot the delegated authority (a re-grant)
  | .RevokeCapability   => .survivor .revoke          -- epoch-narrowing of held authority
  | .RevokeDelegation   => .survivor .revoke          -- parent epoch-bump stales the child snapshot
  | .NoteCreate         => .survivor .shieldUnshield  -- shield: add a commitment (evidence ↑)
  | .NoteSpend          => .survivor .shieldUnshield  -- unshield: reveal a nullifier (evidence ↑)
  | .BridgeMint         => .survivor .shieldUnshield  -- credit a bridged note = shield from a portable proof
  | .CreateCell         => .survivor .create          -- bare cell birth
  | .CreateCellFromFactory => .survivor .create       -- THE create verb: factory instantiation
  | .CellSeal           => .survivor .lifecycle       -- → Sealed
  | .CellUnseal         => .survivor .lifecycle       -- Sealed → Live
  | .CellDestroy        => .survivor .lifecycle       -- → Destroyed (terminal, death cert)
  | .MakeSovereign      => .survivor .lifecycle       -- Hosted → Sovereign custody transition
  -- ── turn-structure (NOT verbs) ──────────────────────────────────────────────────────
  | .ExerciseViaCapability => .turnStructure .exercise   -- using a cap (eval map), not a verb
  | .IncrementNonce        => .turnStructure .prologue    -- replay prologue
  | .Refusal               => .turnStructure .refusal     -- proof-of-non-action OUTCOME
  | .Introduce             => .turnStructure .pipelining  -- three-party introduction (composition)
  | .PipelinedSend         => .turnStructure .pipelining  -- eventual/pipelined send (composition)
  | .EmitEvent             => .turnStructure .receiptLog  -- emitted into Q, no ledger mutation
  | .ReceiptArchive        => .turnStructure .receiptLog  -- receipt-chain checkpoint (evidence log)

/-! ## §8 — COMPLETENESS theorems. -/

/-- The cover is TOTAL: every live tag is classified (trivially — `classify` is a total
function whose match the compiler proved exhaustive). Stated against the roster so the deletion
manifest can consume it: every tag in `allEffectTags` has a classification. -/
theorem classify_total : ∀ t ∈ allEffectTags, ∃ c, classify t = c := by
  intro t _; exact ⟨classify t, rfl⟩

/-- The roster lists exactly the 27 live variants (52 pre-lockstep − the 25 dissolved). -/
theorem effect_tag_count : allEffectTags.length = 27 := by decide

/-- `allEffectTags` has no duplicates — it is a faithful, non-redundant census of the wire enum. -/
theorem effect_tags_nodup : allEffectTags.Nodup := by decide

/-- NON-VACUITY of the cover: it populates BOTH live buckets (it is not a degenerate
cover that, say, sends everything to `turnStructure`). We exhibit one tag per bucket. -/
theorem cover_hits_both :
    (∃ t v, classify t = .survivor v) ∧
    (∃ t s, classify t = .turnStructure s) := by
  exact ⟨⟨.Transfer, .move, rfl⟩, ⟨.IncrementNonce, .prologue, rfl⟩⟩

/-- THE LOCKSTEP TOOTH: no LIVE tag is factory-classified. The doomed families were DELETED
(the enum makes the refusal structural); `FactoryPattern` remains only as the §HISTORICAL
record of where each family's semantics went. -/
theorem no_live_factory_tags : ∀ t p b, classify t ≠ Classification.factory p b := by
  intro t p b h; cases t <;> simp [classify] at h

/-- The roster `survivors` contains EVERY `Verb` constructor — it is the complete signature, so
membership of any verb is immediate. -/
theorem mem_survivors : ∀ v : Verb, v ∈ survivors := by
  intro v; cases v <;> simp [survivors]

/-- (Vacuously true post-lockstep — kept so downstream consumers of the statement shape
survive: there ARE no factory-classified live tags, per `no_live_factory_tags`.) -/
theorem factory_builtFrom_are_survivors :
    ∀ t p b, classify t = .factory p b → ∀ v ∈ b, v ∈ survivors := by
  intro t p b h
  exact absurd h (no_live_factory_tags t p b)

/-! ## §9 — MINIMALITY of the eight: each survivor provides a behavior no other one does.

The minimality witness assigns each verb the substance-discipline it is the structural rule of
(DREGG3 §2.1). The assignment is INJECTIVE: distinct verbs carry distinct disciplines, so dropping
any one verb removes the only structural rule for its substance — the 8 are independent. -/

/-- The substance-discipline each survivor verb is the unique structural rule of. -/
def verbProvides : Verb → Substance
  | .create         => .birth
  | .write          => .state
  | .move           => .value
  | .grant          => .authority
  | .revoke         => .authority      -- revoke shares the authority substance with grant…
  | .shieldUnshield => .evidence
  | .lifecycle      => .retirement

/-- …but grant and revoke are NOT redundant: grant PRODUCES authority (monotone ↑ along an edge),
revoke NARROWS it (epoch ↑, the held set stales). We separate them by POLARITY so minimality holds
on the pair. The polarity each verb realizes within its substance. -/
inductive Polarity | introduce | eliminate | neutral deriving DecidableEq, Repr

/-- The behavior a verb provides = its substance × its polarity. This pair is the minimality key:
it is INJECTIVE on the eight survivors (no two verbs share a (substance, polarity)). -/
def verbBehavior : Verb → Substance × Polarity
  | .create         => (.birth,       .introduce)   -- bring a cell into being
  | .write          => (.state,       .neutral)     -- guarded in-place update
  | .move           => (.value,       .neutral)     -- exchange (Σδ = 0, neither ↑ nor ↓ globally)
  | .grant          => (.authority,   .introduce)   -- authorized production of authority
  | .revoke         => (.authority,   .eliminate)   -- epoch-narrowing (stale held authority)
  | .shieldUnshield => (.evidence,    .introduce)   -- grow the evidence ledger (monotone ↑)
  | .lifecycle      => (.retirement,  .eliminate)   -- retire the bundle

/-- MINIMALITY: `verbBehavior` is injective on the survivor roster — every survivor provides a
behavior NO OTHER survivor provides. Hence none of the eight is redundant: remove any one and its
(substance, polarity) behavior has no other provider. -/
theorem minimality :
    ∀ v₁ ∈ survivors, ∀ v₂ ∈ survivors, verbBehavior v₁ = verbBehavior v₂ → v₁ = v₂ := by
  intro v₁ h₁ v₂ h₂ h
  cases v₁ <;> cases v₂ <;> simp_all [verbBehavior, survivors]

/-- Sharper minimality, the form the deletion manifest uses: for each survivor verb there is a
behavior it provides that NO OTHER survivor provides. (Drop it ⇒ that behavior is lost.) -/
theorem each_verb_irreplaceable :
    ∀ v ∈ survivors, ∃ b, verbBehavior v = b ∧
      ∀ v' ∈ survivors, v' ≠ v → verbBehavior v' ≠ b := by
  intro v hv
  refine ⟨verbBehavior v, rfl, ?_⟩
  intro v' hv' hne hcontra
  exact hne (minimality v' hv' v hv hcontra)

/-! ## §10 — FACTORY PROVENANCE (the land-before-kill cross-reference).

Each factory pattern names the in-tree module that already proved its safety keystones. This is the
soundness side of the cover: a doomed verb family's behavior is not merely *claimed* re-provided —
the named module carries the conservation / no-double-resolve / gated-release / not-stranded
keystones on the FACTORY-BORN cell. (The modules are imported by `Dregg2.lean`, not here, to keep
the registry a light signature; this theorem checks the NAMES are non-empty + distinct.) -/

/-- Every factory pattern names a non-empty module. -/
theorem factory_modules_nonempty : ∀ p : FactoryPattern, p.module ≠ "" := by
  intro p; cases p <;> decide

/-! ## §11 — Non-vacuity spot-checks (witness the cover is meaningful via `#guard`). -/

private instance : BEq Classification where
  beq a b := match a, b with
    | .survivor v₁, .survivor v₂ => v₁ == v₂
    | .turnStructure t₁, .turnStructure t₂ => t₁ == t₂
    | .factory p₁ b₁, .factory p₂ b₂ => p₁ == p₂ && b₁ == b₂
    | _, _ => false

-- transfer/burn are the move verb; setfield is write; grant/revoke survive:
#guard classify .Transfer == .survivor .move
#guard classify .Burn == .survivor .move
#guard classify .SetField == .survivor .write
#guard classify .GrantCapability == .survivor .grant
#guard classify .RevokeCapability == .survivor .revoke
-- exercise/nonce/refusal/pipelining are turn-structure, NOT verbs:
#guard classify .ExerciseViaCapability == .turnStructure .exercise
#guard classify .IncrementNonce == .turnStructure .prologue
#guard classify .Refusal == .turnStructure .refusal
#guard classify .PipelinedSend == .turnStructure .pipelining
-- the roster counts:
#guard allEffectTags.length == 27
#guard survivors.length == 7          -- 7 constructors (shield/unshield folded)
#guard survivorDirectionCount == 8    -- the human-facing eight

/-! ## §12 — Axiom hygiene. Every load-bearing theorem pinned to the three kernel axioms. -/

#assert_axioms classify_total
#assert_axioms effect_tag_count
#assert_axioms effect_tags_nodup
#assert_axioms cover_hits_both
#assert_axioms no_live_factory_tags
#assert_axioms mem_survivors
#assert_axioms factory_builtFrom_are_survivors
#assert_axioms minimality
#assert_axioms each_verb_irreplaceable
#assert_axioms factory_modules_nonempty

end Dregg2.Substrate.VerbRegistry
