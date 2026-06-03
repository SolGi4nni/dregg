# FEATURE-BUILD-BRIEFING — five upcoming Lean4 verification tracks for dregg2

*Research date: 2026-06-03. Lean v4.30, mathlib + aesop deps already present. Read-only:
every `file_path:symbol` below was verified against the actual `metatheory/Dregg2/` code, not
speculated. All paths absolute under `/Users/ember/dev/breadstuffs`.*

Repo root: `/Users/ember/dev/breadstuffs` · Lean tree: `metatheory/Dregg2/` · root import file:
`metatheory/Dregg2.lean`.

The living-cell substrate every track builds against:

- `metatheory/Dregg2/Exec/CellReal.lean:30` `cellObsA : RecChainedState → AssetId → ℤ` (per-asset
  conservation badge), `:36` `ConservingForest`, `:41`
  `cellNextA (s : RecChainedState) (cf : ConservingForest) : RecChainedState`
  (commit-on-`some` / stay-put-on-`none` real executor step), `:116` `SchedA := Nat → ConservingForest`,
  `:119` `trajA (s) (sched) : Nat → RecChainedState`.
- `metatheory/Dregg2/Exec/CellCarry.lean:57`
  `livingCellA_carries (Good) (hpres : ∀ s cf, Good s → Good (cellNextA s cf)) (s) (hinit : Good s) (sched) : ∀ n, Good (trajA s sched n)`
  — THE parametric coinductive crown every safety property routes through.

---

## TRACK 1 — THE HATCHERY API (the toolkit the other tracks reuse)

Four built, kernel-clean (`#assert_axioms`-pinned to `{propext, Classical.choice, Quot.sound}`) modules.
Public surface, exactly:

### `metatheory/Dregg2/Verify/Tactics.lean` — Tier 1 (the boilerplate-killer tactics)

- **`carry_forever Good`** (`:58`, a `macro`). Reduces a goal `∀ n, Good (trajA s sched n)` to the two
  named subgoals `hpres` and `hinit` via `refine livingCellA_carries $Good ?hpres _ ?hinit _`. `s`/`sched`
  unify silently from the goal.
- **`exec_frame (grow)?`** (`:76`, an `elab`). Proves `∀ s cf, Good s → Good (cellNextA s cf)`:
  `intro s cf hgood` → `simp only [cellNextA]` → `rcases hc : execFullForestA s cf.1 with _ | s'`
  (flat form so an unclosed commit goal ESCAPES to the caller) → the **reject/stay-put arm is closed
  universally** (`Option.getD_none; exact hgood`) → the commit arm tries, in order:
  `exact Trans.trans hgood ($grow s s' cf.1 hc)` (if a forest-grow lemma supplied), then
  `aesop (rule_sets := [Dregg2])`, then **honest hand-back** (`skip` — never a hidden `sorry`; the
  open commit goal exposes `hgood`/`s`/`s'`/`cf`/`hc` as raw binders, see `logMono_handback_demo:166`).
  Optional `grow` parsed with `colGt`.
- Minimal usage (the four gate theorems, `:117`–`:155`):
  ```
  theorem foo (s) (sched) : ∀ n, P (trajA s sched n) := by
    carry_forever (fun s' => P s')
    case hpres => exec_frame someForestGrowLemma   -- or bare `exec_frame` for [Dregg2] auto
    case hinit => exact <base proof>
  ```

### `metatheory/Dregg2/Verify/Frames.lean` — Tier 2 (reusable forest-monotone combinator + aesop rule-set)

- **`cellNextA_carries_rel`** (`:80`): one-step packager parametric in a `[Trans R R R]` relation,
  a `proj : RecChainedState → α`, and a `forestGrow` witness.
- **`livingCellA_carries_rel`** (`:99`): the forever combinator — feeds the above to `livingCellA_carries`.
  Concrete instances: `commitments_grow_forever:145`, `nullifiers_grow_forever:153`,
  `revoked_grow_forever:161`, `logLen_grow_forever:170` (covers `⊆` and `Nat`'s `≤`).
- The **`[Dregg2]` aesop rule-set** is *declared* in `metatheory/Dregg2/Catalog.lean` and *populated*
  here (`:193`–`:238`): `List.Subset.trans` (unsafe 50%), the COMMITMENTS `_eq` per-mutator frame family,
  and the public forest-grow lifts `execFullForestA_{commitments,nullifiers}_grow` +
  `Dregg2.Apps.Identity.execFullForestA_revoked_grow`.

### `metatheory/Dregg2/Verify/Contract.lean` — Tier 3 (the first-class `CellContract` object)

- **`SafetyShape`** (`:73`): `| monotone | membership | constant | other`, `DecidableEq, Repr`.
- **`CellContract`** (`:92`): fields `Inv : RecChainedState → Prop`,
  `step_ob : ∀ s cf, Inv s → Inv (cellNextA s cf)`, `shape : SafetyShape := .other`.
- **`CellContract.forever`** (`:105`): `(C) (h : C.Inv s) (sched) : ∀ n, C.Inv (trajA s sched n)`
  — body is `livingCellA_carries C.Inv C.step_ob s h sched`.
- **`CellContract.always`** (`:116`): `(C) (h : C.Inv s) (sched) : Always C.Inv s sched`
  — body is `always_of_step_invariant C.Inv C.step_ob s h sched` (the Track-2 `□`).
- Concrete contracts: `logAppendOnly:139`, `conserved:148`, `revokedPersists:162`,
  `nameRegisteredContract:192`, `subWFContract:209`.

### `metatheory/Dregg2/Verify/Catalog.lean` — Tier 4 (declarative shape macros — the spec language)

Each `term`-macro expands to a real `CellContract` whose `step_ob` is discharged through the
Tier-1/2 engine:
- **`monotone_registry% f x`** (`:70`, `f ∈ {revoked, commitments, nullifiers}`) → `x ∈ ·.kernel.f`,
  `shape := .membership`. Usage: `(monotone_registry% revoked credNul).forever hinit sched` (`:208`).
- **`conservation% a`** (`:120`) → expands to `fun (s0 : RecChainedState) => {Inv := cellObsA · a = cellObsA s0 a, …}`,
  `shape := .constant`. Bind the baseline at the use site: `(conservation% (0 : AssetId)) fma0` (`:228`).
- **`confinement% U`** (`:148`) → expands to `fun (hctrl : Auth.control ∈ U) => {Inv := CapsConfined U ·.kernel.caps, …}`,
  `shape := .other`; surfaces the `control ∈ U` hypothesis honestly. Usage:
  `(confinement% fullAuthCeiling) (by decide)` (`:239`). Depends on `metatheory/Dregg2/Exec/CellConfine.lean`.
- **`automaton_inv% a b`** (`:179`) → `fun s0 => {Inv := cellObsA · a + cellObsA · b = cellObsA s0 a + cellObsA s0 b, …}`,
  `shape := .other`; commit arm closed by `cellObsA_next` ×2 + `omega`.

**Recommended new modules for Track 1:** none required — Track 1 *is* the toolkit. The other four tracks
should `import Dregg2.Verify.Catalog` (transitively pulls Contract/Tactics/Frames) and reuse
`carry_forever`/`exec_frame`/`CellContract` rather than re-typing `livingCellA_carries` skeletons. The
one honest gap in Tier 4 (documented at `Catalog.lean:27`–`:33`): **`eventually% Goal` / liveness `◇`-shapes
are deferred to the CTL/μ workflow** — i.e. Track 2 should add the `◇`-shape macro back into this catalog.

---

## TRACK 2 — CTL / μ-CALCULUS TEMPORALITY

### What exists (the LTL layer + the LTS abstraction)

- `metatheory/Dregg2/Execution.lean` — the **abstract transition-system vocabulary**: `:23` `System`
  (`Config : Type u`, `Step : Config → Config → Prop`), `:33` `Run` (reflexive-transitive closure),
  `:51` `StepInvariant`, `:57` `invariant_run`, `:65` `Safe`/`:70` `safe_of_stepInvariant`, `:76` `Final`,
  `:81` `Progresses` (the stated-but-unproved deadlock-freedom target).
- `metatheory/Dregg2/Proof/Temporal.lean` — **LTL `□`/`◇`/`◯` over the living cell's `trajA`**:
  `:73` `Always (□)`, `:78` `Eventually (◇)`, `:84` `Next (◯)`. Headline `:101`
  `always_of_step_invariant` (= `livingCellA_carries` in modal dress). Modal algebra:
  `always_now:111`, `always_mono:117`, `always_and:124`, `always_idem:177` (S4, via `trajA_add:158` +
  `dropSched:152`), `eventually_of_now:186`, `eventually_of_always:193`,
  `not_eventually_iff_always_not:205`, `not_always_iff_eventually_not:215`, `always_imp_next:225`.
  Cross-check to reachability: `:250` `livingSystem := inducedSystem livingCellA`, `:256`
  `trajA_reachable`, `:270` `always_of_reachable_invariant`, `:281` `always_iff_reachable`.
  Concrete `□`-safeties: `always_conserved:306`, `always_logMono:318`, `always_revoked_persists:341`,
  `always_conj_safety:352`.
- `metatheory/Dregg2/Proof/LTS.lean` — the **operational small-step LTS + forward-simulation square**:
  `recAbsStep:51`, `AbsStep:61`, `AbsRun:112`, `recAbsStep_forward:81`, `authAbsStep:227`,
  `AbsStep':270`, `absStep'_forward:288`. Multi-cell lifts in `Proof/CrossCellLTS.lean`
  (`crossAbsStep`, `crossAbsStep_forward`) and `Proof/ForestLTS.lean` (N-ary `forestApply`/
  `forestAbsStep`/`forestAbsStep_forward` over a `Fintype ι`).

What the LTL layer is NOT (honest residue, `Temporal.lean:36`–`:49`): no Hoare/WP over the forest
executor, **no branching CTL `∀◇`/`∃□` over the schedule tree**, no `U`-calculus, no liveness under
fairness. These are exactly Track 2's targets.

### Cleanest path to add CTL + the modal μ-calculus

**`Mathlib.Order.FixedPoints` is ALREADY a transitive dependency and in active use.** It is imported at
`metatheory/Dregg2/Paco/Basic.lean:3`, and `OrderHom.lfp`/`OrderHom.gfp`/`OrderHom.le_gfp`/
`OrderHom.map_gfp` are used throughout `Dregg2/Paco/**` and `Dregg2/Proof/CoinductiveAdversary.lean:394`
(`F.toOrderHom.gfp`). So no new lakefile dep is needed — `import Mathlib.Order.FixedPoints` directly.

Build over `Execution.System` (state-set semantics), NOT over `trajA` (which is schedule-indexed, hence
linear). The state-predicate carrier is `Set State` = `State → Prop`, a `CompleteLattice`. Pre-image of
`Step` gives the two basic modalities; `OrderHom.lfp`/`gfp` give the recursive ones:

- `EX P := {s | ∃ t, S.Step s t ∧ P t}` ; `AX P := {s | ∀ t, S.Step s t → P t}` (plain monotone maps).
- `EF P := OrderHom.lfp ⟨fun Q => P ⊔ EX Q, mono⟩` ; `AF P := OrderHom.lfp ⟨fun Q => P ⊔ AX Q, mono⟩`.
- `EG P := OrderHom.gfp ⟨fun Q => P ⊓ EX Q, mono⟩` ; `AG P := OrderHom.gfp ⟨fun Q => P ⊓ AX Q, mono⟩`.
- `EU P R := OrderHom.lfp ⟨fun Q => R ⊔ (P ⊓ EX Q), mono⟩` ; `AU` dually.
- Each `OrderHom` needs only a `Monotone` proof (the modal maps are monotone in `Q`); `lfp`/`gfp` then
  supply Knaster–Tarski + Park induction/coinduction for free.

The μ-calculus proper: a `Kripke` frame = the `System` + an atomic valuation, formulas interpreted as
`OrderHom (Set State) (Set State)`, with `μX.φ := OrderHom.lfp φ` and `νX.φ := OrderHom.gfp φ`
named instances. Lean 4.30's `coinductive` keyword (used natively at
`Dregg2/Proof/CoinductiveAdversary.lean:85` for `ObsBisim`) is the alternative for the relational
`νF` face; for the *state-set* μ-calculus the `OrderHom.lfp/gfp` route is cleaner and reuses the
existing fixpoint algebra.

**Bridges to land (the non-vacuity payoff):**
- `AG P` over `livingSystem` ≡ `∀ sched, Always P` — already half-proved as
  `Temporal.always_iff_reachable:281`. The new CTL `AG` should be defeq-bridged to it.
- `EF`(committed-with-progress) over `livingSystem` is the first genuine branching liveness — gives
  Track 4's `Progresses` (`Execution.lean:81`) a temporal statement.

**Recommended new modules for Track 2:**
1. `metatheory/Dregg2/Proof/CTL.lean` — `EX/AX/EU/AU/EF/AF/EG/AG : (S.Config → Prop) → (S.Config → Prop)`
   over `Execution.System`, the unfolding laws (`EF P = P ⊔ EX (EF P)` etc. from `OrderHom.map_lfp`),
   the `AG`↔`always_iff_reachable` bridge, the `EF`↔reachability bridge, the CTL duality lemmas.
2. `metatheory/Dregg2/Proof/MuCalculus.lean` — the Kripke frame, `μ`/`ν` as named `OrderHom.lfp/gfp`,
   the encoding `EF/EG/AF/AG` as μ/ν instances, Park induction examples.
3. Extend `metatheory/Dregg2/Verify/Catalog.lean` with the deferred **`eventually% Goal`** liveness
   shape (the `Catalog.lean:27` H5 residue), now that `◇`/`EF` has a fixpoint home.

---

## TRACK 3 — EFFECTS / CAVEATS / PREDICATES COMPLETENESS

### The `FullActionA` inductive (`metatheory/Dregg2/Exec/TurnExecutorFull.lean:1928`) — 51 constructors

Grouped exactly as in source. **All 51 have real `execFullA` semantics** (the dispatch is
`execFullA:2236`–`2303`); there are NO `sorry`/no-op stubs in the dispatch. Crypto is portaled at the
*theorem* layer (`fullActionInvA` / §8 carriers), not faked in the executor. The per-effect kernel op:

| group | constructor (`:line`) | `execFullA` kernel op (`:2236+`) |
|---|---|---|
| core | `balanceA:1930` | `recCexecAsset` |
| | `delegate:1932` | `recCDelegate` |
| | `revoke:1934` | `some (recCRevoke …)` |
| | `mintA:1936` | `recCMintAsset` |
| | `burnA:1938` | `recCBurnAsset` |
| §MA-state (5, bal-neutral) | `setFieldA:1943` | `stateStep … f` |
| | `emitEventA:1946` | `some (emitStep …)` (NO auth gate — dregg1 emit) |
| | `incrementNonceA:1949` | `stateStep … nonceField` |
| | `setPermissionsA:1953` | `stateStep … permsField` |
| | `setVKA:1957` | `stateStep … vkField` |
| §MA-auth (7) | `introduceA:1964` | `recCDelegate` |
| | `delegateAttenA:1970` | `recCDelegateAtten` (rights-carrying, `granted ≤ held`) |
| | `attenuateA:1974` | `some (attenuateStepA …)` |
| | `dropRefA:1977` | `some (recCRevoke …)` |
| | `revokeDelegationA:1982` | `some (recCRevoke …)` |
| | `validateHandoffA:1987` | `recCDelegate` |
| | `exerciseA:1991` | `exerciseStepA` |
| §MA-supply (3) | `createCellA:1999` | `createCellChainA` |
| | `spawnA:2003` | `spawnChainA` |
| | `bridgeMintA:2009` | `recCMintAsset` (§8 foreign-finality portal carried) |
| §MA-escrow (9) | `createEscrowA:2018` | `createEscrowChainA` |
| | `releaseEscrowA:2021` | `releaseEscrowChainA` |
| | `refundEscrowA:2024` | `refundEscrowChainA` |
| | `createObligationA:2028` | `createEscrowChainA` (dispatch-ALIASED) |
| | `noteSpendA:2032` | `noteSpendChainA` |
| | `noteCreateA:2035` | `some (noteCreateChainA …)` |
| | `createCommittedEscrowA:2040` | `createEscrowChainA` (ALIASED; §8 opening portal) |
| | `releaseCommittedEscrowA:2042` | `releaseEscrowChainA` (ALIASED) |
| | `refundCommittedEscrowA:2044` | `refundEscrowChainA` (ALIASED) |
| §MA-bridge (3) | `bridgeLockA:2054` | `bridgeLockChainA` |
| | `bridgeFinalizeA:2064` | `bridgeFinalizeChainA` (the ONE disclosed non-conserving leg) |
| | `bridgeCancelA:2069` | `bridgeCancelChainA` |
| §MA-seal (6) | `sealA:2076` | `stateStep … sealField` (AEAD = §8 portal) |
| | `unsealA:2080` | `stateStep … unsealField` (AEAD = §8 portal) |
| | `createSealPairA:2084` | `stateStep … sealPairField` |
| | `makeSovereignA:2090` | `makeSovereignStep` (FILL #133 value-rebind, not a flag) |
| | `refusalA:2094` | `stateStep … refusalField` |
| | `receiptArchiveA:2098` | `stateStep … lifecycleField` |
| §MA-queue (4) | `queueAllocateA` | `queueAllocateChainA` |
| | `queueEnqueueA` | `queueEnqueueChainA` |
| | `queueDequeueA` | `queueDequeueChainA` |
| | `queueResizeA` | `queueResizeChainA` |
| §MA-swiss (4) | `exportSturdyRefA` | `swissExportChainA` |
| | `enlivenRefA` | `swissEnlivenChainA` |
| | `swissHandoffA` | `swissHandoffChainA` |
| | `swissDropA` | `swissDropChainA` |

Key proved law over the whole set: `execFullA_ledger_per_asset:2314` (combined per-asset conservation
VECTOR). The forest join + auth gate: `metatheory/Dregg2/Exec/FullForest.lean` (`execFullForestA:205`,
`execFullForestA_eq_execFullTurnA:286`, `_conserves_per_asset:371`, `_no_amplify:398`,
`_each_attests:504`) and `metatheory/Dregg2/Exec/FullForestAuth.lean` (the 3-part gate
`gateOK = credentialValid && capAuthorityG && caveatsDischarged`, `execFullAGated`, `eraseG`, the
10-variant `Authorization` sum `:103`, `AuthPortal` class `:86`).

**Honest gaps in the effect layer** (not stubs, but documented scope-outs, from the source comments):
- `bridgeMintA` foreign-chain finality, committed-escrow opening, note range/spending proofs, seal AEAD —
  all are §8 *theorem-layer* portals (carried Props), correct by design.
- `FullForest.lean:531`+ — **cross-target (cross-cell) subtrees** are routed to `Exec/CrossCellForest.lean`,
  not baked into `execFullForestA`; **Bearer-bypass (`DelegationMode::Bearer`) is scoped OUT for v1**.
- `FullForestAuth.lean:32` — **`.coordinated` (cross-cell) caveats fail-close intra-cell**, routed to
  `Exec/CrossCaveat.lean`.

### Caveat / predicate kinds modeled vs the Rust set still missing

- `metatheory/Dregg2/Authority/Caveat.lean:38` `Caveat` = `| local (Ctx → Bool) | thirdParty (gateway)`;
  `:53` `TokenKind`; `:65` `Token`; `attenuate_narrows` (append = narrow, the Heyting residual).
- `metatheory/Dregg2/Authority/CaveatChain.lean:84` `Link`, `:96` `Chain` — the **real macaroon HMAC
  running-tag chain** (`seedTag`/`Chain.append`/`Chain.replayTag`/`Chain.verify`), `MacUnforgeable`
  §8 portal; `verifiedChainGate` yields a `Ctx → Bool`.
- `metatheory/Dregg2/Authority/ThirdPartyDischarge.lean:124` `ThirdPartyCaveat`, `:136` `DCaveat`,
  `:150` `DischargeMacaroon`, `:226` `accepts` — the 3-conjunct gate (FRESH ∧ CHAIN ∧ BOUND), the
  ticket/VID two-key split, replay+cross-bind teeth.
- `metatheory/Dregg2/Authority/Predicate.lean:35` `WitnessedKind` =
  `| dfa | temporal | merkleMembership | nonMembership | pedersen | blindedSet | bridge | custom (vk)`
  — faithful to dregg1 `WitnessedPredicateKind`; each kind dispatched to a `Verify` plugin / `CryptoKernel.verify`.
- `metatheory/Dregg2/Authority/SelectiveDisclosure.lean:48` `Predicate` = `Gte/Lte/Gt/Lt/InRange/Eq`
  (the `bridge::present::Predicate` set), `:87` `Credential`, `:106` `ProvenPredicate`, `:130`
  `Presentation`; laws `presentation_hides_undisclosed`, `proven_predicate_holds`, `multishow_unlinkable`.
- `metatheory/Dregg2/Authority/DesignatedVerifier.lean:117` `TransferDial`, `DischargedFor`,
  the public↔designated-verifier transferability axis (`DVKernel` §8 portal).

**Still missing vs the Rust** (the sequential widening targets): the cross-cell `.coordinated` caveat
*discharge* (only fail-closed today, routed to `CrossCaveat`); the biscuit *delegation-graph*
verification (the macaroon HMAC chain is modeled; the biscuit public-key block graph is named in
`Caveat.lean` but not executed against `gateOK`); tiered caveat *meet* semantics wired into
`execFullForestA` for the non-`.local` arms.

**Recommended new modules for Track 3:**
1. `metatheory/Dregg2/Authority/CoordinatedCaveat.lean` — promote `CrossCaveat`'s fail-closed
   `.coordinated` arm to a real cross-cell discharge, then unblock its arm inside `FullForestAuth.gateOK`.
2. `metatheory/Dregg2/Authority/BiscuitGraph.lean` — the biscuit public-key delegation-block graph
   verifier (the off-island dual of `CaveatChain`'s intra-vat HMAC).
3. (carry-forest) a `FullForestAuth`-level theorem that each widened caveat kind is discharged on the
   committed node (the `gatedActionInvG` AND-conjunct extended), reusing `exec_frame`/`CellContract`
   from Track 1 for the "caveat-discharged-forever" carries.

---

## TRACK 4 — CONFIDENTIALITY / NONINTERFERENCE / LIVENESS

### Noninterference / information-flow — NONE EXISTS (greenfield)

A repo-wide search found **no** Volpano-Smith/seL4-style noninterference, low-equivalence, or
information-flow module. The "indistinguishable"/"low" textual hits (`Privacy.lean`, `Crypto/BlindedSet.lean`,
`Authority/SelectiveDisclosure.lean`, `Authority/DesignatedVerifier.lean`) are *crypto observer-view
equality* (an `addrView a = addrView a'` collapse), not a state-noninterference theorem over the executor.
This matches `EXTERNAL-LEAN-REFERENCES.md §2a`: "no ready Lean 4 library exists — BUILD-OURSELVES on
mathlib lattices; the seL4/l4v Isabelle proof is the blueprint; ~6 core lemmas."

### Liveness / fairness scaffolding that DOES exist

- `metatheory/Dregg2/Liveness.lean` — **GC-as-cell-liveness** (the operational dual of `Boundary`):
  `LivenessGraph:76`, `reachable:99`, `Dead:194`, `dead_undecidable:244` (halting reduction!),
  `Lease`/`leaseExpired:276`/`Live:285`, `gc_safety_local:330`, `revocation_needs_consensus:367`,
  `crossvat_cycle_leaks:411`, `leak_bounded_by_lease:439`. This is *reachability* liveness, not BFT
  liveness.
- `metatheory/Dregg2/Proof/BFTLiveness.lean` — the **O2 pacemaker**: `Pacemaker` bundles
  `honestLeader`/`synchronizes`/`honest_quorum`/`honest_le_delivered` (DLS88 GST round + ELRS
  synchronization + HotStuff Δ-delivery, all as *fields*, never axioms); `gstRound_obtains` *derives*
  the quorum.
- `metatheory/Dregg2/Proof/Synchronizer.lean` — the **randomized leader-rotation** + expected-O(1)-views
  bound: `LeaderRotation:159`, `expected_views_eq:105` (= `1/h`), `expected_views_O1:114`,
  `honest_hit_as:126` (geometric law sums to 1), `synchronizer_round_obtains:213`. Real mathlib
  probability (`tsum_coe_mul_geometric_of_norm_lt_one`).
- `metatheory/Dregg2/Proof/Temporal.lean` already gives `◇` (`Eventually`) but only the trivial
  `◇`-theorems (`P now → ◇P`, `□P → ◇P`); a *real* `◇`(progress) needs a fairness hypothesis on `SchedA`
  (noted at `Temporal.lean:42`). `Execution.Progresses:81` is the stated unproved target.

### Cleanest shape to add (a) noninterference and (b) stronger liveness

**(a) Noninterference** — the seL4/Volpano-Smith shape over the REAL executor:
- Carrier: a `SecurityLattice` (`Mathlib.Order.Lattice`/`CompleteLattice`), a labeling
  `level : FieldName/AssetId/CellId → Label`, and **low-equivalence on `RecChainedState`**:
  `lowEq ℓ s s' := ∀ field, level field ≤ ℓ → readField s field = readField s' field` (project the
  schema-public/`≤ℓ` slice). This reuses `Privacy.lean:91` `project` + `field_projection_hides_private`
  as the *field-tier* warmup, lifted to the kernel state.
- The theorem (an **effect-slice preserving low-equivalence**): for an effect `fa : FullActionA` whose
  observable footprint is `≤ ℓ`, `lowEq ℓ s s' → execFullA s fa ≈ execFullA s' fa` modulo `lowEq ℓ` on
  the outputs — i.e. `cellNextA` is a noninterference step. Then lift to the trajectory via
  `livingCellA_carries` (Track 1's `carry_forever`): "low-equivalence is preserved forever" becomes a
  `CellContract` with `Inv := lowEq ℓ s0`.
- Discipline: the §8 crypto-hiding (Pedersen/Poseidon) stays a portal; the Lean law is the
  *information-theoretic* state-projection noninterference, exactly as `SelectiveDisclosure.lean` keeps
  the computational property as a portal.

**(b) Stronger liveness** — fairness quantifiers + GST as first-class:
- Add a `Fair : SchedA → Prop` predicate (`□◇`-enabled-implies-taken over `ConservingForest` choices),
  then `eventually_under_fairness : Fair sched → (variant decreases) → Eventually Committed s sched`.
  This is the `Temporal.lean:42` residue and discharges `Execution.Progresses`.
- A standalone `GST`/partial-synchrony model (the `EXTERNAL-LEAN-REFERENCES.md §5c/§5f` "BUILD-OURSELVES"
  target) parameterizing delivery by a global-stabilization-time index, feeding `BFTLiveness.Pacemaker`'s
  delivery fields from a delay-bound rather than carrying them as bare hypotheses.

**Recommended new modules for Track 4:**
1. `metatheory/Dregg2/Proof/Noninterference.lean` — `SecurityLattice`, `lowEq` on `RecChainedState`,
   the per-effect noninterference slice over `execFullA`, and the `livingCellA_carries`-lifted
   "low-equivalence forever" `CellContract`. (Blueprint: `EXTERNAL-LEAN-REFERENCES.md §2a`, seL4 l4v
   `proof/infoflow`.)
2. `metatheory/Dregg2/Proof/Fairness.lean` — `Fair : SchedA → Prop` (weak/strong fairness as `□◇`),
   `eventually_under_fairness`, and the discharge of `Execution.Progresses` for `livingSystem`.
3. `metatheory/Dregg2/Proof/GST.lean` — the partial-synchrony delay-bound model feeding
   `BFTLiveness.Pacemaker.honest_le_delivered`.

---

## TRACK 5 — PRIVACY-CRYPTO STACK (model dregg1 Rust primitives in Lean)

### Already in Lean (do NOT duplicate)

- `metatheory/Dregg2/Privacy.lean` — three privacy tiers: field (`project:91`,
  `field_projection_hides_private:101`), value (`Commitment:124`, `committed_conservation:160`,
  Pedersen homomorphism), graph (`StealthAddr:265`, `ZkAuthChain:289`, `SetCommitment`/`MemProof`,
  `Note`/`Nullifier`, `GraphPrivacyKernel:349` + `BlindedMembershipKernel:396` classes;
  `unlinkable:431`, `nullifier_prevents_double_spend:494`, `nullifier_hides_identity:512`,
  `anonymity_nullifier_reconciliation:523`).
- `metatheory/Dregg2/CryptoKernel.lean` — the §8 Lean↔Rust portal boundary.
- `metatheory/Dregg2/PrivacyKernel.lean` — value + nullifier tiers over `CryptoKernel`.
- `metatheory/Dregg2/Crypto/PortalFloor.lean` — **8 `@[extern]` §8 portals**: `ed25519VerifyExtern:33`,
  `starkVerifyExtern:63`, `pedersenCommitExtern:93`, `poseidon2HashExtern:137`, `blake3HashExtern:170`,
  `nullifierDeriveExtern:197`, **`aeadOpenExtern:222`** (the AEAD decrypt-and-authenticate — sealed
  boxes + encrypted turns hang off this), `hmacSha256Extern:253`.
- `metatheory/Dregg2/Crypto/Primitives.lean` (Layer A: `CryptoPrimitives` class, `commit_hom` proved,
  `collisionHard`/`binding`/`unlinkable` Prop carriers), `Crypto/VerifierKernel.lean` (Layer B:
  `verify` as a contract), `Crypto/PredicateKernel.lean` (Layer C: per-kind circuit obligations).
  Plus per-kind §8 discharges: `Crypto/Merkle.lean`, `Crypto/Pedersen.lean`, `Crypto/BlindedSet.lean`,
  `Crypto/NonMembership.lean`, `Crypto/Bridge.lean`, `Crypto/Dfa.lean`, `Crypto/Temporal.lean`,
  `Crypto/Custom.lean`, `Crypto/UCBridge.lean`.
- `metatheory/Dregg2/Authority/SelectiveDisclosure.lean` — selective disclosure + predicate proofs +
  `multishow_unlinkable` (the presentation path; see Track 3).

**Gap:** the PortalFloor has NO garbled-circuit, stealth-address-derivation, or SSE-search-token
portal yet. Those are the new §8 portals Track 5 adds.

### Rust source → minimal Lean modeling target (each: structure + ONE security property + §8 portal)

All Rust files confirmed present:

1. **Stealth addresses** — `wasm/src/privacy.rs` (1888 lines): `derive_stealth_keys:26`,
   `create_stealth_address:97`, `derive_stealth_one_time_address:142`, `check_stealth_ownership:156`,
   `scan_stealth_announcements:209` (EIP-5564/Monero one-time keys).
   Lean target: a `StealthScheme` structure (`scanKey`/`spendKey`/`oneTimeAddr (r, P) = derive …`); the
   security property is **unlinkability**: `addrView (derive r₁ P) = addrView (derive r₂ P)` (two
   one-time addrs to the same recipient are observer-indistinguishable). `Privacy.lean:265` `StealthAddr`
   + `GraphPrivacyKernel.unlinkable` is the existing carrier — *extend*, don't duplicate; the §8 portal
   is the DDH/key-derivation hardness (new `stealthDeriveExtern`).
2. **Encrypted turns** — `turn/src/encrypted.rs` (504 lines): `EncryptedTurn:53`,
   `TurnValidityProof:96`, `compute_agent_commitment:138`, `encrypt_for_executor:188`,
   `decrypt_for_executor:248`, `may_conflict_with:317`, `order_encrypted_turns:370`.
   Lean target: an `EncryptedTurn` structure (ciphertext + `TurnValidityPublicInputs`); the property is
   **correctness-under-decryption + conflict-set soundness** (`decrypt (encrypt t) = t` modulo the AEAD
   portal, and `may_conflict_with` is sound w.r.t. the plaintext conflict relation). §8 portal:
   `aeadOpenExtern` (already in PortalFloor) + the STARK validity proof.
3. **Sealed boxes** — `tokenizer/src/encrypt.rs` (310 lines): `TokenizerKeypair:25`, `SealedSecret:72`,
   `SealedSecret::seal:83`, `open:114` (X25519 ECDH + AEAD; also `intent/src/sse.rs:258 seal_encrypt`).
   Lean target: a `SealedBox` structure (`seal pk pt` / `open sk box`); the property is
   **open∘seal round-trip + confidentiality** (`open sk (seal pk pt) = some pt` for the matching key,
   `none` otherwise). §8 portal: `aeadOpenExtern` + an X25519 ECDH portal (new).
4. **Searchable symmetric encryption** — `intent/src/sse.rs` (1055 lines): `generate_search_token:65`,
   `tokens_for_matchspec:79`, `extract_sse_keywords:92`, `capability_matches_tokens:127`,
   `EncryptedIntent:368`.
   Lean target: an `SSEScheme` structure (`searchToken (kw, epoch)` / `matches (token, encryptedDoc)`);
   the property is **search-token soundness + keyword privacy** (`matches (searchToken kw) doc ↔
   kw ∈ keywords doc`, and the token reveals nothing about non-queried keywords — observer-view collapse
   over non-matching docs). §8 portal: the PRF/keyed-hash for `generate_search_token` (a new
   `sseTokenExtern`, BLAKE3-keyed).
5. **Garbled circuits** — `circuit/src/garbled.rs` (904 lines): `GarbledGate:42`, `GarbledCircuit:50`,
   `EvalResult:85`, `GarbledEvaluationProof:109`, `garbling_hash:128`, `color_bit:173`, `hash_label:220`,
   `garble_comparison_circuit:260`, `evaluate_garbled_circuit:386`, `prepare_private_threshold_check:465`.
   Lean target: a `GarbledCircuit` structure (`gates`, wire labels) + `eval`; the property is
   **garbled-circuit privacy / authenticity** (the evaluator learns only the output label, not the
   inputs — `evalView` depends only on the revealed output, modeled as observer-view equality across
   input pairs that agree on the output). §8 portal: the garbling-hash (Free-XOR/half-gates) hardness —
   a NEW portal (no garbled portal exists in PortalFloor). Blueprint:
   `EXTERNAL-LEAN-REFERENCES.md §4c` (SymbolicCryptographyLean has *verified symbolic security of
   garbled circuits* — the closest external reference).
6. **Blinded-leaf multi-show unlinkability + presentation randomness** — `bridge/src/present.rs`
   (3821 lines): `BridgePresentationBuilder:103`, `BridgePresentationProof:150`, `prove:669`,
   `verify_presentation_full:1993`, `verify_presentation_nonce:2136`, `verify_presentation:2488`,
   `verify_fold_chain:2599`.
   Lean target: a `BlindedPresentation` structure (a blinded credential leaf + a fresh per-show nonce);
   the property is **multi-show unlinkability** (two presentations of the same leaf with distinct fresh
   blindings have equal observer-views — the `verify_presentation_nonce` randomness is what breaks
   linkability). This is the natural extension of the existing
   `SelectiveDisclosure.multishow_unlinkable` to the *blinded-leaf* (Merkle-leaf) layer. §8 portal: the
   STARK fold-chain verification (`starkVerifyExtern`, already present) + the per-show ring/blinding
   hiding.

The **VCVio game-logic blueprint** (`EXTERNAL-LEAN-REFERENCES.md §4a`, IACR 2026/899) is the recommended
substrate if any of these need a *computational* (game-based, `OracleComp`) statement rather than the
information-theoretic observer-view-collapse the existing `Privacy.lean`/`SelectiveDisclosure.lean` use.
For the first cut, follow the house style: prove the information-theoretic core, carry the computational
hardness as a `Prop` field of a kernel class (the `CryptoKernel`/`GraphPrivacyKernel` idiom).

**Recommended new modules for Track 5:**
1. `metatheory/Dregg2/Crypto/Stealth.lean` — `StealthScheme` + unlinkability, extending
   `Privacy.StealthAddr`/`GraphPrivacyKernel`.
2. `metatheory/Dregg2/Crypto/SealedBox.lean` — `SealedBox` (X25519+AEAD) + open∘seal round-trip
   (covers both `tokenizer/encrypt.rs` and `turn/encrypted.rs`'s AEAD core).
3. `metatheory/Dregg2/Crypto/EncryptedTurn.lean` — `EncryptedTurn` + decrypt-correctness +
   conflict-set soundness (builds on `SealedBox`).
4. `metatheory/Dregg2/Crypto/SSE.lean` — `SSEScheme` + search-token soundness + keyword privacy.
5. `metatheory/Dregg2/Crypto/Garbled.lean` — `GarbledCircuit` + garbled-circuit privacy (NEW §8 portal).
6. `metatheory/Dregg2/Crypto/BlindedPresentation.lean` — blinded-leaf multi-show unlinkability
   (extends `SelectiveDisclosure.multishow_unlinkable`).
7. Add the missing §8 portals to `metatheory/Dregg2/Crypto/PortalFloor.lean`:
   `stealthDeriveExtern`, X25519-ECDH, `sseTokenExtern`, the garbling-hash portal.

---

## Cross-track summary of recommended new modules

| Track | New modules |
|---|---|
| 1 (Hatchery) | none — reuse `Verify.{Tactics,Frames,Contract,Catalog}`; only the deferred `eventually%` shape (lands with Track 2) |
| 2 (CTL/μ) | `Proof/CTL.lean`, `Proof/MuCalculus.lean`, + `eventually%` into `Verify/Catalog.lean` |
| 3 (effects/caveats) | `Authority/CoordinatedCaveat.lean`, `Authority/BiscuitGraph.lean`, + a carried caveat-discharge forest theorem |
| 4 (NI/liveness) | `Proof/Noninterference.lean`, `Proof/Fairness.lean`, `Proof/GST.lean` |
| 5 (privacy-crypto) | `Crypto/{Stealth,SealedBox,EncryptedTurn,SSE,Garbled,BlindedPresentation}.lean` + 4 new `PortalFloor` externs |

**Shared dependency facts (verified):** `Mathlib.Order.FixedPoints` is already pulled (via
`Paco/Basic.lean`); `OrderHom.lfp/gfp` are in active use — Track 2 needs no new dep. Lean 4.30 native
`coinductive` is exercised at `Proof/CoinductiveAdversary.lean:85`. Every shipped Verify/Proof keystone is
`#assert_axioms`-pinned to `{propext, Classical.choice, Quot.sound}` — new modules should keep that bar.
