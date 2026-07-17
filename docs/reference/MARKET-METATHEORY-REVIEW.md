# Market Metatheory — Merciless Assurance Review (2026-07-17)

Read-only sufficient-test audit of every `metatheory/Market/*.lean` (37 files), the verified
core the confidential-clearing product rests on. The discipline is the one that found vacuity in
ArkLib's `KZG.binding`, in our own FRI "57 calculator bits", and in our `*HardQuant` costumes,
turned inward on our own assurance core. A found vacuity / mirror / laundering is a WIN.

Verdict vocabulary: **PROVEN** · **HONEST-CARRIER** (assumed but honestly named + graded) ·
**VACUOUS** · **MIRROR** · **LAUNDERED** · **OVER-NAMED** (statement true but the doc/name claims
strictly more than it proves).

Build state: the confidential-clearing core (the FhEgg trio, Mpc, RevealNothing) has no current
oleans and depends on `FhEggClearing.lean`, which a sibling lane is actively editing — it was NOT
built (clobber/race hazard, correctly avoided). The foundation files DO build: `lake env lean
Market/Optimality.lean` exits 0 and prints `#assert_all_clean: 10 keystones pinned kernel-clean`,
compiling Priced + Ring on the fly. So the `#assert_axioms` / `#assert_all_clean` pin mechanism is
REAL and enforced at build time (not decorative); the foundation pins are green. The FhEgg-core pins
are structurally correct (name the right theorems) but their current greenness is unverified this
session.

---

## HEADLINE FINDINGS (ranked by value)

### 1. ⚑⚑⚑ The MPC "joined theorem" reveals the SUBOPTIMAL balance-threshold clearing, and its "optimal" is the WEAK uniform-price optimality — NOT volume-maximization. (OVER-NAMED)

`MpcClearingSecurity.MpcClearing` defines its revealed clearing price/volume as
- `pStar := balanceCrossing mc.bk mc.hcross` (`MpcClearingSecurity.lean:314`)
- `vStar := balanceVolume mc.bk mc.hcross` (`:317`)

But `FhEggClearing.lean` is emphatic (§3, `:193-273`) that `balanceCrossing` — the LEAST balanced
bucket, `Nat.find` on `Clears` — is **NOT the clearing price**; it is exactly "the object the OLD
least-`{demand ≤ supply}` heuristic mistook for the clearing price" (`:199-200`), and
`workBook_old_crossing_suboptimal` (`:487-488`) PROVES that bucket clears only `6 < 8`. The correct
uniform-price rule is the volume-argmax `crossing`/`clearedVolume` (§4).

The joined theorem `cleared_conserving_optimal_and_reveal_only` (`MpcClearingSecurity.lean:429-443`)
proves part (a) by `clearedBatch_optimal (mc.vStar) mc.ρ`. But `clearedBatch_optimal`
(`FhEggClearing.lean:436-443`) holds for **ANY** `V ≥ 0`, `ρ > 0` — it is `uniform_price_optimal`
(`Optimality.lean:174-184`) = conservation + individual-rationality + value-neutrality/no-arbitrage.
It does NOT reference `clearedVolume_optimal` (the volume-maximization). So the "optimal" in the
joined theorem is the WEAK uniform-price optimality that holds at any volume — the volume-maximizing
optimality FhEggClearing crowns as the correct rule is **not in the join**.

Made concrete: the witnessed `mcA` uses `bookA = workBook`, and `mcA_leakage` proves its revealed
`(p*, V*) = (2, 6)` (`MpcClearingSecurity.lean:468-471`) — the SUBOPTIMAL balance threshold FhEgg's
own tooth marks as leaving 2 units of matchable volume on the table. The doc-comment nonetheless
frames this as "verified optimality joined to verified privacy… no prior work holds both" and "the
SAME `(p*, V*)` in both halves" (`:406-428`). True that both halves reference `mc.vStar`; misleading
that "optimality" means the volume-maximization and that `(p*,V*)` is the argmax clearing price.
**Verdict: OVER-NAMED.** The statement is true (a batch at `balanceVolume` conserves and is
value-neutral, and the balance sign vector is `p*`-determined); the framing conflates weak
uniform-price optimality with volume-maximization and presents the suboptimal balance clearing as
the optimal one.

### 2. ⚑⚑ Internal model discrepancy: two different "what mpc_crossing reveals". (needs reconciliation)

- `FhEggRustDenotation.mpcOutput` uses `mpcArgmaxUpto` (the ARGMAX) and proves
  `mpcOutput = leanClearingOutput` = `(crossing, clearedVolume)` (`FhEggRustDenotation.lean:570-613`).
  Here the MPC reveals the **argmax** clearing.
- `MpcClearingSecurity` models the MPC as opening the monotone sign vector `[Clears bk j]`
  (`clearsVec`, `:236`), whose threshold is `balanceCrossing`, and its clean simulability argument
  `clearsVec_eq_step` (`:247-253`) works **only** because that vector is a monotone threshold step
  (proven from `imbalance_antitone`). The argmax's transcript is NOT a monotone step vector, so the
  §2 `p*`-determinacy argument does **not** cover the object the denotation file models.

Whichever transcript the deployed `mpc.rs` actually opens, only one of {the correctness/denotation
result, the clean reveal-only argument} applies to it as proven. This seam — is deployed
`mpc_crossing` the balance-threshold opener (secure per §2, but suboptimal per FhEgg) or the argmax
opener (correct, but its transcript's simulability is unproven here)? — is not named in either file.

### 3. ⚑⚑ The Rust↔Lean denotation binding is an HONESTLY-NAMED re-authored model — NOT byte-identity, NOT a mechanized faithful denotation. (HONEST-CARRIER, seam un-closed)

This is the seam most at risk of byte-identity laundering; it is not laundered, but it is also not
closed. Every Rust-facing file re-authors the Rust algorithm as a Lean function, proves properties
of the Lean function, and NAMES the source-correspondence + numeric-refinement as an explicit,
un-discharged residual:

- `FhEggRustDenotation`: `rustArgmaxUpto`/`rustReferenceOutput` are Lean re-authorings; the
  doc-comment even calls `rustArgmaxUpto` "the independently written Rust loop" while it is a Lean
  `def` (`:74-80, :112-114`). The whole TFHE ciphertext program is reduced honestly to
  `TfheU32PrimitiveLaws` + `FhEggTfheSourceRefinementResidual` (`:508-520`) — both explicitly named,
  with a transparent-ops non-vacuity pole clearly labelled "only a non-vacuity pole" (`:532-535`).
- `CertQpRustDenotation`: the file states plainly "This file mirrors those source expressions over
  exact rationals" (`:16`); the f64/IEEE gap is the named `CertQpRustF64RefinementResidual`
  (`:330-337`).
- `FhEggLedgerBinding`: the deployed-output→ledger tie is the named `FhEggLedgerSourceBinding`
  (`:197-206`), explicitly "not silently assumed" (`:18-20`).

The binding to the ACTUAL deployed Rust is therefore trust-by-human-reading ("mirrors those source
expressions"), discharged only up to a NAMED source-refinement residual that is never proven. This
is honest (genuine semantic content + teeth, not byte-identity) but the faithful denotation of
deployed Rust is **un-mechanized**: no extraction, no differential-testing pin lives in Lean. The
strongest de-laundering move available — pinning the Lean model against extracted/tested Rust — is
the open work.

### 4. RevealNothing confidentiality is CONDITIONAL on the named `HidingFriPcs` floor, exemplarily honest. (HONEST-CARRIER — the gold standard)

`RevealBundle.reveal_law` (`RevealNothing.lean:197-198`) is the reveal-nothing law as a bundle
FIELD. Every reveal-nothing consequence (`reveal_nothing`, `same_leakage_indistinguishable`,
`view_factors_through_leakage`) is a theorem ABOUT a bundle satisfying that field. For the DEPLOYED
bundle the field is the un-discharged `HidingFriPcs` statistical-ZK + hash-hiding +
nullifier-unlinkability floor; the `shellBundle` (`:257-260`) satisfies it by `rfl` but its
`view := canonicalSim ∘ Q` is the IDEAL world, not the deployed transcript. The HONEST GRADE section
says outright: "Do NOT read this as 'reveal-nothing is proved' — it is proved *conditional on the
PCS-ZK floor*" (`:76`). Genuine teeth (`leaky_no_simulator` `:325`, `leakyVB_not_hiding` `:376`)
show the law is falsifiable, not vacuous `True`. This is the model of how to name a floor.

### 5. The perfect-hiding lemma (Mpc §1) is genuinely PROVEN and non-vacuous — but is a fact about the primitive, weakly bound to the deployed view.

`perfect_hiding` (`MpcClearingSecurity.lean:149-151`) constructs an EXPLICIT view-preserving
bijection `rebalanceEquiv` (`:127-141`) for every finite abelian group and every below-full
coalition; the below-full hypothesis is load-bearing (`full_collusion_breaks_hiding` `:164-172`);
`otpMasks` (`:178-181`) is the `n=2, ZMod 2` instance. All PROVEN, kernel-clean, non-vacuous. Caveat
(sufficient test): this is a fact about the additive-sharing PRIMITIVE. In `reveal_only` the
`MpcView` records only `maskedLen : ℕ` (`:268`), not the masked values — the values' hiding is
argued by §1 but the view simply EXCLUDES them by modeling choice; the connection to the deployed
`mpc.rs` transcript is an (honestly-stated) modeling assumption, not a mechanized binding.

---

## PER-FILE VERDICTS

### Confidential-clearing core (read in full by the reviewer)

**FhEggClearing.lean** — the uniform-price aggregation core. PROVEN and strong.
- `clearedVolume_optimal` (`:360-363`): the argmax MAXIMIZES executed volume, `∀ q < K`. Genuine,
  non-vacuous volume-maximization (not the weak uniform-price sense), with the worked-book
  suboptimality tooth `workBook_old_crossing_suboptimal` (`:487`). **PROVEN.**
- `clearedBatch_conserves` (`:386`), `clearedBatch_optimal` (`:436`): conservation + weak
  uniform-price optimality of the two-leg batch, at ANY `V ≥ 0`. **PROVEN** (note the "optimal"
  scope — see Finding 1).
- Monotonicity/fold lemmas (`demand_antitone`, `imbalance_antitone`, `Fstep_monotone`): **PROVEN**,
  real content underpinning §2 of Mpc.
- §7 emit bridge (`clearingCircuit_sound` `:580`): HONESTLY scoped — encodes only the balance
  decomposition + conservation gates, NOT the argmax selection; the scope note (`:553-559`) says so
  explicitly. **PROVEN + honestly scoped.**

**FhEggRustDenotation.lean** — see Findings 2, 3. Core equalities
(`FhEggCrossingDenotation` `:124`, `fheOutput_eq_rustReferenceOutput` `:209`,
`MpcCrossingDenotation` `:607`) are **PROVEN** relations between Lean re-authorings under the honest
`AggregatesFitU32` premise (`:96-98`, satisfiable — a real range bound, not empty). The
whole-program TFHE reduction `tfheEval_decrypt_eq_fheOutput` (`:494`) is **PROVEN** and genuinely
reduces to the two named residuals — a real de-opaquing of the former "restate the final equality"
carrier. `MpcCrossingRevealOnlyDenotation` (`:646`) is `rfl` (true-by-construction of the view type)
but backed by the genuine negative tooth `mpcCurveHeightLeakage_refused` (`:668`). **HONEST-CARRIER.**

**FhEggLedgerBinding.lean** — `fhEgg_output_executes_exact_drex_clearing` (`:181-191`) is a genuine
CONTENT theorem: it constructs a `DrexClearing` whose `nodes` are literally
`fhEggMatchNodes (crossing bk K) (clearedVolume bk K)` and proves it settles through the real
`settleRing` (`:141-162`). **PROVEN** as a specification-level content theorem — honestly labelled
"This is a specification-level content theorem" (`:18`). Caveat: `fhEggSettlePre` (`:96-106`) FUNDS
the buyer/seller by construction, so "settles" is conditional on funding, not a claim the real
ledger holds the funds — honestly in scope. Deployed-output binding is the named
`FhEggLedgerSourceBinding` (Finding 3).

**MpcClearingSecurity.lean** — see Findings 1, 5. `perfect_hiding`, `clearsVec_eq_step`
(`:247`), `reveal_only` (`:334`), `same_leakage_indistinguishable` (`:342`), `compose_reveals_only`
(`:528`), the `PerfectZK` bridge (`:574-583`) — all **PROVEN**, kernel-clean, with real teeth
(`mpc_leaky_no_simulator` `:390`, on two genuinely different real books). The novel JOINED theorem is
**OVER-NAMED** (Finding 1). The confidentiality posture is semi-honest / perfect-hiding + a NAMED
frontier (malicious security, the `HidingFriPcs` floor, full UC) — the file states this frontier
explicitly (`:50-64`).

**RevealNothing.lean** — see Finding 4. **HONEST-CARRIER**, the exemplar.

### Conservation / fairness / optimality foundations (read in full, build-verified green)

**Priced.lean** — `priced_clearing_keystone` (`:240`): conservation (`netFlow = 0`, a real per-asset
cross-party Σ) + limit-respect + partial-fill consistency. **PROVEN**, two-polarity teeth
(`overfill_refused` `:435`, `badPrice_refused` `:449`, `pairLeak_refused` `:462`), multi-pair
composition real (`Conserves_append` `:158`). Non-vacuous positive witness with an actual partial
fill.

**Fairness.lean** — `clearing_respects_limits` (`:112`), `cycleValid_fulfilled_respects_limits`
(`:130`): the GIVE-side limit law bound to the REAL executor `CycleValid`/`settleRing`/`settleRing_
conserves` from `Dregg2.Intent.Ring` (not a mirror). **PROVEN**, teeth refuse over-debit /
wrong-asset at FORMATION (`overdebit_refused` `:196`, `wrongAsset_refused` `:203`).

**Optimality.lean** — `uniform_price_optimal` (`:174`): IR + no-arbitrage/value-neutrality +
envy-freeness. **PROVEN**, split-price arbitrage/envy teeth (`splitFills_admits_arbitrage` `:247`).
Minor: `no_improving_deviation` (`:144`) is the algebraic tautology `a·p·p⁻¹ − a = 0` — the "no
improving deviation" reading is slightly OVER-NAMED; the real content is `uniform_price_no_arbitrage`
(value-neutrality). Build-verified: `#assert_all_clean: 10 keystones pinned kernel-clean`, exit 0.

### Other Rust/crypto binding

**AggregateBinding.lean** — a MODEL of honest floor-naming. `collision_yields_msis_witness` (`:71`)
and `binding_break_yields_msis_solution` (`:279`) are **PROVEN** (pure algebra + reduction);
`aggregate_binding_of_MSISHard` (`:401`) is a **PROVEN** advantage reduction: quantitative Module-SIS
hardness ⇒ aggregate binding, with NO probability loss. The floor `MSISHard` (`:392`) is
`MSISHardQuantShape` over an adversary-indexed advantage with a `ResourceModel` (`:381-388`) whose
`bindingNonempty`/`msisNonempty` fields FORBID vacuity-by-empty-adversary-class, and it explicitly
avoids the false existence-refutation `Lattice.MSISHard` (`:33`, `:139-144`). Anti-scalar tooth
`scalarStyleBreak_not_short` (`:489`) real. **HONEST-CARRIER (the good kind: adversary-indexed,
non-vacuous, `prove-the-floor-false`-safe).**

### Economic cluster (careful-reading subagent, not yet independently rebuilt)

**Clearing.lean** — `clearing_conserves_per_asset` (`:248`), `clearing_fair` (`:168`),
`exact_clears_iff` (`:285`): **PROVEN**, genuinely non-vacuous — on `Discrete DemoRes`, `Converts`
forces bundle equality, so conservation is a real cross-party Σ predicate, not `True`. Teeth real
(3-party ring clears what all 1-/2-party sub-books cannot).

**Aggregation.lean** — `aggregate_sound` (`:148`): **PROVEN** (mergeSort perm + pairwise).
`faithful_preserves_count` (`:170`) proves length + nonce-sum (decidable projection of the `Perm`),
HONESTLY disclosed as such. Four teeth real.

**Liquidity.lean** — `pool_solvent_forever` (`:145`): **PROVEN** ∀-schedule fold-invariant,
non-vacuous. `pool_backing_solvent_forever` (`:162`): **HONEST-CARRIER** (reuses upstream
`stripe_reserve_solvent_forever`). `Pool` is a model, not the executor ledger — disclosed.

**GraduationPool.lean** — model refinements **PROVEN**. ⚑ FLAG (prose over-read): doc-comments
(`:13-24`, `:116-120`) assert the DEPLOYED Solidity `DreggSolventPool` / on-chain floor guard
"exactly" realizes the `PoolFillValidFloor` discipline; the Lean proves only a model statement — the
`.sol ↔ Lean` tie is unverified prose. **OVER-NAMED (prose).**

**Lending.lean** — ⚑ FLAG: the marquee `no_bad_debt` (`:163`) is DEFINITIONAL — `Liquidatable :=
(liquidate …).isSome`, `liquidate` returns `some` iff underwater, so `BadDebt` is `P ∧ ¬P` by fiat.
Genuinely disclosed (`:48-58`: "a modeling consequence… NOT an operational proof"), but the
title/register over-reads. `classify_exhaustive` (`:193`) is VACUOUS/tautological (restates a
3-constructor inductive has 3 constructors) — decorative. `lending_sound` (`:373`) conjoins two
state-disjoint models (cosmetic, honest). Operational lifecycle theorems PROVEN. **Verdict:
HONEST-CARRIER but title OVER-NAMED; one decorative-VACUOUS lemma.**

**CrossMargin.lean** — `crossMargin_position_sound` (`:252`): **PROVEN** composition of three real
upstream towers, instantiated against the REAL `posFills`/`demoPool` (not re-authored stubs). Teeth
real (budget cannot be minted by sub-delegation). Scope disclosed.

**OracleWeld.lean** — `no_bad_debt_attested` (`:145`), `lending_sound_attested` (`:166`): add zero
LOGICAL content over `Lending.no_bad_debt` (∀ am still ranges over every ℚ price), EXPLICITLY
disclosed (`:30-35`). Crucially NOT laundered: the weld GRADES the price `ATTESTED` and
`mark_leg_not_proved` (`:130`) machine-checks `attested ≠ proved` — the honesty is a theorem, not
prose. Minor: "ATTESTED by construction" slightly overstates a default field. **HONEST-CARRIER, not
laundered.**

### Cert cluster (careful-reading subagent)

No `sorry`/`admit`/`native_decide`/opaque `axiom` in any file; `by decide`/`#guard` are kernel
computation. Math cores PROVEN and non-vacuous. Two real findings (one overclaim, one mirror).

**CertF.lean** — `weak_duality` (`:113`), `certifies_epsilon_optimal` (`:133`), `gap_nonneg`
(`:146`): genuine LP weak duality quantifying over EVERY primal-feasible `f'`; `DualFeasible` demands
a real dual point and `gap ≤ ε` constrains `cᵀs`. **PROVEN**, richly inhabited (`ringCert_valid`),
teeth genuinely refuse, emit bridge an honest iff. (This is the ε-optimality Mpc §5 relies on —
verified real.)

**CertFDescriptor.lean** — ⚑ FLAG: `rangeGadget_forces_range` (`:283`) is **PROVEN** and
load-bearing. But the headline `certFDescriptor_emit_sound` (`:547`) **OVERCLAIMS**: the doc-comment
(`:547-573`) claims it forces the FULL Cert-F certificate, ALL FIVE families incl. the ε-gap
`cᵀs − wᵀf ≤ ε`. The STATEMENT delivers only conservation `≡0 mod p`, `0 ≤ f`, `0 ≤ s`, and bare
`0 ≤ u`, `0 ≤ d`, `0 ≤ g` — the nonnegativity of three SLACK columns WITHOUT the gates linking them
(`u==c−f`, `d==π_head−π_tail+s−w`, `g==ε−(cᵀs−wᵀf)`). For the GAP the linking gate is extracted
NOWHERE (`certFDescriptor_gap_sound` `:491` reaches only the range-gadget tail, never the
`g==ε−gap` head gate). So the ε-optimality clause — the whole point of a certificate — is NOT
established at the descriptor level despite the prose. Delivers ~2.5 of 5 claimed families. **Verdict:
OVER-NAMED (the ε-gap, the load-bearing clause, is not proved here).**

**CertQp.lean** — `quad_convex_ge` (`:171`), `qp_certifies_epsilon_optimal` (`:207`): **PROVEN**
convex duality; honestly discloses the deployed Rust OSQP checker is a DIFFERENT (residual)
certificate (matches `CertQpRustDenotation`'s mismatch tooth). No overclaim.

**PriceCert.lean** — no-arbitrage LP duality **PROVEN**; `snell_feasible_upper_bound` (`:314`) proves
only the upper-bound direction, multi-step + dual-exactness honestly NAMED residuals. No overclaim.

**FhIRAdmissible.lean** — ⚑⚑ FLAG: **MIRROR / definitional.** `RunnableAt T m := carrierTransports
T m ∧ verifyNotFind T m`, but `carrierTransports`/`verifyNotFind` (`:99-109`) are DEFINED as literal
manifest-flag equalities (`m.publicOps=true`, etc.) — the same booleans `passes` (`:90`) ANDs. So
`passes_runnable` (`:123`) / `compiles_admissible` (`:178`) are a tautological flag-drop, and the
"⟹ open gap" witnesses (`:302`, `:313`, proved by `⟨⟨rfl,rfl,rfl⟩,rfl⟩`) are manufactured by
defining the "semantic" predicate to ignore the one field (`approvedCone`) the syntactic one checks.
The doc's "RunnableAt is a semantic Prop… the theorem maps one to the other" is the laundering:
`RunnableAt` carries NO semantics independent of the booleans `passes` already checks. Kernel-clean
and true, but establishes no syntactic⇒semantic bridge. **Verdict: MIRROR / VACUOUS-of-content.**

**StreamingCert.lean** — `streaming_cert_telescopes` (`:72`): **PROVEN** `Finset.sum` of immutable
per-batch CertF receipts. Real.

**PrecisionEnvelope.lean** — `E_T` is an explicitly-CARRIED, admittedly-underived parameter;
`tolerance_split_soundness_untouched` (`:99`) binds `_E_T` unused (soundness independent of envelope,
honestly made). No laundering.

**MintSafeQuantization.lean** — strong file. `mint_safe_quantization` (`:78`),
`field_gate_refines_nat_eq` (`:128`, no-wrap), `mint_safe_floor_ceil` (`:323`),
`sufficient_surplus_passes_gate` (`:348`): all **PROVEN**, load-bearing teeth
(`field_gate_without_range_mints`, `genuine_mint_fails_gate`).

**QuantizedConservation.lean** / **ExactGapNoWrap.lean** — **PROVEN** no-wrap conservation at deployed
params (VALUE_BITS 26, BabyBear), load-bearing teeth mint the full modulus `p` when range dropped.
`perVertexConservation_noWrap` relies on the imported `Dregg2.Bignum.legs_noWrap_conservation`.

**WideCommitBoundary.lean** — `receiptRoot_binds`/`turnDigest_binds`/`stateDecode8_*_faithful`:
binding/injectivity conditional on `Poseidon2SpongeCR`/`Poseidon2WideCR` CR HYPOTHESES, honestly
carried as explicit arguments. **HONEST-CARRIER.** Eight-lane payload `S.commit :: replicate 177 0`
headroom disclosed.

**CertFGolden.lean** — 22 lines, a single generated golden byte-literal (`emitVmJson2` pin target).
Nothing to verify semantically.

### Ledger / ZK / settlement cluster (careful-reading subagent)

No `sorry`/`admit`/opaque `axiom`; every headline pinned. Valuable failures flagged first.

**InterchainCustody.lean** — ⚑⚑ TWO failures.
- `custody_cross_boundary_conserves` (`:341`): **LAUNDERED conjunction.** The "end-to-end
  cross-boundary conservation keystone" conjoins two INDEPENDENT facts sharing no variable — the
  `DrexClearing c`/`mirrorAsset` are unconstrained relative to the lock/release lifecycle
  (`a,a',m0,m1,m2`); nothing forces `c` to trade the mirror asset. The conservation clause is just
  `settleRing_conserves … c.settled` (holds for ANY clearing); the `systemValue` clause (`:346`) is
  trivial (the same `m1.gap` added to both sides of an already-proven equation). "The mirror trades
  through the clearing" is narrative, not statement.
- `lock_refund_restores` (`:445`): **VACUOUS.** `refund m0 _stuck := m0` (`:440`, a constant
  function), so the theorem is `rfl` by construction — models no refund mechanism.
- `gatedRingRelease` gating (`:388`): the "gated on the SAME clearing proof" is an uninterpreted
  `cleared : Bool`; no binding to any `DrexClearing`/proof object. The atomicity story rests on a flag.

**CrossChainSettlement.lean** — the whole cross-chain layer is a **crypto-free abstract accept-path
model** (highest mirror-risk item). `settleDrex` (`:152`) does ZERO cryptography — a continuity
`if rootOf c.pre = S.provenRoot`; `rootOf`/`Root` are abstract parameters, the demo root
(`:303`) a toy 2-integer projection, the Groth16 pairing the NAMED residual (`:60-76`). The
`ProvenState` register + `demoProven` anchor are authored in-file (a self-anchored re-authored peer).
Header is candid (accept-path model, "dev ceremony toxic-waste-known"), teeth genuine
(`settleDrex_continuity_broken`, `minting_post_unsettleable`). **HONEST-CARRIER, but the "a fair DrEX
fill IS settle-able cross-chain" framing outruns the abstract statement.**

**LedgerRealization.lean / LedgerRealizationExt.lean** — **PROVEN** with real two-pole teeth.
`fullFill_cycle_ledger_realized` (`:222`) honestly conditional on `hsettle`; tightness load-bearing
(`nonTight_fullFill_not_conserving` computes `netFlow·10 = −2 ≠ 0`). Ext's
`partialFill_cycle_ledger_realized` (`:206`) is the sharp result (no tightness);
`shielded_ring_fused_clears` (`:312`) conditional on `hfused` (discharged concretely), the
Pedersen-value-in-AIR tie a named residual (Ext `:52-54`).

**ShieldedClearing.lean** — **PROVEN** with an honestly-named DECOUPLING: `shielded_ring_clears`
(`:187`) conjoins (a/b) conservation+fairness over the DECLARED `MatchNode` columns with (c)
privacy/no-double-spend over the HIDDEN note-spend — and the two layers are NOT bound (legA declares
`offerAsset 10, offerAmount 100` while its note is `asset 0, value 3`). Header states this openly;
fusion is the `LedgerRealizationExt` weld. `shielded_ring_value_conserves_hidden` (`:227`)
generic-PROVEN but its witness runs on the toy additive `refVC`; `shielded_ring_clears_real_crypto`
(`:259`) re-grounds on real Pedersen/Poseidon2 with named floors. **HONEST-CARRIER (decoupling
disclosed).**

**ShieldedRingEndpointDescriptor.lean** — **PROVEN**, strong. `ringKernel_settles` (`:91`) a general
settlement proof (funext, not a decide-toy); commitment-binding under named `Poseidon2WideCR`.
`RingEndpointAccepted` (`:495`) bundles `satisfied : Satisfied2` with `decode`/`fold` as STRUCTURE
FIELDS — the projections are sound given the structure, but the implication "Satisfied2 ⟹ decode ∧
fold" is ASSUMED (the descriptor-refinement residual `ProtocolAssurance` names). Honestly conditional.

**ZKOpenRel.lean** — **PROVEN**, honest, modest. Category/functor/`d⁻¹(0)` conservation genuine
Mathlib instances. Strong honesty signal: `guardedTraceClosure_refuted` (`:490`) proves the module's
OWN earlier conjecture FALSE. `traceAdmissible_guarded` (`:522`) a genuine Knaster-Tarski replacement.
CAVEAT: the four fhEgg instances are `TraceAdmissible` only TRIVIALLY — their feasibility relation is
`rel _ _ := True`, so admissibility is `Φ = id` over a total relation (`:661-678`), honestly noted.
Privacy (§7) is the WEAK functional notion (`view = sim ∘ Q` ⟹ same-leakage ⇒ same-view = naturality),
NOT cryptographic indistinguishability — honestly named.

**ProtocolAssurance.lean** — the MOST honest file; PROVEN-conditional on openly-named residuals.
`settleRing_refines_turnSpec` (`:232`) substantive (destination-liveness from balance + cycle
settlement). The composition theorems `lightclient_market_seam` (`:664`),
`starkMarketClaimExtraction_of_effect_step` (`:583`),
`accepted_market_settles_on_same_commitment_surface` (`:750`) all take `…Residual` propositions as
HYPOTHESES (`MarketEffectEndpointExtractionResidual` `:336`, `ShieldedRingApexRefinementResidual`
`:391`) — the `#assert_axioms`-invisible carriers, but every one is named `…Residual`, documented
OPEN. Crucially `not_marketEffectApexLiftResidual_balance` (`:528`) REFUTES their own proposed naive
bridge (tag-0 dispatch appends 1 receipt, a fused ring appends 2). `SettlementVerifier25Refines`
(`:872`) is a named-OPEN residual over an abstract `verifyProof`; the demo `#guard` (`:916`) uses
`fun _ _ => true` — a fake verifier, honestly a codec smoke test, NOT a soundness claim.

**Named carriers / floors / residuals in this cluster** (each `#assert_axioms`-invisible): `StarkSound
hash R` (typeclass), `MarketEffect*`/`ShieldedRing*Refines`/`StarkMarketClaimExtraction`
(descriptor-refinement obligations, naive route proven undischargeable `:528`),
`SettlementVerifier25Refines` + abstract `verifyProof` (Groth16 accept ⟹ clearing existence, OPEN),
`Poseidon2WideCR`/`Poseidon2Width8`, `CryptoPrimitives` DLog binding / `Poseidon2SpongeCR`, abstract
`rootOf`/`Root` (CrossChainSettlement, no crypto content), the `hsettle`/`hfused`/`hcont` conditional
hypotheses (discharged concretely in demos).

---

## RANKED IMPROVEMENT PLAN

1. **Reconcile the balance-threshold vs argmax split (Findings 1 & 2).** Decide what deployed
   `mpc_crossing` opens. If it opens the argmax (correctness-required), the clean §2 `p*`-determinacy
   argument does not apply to it — a new simulability argument is owed for the argmax transcript. If
   it opens the balance threshold (secure per §2), then it clears the SUBOPTIMAL price and the
   product is not volume-maximizing. Either way, re-name the joined theorem to state which optimality
   (weak uniform-price vs volume-max) and which price it actually joins to privacy. Highest value:
   this is the paper's marquee "novel join" and it currently over-claims.

2. **Discharge or shrink the `HidingFriPcs` statistical-ZK floor (Finding 4).** The deployed
   reveal-nothing is entirely conditional on it. It is honestly named, but it is THE confidentiality
   guarantee — a real Lean statistical-ZK simulator for the deployed FRI PCS is the biggest single
   assurance upgrade for the product.

3. **Mechanize the Rust↔Lean denotation binding (Finding 3).** The re-authored models are honest but
   the source-refinement residuals (`FhEggTfheSourceRefinementResidual`, `CertQpRustF64Refinement
   Residual`, `FhEggLedgerSourceBinding`) are trust-by-reading. Pin them with extracted-Rust
   differential tests or codegen so "the Lean models the deployed Rust" stops being inspection.

4. **Bind the perfect-hiding primitive to the deployed transcript (Finding 5).** Make `reveal_only`
   carry the masked VALUES (not just `maskedLen`) and discharge their hiding via `otpMasks`, so the
   confidentiality theorem is about the real transcript, not a view that excludes the sensitive lane
   by definition.

5. **Prove the deployed-realization ties or downgrade the prose (GraduationPool, Lending title).**
   Either verify the Solidity `DreggSolventPool` ↔ Lean correspondence, or soften "the deployed pool
   realizes" to "a model of the deployed pool." Same for the Lending "undercollateralization-
   impossible marquee" register vs its definitional content.

6. **Rebuild or retire FhIRAdmissible's "semantic" layer.** Either give `RunnableAt` genuine content
   independent of the manifest booleans (an actual carrier-transport / certificate-soundness
   predicate), or drop the syntactic⇒semantic framing — as written it is a MIRROR.

7. **Fix or re-name the two InterchainCustody keystones.** Bind `custody_cross_boundary_conserves` so
   the clearing `c` actually trades the mirror asset (share a variable), and replace the constant
   `refund` with a modeled mechanism — otherwise state them as trivial and stop calling them the
   cross-boundary keystone.

8. **Extract the CertFDescriptor gap-gate.** Prove `g == ε − (cᵀs − wᵀf)` at the descriptor level and
   compose the box-upper/dual link sub-lemmas into `certFDescriptor_emit_sound`, so the headline
   actually forces the ε-optimality clause it claims (currently ~2.5 of 5 families).

9. **Retire decorative lemmas** (`classify_exhaustive`) and tighten `no_improving_deviation`'s claim
   to what it proves (round-trip value-neutrality, not game-theoretic no-deviation).

## What FAILS the sufficient test (the valuable findings, ranked)

- **⚑ FhIRAdmissible.lean: MIRROR / VACUOUS-of-content.** The "semantic" `RunnableAt` layer is
  definitionally the same manifest booleans as the syntactic `passes`; `compiles_admissible` is a
  tautological flag-drop, and the "⟹ open gap" is a definitional artifact (ignore the one field the
  syntactic check uses). The doc's "non-vacuous semantic Prop" is laundering — no syntactic⇒semantic
  bridge exists. This is the clearest whole-file failure.
- **⚑ InterchainCustody.lean: one LAUNDERED conjunction + one VACUOUS tautology.**
  `custody_cross_boundary_conserves` (`:341`) conjoins two variable-disjoint facts (the `systemValue`
  clause is the same `gap` on both sides of an already-proven conservation); `lock_refund_restores`
  (`:445`) is `rfl` over a constant `refund` function. The atomicity gate is an uninterpreted Bool.
- **⚑ CertFDescriptor `certFDescriptor_emit_sound` (`:547`): OVER-NAMED — the ε-gap is not proved.**
  Doc claims all 5 certificate families incl. `cᵀs − wᵀf ≤ ε`; the gap-linking gate is extracted
  nowhere, so the ε-optimality clause (a certificate's whole point) is unestablished at the descriptor
  level. Delivers ~2.5 of 5.
- **⚑ MpcClearingSecurity joined theorem: OVER-NAMED** — reveals the suboptimal balance threshold;
  "optimal" is the weak uniform-price sense, not the volume-max the correctness file crowns.
- **Balance-threshold vs argmax model discrepancy** — the two core files disagree on what the MPC
  reveals; the clean §2 security argument covers only the balance-threshold transcript.
- **Lending `no_bad_debt`: definitional (`P ∧ ¬P`)** — disclosed, but the marquee register overshoots;
  **`classify_exhaustive`: VACUOUS/tautological** decorative lemma.
- **GraduationPool / Lending-title / CrossChainSettlement "deployed/cross-chain realizes":
  OVER-NAMED prose** — the `.sol` / foreign-chain / operational tie is not in the Lean statement.
- **The Rust↔Lean binding is not byte-identity laundered, but it is un-mechanized** — faithful only
  up to un-discharged named residuals.

Balanced against these: the conservation/fairness/optimality foundations (Priced, Fairness,
Optimality, Clearing, CertF, CertQp, PriceCert, MintSafeQuantization, LedgerRealization) are genuinely
PROVEN, non-vacuous, two-polarity teeth, bound to the REAL `settleRing`/`posFills`/`demoPool` objects —
no mirror there. RevealNothing, AggregateBinding, WideCommitBoundary, ProtocolAssurance name and grade
every carrier exemplarily, and ProtocolAssurance/ZKOpenRel even refute their own tempting shortcuts.
The failures cluster in (a) doc-register over-naming of statements that prove less than their prose,
(b) two genuinely content-free files/keystones (FhIRAdmissible, the two InterchainCustody theorems),
and (c) the confidentiality/denotation seams being named-but-un-discharged rather than mechanized.
