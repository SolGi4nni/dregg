# AIR Composition & Proof-Verification-Count Audit

Date: 2026-06-28. Scope: read-only soundness/architecture audit of AIR composition,
the per-turn proof-verification surface, and the staged gentian/satisfaction welds.
Evidence is cited to file:line at HEAD. **No code was changed by this audit**; every
finding below names a fix but does NOT apply it (concurrent gentian-deep / screenshot /

Method: read the composition machinery (`circuit-prove/src/{lean_lookup_air,
joint_turn_recursive,custom_proof_bind}.rs`), the EffectVM AIR + column layout
(`circuit/src/effect_vm/{air,columns,trace_rotated,satisfaction_weld,
authority_digest_weld}.rs`), the deployed verify path (`turn/src/executor/
{proof_verify,atomic}.rs`, `cell/src/custom_effect.rs`), the degree budget
(`circuit/src/descriptor_ir2.rs`), and a metatheory sweep of the named engine facts
and weld Lean specs (`metatheory/Dregg2/**`).

---

## Q1 — AIR composition correctness

**Verdict: composes correctly, with the soundness resting on a small set of explicitly
NAMED engine facts that are Lean hypotheses/structure-fields, never axioms. No
dregg-specific soundness is assumed-without-proof. No unconstrained lookup bus found in
the audited surface.**

### The composition machinery and where each rests

- **Multi-table batch (the deployed leaf verify).** A sovereign transition is verified
  through `descriptor_ir2::verify_vm_descriptor2` over an `Ir2BatchProof`
  (`turn/src/executor/proof_verify.rs:278-489`). Tables + LogUp legs are folded into one
  batch-STARK whose `degree_bits` are re-derived by the verifier via
  `ProverData::from_airs_and_degrees` (`circuit/src/descriptor_ir2.rs:4804,4864`) — the
  verifier does not trust prover-supplied shapes (it checks `proof.degree_bits.len() ==
  airs.len()` and pins byte-table `degree_bits == LIMB_BITS`,
  `descriptor_ir2.rs:4794-4857`).

- **LogUp range bus (`circuit-prove/src/lean_lookup_air.rs`).** The `[0,256)` range
  table and the query AIR share the `range8` bus (`RANGE_BUS`, line 68); the table emits
  `bus.table_entry(value, mult)` (line 234) and the query emits `bus.lookup_key(limb)`
  (line 279); the batch prover enforces the global cumulative sum balances to zero. The
  bus is correctly wired: multiplicities are computed to balance
  (`build_query_trace`/`build_range_table_trace`, lines 298-366), and a **recomposition
  tooth** `Σ limbᵢ·256ⁱ = wire` (line 283) plus a tight top-limb bit-decomposition
  (lines 258-275) close the field-wrap gap the byte table alone would leave. The
  adversarial test `range_lookup_rejects_out_of_range` (line 555) confirms a value ≥ 2³⁰
  has no satisfying witness. **No unconstrained bus.** The module's own docstring is
  honest that LogUp-argument soundness ("a balanced bus ⟹ every queried limb is a real
  table entry") is the p3-lookup cross-system portal, not relitigated here
  (`lean_lookup_air.rs:36-45`).

- **Recursive aggregation (`circuit-prove/src/joint_turn_recursive.rs`).** N per-cell
  rotated descriptor leaves + a binding leaf are wrapped in-circuit (uni→batch) and
  pairwise-folded to ONE root via `aggregate_tree` (lines 342-382). The verifier checks
  exactly three teeth: VK-pin, claimed-publics-against-the-carried-binding-proof, and the
  root batch proof — cost independent of cell count
  (`verify_joint_turn_recursive`, lines 396-431). The discriminating tooth
  `ungated_joint_prover_with_forged_cell_commit_cannot_produce_a_root` (named lines
  54-61) earns the claim that the host gate is admission discipline, not the soundness
  boundary: a forged `cell_commit` has no satisfying descriptor leaf.

### The named engine facts — confirmed hypotheses/structures, NOT axioms

The metatheory sweep found **no load-bearing `axiom` and no `sorry`** anywhere in the
soundness stack. The only two real `axiom` decls in `Dregg2` are deliberately-labeled
demo axioms for the proof-badge gallery (`Dregg2/Widget/Basic.lean:298-299`), referenced
by no soundness theorem. The carriers are:

| Fact | Kind | Location |
|---|---|---|
| `StarkSound` (FRI/p3 verify ⟹ ∃ witness extraction; includes the LogUp leg) | `class … : Prop`, threaded `[StarkSound …]` | `Dregg2/Circuit/CircuitSoundness.lean:382` |
| `Poseidon2SpongeCR` (collision resistance) | `def … : Prop`, threaded `hCR` | `Dregg2/Circuit/Poseidon2Binding.lean:169` |
| `descriptorRefines` (per-effect refinement) | `def … : Prop`, threaded `hrefines` | `CircuitSoundness.lean:232` |
| `DeployedFaithful` (deployed-tree faithfulness) | `structure` | `Dregg2/Circuit/DeployedCapTree.lean:299` |
| `EngineSound{recursive_sound,leaf_sound,binding_sound}` (= the doc's `RecursiveVerifierSound`/`InnerProofSound`/`BindingAirSound`) | `structure … : Prop`, threaded `es` | `Dregg2/Circuit/RecursiveAggregation.lean:121-136` |

The doc names `InnerProofSound`/`BindingAirSound`/`RecursiveVerifierSound` appear ONLY in
docstrings (`RecursiveAggregation.lean:24,29,33`); the real carrier is the `EngineSound`
structure whose three FIELDS are the hypotheses, with a non-vacuity/satisfiability tooth
(`RecursiveAggregation.lean:344-352`) so the bundle is not vacuously assumable.

### The apex

`lightclient_unfoolable` (`CircuitSoundness.lean:453`) states: a verifying batch (the
light client supplies only `pi`,`π` — no `pre`/`post`) yields a genuine kernel transition
committing to `pi.pre`/`pi.post`, carrying `hCR`, `[StarkSound]`, `hrefines`, `hwitdec`.
`#assert_axioms`-clean (line 1058). The `∀ e, descriptorRefines` family is **assembled +
proven** from the per-effect rungs (`CircuitSoundnessAssembled.lean:447`,
`ClosureFanoutGenuine.lean:1066`), each `#assert_axioms`-clean, leaving only the standard
crypto carriers. The LogUp/multiset bus has **no separate Lean soundness statement** — it
is subsumed into `StarkSound` (confirmed: no `LogUp`/`multiset`-argument theorem exists;
`Dregg2/Crypto/Dfa.lean` models lookups abstractly as a membership relation, not the
argument).

**Q1 conclusion:** the composition is sound modulo exactly the standard, explicitly-carried
crypto floor (FRI/STARK extraction including LogUp, Poseidon2-CR, deployed-tree
faithfulness, recursion-engine soundness). Nothing dregg-specific is assumed without proof.

---

## Q2 — Proof-verification count per turn (the cost/DoS surface)

**Verdict: the EffectVM leaf count is bounded by the (wire-controlled) cohort-run count,
with roughly symmetric prover/verifier cost. BUT the custom-effect sub-proof
verification loop is UNBOUNDED and ASYMMETRIC — a single authorized turn can force the
verifier to run an arbitrary number of recursive STARK verifications. This is a real
DoS finding (FINDING 1).**

### (a) The EffectVM STARK — one verify per *cohort run*, not per effect

Within one homogeneous cohort run, the entire effect sub-sequence is rows of ONE AIR
instance ⇒ one batch verify (`verify_one_cohort_run`,
`proof_verify.rs:422,487`). A turn splits into N **maximal homogeneous** cohort runs
(`split_into_cohort_runs`, `proof_verify.rs:357`); the multi-cohort path verifies one leg
per run and chain-checks adjacency (`proof_verify.rs:367-447`). So the EffectVM verify
count is **N = number of cohort runs ≤ effects.len()** (worst case: an effect set that
alternates classes). This fan is roughly **symmetric**: forcing N leg-verifies requires
the attacker to produce N valid chained legs (a broken chain fails fast at the adjacency
check, `proof_verify.rs:399-407`, before the expensive per-leg verify). Lower-severity
than (b), but note there is no explicit cap on `effects.len()` / cohort-run count — see
FINDING 2.

### (b) FINDING 1 (Medium-High) — unbounded, asymmetric custom-proof verification

`enforce_custom_effect_proofs` (`turn/src/executor/proof_verify.rs:222-253`) runs at the
TOP of `verify_and_commit_proof` (line 198), **before** the main proof is verified, and
loops over **every** entry of the wire-supplied `turn.custom_program_proofs` vec:

```rust
for (i, proof) in proofs.iter().enumerate() {
    registry.verify(&proof.vk_hash, &proof.public_inputs_bytes(), &proof.proof_bytes)?;
}
```

`registry.verify` dispatches to the registered `CustomEffectVerifier::verify`
(`cell/src/custom_effect.rs:350-363`); the genuine production verifier is
`custom_proof_bind::verify_proof_bind`, which performs a **full recursive STARK verify**
(`program.verify_transition`, `circuit-prove/src/custom_proof_bind.rs:268`).

There is **no length cap** on `turn.custom_program_proofs` and **no binding** of its
length to the in-circuit `PI[CUSTOM_EFFECT_COUNT]` or to the cell's `max_custom_effects`.
Confirmed:
- the in-circuit sum-check binds the number of Custom *rows* in the trace to
  `PI[CUSTOM_EFFECT_COUNT]` (`circuit/src/effect_vm/columns.rs:247-250`,
  `pi.rs:74-78`), with verifier-supplied `PI[MAX_CUSTOM_EFFECTS]` hard-capped at
  **64** (`pi.rs:783`, soft 16, default 4) — but this is the *in-circuit row count*,
  entirely separate from the off-circuit wire vec;
- a grep for any comparison of `custom_program_proofs.len()` against the in-circuit
  count, `max_custom_effects`, or any cap returns **nothing**;
- `enforce_custom_effect_proofs` has no early bound;
- the loop does not deduplicate identical entries.

**The attack.** A cell owner submits ONE authorized turn (one signature, one fee) whose
`custom_program_proofs = vec![valid_proof; M]` for attacker-chosen large M, replicating a
single valid sub-proof. The verifier runs M recursive STARK verifications before doing
anything else. Cost: verifier work ≈ M × (one recursive STARK verify ≈ ~ms–tens-of-ms);
attacker work ≈ producing one small sub-proof. At M = 10⁶ this is minutes-to-hours of
verifier CPU per turn — a strongly asymmetric resource-exhaustion DoS. The turn-hash binds
the vec (`turn/src/turn.rs:495-497`) but that only fixes identity, not length. The fee is
per-turn, not per-proof, so it does not bound the work.

**Proposed fix (NOT applied).** In `enforce_custom_effect_proofs`, BEFORE the loop:
1. reject the turn if `proofs.len()` exceeds the cell's declared `max_custom_effects`
   (read via the existing `read_cell_max_custom_effects`, itself hard-capped at
   `MAX_CUSTOM_EFFECTS_HARD_CAP = 64`). This is the cheap, decisive DoS cap (≤64
   verifies/turn) and needs no proof.
2. (completeness, separately) after the main EffectVM proof verifies, cross-check
   `proofs.len() == PI[CUSTOM_EFFECT_COUNT]` so the off-circuit dispatch count equals the
   in-circuit Custom-row count — closing the orthogonal seam that the wire vec and the
   in-circuit count are currently independent.

Enforcement point: the kernel gate (`enforce_custom_effect_proofs` is the executor /
light-client entry that already fail-closes on an unregistered vk_hash). The cap also
belongs in the SDK turn builder as a producer-side guard, but the *binding* check must be
in the kernel gate.

### (c) Other forced verifies

The recursive aggregation root is ONE verify regardless of cell count
(`verify_joint_turn_recursive`, by construction). The custom `proof_bind` recursion is
the only per-step recursive verify beyond the EffectVM leaf, and it is the unbounded one
above.

---

## Q3 — Are the weld AIR specs good?

**Verdict: the staged weld gates are well-formed — degree-correct (≤2, far inside the
budget), columns real/allocated, selector-gating structurally inert at sel=0, and the
gate semantics faithful to the Lean spec they claim. The honest STAGED caveat (the
recompute/decode CHAINS are not yet realized) is correctly mirrored on both the Rust and
Lean sides as named hypotheses, not hidden gaps.**

### Degree

- Whole-batch constraint-degree ceiling is **8** (`setFieldDyn` main gate), with the main
  table ≤3 for every other descriptor, far inside `log_blowup = 6`
  (`descriptor_ir2.rs:4476-4478,4954-5011`, the `ir2_degree_budget` tooth). The EffectVM
  AIR descriptor pins `max_degree: 9` (`effect_vm/air.rs:328`).
- The satisfaction gates are `sel · (col − const)` = **degree 2**
  (`satisfaction_weld.rs:34,77-83`). The gentian gates are recompute-bind = degree 1
  (`diff_gate`), decode-boolean = degree 2, selector-force = degree 2
  (`authority_digest_weld.rs:67-104`). All ≤2 row-local gates — they do NOT raise the
  main-table degree past the frozen budget.

### Columns real/allocated

- `ESCROW_SEL_COL = PARAM_BASE+2 = 70`, `WIT_DIGEST_COL = PARAM_BASE+3 = 71`,
  `FLOOR_ESCROW_COL = PARAM_BASE+4 = 72` (`satisfaction_weld.rs:51`,
  `authority_digest_weld.rs:52,57`), inside the deployed 8-wide param block
  (`PARAM_BASE = 68`, `NUM_PARAMS = 8`, `columns.rs:208-210`), which the rotated trace
  preserves (graduation APPENDS; positions `< ROT_WIDTH` unchanged,
  `trace_rotated.rs:104-118`). These are real allocated columns. The recompute-bind reads
  `auth_digest_col() = BEFORE_BASE + B_AUTHORITY_DIGEST` (r23, limb 24,
  `trace_rotated.rs:127,173`) — the committed authority-digest limb the chained
  `wireCommitR` → ~124-bit wide commit absorbs, so a pure light client binds it. No
  phantom column refs. The four gentian columns are asserted distinct
  (`authority_digest_weld.rs:141-157`).
- Note (informational, not a finding): these three param slots are general scratch
  multiplexed per-descriptor — in the *Custom* descriptor the same physical cols 68..76
  carry `custom_program_vk_hash`/`custom_proof_commitment` (`columns.rs:498-502`). No
  aliasing within a single descriptor (settleEscrowSat ≠ custom, different VKs), but the
  8-column param block is the scratch budget each welded descriptor draws from.

### Selector-gating inert at sel=0

The gates are products with the selector/floor column, so they vanish *structurally*
(degree, not intent) when the gate column is 0. Confirmed by tests
`selector_off_makes_the_gates_inert` (`satisfaction_weld.rs:279`) and
`non_escrow_cell_leaves_selector_free` (`authority_digest_weld.rs:212`). The biting teeth
are present and pass: `partial_settle_is_unsat`, `phantom_settle_is_unsat`,
`emitted_descriptor_carries_the_welded_gates_and_they_bite` (parses the staged
`settleEscrowSatVmDescriptor2R24` from the committed registry TSV and confirms the Rust
builder reproduces its four emitted gate bodies byte-for-byte,
`satisfaction_weld.rs:205-277`); `floor_one_with_selector_off_is_unsat`,
`forged_digest_is_unsat`, `non_boolean_floor_is_unsat` (`authority_digest_weld.rs`).

### Gate semantics faithful to spec

The recompute-bind gate `WIT_DIGEST_COL − AUTH_DIGEST_COL == 0`
(`authority_digest_weld.rs:89,100`) does bind the recompute-output column to the committed
`B_AUTHORITY_DIGEST` limb. The Lean twins `gentian_selector_forced`/`gentian_settle_forced`
(`Dregg2/Deos/InAirAuthorityDigestSelector.lean:243,281`) prove the selector is forced
ON from the committed declaration — **conditional on three named hypotheses**: `hbinds :
DeclCommitBinds` (the authority-digest collision-resistance floor,
`Dregg2/Deos/ConstraintBinding.lean:142`, the analog of `Poseidon2SpongeCR`), `hrecompute`
(recompute-output = digest(witnessed decl)), and `hdecode` (floor column = escrow-bit
decode). `hrecompute`/`hdecode` are exactly the gadget-faithfulness chains the Rust marks
as "named remaining work" (`authority_digest_weld.rs:25-31`). The Lean does NOT claim the
chains are proven; it models them as hypotheses and proves the forcing + teeth on top
(`#assert_all_clean` at `InAirAuthorityDigestSelector.lean:412`,
`CapacitySatisfaction.lean:477`, `SettleEscrowSatWideDescriptor.lean:266`). This is an
honest STAGED seam, not a laundered gap.

**Caveat to keep visible (not a defect of the spec, a property of STAGED-ness):** until
the recompute/decode chains are realized in-AIR and the VK is flipped, a pure light client
does NOT yet witness satisfaction — only a verifier holding the committed-state opening
does (`satisfaction_weld.rs:21-31`). The specs say so plainly.

---

## Q4 — Does the gentian gadget have to be in-AIR?

**Verdict: the degree-≤2 selector-forcing/satisfaction SKELETON is appropriately in-AIR
(`base ++ gentianGates`) and sustainable — it adds constraints, not main-table degree
past budget, and ~no width (reuses param scratch). The part that genuinely pressures the
choice is the unrealized recompute/decode CHAIN, where a composed chip-lookup sub-table
(Option B) is the better tool than a raw in-AIR byte-sponge (Option A). Threshold below.**

### Why in-AIR is fine for the skeleton

- **No extra verify.** Appending gates to the existing EffectVM descriptor keeps the
  per-turn leaf count unchanged (Q2). A separate weld-AIR composed via LogUp/batch would
  add a table to the batch (more FRI work) for no benefit at this degree.
- **No degree-budget pressure.** The added gates are degree ≤2 row-local equalities
  (Q3); the frozen main-table budget is 8 (`descriptor_ir2.rs:4956`), the FRI engine runs
  `log_blowup = 6`. Degree-≤2 selector gates cannot approach that ceiling regardless of
  how many welds (18/19/Custom/temporal) are added.
- **No width accumulation across effect classes.** Each weld lives in its OWN cohort
  descriptor (`settleEscrowSatVmDescriptor2R24`, etc.), and reuses the same 8 physical
  param scratch columns per-descriptor rather than widening a shared mega-AIR. So adding
  per-effect-class welds does not monotonically grow one EffectVM AIR's width.

### The real threshold

The 8-wide param scratch block (`NUM_PARAMS = 8`, `columns.rs:210`) is the per-descriptor
budget. The gentian skeleton already consumes param2/3/4 (selector + recompute-out +
floor). A single welded descriptor that needs MORE than ~5 fresh scratch columns, OR a
gate above degree ~8, would blow the budget. The named remaining gentian work — the
literal in-AIR recompute of `compute_authority_digest_felt` (a variable-length byte-sponge
over the postcard declaration) and the `required_capacity_caveat_tags` decode
(`authority_digest_weld.rs:26-31`) — is precisely such a case: a raw in-AIR sponge
(Option A) is a high-degree, many-column constraint family that WOULD pressure both
budgets. The design's Option B (a felt-domain required-floor limb + **chip-lookup**
recompute) is exactly the "separate composed sub-table via LogUp" approach — it keeps the
main table thin and pushes the sponge into the already-present poseidon2-chip table
(`N_ROT_SITES = 40` lane blocks, `trace_rotated.rs:106-118`). 

**Recommendation:** keep the degree-≤2 forcing/satisfaction gates in-AIR (they are
cheap and correct there); realize the recompute/decode chains via the chip-lookup route
(Option B), NOT as raw in-AIR sponge constraints — that is the sustainable boundary as
more effect families are welded.

---

## Summary of findings

| # | Severity | Finding | Fix (proposed, not applied) |
|---|---|---|---|
| 1 | **Medium-High** | `enforce_custom_effect_proofs` loops over the wire-supplied `turn.custom_program_proofs` with no length cap and no binding to `PI[CUSTOM_EFFECT_COUNT]` / `max_custom_effects`; each entry is a full recursive STARK verify, run before the main proof. A single authorized turn (one fee) replicating one valid sub-proof forces arbitrarily many verifications — asymmetric DoS. (`turn/src/executor/proof_verify.rs:222-253`, `cell/src/custom_effect.rs:350`) | Cap `proofs.len()` against the cell's `max_custom_effects` (hard cap 64) before the loop, in the kernel gate; separately, after the main verify, assert `proofs.len() == PI[CUSTOM_EFFECT_COUNT]`. |
| 2 | Low | No explicit cap on `effects.len()` / cohort-run count ⇒ EffectVM leaf-verify count grows with a wire-controlled effect count (cost roughly symmetric, so lower severity). (`proof_verify.rs:357-447`) | Bound effects-per-turn at admission; or rely on wire-decode size limits + the symmetric proving cost. Verify the postcard decode bound is set. |
| — | Info | Layout comments in `columns.rs:11,31` disagree on EffectVM width (186 vs 188) vs `trace_rotated.rs:80` (V1_WIDTH 187); param scratch is multiplexed per-descriptor (no aliasing, but the 8-col block is the weld budget). | Reconcile comments in the descriptor-regeneration lane. |

**Verdicts:** Q1 composes-correctly (modulo the named standard-crypto carriers, all Lean
hypotheses/structures, zero axioms). Q2 EffectVM = 1 verify per cohort run (bounded by
effects, symmetric); **custom-proof verification is UNBOUNDED and asymmetric — FINDING 1**.
Q3 weld specs are good (degree-correct, real columns, structurally inert at sel=0,
spec-faithful, honestly STAGED). Q4 in-AIR is the right call for the degree-≤2 skeleton
and sustainable; realize the recompute/decode chains via a composed chip-lookup, not a raw
in-AIR sponge.
