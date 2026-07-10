# DEBT-A — giving `verifyBatch` a DEFINITION and discharging `DeployedMatchesModel`

**Honest scope, first sentence.** The deployed `verify_batch`
(`p3-batch-stark`, rev `82cfad7`, `batch-stark/src/verifier/mod.rs:30`) runs a shape/ZK
validation → a Fiat-Shamir transcript → `pcs.verify` (the FRI query/PoW/Merkle/final-poly
loop, `:502`) → a per-instance OOD quotient identity `C(ζ)=Z_H(ζ)·q(ζ)` + logup check
(`:505-643`); the Lean `verifyAlgo` (`FriVerifier.lean:557`) models the **FRI core + the
quotient identity + query-PoW + a segment tooth** but STUBS Merkle (`merklePaths := true`,
`FriVerifier.lean:511`) and omits the shape/ZK/commit-phase-PoW/preprocessed-perm/global-logup
Rust steps — so it is a genuine but PARTIAL model; and **modeling `verifyBatch` alone does NOT
discharge `StarkSound`**, because it only reduces the code-refinement half (`DeployedRefines`,
link E) to a KAT obligation — the positive extraction half (`AlgoStarkSound.extract`, which
contains `FriExtract`) is a proof-of-KNOWLEDGE obligation that FRI proximity cannot manufacture
(commit `3ee8b5ee8`) and remains blocked regardless.

This doc is the `verifyBatch`-side companion to `DEBT-A-STARKSOUND-TARGET.md` (the
`AlgoStarkSound`/`DeployedRefines` audit) and `DEBT-A-CARRIER-AUDIT.md`.

---

## 1. What the deployed `verify_batch` actually does

`p3-batch-stark` rev `82cfad7`,
`~/.cargo/git/checkouts/plonky3-7d8a3b21a665a86f/82cfad7/batch-stark/src/verifier/mod.rs`
(the exact `verify_batch` the dregg backend calls — `circuit/Cargo.toml:201`, used at
`circuit/src/descriptor_ir2.rs:4868` etc.):

| # | Step | Lines |
|---|------|-------|
| 1 | destructure `BatchProof` (commitments, opened_values, opening_proof) | `:47-55` |
| 2 | shape sanity: `airs.len == instances.len`; ZK randomization present ⟺ `ZK` | `:60-85` |
| 3 | per-instance opened-values shape: trace widths, quotient-chunk counts, preprocessed widths, lookup-data lengths; `validate_degree_bits` | `:86-274` |
| 4 | Fiat-Shamir: observe instance count/binding/main/public/preprocessed, sample perm (logup) challenges + `alpha`, observe quotient commitment, **sample OOD `zeta`** | `:143-300` |
| 5 | build `coms_to_verify`: trace round (`ζ`,`ζ_next`), quotient-chunks round, preprocessed round, permutation round | `:302-499` |
| 6 | **`pcs.verify(coms_to_verify, opening_proof, challenger)`** — the FRI/Merkle opening argument (see §1a) | `:502` |
| 7 | per-instance: `recompose_quotient_from_chunks` at `ζ`, then `verify_constraints_with_lookups` = OOD identity `C(ζ)=Z_H(ζ)·q(ζ)` + logup | `:505-621` |
| 8 | global logup: cross-instance cumulative sums balance (`verify_global_sum`) | `:623-643` |

### 1a. Inside `pcs.verify` → `verify_fri` (`fri/src/verifier.rs:113`)

- sample folding `alpha` (`:143`); validate per-query commit-phase opening counts (`:147-204`)
- **commit-phase grinding PoW** per fold: `check_witness(commit_proof_of_work_bits, …)` (`:222`)
- `final_poly.len() == final_poly_len()` + observe (`:230-238`)
- `query_proofs.len() == num_queries` (`:241`)
- **query grinding PoW**: `check_witness(query_proof_of_work_bits, query_pow_witness)` (`:254`)
- per query: `sample_bits` index (`:268`) → `open_input` (Merkle-path openings) → `verify_query`
  FRI fold-chain with sibling-vs-commitment checks (`:298`) → **final-poly eval == folded_eval**
  (`:319-324`)

## 2. `verifyAlgo` ↔ Rust correspondence (the heart of `DeployedMatchesModel`)

`verifyAlgo` (`FriVerifier.lean:557`) = `vk.shapeMatches && foldConsistent && merklePaths &&
batchTables && queryPow && segmentTooth`.

| `verifyAlgo` conjunct | Rust step | Status |
|---|---|---|
| `foldConsistent` (`concreteFriChecks`, `:503`: query-count == derived qidx + `friQueryCheck` per query) | `verify_fri` query loop + `verify_query` fold-chain + final-poly eval (`verifier.rs:261-326`) | **MATCHED** (FRI core) |
| `batchTables` (`batchTablesCheck`, `:655`: OOD identity `C(ζ)=Z_H·q` + degree pin + per-table bus) | per-instance constraint check `:505-621` | **MATCHED** |
| `queryPow` (`queryPowCheck`, `:664`: `powBits`) | query grinding `check_witness` (`verifier.rs:254`) | **MATCHED** |
| `vk.shapeMatches` (`RecursionVk`, `:544`; blake3 VK **out of band**) | shape/degree validation `:86-274` | **PARTIAL** — real VK fingerprint not in the conjunct |
| `merklePaths` (`concreteFriChecks`: `= true`, `:511`) | Merkle openings inside `pcs.verify` (`:502`) | **RUST-ONLY / Lean STUB** — binding lemma `merkleRecompute_binds` (`:235`) exists but is NOT wired into the accept path |
| `segmentTooth` (`exposedSegment == pub.segment`, `:549`) | recursion public-input binding (wrap `ivc_turn_chain.rs`), not bare `verify_batch` | **LEAN-ONLY** (stricter — safe) |

**Rust steps with NO `verifyAlgo` counterpart** (verifyAlgo is WEAKER here — the dangerous
direction; each must live in the model's `extra` or `DeployedMatchesModel` is FALSE): ZK
randomization checks (`:74-85,:201-208`); full opened-values shape validation (`:86-274`);
**commit-phase grinding PoW per fold** (`verifier.rs:222`); preprocessed + permutation round
openings (`:408-499`); **global logup cross-instance balance** (`:623-643`); the actual
Merkle-path recompute (stubbed `true` in Lean).

**Net:** `verifyAlgo` is neither a subset nor a superset of the deployed verifier. It is
stricter on `segmentTooth`, EQUAL on FRI-fold/quotient/query-PoW, and STRICTLY WEAKER on
Merkle + shape/ZK + commit-PoW + preprocessed/perm + global-logup. So `verifyAlgo` accept does
NOT imply Rust accept, and (more dangerously) it is not the case that Rust accept implies
`verifyAlgo` accept until Merkle is de-stubbed — the `merklePaths := true` stub means a proof
with a forged Merkle path could pass `verifyAlgo` while the Rust verifier rejects, which is the
SAFE direction for `DeployedRefines` (Rust stricter) but means `DeployedMatchesModel` (byte
EQUALITY of verdicts) is currently unattainable without de-stubbing.

## 3. The restructure — Option A vs Option B

The scaffolding already exists (`DeployedRefinesProof.lean`):
- `verifyBatchModel := if verifyAlgo && extra then accept else reject` (`:55`)
- `DeployedMatchesModel R … := ∀ pi π, verifyBatch (vkOfRegistry R) pi π = verifyBatchModel …`
  (`:119`)
- `deployedRefines_of_matchesModel : DeployedMatchesModel ⟹ DeployedRefines` (`:134`, proved).

**Option A — `def verifyBatch := verifyBatchModel …`.** Makes `DeployedRefines` `rfl`-ish and
collapses the two obligations to one (`DeployedMatchesModel`). Two blockers:

1. **Import cycle.** `verifyBatch` is `opaque` at `CircuitSoundness.lean:353`;
   `verifyBatchModel`/`verifyAlgo` live DOWNSTREAM in `DeployedRefinesProof`/`FriVerifier`,
   which `import CircuitSoundness` (`FriVerifierBridge.lean:47`). Defining `verifyBatch` in
   terms of `verifyBatchModel` is circular. Option A requires moving `verifyAlgo` +
   `verifyBatchModel` **at or below** `CircuitSoundness`, or splitting `CircuitSoundness` so the
   apex sits above the model. That is a real file reshuffle, not a one-liner.

2. **Ripple.** `verifyBatch` is referenced by **25** `Dregg2/Circuit/*.lean` files; `StarkSound`
   by **42** (incl. `Dregg2/Crypto/*`). Most reason ABSTRACTLY (through the `accept` verdict /
   the `StarkSound` class) and would recompile unchanged when `opaque`→`def`. The exception is
   **`CustomCarrierAttack.lean`** (an adversarial proof that leans on `verifyBatch` being
   uninterpreted) — a `def` gives `verifyBatch` computational content and MAY break or trivialize
   those proofs; each must be re-audited. Also `DeployedMatchesModel` would then be trivially
   `True` for the chosen `extra`, so the residual MUST relocate into: (a) proving `extra`
   captures the Rust-only steps, and (b) the leanc/KAT discharge of §4 — otherwise Option A
   LAUNDERS the gap (relabels an assumed carrier as a definitional `rfl`).

**Option B — keep `verifyBatch` opaque, carry `DeployedMatchesModel` (or `DeployedRefines`) as
a named floor forever.** This is the current state. It is honest: the residual is a NAMED `Prop`
(`DeployedRefinesProof.lean:119`), never an `axiom`, and `deployedRefines_of_matchesModel`
isolates exactly what remains. Its cost: the trusted surface stays "two carriers" (see
`DEBT-A-STARKSOUND-TARGET.md §5`) and the verdict-equality is never mechanically checked.

**Recommendation:** Option B for the LOGIC (do not fake a `def`), plus the §4 empirical
discharge to give `DeployedMatchesModel` real teeth. Do NOT take Option A unless the reshuffle
lands AND the KAT corpus of §4 exists — a definitional `verifyBatch` without the corpus is the
`genuineChipTbl_sound`-over-constant-zero pattern (a name that sounds discharged).

## 4. Discharging `DeployedMatchesModel` — the Poseidon2 KAT precedent

**The precedent (`Poseidon2BabyBearW16.lean`).** The deployed permutation is MODELED in Lean
with the real round constants (`:169`) and VALIDATED bit-exact by `#guard`s (`:190,196,203`)
that replay known-answer vectors emitted from the deployed Rust
`default_babybear_poseidon2_16().permute(·)` — if the model diverged by one limb the build
FAILS (`:29-32`). That is the discharge pattern: a modeled computation + a golden corpus + a
build-failing equality check.

**Applying it to `verifyBatch`.** `DeployedMatchesModel` is a verdict equality over ALL
`(pi,π)`, so a finite `#guard` corpus VALIDATES but does not PROVE it — same status the
Poseidon2 `#guard`s have (validation, not a `∀`-theorem). Concretely:

1. **De-stub the model first.** Wire `merkleRecompute_binds` (`:235`) into a real `merklePaths`
   conjunct, and populate `extra` (`DeployedRefinesProof.lean:59`) with the Rust-only steps
   (ZK/shape/commit-PoW/preprocessed-perm/global-logup, §2). Until then `verifyBatchModel` ≠ the
   Rust verdict on Merkle-forged or shape-malformed proofs and the corpus WILL diverge.
2. **The harness EXISTS.** `dregg-lean-ffi/` links the Lean archive (`libdregg_lean.a`) via the
   `@[export]` no-copy `lean_object*` boundary (`src/lean_direct.rs`) and already runs
   Lean↔Rust differentials (`src/circuit_differential.rs`, `src/state_differential.rs`) against
   a golden corpus (`goldens/`, `REGENERATE.md`). No `@[export]` on `verifyAlgo`/`verifyBatchModel`
   exists yet (grep: zero in `FriVerifier.lean`/`DeployedRefinesProof.lean`) — that marshalling is
   the build task.
3. **The corpus.** Real proofs from `verify_batch`'s call sites (`descriptor_ir2.rs:4868`,
   `merkle_air.rs:139`, `dsl/dsl_p3_air.rs:796`) — ACCEPT cases plus REJECT cases (tampered
   quotient, forged Merkle path, wrong query count, bad PoW) — fed through BOTH the Rust
   `verify_batch` and the `@[export]`-ed `verifyBatchModel`; assert equal verdicts. Put the
   corpus under `circuit/tests/fixtures/` (alongside `discharge-sat-v3-staged.json`) or
   `dregg-lean-ffi/goldens/`.

**Honest residual after the corpus:** exactly `leanc` (trust the Lean→C compilation of the
exported model) + the corpus's coverage (a differential over a finite sample, not a `∀`-proof) +
the `extra`/Merkle de-stub being faithful. That is the same residual class the Poseidon2 KAT
carries — validation, not proof — and it is honest to state it as such.

## 5. Verdict — does modeling `verifyBatch` SUFFICE for `StarkSound`?

**No.** `StarkSound.extract` (`CircuitSoundness.lean:382`) demands, from `verifyBatch … =
accept`, a PRODUCED satisfying `VmTrace` `t`. The bridge factors this into `AlgoStarkSound`
(accept ⟹ ∃ trace, the extraction) × `DeployedRefines` (Rust = spec) —
`starkSound_of_verifyAlgo` (`FriVerifierBridge.lean:106`). Modeling `verifyBatch` (Option A) or
running the §4 KAT corpus discharges ONLY `DeployedRefines`/`DeployedMatchesModel` — the
CODE-refinement half (link E). The positive extraction `AlgoStarkSound.extract` (link A′/D)
is UNTOUCHED, and it contains `FriExtract`.

Per commit `3ee8b5ee8` (`FriExtractReal.lean`, `AggAirSound.lean:140`): `FriExtract` is a
proof-of-KNOWLEDGE obligation living ABOVE FRI — it takes a PROPERTY ("the subcircuit is
satisfied") and must yield an EXPLICIT native WITNESS. FRI proximity presupposes the transcript;
it never manufactures one ("the direction is wrong"). So no amount of FRI-at-BabyBear or
`verifyBatch`-modeling work discharges `FriExtract`; it needs (i) in-circuit ⟹ native knowledge
extraction and (ii) `oracle_binding` (Poseidon2 HashCR) pinning `(c,s)`.

**Therefore:** modeling `verifyBatch` is worth doing — it de-opaques the verifier verdict,
lets the proven reject-teeth bite the deployed verifier
(`deployed_rejects_tampered_quotient`, `FriVerifierBridge.lean:170`), and reduces the
code-trust residual to a Poseidon2-style KAT — but it does NOT finish DEBT-A. After it,
`StarkSound` still rests on the assumed `AlgoStarkSound.extract`, whose FRI-extraction core is
blocked by the knowledge-extraction gap, independent of the verifier model. Do the modeling for
what it buys; do not represent it as closing the keystone.
