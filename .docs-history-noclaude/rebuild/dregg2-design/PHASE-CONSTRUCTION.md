> **Provenance.** Recovered 2026-05-30 from the prior session's read-only study agent
> (`~/.claude/.../subagents/`), which designed this as the body for this path but could not
> write it (read-only `Plan` mode). Verbatim except for stripped read-only-mode preamble.
> Consolidated alongside `PHASE-SHIFT.md`.

# PHASE-CONSTRUCTION — the META roadmap: from verified Lean kernel/Spec to the running dregg system

**Intended doc path:** `/Users/ember/dev/breadstuffs/docs/rebuild/PHASE-CONSTRUCTION.md` (I am in read-only/planning mode — this content is the doc body; it was not written to disk).

**Status anchor (ground truth, from code 2026-05-30):** what exists is a verified *micro-core* (`Dregg2/Exec/Kernel.lean`: a 2-field `KernelState` = `Finset accounts + bal : CellId→ℤ + caps`, one `exec` doing one transfer with conservation + fail-closed authority PROVED), a *matured abstract Spec web* (`Dregg2/Spec/*` — Guard/Conservation/Authority/Lifecycle/Hyperedge/Choreography/Await/VatBoundary, cross-linked by `Coherence`), the *first `Exec ⊑ Spec` square* (`Dregg2/Spec/ExecRefinement.lean` — conservation + authority projections PROVED, operational LTS OPEN), a *content-addressed cell substrate* not yet wired into the kernel (`Dregg2/Exec/Value.lean`), and a *working FFI beachhead* (`dregg-lean-ffi/`, 10k/10k golden-oracle differential). This is NOT a verified distributed OS and NOT yet a dregg1 successor. This doc frames the phase that makes it one, and frames the four tooling studies that feed it.

---

## 1. The refinement-to-implementation strategy

There are three ways Lean meets running Rust, and the honest answer is **all three, partitioned by trust criticality** — not one chosen globally. The repo already instantiates the seams for each.

### The three options (each already has a beachhead in-tree)

**(a) Lean-as-host via FFI** — Rust calls the compiled Lean kernel over the C ABI. Beachhead: `Dregg2/Exec/FFI.lean` `@[export]`s `dregg_kernel_transfer_total` / `dregg_kernel_authorized` (the *same* `exec`/`authorizedB` whose `exec_conserves`/`exec_authorized` are proved); `dregg-lean-ffi/` links the 258MB `libdregg_lean.a` and runs it. **Strength:** the running bytes ARE the proved function — zero translation gap. **Cost/risk:** the Lean runtime (GC, `lean_object`) lives inside a Rust process; marshalling is scalar-only today (`UInt64 ⇄ ℤ`); real turns carry `Digest`/`Proof`/`Finset`-shaped state whose marshalling could become its own unverified TCB (DREGG1-TO-DREGG2 risk #2). `lake⟷cargo` build integration and wasm32 cross-compile are open engineering.

**(b) Lean→Rust extraction/transpilation** — compile/transpile the kernel to readable Rust. **Strength:** no Lean runtime in production; native speed. **Cost/risk:** Lean has no production-grade verified extraction to Rust (unlike CakeML for HOL4, which is the move svenvs Tier 2 makes). Building one is a research project and inserts an *unverified compiler* into the TCB — exactly the trust regression to avoid. **Recommendation: do not build this now.** It is the long-run ideal but off the critical path.

**(c) Differential golden-oracle** — Lean is the *reference*; native Rust is validated against it case-by-case until 100% agreement, then swapped. Beachhead: `dregg-lean-ffi/src/differential.rs` (10k/10k agree), the `dregg-dsl-differential` "backend #8". **Strength:** keeps dregg1 running the whole time; lets fast native Rust own the hot path while a *proved* oracle certifies it; no Lean runtime in the shipped fast path. **Cost/risk:** agreement is empirical cross-validation over the tested distribution, *not certification* (DREGG1-TO-DREGG2 risk #3) — a Rust impl can diverge on untested inputs.

### Recommended partition

| Part of the system | Strategy | Why |
|---|---|---|
| **The semantic decision core** (admissible? post-state? authorized? conserves?) — the REPLACED-BY-LEAN crates `turn`/`cell`-program/`coord` | **(a) Lean-as-host** as the always-lawful baseline, with **(c) differential** as the migration ratchet | The decision is small, soundness-critical, and proved. Host it; diff the native fast-path against it until equal, then the native path is certified-by-oracle. This is the cascade already designed. |
| **Crypto / proving / transport / persistence** — the STAY-RUST portal impls (`circuit`, `credentials`, `blocklace`, `net`, `storage`, `secrets`) | **neither** — these are `@[extern]` portal *instances* (`CryptoKernel`/`World`), validated by **(c)** on their laws | Lean never proves crypto soundness (the §8 boundary). Rust *implements* the portal; the harness property-tests `commit_hom`/`hash_inj`/`recv_mono` hard. |
| **Products** (`node`, `extension`, `cli`, `sdk` construction half, bots) | **STAY-RUST**, hosting an FFI-shim kernel | Above the core; gain a verified backbone, change little at the surface. |
| **Long-run** | **(b) extraction** | Only once a verified Lean→Rust path exists. Not now. |

**Where the toy `KernelState` gets replaced by the concrete `Value` cell.** Today `KernelState.bal : CellId→ℤ` is a single scalar ledger. The concrete cell is `Dregg2/Exec/Value.lean`'s schema-keyed record `Value` (named fields, `flatten`/`width`/`conforms`, `flatten_width` PROVED — the circuit-over-records foundation that un-freezes dregg1's 8-slot `[FieldElement;8]` in `cell/src/state.rs:11`). The replacement is **Phase (i)+(ii)**: lift `KernelState` so a cell's state is a `Value` conforming to a `Schema`, re-prove `exec_conserves`/`exec_authorized`/`cexec_attests` over it, and re-state the conserved quantity as a `Spec.Conservation` domain measure over the `balance` field rather than the whole-state ℤ. `Value.lean` is built but **not yet imported by `Kernel.lean`** — wiring it in IS the concrete-instance work.

---

## 2. Closing the verification loop — what "verified dregg" actually means

End-to-end "verified dregg" is the **three-layer refinement tower**, with the crypto portal discharged externally:

   Metatheory (candidate-independent logic)         Metatheory/ConstructiveKnowledge.lean
        ⊒  realizes
   Spec  (abstract laws of dregg2)        ⊑    Dregg2/Spec/* (Guard/Conservation/Authority/…)
        ⊒  refines                              cross-linked by Spec/Coherence
   Exec  (executable design kernel)       ⊑    Dregg2/Exec/Kernel.exec
        ⊒  refines / golden-oracle
   Rust  (running impl, FFI-hosted)            dregg-lean-ffi + the cascade
        with §8 portal obligations discharged by circuits (CryptoKernel/World laws)

The chain is **Spec ⊒ Exec ⊒ Rust**, each link a refinement square, and the §8 crypto/world laws cut out to circuit obligations (the honest open-obligation bucket #1 in README; never Lean's job).

**What's proved today (the beachhead):** `Spec/ExecRefinement.lean` proves the **conservation projection** (`exec_refines_conservation`: the kernel's `Σδ` over `Bal=ℤ`, `Domain.balance` IS `Spec.conservedInDomain`) and the **authority projection** (`exec_authz_refines_guard` + `exec_heldcap_is_graph_has`: the decidable cap gate refines `Spec.Guard`/`Spec.Authority.Graph`) of the `Exec ⊑ Spec` square, assembled in `exec_step_refines`. The bottom edge (`Exec ⊒ Rust`) is the FFI + differential. The §8 cut is `Circuit.bridge` (the kernel circuit ↔ `fullStepInv`, both directions, from which `CryptoKernel.verify`'s law is *derived* per SUCCESSOR-ROADMAP).

**The minimal closed loop for ONE application.** The cleanest candidate is the **RDII authenticated-workflow / transfer** already in-tree as `Dregg2/Protocol/Workflow.lean` (the "DocuSign for authenticated workflows": author→reviewer→CI, every step capability-gated, phase-ordered, attested via `CryptoKernel.verify`). The minimal loop is:

1. **Spec layer:** the workflow's "who may sign / in what order / with what attestation" expressed as `Spec.Guard` gates (authorization ⊣ + precondition + caveat) over a `Spec.Lifecycle`/phase transition — currently `Workflow.lean` proves `exec_authorized`/`exec_in_order`/`merge_requires_approved`/`exec_attested` directly; re-found them as `Spec.Guard.admits` instances.
2. **Exec layer:** the workflow step is one `exec` over a `Value`-cell whose schema carries `phase`; the `Exec ⊑ Spec` square (extended to the workflow gate) certifies the executable step refines the Spec gate.
3. **Rust layer:** the `extension`/`node` drives the UI/transport; the *decision* ("may this party take this step now?") calls the FFI-hosted kernel; the differential harness keeps the native fast-path ≡ the oracle.
4. **§8:** the signature/attestation is a `CryptoKernel.verify` statement — ZK-capable, discharged by `circuit`/`credentials`.

That is "verified dregg" for one application: an authorization that is **machine-checked, not asserted**, all the way from the abstract Guard law to the running Rust the extension calls. **Do this for the transfer/workflow first; generalize after.**

---

## 3. The phase sequence — order, dependencies, critical path

(i) Prelude + concrete-cell instance ──┬──► (ii) catalog instantiation ──┐
   (Spec/Prelude.lean; Value→Kernel)    │      (constraints/effects/auths   │
                                        │       as Spec constructions)      │
                                        │                                   ▼
                                        └──────────────────────────► (iii) Exec rework as
                                                                          FULL Spec refinement
                                                                          (the operational LTS)
                                                                               │
                          (iv) CryptoKernel overhaul (real §8) ─── parallel ───┤
                          (circuit AIR over records)                           │
                                                                               ▼
                                                                       (v) the Rust cascade
                                                                          (turn/cell/coord → FFI)
                                                                               │
                                                                               ▼
                                                                  (vi) first verified application
                                                                       (RDII / transfer loop)

**Phase (i) — Prelude + concrete-cell instance.** *Mechanical-to-moderate.* Factor the shared abstract carriers (`CellId`, `Digest`, `Statement`, `Witness`, `Rights`, `Bal`, `TurnId`) into `Dregg2/Spec/Prelude.lean` — the sketch and the soundness obligations already exist in `Spec/Coherence.lean §7` (the cross-link lemmas `guard_is_authority_conferral`, `conservation_is_hyperedge_cg5`, etc. ARE the proof that the merge is sound). Concurrently, wire `Exec/Value.lean` into `Exec/Kernel.lean`: replace `bal : CellId→ℤ` with a `Value`-record cell-state, re-proving `exec_conserves`/`exec_authorized` over the `balance` field. **Dependency:** none upstream; gates everything. **Risk:** moderate — touching every `Spec.*` module; the `Coherence` bridges de-risk it.

**Phase (ii) — catalog instantiation.** *This is where metaprogramming pays off.* dregg1's ~29 `StateConstraint`s (`cell/src/program.rs:597`), its effect kinds, and its auth kinds become **derived smart-constructors** over the small Spec primitives — NOT a flat 30-variant coproduct port (the explicit anti-goal in `Spec/Guard.lean`: "a flat ~30-variant port is exactly the legacy mistake this layer exists to delete"). Each constraint = a `Spec.Guard` (firstParty or witnessed-behind-the-oracle); each effect = a `Spec.Conservation` `LinearityClass`-typed delta; each auth = a `Spec.Authority` graph op. **Dependency:** (i). **Risk:** mechanical *per item* but voluminous (~29×) — the strongest case for the metaprogramming study generating them.

**Phase (iii) — Exec rework as FULL Spec refinement.** *The hard research core.* Today `ExecRefinement.lean` proves the *static projections* of the square; the OPEN residue (its §4) is the **abstract small-step LTS** `AbsStep : AbstractState → AbstractState → Prop` such that `exec k turn = some k' → AbsStep (absOf k) (absOf k')` (full forward simulation, not projection-preservation). This is the same residue flagged by `Proof/Refine` and `Spec.Authority.only_connectivity_begets_connectivity`'s OPEN (whole-history graph bookkeeping). **Dependency:** (i),(ii) — you can't define the abstract LTS until the cell/catalog shape is fixed. **Risk:** RESEARCH. This is the l4v `Design ⊑ Abstract` operational diagram; it is genuinely hard.

**Phase (iv) — CryptoKernel overhaul (real §8).** *Parallel track, mostly Rust+circuit.* Replace the 4-scalar-ℤ `kernelCircuit` with the real field-AIR over records (the `Value.flatten`/`width` discipline makes this well-defined — `flatten_width` is the foundation lemma), bind `chainOk`→Poseidon digest, and extract `kernelCircuit` to the prover. The Lean side stays an uninterpreted `[CryptoKernel …]` with laws; Rust (`circuit`, `credentials`) discharges. **Dependency:** loosely on (i) (record schema); otherwise parallel. **Risk:** large engineering + the §8 trust boundary (below).

**Phase (v) — the Rust cascade.** *Engineering, oracle-gated.* Per DREGG1-TO-DREGG2 §D: Cascade 1 (instantiate portals in Rust via `@[extern]`), Cascade 2 (retire `turn`'s admissibility/authority/conservation decision into FFI'd `Exec`), Cascade 3 (predicate seam as `Laws.Verifiable`), Cascade 4 (`coord`→`JointTurn`/`Confluence`, REUSE `bilateral_aggregation_air`, binding-as-hypothesis), Cascade 5 (daemon hosts kernel). Each crate graduates by differential-equality to the oracle, then swaps. **Dependency:** (iii) for the soundness-critical parts, (iv) for the portal. **Gating risk:** *step-completeness* — Cascade 2 cannot land until the in-circuit `StepInv = Conservation ∧ Authority ∧ ChainLink ∧ ObsAdvance` is built, because dregg1's auth runs *outside* the proof today (`authorize.rs`). This is risk #1.

**Phase (vi) — first verified application.** The RDII/transfer closed loop from §2.

### The critical path

(i) Prelude+cell ──► (ii) catalog ──► (iii) operational LTS ──► (v.Cascade2) turn-retire ──► (vi) RDII loop

(iv) CryptoKernel and (v.Cascade1) portal-instantiation run **in parallel** and rejoin at (v.Cascade2). **The single longest pole is (iii)** — the operational LTS / full forward-simulation diagram — because every downstream soundness claim (and the coinductive `Boundary.sound_of_step_complete` keystone) depends on it, and it is research, not engineering.

---

## 4. What the four tooling studies must deliver (the framing)

These are the sibling studies this META roadmap frames. Each must produce a *specific artifact* the construction consumes:

**eDSL study** — *the surface for cells/programs.* Must deliver: a concrete syntax for declaring a cell = `(Schema, CellProgram)` over `Exec/Value.lean`'s `Value`, where a program is a guarded transition. **Construction needs:** the input format that Phase (i)/(vi) author cells in, and the *untrusted compiler* (`dregg-dsl`) that lowers DSL → `Value`-schema + `Spec.Guard` gates. It must be honest about the find/verify polarity (`Bool` verify in TCB, `Option` find untrusted). Output: a cell/program surface that compiles to the verified core, content-addressed by `ir_hash`.

**Metaprogramming/tactics study (catalog generation)** — *generate the catalog.* Must deliver: Lean elaborators/macros that emit the ~29 `StateConstraint` smart-constructors of Phase (ii) as `Spec.Guard`/`Spec.Conservation`/`Spec.Authority` derived definitions, each with its coincidence-with-legacy lemma auto-generated. **Construction needs:** Phase (ii) is voluminous-mechanical; without generation it is hand-written 29× and rots. Output: the catalog as *generated* Spec constructions + their refinement obligations stubbed.

**VCG/WP study** — *verify cell programs.* Must deliver: a verification-condition generator / weakest-precondition calculus over `CellProgram` transitions, so that "this program preserves its cell invariant / conserves / stays authorized" reduces to dischargeable VCs. **Construction needs:** Phase (vi) (and every real application) needs per-program proofs, not just per-kernel; the VCG is what makes a *cell program* (not just the kernel) verifiable. Output: `wp(program, postcondition)` and the soundness theorem tying it to `Exec.exec`.

**Tactics study** — *discharge the VCs.* Must deliver: domain tactics (extending `Dregg2/Tactics.lean`) that close the VCs the VCG emits — the conservation `Finset.sum` cancellations, the Guard `admits` Boolean-algebra rewrites, the authority `confers`/`Graph.has` goals. **Construction needs:** without tactics, every catalog item and every cell program is a bespoke manual proof. Output: a tactic library that makes Phase (ii)/(vi) proofs near-automatic.

**CryptoKernel-overhaul study** — *real §8.* Must deliver: the real field-AIR over `Value` records, the `chainOk`→Poseidon binding, the extraction of `kernelCircuit` to the Rust prover, and the property-test suite that exercises `commit_hom`/`hash_inj`/`recv_mono` hard. **Construction needs:** Phase (iv); it discharges the §8 open-obligation bucket #1 that the whole tower cuts out to circuits. Output: a Rust `CryptoKernel` instance whose laws are empirically certified and whose binding is the circuit obligation.

---

## 5. Honest blockers + risks (what's research, what's mechanical, what's hard engineering)

**RESEARCH (genuinely hard — may not close):**
- **The operational LTS / full refinement diagram (Phase iii).** The OPEN in `ExecRefinement.lean §4` and `Proof/Refine`. Static projections are proved; the forward-simulation `AbsStep` is not. This is the longest pole and gates the coinductive `Boundary` keystone. **Highest single risk.**
- **The three-judgement projection split** (I-confluence independent of conservation/ordering; the classifier is NOT the session type — DREGG1-TO-DREGG2 risk #5, `OPEN-PROBLEMS #1`). The Coordination/Projection soundness rests on no paper in the corpus. **Ship `JointTurn` (bilateral) first; treat Coordination as research-grade.**
- **Cross-disjoint-group atomic+live+partition-tolerant commit is a genuine impossibility** (risk #4). Design around it (restrict to I-confluent, or accept blocking+timeout); do not promise to "fix" it.
- The deep coinductive/joint opens already classified as honest open-obligation bucket #2 (cross-cell bisimulation, whole-history non-forgeability closure, Byzantine quorum-intersection, GST-liveness) — these need the adversary/GST model.

**HARD ENGINEERING (tractable but real):**
- **The §8 discharge** (Phase iv): real AIR over records, Poseidon binding, prover extraction. `Value.flatten_width` makes it *well-defined*; building it is large.
- **The Rust trust boundary.** Lean→C linking into a Rust crypto host at scale is unproven beyond the scalar PoC (risk #2). Real turns carry `Digest`/`Proof`/`Finset` state; marshalling must not become an unverified TCB. The differential harness is *empirical, not certification* (risk #3) — a non-lawful Rust impl silently makes parametric Lean theorems vacuous.
- **Step-completeness in dregg1 is unverified and probably false today** (risk #1, the gating risk): auth runs outside the proof (`authorize.rs`), PI surface lacks `AUTH_ROOT`/`CONSERVATION_VECTOR`/`CONSTRAINT_MANIFEST_HASH`. Under coinduction a step-incomplete proof permits a drifting future — *nothing downstream is sound*. Phase 0 audit gates Cascade 2.

**MECHANICAL (bounded work, de-risked by tools):**
- The `Spec/Prelude` factoring (Phase i) — the `Coherence §7` bridges already prove it sound.
- The catalog instantiation (Phase ii) — voluminous but each item is a smart-constructor; the metaprogramming study removes the toil.
- The FFI surface generalization beyond scalars — engineering, bounded.

---

## Recommended first-90-days sequence

**Days 1–30 — found the concrete substrate + audit the gate.**
1. Factor `Dregg2/Spec/Prelude.lean` from the `Coherence §7` sketch (the soundness obligations are already proved cross-links). Make every `Spec.*` module import it.
2. Wire `Exec/Value.lean` into `Exec/Kernel.lean`: cell-state becomes a `Value` record; re-prove `exec_conserves`/`exec_authorized` over the `balance` field.
3. **In parallel, run the Phase-0 step-completeness audit** on dregg1's `turn`/`authorize.rs` (is auth in-proof? is the PI surface complete?). This verdict gates the whole cascade — do it now, cheaply, before committing the rest.

**Days 31–60 — the catalog + the first refinement extension.**
4. Stand up the metaprogramming + tactics tooling enough to generate the first slice of the catalog (Phase ii) as `Spec.Guard`/`Conservation`/`Authority` smart-constructors.
5. Extend `ExecRefinement.lean` from the toy transfer to the **workflow/transfer gate** — refine `Protocol/Workflow.lean`'s `exec_authorized`/`exec_in_order` onto `Spec.Guard` instances. This is the Spec-side of the first verified application.

**Days 61–90 — the first closed loop, narrow.**
6. Generalize the FFI surface past scalars to the workflow's cell-state (the `Value`-marshalling), keeping it differential-gated against the oracle.
7. Drive the **RDII/transfer closed loop** (§2) end-to-end on the smallest surface: `node`/`extension` calls the FFI-hosted kernel for the authorization decision; the harness certifies native ≡ oracle; the §8 attestation is a `CryptoKernel.verify` stub.
8. Begin the operational-LTS research (Phase iii) as a parallel long-pole track — it will not finish in 90 days, but it must *start*, because it gates everything downstream.

## The single highest-leverage next move

**Wire `Exec/Value.lean` into `Exec/Kernel.lean` and re-prove the two kernel laws over the record cell-state (Phase i, concrete-instance).** Rationale: it is the *one* move that unblocks the most. It converts the toy `bal : CellId→ℤ` into the real content-addressed cell — which (a) every later phase depends on (catalog, LTS, cascade, application all need the concrete cell), (b) is the prerequisite the `Value.lean` foundation was *built for* but never connected to, (c) is mechanical-to-moderate (the laws are already proved over ℤ; lifting them to the `balance` field of a record is a localized re-proof aided by `flatten_width`), and (d) immediately makes the FFI beachhead carry *real* dregg cell-state rather than two scalars — turning the 10k/10k differential from a scalar PoC into the actual migration ratchet. It is the smallest change with the largest unblocking radius, and it is the literal seam between "verified micro-core" and "verified dregg."

---

### Critical Files for Implementation
- `/Users/ember/dev/breadstuffs/metatheory/Dregg2/Exec/Kernel.lean` — the toy `KernelState`/`exec` to be lifted to the `Value` cell (Phase i).
- `/Users/ember/dev/breadstuffs/metatheory/Dregg2/Exec/Value.lean` — the content-addressed record substrate to wire in (the concrete-cell instance, `flatten_width` foundation).
- `/Users/ember/dev/breadstuffs/metatheory/Dregg2/Spec/ExecRefinement.lean` — the `Exec ⊑ Spec` beachhead; §4 holds the operational-LTS OPEN that is the critical-path long pole (Phase iii).
- `/Users/ember/dev/breadstuffs/metatheory/Dregg2/Spec/Coherence.lean` — §7 sketches `Spec/Prelude.lean` and proves the carrier-merge sound (Phase i Prelude).
- `/Users/ember/dev/breadstuffs/metatheory/Dregg2/Exec/FFI.lean` + `/Users/ember/dev/breadstuffs/dregg-lean-ffi/` — the Lean→Rust beachhead + golden-oracle differential to generalize past scalars (Phase v ratchet).
