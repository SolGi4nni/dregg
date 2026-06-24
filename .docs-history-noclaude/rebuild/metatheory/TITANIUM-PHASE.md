# THE TITANIUM PHASE — one description, one theory, one trust base

*v2. v1 made two mistakes: it organized around **features** (six parallel "ribs") instead of around
**structure**, and it buried the actual blocker — dregg carries **too many descriptions of itself**
(five proof stacks, two circuit descriptions, two executors, a neglected DSL, narration cruft), and every
duplication is a place the proofs might be about the **wrong artifact**. Titanium is not "more proofs." It is:*

> **Collapse the system to ONE canonical description; build ONE theory the guarantees fall out of; and end at
> ONE theorem — *under a minimal, named, machine-audited trust base, the dregg protocol, across any topology,
> against an f<n/3 adversary, UC-realizes an ideal sovereign capability-ledger; and nothing outside that trust
> base is trusted.* **

Structure: **Phase 0 Coherence** (one of everything) → **Phase 1 The Fibration** (the unifying theory) →
**Phase 2 The Ribs as fibres** → **Phase 3 The Crown** (UC + the minimal-TCB theorem) → **Phase 4 The Stack**
(verified language, down to seL4, out to light clients and the grassroots).

---

## PHASE 0 · COHERENCE — there is exactly ONE of everything

*The most neglected and most foundational phase. Duplication is not mess-as-aesthetics; it is mess-as-unsoundness
(a proof about a circuit you don't run proves nothing) and mess-as-paralysis (every subagent re-derives which
of the N descriptions is real). Nothing above Phase 0 is trustworthy until Phase 0 holds.*

- **0.1 · ONE proof system.** Five stacks today (bespoke `stark.rs` hand-rolled FRI; `p3-uni-stark`/`-fri`/
  `-batch-stark`; `p3-poseidon2-circuit-air`; the `plonky3-recursion` fork; a leftover kimchi/pickles Pasta
  verifier `poseidon_stark_verifier_circuit`). **Decision (validated by running the code): Plonky3 on
  BabyBear/Poseidon2.** *Delete* `stark.rs`, the kimchi/pickles/Pasta path, and any other prover/verifier. One
  audited prover, one audited verifier. (The in-flight `stark.rs`→p3 migration is step one of this.)
- **0.2 · ONE circuit description (source = Lean).** The Lean circuit *descriptors* are the **single source of
  truth**; the Rust prover runs the circuit *extracted* from them (`lean_descriptor_air`, made efficient +
  covering the hash layer via `p3-poseidon2-circuit-air`). **Delete `effect_vm` and every bespoke hand-written
  AIR.** Theorem to keep: *the circuit we prove sound is byte-identical to the circuit the prover runs.* Without
  this, every soundness theorem in the repo is potentially vacuous.
- **0.3 · ONE executor (finish the swap).** Today the Lean executor can *veto* on the commit path (the beachhead)
  but the Rust `apply.rs` still *produces* the state. Complete it: the verified Lean executor is the **state
  producer**; `apply.rs` is demoted to a differential check (kernel-vs-Rust, never the reverse). Project the last
  GAP effect; the differential goes to 0 GAP. One executor, and it's the verified one.
- **0.4 · ONE authoring language.** The neglected `dregg-dsl` either becomes *the* verified high-level language
  for cells/contracts — compiling to the one circuit, with a **compiler-correctness theorem** (source semantics
  ⟹ circuit semantics) — or it is deleted and the single real authoring path is named. No half-maintained DSL.
- **0.5 · ONE assumption set, ZERO narration.** The trust base is a single, explicit, machine-checked list (§
  Crown). And purge the cruft: the comments that *narrate* "we don't use open holes / no lurking holes" are deleted —
  the discipline lives in `#assert_axioms`, not in prose about it, and the prose poisons every open-hole grep.
- **0.6 · ONE CI gate.** A single matrix that fails a PR on: Lean not axiom-clean, Rust tests red, Isabelle
  (`isabelle build`) red, the `DREGG_LEAN_SHADOW_STRICT=1` differential diverging, *or* an open-hole grep hit that
  isn't a registered open front. Coherence is enforced, not aspired to.

**Milestone 0 (the gate to everything else):** the repo contains exactly one prover, one circuit source, one
commit-path executor, one authoring language, one assumption list; the open-hole grep returns only registered
fronts; and the single CI matrix is green.

---

## PHASE 1 · THE FIBRATION — the distributed-adversarial semantics as one indexed structure

*v1's "ribs" are not independent; they are **fibres of one structure**. This is the real intellectual core, and
it's novel: parametrized verification of a distributed system as a fibration.*

- **The base.** `B = Topology × FaultModel × CryptoStrength` — the space of deployment conditions. A point is
  e.g. `(single-machine, no-faults, ideal-crypto)` … up to `(global-mesh, f<n/3 Byzantine, computational-crypto)`.
- **The fibres.** Over each `b ∈ B` sits the system's *guarantee* at that deployment: conservation, attenuation,
  revocation-latency, confinement, finality, privacy — *as they actually hold there.*
- **The terminal fibre = today's proofs.** Over `(single-machine, honest, ideal)` the fibre is the strong local
  property we already proved — `lift_collapse` is *definitional*, not a new theorem.
- **The reindexing functor `lift`.** Moving to a weaker base point reindexes the fibre to its bounded form, with
  a **tight** bound (the revocation prototype is the first instance; generalize `lift` to the functor, then
  re-derive conservation/attenuation/finality as instances — proving the structure is real, not a metaphor).
- **The global section = the protocol's promise.** A *coherent choice of fibre over all of `B`* is exactly "the
  protocol behaves correctly at every deployment"; the **UC realization (Phase 3) is the global section**, and
  Phase 0's coherence is what lets the section be *single-valued* (one description ⇒ one section).
- **The single-machine principle, formalized as the fibration's geometry:** the strong props live at the apex of
  `B`; distribution and adversity move *down*; every guarantee is the apex property *transported* by `lift` and
  *weakened by a measured amount*. "Distributed bounds the single-machine ideal" becomes a theorem about
  reindexing, not a slogan.

**Milestone 1:** `Dregg2/Distributed/Fibration.lean` — `B`, the fibre, `lift`, `lift_collapse`, and three
properties (conservation, attenuation, revocation) realized as fibres through the *same* functor.

---

## PHASE 2 · THE RIBS, as fibres of Phase 1

Each is now "compute the fibre of property P over the real base point and prove the bound tight" — a real
multi-week proof, but *organized* by the fibration, not invented separately.

- **2.1 Consensus (the long pole).** Formalize the blocklace + `tau`-ordering; prove **agreement** (no two honest
  finalized orders conflict, via quorum intersection at `f<n/3`), **equivocation-exclusion** (double-signing is
  self-incriminating evidence in the blocklace ⇒ excludable), and **post-GST liveness**. `ConsensusExec.lean`
  (finalized-order→executor, `no_conflicting_finalized_state`) is the seam; finish the consensus core under it.
- **2.2 Distributed revocation (generalized).** Delegation-chain revocation (transitive, bounded by chain-length
  × per-hop) and the finality interaction (`enforced ⇔ final ∧ propagated`) — lifted, composed with 2.1.
- **2.3 Information flow → non-interference.** Unify the field-classification and capability axes; **the
  disclosure dial *is* the security lattice.** Prove non-interference for the protected fragment; give the covert
  channels (timing, turn-existence, fee/ordering) an explicit *bounded* taxonomy + mitigation. "Private
  computation = non-interference up to this named, bounded channel set."
- **2.4 Metadata privacy (strengthened).** Private joint turns (participant-anonymous aggregation), coordination-
  graph hiding (proven anonymity-set bound), timing/volume cover-traffic indistinguishability.
- **2.5 Economics / DoS.** A resource-accounting + mechanism model: spam-deterrence (`fee ≥ marginal junk cost ⇒
  honest work bounded by fees`), incentive-compatibility of 50/30/burn, griefing-unprofitability. Sound ≠
  live-under-economic-attack; this closes that.

---

## PHASE 3 · THE CROWN — UC realization + the minimal trust base

- **3.1 `dregg ⊑_UC F_dregg`.** Construct the simulator (faking the real transcript from `F_dregg`'s leakage via
  STARK-ZK + Pedersen-hiding); the hybrid argument (each step bounded by one carrier's advantage); UC composition
  glues the sub-functionalities the Phase-2 ribs realize. The `F_dregg` scaffold + carrier games exist; close the
  reduction. (Needs Isabelle CI from Phase 0.6.)
- **3.2 THE MINIMAL-TRUST-BASE THEOREM (the apex — the "retire trust" statement made formal).** State the trust
  base *as a set* — `TCB = { the seL4 kernel (Phase 4), the audited Plonky3 verifier, the four crypto carriers,
  the f<n/3 + GST model }` — and prove that **the system's security depends on TCB and nothing else**: every
  other component is either proven correct or eliminated by Phase 0. This is the whole point — not "the parts are
  sound," but *"here is exactly what you trust, it is short, and it is all you trust."*

---

## PHASE 4 · THE STACK — down to the metal, out to the world

- **4.1 The DSL as a verified language** (from 0.4): writing an app = writing verified code; the compiler-
  correctness theorem makes the app's safety a corollary of the source.
- **4.2 Light clients + succinctness.** Gold recursion ⇒ an O(1)-to-verify proof of the *whole finalized state*
  ⇒ a phone verifies `(head, state-query)` without the chain. Prove light-client soundness. (Succinctness becomes
  a *proven* property, not a hope.)
- **4.3 The grassroots sovereignty spectrum, as a theorem.** dregg is Shapiro-grassroots; prove the continuum —
  `single-machine ↔ federated ↔ global` is a *path through the fibration's base* `B`, with the guarantee at each
  point computed by `lift` and the economics (2.5) making it self-sustaining. "Your phone is a node" becomes a
  theorem about a base point, not marketing.
- **4.4 The whole stack: seL4/Robigalia.** dregg as a *verified userspace on a verified microkernel.* Each phase
  shrinks the TCB until 3.2's set is `{ seL4, the verifier, the crypto, the fault model }` — the trust chain
  proven from hardware up. The endgame the README has always pointed at.

---

## The apex theorem (what all of it composes to)

```
Theorem (Titanium):
  Assume TCB = { seL4 correctness, Plonky3-verifier soundness,
                 Poseidon2-CR, ed25519-EUF-CMA, STARK-extractability, DLog-binding,
                 f < n/3 Byzantine, partial-synchrony-with-GST }.
  Then for every base point b ∈ B (topology × faults × crypto), the dregg protocol
  realizes  lift(F_dregg, b)  — an ideal sovereign capability-ledger that is
  conservation-sound, attenuation-sound, revoking-within-bound(b), confined-up-to-Channels,
  metadata-private-up-to-the-graph, and economically-DoS-bounded —
  and no component outside TCB is trusted.
```

## Sequencing & critical path
```
PHASE 0 COHERENCE  ──(gate)──►  PHASE 1 FIBRATION ──► PHASE 2 ribs ──► PHASE 3 CROWN ──► PHASE 4 STACK
   │ (one prover/circuit/executor/DSL/assumptions; Isabelle CI; purge narration)
   └─ consensus core (2.1) starts in parallel immediately — it's the long pole and gates the crown.
```
- **Phase 0 is the gate.** Do it first and completely; the rest is unsound or confusing without it.
- **Critical path = Phase 0 → 2.1 consensus → 3.1 UC.** Start consensus the moment Phase 0's coherence lands.
- The fibration (Phase 1) is cheap to stand up and makes every rib an instance; do it right after 0.

## Success criteria (Titanium, not token)
1. `grep -r` finds **one** prover, **one** circuit source, **one** commit-path executor — the deletions are done.
2. The apex theorem is **stated**, its hypotheses are **exactly** the TCB set, and the minimal-TCB theorem (3.2)
   proves nothing else is trusted.
3. Every rib is a **fibre through the one `lift` functor**, machine-checked, with both a non-vacuity *and* a
   negative tooth (boundary proven both directions).
4. Lean axiom-clean **and** Isabelle `isabelle build` green **and** the strict differential 0-GAP — all in one CI.
5. The TCB shrinks monotonically across phases toward `{ seL4, verifier, crypto, fault-model }`.

## Honest risks
- **Consensus liveness** may need new technique (highest-risk, longest).
- **The UC simulator** is research-grade; the reduction is the hard part.
- **The two-prover (Lean↔CryptHOL) seam** is a permanent trust edge unless mechanized — treat transport fidelity
  as a first-class artifact.
- **Phase 0 is unglamorous and will be tempting to skip** — it is the foundation; skipping it is how the mess
  regrew the last three times.
