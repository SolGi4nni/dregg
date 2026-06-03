# External Lean 4 Reference Libraries — dregg2 Formal Methods Push

*Research date: 2026-06-02. Covers all five requested topic areas.*

---

## QUICK VERDICT TABLE

| Topic | Best Candidate | Recommendation |
|---|---|---|
| Temporal logic (CTL, CTL*, μ-calculus) | **Nothing exists** for branching-time; LeanLTL for LTL variants | BUILD-OURSELVES (μ-calc / CTL) on mathlib fixpoints; ADOPT LeanLTL for LTL |
| Info-flow / noninterference | Nothing ready in Lean 4 | BUILD-OURSELVES on mathlib lattices |
| Coalgebra / bisimulation / HML | **CSLib** (leanprover/cslib) | ADOPT — HML + bisimulation proven; mu-calc extension deferred but base is there |
| Cryptography (commitments, ZK, game-based) | **VCVio** (dtumad/VCV-io) | ADOPT with eyes open — Apache-2, mathlib-based, sorry-free per paper |
| Liveness / fairness / distributed | **Lentil** (verse-lab/Lentil) for TLA; manual for GST | ADOPT Lentil as scaffold; BUILD-OURSELVES for GST/fairness quantifiers |

---

## 1. TEMPORAL LOGIC (CTL, CTL*, μ-calculus, LTL)

### 1a. LeanLTL — *ADOPT for linear-time only*

- **URL:** <https://github.com/UCSCFormalMethods/LeanLTL>
- **Paper:** arXiv 2507.01780 / ITP 2025 supplementary  
- **License:** CC BY 4.0 (paper); repo license not determined from remote content — check before importing
- **Lean version:** Lean 4 (specific toolchain undetermined without local checkout)
- **What it gives us:** A unifying framework for all *linear-time* temporal logic variants — standard LTL (infinite traces), LTLf (finite traces), and their embeddings into a common trace-based semantics. Allows mixing arbitrary Lean expressions with temporal operators. Proves standard flavors of LTL embed into the framework. Provides automation hooking into Lean's existing tactics. Published at ITP 2025, so peer-reviewed.
- **TCB verdict:** Paper makes no mention of `sorry` or oracle backends. Automation uses Lean tactics (no SMT/Z3 calls). Appears clean. Verify with `#check_axioms` before shipping.
- **Gap:** Strictly linear-time. No CTL, CTL*, or μ-calculus. Cannot reason about branching paths, greatest-fixpoint safety + liveness interleaving, or alternating-time properties.

---

### 1b. mrigankpawagi/LeanearTemporalLogic — *AVOID (incomplete, pre-library)*

- **URL:** <https://github.com/mrigankpawagi/LeanearTemporalLogic>
- **License:** Not stated
- **What it gives us:** A standalone LTL formalization for Lean 4 (syntax, semantics, transition systems, lemmas). Author notes "work in progress, not ready for use as a dependency." Superseded by LeanLTL in scope and polish.
- **TCB verdict:** Unknown — README warns of WIP status.
- **Recommendation:** AVOID; use LeanLTL instead.

---

### 1c. CTL / CTL* / Modal μ-calculus — *BUILD-OURSELVES*

No Lean 4 library for CTL, CTL*, or the modal μ-calculus exists as of June 2026. The closest in any proof assistant is a Coq gist from 2009 (qnighy/ad136d01) for propositional μ-calculus — not portable without serious effort.

**Build-on:** mathlib's `Mathlib.Order.FixedPoints` (Knaster-Tarski theorem, `lfp`/`gfp` for complete lattices, Kleene iteration, Park induction). Lean 4.20+'s new `greatest_fixpoint`/`least_fixpoint`/`coinductive` tactic-level support generates Park-induction principles and is directly usable to define `νX.φ` / `μX.φ` over transition systems.

**The μ-calculus path:** Define a Kripke frame (transition system), interpret modal operators as monotone endofunctions on `Set State`, then `lfp`/`gfp` from `Mathlib.Order.FixedPoints` gives both the semantics and the Knaster-Tarski–powered induction/coinduction principles. CTL operators `EF`, `EG`, `AF`, `AG` are just specific lfp/gfp instances. We already vendor Paco (hxrts/paco-lean) for parameterized coinduction, which composes with this.

---

### 1d. Lentil — TLA-style temporal reasoning for distributed specs

*(Also discussed under §5 — referenced here for temporal completeness)*

- **URL:** <https://github.com/verse-lab/Lentil>
- Provides Lamport's Temporal Logic of Actions formalized in Lean 4 (ported from coq-tla). Useful for action-labeled transition systems and safety/liveness in a concurrent-system idiom. Not CTL/μ-calculus, but covers the "□" / "◇" and action-enabled fragments relevant to fairness.

---

## 2. INFORMATION-FLOW / NONINTERFERENCE / CONFIDENTIALITY

### 2a. No ready Lean 4 library exists — *BUILD-OURSELVES*

**Complete negative result.** As of June 2026, there is no Lean 4 formalization of:
- Denning-style security lattices / noninterference
- IFC type systems (Volpano-Smith-Irvine or stronger)
- Bell-LaPadula / Biba
- Declassification / endorsement policies
- Gradual/probabilistic noninterference

The only nearby work:
- **denismazzucato/noninterference-lean** — Lean 3, leanpkg-based, incomplete (Lemmas 6.5–6.8 admitted), formally dead.
- **seL4/l4v proof/infoflow** — Isabelle/HOL, not Lean 4. Establishes noninterference for seL4 kernel, well-regarded, but no Lean port path is short.
- **Mechanized Noninterference for Gradual Security** (arXiv 2211.15745) — mechanized in Agda, not Lean 4.
- **Sheaf semantics of TINI** (arXiv 2204.09421) — Agda. Conceptually interesting (sheaf model of termination-insensitive NI) but no Lean port.

**Build-on:** mathlib's `Mathlib.Order.Lattice` (for the security lattice), `Mathlib.Data.Rel` (for dependency / information-flow relations), plus our existing cell-permission lattice in `Authority.lean`. The Volpano-Smith type-system proof is the canonical "first formalization" target — it is ~6 semantic lemmas over a simple While language, well within reach in one sprint.

---

## 3. COALGEBRA / BISIMULATION / MODAL LOGIC / PROCESS CALCULI

### 3a. CSLib (leanprover/cslib) — *ADOPT — PRIMARY recommendation*

- **URL:** <https://github.com/leanprover/cslib>
- **License:** Apache-2.0
- **Lean version:** Checked with Lean 4.28.0-rc1 (Feb 2026 papers)
- **What it gives us:** CSLib is the official Lean Computer Science Library, maintained under leanprover. Relevant modules:
  - `Cslib/Languages/CCS/` — Milner's CCS formalized, bisimilarity proved a congruence
  - `Cslib/Logics/HML/` — Hennessy-Milner Logic: syntax, satisfaction, denotational semantics, **Hennessy-Milner theorem** (bisimilarity = HML-equivalence for image-finite LTS)
  - `Cslib/Logics/Modal/` — modal logic module (details require local checkout)
  - General LTS infrastructure: labelled transition systems, bisimulation, weak bisimulation, simulation, trace equivalence
- **TCB verdict:** February 2026 paper (arXiv 2602.15409) explicitly states no `sorry` and no custom axioms. Proofs use `grind` tactic. CLEAN.
- **Note on HML paper (arXiv 2602.15409):** Three major theorems proved sorry-free: (1) satisfaction ≡ denotational semantics, (2) bisimulation invariance, (3) Hennessy-Milner theorem. Mu-calculus / CTL extensions are called out as future work.
- **Gap:** No μ-calculus, no CTL, no temporal operators yet. What exists is the ideal *substrate* for those extensions.

---

### 3b. mathlib4 QPF / Cofix — *ADOPT as substrate for coinductive types*

- **URL:** <https://github.com/leanprover-community/mathlib4> — `Mathlib.Data.QPF`
- **License:** Apache-2.0
- **What it gives us:** Quotients of Polynomial Functors: final coalgebra (`Cofix`) over any QPF-functor, with bisimulation principles (`Cofix.bisim`, `Cofix.bisim_rel`, `Cofix.bisim'`). The bisimulation principle directly proves coinductive equality from a bisimulation relation. This is the mathlib-resident path to coinductive process types.
- **TCB verdict:** Mathlib; no external axioms beyond the standard Lean kernel.

---

### 3c. Lean 4.20 `coinductive` / `greatest_fixpoint` — *ADOPT (built-in)*

- Lean 4.20.0 (released 2025-06-02) added `greatest_fixpoint`/`least_fixpoint` clauses for recursive Prop-valued functions, generating **Park induction principles** automatically. This is kernel-level, no external library needed, and interacts cleanly with `Mathlib.Order.FixedPoints`. Use for any bisimulation or μ-calculus proposition.

---

### 3d. FormalizedFormalLogic/Foundation — *AVOID (wrong scope)*

- **URL:** <https://github.com/FormalizedFormalLogic/Foundation>
- License: Apache-2.0. Covers classical/intuitionistic propositional and first-order logic, superintuitionistic modal logics (GL, S4-class), Kripke semantics, completeness. Does NOT cover Hennessy-Milner, bisimulation, CTL, LTL, or process calculi. Good for proof-theory / Gödel-style results, not for verification modal logics.

---

### 3e. m4lvin/lean4-pdl — *ADOPT if PDL becomes relevant*

- **URL:** <https://github.com/m4lvin/lean4-pdl>  
- License: Apache-2.0. Lean 4. Propositional Dynamic Logic with Craig interpolation. Tableau-based, sorry-free per README badge. PDL subsumes basic modal logic and is related to CTL (tree-shaped paths). Not directly CTL or μ-calculus, but the tableau machinery is reusable. Import if we need PDL-based access-control modalities.

---

## 4. CRYPTOGRAPHY IN LEAN 4

### 4a. VCVio / VCV-io — *ADOPT — PRIMARY recommendation*

- **URL:** <https://github.com/Verified-zkEVM/VCV-io> (also: `@dtumad/VCVio` on Lean Reservoir)
- **Paper:** IACR ePrint 2026/899 (*VCVio: Verified Cryptography in Lean via Oracle Effects and Handlers*)  
- **License:** Apache-2.0
- **Lean version:** v4.22.0 – v4.29.0 (actively maintained as of June 2026)
- **Mathlib:** Yes, foundational dependency
- **What it gives us:** A complete foundational framework for game-based cryptographic proofs in Lean 4, inspired by FCF (Coq). Key features:
  - `OracleComp` monad for oracle computations with denotational probability semantics
  - Relational and unary program logic with interactive tactics for stepping through games
  - Oracle handlers: caching, logging, reprogramming, seed pre-sampling
  - Rewinding via deterministic transcript replay (no rewindability axioms)
  - **Proved:** Bellare-Neven forking lemma (first mechanized without rewindability axioms), EUF-CMA security for Schnorr signatures, random-oracle commitment scheme
  - Sigma protocols, Fiat-Shamir, Fischlin transforms
  - LatticeCrypto submodule: ML-DSA (Dilithium), ML-KEM (Kyber), Falcon
  - Probability theory and complexity based on / compatible with mathlib
- **TCB verdict:** Paper states "fully foundational proofs." No mention of sorry, external SMT, or oracle backends. The framework explicitly avoids the rewindability axioms that prior EasyCrypt formalizations required. Check `#check_axioms` on key theorems before shipping. LIKELY CLEAN.
- **Gap:** No AEAD formalization. No Merkle tree proofs. No general STARK/FRI argument.

---

### 4b. CatCrypt — *WATCH but NOT YET ADOPTABLE*

- **URL:** Not publicly available as of submission (June 2026 paper, IACR 2026/604)
- **Paper:** *CatCrypt: From Rust to Cryptographic Security in Lean* (Bas Spitters, Aarhus)
- **What it gives us (when available):** SSProve-style state-separating proofs ported to Lean 4; end-to-end Rust-to-Lean pipeline via Hax; 172 protocols formalized; 110 with full pipeline.
- **TCB concern:** Developed primarily by GenAI with human direction over ~2 months. While "human direction, design and review" is claimed, the velocity (172 protocols in 2 months) warrants extra `#check_axioms` scrutiny before adopting. Repo not yet public.
- **Recommendation:** WATCH — when repo is released, audit for `sorry` and axiom hygiene before importing.

---

### 4c. SymbolicCryptographyLean (ravst) — *ADOPT for symbolic-to-computational bridge*

- **URL:** <https://github.com/ravst/SymbolicCryptographyLean>
- **License:** MIT (with Apache-2.0 for VCVio subdir)
- **What it gives us:** Formalized computational soundness theorem (symbolic indistinguishability → computational indistinguishability) and verified symbolic security of garbled circuits. Builds on VCVio. Accepted to CSF 2026. Useful if we want to reason about our protocol's symbolic security and lift to computational.
- **TCB verdict:** Builds on VCVio (clean), paper in peer review at CSF 2026. No `sorry` mentioned. Depends on VCVio as oracle substrate.

---

### 4d. risc0/risc0-lean4 — *AVOID (research artifact, WIP)*

- **URL:** <https://github.com/risc0/risc0-lean4>
- License: Apache-2.0. Formalizes SHA2-256, Merkle trees, Baby Bear field, NTT, FRI verification. BUT: README says "research artifacts, should not be used for any purpose." No sorry audit. Trailing the main RISC Zero codebase.
- **Note:** Merkle tree formalization here is the closest thing to a Lean 4 Merkle proof we found, but the WIP status is a blocker. Useful as reference for our own build.

---

### 4e. zkcrypto/cryptolib — *SUPPLEMENTARY (limited scope)*

- **URL:** <https://github.com/zkcrypto/cryptolib>
- **License:** Apache-2.0 / MIT dual
- **What it gives us:** Formal correctness and semantic security proofs for ElGamal, RSA, OTP, stream/block ciphers, DDH assumption. Limited scope (no ZK, no commitments, no Merkle, no AEAD). Less powerful than VCVio for our purposes.

---

### 4f. What is MISSING in Lean 4 cryptography

- No formalized **AEAD** (AES-GCM, ChaCha-Poly) with IND-CCA proofs
- No formalized **Merkle tree / vector commitment** with opening-binding
- No formalized **STARK / FRI** argument (risc0-lean4 has fragments, WIP)
- No formalized **Pedersen / KZG / inner-product commitments**
- No Lean analog of **CryptHOL** (Isabelle) in full generality — VCVio is the closest

---

## 5. LIVENESS / FAIRNESS / DISTRIBUTED-SYSTEMS VERIFICATION

### 5a. Lentil (verse-lab) — *ADOPT as TLA scaffold*

- **URL:** <https://github.com/verse-lab/Lentil>
- **License:** Apache-2.0
- **Lean version:** Lean 4 (100% Lean, 83 commits as of mid-2026)
- **What it gives us:** Temporal Logic of Actions (TLA/Lamport) formalized in Lean 4, ported from coq-tla. Provides `□` (always), `◇` (eventually), action-enabled predicates, and compositional specs for concurrent/distributed systems. The verse-lab group uses it as scaffolding for their Veil framework (see below). Enables writing distributed protocol specs in a style directly translatable to/from TLA+.
- **TCB verdict:** No explicit sorry disclosure; repo is small (21 stars) and primarily infrastructure. The verse-lab group is active in verification research (published Rabia, Stellar, Suzuki-Kasami proofs in Veil).
- **Gap:** No fairness quantifiers (weak/strong fairness) documented. No GST model. Partial TLA, not TLA+.

---

### 5b. Veil (verse-lab) — *AVOID for liveness (SMT-laundering); USEFUL for safety prototyping*

- **URL:** <https://github.com/verse-lab/veil>
- **License:** Apache-2.0
- **What it gives us:** A verification framework for safety (and future liveness) of distributed protocols, embedding decidable FOL fragments for push-button verification. Case studies: Rabia, Stellar Consensus, Suzuki-Kasami. Actively developed.
- **TCB verdict:** **AVOID for TCB-clean proofs.** Veil uses **z3 and cvc5** as external SMT oracles for automated reasoning. Proofs discharged by SMT calls would introduce external oracle trust into our TCB — exactly what our standing rule forbids. The framework is useful for exploratory work and invariant discovery, but any proof imported from Veil that relied on z3/cvc5 would need to be re-proved in pure Lean.
- **Use as:** Rapid safety-invariant discovery tool only; do not import proofs.

---

### 5c. EPFD blog example (protocols-made-fun.com, June 2025) — *REFERENCE only*

An independently-written Lean 4 proof of strong completeness for an Eventually Perfect Failure Detector (EPFD) under partial synchrony (GST model, message delay bound, clock non-zenoness). ~1000 lines across 13 lemmas. Uses first-order `∀/∃` over natural-number time indices rather than modal operators (author notes TLA+ equivalents). Shows the GST model is encodeable directly in Lean without a library. Not a library — a reference proof showing feasibility.

---

### 5d. Shipwright (MIT CSAIL) — *AVOID (Dafny, not Lean 4)*

arXiv 2507.14080. Impressive liveness + Byzantine fault tolerance framework for distributed protocols (PBFT case study). But implemented in **Dafny**, not Lean 4. No port path.

---

### 5e. LeanLTL fairness encodings

LeanLTL (§1a) can encode weak/strong fairness as LTL formulas (□◇enabled → □◇taken). Since liveness over infinite traces is the core use case of distributed protocol verification, LeanLTL is a clean mathlib-compatible substrate for fairness-indexed properties — without needing an external library.

---

### 5f. What is MISSING in Lean 4 distributed verification

- No Lean 4 library with a formalized GST model + proved partial-synchrony theorems
- No mechanized FLP impossibility proof in Lean 4
- No Lean 4 formalization of Cordial Miners / DAG-based consensus (our dregg1 protocol)
- Liveness under Byzantine faults + fairness in pure Lean (no SMT) = BUILD-OURSELVES

---

## 6. MATHLIB FOUNDATION PRIMITIVES (cross-cutting)

These mathlib modules are the *build-on* substrate for anything we construct ourselves:

| Module | What it provides | Use for |
|---|---|---|
| `Mathlib.Order.FixedPoints` | Knaster-Tarski, `lfp`/`gfp`, Kleene iteration, Park induction | μ-calculus semantics, CTL operators |
| `Mathlib.Data.QPF.Univariate.Basic` | Final coalgebra `Cofix`, bisimulation principles | Coinductive process types |
| `Mathlib.Order.Lattice` / `CompleteLattice` | Complete lattice, `sSup`/`sInf` | Security lattices, IFC |
| `Mathlib.Data.Rel` | Binary relations, composition, closures | Transition systems, noninterference |
| `Mathlib.Probability.*` | Probability distributions over `MeasurableSpace` | Cryptographic game reductions |
| Lean 4.20+ `coinductive` keyword | Park-induction principles, coinductive predicates | Bisimulation, liveness properties |

---

## 7. TCB HYGIENE SUMMARY

**CLEAN (adopt without asterisk):**
- CSLib (leanprover/cslib) — sorry-free per Feb 2026 paper, Apache-2
- mathlib4 QPF/FixedPoints — mathlib standard
- VCVio — "fully foundational," no rewindability axioms, Apache-2

**LIKELY CLEAN (verify before shipping):**
- LeanLTL (UCSCFormalMethods) — ITP-2025 peer reviewed, no mentions of sorry; run `#check_axioms`
- Lentil (verse-lab) — small, active; run `#check_axioms`
- SymbolicCryptographyLean — depends on VCVio; CSF-2026 peer reviewed

**AVOID (TCB concern):**
- Veil — z3/cvc5 SMT oracle backend for proof obligations
- Ix (argumentcomputer) — pre-alpha, explicit ZK-laundering of Lean typecheck into SNARKs, not an axiom-clean proof library
- risc0-lean4 — "research artifact, should not be used"

**AVOID (wrong language / dead):**
- denismazzucato/noninterference-lean — Lean 3, incomplete
- mrigankpawagi/LeanearTemporalLogic — WIP, superseded by LeanLTL

**WATCH:**
- CatCrypt — AI-generated body, not yet public; audit when released

---

## 8. ADOPTION PRIORITIES

1. **Immediate:** Add CSLib as a lakefile dependency for the LTS / bisimulation / HML foundation. This gives us the coalgebra substrate for our cell transition systems.

2. **Immediate:** Add VCVio for game-based crypto. Covers our commitment, sigma-protocol, and signing needs.

3. **Adopt LeanLTL** for any LTL safety/liveness spec on traces (e.g., "the nullifier set grows monotonically forever" can be stated as an LTL safety formula).

4. **Build μ-calculus / CTL** over `Mathlib.Order.FixedPoints` + Lean 4.20 `greatest_fixpoint`. No external library needed — the substrate is already there.

5. **Build noninterference** (Volpano-Smith style) ourselves on mathlib lattices. The seL4/l4v Isabelle proof is a precise blueprint; ~6 core lemmas.

6. **Build GST/fairness/distributed** in Lean 4 using LeanLTL + Lentil as vocabulary, and the EPFD blog proof as a template. Veil is useful for invariant discovery but must never supply proof terms to our TCB.

---

*Sources consulted: arXiv 2507.01780 (LeanLTL), arXiv 2602.15409 + 2602.15078 (CSLib/HML), IACR 2026/899 (VCVio), IACR 2026/604 (CatCrypt), github.com/leanprover/cslib, github.com/Verified-zkEVM/VCV-io, github.com/verse-lab/veil, github.com/verse-lab/Lentil, github.com/m4lvin/lean4-pdl, github.com/FormalizedFormalLogic/Foundation, github.com/risc0/risc0-lean4, github.com/ravst/SymbolicCryptographyLean, mathlib4 docs (QPF, FixedPoints), Lean 4.20.0 release notes, protocols-made-fun.com EPFD proof, arXiv 2507.14080 (Shipwright/Dafny).*
