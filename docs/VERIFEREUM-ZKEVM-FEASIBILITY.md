# Verifereum → zkEVM feasibility: can dregg's arithmetizer compile a verified EVM into a state-validity AIR?

Status: RESEARCH / FEASIBILITY READ (no build). Author pass 2026-07-26.

> **[ADDED 2026-07-27 — a provenance fact this document did not disclose.]** Everywhere below this
> calls the source *"Verifereum"* without noting that **the local checkout is a locally-modified
> fork**: `~/dev/verifereum` carries **2 dregg commits atop upstream `8107a32`** (`513beea` "track
> the bytecode-proof corpus", `bf8294d` "DreggVault no-double-withdraw bytecode proof"), plus an
> uncommitted working change. The cited `spec/` and `util/` files are **untouched by the fork, so
> every pin in this document holds** — but a reader auditing against upstream Verifereum should know
> the tree they would be handed is not upstream. (audit F-D7.)
>
> Two positives from the same audit, recorded because they were checked and held: this document's
> **in-repo inventory holds** — `Sha256Gadget`, `Bls12381Tower*`, `EffectVmEmitIvcStateTransition`
> and `LightClientMpt` were independently confirmed to exist, `Keccak` appears only in ML-DSA sponge
> contexts (consistent with *"only a carrier, NOT built"*), and the **"~29.7k gates/block" figure is
> genuinely sourced** to `Sha256Gadget.lean:57`.

Scope: a grounded read of the dregg arithmetizer + a sourced read of Verifereum, against the
thesis that dregg's `def`-generator arithmetizer can turn a *verified* EVM step function into an
AIR proving ETH **state validity** — a proof-native guarantee to sit beside (not replace) the
honest-majority consensus light-client.

---

## 0. Verdict

**TRACTABLE-FIRST-SLICE (a real POC exists) — but the thesis as literally stated is PARTIALLY
REFUTED, and the full zkEVM is a DEEP MULTI-YEAR BUILD.** Three separable claims, graded honestly:

1. **The architecture claim is VALIDATED.** dregg's arithmetizer *is* a `def`-generator: a Lean
   `def` over `AirBuilder.Head` (`Σ coeff·∏cols + const`) lowered to gate `EmittedExpr`, with the
   correctness `∀`-spec living in a *refinement theorem* (`*_forces`, `*_no_forgery`) — never in the
   AIR. It arithmetizes COMPUTATIONS, and dregg **already arithmetizes its own VM step function**
   (`EffectVmEmit*` family + `EffectVmEmitIvcStateTransition` — a per-row state-transition AIR). So
   "arithmetize the EVM step, keep the `∀` in a once-proved Lean lemma" is not speculative; it is the
   shape the tree already runs at, for a different VM.

2. **The "Verifereum" leg is REFUTED as a *free* source of "verified".** Verifereum is **HOL4**, not
   Lean. Its `step` is an executable HOL4 function — exactly the *computational* shape the thesis
   needs — but it lives in a *different logic from a different prover*. dregg's arithmetizer ingests
   Lean `def`s; it cannot ingest an HOL4 term, and there is no production HOL4→Lean semantics-transfer
   tooling (the two don't share a foundation: HOL4 is classical simple type theory, Lean is CIC). So
   the clean thesis — "one machine-checked Lean theorem: AIR ⟺ the *verified* EVM semantics" —
   **cannot be had by pointing at Verifereum.** You must either (a) PORT Verifereum's step to Lean
   (large; and the port's fidelity to Verifereum becomes a NEW, undischarged residual — a
   cross-prover differential, not a proof), or (b) swap the semantics source to a **Lean-native
   verified EVM** — which *exists*: Nethermind's EVM/Yul-in-Lean (Cancun, validated against 99.99% of
   Ethereum tests). For the "both `∀`s in Lean" architecture, Nethermind-in-Lean is the better-fitting
   leg than Verifereum; Verifereum's edge is currency (Osaka fork) and being purpose-built as a
   *semantics* rather than a compiler model.

3. **The full EVM is a DEEP BUILD.** Independent of which spec you refine against, arithmetizing all
   ~140 opcodes + gas + precompiles + the keccak MPT is a multi-year, multi-person effort at the scale
   of every production zkEVM. But a **tractable first slice** — a "verified mini-EVM step" (256-bit
   arithmetic/stack opcodes, no storage/keccak/precompiles) — is real, composes the pieces that
   already exist, and is the right POC.

**Net:** the *arithmetization architecture* is sound and demonstrably in-hand; the *distinctive prize*
("provably the verified semantics") is reachable but NOT for free from Verifereum — it costs a
Lean-side semantics (port, or adopt Nethermind's) whose fidelity is then the load-bearing residual;
the *full zkEVM* is a deep build with a tractable first slice.

---

## 1. Verifereum assessment (sourced)

| dimension | finding | source |
|---|---|---|
| Prover / language | **HOL4** (Higher-Order Logic), implemented in Standard ML. **Not Lean, not Coq.** | verifereum.org; repo README |
| Step shape | **Executable function**, not a relation. Main entry `step : unit execution_result` where `execution_result = (α + exception option) # execution_state`; dispatch via `step_inst op` after `FLOOKUP parsed context.pc`; e.g. `Add ↦ step_binop Add word_add`. This is the *computational* `def` the thesis wants. | `spec/vfmExecutionScript.sml` |
| Executability | Semantics is "executable by evaluation inside the logic, used to run the conformance tests." Explicitly not a fast EVM. | verifereum.org |
| EVM coverage | "Approximately complete Ethereum Execution Spec Tests (EEST) suite coverage." Targets the **live Osaka fork**; preparing Glamsterdam. Ships utilities for **RLP, Merkle-Patricia Trie, secp256k1, ABI**. | verifereum.org; repo README |
| State model | `execution_state` / `vfmStateScript.sml`; account+storage trie via `util/merklePatriciaTrieScript.sml`. Gas + precompiles present (EEST-level). | repo file tree |
| Maturity | Self-described production-quality; first community event Feb 2025; public progress tracker. A serious, current, near-complete EVM semantics — genuinely more complete than a from-scratch Lean model would be today. | verifereum.org |
| **Portability to dregg** | **LOW as-is.** HOL4 term → Lean `def` is a manual re-mechanization; no automated transfer. The port would be a fresh Lean artifact whose agreement with Verifereum is a *conformance/differential* fact (shared EEST vectors), **not** a machine-checked refinement — and per house law, a differential is drift-detection, not verification. | analysis |

**Honest consequence for the thesis wording.** The thesis says "Verifereum's verified semantics +
dregg's forcing lemma are the two `∀`-refinements, **both in Lean**." That is not achievable with
Verifereum, because Verifereum's `∀` lives in HOL4. The achievable shapes are:

- **(A) Port-then-refine.** Re-mechanize Verifereum's `step` (or a slice) as a Lean `def`; arithmetize
  that; prove `AIR ⟺ Lean-step` in Lean. The "verified against a real EVM" claim then rests on
  `Lean-step ≈ Verifereum-step`, anchored only by **shared EEST conformance vectors** — a
  differential, NOT a proof. Name it as such; do not launder it as "refined against Verifereum."
- **(B) Adopt a Lean EVM.** Use **Nethermind's EVM/Yul-in-Lean** (Cancun; 99.99% of Ethereum tests)
  or the **Verified-zkEVM** effort (`Verified-zkEVM/evm-asm`; the Evm64 line has ~24 fully-proved
  opcodes: ADD/SUB/MUL/DIV/MOD/AND/OR/XOR/NOT/SHL/SHR/SAR/LT/GT/EQ/… incl. PUSH/DUP/SWAP) as the Lean
  `∀`-leg. Then "both `∀`s in Lean" holds honestly, and the semantics is *already* a Lean object the
  arithmetizer can ingest. Cost: Cancun-fork lag vs Verifereum's Osaka.

Either way the "verified" adjective only reaches as far as the Lean reference's fidelity to the real
EVM. That fidelity — port-differential (A) or another team's Lean model (B) — is the new soft spot,
and it must be stated at that resolution.

---

## 2. The arithmetizer-gap inventory

The generator vocabulary is `metatheory/Dregg2/Circuit/Emit/AirBuilder.lean`: `Head` = `Σ coeff·∏cols
+ const`; `headToExpr_eval` is the once-proved semantic bridge (gate poly evaluates to the head
value); gadget families are boolean-pin (`gBin`, forced `x(x-1)=0`), conditional-nonzero
(`condNonzero_forces`), bit-decomposition **range** (`rangeNonneg`), and signed compare
(`forcedGe0`). The felt field is **BabyBear** (`2013265921`, ~31 bits); gates are read over ℤ (the
strong reading), and the mod-p↔ℤ width gap is a **named, shared residual** across every Emit file.

| EVM need | dregg status | template / evidence | classification |
|---|---|---|---|
| **(a) 256-bit word ALU** (add/mul/sub/div/mod, bitops, cmp, mod 2²⁵⁶) | **NOT built**, but directly templated. | `Emit/Bls12381Tower.lean` does non-native modular arithmetic by *quotient witness*: encode a big int as limbs over BabyBear, witness the quotient, check the big-int identity over ℤ, `fpMulCore_forces` proves the congruence. **EVM mod 2²⁵⁶ is STRICTLY SIMPLER than a prime field**: power-of-two modulus ⇒ "reduce" = drop the high limbs (the carry/quotient is just the overflow bits), and there is **no `z < p` canonicity compare** (the one named residual in the BLS tower vanishes). Bitops/shifts are the `Sha256Gadget` bit-column discipline at width 256. | **TRACTABLE — express via existing pattern.** The single most reusable gap. |
| **(b) Keccak-256** (SHA3/KECCAK256 opcode + every MPT node hash) | **NOT built** (keccak is only a *carrier* today, `toyKeccak` in models). | `Emit/Sha256Gadget.lean` is the exact template: 32 boolean columns/word, XOR/AND/NOT as local bit gates, ARX round as a `def`-generator `foldl`, both-polarity KAT'd, ~29.7k gates/block. Keccak-f[1600] is a *different* permutation (θ/ρ/π/χ/ι over a 5×5×64 state, no modular add) but the **same bit-gate discipline**; note EVM uses Keccak-256, not NIST SHA-3 (padding differs). | **NEW but templated.** Sizeable (1600-bit state; on the order of SHA per invocation) and on the hot path for every trie op. |
| **(c) MPT / storage trie** | **Rules exist in Lean** (not as an AIR). | `Dregg2/Bridge/LightClientMpt.lean` already formalizes EIP-1186: state-trie → account(nonce,balance,storageHash,codeHash) → storage-trie, with **RLP encode injectivity PROVEN** (`encodeNode_injective`, `encAccount_injective`) and keccak-CR as a named carrier + binding theorem (`mpt_balance_binding`). The Merkle-fold AIR machinery generalizes (`Sha256MerkleFold`, `MerkleMembership*Emit`). | **NEW-ish, with a real head-start** — but gated on (b): a trie AIR needs an *in-circuit* keccak, which does not exist. Today's MPT is rules-over-a-carrier, not a hashing circuit. |
| **(d) memory / stack / gas metering (RAM argument)** | **SKELETON ALREADY IN IR-v2.** | `Dregg2/Circuit/DescriptorIR2.lean` defines five tables incl. a **`memory` table** `(addr, value, prev_value, prev_serial, kind∈{read,write,…})` with the offline-memory-checking discipline: "serial-ordered and multiset-balanced" — i.e. the standard permutation-argument RAM. `VmConstraint2.lookup` + `Lookup.lean` carry the LogUp-style lookup. Stack and memory become memory-table accesses; gas is an accumulator column with `forcedGe0` non-negativity. | **Largest new subsystem in most zkEVMs — here the hardest machinery is PRESENT in skeleton.** The biggest single de-risk of this whole direction. |
| **(e) ~140 opcodes as dispatch** | **Pattern exists** (not for EVM). | The `EffectVmEmit*` family already dispatches ~50 effect variants via one-hot selectors into per-variant sub-circuits, refined per variant. EVM dispatch is the same: a one-hot opcode selector column gating per-opcode-family sub-AIRs. | **Express via existing pattern**, but ~140× the surface + gas/exception/PC-update glue per opcode. Mechanical, vast. |
| precompiles (ecrecover, modexp, ecadd/mul, pairing, blake2f, KZG point-eval) | mostly NOT built | `Bls12381Tower.lean` is the *foundation* for the pairing precompile (§7 names Fp6/Fp12/Miller/final-exp as ~millions of gates); secp256k1 ecrecover has no gadget. | **NEW, heavy.** Deferrable out of any first slice. |

**Summary:** of the five, **(d) is the pleasant surprise** (the RAM argument is already scaffolded),
**(a) is the most leverage-per-effort** (mod-2²⁵⁶ is *simpler* than the prime-field arithmetic already
proven), **(b)/(c) are templated-but-real new crypto**, and **(e) is mechanical-but-enormous**.

---

## 3. Honest cost

**Order of magnitude.** Production zkEVMs (zkSync, Polygon zkEVM, Scroll, Taiko, and the zkVM route —
RISC0/SP1 proving `revm`) are **tens of person-years, multi-team, multi-year** efforts. Per-opcode
gate cost ranges from ~hundreds (a 256-bit ADD) to tens of thousands (KECCAK256, memory-expansion
ops); a full block proof is in the **millions-to-billions of gates**, which is why the ecosystem has
moved toward zkVMs and recursion/continuations rather than monolithic circuits. dregg's per-op costs
would land in that same regime (SHA-256 already costs ~29.7k gates/block here; keccak comparable;
non-native 256-bit mul ~hundreds–low-thousands). **There is no way to make "a full verified zkEVM" a
short project.**

**What the Verifereum/arithmetizer route buys that shipping zkEVMs do NOT.** Production zkEVM circuits
are **hand-built and audited, not proven equal to a formal EVM spec** — arithmetization bugs are a
recurring class (found in audits and in the wild). A dregg EVM AIR carrying a machine-checked
`*_forces`/refinement lemma to a *Lean* EVM step reference would be **spec-correct-by-construction on
the arithmetization side** — the circuit provably computes the reference semantics, not merely "passes
tests." That is genuinely rare (the Verified-zkEVM effort is the only comparable public attempt, and
it is early). **This is the real prize and it is defensible — with two honest caveats:**

- The "verified" reaches only as far as **the Lean reference's fidelity to the real EVM** (port-diff
  or adopted model; §1) — a conformance anchor, not a proof of the reference itself.
- It inherits dregg's **standing FRI/STARK soundness floor** (the deployed prover is a
  calculator-grade bit-security object today; "the light client accepts" is not unconditional
  soundness). A verified AIR on top of an undischarged floor is a *stronger circuit*, not a *sound
  proof system*. Describe at that resolution.

**The tractable first slice — a "verified mini-EVM step" POC.** YES, one exists and it composes only
already-present or simplest-new pieces:

- **Opcode set:** the stack/arithmetic fragment — `ADD, MUL, SUB, DIV, MOD, LT, GT, EQ, ISZERO,
  AND, OR, XOR, NOT, SHL, SHR, PUSH, POP, DUP, SWAP`. (Exactly the fragment Evm64 has fully proved,
  which also gives a ready-made Lean reference for leg (B).)
- **No** storage, **no** keccak, **no** precompiles, **no** exact gas (flat or omitted).
- **State:** stack as `memory`-table accesses (reusing the existing offline-memory-checking table);
  PC as an accumulator; one-hot opcode selector for dispatch.
- **ALU:** the 256-bit modular gadget via the `Bls12381Tower` quotient-witness template specialized to
  mod 2²⁵⁶ (simpler — no prime, no canonicity compare).
- **Refinement:** `stepMiniEvm_forces` — the AIR row accepts iff the ported/adopted Lean mini-step
  relates (pre-stack, opcode) to (post-stack), proven once, `∀`-quantified, outside the AIR.

This is a genuine composition (arithmetizer gadgets + existing memory table + a Lean mini-EVM `def` +
a forcing lemma), not a toy `#eval`, and it exercises every load-bearing joint of the thesis at the
smallest non-trivial scale.

---

## 4. Payoff vs the light-clients — validity is not the tip

The deployed ETH light-client (`Emit/LightClientEthAir.lean`, refining
`Bridge/LightClientEth.eth_no_forgery`) proves a **consensus** decision: the sync committee — an
**honest-majority (2/3) trust assumption**, carried as the `BLS_OK` bit — signed off on this finalized
beacon/execution `state_root`. It answers **"is this the tip the honest majority agreed to?"**
(finality / canonicity). It does **not** re-execute the block; it *trusts the validators executed
correctly*. Trust root: honest-majority of a committee.

A zkEVM proves the orthogonal thing — **state VALIDITY**: given `pre_state_root` and a block, the
`post_state_root` is the **correct** result of EVM execution — **no honest-majority assumption**, a
proof-native guarantee. That is the upgrade: from "the committee vouches for the result" to "the result
is provably the EVM's output."

**But validity ≠ tip, and this is the load-bearing honest point.** A zkEVM proves "*IF* this is the
block, its execution is valid." It says nothing about **which** block is canonical/final — that is
still a consensus question. So a truly proof-native ETH view needs **BOTH**, and they are
**complementary, not substitutes**:

- **canonicity/finality** — which block is the tip: the consensus light-client (today's honest-majority
  `LightClientEthAir`), or eventually a consensus-STARK; and
- **validity** — the tip's state is correctly computed: the zkEVM here.

The zkEVM removes the *execution*-trust assumption; it does not remove the *consensus*-trust
assumption. Selling it as "replaces the light-client" would be exactly the kind of scope-drop house
law forbids. Its honest headline: **"proof-native state validity for ETH, composed with (not instead
of) the finality client."**

---

## 5. The single highest-leverage first move

**Build the 256-bit modular ALU gadget for ONE opcode (ADD) end-to-end, and in the same slice resolve
the Lean-semantics-leg decision — by refining against a Lean mini-step, NOT Verifereum directly.**

Concretely, one focused Lean lane:

1. **`Emit/EvmWord256.lean`** — a `def`-generator for the 256-bit word (limbs over BabyBear, à la
   `fpValue`) and `addMod256` via the quotient-witness template specialized to 2²⁵⁶ (drop-the-high-
   limb; no canonicity compare), with `addMod256_forces : gate holds → out ≡ a+b (mod 2²⁵⁶)`, KAT'd
   both polarities. This is pure arithmetizer work, entirely inside the existing vocabulary.
2. **A Lean `def` mini-step for ADD** (pop a, pop b, push (a+b) mod 2²⁵⁶) — sourced by *adopting*
   Evm64/Verified-zkEVM's Lean ADD if usable, else a 20-line local `def` — and a refinement
   `evmAddAir_refines_step`. This forces the prover-mismatch question into the open on day one: you
   *cannot* write this against Verifereum's HOL4 `step`, which makes the port-vs-adopt decision
   concrete rather than aspirational.

Why this and not, say, keccak or the opcode dispatch: (a) it is the **most-reused gadget** (every
arithmetic/comparison/gas op needs 256-bit modular math), (b) it is the **simplest genuinely-new**
gadget (mod 2²⁵⁶ < prime field, and the tower already proves the harder case), (c) it **surfaces the
one thesis-critical risk immediately** — that "the verified EVM" is HOL4 and the honest refinement
target must be a *Lean* step whose EVM-fidelity is a conformance anchor, not a theorem. Everything
downstream (keccak, MPT, dispatch, gas) is templated or scaffolded; this move buys the most
information about whether the *distinctive* claim survives contact.

---

## Appendix — key files read

- `metatheory/Dregg2/Circuit/Emit/AirBuilder.lean` — the `Head` generator vocabulary + `headToExpr_eval`
  bridge + gadget families (`gBin`, `condNonzero_forces`, `rangeNonneg`, `forcedGe0`).
- `metatheory/Dregg2/Circuit/Emit/Sha256Gadget.lean` — the ARX/bit-gate crypto-fold template (keccak's model).
- `metatheory/Dregg2/Circuit/Emit/Bls12381Tower.lean` — non-native modular arithmetic by quotient
  witness (the 256-bit ALU template; `fpMulCore_forces`).
- `metatheory/Dregg2/Circuit/DescriptorIR2.lean` — IR-v2 tables incl. the **`memory` offline-memory-
  checking table** + `lookup` (the RAM-argument skeleton) and `VmConstraint2`.
- `metatheory/Dregg2/Circuit/Emit/LightClientEthAir.lean` — the deployed honest-majority ETH client
  (the thing state-validity composes *with*).
- `metatheory/Dregg2/Bridge/LightClientMpt.lean` — EIP-1186 MPT rules proven in Lean (RLP injectivity,
  keccak-CR carrier, `mpt_balance_binding`).
- `metatheory/Dregg2/Circuit/Emit/EffectVmEmitIvcStateTransition.lean` — precedent: dregg already
  emits a per-row STATE-TRANSITION step function as an AIR.

## Sources

- [Verifereum — verifereum.org](https://verifereum.org)
- [verifereum/verifereum (repo)](https://github.com/verifereum/verifereum)
- [verifereum/vyper-hol](https://github.com/verifereum/vyper-hol)
- [Nethermind — a formal EVM/Yul model in Lean (Cancun, 99.99% of tests)](https://www.nethermind.io/blog/a-trustworthy-formal-model-of-evm-yul-in-lean)
- [Verified-zkEVM/evm-asm](https://github.com/Verified-zkEVM/evm-asm)
- [Ethereum formal verification overview (leonardoalt)](https://github.com/leonardoalt/ethereum_formal_verification_overview)
