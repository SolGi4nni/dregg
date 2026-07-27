# MINA REALITY GATE — the assembled Kimchi verifier vs. a REAL Mina/Kimchi proof

**Question.** `kimchiVerifyDecision` (C1–C9 composed, `metatheory/Dregg2/Circuit/Emit/KimchiVerify.lean`)
has only ever been exercised on synthetic/toy witnesses over `ℚ`. How far is it from accepting a
**real** Kimchi proof — a small transcription fix, or several subsystems?

**Answer (verdict up front).** Several subsystems — but with a genuinely strong, non-vacuous core.
On a **real** proof (produced and ACCEPTED by o1-labs' own `kimchi::verifier::verify`), the shipped
C8 (`combined_inner_product`) and C5 (`ftEval0`) formulas **reproduce the reference verifier's exact
intermediate scalars over the real 255-bit Pasta field**, and C1 (shape) + C9 (IPA deferral, `k=16`)
run the shipped decision on real proof data. But the assembled *decision* does **not consume the
field values** (it is C1 ∧ three opaque crypto carriers), the shipped field formulas **cannot even be
typed at the real field** (no `Field (ZMod pN)` instance), and three named carriers
(custom-gate streams / Fr-sponge / IPA `msm==0`) remain. This is **not** one bug-fix away.

All Lean below is axiom-clean (`#assert_axioms` ⊆ `{propext, Classical.choice, Quot.sound}`), built
on hbox (`swarm-build lake build Dregg2.Circuit.Emit.KimchiRealProofGate`), no `native_decide`.

---

## 1. The real proof (source + how)

- **Source (a):** o1-labs `proof-systems` @ `36a8b510` (v0.7.0), the `kimchi` crate.
- **Harness:** `proof-systems/kimchi/examples/reality_gate_export.rs` (committed in that repo).
  - Circuit: `create_circuit` generic gadget, **5 public inputs**, witness filled; `new_index_for_test`.
  - Proof: `ProverProof::create::<BaseSponge, ScalarSponge, _>` over **Vesta/Pasta**, `OsRng`.
  - **Ground truth:** `kimchi::verifier::verify::<…, Vesta, …, OpeningProof<Vesta>>` **ACCEPTS** it.
  - Field values (challenges, evals, `ft_eval0`, `combined_inner_product`, public evals, alpha powers,
    the `es`-order eval lists, IPA prechallenges) extracted via `proof.oracles(...)` — the exact
    oracle path `to_batch` runs — and dumped as decimal in `metatheory/kimchi_real_proof.json`.
- This is a **real Kimchi proof** (real prover, real SRS, accepted by the real verifier), not synthetic.
  (Source (b) o1js and (c) a Mina mainnet block proof were not needed; (a) succeeded.)

Shape of the real proof: `prev_challenges=0`, `public=5`, `w_comm=15`, `σ_evals=6`, `coeff=15`,
`t_comm=7`, `chunk_size=1`, domain `n=32`, `zk_rows=3`, `max_poly_size=65536`, IPA rounds `k=16`.

## 2. FIELD CORRECTION (a real labeling bug the gate surfaced)

`Vesta::ScalarField = Fp` (mina-curves `curves/src/pasta/fields/fp.rs`, modulus
`28948022309329048855892746252171976963363056481941560715954676764349967630337` = Lean `PastaField.pN`).
**All** evaluations, challenges, `ft_eval0`, and `cip` live in **Fp = `ZMod pN`**.

`KimchiVerify.lean`'s header says the real statement is instantiated at *"`Fq = ZMod PastaField.qN`
(all evaluations, challenges, scalar arithmetic)"*. **That is the wrong field** — `qN` is the Vesta
**base** field (curve coordinates), `28948…647379679742748393362948097`. The formulas are
`variable {F} [Field F]` (field-generic), so the *arithmetic* is unaffected, but the named/intended
instantiation is wrong. Instantiating and feeding real Fp values at `ZMod qN` would reduce products
mod the wrong prime and fail. **This gate uses the correct `ZMod pN`.** Fix: header label `qN → pN`.

## 3. What the decision actually consumes (the structural finding)

```
kimchiVerifyDecision prevLen publicLen wLen sLen coeffLen tCommLen chunkSize
                     transcriptOk ipaOk deferralOk
  = shapeOk … (C1)  &&  transcriptOk  &&  ipaOk  &&  deferralOk
```

The top-level decision takes **seven `Nat` shape counts + three `Bool` carriers**. **No field
element enters it.** The C4–C8 field formulas (`publicEval`, `ftEval0`, `permScalar`, `ftComm`,
`combinedInnerProduct`) are **standalone `def`s** with `ℚ` KATs; they are *not wired into*
`kimchiVerifyDecision`. So "running a real proof through the decision" exercises **C1 + three
asserted carriers**; the field-formula fidelity is a *separate* demonstration (this gate).

## 4. What RAN on real values — `metatheory/Dregg2/Circuit/Emit/KimchiRealProofGate.lean`

Because the shipped C4–C8 defs are `[Field F]`-typed and **there is no `Field (ZMod pN)` instance in
the tree** (see §5), they cannot be instantiated at the real field. The gate uses `CommRing`-typed
mirrors (`cipR`, `ftEval0R`) whose bodies are **byte-identical** to the shipped defs and are tied to
them **by `rfl` for every field** (`cipR_eq`, `ftEval0R_eq`). So evaluating a mirror at `ZMod pN`
runs the shipped def's exact computation, at a `CommRing` where its `[Field F]` signature cannot be
typed. Each check below is a real-value **differential** (agreement with o1-labs' reference verifier),
non-vacuous (each has a companion tamper theorem), decided in the kernel over the real 255-bit field.

| Check | Theorem | Result on the REAL proof |
|---|---|---|
| **C1** shape | `c1_real_accepts` / `c1_real_discriminates` | shipped `kimchiVerifyDecision 0 5 15 6 15 7 1 true true true = true`; every single tamper (public 5→0, w 15→14, prev 0→1, each carrier) → `false` |
| **C8** `combined_inner_product` | `c8_real_matches` / `c8_discriminates_on_real` | shipped `combinedInnerProduct` on real `v,u` + the **45-entry es-order eval lists** (public, ft, z, 6 selectors, 15 w, 15 coeff, 6 σ, at ζ and ζω) **= Rust `cip` exactly**; bumping `EVZ[0]` breaks it |
| **C5** `ftEval0` | `c5_ft_real_matches` / `c5_discriminates_on_carrier` / `c5_discriminates_on_witness` | shipped `ftEval0` **= Rust `ft_eval0`** given the C6 `linConstTerm` and `denomInv` carriers; bumping either the carrier or a witness eval `w₀` breaks it |
| C5 carriers grounded | `denom_form_ok` / `denom_inv_ok` | `DENOM = (ζ − ω^{n−3})(ζ − 1)` (cross-checks Rust `w() = ω^{n−3}`) and `DENOM · DINV = 1` in `ZMod pN` |
| **C9** IPA deferral | `c9_real_deferral` / `c9_deferral_discriminates` | shipped `ipaDeferralOk` on the real **k=16** rounds records k challenges + `2^16` deferred terms; claiming `k=15` → `false` |
| **C3** raw-vs-endo | `c3_raw_vs_endo_shape_real` | real β,γ are `< 2^128` (raw sponge squeezes), α,ζ,v,u are `> 2^128` (255-bit `to_field(endo_r)` images) — matches `KimchiVerify.squeeze_order`'s raw/endo flags on a real proof |

**These are the strong, honest results:** the C8 aggregation transcription and the C5 `ft(ζ)` assembly
**faithfully reproduce a real proof's intermediate scalars over the real Pasta scalar field**, and they
are demonstrably not vacuous.

## 5. What could NOT run — the precise remaining gap

1. **No `Field (ZMod pN)`** — the shipped C4–C8 defs are `[Field F]`-typed and there is no
   prime-field instance for the 255-bit Pasta scalar field anywhere in the tree (no in-kernel
   `Fact (Nat.Prime pN)`; `native_decide` forbidden). They had **only ever been evaluated over `ℚ`**.
   The gate runs `CommRing` mirrors instead; running the *Field-typed* def itself on real values needs
   either a Pratt-certificate primality proof of `pN`, or a refactor of the formulas to `CommRing`
   (supplying/deriving inverses, as `ftEval0R` does for the single `denominator⁻¹`).
2. **The decision does not compose the field checks** — `kimchiVerifyDecision` = C1 ∧ three carriers;
   C4–C8 fidelity is shown here *beside* the decision, not *inside* one `accept`.
3. **C6 `linConstTerm` (custom gates)** — the Poseidon / VarBaseMul / CompleteAdd / EndomulScalar
   constraint streams are a **carrier** (the real `PolishToken::evaluate` value was fed in). Only the
   generic gate is emitted from Lean (`genericGate_evaluates`).
4. **C3 phase-2 sponge** — not instantiated; the real β,γ,α,ζ,v,u **cannot be re-derived** in Lean
   (the ORDER is proven; the sponge VALUES are the K3 + un-instantiated-sponge carrier).
5. **C9 `ipaOk` (`msm == 0`)** — the terminal IPA/FRI opening-soundness floor, **not discharged**
   (a STARK/light client proves the trace, not the opening). This is the Pickles-recursion frontier.
6. **C4 `publicEval`** — not run standalone (its value `p(ζ)` enters `ftEval0` as an input; running it
   standalone needs the batch-inverted Lagrange denominators, not extracted here).

## 6. Distance to "verifies a real Kimchi proof" — ordered by effort

1. **[trivial]** Fix the `KimchiVerify` header field label `qN → pN` (§2).
2. **[small]** Compose what this gate runs *separately* into one end-to-end `accept` over a real-proof
   structure (thread C4/C5/C8 outputs + C1 + carriers).
3. **[medium]** Make the shipped formulas runnable at the real field: either a Pratt primality
   certificate for `pN` → real `Field (ZMod pN)`, or a `CommRing` refactor + inverse supply.
4. **[medium]** Emit C6's custom-gate constraint streams from Lean (retire the `linConstTerm` carrier);
   instantiate the phase-2 sponge (retire the C3 value carrier).
5. **[terminal]** The IPA/FRI opening-soundness floor (`ipaOk`) is inherited, not discharged — the same
   floor every STARK-backed light client carries. "Verifies a real proof" end-to-end still rests on it.

**Bottom line:** the transcription is real and faithful where a real proof can test it (C8 full
aggregation + C5 `ft(ζ)` reproduce the reference verifier exactly, non-vacuously), but the assembled
object is **several subsystems** — field-instance, decision-composition, and three crypto carriers —
short of accepting a real Kimchi proof end-to-end, plus one trivial header-label fix.

## 7. Reproduce

```
# Real proof + field-value extraction (o1-labs repo, local cargo — separate from breadstuffs):
cargo run --release --example reality_gate_export -p kimchi \
  --manifest-path ~/dev/proof-systems/kimchi/Cargo.toml > metatheory/kimchi_real_proof.json
# (prints to stderr: "real verifier ACCEPTED the real proof" + the ω/zkpoly cross-checks)

# The Lean reality gate (hbox; Mathlib cached):
swarm-build lake build Dregg2.Circuit.Emit.KimchiRealProofGate
```

Artifacts: `metatheory/Dregg2/Circuit/Emit/KimchiRealProofGate.lean` (the gate),
`metatheory/kimchi_real_proof.json` (the real-proof fixture),
`proof-systems/kimchi/examples/reality_gate_export.rs` (the extractor).
