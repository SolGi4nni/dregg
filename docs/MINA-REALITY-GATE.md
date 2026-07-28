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

**UPDATE (composition landed, 2026-07-27).** Two of those gaps are now closed. (1) The field
LABEL is corrected at the source: `KimchiVerify`'s header/residuals now say `Fp = ZMod pN`
(Vesta::ScalarField), not `Fq/qN`. (2) The C5/C8 field-value checks are now **composed INTO one
decision that CONSUMES the real field values** — `kimchiVerifyDecisionField` (`KimchiVerify` §9b),
run over `ZMod pN` **as a `CommRing` with a WITNESSED inverse** (the prover supplies `denomInv`,
checked `denom·denomInv = 1` in the ring — no `Field`/primality instance needed). Evaluated in-kernel
on the REAL proof (`KimchiRealProofGate` §6b): `real_field_decision_accepts` shows C1 (shape) ∧ C8
(`cip = combinedInnerProduct`) ∧ witnessed-inverse ∧ C5 (`ft_eval0`) all ACCEPT over the real Pasta
scalar field; `real_field_decision_discriminates` shows each single tamper (cip, an es-order eval,
`ft_eval0`, a witness eval, the inverse witness, a shape count, a carrier) REJECTS. **No Pratt
primality certificate was needed** — the CommRing + witnessed-inverse route sidesteps it entirely.
Precise honest claim: *the decision now checks a real proof's arithmetic over the real field, modulo
the three named crypto carriers* (C3 Fr-sponge values, C6 custom-gate token streams, C9 IPA `msm==0`),
plus C4 `p(ζ)` fed as an input and C7's commitment-side MSM (K2 carrier). It does **not** verify Mina.

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
**APPLIED (2026-07-27):** `KimchiVerify`'s "two fields" header and §12 residual #4 now read
`Fp = ZMod PastaField.pN`; the gate header's mislabel note is updated to "now corrected at source".

## 3. What the decision actually consumes (the structural finding)

```
kimchiVerifyDecision prevLen publicLen wLen sLen coeffLen tCommLen chunkSize
                     transcriptOk ipaOk deferralOk
  = shapeOk … (C1)  &&  transcriptOk  &&  ipaOk  &&  deferralOk
```

The top-level `kimchiVerifyDecision` takes **seven `Nat` shape counts + three `Bool` carriers** —
**no field element enters it.** That was the structural finding.

**CLOSED (2026-07-27).** `kimchiVerifyDecisionField` (`KimchiVerify` §9b) is a NEW composed
decision that CONSUMES the field values:

```
kimchiVerifyDecisionField … n  polyscale evalscale evZeta evZetaOmega cipClaimed
                            omega zeta … w s shift zZeta zZetaOmega pZeta linConstTerm denomInv
                            ftEval0Claimed  transcriptOk ipaOk deferralOk
  = kimchiVerifyDecision … (C1 + 3 carriers)              -- the old decision, unchanged
  && decide (combinedInnerProduct … evZeta evZetaOmega = cipClaimed)     -- C8, over the field
  && decide ((ζ − ω^{n−3})(ζ − 1) · denomInv = 1)                        -- witnessed inverse
  && decide (ftEval0 … denomInv = ftEval0Claimed)                        -- C5, over the field
```

(`kimchiVerifyDecisionField_refines` proves this `= rfl`: the field checks are ADDED to the old
decision, not a replacement.) `combinedInnerProduct`/`ftEval0` are still the shipped `[Field F]`
formulas; §4/§5 explain the `CommRing`-mirror + witnessed-inverse route that lets them run at
`ZMod pN`. So "running a real proof through the decision" now exercises **C1 + C8 + C5 over the real
field + three carriers** — the field-formula fidelity is *inside* one accept, not beside it.

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
| **COMPOSED** C1+C8+C5 | `real_field_decision_accepts` / `real_field_decision_discriminates` | **`kimchiVerifyDecisionField` on the real proof over `ZMod pN` = `true`** — shape (C1) ∧ `cip = combinedInnerProduct` (C8) ∧ `(ζ−ω^{n−3})(ζ−1)·DINV = 1` (witnessed inverse) ∧ `ft_eval0 = ftEval0` (C5), plus 3 carriers; every single tamper (cip, an es-order eval, ft_eval0, a witness eval, the inverse witness, a shape count, a carrier) → `false` |

**These are the strong, honest results:** the C8 aggregation transcription and the C5 `ft(ζ)` assembly
**faithfully reproduce a real proof's intermediate scalars over the real Pasta scalar field**, and — as
of the composition — that arithmetic now **flows THROUGH one accept** (`kimchiVerifyDecisionField`),
in-kernel over `ZMod pN`, demonstrably non-vacuous (a tampered value rejects).

## 5. What could NOT run — the precise remaining gap

1. **No `Field (ZMod pN)`** — the shipped C4–C8 defs are `[Field F]`-typed and there is no
   prime-field instance for the 255-bit Pasta scalar field anywhere in the tree (no in-kernel
   `Fact (Nat.Prime pN)`; `native_decide` forbidden). **RESOLVED WITHOUT A FIELD INSTANCE
   (2026-07-27):** the C5/C8 checks run over `ZMod pN` as a `CommRing` via byte-identical mirrors
   (`cipR`/`ftEval0R`, `rfl`-tied) with the one `ftEval0` inverse SUPPLIED as a witness `denomInv`
   and checked `denom·denomInv = 1` in the ring (a unit's inverse is unique, so this pins it). **No
   Pratt primality certificate was needed.** (The residual is only that the *Field-typed* def itself
   is never instantiated at `ZMod pN` — the mirror computes the identical value, tied by `rfl`.)
2. ~~The decision does not compose the field checks~~ **CLOSED (2026-07-27):**
   `kimchiVerifyDecisionField` (§9b, `refines`-tied to `kimchiVerifyDecision`) composes C1 + the C8
   `cip` check + the witnessed-inverse + the C5 `ft_eval0` check into one accept, evaluated in-kernel
   on the real proof (`real_field_decision_accepts`, non-vacuous via `real_field_decision_discriminates`).
3. **C6 `linConstTerm` — GENERIC gate now COMPOSED (2026-07-27).** The double-generic gate constraint
   is transcribed (`genericGateConstraint`, algebraic + the `PolishToken` stream
   `genericConstraint_evaluates`) and threaded INTO the accept (`gateLinConst` +
   `kimchiVerifyDecisionGates`, `KimchiVerify` §9c): `ftEval0`'s constant term is DERIVED from the real
   generic-gate constraint, not the carrier. On the real proof `genericGateConstraint(real) = LCT`
   exactly and all 5 custom-gate selectors are zero (`generic_gate_matches_lct`,
   `custom_selectors_zero`), so THIS proof's whole `linConstTerm` is the generic gate — carrier
   retired. STILL CARRIED: the CUSTOM-gate bodies — Poseidon is transcribed as a def-generator
   (`poseidonLaneConstraint`) but NOT exercised (`poseidon_selector = 0`); complete_add/varbasemul/
   endomul/endomul_scalar bodies live behind their (here-zero) selectors.
4. **C3 phase-2 sponge — INSTANTIATED over `Fp = pN` (2026-07-27).** The Fr-sponge IS K3's
   Poseidon-over-Fp sponge (`Vesta::sponge_params() = fp_kimchi`, `curve.rs:63` — the earlier "over
   `Fq`/`qN`" label was the same Fp/Fq mislabel this gate corrected): `frSpongeDigest = Ref.hash` of the
   phase-2 absorb stream, whose `absorb_evaluations` point order is proven (`frEvalPointOrder`,
   `KimchiVerify` §9d). It consumes the real `ft_eval1` + public evals non-vacuously (`#guard`). STILL
   CARRIED: the fq-sponge `digest` value (phase-1 `Fq`-sponge over `qN`, not extracted) and the
   `challenge()` endo map (low-128-bit truncation + `to_field(endo_r)`) — so the actual β,γ,α,ζ,v,u are
   still not re-derived end-to-end.
5. **C9 `ipaOk` (`msm == 0`)** — the terminal IPA/FRI opening-soundness floor, **not discharged**
   (a STARK/light client proves the trace, not the opening). This is the Pickles-recursion frontier.
6. **C4 `publicEval`** — not run standalone (its value `p(ζ)` enters `ftEval0` as an input; running it
   standalone needs the batch-inverted Lagrange denominators, not extracted here).

## 6. Distance to "verifies a real Kimchi proof" — ordered by effort

1. ~~**[trivial]** Fix the `KimchiVerify` header field label `qN → pN`~~ **DONE (2026-07-27, §2).**
2. ~~**[small]** Compose what this gate runs separately into one end-to-end `accept`~~ **DONE
   (2026-07-27):** `kimchiVerifyDecisionField` threads C1 + C8 (`cip`) + C5 (`ft_eval0`) + the
   witnessed inverse; `real_field_decision_accepts` evaluates it on the real proof over `ZMod pN`.
3. ~~**[medium]** Make the shipped formulas runnable at the real field~~ **DONE for C5/C8
   (2026-07-27) via the `CommRing` + witnessed-inverse route — no Pratt certificate.** (C4
   `publicEval` recomputation still needs the un-extracted Lagrange denominators — see §5.6.)
4. ~~**[medium]** Emit C6's custom-gate constraint streams from Lean; instantiate the phase-2 sponge~~
   **PARTLY DONE (2026-07-27):** C6 GENERIC gate emitted + composed (`kimchiVerifyDecisionGates`;
   carrier retired for this proof, which fires no custom gate); C3 Fr-sponge INSTANTIATED over `Fp`
   (K3, `frSpongeDigest`), phase-2 order proven, non-vacuous on the real evals. REMAINING: the custom
   gate BODIES (Poseidon transcribed but selector-0; complete_add/varbasemul/endomul/endomul_scalar
   carried) and the C3 fq-sponge digest value + `challenge()` endo map (so v/u are not re-derived).
5. **[terminal]** The IPA/FRI opening-soundness floor (`ipaOk`) is inherited, not discharged — the same
   floor every STARK-backed light client carries. "Verifies a real proof" end-to-end still rests on it.

**Bottom line:** the transcription is real and faithful where a real proof can test it (C8 full
aggregation + C5 `ft(ζ)` reproduce the reference verifier exactly, non-vacuously), and **that
arithmetic now flows THROUGH one in-kernel accept over the real field** (`kimchiVerifyDecisionField`,
composed + evaluated, no Field/Pratt instance). What remains between here and "verifies a real Kimchi
proof": the three named crypto carriers (C6 custom-gate token streams, C3 phase-2 Fr-sponge values,
C9 IPA `msm==0`), C4's `p(ζ)` fed as an input, and C7's commitment-side MSM (K2). Precisely: **the
decision now checks a real proof's arithmetic over the real field, modulo those crypto carriers** —
it does **not** verify Mina.

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
