# PICKLES-VERIFIER-SCOPE.md — from a single Kimchi verify to Mina's Pickles recursion

**Status:** research / scoping only. No Lean, no build. Audience: ember + the K7 (Pickles) build.
This is the follow-on named in `docs/MINA-KIMCHI-VERIFIER-PLAN.md` item 6 ("Pickles/recursion tip …
recursion is the follow-on") and the frontier `KimchiVerify.lean` freezes at `prevLen = 0`.

It maps every piece of a Pickles verifier onto **have** (an instantiation of a primitive the K-lanes
already built) vs **new** (recursion machinery with no analog in the single-proof verifier), with
source pins, and turns "meaningfully further than the Kimchi verifier" into an ordered task list.

## Provenance (what was read)

- **We have** (`/Users/ember/dev/breadstuffs`, HEAD `429a5afdce`):
  `metatheory/Dregg2/Circuit/Emit/` — `PastaField` (K1, **Fp AND Fq**), `PastaCurve` (K2, **Pallas AND
  Vesta** + endo), `PastaCurveComplete` (K4a, RCB add both curves), `PastaScalarMul` (K4b, GLV `[k]P`
  both curves), `PastaPoseidon` (K3, Poseidon-over-Pasta sponge, **Fp state only**), `PastaIPA` (K4c,
  the IPA deferral + `sVec_eq_bPoly`), `KimchiVerify` (K5, the single-proof decision, `prevLen = 0`),
  `KimchiRealProofGate` (K5 run on a real proof over `ZMod pN`, `k = 16`). Docs:
  `KIMCHI-VERIFY-SPEC.md`, `MINA-REALITY-GATE.md`.
- **o1-labs `proof-systems`** (`/Users/ember/dev/proof-systems`, HEAD `f6d958dc05`, `git describe`
  `0.7.0-11-gf6d958dc05`; the K-lanes cite `36a8b510` = same `0.7.0` version, different rev — **the
  cited line pins `commitment.rs:426-476` and `ipa.rs:301-502` did NOT drift**). This is the
  polynomial-commitment / IPA backend. **CORRECTION to the task framing:** there is **no Rust
  "pickles crate"** here. The only `pickles`-named target is `o1vm`'s MIPS-zkVM flavour
  (`o1vm/src/pickles/`), unrelated to Step/Wrap. Step/Wrap recursion lives in OCaml (mina) and is
  re-implemented in Rust in openmina (mina-rust). `arrabbiata/` is a *Nova/folding* scheme — a
  different recursion approach, not Pickles.
- **o1-labs `mina`** (`/Users/ember/dev/mina/src/lib/pickles`, vendored source, no local git rev) —
  the **canonical** Pickles (Step/Wrap, tick/tock, `Deferred_values`, `inductive_rule`, the VK).
- **openmina `mina-rust`** (`/Users/ember/dev/mina-rust`, HEAD `82480cd468`, v0.19.0) —
  `crates/ledger/src/proofs/` — a clean **Rust** Pickles verifier (the easiest cross-check; it is
  what actually verifies a real mainnet block/tx today).

---

## TL;DR — the three things this doc must print

### 1. The have-vs-new split

**HAVE — the whole arithmetic floor for BOTH sides of the cycle already exists.** Pickles is two
Kimchi verifiers on the two Pasta curves that check each other. The single-proof lanes were built
field-/curve-generic, so:

| Pickles needs | Already built | Note |
|---|---|---|
| Fp arithmetic (Step scalars) **and** Fq arithmetic (Wrap scalars) | **K1** `PastaField` (both `pN`, `qN`) | both primes forced |
| Pallas point ops (Step-native) **and** Vesta (Wrap-native) + the endo | **K2** `PastaCurve` (both curves, `φ = [λ]`) | both `#guard`'d on-curve |
| RCB complete add + GLV `[k]P` on **both** curves | **K4a/K4b** `PastaCurveComplete`/`PastaScalarMul` | `pallas*`/`vesta*` instantiations |
| the IPA `⟨s,G⟩` sg-accumulation identity | **K4c** `PastaIPA.sVec_eq_bPoly` + `deferral_compression` | **IS** `b_poly_coefficients`; the head start |
| the b-poly evaluator (`b_correct` deferred check) | **K4c** `bEval` | = OCaml `challenge_polynomial` |
| `combined_inner_product` + `ft_eval0` (the `cip`/`ft` deferred checks) | **K5** `combinedInnerProduct`, `ftEval0` | reproduce a real proof's scalars over `ZMod pN` |
| the single-Kimchi-verify decision | **K5** `kimchiVerifyDecision(Field)` | instantiated at the **Step** shape (Vesta-committed, `k=16`) |
| the Fiat–Shamir Poseidon sponge | **K3** `PastaPoseidon` | **one flavour only** (Fp state) — Wrap needs the Fq-state mirror |

**NEW — the recursion glue, none of which the single-proof verifier contains:** the two
`Deferred_values` records + the shifted-value field bridge; `finalize_other_proof` (the four-way
cross-check that discharges the opposite proof's non-native scalar arithmetic); the
**transcript-equality binding** that makes the exposed public-input scalars *sound*; `prev_challenges
> 0` (the `RecursionChallenge` fold, retiring the `prevLen = 0` freeze); the base case (dummy proof +
`is_base_case` bypass); the wrap-VK model + `branch_data`/domain selection; and Mina's concrete
instantiation (real Step/Wrap VKs, the tx-snark merge tree, the block step rule, the tip verify).

### 2. The ordered task list (dependency order; effort honest; see §7 for detail)

- **P0** — Instantiate K5 at the **Wrap** shape (Pallas-committed, Fq scalars, `k=15`). *Medium.*
- **P1** — Close `accumulator_check` (the sg discharge) on top of `sVec_eq_bPoly`. *Small–medium.*
- **P2** — The `Deferred_values` data model + Type1/Type2 shifted-value bridge. *Small–medium.*
- **P3** — `finalize_other_proof`: the four re-checks (`xi`/`cip`/`b`/`plonk`) on ONE side. *Medium.*
- **P4** — **The transcript-equality binding** (`assert_eq_plonk` + digest/bp-challenge equality) —
  the soundness of P3. *Hard — the single hardest buildable piece.*
- **P5** — Mirror P3+P4 to the other side (field swap Fp↔Fq). *Small (mirror).*
- **P6** — `prev_challenges > 0`: the `RecursionChallenge` fold; retire the `prevLen = 0` freeze. *Medium.*
- **P7** — Base case + inductive gating (dummy proof, `is_base_case`, `proof_must_verify`). *Small–medium.*
- **P8** — Wrap-VK model + `branch_data`/domain selection + `max_proofs_verified` encodings. *Medium.*
- **P9** — Mina's instantiation: real VKs, tx-snark merge tree, block step rule, protocol-state hash,
  the tip verify (`verify_block` = accumulator_check + native wrap verify). *Medium–large.*
- **P10** — *(terminal, inherited — not "built")* the IPA `msm == 0` opening-soundness floor. *N/A.*

### 3. The single hardest piece

**P4 — the deferred-values cross-check as a SOUND theorem: the transcript-equality binding.** The
whole recursion is sound only because the scalars a proof exposes in its *public input* are pinned,
across a non-native field boundary, to the challenges the group sub-verifier actually sampled —
`assert_eq_plonk` (`wrap_verifier.ml:492-499`), the sponge-digest equality, and the
per-round bulletproof-challenge equality (`wrap_main.ml:430-439`, `step_verifier.ml:1271-1285`),
carried over the `Shifted_value` Type1/Type2 bridge (`common.ml:91-103`). This has **no analog in
K5** (which consumes challenges as given), it spans both fields, and it is where security lives. The
absolute-hardest thing (P10, the IPA opening-soundness floor) is *inherited, not dischargeable* — the
same floor every STARK-backed light client carries — so it is a named terminal residual, not a task.

---

## §A — The Step/Wrap construction (which K-lane instantiates which side)

Pickles is a **2-cycle of two circuits**, each an in-circuit Kimchi verifier for the other, on the
opposite Pasta curve — so each side's scalar-field arithmetic is *native* to the other side. The
cycle is fixed in the backend and the field-witness impls:

- **Tick = Step**, **Tock = Wrap** [S — `mina/src/lib/pickles/impls.ml:5,33-34,146-153`;
  `mina/src/lib/pickles/backend/backend.ml:1-9`]. Field order: `Tick.Field = Fp < Fq = Tock.Field`
  [`impls.ml:51`].
- **Step** is Fp-native, does group ops on **Pallas** (`Pallas.BaseField = Fp`), produces a
  **Vesta**-committed Kimchi proof, **16 IPA rounds** (max degree `2^16`)
  [`mina/src/lib/pickles/step_main_inputs.ml:114-115`; `common.ml:6-14`;
  `kimchi_pasta_basic.ml:16-17`; `mina-rust/crates/ledger/src/proofs/field.rs:90-107`
  (`Parameters = PallasParameters`, `OtherCurve = Vesta`, `NROUNDS = 16`); `mod.rs:33-34`].
- **Wrap** is Fq-native, does group ops on **Vesta** (`Vesta.BaseField = Fq`), produces a
  **Pallas**-committed Kimchi proof, **15 IPA rounds** (max degree `2^15`)
  [`mina/src/lib/pickles/wrap_main_inputs.ml:104-105`; `field.rs:109-125`
  (`Parameters = VestaParameters`, `OtherCurve = Pallas`, `NROUNDS = 15`)].
- **Direction:** **Step** proves the application statement AND recursively verifies **0/1/2 previous
  Wrap proofs** [`mina/src/lib/pickles/step_main.ml:28-121`]; **Wrap** wraps **exactly one** Step
  proof [`mina/src/lib/pickles/wrap_main.ml:401-414`]. The object a node consumes for a block/tx is
  the **outermost Wrap proof**, verified as a single Tock/Pallas Kimchi proof
  [`mina/src/lib/pickles/verify.ml:132,206,210`; `mina-rust/.../verification.rs:499-521`].

**The K-lane mapping (both sides are already floored):**

| Pickles side | field | native curve (in-circuit point ops) | commits its proof on | K-lanes that instantiate it |
|---|---|---|---|---|
| **Step** (tick, 16 rounds) | Fp (`pN`) | Pallas | Vesta | K1(Fp), K2(Pallas)+K4a(`pallasCompleteAdd`)+K4b(`pallasLadder`), K3(Fp sponge), K4c, **K5 (already at this shape)** |
| **Wrap** (tock, 15 rounds) | Fq (`qN`) | Vesta | Pallas | K1(Fq), K2(Vesta)+K4a(`vestaCompleteAdd`)+K4b(`vestaLadder`), **K3 Fq-sponge = residual**, K4c, **K5 re-instantiated (P0)** |

The key observation: **K1/K2/K4a/K4b already cover BOTH curves and BOTH fields** (they were authored
generic and instantiated twice). The only arithmetic gap is **K3's sponge, built for the Fp state
only** — the Wrap side needs the same Poseidon permutation over the Fq state (a mechanical mirror,
already a named K3/`KimchiVerify` §12.3 residual). Our `KimchiRealProofGate` (`k=16`, Vesta-committed,
Fp scalars) is exactly a **Step-shape** proof; verifying a real Mina block additionally needs the
**Wrap-shape** verify (P0).

---

## §B — The DEFERRED-VALUES cross-check (the heart; genuinely NEW)

**The principle** [S — `mina/src/lib/pickles/composition_types/composition_types.ml:24-32`]: a
verifier circuit does the *group* part of verifying the other proof, but the *scalar-field*
arithmetic (combined inner product, the b-poly evaluation, the plonk-derived scalars) is in a field
**non-native to that circuit**. So it does not compute those; it **exposes them in its own public
input** as `Deferred_values`, and the **next circuit — which runs on the other curve, where that
field is native — recomputes and checks them**. Each proof defers its own scalar arithmetic one hop.

### The two records (symmetric, one per curve)

**Wrap-side `Deferred_values`** carries the **Step proof's Fp scalars** [S —
`composition_types.ml:215-268`], **Step-side** carries the **Wrap proof's Fq scalars** [S —
`composition_types.ml:1152-1164`]. In Rust: `DeferredValues<F>` +`Plonk<F>`
[`mina-rust/.../public_input/prepared_statement.rs:14-35`], and the in-circuit `Unfinalized`
[`mina-rust/.../unfinalized.rs:102-116`]. Field-by-field, with where each is **re-checked**:

| Deferred field | what it is | recomputed + checked by (in-circuit / native) |
|---|---|---|
| `plonk = {alpha, beta, gamma, zeta}` | the four Fiat–Shamir IOP challenges | re-squeezed; bound by `assert_eq_plonk` (§B binding) |
| `plonk.{zeta_to_srs_length, zeta_to_domain_size, perm}` | derived scalar exponentiations / perm scalar | `plonk_checks_passed` via `derive_plonk` [`step.rs:874`; `plonk_checks.rs:238-271`; OCaml `wrap_verifier.ml:1028-1037`] |
| `combined_inner_product` | `Σ_i Σ_j r^i ξ^j f_j(pt_i)` | `combined_inner_product_correct` — recompute via `ft_eval0` + fold all evals with ξ [`step.rs:748-845`; OCaml `wrap_verifier.ml:951-1009`]. **Reuses K5 `combinedInnerProduct`/`ftEval0`.** |
| `b` | `challenge_poly(ζ) + r·challenge_poly(ζω)` | `b_correct` [`step.rs:854-862`; OCaml `wrap_verifier.ml:1015-1026`]. **Reuses K4c `bEval` (= `challenge_polynomial`, `wrap_verifier.ml:14-35`).** |
| `xi` | the poly-combining ("polyscale") challenge | `xi_correct = field.equal(squeeze(), xi)` [`step.rs:694-697`; OCaml `wrap_verifier.ml:895-902`] |
| `bulletproof_challenges` | the `k` IPA round challenges | endo-mapped, feed `b_correct`; **cross-checked against the group verifier's** [`step.rs:1759-1772`] |
| `branch_data` *(wrap only)* | `{proofs_verified, domain_log2}` | selects the eval domain; validated in `run_checks` [`step.rs:598-604`; `verification.rs:644-651`] |

### Emit vs re-check (the symmetry — this is the new formal content)

Two `incrementally_verify_proof` (emit) + two `finalize_other_proof` (discharge), one per curve:

- **Wrap.`incrementally_verify_proof`** [`wrap_verifier.ml:501-732`] samples β,γ,α,ζ, builds `ft_comm`,
  runs the IPA **group** check `check_bulletproof`, and **binds** the sampled challenges to the
  exposed deferred `plonk` via `assert_eq_plonk` [`wrap_verifier.ml:492-499`]. → emits the **Step
  proof's Fp** deferred values.
- **Step.`finalize_other_proof`** [`step_verifier.ml:887-1149`; Rust `step.rs:519-887`, AND of the
  four sub-checks at `step.rs:876-884`] recomputes and **discharges** those Fp values (`Shifted_value`
  **Type1** over Fp). → closes the Wrap→Step hop.
- Mirror: **Step.`incrementally_verify_proof`** [`step_verifier.ml:498-517`] emits the **Wrap proof's
  Fq** deferred values; **Wrap.`finalize_other_proof`** [`wrap_verifier.ml:820-1049`, Type2 over Fq]
  discharges them. → closes the Step→Wrap hop.
- **Native mirror (the tip):** `expand_deferred` recomputes, out of circuit, exactly what the next
  circuit would check [OCaml `wrap_deferred_values.ml:19-210`; Rust `step.rs:1915-2072`,
  `verification.rs:676-719`]. This is the concrete reference a Lean deferred-values model must match.

**Reuse payoff:** three of the four `finalize_other_proof` sub-checks are already built — `b_correct`
is K4c `bEval`; `combined_inner_product_correct` is K5 `combinedInnerProduct` + `ftEval0`;
`xi_correct` is one sponge squeeze (K3) + a field equality. The genuinely new work is (a) the
`plonk_checks`/`derive_plonk` scalar derivations, (b) the **binding** (§ next), and (c) the
`Shifted_value` Type1/Type2 encoding that lets an Fp value be carried and compared inside an
Fq-native circuit [OCaml `common.ml:91-103`; `step_verifier.ml:826` / `wrap_verifier.ml:789-791`].

### The binding (why the exposed scalars are sound) — the single hardest piece

The public-input `Deferred_values` are attacker-chosen bytes until they are pinned to the group
sub-verifier. That pinning is: `assert_eq_plonk` (sampled β,γ,α,ζ **=** exposed `plonk`)
[`wrap_verifier.ml:492-499`, called `:717-731`]; the sponge-digest equality [`wrap_main.ml:430-432`];
and the per-round bulletproof-challenge equality [`wrap_main.ml:433-439`; `step_verifier.ml:1271-1285`].
Proving `finalize_other_proof ∧ (these asserts) ⟹ the deferred scalar arithmetic is genuinely the
opposite proof's` — across the non-native field via the shifted-value bridge — is the new soundness
theorem, and the hardest buildable item (P4).

---

## §C — The accumulator / sg bulletproof accumulation (mostly HAVE)

This is the **head start**. The deferred `⟨s,G⟩` MSM (the IPA cost center) is not recomputed each
recursion step; the `k` round challenges are accumulated and the `2^k`-term MSM is discharged once.
The math is exactly **K4c**:

- **`sVec_eq_bPoly`** (`PastaIPA.lean:113`) is the identity `Σ_i (sVec cs)_i · x^i = ∏_j (1 + cs_j
  x^{2^…})` — i.e. the `2^k` s-vector is the b-poly coefficient vector reconstructible from `k`
  challenges. This mirrors `b_poly` [`proof-systems/poly-commitment/src/commitment.rs:426-436`] and
  `b_poly_coefficients` (the `s ↦ s ++ c·s` doubling) [`commitment.rs:464-476`], and proof-systems'
  own consistency test [`commitment.rs:912-939`]. **Pins verified un-drifted at HEAD `f6d958dc05`.**
- The discharge is `sg == MSM(urs.g, b_poly_coefficients(challenges))`, batched across proofs, one
  pairing-free `msm(points, scalars) == 0` [Rust `accumulator_check.rs` (whole, 64 lines) →
  `urs_utils.rs:11-68`, `b_poly_coefficients` at `:54`, `msm == 0` at `:67`; OCaml
  `Ipa.Step.accumulator_check`, `verify.ml:135-143`, `common.ml:197-211`]. In `SRS::verify` the split
  is the `sg` term [`ipa.rs:410-411`] plus `⟨sg_rand·s, G⟩` [`ipa.rs:402,419-424`].
- The deferred obligation carried across recursion is `RecursionChallenge { chals, comm }` —
  "the accumulated commitment `U = ⟨h,G⟩` … the 'deferred' part of IPA verification"
  [`proof-systems/kimchi/src/proof.rs:213-218,225,241,437-442`].

**Residual to close (P1):** K4c proves the *identity* and the *compression* (`deferral_compression`);
what remains is the batching wrapper — the RNG/Fiat–Shamir batching scalars `rs` [`urs_utils.rs:25-32`;
`ipa.rs:356-357`, the `[R-design]` deviation of `KIMCHI-VERIFY-SPEC.md`] and the multi-proof batch —
plus the terminal `msm == 0` itself, which is the inherited IPA/FRI opening-soundness floor (P10),
not dischargeable in-kernel.

---

## §D — Mina's specific instantiation (what verifying a REAL block/tx needs; NEW plumbing)

**The wrap VK = a Kimchi verifier index over Pallas.** `Poly.t = {max_proofs_verified,
actual_wrap_domain_size, wrap_index : Plonk_verification_key_evals, wrap_vk}` [S —
`mina/src/lib/pickles_base/side_loaded_verification_key.ml:140-157`]. `index_to_field_elements`
[`:159-183`] serializes `wrap_index` as **8 commitment groups**: `sigma_comm(7) ++
coefficients_comm(15) ++ [generic; poseidon; complete_add; mul; emul; endomul_scalar]` — these ARE
the wrap verifier index. Reconstruction of the runnable `Impls.Wrap.Verification_key` (Tock/Pallas):
`of_repr` [`mina/src/lib/pickles/side_loaded_verification_key.ml:206-262`] — `max_poly_size = 2^15`
[`:234`], `prev_challenges = 2` ("Wrap_hack", `:236`), `lookup_index = None` [`:255`].

**Domains + widths a verifier must know** [S]: `max_proofs_verified ∈ {0,1,2}`
[`pickles_base/proofs_verified.ml:5-17`], encoded in-circuit as a 2-bit prefix mask or 3-bit one-hot
[`:70-143`]; wrap domain `∈ {2^13, 2^14, 2^15}` keyed by `proofs_verified` (`0→13, 1→14, 2→15`)
[`common.ml:27-45`]; step blinding domain `2^6`, wrap `2^7` [`step_main_inputs.ml:97`,
`wrap_main_inputs.ml:101`]; the wrap statement public-input layout (5 Fp + 2 challenge + 3
scalar-challenge + 3 digest + 16 bulletproof-challenge + 1 branch-data + 8 feature-flag)
[`composition_types.ml:814-943`]; `branch_data` packs `{2-bit proofs_verified, 8-bit domain_log2}`
into one field [`branch_data.ml:45-84,135-136`].

**The real VKs + the tx-snark** [S — mina-rust]: the mainnet/devnet **blockchain** and **transaction**
verifier indices are embedded JSON [`verifiers.rs:176-279`, files `crates/ledger/src/proofs/data/
{mainnet,devnet}_{blockchain,transaction}_verifier_index.json`]; SRS via
`SRS::<Vesta>::create(2^15)` [`verifier/mod.rs:38-45`]. The transaction snark is a **merge tree**: a
base leaf is `InductiveRule::empty` (zero previous proofs) [`transaction.rs:4289`], and `merge_main`
recursively combines two child statements/proofs 2-to-1 [`merge.rs:36`]. The **block** step rule wires
**two** previous proofs — the previous blockchain-state proof and the txn-snark proof —
[`block.rs:1788-1799`], with the genesis base case at `block.rs:1684,1784-1786`.

---

## §E — Base case + inductive structure (NEW gating)

- **Inductive rule** [S — `mina/src/lib/pickles/inductive_rule.ml:9-23,103-120`]:
  `Previous_proof_statement = {public_input; proof; proof_must_verify : Boolean}`; a rule has
  `prevs` (tags of previous proofs) + `main`.
- **Base case = a previous slot with `proof_must_verify = false`, fed a dummy proof.** The verify gate
  is `verified && finalized ||| not should_verify` [OCaml `step_main.ml:121`; Rust
  `step.rs:1893-1894` `verified.and(finalized).or(should_verify.neg())`] — a non-verifying slot passes
  unconditionally. `is_base_case = not should_verify` also **bypasses the bulletproof-challenge
  equality**, substituting the exposed challenge for the recomputed one [`step_verifier.ml:1281`; Rust
  `step.rs:1765-1772,1881`]. Dummy content: `dummy.ml:9-54` (`Ipa.{Wrap,Step}.{challenges,sg}`), Rust
  `unfinalized.rs:286-297,308-368`, `dummy/mod.rs` (`trivial_vk.bin`, `sideloaded_proof.bin`).
- **The tip (end-to-end real verify)** [OCaml `verify.ml:21-213`; Rust `verification.rs:750-785`
  `verify_block`, `:858-896` `verify_impl`]: (1) natively recompute the Tick deferred values
  (`expand_deferred`); (2) `accumulator_check` (the §C sg check on Vesta); (3) reconstruct the wrap
  statement public input and `batch_verify` the **Wrap (Pallas) Kimchi proof**. Steps (2)+(3) are HAVE
  (K4c + K5); step (1) is the NEW deferred-values native mirror.
- **Where `prev_challenges` re-enters native Kimchi verify** (the `prevLen = 0` frontier) [Rust
  `prover.rs:30-177` `make_padded_proof_from_p2p`]: `old_bulletproof_challenges` +
  `challenge_polynomial_commitments` become `RecursionChallenge<Pallas>` folded into the outer proof's
  combined-inner-product relation, padded to 2 (Wrap_hack). With `prev_challenges = 0` this term
  vanishes; modeling the fold + padding is P6.

---

## §7 — The ordered task list (detail: what to build, effort, have-vs-new)

Discipline reminder: **House Law #1** — every constraint/decision below is **Lean-authored** (the
K-lanes are Lean gadgets/`@[export]` decisions; Rust only calls the artifact). None of this is a Rust
AIR. State the substrate out loud at task #1.

**Phase 0 — instantiate the two Kimchi verifiers on both curves (mostly HAVE)**

- **P0 — K5 at the Wrap shape.** *Medium.* Re-instantiate `kimchiVerifyDecision(Field)` for a
  Pallas-committed, Fq-scalar, `k=15` proof (the object a node actually verifies). K5 is field-generic
  so the decision body is reuse; the real work is the **Fq-state Poseidon sponge** (mirror K3 to the
  Fq permutation — `KimchiVerify` §12.3 residual) and a **real Wrap-proof fixture** (extract from a
  mainnet block via mina-rust's `verify_block` path). *Have:* K1(Fq), K2(Vesta/Pallas), K5 body.
  *New:* the Fq sponge instance, the wrap VK domains (§D), the wrap fixture.
- **P1 — Close `accumulator_check`.** *Small–medium.* On top of `sVec_eq_bPoly`/`deferral_compression`,
  add the batching scalars + multi-proof batch to model `batch_dlog_accumulator_check` down to the
  `msm == 0` [`urs_utils.rs:11-68`]. *Have:* the identity (K4c). *New:* the batching wrapper; the
  terminal MSM is the inherited floor (P10).

**Phase 1 — the deferred-values cross-check (the genuinely NEW core)**

- **P2 — The `Deferred_values` data model + shifted-value bridge.** *Small–medium.* The two records
  [`composition_types.ml:215-268,1152-1164`], `Plonk` minimal/in-circuit [`:45-61,102-123`], and the
  `Shifted_value` Type1/Type2 encoding that carries an Fp scalar inside an Fq circuit and back
  [`common.ml:91-103`]. *New*, but pure data + one algebraic encoding.
- **P3 — `finalize_other_proof` (one side).** *Medium.* The four checks discharging the Step proof's
  Fp values inside a Wrap circuit: `xi_correct` (K3 squeeze + eq), `combined_inner_product_correct`
  (**K5** `combinedInnerProduct`+`ftEval0`), `b_correct` (**K4c** `bEval`), `plonk_checks_passed`
  (`derive_plonk` — new scalar derivations) [`wrap_verifier.ml:820-1049`; `step.rs:519-887`]. *Have:*
  3 of 4 check cores. *New:* `derive_plonk`, the assembly, the accept theorem + a tamper falsifier.
- **P4 — The transcript-equality binding (the hardest piece).** *Hard.* `assert_eq_plonk`
  [`wrap_verifier.ml:492-499`] + sponge-digest equality + per-round bulletproof-challenge equality
  [`wrap_main.ml:430-439`; `step_verifier.ml:1271-1285`], proven to pin the public-input deferred
  scalars to the group sub-verifier across the non-native field. This is the soundness of P3 and the
  new formal content with no K5 analog.
- **P5 — Mirror to the other side.** *Small.* Step-discharges-Wrap (Fp↔Fq swap, Type1↔Type2)
  [`step_verifier.ml:887-1149`]. Mechanical once P3/P4 exist.

**Phase 2 — recursion structure + Mina specifics (NEW plumbing)**

- **P6 — `prev_challenges > 0`.** *Medium.* Retire K5's `shapeOk … decide (prevLen = 0)` freeze: fold
  `RecursionChallenge` b-poly evals into the transcript (C3) + `combined_inner_product` (C8), model
  `messages_for_next_{step,wrap}_proof` / `old_bulletproof_challenges` accumulation + Wrap_hack padding
  to 2 [`prover.rs:30-177`; `composition_types.ml:369,819`]. *Have:* K4c b-poly. *New:* the fold + the
  passthrough/accumulation.
- **P7 — Base case + inductive gating.** *Small–medium.* The dummy proof, `is_base_case` bypass,
  `proof_must_verify` gate, genesis base case [`step_main.ml:36-37,106,121`; `dummy.ml`; `block.rs:1684`].
- **P8 — Wrap-VK model + domains.** *Medium.* `index_to_field_elements` (8 commitment groups),
  `of_repr` reconstruction, `wrap_domains` {2^13,2^14,2^15} by `proofs_verified`, the one-hot/prefix
  masks, `branch_data` packing [`side_loaded_verification_key.ml`; `proofs_verified.ml`;
  `common.ml:27-45`; `branch_data.ml`]. Mechanical serialization + domain selection.
- **P9 — Mina's concrete instantiation.** *Medium–large.* Load the real mainnet/devnet blockchain +
  transaction verifier indices [`verifiers.rs:176-279`, `data/*.json`]; model the tx-snark merge tree
  (`InductiveRule::empty` leaf + `merge_main`) and the block step rule (2 prevs); hash the protocol
  state; wire the tip `verify_block` = `accumulator_check` (P1) + native Wrap verify (P0)
  [`verification.rs:750-785`]. Lots of concrete plumbing, each piece mechanical; this is what makes it
  a real **Mina light client** (and, per `MINA-KIMCHI-VERIFIER-PLAN.md`, transitively any chain
  settling a Kimchi proof to Mina).

**Phase 3 — the terminal floor**

- **P10 — The IPA/FRI opening-soundness floor.** *Not built — inherited.* `msm == 0` [`ipa.rs:501`]
  is the same undischarged floor `KimchiVerify` §12.1 and every STARK-backed light client carries. It
  is the honest terminal residual, named — not a task with an effort.

---

## §8 — Honesty ledger (what this doc does and does not claim)

- The **arithmetic floor for both Step and Wrap already exists** (K1 both fields, K2 both curves,
  K4a/b both curves) — the two-curve requirement is *instantiation*, not new algebra. The one
  arithmetic gap is K3's Fq-state sponge (P0), already a named residual.
- The **sg-accumulation math is proven** (K4c `sVec_eq_bPoly`); `accumulator_check` is a batching
  wrapper (P1) over it plus the inherited terminal MSM (P10).
- The **genuinely new work is recursion glue** — the deferred-values cross-check (P2–P5), the
  `prev_challenges` fold (P6), the base case (P7), the wrap-VK/domains (P8), and Mina's concrete
  wiring (P9). Of these, the **binding that makes the cross-check sound (P4) is the single hardest**
  buildable piece.
- Nothing here discharges the terminal IPA/FRI opening-soundness floor (P10). "Verifies a real Mina
  block" end-to-end still rests on it, exactly as the single-proof `KimchiVerify` does. Describe any
  Pickles verify at that resolution.
