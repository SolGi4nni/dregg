# The PQ axiom picture — re-measured, verbatim

**Measured on hbox 2026-07-24**, Lean `leanprover/lean4:v4.30.0`, against
`~/dev/breadstuffs/metatheory` at the tree that follows the "the LAST `native_decide` is GONE"
Keccak commit. Every line in the tables below is a *transcription of real `#print axioms` output*
that is reproduced verbatim in the appendix — nothing here is copied from a prior claim.

Reproduce with:

```
export PATH=$HOME/.elan/bin:$HOME/.cargo/bin:$PATH
export HACL_DIST=$HOME/src/hacl-star/dist/gcc-compatible
export LIBRARY_PATH=$HACL_DIST
cd ~/dev/breadstuffs/metatheory
SWARM_MEM_MAX=64G swarm-build lake build \
  Dregg2.Crypto.Keccak.Fips202SpongeRefine Dregg2.Crypto.MlKemKeygenRefine \
  Dregg2.Crypto.MlDsaKeygenRefine Dregg2.Crypto.VerifyCoreHashFrame \
  Dregg2.Crypto.MlKemKeygenAcvp Dregg2.Crypto.MlKemEncapsAcvp \
  Dregg2.Crypto.MlDsaKeygenAcvp Dregg2.Crypto.MlDsaSigGenAcvp Dregg2.Crypto.MlDsaSigVerAcvp
SWARM_MEM_MAX=64G swarm-build lake env lean AxiomProbe.lean
```

> ⚠ **The cap was `24G` here until 2026-07-25, and it was killing these exact builds.**
> A census of hbox's user journal found **198 `oom-kill` events** between 07-17 and 07-24.
> Across 3111 scopes that reported a memory peak, **every one of the 67 killed scopes
> peaked at exactly a cap value** (`24G`×60, `32G`×5, `40G`, `70G`) and **not one of the
> 3044 survivors exceeded ~14G** — so the killer was always the per-build cap, never box
> pressure. The `24G` line above is where 60 of those came from: this file presents itself
> as *the* reproduce recipe, so every lane that needed these modules copy-pasted a cap
> that `MlDsaKeygenRefine`, `MlKemKeygenRefine` and `VerifyCoreArgAssembly` genuinely
> exceed. On 07-24 one lane retried the same killed `lake build` nine times in 32 minutes,
> because `swarm-build` surfaced the kill as an ordinary nonzero status — indistinguishable,
> from inside a lane, from a proof error. `scripts/pbuild` now reports that case as
> `VERDICT outcome=ENVFAULT` with the journal line as evidence.
>
> If you narrow this to a single module you can lower the cap again — but **measure it**
> (`systemctl --user show <scope> -p MemoryPeak`, or read the `memory peak` line
> `journalctl --user` prints when the scope exits) rather than inheriting a number.

`clean` below means the axiom set is **exactly** `[propext, Classical.choice, Quot.sound]` — the
three standard Lean kernel axioms, which is the corpus definition of clean (`docs/AXIOM-HYGIENE.md`,
`Dregg2.cleanAxioms`).

---

## 0. READ THIS FIRST — how `native_decide` shows up in Lean 4.30

Do **not** grep for `Lean.ofReduceBool` to decide whether compiled-evaluation trust is present.
In this toolchain `native_decide` no longer surfaces those names. It mints a **per-declaration**
axiom instead. Checked directly on hbox:

```
theorem tiny_nd : (List.range 3).all (fun x => x < 3) = true := by native_decide
#print axioms tiny_nd
-- 'tiny_nd' depends on axioms: [tiny_nd._native.native_decide.ax_1_1]
```

`Lean.ofReduceBool` and `Lean.trustCompiler` still *exist* as constants in the toolchain
(`axiom Lean.ofReduceBool : ∀ (a b : Bool), Lean.reduceBool a = b → a = b`;
`axiom Lean.trustCompiler : True`), they are simply not what `native_decide` emits any more.

**So the load-bearing signal is: does the axiom set contain any `…._native.native_decide.ax_*`
name at all?** A theorem whose set is exactly the clean triple has *no* compiled-evaluation trust,
transitively — `collectAxioms` is transitive, so this cannot be hidden one import down.

That is the sense in which the Keccak chain is axiom-clean below, and it is the stronger reading,
not the weaker one.

---

## 1. Keccak / FIPS 202 refinement chain — ALL CLEAN

The executable Keccak (`Dregg2.Crypto.Keccak`) provably refines the FIPS 202 bit-level spec
(`Keccak.Fips202`), with **no compiled-evaluation trust anywhere in the chain**.

| theorem | shape | axioms | clean? |
|---|---|---|---|
| `Keccak.Fips202Lfsr.rc_lanes_all` | closed finite (24×64 bits), kernel `decide` | `[propext, Classical.choice, Quot.sound]` | ✅ |
| `Keccak.Fips202Refine.rc_lanes_eq_exec` | closed finite; proof is `rc_lanes_all` | `[propext, Classical.choice, Quot.sound]` | ✅ |
| `Keccak.Fips202Round.keccakRound_refines_spec` | `∀ a ir, a.size = 25 → …` | `[propext, Classical.choice, Quot.sound]` | ✅ |
| `Keccak.Fips202Round.keccakF_refines_spec` | `∀ a, a.size = 25 → …` | `[propext, Classical.choice, Quot.sound]` | ✅ |
| `Keccak.Fips202SpongeRefine.absorb_refines_spec` | `∀ rate padded, …` | `[propext, Classical.choice, Quot.sound]` | ✅ |
| `Keccak.Fips202SpongeRefine.squeeze_refines_spec` | `∀ rate s0 outLen, …` | `[propext, Classical.choice, Quot.sound]` | ✅ |
| `Keccak.Fips202SpongeRefine.sponge_refines` | proof of `Fips202Refine.SpongeRefinesObligation` | `[propext, Classical.choice, Quot.sound]` | ✅ |

**What this buys.** SHAKE256/SHAKE128 as *deployed* provably equal the FIPS 202 sponge as
*specified*, with the kernel as the only checker. The round-constant table — historically the one
`native_decide` in the stack — is now checked by a kernel `decide` on top of two genuine `∀`
bridges (`rcBit_eq_rcBitRec`, `rcLaneOf_eq_rcLaneOfRec`) that replace FIPS 202 Algorithm 5's
well-founded `Std.Legacy.Range` do-loop, which the kernel cannot unfold, by a structurally
recursive twin.

**Honest scope.** `rc_lanes_eq_exec` is still a claim about **24 specific constants**, not a `∀`.
It is finite-but-kernel-checked, which is a strictly different (and better) thing from
finite-and-compiler-checked. The `∀` form is `Fips202Lfsr.round_constants_are_lfsr`.
Cross-check: `grep -c "by native_decide"` over `Fips202Lfsr.lean`, `Fips202Round.lean`,
`Fips202Refine.lean`, `Fips202SpongeRefine.lean` is **0** — every occurrence of the string
`native_decide` in those four files is prose.

---

## 2. Key generation refinements — CLEAN, and two of them UNCONDITIONAL

| theorem | shape | axioms | clean? |
|---|---|---|---|
| `MlKemKeygenRefine.kpkeKeyGen_refines_ring` | `∀ (d : List UInt8)`, **unconditional** | `[propext, Classical.choice, Quot.sound]` | ✅ |
| `MlKemKeygenRefine.kpkeKeyGen_refines_ring_of_rholen` | `∀ d`, hyp `(rhoOf d).length = 32` | `[propext, Classical.choice, Quot.sound]` | ✅ |
| `MlDsaKeygenRefine.mldsaKeygen_pk_refines_ring` | `∀ (xi : List UInt8)`, **unconditional** | `[propext, Classical.choice, Quot.sound]` | ✅ |
| `MlDsaKeygenRefine.mldsaKeygen_refines_ring` | `∀ xi`, hyp `hS : ExpandSSized xi` | `[propext, Classical.choice, Quot.sound]` | ✅ |

`kpkeKeyGen_refines_ring` is the `_of_rholen` form with the side condition **discharged** by
`rhoOf_length d`, so it holds for every byte list with no hypothesis at all. Likewise
`mldsaKeygen_pk_refines_ring` is a plain `∀ xi` — the deployed `mldsaKeygenInternal xi` public key,
byte-decoded, *is* the ring-level `(ρ, t₁)`.

**The one place a witness is needed, named explicitly:** `mldsaKeygen_refines_ring` still carries
the typed hypothesis `hS : ExpandSSized xi` (the `ExpandS` output is correctly sized). The concrete
witness that this is inhabited, `MlDsaKeygenRefine.expandS_sized_witness`, is a **single-input**
`native_decide` and is reported as such:

```
'Dregg2.Crypto.MlDsaKeygenRefine.expandS_sized_witness' depends on axioms: [propext,
 Quot.sound,
 Dregg2.Crypto.MlDsaKeygenRefine.expandS_sized_witness._native.native_decide.ax_1_1]
```

That is a **non-vacuity witness**, not the theorem. `ExpandSSized` for all `ξ` is OPEN.

---

## 3. ML-DSA verify — hash framing CLEAN, argument leg still a typed hypothesis

| theorem | shape | axioms | clean? |
|---|---|---|---|
| `Fips204ChallengeHash.challengeHash_frames` | `∀`, hyp `SpongeRefinesObligation` | `[propext, Classical.choice, Quot.sound]` | ✅ |
| `Fips204ChallengeHash.challengeHash_frames_deployed` | `∀`, sponge **discharged** | `[propext, Classical.choice, Quot.sound]` | ✅ |
| `VerifyCoreHashFrame.hashFrame` | `∀`, hyp `SpongeRefinesObligation` | `[propext, Classical.choice, Quot.sound]` | ✅ |
| `VerifyCoreHashFrame.hashFrame_deployed` | `∀`, sponge **discharged** | `[propext, Classical.choice, Quot.sound]` | ✅ |
| `VerifyCoreHashFrame.challengeMatches_eq_specHash` | `∀`, hyps `hSponge`, `hArg` | `[propext, Classical.choice, Quot.sound]` | ✅ |
| `VerifyCoreHashFrame.verifyCore_eq_specVerifyB` | `∀`, hyps `hSponge`, `hh`, `hnorm`, `hArg` | `[propext, Classical.choice, Quot.sound]` | ✅ |
| `VerifyCoreHashFrame.verifyCore_eq_specVerifyB_deployed` | `∀`, hyps `hh`, `hnorm`, `hArg` (sponge **discharged**) | `[propext, Classical.choice, Quot.sound]` | ✅ |
| `VerifyCoreEqSpec.w1Row_recovers_arg` | `∀`, per-coefficient argument leg | `[propext, Classical.choice, Quot.sound]` | ✅ |

**The `_deployed` corollaries are now exactly as clean as the hypothesis forms.** Before the Keccak
work they inherited a compiled-evaluation residual through `sponge_refines → rc_lanes_eq_exec`; they
no longer inherit anything. Five prose sites in `Fips204ChallengeHash.lean` and
`VerifyCoreHashFrame.lean` still claimed that residual was live and were corrected on 2026-07-24;
they were wrong in the *conservative* direction (over-claiming trust, not under-claiming it).

**What is still OPEN, named:** `verifyCore_eq_specVerifyB_deployed` remains **conditional on
`hArg`** — that the value verify hashes is `UseHint(h, A·z − c·t₁·2^d)` assembled across all six
rows. The per-coefficient leg is closed (`w1Row_recovers_arg`, `∀`, clean); the six-row `w1Encode`
assembly is not. `hArg` is a signature in the symbol table, not a paragraph. `hnorm` and `hh` are
likewise typed side conditions. **These theorems are NOT a full "deployed verify = FIPS 204
verify".**

Also note `#assert_axioms` is deliberately *not* applied to the `_deployed` corollaries; they are
reported by `#print axioms` in the build log so that a regression in the Keccak floor shows up
loudly here instead of being silently inherited. That is now a live tripwire rather than a
concession.

---

## 4. Deployed-core ACVP KATs — ALL carry `native_decide`, and that is EXPECTED

Every one of these is a **finite check against published NIST ACVP vectors**, not a `∀`. They are
evidence that the deployed pipeline reproduces NIST's bytes; they are not refinement theorems and
they are not `#assert_axioms`-pinned.

| theorem | what it checks | extra axiom beyond the clean set |
|---|---|---|
| `MlKemKeygenAcvp.keygen_matches_acvp_tc26` | ML-KEM-768 keyGen tc26, `ek`+`dk` byte-for-byte | `…keygen_matches_acvp_tc26._native.native_decide.ax_1_1` |
| `MlKemKeygenAcvp.keygen_matches_acvp_tc27` | ML-KEM-768 keyGen tc27 | `…keygen_matches_acvp_tc27._native.native_decide.ax_1_1` |
| `MlKemEncapsAcvp.encaps_matches_acvp_group` | all 25 ACVP encaps vectors | `…encaps_matches_acvp_group._native.native_decide.ax_1_1` |
| `MlKemEncapsAcvp.encaps_decaps_roundtrip_acvp_group` | decaps of NIST `dk` over produced ct recovers NIST `k`, 25 vectors | `…encaps_decaps_roundtrip_acvp_group._native.native_decide.ax_1_1` |
| `MlDsaKeygenAcvp.keygen_matches_acvp_tc26` | ML-DSA-65 keyGen tc26, `pk`+`sk` | `…keygen_matches_acvp_tc26._native.native_decide.ax_1_1` |
| `MlDsaSigGenAcvp.sign_matches_acvp_group` | ACVP sigGen group | `…sign_matches_acvp_group._native.native_decide.ax_1_1` |
| `MlDsaSigGenAcvp.sign_verify_agree_acvp_group` | sign/verify agreement over the group | `…sign_verify_agree_acvp_group._native.native_decide.ax_1_1` |
| `MlDsaSigVerAcvp.verifyCore_matches_acvp_sigVer` | 15 ACVP sigVer vectors (3 accept, 12 reject) | `…verifyCore_matches_acvp_sigVer._native.native_decide.ax_1_1` |

Note `MlKemEncapsAcvp` / `MlDsaSigGenAcvp` / `MlDsaSigVerAcvp` also carry `Classical.choice`;
`MlKemKeygenAcvp` / `MlDsaKeygenAcvp` do not. Neither fact matters for assurance — the
`._native.` axiom is what is doing the trusting.

**Is that OK?** Yes, *provided nobody calls them refinement*:

* Each is a **single-vector or single-group KAT**. It quantifies over nothing. A KAT cannot be
  stated without evaluating the implementation, so compiled evaluation is intrinsic to the claim,
  not an artifact of a lazy proof.
* Their assurance value is **anti-vacuity and interop**: they rule out a pipeline that is
  self-consistently wrong, and they pin the byte-level conventions (domain separation, encode
  order, the `dk = dkPKE ‖ ek ‖ H(ek) ‖ z` wrapper) against an *external* authority — NIST's
  published expected values, not any Rust crate's output.
* They are **not** on the assurance path for any `∀` statement. No theorem in §1–§3 imports their
  axiom. That is checkable: every §1–§3 row above is the bare clean triple.

**Not OK would be:** a `∀`-shaped refinement theorem discharged by `native_decide`, or a KAT
described as if it were a refinement. Neither is present.

---

## 5. Deliberate non-vacuity witnesses — `native_decide` by design

These exist to prove the corresponding `∀`-theorems are not vacuous. They are witnesses, **not**
foralls, and they are deliberately not gated.

| witness | pairs with | extra axiom |
|---|---|---|
| `Keccak.shake256_empty_kat` | the FIPS 202 spec sponge (spec-side anchor `spec_SHAKE256_empty_cavp`) | `…shake256_empty_kat._native.native_decide.ax_1_1` |
| `MlKemRing.nttLeftInverse_sample` | `intt ∘ ntt = id` on canonical polys (the `∀` is clean) | `…nttLeftInverse_sample._native.native_decide.ax_1_1` |
| `MlKemRing.nttMulHom_sample` | `ntt (schoolbookMul a b) = pointwiseNtt (ntt a) (ntt b)` (the `∀` is clean) | `…nttMulHom_sample._native.native_decide.ax_1_1` |
| `MlDsaKeygenRefine.expandS_sized_witness` | inhabits `ExpandSSized` for `mldsaKeygen_refines_ring`'s hypothesis | `…expandS_sized_witness._native.native_decide.ax_1_1` |

`shake256_empty_kat` is the NIST CAVP `SHAKE256("")` answer computed on the **deployed** side; the
spec side has its own independent anchor, so the two meet without either being assumed.

---

## 6. Summary of the assurance floor

* **Clean, `∀`, no compiled-evaluation trust:** the entire FIPS 202 refinement chain; both
  key-generation refinements (two of them unconditional); the whole ML-DSA verify hash-framing
  chain; the per-coefficient `useHint` argument leg. **19 theorems, measured** (7 + 4 + 8).
* **Named OPEN obligations** (typed hypotheses, not prose): `hArg` (six-row `w1Encode` argument
  assembly) and `hnorm`/`hh` in ML-DSA verify; `ExpandSSized` for all `ξ` in ML-DSA keygen.
  `Fips202Refine.RoundCompositionObligation` is discharged only in its `ir < 24` specialization
  (`keccakRound_refines_spec_RC`) — as literally written it quantifies `ir` over all of `ℕ`, where
  both sides diverge (`RC[ir]! = 0` vs. a genuine LFSR lane), so the literal `∀ ir : ℕ` form is not
  a statement anyone should want.
* **`native_decide` remains, in exactly two categories, both of which are finite by construction:**
  ACVP KATs (§4) and non-vacuity witnesses (§5). No `∀`-theorem depends on either.
* **Below all of it** sits the ordinary un-formalized floor this document does not address: the
  cryptographic hardness assumptions (MLWE/MSIS, SHAKE collision resistance), the Lean kernel and
  compiler, and — where the FFI path is exercised — the C toolchain. Cite FIPS 202 / FIPS 203 /
  FIPS 204 for the specs; the transcription of the standard into `Fips202Spec` / `Fips203Kem` /
  `Fips204Spec` is a reading a human must diff, and no theorem can establish it.

---

## 7. Prose corrected, and prose still known-stale

**Corrected 2026-07-24** (prose only; no theorem statement was touched):

| file | line (pre-edit) | was | now |
|---|---|---|---|
| `Fips204ChallengeHash.lean` | ~62 (`## Axioms` header block) | "inherits … the ONE pre-existing `Lean.ofReduceBool` residual of the whole Keccak stack" | Keccak chain is axiom-clean; `rc_lanes_eq_exec` is a kernel `decide`; measured axiom set quoted |
| `Fips204ChallengeHash.lean` | ~165 (`challengeHash_frames_deployed` docstring) | "AXIOM NOTE … this corollary carries `Lean.ofReduceBool`" | "AXIOM NOTE (measured) … this corollary is axiom-CLEAN"; explains the finite-but-kernel-checked step |
| `VerifyCoreHashFrame.lean` | ~65 (header bullet) | `_deployed` corollaries "inherit the Keccak floor's single compiled-evaluation residual" | discharge is free; corollaries measure the clean triple |
| `VerifyCoreHashFrame.lean` | ~353 (`_deployed` section header) | "They inherit the Keccak floor's single compiled-evaluation residual" | "They inherit NOTHING extra"; explains why `#print axioms` is kept as a tripwire |
| `VerifyCoreHashFrame.lean` | ~415 (trailing comment) | "the `_deployed` corollaries inherit the Keccak floor's one compiled-evaluation residual" | states they no longer do, with the measured axiom set |

All five were wrong in the **conservative** direction — they claimed more trusted base than the
artifact actually has. That is the safe way to be wrong, and it is still wrong.

**Known-stale, NOT corrected here** (different owner, flagged for a later pass):

* `Keccak/Fips202Refine.lean:174` — section header `## The OPEN obligations — stated exactly,
  discharged NOWHERE.` The module's own header at lines 43–47 already says the opposite and is
  correct: all three are discharged downstream.
* `Keccak/Fips202Refine.lean:183` — `KeccakFRefinesObligation` docstring says "NOT proven"; it is
  proven, by `Fips202Round.keccakF_refines_spec`.
* `Keccak/Fips202Refine.lean:176-177` — `RoundCompositionObligation` docstring says "NOT proven".
  Defensible as literally written (see §6) but misleading without the `ir < 24` caveat.

---

## Appendix — verbatim `#print axioms` output

Produced by `lake env lean AxiomProbe.lean` on hbox, 2026-07-24. Zero errors, and the preceding
`lake build` reported `Build completed successfully (8535 jobs).`

```
'Dregg2.Crypto.Keccak.Fips202Refine.rc_lanes_eq_exec' depends on axioms: [propext, Classical.choice, Quot.sound]
'Dregg2.Crypto.Keccak.Fips202Lfsr.rc_lanes_all' depends on axioms: [propext, Classical.choice, Quot.sound]
'Dregg2.Crypto.Keccak.Fips202Round.keccakRound_refines_spec' depends on axioms: [propext, Classical.choice, Quot.sound]
'Dregg2.Crypto.Keccak.Fips202Round.keccakF_refines_spec' depends on axioms: [propext, Classical.choice, Quot.sound]
'Dregg2.Crypto.Keccak.Fips202SpongeRefine.absorb_refines_spec' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Dregg2.Crypto.Keccak.Fips202SpongeRefine.squeeze_refines_spec' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Dregg2.Crypto.Keccak.Fips202SpongeRefine.sponge_refines' depends on axioms: [propext, Classical.choice, Quot.sound]
'Dregg2.Crypto.MlKemKeygenRefine.kpkeKeyGen_refines_ring' depends on axioms: [propext, Classical.choice, Quot.sound]
'Dregg2.Crypto.MlKemKeygenRefine.kpkeKeyGen_refines_ring_of_rholen' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Dregg2.Crypto.MlDsaKeygenRefine.mldsaKeygen_pk_refines_ring' depends on axioms: [propext, Classical.choice, Quot.sound]
'Dregg2.Crypto.MlDsaKeygenRefine.mldsaKeygen_refines_ring' depends on axioms: [propext, Classical.choice, Quot.sound]
'Dregg2.Crypto.MlDsaKeygenRefine.expandS_sized_witness' depends on axioms: [propext,
 Quot.sound,
 Dregg2.Crypto.MlDsaKeygenRefine.expandS_sized_witness._native.native_decide.ax_1_1]
'Dregg2.Crypto.VerifyCoreHashFrame.verifyCore_eq_specVerifyB' depends on axioms: [propext, Classical.choice, Quot.sound]
'Dregg2.Crypto.VerifyCoreHashFrame.verifyCore_eq_specVerifyB_deployed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Dregg2.Crypto.VerifyCoreHashFrame.hashFrame' depends on axioms: [propext, Classical.choice, Quot.sound]
'Dregg2.Crypto.VerifyCoreHashFrame.hashFrame_deployed' depends on axioms: [propext, Classical.choice, Quot.sound]
'Dregg2.Crypto.VerifyCoreHashFrame.challengeMatches_eq_specHash' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Dregg2.Crypto.Fips204ChallengeHash.challengeHash_frames' depends on axioms: [propext, Classical.choice, Quot.sound]
'Dregg2.Crypto.Fips204ChallengeHash.challengeHash_frames_deployed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Dregg2.Crypto.VerifyCoreEqSpec.w1Row_recovers_arg' depends on axioms: [propext, Classical.choice, Quot.sound]
'Dregg2.Crypto.MlKemKeygenAcvp.keygen_matches_acvp_tc26' depends on axioms: [propext,
 Quot.sound,
 Dregg2.Crypto.MlKemKeygenAcvp.keygen_matches_acvp_tc26._native.native_decide.ax_1_1]
'Dregg2.Crypto.MlKemKeygenAcvp.keygen_matches_acvp_tc27' depends on axioms: [propext,
 Quot.sound,
 Dregg2.Crypto.MlKemKeygenAcvp.keygen_matches_acvp_tc27._native.native_decide.ax_1_1]
'Dregg2.Crypto.MlKemEncapsAcvp.encaps_matches_acvp_group' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Dregg2.Crypto.MlKemEncapsAcvp.encaps_matches_acvp_group._native.native_decide.ax_1_1]
'Dregg2.Crypto.MlKemEncapsAcvp.encaps_decaps_roundtrip_acvp_group' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Dregg2.Crypto.MlKemEncapsAcvp.encaps_decaps_roundtrip_acvp_group._native.native_decide.ax_1_1]
'Dregg2.Crypto.MlDsaKeygenAcvp.keygen_matches_acvp_tc26' depends on axioms: [propext,
 Quot.sound,
 Dregg2.Crypto.MlDsaKeygenAcvp.keygen_matches_acvp_tc26._native.native_decide.ax_1_1]
'Dregg2.Crypto.MlDsaSigGenAcvp.sign_matches_acvp_group' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Dregg2.Crypto.MlDsaSigGenAcvp.sign_matches_acvp_group._native.native_decide.ax_1_1]
'Dregg2.Crypto.MlDsaSigGenAcvp.sign_verify_agree_acvp_group' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Dregg2.Crypto.MlDsaSigGenAcvp.sign_verify_agree_acvp_group._native.native_decide.ax_1_1]
'Dregg2.Crypto.MlDsaSigVerAcvp.verifyCore_matches_acvp_sigVer' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Dregg2.Crypto.MlDsaSigVerAcvp.verifyCore_matches_acvp_sigVer._native.native_decide.ax_1_1]
'Dregg2.Crypto.Keccak.shake256_empty_kat' depends on axioms: [propext,
 Quot.sound,
 Dregg2.Crypto.Keccak.shake256_empty_kat._native.native_decide.ax_1_1]
'Dregg2.Crypto.MlKemRing.nttLeftInverse_sample' depends on axioms: [propext,
 Quot.sound,
 Dregg2.Crypto.MlKemRing.nttLeftInverse_sample._native.native_decide.ax_1_1]
'Dregg2.Crypto.MlKemRing.nttMulHom_sample' depends on axioms: [propext,
 Quot.sound,
 Dregg2.Crypto.MlKemRing.nttMulHom_sample._native.native_decide.ax_1_1]
```

The probe that produced this is `metatheory/AxiomProbe.lean`.
