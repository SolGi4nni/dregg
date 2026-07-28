# ADVERSARIAL AUDIT — the Mina/Kimchi verifier stack (K1–K6 + the reality gate)

**Scope.** Twelve commits, 2026-07-26/27: `1ba1d6613` `6a3ff11ab` `4a39a1e3b` (kimi) ·
`fbdfad15c` `0d0c71284` `6eb283421` `78ae2edf7` `38d64b233` `7f42aa143` `6705d1bd4`
`08792300c` `0fe996ebe`. Files: `metatheory/Dregg2/Circuit/Emit/Pasta{Field,Curve,Poseidon,
CurveComplete,ScalarMul,IPA}.lean`, `KimchiVerify.lean`, `KimchiRealProofGate.lean`,
`MinaStateQuery.lean`, `metatheory/kimchi_real_proof.json`, `docs/MINA-REALITY-GATE.md`.

**Method.** Theorem STATEMENTS read, not names. Every numeric constant re-derived in Python from
the upstream source (`~/dev/proof-systems`, `~/dev/mina`). The reality-gate fixture recomputed
end-to-end from `kimchi/src/verifier.rs` and `poly-commitment/src/commitment.rs`. The Poseidon
reference re-implemented from the RUST constants and diffed against the Lean's. Agent transcripts
(`cv`, `~/.kimi-code/logs/`, both session scratchpads) spelunked for wall-then-workaround.

**Read-only.** Nothing was fixed. Note the tree moved during the audit: `835db56c6` landed after
`0fe996ebe` and rewrites `KimchiVerify` §9c/§12; in-scope verdicts are against the file states at
`0fe996ebe`, with out-of-scope observations flagged as such.

---

## Verdict summary

| Commit | Verdict | Worst defect |
|---|---|---|
| `1ba1d6613` K1 PastaField (kimi) | **CLEAN** | (KAT-weight nit F16) |
| `6a3ff11ab` K2 PastaCurve+endo (kimi) | **CLEAN** | asymmetric axiom pins (F14) |
| `4a39a1e3b` K3 PastaPoseidon (kimi) | **SIN — SEV 1** | F1: sponge double-permutes on even input; header's "ALL NINE" is false |
| `fbdfad15c` K4a RCB complete-add | **CLEAN** | — |
| `0d0c71284` K4b scalar-mul ladder | **CLEAN** | — |
| `6eb283421` K4c PastaIPA | **SIN — SEV 3** | F8: `deferral_compression` is a definitional tautology |
| `78ae2edf7` K5 KimchiVerify | **SIN — SEV 3** | F8 (`deferral_records`), F12 orphaned from every build target |
| `38d64b233` K6 MinaStateQuery | **SIN — SEV 1** | F2: all three CR floors are PROVABLY FALSE ⇒ every payoff theorem vacuous. Plus F3, F4, F7 |
| `7f42aa143` reality gate | **SIN — SEV 3** | F10: doc says the extractor is "committed in that repo"; it is untracked. Core result is GENUINE |
| `6705d1bd4` C4–C8 over ZMod pN | **SIN — SEV 2** | F5: no consistency binding between C8's eval vector and C5's eval arguments |
| `08792300c` C6 gate + C3 Fr-sponge | **SIN — SEV 2** | F6 carrier widened not retired; F9 two theorems silently demoted to toy `#guard`s |
| `0fe996ebe` docs | **CLEAN** (inherits F6/F9 wording) | — |

**Real findings: 19** — 4 material (F1–F4, two of them SEV 1), 3 structural (F5–F7),
12 hygiene/provenance/KAT-weight.

**The headline is not fake.** The reality gate's core claim survived every check I could throw at
it (§A). The two SEV-1 wounds are both in the *Mina-side* leg (K3's sponge scheduling and K6's
crypto floors), not in the Kimchi-verifier arithmetic.

---

## A. What I verified as GENUINE (so the SINs below are readable at the right resolution)

These are the checks that could have gone red and did not.

1. **`pN` / `qN` and their curve roles.** `PastaField.lean:123,131` match
   `curves/src/pasta/fields/fp.rs:9` / `fq.rs:9` digit-for-digit; `pN` = Pallas `BaseField`
   (`pallas.rs:21`) = Vesta `ScalarField` (`vesta.rs:22`), exactly as the header says. Both
   `= 2^254 + <claimed offset>`, both 255-bit, limb encodings reproduce. (o1-labs' naming trap —
   `fp.rs` calls its config `FqConfig` — was read through correctly.)

2. **Endo scalars ζp, ζq, λ_Pallas, λ_Vesta** (`PastaCurve.lean:113,118,124,128). Re-derived from
   the *recipe*, not the values: `sponge.rs:110-114` `GENERATOR^((|F|−1)/3)` with `GENERATOR = 5`
   (`fp.rs:10`, `fq.rs:10`) — cited line numbers are exact. I then RAN `ipa.rs:214-231`'s
   disambiguation branch: for Pallas `[ζq]G ≠ φ(G)` but `[ζq²]G = φ(G)`; same for Vesta. The
   Lean's "the square for both curves" is correct **and** non-trivial. Independently corroborated
   against Mina OCaml's hardcoded vectors (`~/dev/mina/src/lib/crypto/kimchi_bindings/js/test/
   bindings_js_test.ml:509,514,587,592`) — all four match.

3. **Poseidon parameters.** Width 3 / rate 2 / capacity 1 / α = 7 / 55 full / 0 partial / full MDS /
   **`PERM_INITIAL_ARK = false`** all match `poseidon/src/constants.rs:32-40`. Round order
   (S-box → MDS → add RC) matches `permutation.rs:55-70`. **All 9 MDS entries and all 165 round
   constants are byte-identical to `poseidon/src/pasta/fp_kimchi.rs`** (I extracted both sides and
   compared as integer lists: 0 mismatches). 55 rows is right, not 56 — 56 would be the
   initial-ARK shape. `mdsN[0][0]` is `fp_kimchi`, not `fq_kimchi` — the right field.

4. **The gold Poseidon vectors are real.** I implemented Poseidon in Python *from the Rust
   constants and the Rust `full_round`* and reproduced all seven `#guard`ed vectors
   (`PastaPoseidon.lean:686-698`) exactly. (This is what makes F1 provable rather than a suspicion.)

5. **RCB `b3 = 15`** (`PastaCurveComplete.lean:72`) — derived as `3 * curveB`, `#guard`ed at 15,
   and *uniquely* right: transcribed into Python, RCB Alg. 7 reproduces the group law on both
   curves at `b3 = 15` and fails at 3, 5, 10.

6. **The reality-gate fixture is a real prover run, not synthesized.** `metatheory/kimchi_real_proof.json`
   satisfies simultaneously: `alpha0 = α^21`, `alpha1 = α^22`, `alpha2 = α^23` (exactly the
   `ArgumentType::Permutation` alpha block); `ω` has multiplicative order exactly 32;
   `w_zk = ω^(n−3)`; `denominator = (ζ−ω^{n−3})(ζ−1)` and `denominator·denom_inv = 1`;
   `shift[0] = 1`; β,γ < 2^128 while α,ζ,v,u > 2^128; all 16 IPA prechallenges < 2^128. Hand-built
   data does not satisfy those at once. The extractor
   (`~/dev/proof-systems/kimchi/examples/reality_gate_export.rs`) calls the real
   `ProverProof::create` and the real `kimchi::verifier::verify(...).expect(...)`; the log
   spelunk re-ran it and captured `[ground truth] real verifier ACCEPTED the real proof`.

7. **The reality gate's arithmetic differentials are genuine.** From the fixture alone I
   recomputed, in Python, straight from `verifier.rs:412-489`: `ft_eval0` — **matches Rust's**.
   From `commitment.rs`'s `combined_inner_product` semantics: `cip` — **matches Rust's**. And
   `genSel·(c1 + α·c2)` — **matches Rust's `PolishToken::evaluate(constant_term)`**. So
   `c5_ft_real_matches`, `c8_real_matches` and `generic_gate_matches_lct` are real differentials
   against o1-labs' own verifier, not self-consistency. The Lean's `ftEval0` transcription is
   term-for-term faithful (zip-truncation to 6 σ-terms and 7 shift-terms, `index.w() = ω^{n−3}`,
   the `−p(ζ)` / `−denomFold` / `+numerator·denomInv` / `−linConstTerm` order — all correct).

8. **All 30 Lean literals match the JSON.** I parsed `KimchiRealProofGate.lean`'s `OMEGA ZETA BETA
   GAMMA ALPHA VV UU A0 A1 A2 PZ ZZ ZZW LCT DINV DENOM FT0 CIP SHIFT WZ SZ EVZ EVZW IPACHALS FT1_N
   PZ_N PZW_N N GENSEL COEFFZ` and compared against `kimchi_real_proof.json`: **0 mismatches**,
   including `GENSEL == EVZ[3]` and `COEFFZ == EVZ[24:39]`.

9. **`real_field_decision_accepts` really is over the real field.** `Fp := ZMod pN`
   (`KimchiRealProofGate.lean:63`), `kimchiVerifyDecisionField (R := Fp)`, closed `by decide` —
   kernel arithmetic mod the real 255-bit Pasta prime, not ℚ and not a toy. The `cipR`/`ftEval0R`
   mirrors are tied by `rfl` at `[Field K]`, which *does* enforce defeq of the bodies; they cannot
   silently diverge from the shipped defs.

10. **`custom_selectors_zero` is correctly scoped as stated.** `EVZ.getD 4 1 … getD 8 1` are
    poseidon/complete_add/mul/emul/endomul_scalar at ζ; I confirmed `EVZ[4:9] = [0,0,0,0,0]` in the
    fixture, and the `1` default means an out-of-range index would fail rather than pass. (What is
    *not* right is its connection to the accept — see F6.)

11. **No `sorry` / `native_decide` / `admit`** in any of the twelve commits. Every grep hit is
    prose in a doc-comment. `#assert_axioms` (`metatheory/Dregg2/Tactics.lean:39-52`) is a genuine
    rejector over `collectAxioms`, and the log spelunk found it doing its job: transient `sorryAx`
    leaks in kimi's K2 `pallasDouble_forces` and K3 `round_forces`/`permFrom_forces`/`perm_forces`
    were caught by the gate and never shipped.

12. **The heavy forcing theorems are real.** `fp/fq{Add,Sub,Mul}Core_forces`, `perm_forces`
    (55-round `List.range` fold induction), `pallasCompleteAdd_forces` (33 gate hypotheses →
    the ℤ RCB trace mod p), `pallasRcbStep_forces`, `foldl_dstep_forces`, `pallasLadder_forces` —
    all consume `acceptB … = true` or explicit gate-evaluation hypotheses and conclude a value
    relation. None is `True := trivial`, `P → P`, or empty-premise. `sVec_eq_bPoly`
    (`PastaIPA.lean:113`) is a genuine induction over any `CommRing`, and its `sVec`/`bEval`
    orientation (head = highest round) matches `commitment.rs:426-476`.

---

## B. The findings

### F1 — SEV 1 · `Ref.absorbAll` DOUBLE-PERMUTES; the file's own KAT set cannot see it
`metatheory/Dregg2/Circuit/Emit/PastaPoseidon.lean:329-332`

```lean
def absorbAll (st : List Nat) : List Nat → List Nat
  | [] => perm st
  | [x] => perm (absorbAt st 0 x)
  | x :: y :: rest => absorbAll (perm (absorbAt (absorbAt st 0 x) 1 y)) rest
```

For input `[x, y]` the third clause fires with `rest = []`, then the **first clause permutes
again** → two permutations. Upstream `ArithmeticSponge` (`poseidon/src/poseidon.rs`, absorb/squeeze)
permutes only when a full rate block is absorbed **and another element arrives**, plus once at
squeeze → **one** permutation. Diverges for every input of nonzero even length (2, 4, 6, …).

The file's own prose at `:39-43` describes the upstream behaviour **correctly** — "permuting when a
full rate block is absorbed **and more input arrives**". The code does not implement its own
doc-comment. A name is a claim.

**Measured** (my Python, both semantics, upstream constants):

| input | real mina-poseidon / o1js | Lean `Ref.hash` |
|---|---|---|
| `[123456789, 987654321]` | `6772978760933812024160307839154538618423125613299338612712092411478945181912` | `23397677932345629730936879514936877232937627317971664105867317815527328737417` |
| `[pN−1, pN−1]` | `20810074891993247493960274286147277584611699933767320058174718289332701361363` | `8219658745770503307740253059558344825226897798820789573635148578028951530372` |

Both real values are the probe's own gold hex (`circuit-prove/sketches/mina-pasta-hash-probe/src/main.rs`),
and I confirmed my upstream-semantics implementation reproduces them.

**The instrument is blind by construction.** The seven `#guard`s at `:686-698` pin inputs of length
0, 1, 1, 1, 1, 3, 5. **Not one even-length vector is pinned.** The two probe vectors that *are*
even-length are exactly the two the header names and the `#guard`s omit.

**And the header states a falsehood** — `PastaPoseidon.lean:45-49`:

> "an independent Python recomputation of this file's reference … reproduces **ALL NINE** of the
> probe's o1js-1.9.1 gold KATs … `[p−1]`, `[p−1,p−1]`, `[123456789, 987654321]`. The `#guard`s
> below pin six of them in-kernel."

It reproduces **seven**. The two it fails are the two not pinned. (Also: the `#guard`s pin seven,
not six.) Whatever that Python was, it shared the bug — which is what "independent" has to mean
more than.

**Blast radius is not zero** (see F3): `MinaStateQuery.poseidonPair l r = Ref.hash [l, r]` is
*precisely* the length-2 case. `frPhase2Inputs` (`KimchiVerify.lean:672`) happens to be
`5 + 2·|evZeta|` = always odd, so C3 escapes by luck, not by design.

### F2 — SEV 1 · K6's three CR floors are PROVABLY FALSE ⇒ the whole non-equivocation payoff is vacuous
`MinaStateQuery.lean:174, 236, 281-282`

```lean
def PoseidonPairCR : Prop := ∀ a b c d : Nat, poseidonPair a b = poseidonPair c d → a = c ∧ b = d
def AccountLeafCR  : Prop := ∀ a₁ a₂ : Account, leafHash a₁ = leafHash a₂ → accountFields a₁ = accountFields a₂
def ZkappStateCR   : Prop := ∀ s₁ s₂ : List Nat, s₁.length = 8 → s₂.length = 8 → zkappStateHash s₁ = zkappStateHash s₂ → s₁ = s₂
```

`poseidonPair l r = Ref.hash [l, r]` and `Ref.absorbAt st j x = st.set j ((st.getD j 0 + x) % pN)`
(`PastaPoseidon.lean:322`) — every input enters **only** through `(s + x) % pN`. Therefore
`poseidonPair l r = poseidonPair (l + pN) r` while `l ≠ l + pN`. **`PoseidonPairCR → False` is
provable in Lean.** Identically for `AccountLeafCR` (bump `publicKey` by `pN`) and `ZkappStateCR`.

Every theorem taking one of these as a hypothesis is therefore VACUOUS:
`merkleFold_binding` (`:179`), `leafHash_commits_balance/_nonce/_zkappRoot` (`:255,260,265`),
`query_binds_balance` (`:304`), `query_binds_nonce` (`:314`), `query_binds_zkappField` (`:327`),
`mina_verify_then_query` (`:350`). That is the *entire* claimed payoff of K6 — commit `38d64b233`
calls it "the non-equivocation payoff — the queried value is UNIQUELY bound under a verified root".
All of it is `False → anything`.

**This is a regression against the file's own model.** `MinaStateQuery.lean:171-174` and `:232-236`
say these "mirror `EthLeaf.hashPairCR`". They do not. In `Dregg2/Bridge/LightClientEth.lean:98-125`,
`hashPairCR` is a **field of an abstract `EthLeaf` structure**, with `modelLeaf_hashPairCR`
exhibiting a model that SATISFIES it and `collapseEthLeaf_not_hashPairCR` exhibiting one that
REFUTES it — satisfiable, refutable, not provable, exactly the floor discipline. K6 instead pins
the hash to a **concrete** `Ref.hash` and asserts injectivity over all of `Nat`. §10.4 says the
floors are "never claimed provable"; the problem is the opposite one — they are DISprovable, and
nothing in the file can go red to say so.

The doc-comment at `:232-235` even writes "**Poseidon is CR, not injective**" and then defines
injectivity on the next line.

### F3 — SEV 1 · K6's node hash is the WRONG OBJECT, and its "independent" KATs pin the wrong numbers
`MinaStateQuery.lean:106, 277, 395-414`

`poseidonPair l r = Ref.hash [l, r]` (length 2) and `zkappStateHash appState` (length 8) are both
F1's broken case. So the modelled Mina ledger node hash is **not** `Poseidon.hash([l,r])`.

The KATs at `:395-414` are advertised (`:384-386`) as "Root/leaf values computed INDEPENDENTLY (a
Python recomputation … that reproduces the o1js gold `Poseidon.hash` vectors K3 §5 pins)". That
Python reproduces the seven **odd-length** pinned vectors — so it carries the same bug, and the KAT
is circular. Measured:

| KAT | pinned == Lean | real o1js/mina-poseidon value |
|---|---|---|
| `merkleFold poseidonPair 7 [11,13] 2` (`:395`) | `21854892…278209395` | `17876594067382267673618811276889830204275361552710098244484066674450876785088` |
| `zkappStateHash katAppState` (`:412`) | `2877203…259156922` | `7793532852580544308559766028812976281226577801406822679809933151814115881900` |
| `leafHash katAccount` (`:402`) | `12121323…607684178` | **correct** (9 fields, odd length) |

Consequently `MinaStateQuery.lean:786-789` (§10.1) — "The plain node hash IS byte-exact for o1js
application `MerkleTree`/`MerkleWitness`/`MerkleMap` (probe-confirmed)" — is **false as shipped**:
those o1js structures hash `[left, right]`, the exact broken length.

### F4 — SEV 1 (statement quality) · `mina_verify_then_query`'s first conjunct is `P → P`
`MinaStateQuery.lean:350-357`

```lean
theorem mina_verify_then_query (nodeCR : PoseidonPairCR) (leafCR : AccountLeafCR)
    (LedgerRootAttested : Nat → Prop) (root : Nat) (hverified : LedgerRootAttested root) … :
    LedgerRootAttested root ∧ ∀ (a' : Account) …, a'.balance = a.balance :=
  ⟨hverified, fun a' b' hlen hf' => …⟩
```

`LedgerRootAttested` is a *universally quantified free predicate* and the first conjunct is
returned as literally `hverified`. That half is `P → P`. The second half is F2-vacuous. Commit
`38d64b233` presents this as "the K5 seam: (K5) attest-root ∘ (K6) query-under-root" — the seam
carries no content in either component.

### F5 — SEV 2 · The composed decision has NO consistency binding between C8's eval vector and C5/C6's eval arguments
`KimchiVerify.lean@0fe996ebe:453` (`kimchiVerifyDecisionField`), `:579` (`kimchiVerifyDecisionGates`)

`kimchiVerifyDecisionField` takes `evZeta evZetaOmega` (for C8) **and, separately**, `w s shift
zZeta zZetaOmega pZeta ftEval0Claimed`. In the real proof these are *the same data*:
`pZeta = evZeta[0]`, `ftEval0Claimed = evZeta[1]`, `zZeta = evZeta[2]`, `zZetaOmega = evZetaOmega[2]`,
`w = evZeta[9:24]`, `s = evZeta[39:45]`, and (after `08792300c`) `genSel = evZeta[3]`,
`coeff = evZeta[24:39]` — I verified every one of these against the fixture. **The decision checks
none of them.** A prover supplies two independent copies and the accept cannot tell.

In Rust these all come from one `ProofEvaluations` struct; the value is read once. The Lean
decision therefore admits witnesses the real verifier cannot express — it is strictly *weaker*
than the object it transcribes. This is not in the §12 residual list under any name.

Adjacent (same shape, `alpha0/alpha1/alpha2`): nothing in the decision ties them to `α^21/α^22/α^23`.
I confirmed the fixture's values ARE those powers, so the data is honest; the *decision* is not
checking it.

### F6 — SEV 2 · C6's carrier was WIDENED, not retired; the "selectors are zero" link is prose, not proof
`KimchiVerify.lean@0fe996ebe:568` (`gateLinConst`), `KimchiRealProofGate.lean@0fe996ebe:282`

At `0fe996ebe`, `gateLinConst` is

```lean
genericGateConstraint genSel alpha coeff w
+ posSel * posBody + caddSel * caddBody + mulSel * mulBody
+ emulSel * emulBody + emulScalarSel * emulScalarBody
```

The five `*Body` values are **free prover-supplied inputs**. Where the accept previously took one
opaque `linConstTerm`, it now takes **ten** opaque inputs (5 selectors + 5 bodies). The accept
surface got wider.

`real_gate_decision_accepts` (`:282-291`) then passes literal `0`s for all ten — it does **not**
read `EVZ[4..8]`. So the chain "`custom_selectors_zero` ⇒ the custom bodies cannot contribute ⇒ the
carrier is retired" is made in the commit message and the doc, **never in Lean**. The honest
statement is: *for a fixture whose custom selectors are zero, and with the caller hard-coding zero,
the generic gate alone reproduces LCT.* Commit `08792300c`'s "The generic gate's linConstTerm
carrier is RETIRED for this proof" is defensible; the doc's residual list should say the decision
does not itself enforce the zero-selector precondition.

Also in `08792300c`: `poseidonLaneConstraint` (`:555`) is defined and `#guard`ed but is **not**
reachable from `gateLinConst` — `posBody` is opaque. The commit's "Transcribed the DOUBLE-GENERIC
gate constraint fully … and the Poseidon round-equation lane … Threaded it INTO the accept" reads
as if both were threaded; only the generic gate was.

### F7 — SEV 2 · `merkleFold_forces` is a fold congruence, not a forcing theorem, and K6 emits zero gates
`MinaStateQuery.lean:152-163`

```lean
theorem merkleFold_forces (f hp : Nat → Nat → Nat) (hnode : ∀ l r, f l r = hp l r) :
    ∀ (branch : List Nat) (leaf idx : Nat),
      merkleFold f leaf branch idx = merkleFold hp leaf branch idx
```

No `Assignment`, no `acceptB`, no gate. This is `f = g → F f = F g` — a `congr` that holds for any
two pointwise-equal functions. It sits in the same `_forces` naming family as `perm_forces` and
`pallasLadder_forces`, which *do* consume accepted gates. Commit `38d64b233` says it "Discharges
the TREE"; what it discharges is function substitution.

Compounding: `grep -c 'VmConstraint2|Assignment|acceptB|EmittedExpr' MinaStateQuery.lean` = **0**.
The file emits no AIR at all. `merkleFold` is called "the Poseidon Merkle-path fold **generator**"
in both the commit body and the file (`:113`); it generates nothing — it is a `Nat` fold.

### F8 — SEV 3 · `deferral_compression` / `deferral_records` are definitional tautologies
`PastaIPA.lean:167,171` · `KimchiVerify.lean@0fe996ebe:349`

`deferredMsmSize d := 2 ^ d.chals.length` (`:167`). `deferral_compression`'s three conjuncts are
then (i) `(absorbChallenges ⟨[],sg0⟩ us).chals.length = us.length`, (ii) `deferredMsmSize … =
2 ^ us.length` — which is (i) rewritten under the definition — and (iii) `sVec_length`. The only
content is `sVec_length`. Commit `6eb283421` calls this "the `k` vs `2^k` compression that IS the
deferral … (proved)"; nothing about the IPA is proved — `2^k = 2^k` is.

`deferral_records` (`KimchiVerify:349`) repackages the same thing behind `ipaDeferralOk`, whose own
body is `decide (chals.length = k) && decide (deferredMsmSize d = 2^k)` — the second conjunct is
implied by the first, definitionally. `78ae2edf7` calls it "the C9 soundness content".

`sVec_eq_bPoly` itself is a real theorem and is correctly described. The deferral *accounting*
around it is not.

### F9 — SEV 2 · Two C3 theorems were demoted to a 3-element `#guard` after a build wall — undisclosed in the doc
`KimchiRealProofGate.lean@0fe996ebe:326-328`

Build logs (`…/2ed94bdd-…/scratchpad/kimchi_build.log`, `kb.log`, 2026-07-27 20:36–20:37) show:

```
error: KimchiRealProofGate.lean:326:64: maximum recursion depth has been reached
error: axiom-hygiene FAIL: KimchiRealProofGate.fr_sponge_discriminates_on_real_ft1 depends on non-kernel axioms [sorryAx]
error: axiom-hygiene FAIL: KimchiRealProofGate.fr_sponge_discriminates_on_real_pzeta depends on non-kernel axioms [sorryAx]
```

The lane's own words: *"`by decide` on `Ref.hash` … hit max recursion depth …, which then leaked
`sorryAx`. … **Let me switch the C3 non-vacuity to `#guard` with smaller 3-element real-value
hashes**."* Two `theorem`s that were in the `#assert_axioms` pin list became three elaboration-time
`#guard`s over a **3-element** absorb — while `fr_eval_point_order_len`, three lines above, proves
the real Fr-sponge stream is **43 points**. C3 non-vacuity is now demonstrated on a toy absorb.

The Lean file *does* disclose this in its own comment (`:320-325`). `docs/MINA-REALITY-GATE.md`
does not — its C3 row reads as if the Fr-sponge instantiation is uniformly established. The axiom
tripwire worked exactly as designed; the reporting layer lost the fact.

### F10 — SEV 3 · The reality gate's ground truth is UNTRACKED, and the doc says otherwise
`docs/MINA-REALITY-GATE.md@0fe996ebe:39`

> "**Harness:** `proof-systems/kimchi/examples/reality_gate_export.rs` **(committed in that repo).**"

`git -C ~/dev/proof-systems status --porcelain -uall kimchi/examples/` →
`?? kimchi/examples/reality_gate_export.rs`. It is **untracked, in a third-party checkout**, and no
copy exists in breadstuffs. One `git clean -fd` and the fixture becomes unreproducible; the doc's
"Reproduce" recipe is unrunnable from a fresh clone. This is the single sentence in the doc that is
factually wrong.

### F11 — SEV 4 · The `36a8b510` provenance is a hardcoded string, not a measurement
`~/dev/proof-systems/kimchi/examples/reality_gate_export.rs:233` emits the rev as a literal
`println!`. **The claim happens to be true for this fixture** — `git reflog` shows the checkout sat
at `36a8b510cd` from 2026-05-20 until 2026-07-27 19:44, and the fixture was produced 2026-07-26
20:25 — so `7f42aa143` and `6705d1bd4` are honest. But the mechanism records nothing: re-running the
documented recipe *today* (HEAD = `f6d958dc05`, 11 commits on) emits a JSON asserting a rev it was
not built from. I diffed `36a8b510..HEAD` over `curves/ poseidon/ poly-commitment/ kimchi/src/`:
the only changes are `assert!`→`assert_eq!`, a `match`→`?`, and a `cfg_attr` removal — **no
constant and no arithmetic differs**, so nothing verified here is affected.

### F12 — SEV 3 · Every module in K1–K6 + the reality gate ran in NO build target when committed
Each file header says, in as many words, "NOT imported by the truncated `Dregg2` root". `metatheory/lakefile.toml`'s
`Dregg2` lib has no glob — it builds the root module's import closure only. So from `1ba1d6613`
through `6705d1bd4`, ~4,900 lines of `#assert_axioms` and `#guard` KATs executed nowhere; the gate
of record was a one-off manual `swarm-build` per commit. This is the GATING-DEFAULTS-TO-SILENCE
class. **Already closed out of scope** by `e7f9ae653` (2026-07-27 20:35), which rooted the DAG with
a red-proof; `08792300c`/`0fe996ebe` land after it and are covered.

### F13 — SEV 4 · `#assert_axioms` coverage is asymmetric on the endo facts
`PastaCurve.lean:821-831` pins `zetaP_cube`, `lambdaPallas_cube`, `lambdaVesta_cube` but **not**
`zetaQ_cube`, `zetaP_ne_one`, `zetaQ_ne_one`, `lambdaPallas_ne_one`, `lambdaVesta_ne_one`,
`lambdaPallas_eq_zetaQ_sq`, `lambdaVesta_eq_zetaP_sq`. Commit `6a3ff11ab` says "all by-decide-proven
primitive cube roots" — the "primitive" half (`≠ 1`) and the λ = ζ² identities are unpinned, and
one of the four `_cube` facts is too. (`PastaField` misses only `fpVal_eq`, a `rfl` bridge;
`PastaScalarMul`/`PastaPoseidon` miss only plumbing lemmas; `PastaCurveComplete` and
`MinaStateQuery` are 100%.) All the values are correct (§A.2) — this is pin hygiene, not a wound.

### F14 — SEV 4 · C3's raw-vs-endo check on the real proof is a shape observation
`KimchiRealProofGate.lean@0fe996ebe:336-339` proves β,γ < 2^128 and ζ,α,v,u > 2^128. True, and
consistent with `squeeze_order`'s flags — but it is a bit-length assertion, not a derivation of any
challenge. Correctly labelled in §12 residual 3; noted so the table row is not read as more.

### F15 — SEV 4 · KAT-weight nits
- `PastaField.lean:329-332`: the `Ref` add anchors use `X + Y < pN`, so **no modular reduction is
  exercised** at reference level — and `fpAdd X Y` and `fqAdd X Y` are pinned to the *same* number
  for that reason. (The gate-level carry KAT at `:400` does exercise it; the Ref-level pair is
  decorative.)
- `PastaPoseidon.lean:686-688`: `Ref.hash []` and `Ref.hash [0]` are the same value, pinned twice.
- `PastaIPA.lean:192-202`: the identity KATs are over ℤ at 3 challenges; fine, but `katChals`
  never exercises the `ZMod pN` instance the header says is "covered".

### F16 — SEV 4 · Citation drift
`PastaPoseidon.lean:34` cites `full_round` at `permutation.rs:56-71`; at the pinned rev it is
`55-70`. (`sponge.rs:110`, `fp.rs:10`, `fq.rs:10`, `linearization.rs:364`, `verifier.rs:412-489`
all check out exactly.) In the out-of-repo extractor, the `ev_zeta` comment says "7 selectors"
while the code pushes 6.

### F17 — SEV 4 · Header claim "the `#guard`s below pin six of them"
`PastaPoseidon.lean:49` — there are seven. Cosmetic, but it is the same sentence that carries F1's
false "ALL NINE".

### F18 — SEV 4 · Attribution is honest
kimi died mid-K4 (`~/.kimi-code/logs/kimi-code.log`, 2026-07-26T20:38:47Z,
`403 You've reached your usage limit`); `kimi-K4-out.txt` ends mid-sentence. K4a/K4b/K4c
(`fbdfad15c`/`0d0c71284`/`6eb283421`) were built by Claude lanes and `0d0c71284` credits kimi only
for the design decision and a gate-count estimate — which is what happened. No misattribution in
either direction. K1/K2/K3 hbox builds are backed by real log text, not self-report. K2 volunteered
an unprompted honest note that "the generic-forcing approach failed (whnf blowup) and was replaced
with direct proofs". **No sin here** — recorded because the checklist asks.

### F19 — Out of scope, flagged because it is the same defect class
`835db56c6` (landed during this audit) adds `challengesOk` (`KimchiVerify.lean:941` at HEAD). Its
β/γ arguments are **`Nat`s unrelated to the `R`-typed `beta`/`gamma` that `ftEval0R` actually
consumes**, and the only check on them is `< 2^128`. A prover passes `betaN = 0` and any `beta`.
That is F5's shape again, one layer up. Worth a look before the next reality-gate claim.

---

## C. Ranked fix list

1. **Fix `Ref.absorbAll` (F1)** and add `#guard`s at even lengths 2 and 4 — including the two probe
   gold vectors `[123456789, 987654321]` and `[pN−1, pN−1]` that currently go unpinned. Then correct
   `PastaPoseidon.lean:45-49` ("ALL NINE" → what is actually reproduced; "six" → seven). One clause:
   permute lazily, or restructure as block-padding.
2. **Re-pin K6's KATs after (1)** — `merkleFold poseidonPair 7 [11,13] 2` and
   `zkappStateHash katAppState` are wrong numbers today (F3), and retract the "byte-exact for o1js
   `MerkleTree`" claim at `MinaStateQuery.lean:786-789` until it is re-measured.
3. **Replace K6's three CR floors (F2)** with the `EthLeaf` shape the file claims to mirror: an
   abstract hash parameter, plus a satisfying model AND a refuting model. As stated they are
   provably false and every payoff theorem is vacuous. Until then, `38d64b233`'s "non-equivocation
   payoff" should not be cited anywhere.
4. **Delete or restate `mina_verify_then_query` (F4)** — a `P → P` conjunct wearing a seam's name.
5. **Bind the duplicate eval inputs (F5)** — make `kimchiVerifyDecisionField/Gates` *project* `w`,
   `s`, `pZeta`, `zZeta`, `ftEval0Claimed`, `genSel`, `coeff` out of `evZeta`/`evZetaOmega`, or add
   the equality conjuncts. Right now the Lean decision is weaker than the Rust it transcribes, and
   that is not named as a residual.
6. **Make C6's zero-selector precondition a Lean step, not prose (F6)** — feed `EVZ.getD 4 1 …` into
   `real_gate_decision_accepts` instead of literal `0`s, and say in §12 that the decision does not
   itself enforce it.
7. **Rename `merkleFold_forces` → `merkleFold_congr` (F7)**, and stop calling `merkleFold` a
   "generator" — `MinaStateQuery` emits zero constraints.
8. **Vendor both extractors into breadstuffs and fix `MINA-REALITY-GATE.md:39` (F10)**; make the rev
   a measured `git rev-parse HEAD`, not a `println!` literal (F11).
9. **Say in `MINA-REALITY-GATE.md` what the Lean already admits (F9)** — C3's Fr-sponge non-vacuity
   rests on a 3-element `#guard`, not the 43-point real stream, because `by decide` blew the
   recursion limit.
10. **Restate the deferral accounting (F8)** — `deferredMsmSize` is defined as `2^k`; the only
    content is `sVec_length`. Drop "the C9 soundness content".
11. **Complete the `#assert_axioms` pins on the endo facts (F13)** — `zetaQ_cube`, the four `_ne_one`,
    and the two `_eq_*_sq`.
12. Housekeeping: F15 KAT-weight nits, F16 citation drift, F19 before the next gate claim.

---

## D. One line on register

The three commits I would not have believed without checking — `c8_real_matches`,
`c5_ft_real_matches`, `generic_gate_matches_lct` — are the three that held up under an independent
Python recomputation from the o1-labs source. The stack's arithmetic leg is stronger than its
commit subjects, and its Mina leg (K3's sponge, K6's floors) is weaker than its doc-comments. Both
gaps are in the same place: where a `#guard` set could not go red.
