# PROOF-STRATEGY 2026-08-09 — where a proof binds the thing that runs, and where it stops

**Method.** Everything below is read from the tree at `25144cd9c`/`7a181f741` or *evaluated*. Where I
say "evaluated" I ran it: `lake env lean` over a scratch file against the built oleans in
`metatheory/.lake/build/lib/lean/`, no repo file touched. Where I say "searched" I give the grep, because
a negative from an incomplete corpus is how a lane was wrong this week. Five parallel readers swept the
`@[implemented_by]`, `native_decide`/`#guard`, assumed-hypothesis, emitted-bytes and cost-instrument
surfaces; their file:line claims are marked and the load-bearing ones I re-checked myself.

**The thesis.** Our proof effort is concentrated on the one link of the chain a machine already checks
— *does this proof term typecheck, and on what axioms* — while the links that decide whether the proof
reaches the running system have either a hand-written campaign confined to one namespace (*does the
statement say what its name says*) or no instrument at all (*does the compiled twin equal the def it is
attached to*; *do the bytes the verifier reads equal the term the theorem is about*).

**And the well-covered link is less covered than we think.** Three of the four axiom-hygiene commands
have a path that passes while checking nothing — demonstrated by running them, §0.1 — the gate
apparatus is scoped to the corpus with two demo axioms rather than the one with twenty-eight real ones
(§0.2), and the largest Prop-hypothesis in the tree carries a docstring naming a witness that does not
exist (§0.3). Today produced four independent demonstrations of the general shape; the census below
says they are the class, not the instances.

---

## 0. LEAD — claims currently in the tree that this map cannot support

Ordered by how load-bearing the claim is. Each is a *claim we made*, not a defect someone else left.

### 0.1 ⚑⚑ The axiom-hygiene instrument has three fail-open paths — and the file that defines it already implements the fix, twice

**This corrects a claim in my own first draft**, which said these commands are not fail-open. I read
them and concluded that from the code. Then I ran them.

```lean
import Dregg2.Tactics
#assert_all_clean []
#assert_namespace_axioms ThisNamespaceDoesNotExistAnywhere
axiom Evil._native.forged : (1 : Nat) = 1
theorem rests_on_forged : (1 : Nat) = 1 := Evil._native.forged
#assert_compiled rests_on_forged
```

`lake env lean` on that file exits **0**. Output in full:

```
#assert_all_clean: 0 keystones pinned kernel-clean
#assert_namespace_axioms ThisNamespaceDoesNotExistAnywhere: 0 theorems pinned kernel-clean
```

Three separate holes, in ascending severity:

1. **`#assert_all_clean []`** (`metatheory/Dregg2/Tactics.lean:68-75`) — `ident,*` accepts the empty
   list, the loop never runs, it logs and succeeds. 478 sites, each pinning a list; a list emptied in
   a refactor goes green. Zero empty lists in the tree today, so this is latent.
2. **`#assert_namespace_axioms <empty namespace>`** (`Tactics.lean:359-405`) — no non-vacuity floor.
   If the namespace matches zero theorems, because the declaring module is not in the pin site's
   import closure or the namespace was renamed, `checked` stays 0 and the command logs *"0 theorems
   pinned kernel-clean"* and passes. **95 pins in the tree, each green by luck of the import graph.**
3. ⚑ **`#assert_compiled` accepts a hand-written axiom that is merely *named* like a native oracle.**
   `Dregg2.isNativeOracleAxiom` (`Tactics.lean:116-118`) matches any name with a `native_decide` or
   `_native` component. `Evil._native.forged` therefore lands in neither the `bad` filter nor the
   zero-oracle branch, and the pin is **silently green** — no output at all, which is worse than the
   two above. This is the pin used *instead of* `#assert_axioms` on the entire compiler-trusted
   surface: **1 836 sites.** `#assert_axioms` would still catch such an axiom; `#assert_compiled`,
   the command that exists to make compiler trust visible, does not.

The fix is written twice in the same file, thirty lines further down. `#assert_not_depends_on` errors
on an empty list (`Tactics.lean:228-230`: *"a guard that forbids nothing always passes"*) and on a
zero-scan (`:245-247`: *"nothing was walked, so this check passes vacuously"*), and
`#assert_depends_on` repeats the empty-list error at `:265-267`. **The author identified this exact
failure mode, named it in prose, implemented it twice, and did not apply it to the three commands
that carry 22 380 + 478 + 95 + 1 836 pins.** Three `throwError`s close it.

### 0.2 ⚑⚑ The corpus that carries the real axioms is the corpus with no gates

`orb/` holds **28 genuine `axiom` declarations** — 25 in `orb/Crypto.lean` (`:332` chacha roundtrip,
`:343` chacha authenticity, `:349,:355` AES-GCM, `:365` AES-ECB, `:373` X25519, `:383,:394,:404`
crypto_box, `:415,:417` ed25519, `:437,:442` ECDSA-P256, `:449,:454` RSA-PSS, `:461,:474` RSA-PKCS1,
`:482,:483` SHA lengths, `:496,:501,:513` ML-DSA, `:682` XWing KDF, `:686,:695` ML-KEM IND-CCA), plus
`orb/TlsHandshake.lean:1442`, `orb/QuicHeaderProt.lean:66`, `orb/Cache/VaryKey.lean:123`. They are
honestly labelled as an external trust boundary discharged by HACL*/EverCrypt F* and the aws-lc audit
(`orb/Crypto.lean:319,470`), and they are the live TLS/QUIC/cache datapath.

`metatheory/` holds **two**, both deliberate tier-classifier demo fixtures
(`Dregg2/Widget/Basic.lean:298-299`).

And every instrument is scoped to `metatheory/`. Measured: `scripts/axiom-hygiene-guard.sh:38`
(`META="$ROOT/metatheory"`), `scripts/check-guard-discipline.py` (metatheory-only census, `:150`),
zero `orb/` rows in `scripts/guard-discipline-baseline.txt`, **zero `#assert_compiled` in the whole of
`orb/`**, zero `#assert_namespace_axioms`, 131 `#assert_axioms` against metatheory's 22 249 — and
**1 111 `#guard`s in `orb/` that no ratchet counts.**

That is the map's sharpest single statement. We built a careful hygiene apparatus and pointed it at
the corpus with two demo axioms, not the corpus with twenty-eight real ones.

### 0.3 ⚑ `StepCanon` — 378 binder positions, no producer, and a docstring that names a witness which is an axiom-hygiene block

`metatheory/Dregg2/Circuit/Emit/AutomataflStepRefine.lean:152`, one field: every cell of every row is
the canonical BabyBear residue. Its docstring at `:150` and the module header at `:50` both say
*"Inhabited concretely by the §6 witness, so it is never a vacuous antecedent"*, and
`AutomataflStepBackend.lean:50` repeats it. **§6 of that file is `/-! ## §6 — Axiom hygiene. -/`** — a
block of `#print axioms`. There is no §6 witness.

It is assumed at **378 binder positions**, the largest of any Prop in either tree, and re-exported by
`open` into ~15 downstream modules (`AutomataflCoord.lean:58`, `AutomataflResolveRefine.lean:124`,
`AutomataflTurnCapstone.lean:69`, `AutomataflStepCapstone.lean:1439`, …). Searched: every non-comment
mention in `metatheory` and `orb` is the definition, an `open`, a `(hc : StepCanon t)` binder, or
`AutomataflBraidFold.lean:383`, where it is a *conjunct of another hypothesis*. No construction, no
derivation from the range gates (`stepcanon_of|canon_of_sat` — nothing). `Canon` itself is proved only
at four literals (`:103-106`).

This is the `FinalizedRegionStable` docstring failure at 378 binder positions instead of two, and it
is **untracked**: `StepCanon` appears nowhere in `Dregg2/Verify/`, `Circuit/FloorsNonVacuous*.lean`, or
`Circuit/ProofAssurance.lean`.

Its siblings, from the same sweep (binder positions / discharge found):

| hypothesis | binders | status |
|---|---|---|
| `RestIffNo*` ×13 (`Circuit/EffectCommit2.lean:85` + `Circuit/Inst/*`) | ~180 | none — and **known false**, by the tree's own Cantor argument at `Verify/RestFrameFiniteSupportSuccessor.lean:343-356` |
| `RotTableSideW` / `RotTableSideNarrow` (`Circuit/RotatedKernelRefinementAvail.lean:109,154`) | 80 / 26 | none; only transports and projections. The *parent* `RotTableSide` **is** inhabited (`Circuit/FloorsNonVacuousWave.lean:63`) — the upgrade lost the witness |
| `CanonicalAssignment` ×7 + `AirFacts` | ~192 / 37 | none; `airFacts_row0` is built *from* `CanonicalAssignment` |
| `SpineCommits8` (`Circuit/SortedTreeNonMembershipHeap8.lean:65`) | 28 | none; self-labelled "A HYPOTHESIS, never an axiom"; the wide twin `SpineCommitsW` **is** proved |
| `hole_turn_root_compress_binding` (`Circuit/TurnCircuitCompose.lean:126`) | 4 | none — and it is the binder that makes the whole-turn apex's "the prover-folded post-root IS the genuine `recStateCommit`" true (`Spec/WholeTurnTriangle.lean:308`) |

Two of these are *worse* than the calibration case: `RestIffNo*` is refuted, not merely undischarged;
`RotTableSideW` regressed from an inhabited predecessor.

### 0.4 ⚑ Four theorems state `True` under docstrings that state a cryptographic fact

`metatheory/Dregg2/Circuit/FriVerifier.lean:1056` is the sharpest:

```lean
/-- The wrap introduces NO new cryptographic assumption: its soundness rests on
exactly `FriLowDegreeSound` … plus the gnark Groth16/pairing soundness … a refinement
statement, not an unverified reimplementation. -/
theorem wrap_rests_only_on_named_floor : True := trivial
```

Siblings: `Dregg2/CommitBindsGuards.lean:62` (`: True := trivial`, with **`#assert_axioms` pinned on
it at `:64`** — a kernel-cleanliness tick on a proof of `True`), `Dregg2/PicklesSynthesis.lean:181`,
`Dregg2/MinaBridgeGuards.lean:105`. And one that fully degrades:
`Games/PathOfAngels/EditorialRegistry.lean:181`, `theorem expedition_receipt_constructor_remains_private
: True := Cartography.extraction_receipt_constructor_is_private` — a `True` cited to prove a `True`,
under a docstring claiming it re-pins an ADT boundary at the import edge.

There is also a **~112-theorem half-case**: `: True := by fail_if_success …` (e.g.
`Games/PathOfAngels/CrewFieldMissionRuntimeBoundary.lean:48-245`). The tactic block does real
elaboration-time work — `fail_if_success (have _ := Config.mk)` genuinely checks a constructor is
private — but the *statement* is `True`, so nothing composes on it and its `#assert_axioms` certifies
nothing about the claim. **These are `#guard`s wearing a theorem's clothes**: the check lives in the
tactic block, which is exactly where the guard-discipline policy says it must not.

### 0.5 ⚑ `MlDsaRing`'s twin differentials do not pin `ntt` or `intt`. Constructed falsifier, evaluated.

`metatheory/Dregg2/Crypto/MlDsaRing.lean:245-248` says the `#guard`s below it "pin each twin against the
pure ground truth … a genuine fast-vs-pure comparison, NOT fast-vs-fast". For `addPoly`/`subPoly`/
`pointwiseMul` that is true (they compare against inline `Nat` formulas). For `ntt`/`intt` it is not:
the only two tests that touch them are the composite `:356` and the round-trip `:358`, and **both are
satisfied by a twin pair that is not the spec.**

I built one. `fastNtt` post-composed with `List.reverse`, `fastIntt` pre-composed with the same
involution — pointwise multiplication is permutation-equivariant, so the convolution is unchanged and
the round trip is unchanged by construction:

```lean
def nttPerm  (w : Poly) : Poly := (fastNtt w).reverse
def inttPerm (w : Poly) : Poly := fastIntt w.reverse
#eval inttPerm (fastPointwiseMul (nttPerm sampleA) (nttPerm sampleB)) == schoolbookMul sampleA sampleB
#eval inttPerm (nttPerm sampleA) == sampleA
#eval nttPerm sampleA == fastNtt sampleA
```

evaluates to `true`, `true`, `false`. Guard `:356` passes. Guard `:358` passes. The pair differs from
the routed twin. This is demonstration 1's shape — a corpus symmetric in exactly the dimension the two
implementations could differ in — sitting on the ML-DSA **sign and verify** path
(`ntt` is `@[implemented_by fastNtt]` at `:349`, reached from `@[export dregg_fips204_verify_real]`,
`metatheory/Dregg2/Crypto/Fips204Verify.lean:882`).

What actually catches a permuted twin today is a *cross-module accident*: `MlDsaExpandA.lean:15,76`
samples `Â` directly in the NTT domain and never applies `ntt` to it, so in
`MlDsaVerifyReal.lean:182` a permuted `ẑ` meets an unpermuted `Â` and does not cancel, and the
ACVP KATs (`MlDsaSigVerAcvp.lean:175`, `native_decide` over 15 NIST vectors) go red. That is real
coverage. It is not the coverage the docstring claims, and it evaporates if `ExpandA` ever moves to the
coefficient domain.

### 0.6 ⚑ The `MlDsaRing` element-wise guards exist to catch a 32-bit truncation, on a corpus whose largest product is 4.

`MlDsaRing.lean:227-230` states the crux: "a COEFFICIENT PRODUCT reaches `< 2⁴⁶` — which TRUNCATES in a
32-bit multiply", which is why `mulQu` (`:260`) widens to `UInt64`. The corpus is `sampleA` (`:209`)
and `sampleB` (`:212`), both sparse. Evaluated over all 256 lanes:

| quantity | value | threshold that matters |
|---|---|---|
| max `sampleA[i] * sampleB[i]` | **4** | `2³²` (the truncation the guard exists for) |
| max `sampleA[i] + sampleB[i]` | **7** | `q = 8 380 417` (the reduction `addQu` performs) |

So `#guard :366` (`fastPointwiseMul`) stays green against a `mulQu` written the wrong way — the exact
naive port the docstring warns against — and `#guard :362` (`fastAddPoly`) stays green if `addQu`'s
`% qU` is deleted entirely, because it never fires. The one guard that does exercise truncation is the
composite `:356`, which reaches products ≈7×10¹³ from NTT layer 1 onward. **The three differentials
written *for* these twins are degenerate; the twins are covered incidentally, by a fourth.**

### 0.7 ⚑ The τ-level evidence for today's twin repair is `[] = []`.

`BlocklaceFinality.lean:1187` and the body of `7a181f741` both say the keep-first twin "was a silent
order divergence on the live `dregg_tau_order` path". The tooth offered for the τ level is
`fast_tau_matches_the_spec_on_the_uneven_pred_lace` (`:2405-2407`),
`tauOrderFast laceUnevenPreds [0,1] 2 = tauOrder laceUnevenPreds [0,1] 2`. Evaluated:

```
tauOrder laceUnevenPreds [0,1] 2              = []
(tauOrder laceUnevenPreds [0,1] 2).length     = 0
findAllFinalLeaders laceUnevenPreds [0,1] 2   = []
```

The lace finalizes nothing. The theorem is `[] = []`, four lines above a comment that says "a
`@[implemented_by]` differential over a one-element list constrains almost nothing" (`:2413`).

And the stronger reading: **no consumer of `causalPastIncl` in the τ path reads its order.** I
enumerated all of them (`grep -n 'causalPastIncl\b' BlocklaceFinality.lean`): `closureLace` `:423`
(`B.filter (past.contains ·)` — order comes from `B`), `hasEquivInPast` `:435` (`.any`/`.any` → Bool),
`approves` `:448` (`.contains`), `ratifies` `:453` (`.filter … .length` over `past.any`),
`previousRatifiedLeader` `:630` (`foldl` argmax on `(depth, id)`, a total order on distinct ids, hence
order-independent), `ratifiedLeaderChain` `:658` (`.length` only), `anchorSegment` `:810` (`filter` then
`xsortBy`), `tauStep` `:820` (carried as `prevCovered`, read by `.contains`), `mkPastCache` `:877`
(stores the same values). `xsortBy` (`:769`) is `List.mergeSort` under
`roundOf a < roundOf b || (roundOf a == roundOf b && a ≤ b)` — a total order on distinct ids, so its
output is the unique sorted list. Evaluated: two different permutations of the same nine ids give the
identical `xsortBy` output.

So the seam was genuinely violated and the repair is right — a trusted twin must equal its spec, and
resting on accidental order-invariance is exactly the fragility we are trying to remove. But **the
blast radius we stated is not supported by anything in the tree, and the tooth offered as support is
vacuous.** Both halves of that matter: an overstated blast radius is how a real finding gets
discounted the next time.

### 0.8 ⚑ `ClosedExtension` is false of the wire we build, in the scenario it was written for.

`Dregg2/Consensus/TauPrefixMonotone.lean:45-50` says `ClosedExtension` is "three STRUCTURAL facts about
the growth" that "`node/src/catchup.rs::apply_with_buffering` already implements". Its first field
(`:116`) is

```lean
grown : ∃ new : Lace, B' = B ++ new
```

— a *list append*. The Lean `Lace` the node hands `dregg_tau_order` is built by
`node/src/finality_gate.rs:129-144`: the whole block set is collected fresh, sorted by
`(seq, creator)` (`:137`), and **each block's Lean `BlockId` is its index in that sort** (`:141-144`).
So when a lagging validator's low-`seq` block arrives late, it inserts in the *middle* and every later
block is renumbered. `B' = B ++ new` is false.

That is not a hypothetical. It is the honest-laggard trace `TauPrefixMonotone` §8 (`:790-830`) uses as
its own positive exhibit: validator 4 lags, then its round-2 block arrives after validators 1–3 have
published rounds 2 and 3. Sorted by `(seq, creator)`, that block lands between them.

Every stability lemma in the module opens with `obtain ⟨new, rfl⟩ := h.grown` (`:126`, and via
`lookup_stable` at `:133`, `:152`, `:177`, `:349`, `:368`, `:402`, `:409`, `:417`, `:463`, `:477`), so
`tau_finalized_prefix_monotone` (`:654`) and `tau_executed_prefix_fixed` (`:697`) are theorems about a
wire we do not build. The mitigating fact, and it is a real one: the interning is *order-preserving*
under growth (relative order of two blocks in a `(seq, creator)` sort depends only on their own
coordinates), so the conclusion very likely still holds for the node — but that is an argument nobody
has written down, and the theorem does not deliver it. §4 S4 says what to do.

### 0.9 A CI comment is doing a gate's job, and names a test that does not exist.

`.github/workflows/ci.yml:1947-1951` says `TestEmittedDescriptorShapeIsDerivedFromTheFixture` "is what
turns 'the templates agree with each other' into 'the templates agree with the proof they are supposed
to open'". Searched `--include=*.go --include=*.yml --include=*.sh --include=*.md` for
`EmittedDescriptorShapeIsDerived|ShapeIsDerivedFromTheFixture|DerivedFromTheFixture`: **one hit, the
comment itself.** The only shape check that exists is `checkDerivedParity`
(`chain/gnark/emitted_verifier_full.go:343-362`), which validates one part of `verifier_full.json`
against another part of the same file. The workflow's own header already concedes the class at
`ci.yml:1930-1932` — "A DIFFERENTIAL between two committed artifacts detects DISAGREEMENT, never
STALENESS."

### 0.10 Four assertion messages claim a sequence property over a set comparison.

`node/src/finality_gate.rs:686-697` claims "a permutation-free superset relationship … IN the verified
sequence" over a `HashSet<(u64,u64)>` comparison; `:797-834` says "the Lean port is order-faithful to
the Rust tau" over `HashSet<([u8;32],u64)>`. `HashSet` discards the sequence. Same shape at `:594-611`
and `:942-954`. The live differential (`node/src/blocklace_sync.rs:2749-2757`) is honest about it —
`sort_unstable()` before comparing, and the surrounding comment at `:2695-2698` says outright "The
differential below does NOT establish it (it sorts before comparing)."

### 0.11 Two docstrings claim an `@[implemented_by]` that is not installed.

`orb/Body/Chunked.lean:500` and `:1025` say `@[implemented_by decodeStreamImpl]` /
`@[implemented_by decodeStreamExtImpl]`. Neither attribute exists; callers name the impl directly
(`orb/Reactor/Body.lean:133`, `orb/Body/Framing.lean:84`) and rewrite back through proved equalities
(`Chunked.lean:502`, `:1027`). The outcome is sound and *better* than a seam. But an auditor grepping
`implemented_by` gets two false positives, and a reader trusting the docstring believes in a trusted
seam that isn't there. Fix the prose.

---

## 1. THE CHAIN OF CUSTODY — five links, and where the effort sits

A proof reaches the running system only through a chain. Here is the chain, the population of our
effort at each link, and what that link's instrument structurally cannot see.

| # | Link | Instrument | Population | What it cannot see |
|---|---|---|---|---|
| 1 | proof term → kernel | `#assert_axioms` / `#assert_clean` / `#assert_all_clean` / `#assert_namespace_axioms` (`metatheory/Dregg2/Tactics.lean:50,58,68,359`) | **22 380** + 478 + 95 + 13 pin sites (comment-stripped) | *Hypotheses* — `collectAxioms` does not see typeclass params or Prop binders (`Tactics.lean:22-26`). *Whether the pinned statement says anything* (§0.4). *Whether the pin ran at all* (§0.1). And `@[extern]` (168 sites), `@[implemented_by]` (6), `opaque` — all attach behaviour with **no** axiom footprint. |
| 2 | statement → meaning | `PremiseInhabitability*` (4 110 lines) — **hand-written, and scoped to `Circuit/`+`Verify/`** | ~28 rows bracketed | Anything outside those namespaces. Searched all four sweep modules for `Distributed\|Consensus\|ChainExtends\|ClosedExtension\|CrossNode`: four incidental hits. Every historical vacuity here was `#assert_axioms`-clean — the identity carrier, the ∃-image class, the uninhabited `CrossNodeWitness`, the five-floor `CommitSurface`. |
| 3 | statement → compiled code | `#assert_compiled` (`Tactics.lean:124`), differentials, `#guard` | 1 836 pins / 1 994 `native_decide` / **16 128** `#guard` (15 017 metatheory + 1 111 `orb/`) | Whether the differential's *corpus* can distinguish. Nothing measures that. And a forged `*._native.*` axiom (§0.1). |
| 4 | compiled code → the wire | `_eq` theorems (`FinalityGate.lean:376`), 661 `@[export]` across 170 modules | — | The wire *encoder* is Rust. §0.8 is this link failing. |
| 5 | wire → the bytes a verifier reads | `circuit/descriptors/` has a real gate (`ci.yml:2021`); `chain/gnark/emitted/` has none | 9 pinned by a Lean `#guard` on a *string*; **20 with no pin at all** | Staleness of the file on disk versus the term the `#guard` is about. |

Read that column as the finding. **Link 1 carries ~22 900 pins. Links 4 and 5 have no instrument at
all, and link 2's instrument is a hand-written campaign confined to one namespace.** That is the
concentration, stated numerically: the effort sits where a machine already checks, and thins out
exactly as the distance to the running system grows.

**And read link 1's own strength honestly.** `#assert_axioms` in its single-name form is fail-*closed*
on the thing it was designed for: `realizeGlobalConstNoOverloadWithInfo` errors on an unresolvable or
ambiguous name, so a typo cannot silently drop a pin, and a `sorry` in a proof body is caught.
`#assert_compiled`'s zero-oracle branch is a genuinely good two-sided design — a kernel-clean fact
cannot be laundered downward into a compiler-trusted label. But §0.1 shows three of the four commands
have a path that passes while checking nothing, and there are two further softnesses worth naming:

- **358 `#assert_axioms` pins aim at a `def`/`abbrev`/`instance`, not a theorem** — e.g.
  `Dregg2/Hyperedge.lean:453-456`, `Market/ProtocolAssurance.lean:637,920,924,926`,
  `Dregg2/Consistency.lean:341-342`, `Dregg2/Proof/GST.lean:311,315`. `collectAxioms` on plain data
  returns ∅, so they pass for free. The namespace form already filters `unless info.isThm do continue`
  (`Tactics.lean:382`); the single-name form does not.
- **`#assert_not_depends_on` / `#assert_depends_on` (`Tactics.lean:225-280`) are the strongest
  instruments in the file** and should be the template for the rest: empty-list error, unresolvable-name
  error, zero-scanned error, and a positive-control dual sharing the same walk so the two "go blind
  together or not at all" (`:254-255`). Its docstring even records a *measured* refutation of an earlier
  heuristic (`:160-166`).

The net: link 1 measures the axiom footprint of the declarations it actually reaches. It does not
measure the premise footprint, it does not read the statement, and — until §0.1's three `throwError`s
land — it does not guarantee it reached anything.

---

## 2. SEAM CENSUS

### 2.1 `@[implemented_by]` — six sites, two files, all live

| # | Site | pure | twin | live path | differential | ⚑ can the corpus distinguish? | twin = pure proved? |
|---|---|---|---|---|---|---|---|
| 1 | `MlDsaRing.lean:346` | `addPoly` | `fastAddPoly` | `dregg_fips204_{sign,verify}_real` | `:362` | **NO** — max sum 7, `% qU` never fires (§0.2) | none |
| 2 | `MlDsaRing.lean:347` | `subPoly` | `fastSubPoly` | same | `:364` | partial — index 0 has `1 < 4`, real wraparound | none |
| 3 | `MlDsaRing.lean:348` | `pointwiseMul` | `fastPointwiseMul` | same | `:366` direct, `:356` composite | `:366` **NO** (max product 4); `:356` yes | none |
| 4 | `MlDsaRing.lean:349` | `ntt` | `fastNtt` | same | `:356`, `:358` only | **NO** — falsifier constructed, §0.1 | none |
| 5 | `MlDsaRing.lean:350` | `intt` | `fastIntt` | same | `:356`, `:358` only | **NO** — same falsifier | none |
| 6 | `BlocklaceFinality.lean:1373` | `tauOrderFast` | `tauOrderFastImpl` | `dregg_tau_order` | `:2363-2369`, `:2394-2418` | **YES since today** (`laceUnevenPreds`) | no; `tauOrderFast_eq` `:1096` is about the *pure* fast def |

Seam 6 is the model and seams 1–5 are the debt. One attribute at `:1373` covers **seventeen** untheoremed
runtime functions (`fastCausalPastAux` `:1195` … `fastEnrolledFilter` `:1343`), and after today exactly
one lace in the corpus is non-uniform. The other six traces (`trace3`, `traceEquiv`, `traceMW4`,
`trace6`, `traceOrderFork8`, `traceUnenrolled6`) are all round-synchronous and fully cross-linked, so a
*second* first-vs-last-shaped divergence anywhere in those seventeen functions is tested by one lace.
`fastEnrolledFilter`'s first-wins creator map (`:1346`) has no equivocation-specific separating corpus
at all.

### 2.2 ⚑ The mechanism fact that governs all six — and makes the obvious fix vacuous

`#guard` evaluates through the **compiler**, not the kernel (`Lean/Elab/Tactic/Guard.lean:154-166`,
`unsafe evalExpr`), so `@[implemented_by]` is honoured inside it. Therefore, when the attribute is
attached to the pure def itself, **the direct differential is a tautology.** Demonstrated:

```lean
def pureF (n : Nat) : Nat := n + 1
def twinF (n : Nat) : Nat := n + 999
attribute [implemented_by twinF] pureF
#eval pureF 1                  -- 1000
#eval (twinF 1 == pureF 1)     -- true
theorem kernel_still_sees_the_pure_body : pureF 1 = 2 := rfl   -- elaborates
```

Evaluated. `pureF 1` prints `1000`; the differential prints `true`; and `rfl : pureF 1 = 2` is accepted
by the kernel at the same time. A contributor who "closes the gap" on seams 4/5 by writing
`#guard fastNtt sampleA == ntt sampleA` gets a green tautology and a false sense of closure.

`BlocklaceFinality` escapes this only because its attribute is on `tauOrderFast`, an *alias*, leaving
the pure `tauOrder` and `causalPastIncl` unrouted — the file states the discipline explicitly at
`:1167-1172`. **That structural choice, not the guards, is what makes seam 6 testable at all.** It is
the single most transferable thing in this census.

### 2.3 `@[extern]` and `@[csimp]` — clean, and worth saying so

- **168 `@[extern]` sites, every one attached to an `opaque`.** There is no `@[extern] def` anywhere in
  `metatheory`, `orb`, `orb-compiler`, `tools`, `fhegg-rtl` or `dregg-serve-spec`. So none is a
  differential twin: there is no Lean body to diverge from. They are named oracles discharged by Prop
  carriers (`Crypto/PortalFloor.lean:35,65,95,139,172,199,224,256`); a larger trust surface than an
  `implemented_by`, but an *honest* one, and the wire-agreement obligation is stated at
  `Storage/Deployed.lean:63-65`.
- **18 first-party `@[csimp]`s, each a kernel-checked `theorem f_eq_g : @f = @g`.** This is the one
  runtime-substitution mechanism that carries a proof obligation. Its only hazard is scoping and it is
  already documented (`orb/Reactor/SerializeFast.lean:9`): a csimp applies to call sites compiled after
  it is in scope, so mis-scoping is a silent *performance* reversion, never a correctness one.
- One `unsafe` first-party def (`Dregg2/Exec/FFIDirect.lean:452`), wrapping `unsafeIO` for env reads
  with a pure fallback. No `lcProof`/`unsafeCast` in first-party code.

**Conclusion: the trusted-twin hole is exactly six functions.** That is small enough to close
completely, which is what makes it the highest-value target in this document.

### 2.4 The emitted-bytes boundary — the byte-level `allowed_relics`

The precedent is fixed and fixed *well*: `allowed_relics` is now `RelicList mission.allowedRelics`, a
dependent type whose `complete`/`ascending` fields make a wrong list unrepresentable
(`metatheory/Dregg2/Games/PathOfAngels/RelicNamespace.lean:164-167`, consumed at `Emit.lean:2035,2108`).
That is the template.

The same shape is live at the byte level for `chain/gnark/emitted/`:

- **What is proved:** `#guard`s over a Lean **`String`** — `EmitJson.lean:295` (full literal for
  `verifierFullJson`), `InputOpenBatchEmit.lean:1040-1049` and `SelectorEmit.lean:649-656` (length +
  FNV-1a for six more), `Poseidon2Emit.lean:282-283`, `ChallengerReplayEmit.lean:360-361`,
  `InputOpenEmit.lean:600-601`. None reads a file.
- **What is consumed:** the Go verifier loads the **file** —
  `chain/gnark/emitted_verifier_full_test.go:21,26`, `emitted_verifier_full.go:178-181,1551,1613,1738,1889`,
  `emitted_challenger.go:51`, `emitted_fri_stage_replay.go:522`. Searched `chain/gnark/*.go` for
  `fnv|FNV|1099511628211|14695981039346656037`: one **comment** (`emitted_verifier_full.go:1012`).
  Nothing in Go recomputes the pin.
- **Why they need not agree:** the writers are outside the build by design —
  `metatheory/scripts/gen_gnark_emitted_templates.lean:36` ("NOT part of `lake build`"), and siblings
  `gen_fri_fold_template.lean`, `gen_merkle_templates.lean`, `gen_query_pow_templates.lean`. Edit the
  emitter → the `#guard` reds → a human updates the digest → **the file on disk still holds the old
  bytes and nothing looks.**
- **Twenty artifacts carry no pin at all**: `fri_fold_template.json` (1.7 MB), `fri_fold_witness.json`,
  `merkle_path_bn254_d{3..18}.json`, `query_pow_n{0,16}.json`. Searched `metatheory/` for
  `friFoldTemplateJson|merklePathJson|queryPowJson|friFoldWitness` and for the byte lengths — zero hits.
  `fri_fold_witness.json` is the sharpest: `gen_fri_fold_template.lean:11-12` says it dumps "the same
  object `friFold_leaf_refines` quantifies over", and nothing equates the file to the term.

Measured today (by the sweeping reader, recomputing length + FNV-1a over the files): all nine
digest-pinned artifacts currently agree with their pins. **That agreement is unenforced luck, not a
gate** — and `git status` at the time of writing shows six of them `MM` and `chain/gnark/emitted/selectors_db14.json`
`AD`, i.e. they move by hand while a ceremony is mid-flight. `circuit/descriptors/` proves the fix is
cheap and already written — `ci.yml:2021` regenerates from Lean and `git diff --exit-code`s.

### 2.5 Proofs about a term the emitted bytes need not equal — the surviving instances

1. **215 published PI slots the prover chooses.** `Dregg2/Circuit/Emit/UnforcedPiPins.lean:12-16`,
   measured over the three deployed registries: 1 639 pins across 57 wide members, **167** pinning a
   column nothing else references, **48** more pinning a column referenced only on a different row.
   `unforced_pin_admits_any_value` (`:40-45`) proves it constructively: overwrite the column and its
   published slots with any `v` and you have another satisfying witness. This is the general instrument
   for the class and it already exists.
2. **E10 `NEW_COMMIT`.** `turn/src/executor/proof_verify.rs:829-831` claims "the descriptor's
   `pi_binding` at col 261 ties it to the trace's after-block `STATE_COMMIT`, so a forged claim is
   rejected". `:857-861` takes `new_commitment` verbatim from the turn and never recomputes it; the
   defence named is exactly the construct `UnforcedPiPins` proves is not a binding. The falsifier is
   live and states the verdict as open (`circuit/tests/zzz_e10_freeze_owner_falsifier.rs:292-298`).
3. **`MinaAccumulatorAir`'s manifest**, half-closed and self-documented. `:1427-1429` names it —
   "`As : List Pt3` is a free parameter and `accRoutedDesc` will emit any 97-wide table it is handed" —
   and `accumulator_discharge_forced_on_declared_addends` (`:1662`) concludes over "a fold whose addends
   are whatever list the emitter was handed". §10's `accSrsDesc` (`:1615-1617`) replaces the free list
   with a total function; the residual (`:1444-1448`) is that `Gs`/`u⃗` are still emitter parameters and
   the verifier rebuilds the manifest from descriptor bytes without re-deriving it.
4. **`apexShrinkShape`** is 14 hand-written literals (`EmitJson.lean:168-174`) asserted in prose
   (`gen_gnark_emitted_templates.lean:22-24`) to be "the apex-shrink fixture's own numbers". Searched
   `emitted_verifier_full.go` and its test for `apex_shrink_fri_real|LoadRealFixture|fixtures/apex`:
   zero hits. Nothing derives them.
5. **`LightClientMinaAir`'s `SEG_LEN`** — a free witness column in a single-row descriptor, named in
   `LightClientMinaLinkAir.lean:1808-1810` as "the shape `LightClientMinaAir` CANNOT refuse … 290 is as
   cheap to write as 3". The Link AIR closes it (`link_seg_len_counts_the_real_rows`, exercised by
   `short_segment_refused` `:1817-1823`); the bare AIR does not. *Which one the deployed light client
   routes through decides whether this is closed — I did not trace the routing.*

The `maskedLen` precedent is the fix template and it is already applied:
`Market/MpcClearingSecurity.lean:311,339` computes `maskedLen := maskedOpens K b` instead of carrying it
as a field, with the reason recorded at `:575` — "Had `maskedLen` stayed a free field, it was free to be
exactly such a vacuous value."

### 2.6 Hypotheses assumed rather than evaluated

`ChainExtends` (`TauPrefixMonotone.lean:645`) is the honest one and stays honest — but it is honest
about *less* than it carries:

- **It silently absorbs a second unproved fact.** `:70-76`: our `finalLeaderAt` returns `none` unless a
  leader slot holds exactly one block, so a late equivocating leader-slot block *retracts* an anchored
  wave. "Until that is changed, `ChainExtends` also absorbs head-monotonicity, and a live equivocating
  leader can still shorten τ." One named hypothesis, two obligations.
- **Its premise is not enforced.** `ChainExtends` is CM Prop. 3, which CM derives from cordiality.
  `isCordialBlock` is defined (`BlocklaceFinality.lean:705`) and searched: three non-doc occurrences in
  the entire tree (`:705`, `:718`, `:723`) plus two `#guard`s (`:2119`, `:2121`). **No `@[export]`,
  nothing on the receive path.** `blocklace/src/finality.rs:1624`'s `insert_checked` checks predecessor
  presence and equivocation; it never looks at the cardinality of a block's pointer set. The module
  says the same at `:58-66`, and `AckBeforeAdmit.lean:109` calls it "defined, still unwired".
- **It has no downstream consumer.** Searched `tau_finalized_prefix_monotone|tau_executed_prefix_fixed`
  across all `*.lean`: the only hits outside its own module are prose (`Dregg2.lean:1098`,
  `Safety.lean:16`, `OnDemandFeasibility.lean:44,221`). It is a terminal theorem, cited in English.

And `ClosedExtension` — the hypothesis the module presents as *discharged* by the receive path — is
false of the wire (§0.4). So T5's two hypotheses are: one imported from a paper whose premise we do not
enforce, and one that does not hold of the object we build.

The historical instance is worth keeping in view because it is the same shape with the opposite
outcome: `FinalizedRegionStable` was three assumed fields; two became real theorems (`tauStep_stable`
`:409`, `enrolledId_stable` `:477`) the moment τ matched CM Def. 6. **The hypothesis was unprovable
because our definition was wrong, not because the fact was hard.** That is the diagnostic question to
ask of every surviving assumption: *is this unproved because it is deep, or because something upstream
of it is the wrong shape?*

---

## 3. INSTRUMENTS — is each one measuring the thing the defect lives in?

### 3.1 The guard ratchet is measuring a population whose right disposition is deletion, not conversion

`scripts/check-guard-discipline.py` (779 lines) is unusually self-aware: it names its own blind spots
in its header (which guards remain; a guard converted to a vacuous theorem; a guard deleted rather than
converted; the rename-laundering hole that motivates arm (d)). The baseline is **15 262 guards across
1 152 modules**, down from 15 850 measured 2026-08-02 — a real burndown, and slow.

The re-frame it is missing: **most of the population is byte pins on emitted strings, and the binding
those need is §2.4's file gate, not a name.** The top rows are emit modules —
`EffectVmEmitRotationV3.lean` 256, `AutomataflResolveEmit.lean` 209, `ParamComposeGoldenShapes.lean`
154, `ChipTableEmit.lean` 92. Converting `#guard emitJson x == "…"` to
`theorem … := by native_decide` buys a name, a term and an axiom record — and binds *nothing further*,
because the gap is not "is this fact trustworthy" but "does the file on disk equal this string". Once
the regenerate-and-`git diff --exit-code` gate exists, most of those guards are **redundant with a
stronger check and should be deleted**, and the ratchet counts a deletion and a conversion identically
(its header says so).

So: the ratchet is a correct gate on the *habit* and the wrong ledger for the *work*. The ~200 guards
that sit on **seams** — differentials, corpus-adequacy, twin comparisons — are worth every unit of
conversion effort. The ~12 000 that sit on emitted bytes are worth a gate, after which they are worth
deleting. Splitting the baseline into those two populations would let the ratchet say something true
about progress.

**Where the ratchet already worked, and it is the good outcome.** The stale rows in the current
working tree are `AutomataflRules.lean` 110→0, `MultiwayTugFFI.lean` 60→0, `AutomataflFFI.lean` 52→0 —
and the *new* `AutomataflRulesFixtures.lean` carries exactly **110 `native_decide` + 110
`#assert_compiled`**, `MultiwayTugFFIFixtures.lean` exactly 60/60, `AutomataflFFIFixtures.lean` 52/52.
Those are genuine 1:1 conversions: a guard became a named theorem with its compiler trust in the axiom
record. That is why `Dregg2/Games/` is the compiled-trust epicentre — 76% of the `native_decide` mass
and 70% of the `#assert_compiled` mass — and the policy earned it.

**Three things the header does not say, and one it under-sells.**

- ⚑ **Scope is `metatheory/` only** (`:150`, `:745`). `orb/`'s 1 111 guards have **zero rows** — see
  §0.2. About 7% of the corpus's guards are outside the ratchet entirely.
- **`--allow-increase` disables both `d1` and `d2` with one flag** (`:369`, `:373`) and has been used
  **twice on the live record**: `scripts/guard-discipline-baseline.txt:16` (+79, labelled "DEBT MARKER,
  NOT APPROVAL", the wrap_main cone) and `:49` (+1). The ratchet has been turned up 80 guards' worth by
  its own escape hatch — which is fine as a *labelled* debt marker and would be invisible without the
  provenance stamping, so the design is doing its job here.
- **Nearly every provenance line is stamped `-DIRTY`** — refreshes from uncommitted trees are the norm,
  which is precisely the shape the header calls out at `:86-88`.
- **Under-sold:** it implements every arm it describes, including the refresh gate `d1/d2/d3`
  (`:369-389`), *plus* an undocumented fourth — `audit_baseline_integrity` (`:208-241`, wired at
  `:758-768`) re-derives the header `# TOTAL` and the provenance terminus from the row sum, catching a
  hand-edited row. All arms are red-proofed against a synthetic tree (`:502-703`). This is a better gate
  than its own prose admits.

*Working-tree state at the time of writing (not a defect — a ceremony mid-flight):* the gate is RED —
2 modules above baseline (`Consensus/TauPrefixMonotone.lean` 21→37, `Distributed/BlocklaceFinality.lean`
95→125, both today's consensus work) and 8 stale rows. Ledger integrity itself is clean: header
`# TOTAL 15262` equals the row sum.

### 3.2 Cost instruments — measured at the parameter that is convenient

Demonstration 2 confirmed verbatim. `node/src/round_advance_gate.rs:297` builds
`cross_linked_lace(&keys, 1)` and consults at `1` (`:300`, `:312`); the only sweep is committee size
`[3, 5]` (`:293`). The wound is stated in the file at `:330-335`, and the remedy already exists —
`es_gate_cost_against_round_depth` (`:345-385`, depths `[1,4,8,10,11,12,16,24,32,48]`) — **and is
`#[ignore]`d at `:346`.** Four siblings:

| instrument | sweeps | cost lives in |
|---|---|---|
| `dregg-lean-ffi/tests/round_advance_probe.rs:63-80` | nothing; 100 repeats of one 3-round wire | round depth |
| `node/src/finality_gate.rs:864-914` | nothing; one point, n=5 / 6 rounds | round depth — and it is the **named wedge-regression test** ("the wedge is back", `:913`) with an *absolute* `elapsed < 10s` at `:910` |
| `intent/src/solver.rs:1053-1059` | nothing; `max_ring_size: 4` (`:1048`), fixture is 50 *disjoint* 2-cycles (`:1030-1044`) | ring length |
| `turn/tests/perf_growth.rs:149-196` | ledger size M (correct) | actions-per-turn / effects-per-action, both hard-fixed at 1 (`:158-165`) |

And the more insidious variant: `blocklace/tests/perf_growth.rs:171-206` *does* sweep depth (rounds 25
and 225) with a machine-independent growth-exponent bound (`FINALITY_SLACK=3.0`,
`FINALITY_EXPONENT=2.2`, `:42-43`) — an exponential would have blown it wide open — but it measures
`dregg_blocklace::ordering::tau` (`:189`), the **Rust twin**, not the Lean deployed path. Right
parameter, wrong implementation. That harness *looks* like it covers the case.

The one correct instrument, `node/tests/verified_order_budget.rs:239-338` (rounds
`[5,10,20,40,60,80,120,160,240]`, Lean path, prints a local growth exponent), is also `#[ignore]`d
(`:240`).

### 3.3 Differentials that compare through a canonicalizing projection

Each normalization is a projection, and a projection is exactly a class of divergence made invisible.

| site | normalization | checks | blind to |
|---|---|---|---|
| `node/src/blocklace_sync.rs:2749-2757` | `sort_unstable()` on `(seq, creator)` | multiset equality | **any reordering** — precisely what the over-budget fallback substitutes (`:2674-2710`) |
| `node/src/finality_gate.rs:594-611`, `:686-697`, `:797-834`, `:942-954` | `HashSet` ×4 | set equality | reordering **and** duplicate coordinates |
| `blocklace/src/ordering.rs:1701-1709` | `.sort()` | multiset vs the Lean golden | within-cohort permutation only — `:1711-1736` then checks seq-cohort structure. Honest and documented (`OPEN-CM-XSORT`, `:1663-1668`) |
| `blocklace/tests/consensus_fault_sim.rs:1049-1057` | `.sort()` | multiset across two node views | mitigated by the `cohorts()` comparison at `:1060-1078` |

The one place the *sequence* is checked: `node/tests/verified_order_budget.rs:191-202`, unsorted, with
`coords_in_order` at `:137-141` explicitly "NOT sorted: the sequence is the point". Its coverage is
n ∈ {3,4,5} × rounds ∈ {3,6,9} — nine points, and the soundness of the entire over-budget Rust
substitution rests on them.

Negative, with what was searched: `HashSet<(u64` repo-wide over `*.rs` excluding `target/`/`vendor/` —
four hits, all in `finality_gate.rs`. Fifty `tests/*differential*` files grepped for `.sort()`,
`sort_unstable`, `HashSet`, `BTreeSet`, `dedup`, `format!("{:?}"` — the circuit/DSL/FHE/protocol-tests
differentials came back clean; they compare structurally. No `format!`-then-compare, no sorted-key-JSON
differential.

### 3.4 The compiler-trusted surface is load-bearing exactly where the kernel-clean surface is blind

**1 994** `native_decide` and **1 836** `#assert_compiled`, comment-stripped (the raw greps of 3 217 and
2 114 are ~38% and ~13% prose — `Dregg2.lean` narrates "#assert_axioms-clean" dozens of times). The
near-1:1 ratio says the "label your compiler trust out loud" policy is genuinely followed *at that
layer*. The mass is in **fixture** modules — `Games/AutomataflRulesFixtures.lean` 110,
`Games/MultiwayTugFFIFixtures.lean` 60, `Games/PathOfAngels/CrewFieldMissionFixtures.lean` 58,
`Games/AutomataflFFIFixtures.lean` 52 — i.e. case tests that moved into Lean: 76% of the `native_decide`
mass and 70% of the `#assert_compiled` mass sits in `Dregg2/Games/`. Moving them there did not make them
verification, and `#assert_compiled` is the honest label for them.

⚑ **And that is the inversion.** The *loud, instrumented* compiler-trust surface sits on game fixtures.
The *silent* compiler-trust surface — `#guard`, no name, no term, no axiom record — sits on the
**descriptor emitters**: `EffectVmEmitRotationV3.lean` 256, `AutomataflResolveEmit.lean` 209,
`Exec/TurnExecutorFull.lean` 173, `Exec/Program.lean` 167, `Exec/DeployedConstraint.lean` 153 (5
`@[export]`), `Distributed/BlocklaceFinality.lean` 125 (3 `@[export]`), `Exec/FFI.lean` 117 (10
`@[export]`). Every one of the top thirteen except `Games/Dungeon.lean` is a descriptor emitter or the
turn executor. Of the 661 `@[export]` sites, only 407 `native_decide` occurrences sit in modules that
also export — and they are concentrated in `FinalityGate.lean` (11 exports),
`Crypto/Fips204Verify.lean` (12), `RoundAdvanceGate.lean`, `AckBeforeAdmit.lean`,
`Crypto/MlKemDecaps.lean`, `Grain/R3Verify.lean`, `Bridge/MinaBinprotRealBlock.lean`. **The deployed
path's assertions are the ones without names.**

But note where it lands next: `Crypto/Fips204Verify.lean` (30) and `Crypto/KeccakCavp.lean` (39) hold the
ACVP/CAVP KATs, and §0.1 established that **those KATs are the only thing in the tree that can see a
permuted NTT twin.** Meanwhile `Crypto/NttFaithful.lean` (35) proves ∀-facts about the *pure* `ntt`,
which the runtime never executes. So on the ML-DSA path the kernel-clean theorems are about the
unexecuted def and the compiler-trusted vectors are about the executed one. That is not a criticism of
either — it is the map: **the two surfaces do not overlap where it matters, and only the compiler-trusted
one touches the running code.** S1 is what makes them overlap.

---

## 4. STRATEGY — ranked by binding gained per unit of effort

The ranking principle, learned from today: **a move that makes a defect unrepresentable outranks any
amount of checking, and a move that makes a false hypothesis true outranks proving more around it.**
`DWireOutcome.malformed` not being a `DAdmit` beat any amount of checking. `causalPastAuxFast_eq`
returning the *identical list* meant zero theorems needed re-proving. Both are the same move.

**Where else the move applies, concretely** (each is a free value beside a derivable one):

| site | the free thing | the unrepresentable form |
|---|---|---|
| `MlDsaRing.lean:346-350` | an `implemented_by` on the pure def, which makes its own differential a tautology | attach to an alias; a lint refuses the direct form (S1) |
| `turn/src/executor/proof_verify.rs:857` | `new_commitment` accepted from the turn | a type indexed by `(pre_state, turn)` — the `RelicList mission.allowedRelics` move, `RelicNamespace.lean:164-167` |
| the 215 unforced PI slots (`UnforcedPiPins.lean:12-16`) | a published column nothing forces | `SeamSpec.lean`'s `CoveredPort` already **refuses to elaborate** for a port no seam covers — extend it to all three registries |
| `MinaAccumulatorAir.lean:1427` | `As : List Pt3` handed to the emitter | §10's `srsScaledAddends Gs u n`, a total function — done for the addends, still open for `Gs`/`u⃗` (`:1444-1448`) |
| `LightClientMinaAir` `SEG_LEN` | a free witness column ("290 is as cheap to write as 3") | the Link AIR's `link_seg_len_counts_the_real_rows` |

### S0 — Close the three fail-open paths in `Tactics.lean`. Minutes.

**Effort: three `throwError`s, copied from thirty lines below in the same file.**

- `#assert_all_clean` (`:68`) — error on an empty list, exactly as `:228-230` does.
- `#assert_namespace_axioms` (`:359`) — error when `checked == 0`, exactly as `:245-247` does.
- `isNativeOracleAxiom` (`:116`) — stop recognising an oracle by *name pattern*. Check the axiom's
  provenance (it is generated for the declaration being pinned), or at minimum require the axiom to be
  in the same module and reject a user-declared `axiom` outright.

**Binding gained: the highest ratio in this document, by a wide margin.** 22 380 + 478 + 95 + 1 836 pins
currently rest on commands with a demonstrated path that passes while checking nothing (§0.1), and the
compiler-trusted surface — the one that actually touches running code (§3.4) — is pinned by the weakest
of the four. Nothing else here costs minutes.

While in the file: add the `unless info.isThm` filter to the single-name form, so the 358 pins aimed at
`def`s become visible rather than free.

### S1 — Move every `@[implemented_by]` off the pure def onto a `…Fast` alias, and gate it

**Effort: hours.** Five alias defs + five attribute moves in `MlDsaRing.lean:346-350`, retarget
`MlDsaVerifyReal`/`MlDsaSignReal`/`MlDsaKeygen` call sites to the alias, plus one
`scripts/check-implemented-by-alias.py` that refuses any `implemented_by` whose target is reachable from
an `@[export]` without an alias.

**Binding gained: the largest absolute gain in this document** (S0 is the better ratio; this is
the bigger prize). It converts five seams from *no differential is
expressible in Lean* (§2.2, demonstrated) to *a differential is expressible*. Today the naive fix is a
green tautology, which is worse than no fix because it reads as closure. The gate makes the wrong shape
unrepresentable, which is the move that keeps working after we stop paying attention. This is
"unrepresentable over checked" applied to the seam *mechanism itself*, and it is cheap because there
are only six seams.

### S2 — A corpus-adequacy theorem beside every differential

**Effort: one named theorem per differential; ~20 differentials that matter.**

`laceUnevenPreds_layer_repeats_an_id` (`BlocklaceFinality.lean:2394`) is the single best artifact this
census found: a *named theorem asserting the corpus has the property that makes the differential
meaningful*, so that if a future edit makes the lace uniform, the build reds **before** the differential
silently re-blinds. Nothing else in the tree has one. It is also the direct antidote to the
falsifier-that-stopped-falsifying class: re-emitting a fixture disarms every test that mutates it, and
only a corpus-adequacy assertion notices.

Immediate instances: for `MlDsaRing`, a full-range corpus (coefficients near `q-1`, `q/2`, `2¹²`) plus
`theorem sample_products_reach_past_2_32 : … := by native_decide` — because today the maximum product
is 4 (§0.2). For seam 6, at least one more non-uniform lace, and one that exercises
`fastEnrolledFilter` under equivocation.

**This is the generalization of demonstration 1**, and it is a *policy* rather than a fix, which is why
it ranks above the individual repairs below.

### S3 — A vacuous-statement rejector

**Effort: one script, or one `CommandElabM`.** Refuse a `theorem`/`lemma` whose *statement* is `True`,
`P ↔ P`, `P → P`, or `a = a` with syntactically identical sides. Nothing in `scripts/` does this —
`check-guard-modules.py` gates that the `#assert_axioms` pins *run*, not that what they pin *says*
anything.

Current population: 4 outright (`Circuit/FriVerifier.lean:1056`, `CommitBindsGuards.lean:62`,
`PicklesSynthesis.lean:181`, `MinaBridgeGuards.lean:105`), 1 degraded
(`Games/PathOfAngels/EditorialRegistry.lean:181`), and ~112 `: True := by fail_if_success …` (§0.4).
For that last class the rejector should not delete the check — it should force the *statement* to carry
it, which usually means a decidable predicate over the constructor's accessibility rather than `True`.
Pair it with an allow-list so the `orb/Hygiene/SelfTest.lean:31,34` calibration fixtures stay.

This is the ratchet's stated blind spot #2 (`check-guard-discipline.py:44-45`) made into a gate, and it
closes the loop on §3.1: without it, a burndown and a laundering are the same number.

### S4 — Make `ClosedExtension` true of the wire, rather than proving around it

**Effort: an encoder change plus a Lean generalization. A wire flag day.**

The Lean-side fix alone (weaken `grown` to a relabeling embedding) is the wrong shape: it makes the
hypothesis harder to state and does not remove the renumbering. The right fix is at the encoder. Make
the interned `BlockId` a *position-independent* function of the block — pack `(seq, creator_index)` into
the `Nat` — so that ids no longer shift when a late low-`seq` block arrives. Then:

- `grown` weakens from `B' = B ++ new` to `B.Sublist B'` (or just `∀ b ∈ B, b ∈ B'`), which is what the
  wire actually gives, and `lookup_stable` re-derives from `ids_nodup` alone.
- Because `(seq, creator)` lexicographic order is exactly today's index order, `xsortBy`'s tie-break
  (`a ≤ b` on ids) is **unchanged**, so the finalized order should not move. ⚠ *I did not verify that
  by running it; verify before landing.* If it does move, say so in the commit — it re-genesises.

**Binding gained:** T5 stops being a theorem about an object we do not build. That is worth more than
any downstream theorem stacked on a false premise. Says what breaks: the lace wire format
(`node/src/finality_gate.rs:129-186`), every fixture that hard-codes interned ids, and the Lean
`ClosedExtension` statement.

### S5 — The `chain/gnark/emitted/` regeneration gate

**Effort: a copy of an existing job.** `ci.yml:2021` (`descriptor-drift`) already regenerates
`circuit/descriptors/` from Lean and `git diff --exit-code`s. Point the same shape at
`metatheory/scripts/gen_*.lean` → `chain/gnark/emitted/`.

⚠ Copy the shape, not the routing. `descriptor-drift` carries `if: github.event_name != 'push'`
(`ci.yml:2023-2025`) — a 330-minute job against a 92-second commit cadence, so it runs nightly / on a
PR / on demand and **never on a push to main**. That is a defensible trade for a 330-minute
regeneration; it is not defensible for a JSON re-emit that takes seconds. Route the gnark one on push.

**Binding gained:** closes the byte-level `allowed_relics` for **29 artifacts** (9 pinned-but-ungated,
20 unpinned) that a Go verifier compiles an R1CS from today. It also makes ~12 000 `#guard` byte pins
redundant, which turns §3.1's ledger problem into a deletion.

### S6 — Point the whole gate apparatus at `orb/`

**Effort: a scope change in three scripts plus a baseline generation.** `scripts/axiom-hygiene-guard.sh:38`
(`META="$ROOT/metatheory"`), `scripts/check-guard-discipline.py`'s census root, and the `Tactics.lean`
commands `orb/` has simply never adopted (zero `#assert_compiled`, zero `#assert_namespace_axioms`).

**Binding gained:** it is the corpus with 28 real axioms on the live TLS/QUIC/cache datapath and 1 111
uncounted `#guard`s (§0.2). Ranked here rather than at S0's level only because generating an `orb/`
baseline is a real burndown commitment, not a flag flip — but the *first* half (turn the census on and
publish the number) is a flag flip.

### S7 — Mechanize the premise-inhabitability vocabulary we already have, and point it outside `Circuit/`

⚠ **Correction to my own first draft of this item**, which said "nothing measures the premise
footprint". That is false, and it is the exact negative-from-an-incomplete-corpus mistake this document
is supposed to catch. The instrument exists: `Dregg2/Circuit/PremiseInhabitability.lean` (867 lines),
`…ConclusionAxis.lean` (1 006), `…Sweep.lean` (747), `…SweepSettled.lean` (1 490) — **4 110 lines** with
a worked-out vocabulary (`Empties`, `YieldsAt` + `not_of_yieldsAt_refutedAt` as the sharper
point-refutation form, upper/lower brackets, `Discriminating`), plus `VacuitySweepTeeth.lean`,
`ApexPremiseVacuity.lean`, `ExistsImageVacuity.lean`.

So the gap is not conceptual. It is **mechanization and coverage**, and both are cheaper than inventing
the semantics.

1. **Mechanize it. It is about fifteen lines, and I ran it.** A `CommandElabM` that walks the
   environment for constants whose conclusion head is a given `Prop` answers "is this ever produced, or
   only ever assumed" directly:

   ```lean
   run_cmd do
     let env ← getEnv
     for nm in [`…TauPrefixMonotone.ChainExtends, `…TauPrefixMonotone.ClosedExtension] do
       let mut out : Array Name := #[]
       for (n, ci) in env.constants.toList do
         if n.isInternal then continue
         if ci.type.getForallBody.getAppFn.constName? == some nm then out := out.push n
       logInfo m!"{nm} — conclusion-position producers: {out.toList}"
   ```

   Output: `[ChainExtends.mk]` and `[ClosedExtension.mk]` — the auto-generated constructors and nothing
   else. That is the whole check for the `StepCanon` class (§0.3, 378 binders, zero producers), and it
   is a *pin*, not a sweep: `#assert_premises` next to each `#assert_axioms` on the apexes makes the
   premise list change **visibly in a diff**, which is the property a manual campaign can never have.
   ⚠ A constructor-only result is evidence, not proof of vacuity — a term can be built by typeclass
   synthesis or as a field of a larger bundle — so the command should report, and only red on an
   explicit expectation.
2. **Point it outside `Circuit/`.** Searched all four sweep modules plus `VacuitySweepTeeth.lean` for
   `Distributed|Consensus|ChainExtends|ClosedExtension|CrossNode`: four incidental hits across 5 600
   lines. The rows name `GroundedApex`, `AggAirSound`, `FriLdtExtractDeployed`, `CircuitCompleteness`,
   `VerifierKernel` — circuit and crypto soundness classes. **The consensus premises have never been
   swept**, and §0.4 and §2.6 are two of them found by hand this week.

### S8 — Point the existing cost instruments at the parameter the cost lives in

**Effort: hours; the tests already exist.** Un-`#[ignore]` `round_advance_gate.rs:346` and
`verified_order_budget.rs:240`. Replace the absolute `elapsed < 10s` at `finality_gate.rs:910` with a
growth-exponent bound of the shape `blocklace/tests/perf_growth.rs:42-43` already uses — an absolute
threshold at one shallow depth is a test an exponential passes forever. Point
`blocklace/tests/perf_growth.rs:189` at the Lean export rather than the Rust twin, or add a second
sweep that does.

### S9 — Sequence-level comparison where the property *is* the sequence

**Effort: four call sites.** `finality_gate.rs:594-611`, `:686-697`, `:797-834`, `:942-954` — compare
`Vec` sequences, not `HashSet`s, or change the assertion messages to stop claiming order-faithfulness
they cannot witness (§0.6). The nine-point sequence differential at `verified_order_budget.rs:191-202`
is currently the whole basis for the over-budget Rust substitution; widening its corpus is cheap.

### S10 — Wire `isCordialBlock` before formalizing CM Prop. 3

**Effort: one `@[export]` + a refusal policy.** This inverts the sequencing the module implies. CM
Prop. 3 is a real quorum-intersection formalisation over the DAG — days to weeks — and its product
would still be **inapplicable**, because the premise it derives from is not enforced anywhere on the
receive path (§2.6, searched). Wiring the predicate converts the whole leader-safety story from
*unavailable in principle* to *available*, and it is the cheaper half. ⚠ Unlike a missing predecessor,
a cordiality failure is not fixable by waiting, so it needs a refusal policy rather than buffering —
that is the design decision, and it belongs to the operator.

### S11 — Extend the citation gate to non-Lean names

**Effort: a rule in an existing script.** `scripts/check-lean-citations.py` was built yesterday for
exactly the `FinalizedRegionStable` class and covers tracked `.rs`/`.lean` comments. §0.5 is the same
wound one file type over: a `Test\w+` name cited in `.github/workflows/*.yml` that no Go file declares.
One additional form in the same script.

---

## 5. WHAT IS NOT WORTH ITS COST

An honest list, because the brief asked for one.

- **Converting emitted-byte `#guard`s one at a time.** ~12 000 of the 15 262. A name and an axiom
  record buy nothing when the gap is file-versus-string. Gate first (S4), then delete. Converting them
  before the gate exists is motion, and it inflates a burndown number that will later be retired
  anyway.
- **`tauOrderFast_eq` as coverage of seam 6.** It proves the *pure* `tauOrderFast` equals `tauOrder`
  (`BlocklaceFinality.lean:1096`), and `tau_order_export_eq` (`FinalityGate.lean:376`) rewrites through
  it — so the theorem covers a function the runtime does not execute. It is not worthless: it licenses
  the RHS of the differential. It should stop being cited as though it constrains the twin. The file is
  honest about this at `:1162-1165`; the citations elsewhere are not.
- **Formalizing CM Prop. 3 now.** See S10. Real work, correct eventually, currently inapplicable.
- **More theorems downstream of `ClosedExtension`.** Every one is a theorem about an object we do not
  build until S4 lands.
- **A second Rust order implementation as "the differential".** `blocklace/src/ordering.rs::tau` is
  compared against the Lean order through a `sort` at `:1701-1709` and is the thing measured by the one
  perf harness that sweeps the right parameter (`perf_growth.rs:189`). Two implementations that agree
  through a projection are not a differential; they are two shapes that will disagree later, and the
  repo has a long list of exactly that.

---

---

## 5b. Two smaller facts worth recording

- **There is exactly one real `sorry` in `metatheory` + `orb`** after comment/string stripping:
  `metatheory/Dregg2/Bignum/LedgerBalance.lean:456`, closing `biasedLimbs_valid` — the *completeness*
  pole of the signed-ledger limb encoding, documented at `:439-451`, with its *soundness* dual
  `biasedLimbs_unique` (`:466-471`) proved outright. `Dregg2.lean:1147` flags it and states the module
  is **model only: no descriptor, no emit path, no VK, no Rust constraint**. Not load-bearing. ⚠ But
  `scripts/axiom-hygiene-guard.sh:2` says it forbids `sorry` "FOREVER" and `:134` asserts "ZERO sorry /
  admit / sorryAx". Those two facts are in tension; whether the guard trips depends on whether
  `Dregg2.lean:1147` is in the built target. Resolve it in one direction — either allow-list the named
  sorry with its reason, or stop claiming zero.
- **The `orb/Cache/VaryKey.lean:120-127` pattern is the shape to copy** for every uninterpreted
  primitive: `axiom hash : KeyMaterial → Digest` is an uninterpreted *function*, and collision-freeness
  is carried as a `def CollisionFree` **premise** on the theorems that need it, never as an axiom. That
  is exactly the "per-instance side condition, not a field" doctrine the `BundleCutoverCheck` campaign
  landed on the circuit side, arrived at independently in a different corpus.

---

## 6. What I did not check

- Whether the deployed light client routes through `LightClientMinaLinkAir` or the bare
  `LightClientMinaAir` (§2.5 item 5). That routing decides whether `SEG_LEN` is closed.
- Whether S4's id-packing preserves the `xsortBy` tie-break in practice. The argument is in S4; it is an
  argument, not a run.
- `blocklace/src/` beyond `finality.rs::insert_checked` and `ordering.rs`'s differential block.
- The `circuit-prove` leaf adapters (`note_spend_leaf_adapter.rs:526`, `custom_leaf_adapter.rs`,
  `caveat_admission_leaf_adapter.rs`, `solvency_leaf_adapter.rs`, …), which all take
  `public_inputs: &[BabyBear]` from a caller. That is the natural next place to apply the E10 question
  one adapter at a time, and nobody has.
- `headver/` is a git worktree pinned to a pre-fix commit and still contains the keep-first divergence
  (`headver/metatheory/Dregg2/Distributed/BlocklaceFinality.lean:829-836`). Harmless if nothing builds
  from it; worth one command to confirm nothing does.
- Whether the `StepCanon` environment walk (S7's prototype) returns constructors-only for `StepCanon`
  itself. I ran it for `ChainExtends`/`ClosedExtension`; `AutomataflStepRefine.olean` in this working
  tree has an incompatible header (a lane is mid-rebuild), so §0.3's zero-producer claim rests on the
  textual sweep — every non-comment mention read in both trees — not on the environment walk. Re-run it
  once the olean is current; it is the first thing S7 should be pointed at.
- Whether `metatheory/Dregg2/Metatheory/OptimisticAdjudication.lean:401`
  (`theorem all_honest (i : Bool) : CF.Honest i := fun h => h`) is a `P → P` in disguise or intended
  given `CF.Honest`'s definition. Flagged, not read.
</content>
</invoke>
