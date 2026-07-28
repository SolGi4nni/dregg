# OPENING SOUNDNESS, DECONFLATED — "the floor" is THREE things, not one

**2026-07-27, rev. 2.** Every reference below verified by reading the statements at HEAD, not grep.
This document replaces the reflexive catch-all — *"the FRI/IPA opening soundness floor"* — with
the precise 3-way split it has been hiding. **Nothing deployed changes here; this is a naming
correction + a census.** It does not edit any Lean carrier.

> **rev. 2 corrects rev. 1 on three points**, each recorded rather than silently patched: (a) rev. 1
> said the bits move with `num_queries` — **refuted** for the column that binds
> (`query_and_pow_cannot_pass_epsC`); (b) rev. 1 said the `FriLdtExtractV3` apex cutover was
> outstanding — it **landed 2026-07-25**, and what remains is one conjunct over; (c) rev. 1 called
> `Poseidon2SpongeCR` a correctly-carried standard assumption — it is **proven FALSE at deployed
> parameters**, across 276 files. The census below is the full enumeration rev. 1 left as a
> placeholder.

## Why this exists

The phrase *"the floor"* (also: "opening soundness floor", "FRI floor", "STARK floor",
"extraction floor", "IPA `msm==0` floor", "the terminal FRI/IPA soundness floor") is cited across
the docs and memory as if it named **one** irreducible, operator-gated, possibly-unprovable
weakness. It does not. It fuses three categorically different objects, and the fusion is the
cargo-cult: it makes a **parameter dial** look like a wall, makes a **provable theorem** look like
a permanent assumption, and staples **Mina's discrete-log assumption** onto **dregg's hash-based
STARK** as though they were the same carrier.

The single clearest fusion site is `docs/MINA-DREGG-ZKAPP-BRIDGE.md:58`, which writes
*"the terminal FRI/IPA soundness floor, inherited not discharged"* — one phrase covering **(c-Mina)
Mina's IPA over the Pasta cycle (discrete log)** and **dregg's FRI (Poseidon2-CR + FS-RO)** at
once. They share no assumption.

## The split

| tag | what it actually is | is it a fundamental unprovable dregg weakness? |
|---|---|---|
| **(a) bits-dial** | a soundness-*bits* number (51 / 57 / 61 / ~31 / 122.6). A `Finset` density ratio or a `(1−δ)^k` calculator output. | **No** — but it is a **stiffer** dial than "just crank the queries", and §(a) below states exactly which knob moves which column. Not a floor; also not free. |
| **(b) provable-proximity-theorem-not-yet-fully-connected** | the absence of a machine-checked FRI-soundness theorem wired to the deployed verifier. | **No.** The core (BCIKS20 proximity gaps / UD-regime correlated agreement) is **UNCONDITIONAL / statistical** and is **already proven on our disk**. It is an engineering *connection* residual, not a hypothesis. |
| **(c) standard-named-assumption** | the actual cryptographic assumption the accept-side rests on. | **No.** Each is standard and named: **Poseidon2 collision-resistance**, **Fiat-Shamir random-oracle** (both PQ-safe, both dregg's), and **discrete-log** — which is **Mina's IPA, not dregg's**. |

None of the three is "a fundamental unprovable dregg weakness." (a) is a knob, (b) is a theorem
we mostly hold, (c) is either a standard PQ-safe named carrier (dregg) or someone else's
assumption entirely (Mina).

---

## (a) BITS-DIAL — a knob, machine-checked as such, but **three columns with three different knobs**

The security *number* is a calculator reading over a chosen parameter set. It contains **no
adversary and no probability quantified over a strategy**. But "it is just a dial" is itself too
loose, and the loose version has already produced a withdrawn claim. The dial has **three columns**,
and `FriLedgerSound.three_columns_three_dependencies:760` proves they move under **different**
parameters:

| column | what it is | moved by | NOT moved by |
|---|---|---|---|
| **query** (`johnsonBits`, 73 deployed) | `q·lb/2 + pow` | `numQueries`, `powBits` | trace height |
| **commit** (`commitBits`, **51** deployed) | BCIKS20 Thm 8.3 `ε_C` | `extDeg`, `logD0` (trace height), `logBlowup` | **`numQueries`, `powBits`** |
| **per-fold** (`perFoldBits`, 112/109) | fiber count at the fold arity | arity, `logBlowup` | queries |

- **51 bits — the deployed reading, and it is the one that BINDS.**
  `FriDeployedHeightPairing.deployed_wrap_commitBits:142` proves
  `(friCommitLedger ir2LeafWrapRotatedConfig 22 7).commitBits = 51` at the pair the Rust actually
  runs (`ir2_leaf_wrap_config()`, arity 2, `logBlowup = 6`, under `WRAP_LOG_CEIL`'s `2^16` floor ⇒
  `|D⁰| = 2^(16+6) = 2^22`). Both circulating rivals are **refuted as the deployed number**: `61` is
  `recursionConfig` at `2^19` (`deployed_wrap_is_not_61:155`) and `57` is the right config at the
  wrong height (`deployed_wrap_is_not_the_proven120_number:164`,
  `the_proven120_correction_is_half_applied:186`). Composing the two columns by ethSTARK eq. (20),
  `min{51, 73} − 1 = 50` — the commit column binds by **22 bits of slack nobody can spend**
  (`the_commit_column_binds_at_the_deployed_pairing:254`).

- **⚑ QUERIES CANNOT MOVE IT. This is a theorem, not a caution.**
  `FriLedgerSound.query_and_pow_cannot_pass_epsC:746` proves that `numQueries: 19 → 200` and
  `powBits: 16 → 27` — plonky3's practical maximum — balloon the query column to `627` and leave
  `commitBits` **literally equal** (the proof is `rfl`: `ε_C`'s formula mentions neither knob). Any
  document that says the soundness number can be raised by buying queries is **wrong about the
  column that binds.** This is what withdrew "proven Johnson 128 at ext-degree 4".

- **The levers that DO move the commit column**, in order of cost:
  1. **`extDeg`** — worth exactly `log₂ p ≈ 30.91` bits per degree, since `ε_C ∝ 1/p^extDeg`.
     `4 → 8` puts the commit column near `~174`. **This is a flag day**: fresh Groth16 trusted
     setup, on-chain re-key, VK rotation, descriptor re-emit. It is also **not sufficient alone** —
     once `ε_C` clears 73 the *query* column binds, so a composite 128 needs both columns moved.
  2. **Trace height (`logD0`)** — `ε_C ∝ |D⁰|²`, so ~2 bits per trace doubling, in the *unhelpful*
     direction: the `2^12` cost fixture reads `71`, `2^20` reads `55`, deployed `2^22` reads `51`
     (`the_fixture_gap_is_twenty_bits:198`). **Smaller turns are more sound.** A batching decision is
     a soundness decision, which nothing in the tree currently surfaces at design time.
  3. **⚑ `commit_proof_of_work_bits` — a THIRD knob, unpriced, and NOT a flag day.** plonky3 has a
     commit-phase PoW ground per fold round *before* `β` (`fri/src/config.rs:18`, `prover.rs:224`) —
     i.e. against exactly the terms `ε_C` bounds — and omitted from plonky3's own
     `conjectured_soundness_bits`. **Every shipped dregg config sets it to `0`**
     (`circuit/src/plonky3_prover.rs:168`, `stark_zk.rs:147`). It is prover cost only: no trusted
     setup, no re-key. `FRI-BOTH-WIN-LEVERS` §4.4 reports ~+5.5 bits at `lb=7`. **No Lean theorem
     prices it.** `query_and_pow_cannot_pass_epsC`'s own docstring scopes itself away from it
     explicitly — it is a theorem about the two knobs `FriParams` carries, and it does not claim to
     be a theorem about the protocol.

- **The 51 survives the pending arity flip** — `arity_flip_does_not_move_the_commit_column`: same
  `logBlowup`, same `|D⁰|`, arity 2 vs 8, both read `51`. So the corrected number does not have a
  shelf life of one commit.

- **~31 bits** — `FriCarrierEpsilon.deployed_forgery_bound:180`: the honest ceiling of the deployed
  FRI *query leg* is `Q·(9/16 + 2^logN/p)^38`, and it goes useless (>1) by `Q = 2^32`
  (`deployed_bound_useless_at_2pow32:196`). "**~31 bits, not 130, not 57.**" A *different* object
  from `commitBits` — never merge these columns.

- **122.60 bits** — `docs/reference/PROVEN-120-CONFIG.md:37,291`. ⚠ Read at the **`2^12` fixture**
  domain (see its own table), not the deployed `2^22`. At the deployed height the same engine's
  commit column reads `51`, and that document's own §3 correction is proven **half-applied**
  (`the_proven120_correction_is_half_applied:186`).

**Tag-(a) correction.** Any citation that reads a bits number as "the soundness floor" is reading a
**dial position** as a wall — but the dial is stiff, the binding column is `ε_C = 51`, and the
knob most people reach for (`num_queries`) provably does not touch it. The bits are real arithmetic;
they are not adversary-quantified security until (b) lands. See `project-fri-soundness-reality` —
*"The 51/57/61 is a `Finset` density ratio."*

---

## (b) PROVABLE PROXIMITY THEOREM — the real residual, and it is a theorem we largely hold

The "missing FRI soundness theorem" is **attackable**, because FRI's core proximity soundness is
**unconditional / statistical** — BCIKS20 "proximity gaps" (Thm 4.1), in the **unique-decoding
regime** we deploy, is elementary, explicit-constant mathematics. On disk **now**:

- **The keystone is PROVEN**: `metatheory/Dregg2/ForMathlib/PolishchukSpielman.lean:739`
  `polishchuk_spielman` (Cramér–Nardi-fixed form, Kopparty 2025 §2.2), `#assert_axioms`
  kernel-clean, `_fires` non-vacuity witness at `:931`. No `sorry`.
- **The L0–L6 correlated-agreement ladder is landed**:
  `metatheory/Dregg2/Circuit/CorrelatedAgreement/{Scaffolding,BerlekampWelch,Interpolation,Collinearity,Theorems,Interface,RlcDischarge,DecimLiftDischarge}.lean`.
- **An adversary object EXISTS** (this is new since `project-fri-soundness-reality`, which said
  "no adversary object anywhere"): `metatheory/Dregg2/Circuit/FriAdversaryObject.lean` — a typed
  prover `Strategy`, the Fiat-Shamir transform as an `OracleComp`
  (`fsRun_queryBounded`, `fsRun_eval` faithfulness), and `chain_far_strategy_of_farCover`
  (farness survives the whole fold chain at an **arbitrary adaptive** strategy). Kernel-clean.
- **The tower far-survival at the DEPLOYED 2^24 instance is proven**:
  `CorrelatedAgreement/Interface.lean:881` `ud_tower_far_survival` (and `_strategy` at `:837`):
  `winProb bad ≤ rounds·(m−1)(r₁+1)/|F|`, with UD-regime correlated agreement as the explicit
  per-layer hypothesis. `deployed_code_eq` (`:516`) pins it to `friSetupDeployed.C` (rate 1/8).
- **The query spot-check bound is proven, non-vacuously**:
  `metatheory/Dregg2/Circuit/DeployedProximitySoundness.lean` — a `7/16`-far word passes the
  deployed 38-query check on `< 2^-31` of samples (`accept_soundness_deployed`), with a concrete
  far FIRE word (`fSq_far`) and an honest near word at ratio exactly 1. Re-proven over the
  **actual non-uniform** deployed sampler in `DeployedProximitySoundnessSampler`.

**What is NOT yet connected** (named, not hidden — the residual is engineering, not a missing
proof of proximity):

1. **The apex-vacuity — OOD half CLOSED (2026-07-25), `tableOpenings` half OPEN.** The extraction
   bundle the apex consumed concluded `oodPoint = [ood]` (a base-field singleton) while the deployed
   acceptance predicate `verifyAlgoUnifiedFaithfulExt` forces the **4-lane quartic**
   (`params.extDeg = 4`) — jointly unsatisfiable, so the apex quantified over an empty accepting set
   and was **vacuously true** (`PremiseInhabitability.lean` §7 rows E1–E5;
   `singleton_forcing_premise_is_false_at_a_real_pole:809` fires on a real accepting pole).
   **Both lanes have since been cut over**: the vacuous assembler was *deleted*, not patched
   (`AlgoStarkSoundTransferV3.lean:256-276`), and relocated to
   `FriLdtExtractDeployed.algoStarkSound_transferV3_cons:641` over `FriLdtExtractV3Cons:323`, with
   `ApexOodLaneRepair.friLdtExtractV3Cons_iff_noOodShape:706` proving the corrected premise adds
   **exactly zero strength**.
   ⚠ **What remains, and the tree states it as a theorem rather than a note.** Every corrected
   bundle still carries `topen ∈ tableOpenings`, which acceptance does **not** supply:
   `FriLdtExtractDeployed.deployed_accepting_pole_has_no_tableOpenings:902` is a `decide`-backed run
   the deployed apex predicate ACCEPTS with `tableOpenings = []`, and
   `ApexOodLaneRepair.friLdtExtractV3Cons_false_of_accepting_run_without_tableOpenings:801` is the
   refutation. Its docstring is the honest summary: *"The cutover therefore trades a premise empty
   EVERYWHERE for one whose emptiness is CONDITIONAL and UNDECIDED: a strict improvement, not a
   closure."* **No corrected bundle has an exhibited model.** See
   `docs/PLAN-fri-proximity-apex-connection.md` §2 and Slice A.
2. **The transcript wire** — `CorrelatedAgreement/Interface.lean` header: *"NOT carried and NOT
   claimed: the wire from the deployed verifier's transcript to these [CA props]."*
3. **The DecimLift `hlift` at the deployed `m=8` arity** — discharged only at the toy `m=1` fire;
   the deployed instance is the named setup-tower engineering.

Ladder rungs already **landed** toward this: L1 (sampler defect composed into the query leg,
`FriVerifierComposeDefected`), L1a (`DeployedProximitySoundnessSampler`), L2-i (the winProb
corollary, `FriChainStepIdx.chain_far_survival`). Full attack plan + first slice:
`docs/PLAN-fri-proximity-apex-connection.md`.

**Tag-(b) correction.** Any citation calling FRI proximity "an assumption" or "inherited not
discharged" is now **wrong about the math**: the proximity theorem is proven. It is correct only
about the *connection to the deployed apex*, which is a partly-landed engineering ladder with one
named vacuity (V3-lane cutover) still open.

---

## (c) STANDARD NAMED ASSUMPTIONS — one of them is not even dregg's

When (a) is a dial and (b) is closed, what remains under the accept-side is a small set of
**named, standard** assumptions. Enumerate them so no one calls the bundle "one floor":

- **(c-P2) Poseidon2 collision-resistance** — carries Merkle binding: the opened trace IS the
  committed oracle's trace (`FriProximityBridge.hplumb`). The *assumption* is standard and PQ-safe.
  **The carrier that implements it in this tree is not.**

  ⚑⚑ **`Poseidon2SpongeCR` IS PROVEN FALSE AT DEPLOYED PARAMETERS — this is the largest vacuity
  surface named in this document.** `Poseidon2Binding.lean:178` defines it as **injectivity**:

  ```lean
  def Poseidon2SpongeCR (sponge : List ℤ → ℤ) : Prop := ∀ xs ys, sponge xs = sponge ys → xs = ys
  ```

  A sponge into BabyBear has finite range and infinite domain, so it **cannot** be injective —
  collisions *exist* by cardinality, they are merely hard to *find*. `HashFloorHonesty.lean:125`
  `poseidon2SpongeCR_false_babyBear` proves `¬ Poseidon2SpongeCR sponge` for every sponge bounded
  by `p = 2013265921`, i.e. for **every real Poseidon2 `hash_many`**. The same file refutes
  `compressNInjective` (`:110`), `compressInjective` (`:132`) and `HashCR` for any compressing
  commit-reveal (`:144`). `Poseidon2Binding.lean:161` says so itself: *"⚠ BROKEN / VACUOUS AT REAL
  PARAMS … every theorem conditioned on it is vacuously true."*

  **Scale, measured at HEAD:** `Poseidon2SpongeCR` occurs **1639 times across 276 files**. The
  honest computational replacement — `HashFloorHonesty.CollisionResistant:204`, a keyed hash family
  with negligible collision advantage against a `CollisionFinder`, refutable *and* satisfiable —
  appears in **40**. A `…Regrounded` migration is visibly under way in `Dregg2/Crypto/` and has
  **not reached the FRI/STARK apex**: `algoStarkSound_transferV3_cons` and
  `ApexOodLaneRepair.algoStarkSound_transferV3_cons_noOodShape:739` both take
  `(hCR : Poseidon2SpongeCR sponge)` — the refuted one.

  **Consequence, stated plainly:** the deployed apex theorem is vacuous *twice over* — once on its
  FRI premise (§(b) item 1, `tableOpenings`, undecided) and once on its hash premise (`hCR`, proven
  false at any real sponge). Neither vacuity is hidden; both are theorems in the tree. Migrating the
  apex's hash leg to `CollisionResistant` is independent of all FRI work and is the cheapest
  vacuity removal available.
- **(c-RO) Fiat-Shamir random-oracle** — `Crypto/RomOracle.lean`, the `OracleComp` free monad;
  the FS challenge budget is priced by `FriChainStepIdx.hit_cond` (`Q·b/|R|`) and `birthday_cond`.
  These are **information-theoretic ROM bounds against query-bounded adversaries** (the BCS16 /
  ethSTARK class) — a *stronger* posture than concrete security, and PQ-safe. This is dregg's, and
  it is the model under which (b) becomes a theorem.
- **(c-Mina) discrete log** — **NOT dregg's.** This is Mina/Kimchi/Pickles' IPA polynomial
  commitment over the Pasta 2-cycle. It appears only where **dregg verifies a Mina proof**
  (`docs/MINA-DREGG-ZKAPP-BRIDGE.md`, `PastaIPA.lean`, the `msm==0` opening check = bridge item
  **C9**). dregg's own STARK has **no discrete-log dependency**. Stapling it into "the FRI/IPA
  floor" is the conflation's sharpest error: it imports a **non-PQ, curve-based** assumption from
  another proof system and reads it as a dregg weakness.

**Tag-(c) correction.** `docs/MINA-DREGG-ZKAPP-BRIDGE.md:58`'s "terminal FRI/IPA soundness floor,
inherited not discharged" must be split: the **IPA `msm==0`** half is (c-Mina), a discrete-log
opening check that is **Mina's assumption**, inherited only when dregg checks Mina; the **FRI**
half is dregg's (c-P2)+(c-RO) with the (b) theorem attached. They are different assumptions on
different systems and must never be printed as one floor again.

---

## Census — the citation sites, tagged

Full enumeration over `docs/`, the repo-root `.md` files, the memory dir, and `metatheory/**.lean`
doc comments, 19 search terms, each hit read in context rather than counted by grep:

| stage | count |
|---|---|
| raw matches (dominated by unrelated senses — `Nat.floor`, `HandlerFloors.lean`, `FloorRatchet`, lattice `*FloorRegrounded`, dungeon floors) | **2,425** |
| narrowed to the FRI/STARK/IPA opening-soundness sense | 348 |
| minus verified false positives (BFT "soundness floor", the `Satisfied2 ⟹ encode` decode-extraction family, source-location citations of `msm==0`) and this document's own self-census | −38 |
| **genuine citation sites** | **≈ 310, across ≈ 140 files** |

| tag | genuine lines | files |
|---|---|---|
| **(a) bits-dial** | ≈ 96 | 38 |
| **(b) formalization gap** | **≈ 230** | **90** |
| **(c-P2) Poseidon2-CR** | ≈ 27 | 18 |
| **(c-RO) Fiat-Shamir ROM** | ≈ 13 | 6 |
| **(c-DL) discrete log — Mina's, not dregg's** | ≈ 42 | 12 |
| *(c-other: MSIS/MLWE — shares the word "floor", NOT part of this split; do not rewrite)* | ≈ 14 | 9 |
| **FUSION sites (≥2 tags in one phrase)** | **≈ 48** | **12** |

**The headline reading: (b) outnumbers (a) + (c) combined, roughly 1.2 : 1.** What people mean by
"the floor" is overwhelmingly the *missing connection* — not an assumption and not a number. That is
exactly the tag the `polishchuk_spielman` keystone undercuts, and exactly the tag that is
**engineering, not research**.

### The fusion sites — one phrase, two or three assumptions

| site | phrase | tags |
|---|---|---|
| `docs/PICKLES-VERIFIER-SCOPE.md:77,88,220,340,342,359` | "the IPA `msm == 0` opening-soundness floor … *inherited, not dischargeable*"; "Phase 3 — the terminal floor" | **(c-DL)+(b)** ×6 — highest-density fusion file in the repo |
| `docs/MINA-DREGG-ZKAPP-BRIDGE.md:57-58` | "the terminal FRI/IPA soundness floor, inherited not discharged" | **(c-DL)+(b)** — the smoking gun |
| `metatheory/Dregg2/Circuit/Emit/KimchiVerify.lean:58,63,333,369,806,847` | "inherits the IPA/FRI soundness floor — NOT discharged here" | **(c-DL)+(b)** ×6 — largest Lean-residual fusion cluster |
| `docs/MINA-REALITY-GATE.md:154,174` | "the terminal IPA/FRI opening-soundness floor, **not discharged**" | **(c-DL)+(b)** |
| `docs/audit/DEEP-proven-substrate.md:32,222,225,355` | "a **Bool calculator** over a named, undischarged extraction" | **(a)+(b)**, and `:355` **(c-P2)+(c-RO)+(b)** |
| `docs/SUPERSEDED/STARK-FLOOR-REDUCTION.md:61,74,89,134,139,145,201,211-214` | "**IRREDUCIBLE FLOOR (`Poseidon2SpongeCR`)**"; "**IRREDUCIBLE FLOOR (FRI-LDT)**" | **(b)+(c-P2)+(c-RO)** — the original three-way conflation, at its source |
| `docs/DESIGN-crown-lowering-and-assurance-ladder.md:78,85` | "crypto floor (FRI/MLWE/DL)" | three unrelated assumptions in one slash-list |
| `docs/MUTUAL-PROOF-SYSTEMS-LANDSCAPE.md:121,154` | "opening-soundness **floors** (dregg's FRI floor; Kimchi's IPA `msm==0`)" | ✅ **already correctly split — use as the model sentence** |

### ⚑ The single highest-leverage site in the repo

`metatheory/Dregg2/Circuit/FriVerifier.lean:1050-1055`:

```lean
/-- The wrap introduces NO new cryptographic assumption: its soundness rests on
exactly `FriLowDegreeSound` (the same FRI floor as the existing apex) plus the gnark
Groth16/pairing soundness (vetted external tooling). … -/
theorem wrap_rests_only_on_named_floor : True := trivial
```

A theorem whose **statement is `True`** and whose **body is `trivial`**, asserting in its docstring
that the wrap's security rests on a carrier that `FriCarrierVacuity.friLowDegreeSound_content_iff_true:123`
proves is **also `True`**. It is the origin of the `FriLowDegreeSound`-as-a-real-assumption reading in
at least five downstream documents, and the document that propagates it hardest —
`docs/deos/FRI-VERIFIER-PROOF-ENGINEERING.md:151,161,186-187` ("the carriers the wrap rests on are
**exactly** `{FriLowDegreeSound, Poseidon2SpongeCR}`") — contains **zero** vacuity awareness anywhere
in the file. Both named carriers in that set are refuted: one is `True`
(`friLowDegreeSound_content_iff_true`), the other is FALSE at deployed parameters
(`poseidon2SpongeCR_false_babyBear`). This is `feedback-a-doc-comment-is-a-name-not-a-proof` at full
size.

### The load-bearing sites, tagged

| site | phrase | tag | note |
|---|---|---|---|
| `docs/MINA-DREGG-ZKAPP-BRIDGE.md:57-58` | "terminal FRI/IPA soundness floor, inherited not discharged" | **(c-Mina)** + (b) | the fusion; C9 IPA `msm==0` = discrete-log, Mina's |
| `docs/PICKLES-VERIFIER-SCOPE.md:340` | "the terminal floor" (Phase 3) | **(c-Mina)** | Pickles/Kimchi over Pasta = discrete log |
| `docs/reference/PROVEN-120-CONFIG.md` | 122.60 / 51 / 57 bits | **(a)** | dial positions |
| `project-fri-soundness-reality` (memory) | "51 CALCULATOR bits" | **(a)** | explicitly the calculator/dial reading |
| `docs/DESIGN-fri-adversary-object.md` | `FriLdtExtractV3` "the one floor" | **(b)** | the discharge ladder; predates the apex-vacuity finding |
| `docs/reference/FRI-EXTRACTION-FLOOR-DESIGN.md` | "extraction floor" | **(b)** | Stages 1–5, all landed |
| `docs/audit/DEEP-proven-substrate.md:355` | "FRI/STARK extraction … Prop-carriers not axioms" | **(c-P2)+(c-RO)** + (b) | correctly named carriers; the FRI half now has (b) |
| `GOAL-FRI-PRODUCT.md` (FRI CAMPAIGN WAVE 1) | "deployed floor is EMPTY" | **(a)→(b)** | the vacuity counterproof; `FriLowDegreeSound ≡ True` |
| `FriVerifier.lean:995,1037,1051` | `FriLowDegreeSound` "the same FRI floor" | **(a)+(b)** | the NAME is a vacuous costume (`FriCarrierVacuity`); real content = (a) dial + (b) theorem |

---

## MISSTATEMENTS TO CORRECT — four classes, each with its refutation

### 1. ⚑⚑ "Raise `num_queries` to raise the bits" — REFUTED for the column that binds

Refutation: `FriLedgerSound.query_and_pow_cannot_pass_epsC:746` (`q:19→200`, `pow:16→27` leave
`commitBits` **literally equal**; the proof is `rfl`), sharpened by
`three_columns_three_dependencies:760`.

- **This document's own rev. 1 carried the bug** at its `:27`, `:51-52` and `:187` — the (a) row
  cited **51** (which is `commitBits`) while telling the reader to move `num_queries`. **Fixed in
  rev. 2** above; recorded here rather than silently corrected.
- `docs/reference/FRI-SOUNDNESS-FRONTIER-RESEARCH.md:294-297` — the lever table ("powBits 16→20
  +3.29", "numQueries 19→25 +7.87"). Scoped correctly at `:9-11`, but the rows carry no
  commit-column carve-out and it is the most-copied table in the repo.
- ✅ **Use as the model:** `docs/reference/FRI-PARAM-FRONTIER.md:253,353,453` and
  `docs/deos/UMEM-POSTQUANTUM.md:188` — *"cannot buy a margin here: `ε_C` contains neither
  `num_queries` nor `pow_bits`."*

### 2. The deployed number stated as 130 / 61 / 57 / 112.6 / 124 with no mention of **51**

Refutation: `FriDeployedHeightPairing.deployed_wrap_commitBits:142`, with `deployed_wrap_is_not_61`
and `deployed_wrap_is_not_the_proven120_number` adjacent.

- **"~130" with no 51** (11 sites): `docs/reference/faithful-commitment.md:5` ·
  `docs/audit/TRUST-BASE-CENSUS.md:26,201,491` · `docs/deos/COMMITMENT-WAIST-CENSUS.md:20` ·
  `docs/deos/RUST-ONLY-LOGIC-CENSUS.md:128` · `docs/deos/PRIVACY-CONFIDENTIALITY.md:247` ·
  `docs/deos/APEX-VERIFIER-AIR-REDUCTION.md:130` · `docs/deos/WRAP-NATIVE-HASH-DECISION.md:130` ·
  `docs/deos/GPU-PROVER-PROTOTYPE.md:29` · `docs/DESIGN-canonical-byte-felt-codec.md:661` ·
  `docs/reference/DEBT-A-STARKSOUND-TARGET.md:143` · `docs/THE-LINKING-TOWER.md:144`.
- **"~57 calculator bits" with no 51:** `docs/MEGASWARM-FLAW-BACKLOG-2026-07-23.md:77` ·
  `docs/WIDER-HUNT-BACKLOG-2026-07-24.md:48`.
- **"~112.6" without the arity-8 correction:** `docs/reference/FRI-EXTRACTION-FLOOR-DESIGN.md:455`.
- **"~124-bit FRI/STARK soundness floor" — conflates a digest WIDTH with a soundness reading:**
  `metatheory/Dregg2/Circuit/DeployedFieldsTree.lean:13`, `DeployedHeapTree.lean:13`,
  `docs/deos/UMEM-STAGE-B-DESIGN.md:105`. 124 is 8 felts of commitment width; it is not any FRI
  column.

### 3. FRI proximity called "an assumption" / "inherited, not discharged" / "unprovable"

Refutation: `ForMathlib/PolishchukSpielman.lean:739` `polishchuk_spielman` (kernel-clean, non-vacuity
witness `_fires:931`), then the `CorrelatedAgreement/` L0–L6 ladder and `FriAdversaryObject.lean`.

- `docs/PICKLES-VERIFIER-SCOPE.md:77,88,220,342,359` — *"inherited, not **dischargeable**"*. The word
  *dischargeable* is now the wrong claim for the FRI half (it remains right for the IPA half, which
  is (c-DL)).
- `docs/reference/FRI-EXTRACTION-FLOOR-DESIGN.md:108,122,123` — *"It is **unprovable-in-principle**"*.
- `docs/DESIGN-fri-adversary-object.md:28` · `docs/MUTUAL-PROOF-SYSTEMS-LANDSCAPE.md:9,134` ·
  `docs/SUPERSEDED/STARK-FLOOR-REDUCTION.md:89,98,211`.
- **Lean residual comments:** `CircuitSoundness.lean:306,481` (*"REALIZABLE, audited, NOT provable in
  Lean"*) · `KernelConfigSoundness.lean:46` · `metatheory/docs/STARK-FLOOR.md:31`, plus a 28-site
  *"inherits the undischarged FRI/STARK floor"* boilerplate cluster across `Emit/`, `Peephole*`,
  `Fri*` and `Market/`.
- ✅ **Already correct:** `docs/PRIVATE-MARKET-DEV-PLAN-2026-07-25.md:32` (*"to ONE elementary
  theorem, not open research"*) · `docs/TRUE-PEERS-ARCHITECTURE-2026-07-26.md:57` ·
  `docs/FORMAL-DEV-PROJECTS-PLAN-2026-07-25.md:43` · memory `project-lightclient-stark-true-peers:49`.

### 4. `FriLowDegreeSound` treated as a real crypto carrier

Refutation: `FriCarrierVacuity.friLowDegreeSound_content_iff_true:123` (⟺ `True`),
`friLowDegreeSound_has_no_falsifier`, `friLowDegreeSoundTrivial` (constructs it at arbitrary
parameters with no hypotheses), `wrap_sound_needs_no_carrier:166` (the payoff with the carrier binder
**deleted**).

- `FriVerifier.lean:34, 992-994, 1036, 1051-1055` — **the origin**, worst at `:1051-1055` (above).
- `docs/deos/FRI-VERIFIER-PROOF-ENGINEERING.md:151,161,186-187` — *"the carriers the wrap rests on
  are **exactly** `{FriLowDegreeSound, Poseidon2SpongeCR}`"*. **Both are refuted.** Zero vacuity
  mentions in the whole file.
- `docs/audit/TRIAGE-2026-07-16.md:1415` (catalogs it as ASSUMED) ·
  `docs/reference/DEBT-A-CARRIER-AUDIT.md:69-70` · `docs/reference/GNARK-LEAN-AUTHORED-PLAN.md:273,294,411` ·
  `GOAL-FRI-PRODUCT.md:335,404,417` (self-corrected later at `:423,460,472`; the earlier lines were
  never struck).

### ⚑ A structural note: the split existed in 2026 and was lost

`docs/SUPERSEDED/PHASE2-ALL-EFFECTS-SOUNDNESS.md:160` already wrote the floor as
`{Poseidon2SpongeCR, FRI-LDT, FS-game}` — exactly (c-P2) + (b) + (c-RO).
`docs/SUPERSEDED/STARK-FLOOR-REDUCTION.md` then **re-fused** them under "the irreducible crypto
floor" in its own title, and *that* framing is what propagated. Both are in `SUPERSEDED/`, but
`docs/SUPERSEDED/STARK-COMPLETION-AUTOMATION.md:154` and `docs/SUPERSEDED/README.md:18` still route readers to
them. **Cut those two pointers.**

---

## The replacement sentences (use these, retire "the floor")

- Instead of *"we inherit the FRI soundness floor"* say:
  **"FRI proximity is a proven statistical theorem (BCIKS20 UD-regime, on disk); the residual is the
  engineering connection to the deployed apex — retyping `DeployedFriEmbedding` to the sampled bar
  and giving the apex premise a model — plus the named carriers Poseidon2-CR + FS-RO."**
- Instead of *"the terminal FRI/IPA soundness floor"* say:
  **"dregg-FRI's carriers (Poseidon2-CR, FS-RO) — distinct from Mina-IPA's discrete-log opening,
  which is Mina's assumption, inherited only when dregg verifies a Mina proof."**
- Instead of *"51-bit soundness floor"* say:
  **"51 bits is the deployed dial position of BCIKS20's commit-phase `ε_C` at `|D⁰| = 2^22`; it is
  the column that BINDS (`min{51,73}−1 = 50`), it is not adversary-quantified until (b) lands, and
  `num_queries` provably cannot move it — the levers are `extDeg` (~30.9 bits/degree, a flag day),
  trace height, and the unpriced `commit_proof_of_work_bits`."**
- Never say *"raise the queries to get more bits"* about the commit column —
  `query_and_pow_cannot_pass_epsC` refutes it by `rfl`.

See also `project-fri-soundness-reality`, `project-fri-correlated-agreement-formalization`,
`docs/DESIGN-fri-adversary-object.md`, and `docs/PLAN-fri-proximity-apex-connection.md`.
