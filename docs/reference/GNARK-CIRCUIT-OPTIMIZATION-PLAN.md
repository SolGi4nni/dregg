# GNARK-CIRCUIT-OPTIMIZATION-PLAN — the safe optimization frontier the refinement unlocked

**Scope:** the outer BN254/Groth16 settlement wrap (`chain/gnark/settlement_circuit.go`,
**~12.87M R1CS** measured). **Premise:** the Lean-authored gnark verifier is now
refinement-proven — `emitVerifier_refines` / `emitVerifier_refines_deployed`
(`metatheory/Dregg2/Circuit/Emit/GnarkVerifier/EmitVerifier.lean:278,299`, keystone commit
`e11e99a6f`). That refinement is a **guardrail**: any emit change that stops computing the
deployed spec-side Bool fails to re-prove its leaf `*_refines`, so the build goes red. This
document maps where the constraint mass is and ranks the optimizations that guardrail makes
safe to attempt aggressively.

**This is constraint-count only.** The FRI soundness floor
(`project-fri-soundness-reality`; a density reading, not a bound — the proven deployed
columns are `FriDeployedHeightPairing.deployed_wrap_commitBits`
and `DeployedProximitySoundness`, digits in `docs/reference/PROVEN-120-CONFIG.md`) and the single-party Groth16
ceremony (`chain/gnark/README.md:50`) are UNAFFECTED — none of these optimizations touch
the number of proven bits or the trusted setup.

---

## 0. HONEST FRAME — what the guardrail actually guards (read first)

Two objects must not be conflated:

1. **The Lean-emitted circuit** (`emitVerifier`, a `GnarkCircuitData`,
   `EmitVerifier.lean:171`) — six leaf gadgets composed in disjoint `Nat.pair` blocks.
   `emitVerifier_refines` proves it faithful to `verifyAlgo`. **This is what the guardrail
   bites.**

2. **The deployed circuit** (`settlement_circuit.go`, ~12.87M R1CS) — a **hand-authored Go
   gnark twin**, differential-tested against the fixtures, NOT yet emitted from Lean. The
   emit→Go cutover is **DESIGN status** (`docs/reference/GNARK-LEAN-AUTHORED-PLAN.md:3`);
   the Go-side interpreter for Lean-emitted JSON exists (`chain/gnark/emitted_interp.go`)
   but is currently byte-pinned to **only `chain/gnark/emitted/canonicity_toy.json`** — the
   full verifier is not yet replayed through it.

**Consequence for every optimization below:** an optimization authored in a Lean emit gadget
and re-proved is proof-guarded **in Lean**. It only reaches the deployed 12.87M when the
**emit→Go cutover lands** (Lean emits → Go compiles, hand-Go deleted,
`GNARK-LEAN-AUTHORED-PLAN.md:57`). Editing `settlement_circuit.go` directly today is editing
the hand-twin and is **not** proof-guarded. So the cutover is the enabling precondition for
making any of this safe on the deployed circuit — it is called out as a do-first below.

---

## 1. THE MASS MAP (cited)

### 1.1 Per-phase (the drift-canary profile)

`chain/gnark/settlement_profile_test.go` compiles phase-stripped twins and reports the R1CS
delta per phase, pinned to the real circuit's compile (drift canary,
`settlement_profile_test.go:210`). The four phases (`:221-224`):

| phase | what | share |
|---|---|---|
| transcript replay + pins | Fiat–Shamir prefix, claim binding, VK pins | small |
| STARK algebra | constraint-eval at zeta, 6 instances, LogUp balance | ~mid |
| FRI core | commit-phase fold + native Merkle openings | ~mid |
| **open_input** | **input-batch Merkle openings + reduced-opening derivation** | **~80%** |

**The headline number, MEASURED and cited in-source**
(`chain/gnark/stark_open_input.go:47-48`):

> "open_input was **10.35M of the 12.87M total, ~80%**, dominated by the per-query
> per-column Horner"

So **open_input ≈ 10.35M / 12.87M** is where four fifths of the mass lives. The remaining
~2.5M is transcript + STARK-algebra + FRI-core. (README's "~12.2M" `README.md:42` is an
earlier rounded figure; the drift-canary total is 12.87M.)

### 1.2 Deployed shape parameters (what scales the mass)

- **38 FRI queries** (`stark_open_input.go:51`; `docs/reference/PROVEN-120-CONFIG.md:196`,
  `q=38`, `lb=3`, `pow=16`).
- **4 input rounds** per query: trace, quotient, preprocessed, permutation
  (`stark_open_input.go:132`).
- **6 STARK instances**, `degree_bits [9,9,15,14,15]`, `ext_degree 4`
  (`docs/deos/APEX-VERIFIER-AIR-REDUCTION.md:12`). Max input-batch tree depth ≈ 15+`lb`.
- Everything in open_input is inside the **38-query loop** — the mass is
  `queries × (Merkle openings + per-column reduced-opening arithmetic)`.

### 1.3 The two sub-terms of open_input, and the gadget unit costs

**(A) Reduced-opening ARITHMETIC — the dominant sub-term** ("per-query per-column Horner",
`stark_open_input.go:48`). Per query, `deriveOpenInputReducedNative`
(`stark_open_input.go:404`) evaluates, for every committed column of every matrix in all 4
rounds, `S_x = Σ_k α^k·p(x)_k` (base-field opened rows against the alpha ladder,
`:453-459`), then the ext-field combination `alpha_pow·qinv·(S_z − S_x)` per (matrix,point)
(`:479-481`). Unit costs: `ExtMul ≈ 92 R1CS` (measured, `docs/reference/EXT-DEGREE-COST.md:34`);
each S_x column ≈ 4 raw `api.Mul` + amortized `ReduceBounded` (`babybear.go:86`).
**Already-taken lever:** the hoistable half `S_z = Σ α^k·p(z)_k` is transcript-bound and
therefore computed **once** in `NewOpenInputPrecomp` and HOISTED out of the 38-query loop
(`stark_open_input.go:44-57,270-299`) — the source calls this split "THE R1CS lever of the
whole settlement wrap." S_x-across-both-opening-points is also already shared (`:449`), and
the alpha ladder is precomputed (`:259-263`). **The cheap arithmetic wins are already
spent.**

**(B) Merkle-path HASHING.** Per query, per round, `verifyOpenInputBatchNative`
(`stark_open_input.go:334`) walks the input-batch tree: one
`Poseidon2Bn254Compress` per level (`:379`) plus a row-hash per height group
(`multiField32HashNative`, `:367`, multi-block for wide rows — up to 388 base values,
`:31`). **Unit cost: one Poseidon2 permutation = 240 R1CS**, S-boxes only — the linear
layers are constraint-free (`poseidon2_bn254.go:34,83-144`: `(8 full×3 lanes + 56 partial×1
lane)` S-boxes × 3 muls each `= 240`). This is the native-hash swap: the emulated BabyBear
Poseidon2-w16 was **16,837 R1CS/perm** (`merkle_bn254.go:6`,
`docs/deos/WRAP-NATIVE-HASH-DECISION.md:16,52`) — a ~69× reduction already deployed.
Whole-circuit native hashing (open_input Merkle + FRI-core commit paths) ≈ **~2.9M**
(the hashing-vs-fold-residual split is measured by
`chain/gnark/fri_verify_native_test.go:490-498`).

### 1.4 ⚠ Measurement gap the profile does NOT close

`settlement_profile_test.go` reports the **4 phases**, a **per-instance algebra** split
(`:313`), and **marginal gadget costs** (`:396`) — but it does **not** sub-split open_input
into (A) arithmetic vs (B) hashing. The "dominated by per-query per-column Horner"
attribution is an in-source claim (`stark_open_input.go:48`), not a separately-compiled
number. **The relative rank of the hashing optimizations vs the arithmetic optimizations
therefore hinges on a number that is not in the recorded profile.** Closing that gap is the
zero-risk do-first (§3).

---

## 2. RANKED PROOF-GUARDED OPTIMIZATIONS

Refinement-absorb classification (from `EmitVerifier.lean`):

- **LOCAL (proof absorbs):** the emitted gadget's *spec-side Bool is unchanged* (same
  `refRoot` / `foldCheckV` / `batchTablesCheckUnified`). You re-prove **only that leaf's
  `*_refines`** over the new circuit; `emitVerifier_refines`/`_deployed` recompile
  **unchanged** because they cite the leaf theorem **by name** (`EmitVerifier.lean:314-318`)
  and its statement `gHolds (gadgetData …) (asg …) ↔ specBool = true` is stable. The
  composition machinery (`remap_eval_mkM`, `block_ok`, `merged_split`,
  `EmitVerifier.lean:105-230`) is generic over the leaf asserts — it does not care how many
  constraints a leaf emits. **This is the guardrail: an optimized emission that no longer
  computes `specBool` fails the leaf `*_refines` proof → red build.**
- **STRUCTURAL (needs new proof):** the *spec-side changes shape* (e.g. one-path → multi-path
  Merkle). You author a **new leaf refinement theorem** and re-wire the `Inputs`/`sel`/
  `emitVerifier`/`verifyAlgo_mk` block for it (`EmitVerifier.lean:138-182,264-268`). The
  composition still absorbs the block, but the leaf proof is real new work.

Ranked by value / effort:

### #1 — MEASURE open_input's internal split (do-first, §3). LOCAL to the test harness.
Add a Merkle-only vs arithmetic-only sub-phase to `settlement_profile_test.go` (early-return
after `verifyOpenInputBatchNative` vs after `deriveOpenInputReducedNative`). **Saves 0
constraints; unlocks the honest ranking of #2 vs #3.** Effort: hours. Value: it is the
precondition for spending effort on the right half. Not a circuit change → no refinement
impact.

### #2 — Upstream: shrink the apex proof the wrap re-verifies. HIGH value / HIGH effort. OUTSIDE the wrap emit.
The wrap's open_input mass is `queries × opened-columns × depth` **of the apex proof it
verifies**. `docs/deos/APEX-VERIFIER-AIR-REDUCTION.md:131-133` shows re-proving the apex with
**~12 instead of 19 queries** shrinks both the hashing and the reduced-opening chains **~37%**
at the apex; the wrap re-verifies fewer Merkle paths and shorter per-column Horners **linearly**.
Fewer opened columns (narrower apex AIR, `APEX-VERIFIER-AIR-REDUCTION.md:148-153`) cuts the
dominant sub-term (A) directly.
- **Est. savings:** the single largest lever — plausibly **30–40% of the 10.35M** if apex
  queries/columns drop proportionally. This is the only path to the ~5–6M "native-hash STARK
  wrap" reference size (`WRAP-NATIVE-HASH-DECISION.md:40` cites a comparable circom native
  wrap at 5.68M).
- **Emit change:** NONE in the wrap gadgets — it is an **apex re-config** (fewer queries /
  narrower AIR), upstream of `settlement_circuit.go`. The wrap's shape constants
  (`BuildExpectedInputRounds`, `stark_open_input.go:109`) track the new apex shape.
- **Refinement:** `emitVerifier_refines` is **shape-generic** (quantified over
  `I.msibs.length`, the instance list, etc.) so it **absorbs** a smaller shape without a new
  proof — BUT this changes the *proof being verified*, so it rests on the **apex soundness**
  holding at the reduced query count (a soundness argument, not a refinement one). This is
  NOT free and NOT purely constraint-count; flagged as the honest boundary of "safe."

### #3 — Merkle multi-path batching (pruned shared subtree across the 38 queries). MID value / HIGH effort. STRUCTURAL.
Today each of 38 queries recomputes an independent root walk
(`verifyOpenInputBatchNative`, one path per query per round). Queries whose indices agree in
the high bits **share the upper authentication-path nodes**. Hashing the union (pruned)
subtree computes each internal node **once**: for depth `D≈18`, `Q=38` the distinct-node
count ≈ `Q·(D − log₂Q) + 2Q` vs the naive `Q·D` — a **~15–20% cut of the path-compression
sub-term** (the top ~`log₂38 ≈ 5` levels collapse from `Q` walks to ≤`Q` nodes total).
- **Est. savings:** ~15–20% of the Merkle-path compressions. Whether that is a big number
  depends on #1 (how much of the 10.35M is hashing). Row-hashes do **not** batch (each query
  opens different rows), so this only touches the path-compression term.
- **Emit change:** in `MerkleEmit.lean` — replace the single-path `merklePathData`
  (`MerkleEmit` header: per-level `Select`/`Poseidon2Bn254Compress`) with a shared
  pruned-subtree gadget over the 38 index sets.
- **Refinement:** **STRUCTURAL.** The committed `Merkle.merkle_path_refines` is single-path
  (`gHolds (merklePathData |sibs|) (pathAsg …) ↔ refRoot leaf … = mroot`, MerkleEmit header).
  A batched opening needs a **new `merkle_multiopen_refines`** and a re-wired Merkle block in
  `EmitVerifier.lean`. Provable and proof-guardable (the composition cites the new theorem by
  name), but a real proof — not an absorb.

### #4 — BabyBear reduce range-check batching. LOW value / LOW effort. LOCAL (proof absorbs).
`ReduceBounded` (`babybear.go:86`) emits, per reduction, a hinted `(q,r)`, one
`AssertIsEqual(x = q·p + r)`, and range checks on `q` and `r` (`:100-107`). Across a block of
reductions the `r`-canonicity and `q`-bound range proofs can be **batched into one
lookup/commit** (gnark's range-checker already amortizes, `rangecheck.New`, `babybear.go:57`)
rather than per-call. Note candidate **(e) "lookup arguments for range checks" is ALREADY
DEPLOYED** — the deployed reduce uses gnark's commit-based range-checker; `BabyBearFr`/
`FriFoldEmit` name it explicitly ("deployed gnark: lookup argument", `FriFoldEmit.lean`
header). So the only remaining headroom is *sharing the lookup across a block*, not adding
lookups.
- **Est. savings:** low single-digit % of the arithmetic sub-term (the range checks are
  already amortized; this trims the residual per-call overhead).
- **Emit change:** internal to the reduce gadget in `BabyBearFr.lean`.
- **Refinement:** **LOCAL** — the reduce gadget's spec is unchanged (`r = x mod p`), so
  `friFold_leaf_refines` / `batchTable_refines` / the open_input consumers re-prove over the
  new reduce emission and the composition is untouched. Genuinely absorbed.

### #5 — Poseidon2 per-permutation reduction. LOW value / HIGH effort. LOCAL if equivalent, else a security change.
240 R1CS/perm is already near the floor for this instance: `x^5` = 3 muls is optimal
(`x²,x⁴,x⁵`), and the linear layers are constraint-free (`poseidon2_bn254.go:34`). The only
way to move it is **fewer rounds** (`R_F=8`, `R_P=56` are the security parameters), which is a
**security re-derivation**, not a constraint trick — and out of scope (it would touch the
proven bits). A same-cost re-emission buys nothing. **Reject** unless the hash is re-specced
upstream.

### Candidate (d) CSE / DAG dedup — mostly already taken.
Within a query, the shareable values are already shared: `S_z` hoisted, `S_x` shared across
opening points (`stark_open_input.go:449`), the alpha ladder precomputed (`:259`), `xAt`/
`qinvAt` memoized per (height,point) (`:429-433`). Across queries the values are
**query-dependent** (x depends on the sampled index bits; S_x on the opened rows) and cannot
be deduped — the one genuine cross-query CSE is the Merkle pruned subtree, which **is** #3.
Remaining headroom: low.

### Not applicable: config lever (noted, not ranked).
`PROVEN-120-CONFIG.md:71-72` observes that raising the outer `log_blowup` 3→6 takes
`q` 38→36 (a ~5% query-loop shrink) **while raising λ from 70.5 to 122.6**. That is a
**soundness-config** change (it belongs to the proven-120 campaign), not a constraint-only
optimization, and it changes the proof shape — mentioned for completeness, deliberately not
ranked as a wrap optimization.

---

## 3. DO-FIRST + THE HONEST FLOOR

### Do-first (in order)
1. **#1 — profile open_input's internal split.** Zero risk, unblocks the rank of #2 vs #3.
   The current profile stops at "open_input 80%"; you cannot honestly choose between the
   hashing lever (#3) and the arithmetic/upstream levers (#2, #4) without this number.
2. **The emit→Go cutover** (`GNARK-LEAN-AUTHORED-PLAN.md`, DESIGN). Until the full verifier
   is emitted from Lean and replayed through `emitted_interp.go` (today only the canonicity
   toy is), **no** optimization below is proof-guarded on the *deployed* circuit — it is
   guarded only on the Lean object. The cutover is what turns "safe in Lean" into "safe on
   the 12.87M." It is the true enabling do-first.
3. Then, guided by #1: if hashing dominates open_input → **#3** (Merkle batching); if
   arithmetic dominates and it is already at its hoisted floor → **#2** (shrink the apex
   upstream) is the only large lever left.

### The honest floor
- **With queries fixed** (38 is soundness-bound; you cannot drop them without losing bits)
  **and the reduced-opening arithmetic already at its S_z-hoisted floor**, the in-wrap
  constraint tricks (#3 Merkle batching + #4 reduce batching) plausibly shave **~10–20%**:
  **12.87M → ~10.5–11.5M**. That is the ceiling of what the wrap can do to *itself*.
- **The large reductions** (toward the ~5–6M native-hash-wrap reference,
  `WRAP-NATIVE-HASH-DECISION.md:40`) require the **upstream #2 lever**: the wrap's open_input
  mass is fundamentally `apex-queries × apex-opened-columns × depth`. The floor is set by a
  **proof-shape parameter of the apex**, not by any wrap-emit constant — so the deepest cut
  lives in re-proving a leaner apex, which the wrap then inherits linearly.

### What is unaffected (stated plainly)
Every optimization here is **constraint-count only**. The FRI soundness floor
(`project-fri-soundness-reality`; a density reading, not a bound — the proven
deployed columns are `FriDeployedHeightPairing.deployed_wrap_commitBits`
and `DeployedProximitySoundness`, digits in `docs/reference/PROVEN-120-CONFIG.md`) and the single-party Groth16 ceremony
(`README.md:50`) are untouched — no optimization changes the number of proven bits or the
trusted setup. The refinement `emitVerifier_refines` guards *that gnark computes the same
Bool as the spec*, which is exactly the leg optimization could break and now cannot (in
Lean) — it does not, and is not claimed to, add soundness.
