# GNARK-LEAN-AUTHORED-PLAN — replacing the hand-Go outer verifier circuit with a Lean-authored, R1CS-modeled, refinement-proven circuit emitted from the FRI verifier model

**Status:** DESIGN (grounded plan, not a build). Soundness-adjacent.
**Scope:** the OUTER BN254/Groth16 wrap circuit (`chain/gnark/settlement_circuit.go`, ~12.87M R1CS,
test-validated-not-proven). This is the STARK-KILL law #1 ("never hand-author a constraint")
applied to the OUTER verifier — the layer `GOAL-STARK-KILL.md` explicitly fenced off/deleted
rather than solved (it has no `gnark`/`R1CS` mention; grep-confirmed).
**What it closes:** circuit-faithfulness (seam #2 below). **What it does NOT close:** the FRI
extraction floor (#1) and the Groth16 ceremony (#3) — both stated plainly in §3.

---

## 0. The insight, verified against the code

A gnark circuit is not "Go" semantically. `SettlementCircuit.Define` (`chain/gnark/settlement_circuit.go`)
is a **straight-line sequence of `frontend.API` calls** — `api.Add`, `api.Mul`, `api.AssertIsEqual`,
plus gadget calls (`rangecheck.Check`, `Poseidon2Bn254`, hints) that themselves reduce to those. gnark's
compiler (`frontend/cs/r1cs`) lowers that op-DAG to an **R1CS** — a rank-1 constraint system
`A·z ∘ B·z = C·z` — which has an exact mathematical semantics: an assignment `z` satisfies it iff every
row's dot-product identity holds. That semantics Lean can model precisely.

The other half of the insight is already half-built in the tree. The verifier this circuit implements
**already has a Lean model**: `Dregg2.Circuit.FriVerifier.verifyAlgo` / `FriVerifierO.verifyAlgoO`
(`metatheory/Dregg2/Circuit/FriVerifierO.lean:521`) — a computable, straight-line `Bool` verifier whose
body is a six-way conjunction:

```lean
def verifyAlgoO … : PermOC F Bool :=
  obind (deriveTranscriptO RATE toNat params initState logN proof pub) (fun d =>
    .pure
      (vk.shapeMatches proof
        && checks.foldConsistent proof d.betas d.qidx
        && checks.merklePaths proof d.qidx
        && checks.batchTables proof d.betas
        && checks.queryPow proof
        && segmentTooth proof pub))
```

And the refinement **socket already exists**, currently discharged the wrong way. `FriVerifier.lean`
carries (`:1006`–`:1055`):

```lean
abbrev GnarkCircuit (F : Type) := BatchProofData F → WrapPublics F → Bool          -- :1006
def GnarkRefines … (gnark : GnarkCircuit F) : Prop :=                              -- :1012
  ∀ proof pub, gnark proof pub = verifyAlgo perm … proof pub
theorem wrap_sound … (href : GnarkRefines …) (haccept : gnark proof pub = true) :  -- :1037
    ∃ w : GenuineWitness F, w.exists_ ∧ proof.exposedSegment = pub.segment
```

`wrap_sound` is **already proven**: the instant the gnark circuit refines the Lean verifier, it
inherits the verifier's soundness (under the FRI floor). But today `gnark` is an **abstract `Bool`
function** and `GnarkRefines` is an **obligation discharged by fixture/differential testing** against
the hand-authored Go — exactly the "test-validated-not-proven" debt. Line 1008 calls it "the statement
milestone 6 discharges (operation-for-operation, fixture-anchored)."

**This plan replaces that fixture discharge with a structural theorem:** make `gnark` the *denotation of
an R1CS emitted from `verifyAlgo`*, and prove `GnarkRefines` by construction. The emitted R1CS then
*feeds* gnark (Lean emits → Go compiles), so the circuit gnark runs **is** the object Lean proved
faithful — the hand-Go is deleted. This is genuine refinement over a real semantics, not code-gen, and
not the differential-mirror trap (two hand-things agreeing).

---

## 1. The R1CS-semantics model in Lean

### 1.1 What already exists to reuse

`Dregg2.Circuit` (`metatheory/Dregg2/Circuit.lean`) already gives the closest thing to an R1CS model —
its own header says "AIR/R1CS shape, ℤ as field stand-in":

```lean
abbrev Var := Nat                                        -- :55
abbrev Assignment := Var → ℤ                             -- :58   (the witness vector z)
inductive Expr | var | const | add | mul                -- :62   (sums-of-products of wires)
structure Constraint where lhs : Expr; rhs : Expr        -- :77
abbrev ConstraintSystem := List Constraint               -- :87
def satisfied (cs) (a : Assignment) : Prop := ∀ c ∈ cs, c.holds a   -- :90
theorem bridge : satisfied kernelCircuit (encode s t s') ↔ fullStepInv s t s'  -- :226
```

`Dregg2.Exec.CircuitEmit` (`metatheory/Dregg2/Exec/CircuitEmit.lean`) gives the reusable **emit +
faithfulness pattern**: `EmittedExpr` (var/const/add/mul wire form, `:64`), `emit` serializer (`:107`),
`decodeE` inverse (`:124`), `satisfiedEmitted` (`:143`), and

```lean
theorem emit_faithful : satisfied cs a ↔ satisfiedEmitted (emit cs) a     -- via decodeE_emit round trip
```

This is the exact shape we want — an arithmetic constraint system with a `satisfied : CS → Assignment →
Prop` predicate and a *proven* wire-form round trip. **But it is not usable as-is:** (a) it is the DEAD
IR-v1 rail (`CircuitEmit.lean:35` "no deployed path runs it"); (b) it is over `ℤ`, not the BN254 scalar
field; (c) it is degree-unbounded, not rank-1. It is the *skeleton to copy*, not the object to extend.

### 1.2 What is new: model the gnark FRONTEND over `ZMod r`

Model the layer the human actually authors — the `frontend.API` op-DAG — over the **true field** the
soundness lives in, `ZMod r` where `r` = the BN254 scalar modulus (a ℤ stand-in is dishonest here: a
system satisfiable over ℤ need not be over `ZMod r`, and the deployed check is over `Fr`). Sketch (a
type-sketch to validate the socket, not the final grammar):

```lean
abbrev Fr := ZMod 21888242871839275222246405745257275088548364400416034343698204186575808495617

/-- One SSA gate: a fresh wire defined by a frontend op over earlier wires/constants. -/
inductive GOp
  | add (a b : Var) | sub (a b : Var) | mul (a b : Var)
  | constWire (c : Fr)
  | hint (h : HintId) (args : List Var)          -- untrusted advice; MUST be pinned by an assertion
inductive GAssert
  | eq (a b : Var)                               -- api.AssertIsEqual
  | rangeLt (a : Var) (bits : Nat)               -- std/rangecheck.Check (a < 2^bits)
  | poseidon2 (inState outState : List Var)      -- the BN254 permutation gadget (a bound sub-system)
structure GnarkCircuitData where
  numPublic : Nat
  gates     : List (Var × GOp)                   -- wire i := op   (SSA; index = column)
  asserts   : List GAssert
def gEval  : GnarkCircuitData → Assignment Fr → Assignment Fr        -- run the SSA gates
def gHolds : GnarkCircuitData → Assignment Fr → Prop                 -- all asserts hold on gEval
```

`gHolds` is the `satisfied` predicate at the frontend level. Modeling the frontend (not raw R1CS
triples) is the right altitude: it is what `Define` emits, it matches the emit target (§4 lowers the
same op-DAG into `frontend.API`), and the frontend→R1CS flattening is gnark's own compiler
(external-tooling trust, §3). An **optional deepening** models the flattening explicitly — a Tseitin
pass `flatten : GnarkCircuitData → R1CS` introducing one fresh wire per non-rank-1 sub-term, with
`gHolds d z ↔ r1csSat (flatten d) (extend z)` — provable, and it would let us drop the "gnark compiler
trusted" caveat. Recommend deferring it: it is pure additional depth, not on the soundness-inheritance
critical path.

### 1.3 The range-check / hint / lookup subtlety

`rangecheck.Check(v, k)` and hints (`solver.RegisterHint`) are not plain gates — a hint is *untrusted
advice* that is sound only because a later assertion pins it (`chain/gnark/babybear.go:34` "The hint
output is UNTRUSTED; ReduceBounded constrains it"). The model must reflect this: `hint` produces a wire
with **no defining equation**, and soundness of any circuit using it is conditional on the assertions
that pin it. `rangeLt` denotes `(gEval … a).val < 2^bits`; in gnark it is itself a lookup argument, so
its Lean denotation is the *predicate*, and its faithfulness to the lookup gadget is a Stage-A leaf
lemma (`satisfied(rangeGadget k) z ↔ z.val < 2^k`).

---

## 2. The verifier-as-R1CS-emit

### 2.1 Source object and what is reused vs new

**Source:** `verifyAlgoO` (§0) — already the deployed verifier's Lean model, already computable,
already a 6-way AND, already proven faithful to the ℤ/`Bool` deployed form (`verifyAlgoO_run_eq`,
`FriVerifierO.lean:537`). The emitter is a function

```lean
def emitVerifier (params : FriParams) (vk : RecursionVk BabyBear) (checks : FriChecksShape)
    (initState : List BabyBear) (logN : Nat) : GnarkCircuitData
```

that walks the *same* structure `verifyAlgoO` walks and lays down the frontend op-DAG.

**Reused read-only from the FRI-soundness line (codex's / main-line's — do NOT fork):**
- `verifyAlgoO`, `verifyAlgo`, the 6 checks (`foldConsistent`, `merklePaths`, `batchTables`,
  `queryPow`), `segmentTooth`, `deriveTranscriptO` — these ARE the spec; the refinement RHS is literally
  `verifyAlgo … = true`.
- `FriChecks`, `FriCore`, `FieldArith` (`FriVerifier.lean:781`, `:312`) — the abstract op records this
  plan **instantiates** at concrete BabyBear.
- `GnarkCircuit`/`GnarkRefines`/`wrap_sound` (`FriVerifier.lean:1006`+) — the socket this plan
  **discharges**.

The Define body maps onto the six checks 1:1 (`settlement_circuit.go`, phase-verified against
`settlement_profile_test.go`):

| `verifyAlgoO` term            | `SettlementCircuit.Define` phase                                  |
|-------------------------------|------------------------------------------------------------------|
| `deriveTranscriptO` (FS)      | transcript replay loop (`ObserveBabyBearSlice`/`SampleBabyBear`)  |
| `vk.shapeMatches` + canonicity| `AssertIsCanonical` pins + VK pins (`vkPreprocessedRoot`, apex)   |
| `checks.batchTables`          | `VerifyShrinkStarkAlgebra` (`stark_verify_native.go:535`)         |
| `checks.foldConsistent`/`merklePaths` | `VerifyFriNative` (`fri_verify_native.go:275`) + `open_input` |
| `checks.queryPow`             | `PowWitness` grinding check                                       |
| `segmentTooth`                | the 25-lane claim binding (`AssertIsEqual(claim[k], …)`)          |

### 2.2 The three instantiation gaps (from the source model's abstraction)

`verifyAlgoO` is generic over an abstract field `F` with an explicit `FieldArith`/`FriCore` op record
and list-driven loops. Emitting a concrete R1CS closes three gaps:

1. **Concrete field + the BabyBear-in-BN254 emulation gadget.** Deployment is BabyBear (`p =
   2013265921`) with a degree-4 extension, but the gnark witness lives over `Fr`. Each BabyBear element
   is one `Fr` wire holding its canonical residue; multiplication is a **hinted `(q,r)` Euclidean
   reduction** pinned by `x == q·p + r` with `r` range-checked canonical and `q` range-checked small
   (`chain/gnark/babybear.go:1`–`70`, `ReduceBounded`). This gadget is **not modeled in Lean** and must
   be — with a refinement `emulatedMul a b ↔ (a.val * b.val) % p` — and KAT-validated bit-exact against
   `babybear.go`. Plus the degree-4 extension arithmetic (`babybear_ext.go`) over the emulated base.
2. **Static loop unroll.** `queries`, `layers`, `siblings`, `tableOpenings` are `List`-shaped in
   `verifyAlgoO`; R1CS has fixed shape. The emitter unrolls them to the deployed counts
   (`numQueries`, arity, path depth, table count) drawn from `params`/`vk`. Faithfulness: the unrolled
   op-DAG's `gHolds` equals the `List.all`/`foldl` walk at that concrete length.
3. **Boolean lowering.** `decide (a = b)` → `AssertIsEqual`; `&&` → the AND gadget (`c = a·b` on
   {0,1} wires, each pinned boolean). The 6-way AND becomes six assertion clusters that all hold.

### 2.3 The BN254 gadgets: modeled-in-Lean vs gap (honest)

These are the bulk of the new work; none exist in Lean today (grep-confirmed: no BN254 Poseidon2, no
BN254 field model in `metatheory/`):

- **Poseidon2-BN254 permutation** (`poseidon2_bn254.go:111`). BIG LIFT. Needs a concrete Lean
  permutation + KAT bit-exactness, exactly mirroring how `Poseidon2BabyBearW16.lean` pins the BabyBear
  permutation (real round constants, S-box, rounds, validated against deployed Rust). This is the
  cryptographic keystone.
- **MultiFieldChallenger / transcript** (`multifield_challenger.go`, `ObserveBabyBearSlice`,
  `SampleBabyBear`, `splitToFieldOrderLimbs`). `deriveTranscriptO` already models the *algorithm* over
  an abstract `perm`; concretizing binds it to Poseidon2-BN254. `FriVerifier.lean:1019` already names
  this the "silent soundness break" keystone (`TranscriptRefines`).
- **`rangecheck` lookup, Merkle-BN254** (`merkle_bn254.go`) — moderate; standard gadgets, each a
  `satisfied ↔ predicate` leaf lemma.
- **GKR-Poseidon2** (`gkr_poseidon2_bn254.go`) — an *optimization* (batched hashing via a GKR
  sub-protocol) that is **a prototype, not yet wired into `SettlementCircuit`** (production still calls
  the direct `Poseidon2Bn254` gadget, ~240 R1CS/permutation). Recommend the refinement target the
  **non-GKR** Poseidon2 semantics and treat GKR as a provably-equal accelerator (out-of-initial-scope):
  its constraint form differs from plain Poseidon2, so folding it into the first refinement multiplies
  risk. Flag as a labeled deferral. (When wired in, GKR would attack the ~2.9M-R1CS native-hashing mass:
  ~12,008 permutations/proof × 38 queries.)

### 2.4 The precedent that de-risks it

Part of the outer circuit is **already emit-driven, not hand-authored**: the STARK-algebra layer's
constraints are not hand-encoded — they are extracted symbolically from the **inner** AIRs and emitted
as an expression DAG (`fixtures/shrink_symbolic_constraints.json`, Rust-emitted today via
`emit_shrink_symbolic.rs`), then evaluated by ONE generic interpreter
(`chain/gnark/stark_constraint_interp.go`, `SymNode`/`evalSymbolicFoldedNative`, the *only*
constraint-evaluation mode — the hand-mode was removed as a vacuous-check trap). So the pattern "emit a
constraint DAG from the verified side, interpret it generically in gnark" is **live in this exact
circuit**. Two consequences: (a) the `batchTables` check's emit is largely *reuse* — keep the symbolic
interpreter; the CHECK over the DAG is Lean-authored (`BatchTableEmit.batchTable_refines`, ∀ every DAG),
the DAG itself enters as input data. ⚠ CORRECTION (07-19 scout): the shrink DAG does NOT converge to
Lean via STARK-KILL. It is the constraint system of plonky3-recursion's *in-circuit verifier* tables
(`~/dev/plonky3-recursion`, a separate repo, field-generic — "table AIRs depend only on Val/Challenge"),
NOT dregg's effect-vm application AIRs. STARK-KILL Lean-authors the latter; it never touches the former.
So the DAG's *provenance* is a PERMANENT trusted-reference residual (a wrapped third-party recursion
verifier, like the deployed p3 prover), faithfulness discharged empirically by the real-fixture quotient
identity — NOT a gap STARK-KILL closes. (b) this plan generalizes the same "emit + generic interpret"
pattern from the algebra layer to the rest of the *outer* scaffolding (challenger + FRI + Merkle + field
gadgets), which `verifyAlgo` — not the inner AIRs — specifies.

---

## 3. The refinement theorem — precise statement and honest scope

### 3.1 The statement

```lean
/-- The emitted R1CS is satisfiable at a witness encoding (proof, pub, and the honest
    transcript/hash trace) IFF the Lean verifier accepts that (proof, pub). -/
theorem emitVerifier_refines
    (params : FriParams) (vk : RecursionVk BabyBear) (checks : FriChecksShape)
    (initState : List BabyBear) (logN : Nat)
    (proof : BatchProofData BabyBear) (pub : WrapPublics BabyBear) :
    (∃ w : Assignment Fr,
        gHolds (emitVerifier params vk checks initState logN) (encodeWitness proof pub w))
      ↔ verifyAlgo poseidon2Perm RATE toNat params vk checks initState logN proof pub = true
```

The `∃ w` is the standard "advice wires (hints, intermediate hashes) can be filled" — the SOUNDNESS
direction (`→`) is the load-bearing one (a satisfiable R1CS forces acceptance); the completeness
direction (`←`) is discharged by *constructing* the honest witness (mirroring the inner-AIR pattern
`concrete_sat` + `witness_wrong_root_rejected`, `MerkleMembership4aryRefine.lean:234`,`:276`).

**Discharging the existing socket for free.** Define the concrete `gnark`:

```lean
def gnarkDenote params vk checks initState logN : GnarkCircuit BabyBear :=
  fun proof pub => decide (∃ w, gHolds (emitVerifier params vk checks initState logN) (encodeWitness proof pub w))
```

Then `emitVerifier_refines` is exactly `GnarkRefines … gnarkDenote`, and the **already-proven**
`wrap_sound` (`FriVerifier.lean:1037`) fires: a gnark-accepted proof yields a genuine transition whose
segment is the carried publics, under `FriLowDegreeSound`. The abstract-`Bool` obligation becomes a
theorem; the fixture discharge is retired.

### 3.2 What proving it takes

Bottom-up: the field-gadget refinement (§2.2 gap 1), the Poseidon2-BN254 + transcript refinement (§2.3),
each per-check gadget refinement (`gHolds (emit check) ↔ check = true`), the unroll faithfulness (gap 2),
composed by the 6-way AND. Each leaf is a bounded, concrete `Decidable`/`ring`-style proof; the mountain
is their number and the size of the unrolled object (§5).

### 3.3 Honest scope — what it closes and what it does NOT

**CLOSES — circuit-faithfulness (seam #2).** "The R1CS the gnark compiler runs computes exactly the
Lean-specified verifier `verifyAlgo`." Today that is trust in **differential testing** — every gadget has
a plain-Go `*_ref.go` twin (`fri_verify_native_ref.go`, `stark_verify_native_ref.go`,
`babybear_ext_ref.go`, …) driven on shared fixtures for accept/reject + tamper agreement — plus KATs
against the real Rust sponge (`fri_leaf_hash_kat_test.go`, `apex_shrink_real_fixture_test.go`) and one
gated Groth16 e2e. That is validation, not proof, over ~12.87M hand-Go constraints; after, it is
`emitVerifier_refines`, and the hand-Go is deleted (gnark builds from the emitted artifact). The `*_ref.go`
twins do not go away — they become the differential oracle for the lowering check (§4.2).

**DOES NOT CLOSE — the FRI extraction floor (seam #1).** `FriLowDegreeSound` / the `verifyAlgo →
StarkSound` bridge stays a **named terminal crypto carrier** (`FriVerifier.lean:989`,
`FriVerifierBridge.starkSound_of_verifyAlgo`). Per `project-fri-soundness-reality`, the deployed posture
has no adversary/grinding model, so the bit-count is a density reading, not a soundness
bound — the theorem-backed columns are `FriDeployedHeightPairing.deployed_wrap_commitBits`
and `DeployedProximitySoundness` (digits in `docs/reference/PROVEN-120-CONFIG.md`). This plan does not touch it.
A faithful circuit for an unproven-sound verifier is still only as sound as the verifier.

**DOES NOT CLOSE — the ceremony + lowering trust (seam #3).** Groth16 trusted setup, the gnark
frontend→R1CS flattening, and BN254 pairing soundness remain **external-tooling trust**
(`FriVerifier.lean:1050` "the gnark Groth16/pairing soundness (vetted external tooling)"). The deployed
setup is today a single-party DEV/unsafe ceremony (`settlement_snark_test.go`, `groth16_cache.go`);
production needs an MPC — already a named residual (`chain/gnark/README.md:50`). The optional Tseitin
model (§1.2) would retire the flattening half; setup and pairing stay external.

**Two traps to hold the line on.** (a) The Lean model of every BN254 gadget MUST be KAT-validated
bit-exact against the Go gadget — otherwise we prove a *mirror* faithful to itself (the
`describe-at-current-resolution` sin). (b) The emitted artifact MUST feed gnark (delete hand-Go); if
hand-Go is kept and "Lean models it" alongside, that is the differential-mirror trap, not a cutover.

---

## 4. The generic Lean-R1CS → gnark lowering

### 4.1 The emitted format + the Go consumer

Mirror the live inner-AIR rail (`emitVmJson2` → committed JSON → Rust `include_str!` →
`parse_vm_descriptor2`, `descriptor_ir2.rs:1073`) and the live outer symbolic-DAG rail
(`shrink_symbolic_constraints.json` → `stark_constraint_interp.go`):

- **Emit:** `emitGnarkJson : GnarkCircuitData → String`, byte-pinned by `#guard` in the emit file and
  committed at `chain/gnark/emitted/<name>.json`. Node grammar: `{op, args, out}` gates + `{assert}`
  list + public-input map + gadget-invocation records (`rangecheck k`, `poseidon2`, `hint id`).
- **Consume:** ONE generic Go interpreter `BuildFromEmitted(api frontend.API, e Emitted) error` that
  replays each node through `frontend.API` (`api.Add/Mul/Sub/AssertIsEqual`, `rangecheck.Check`,
  `Poseidon2Bn254`, registered hints). This is the trusted lowering — a few hundred lines, and the
  `SymNode` interpreter (`stark_constraint_interp.go`) is the working precedent for exactly this shape.

The interpreter's faithfulness is **per-op-kind** (finite: ~8 kinds), each unit-tested against the
`frontend.API` op it lowers to. It is trusted, not proven — but small and auditable, and (with §1.2's
Tseitin model) provable in principle.

### 4.2 Checking the lowering without proving it

- **Constraint-count parity (drift canary).** Compile the emitted circuit; assert
  `cs.GetNbConstraints()` equals the pinned real count. `settlement_profile_test.go` **already** does
  this per phase (`profPhaseTranscript/Algebra/Fri/Full`, the "DRIFT CANARY" pins the phase-stripped
  twin to the real circuit) — reuse the harness against the emitted circuit.
- **Structural fingerprint.** Hash the emitted op-DAG; pin it (the `#guard` byte-golden discipline).
- **Differential accept/reject.** On the real fixture (`apex_shrink_real_fixture_test.go`,
  `stark_algebra_real_fixture_test.go`) the emitted circuit and the current hand-circuit must
  accept/reject identically — run BOTH during migration, delete hand-Go only when they agree on the KAT
  corpus.
- **Per-op unit tests.** Each interpreter op vs its `frontend.API` semantics on random witnesses.

---

## 5. Tractability + staged plan

Dependency-ordered, each stage a real deliverable (mirroring the FRI 5-stage line). Effort is
small-team calendar time; the FRI-soundness line is the precedent (weeks per stage, and this is
comparable-to-larger because the field/hash emulation gadgets do not exist in Lean yet).

- **Stage A — the frontend/R1CS semantics model** (`GOp`/`GAssert`/`gHolds` over `Fr`, the
  `emit_faithful` round trip, copying `CircuitEmit.lean`'s proven pattern). Deliverable: the type + a
  toy end-to-end refinement (emit a canonicity check, prove `gHolds ↔ v.val < p`) + the emit-JSON
  golden + a 3-node Go interpreter. **~2–4 weeks.** Low risk; pure reuse.
- **Stage B — the BabyBear-in-BN254 field gadget in Lean** (the `(q,r)` reduction + rangecheck model +
  deg-4 extension), refinement to `%p` field ops, KAT vs `babybear.go`/`babybear_ext.go`. Prerequisite
  for all arithmetic. **~3–6 weeks.** Moderate; self-contained but foundational.
- **Stage C — Poseidon2-BN254 + the transcript (THE KEYSTONE).** Concrete Lean permutation + KAT
  bit-exact vs `poseidon2_bn254.go` (mirror `Poseidon2BabyBearW16`), then `MultiFieldChallenger`/
  `deriveTranscriptO` concretized and `TranscriptRefines` proven. **~6–10 weeks.** Highest crypto risk;
  the "silent soundness break" the whole wrap turns on.
- **Stage D — the per-check gadget emits + refinements.** `batchTables` (reuse the already-emitted
  symbolic-DAG interpreter), `foldConsistent`+`merklePaths` (FRI core + Merkle), `queryPow`,
  `segmentTooth`; compose via the 6-AND; the static unroll faithfulness at deployed params. **~2–4
  months.** The bulk of the proof labor.
- **Stage E — the top theorem + cutover.** `emitVerifier_refines`, discharge `GnarkRefines`, wire the
  generic Go interpreter, the constraint-count/differential lowering gates, delete hand-Go. **~1–2
  months.**

**The single hardest piece:** Stage C (Poseidon2-BN254 bit-exactness + the transcript keystone) —
tied with the Stage-D **static unroll + refinement over a ~12.87M-constraint object**. The mass is
concentrated: the `open_input` seam alone is ~10.35M of 12.87M (~80%, `stark_open_input.go:47`), and
native Poseidon2 hashing is ~2.9M — so the unroll/refinement labor lands overwhelmingly on the
FRI-query + open_input + Merkle hashing, not the algebra layer. Proving `gHolds` faithful across that is
real proof-engineering weight, not a leaf lemma. Recommend deferring GKR (§2.3) to shrink risk.

**Honest reachability: MONTHS, not weeks** — a small-team quarter-plus to a first end-to-end
`emitVerifier_refines` at deployed params, and that is under the labeled deferral of GKR and with the
FRI floor (#1) and ceremony (#3) explicitly still open. Stages A–B (weeks) are the cheap, high-value
down payment; they land the semantics model + the field gadget that everything else needs, and are worth
starting independent of the rest.

### Coordination with the FRI verifier model (shared surface — REUSE, don't fork)

`verifyAlgoO` / `FriChecks` / `FriCore` / `FieldArith` / `deriveTranscriptO` / `GnarkCircuit` /
`GnarkRefines` / `wrap_sound` are the FRI-soundness line's objects (codex's / main-line's). This plan
consumes them **read-only** as the spec and discharges `GnarkRefines`; it does not modify them. Do all
emit/lowering work in NEW files — `metatheory/Dregg2/Circuit/Emit/GnarkVerifier*.lean`, a new
`chain/gnark/emitted/` + interpreter — so the soundness lane's files are untouched. The concrete
`FieldArith BabyBear` / `FriCore BabyBear` instances this plan supplies are the natural handoff point:
agree them with the FRI line so both sides instantiate the same records.

---

## Appendix — grounding citations

- Outer circuit: `chain/gnark/settlement_circuit.go` (Define: canonicity → transcript replay → 25-lane
  claim binding → VK pins → `VerifyShrinkStarkAlgebra` → `VerifyFriNative` → `open_input`);
  `fri_verifier.go` (`Publics`, 25 lanes); `stark_verify_native.go:535`; `fri_verify_native.go:275`;
  `multifield_challenger.go`; `poseidon2_bn254.go:111`; `gkr_poseidon2_bn254.go`; `babybear.go:1`
  (BN254 field emulation); `merkle_bn254.go`; `stark_constraint_interp.go` (the live emitted-DAG
  interpreter); `settlement_profile_test.go:1` (~12.87M constraints, phase drift canary).
- Lean verifier model: `metatheory/Dregg2/Circuit/FriVerifierO.lean:521` (`verifyAlgoO`), `:537`
  (`verifyAlgoO_run_eq`); `FriVerifier.lean:781` (`FieldArith`), `:312` (`FriCore`), `:1006`
  (`GnarkCircuit`), `:1012` (`GnarkRefines`), `:1037` (`wrap_sound`), `:989` (`FriLowDegreeSound`),
  `:1019` (`TranscriptRefines`); 5-stage pipeline `FriVerifier{FS,Merkle,Query,Compose,Bridge}.lean`.
- Reusable Lean substrate: `Dregg2/Circuit.lean:55`–`:226` (`Expr`/`Constraint`/`satisfied`/`bridge`);
  `Dregg2/Exec/CircuitEmit.lean:64`–`:175` (`EmittedExpr`/`emit`/`satisfiedEmitted`/`emit_faithful`);
  inner-AIR emit rail `DescriptorIR2.lean:1497` (`emitVmJson2`), `Emit/Poseidon2HashEmit.lean`,
  `Emit/MerkleMembership4aryRefine.lean:185` (refine-theorem shape), `Poseidon2BabyBearW16.lean` (the
  KAT-validated concrete-permutation precedent).
- Alignment: `GOAL-STARK-KILL.md:7` (law #1, inner engine; no `gnark`/`R1CS` mention — this is the outer
  application). Floor honesty: `project-fri-soundness-reality`.
