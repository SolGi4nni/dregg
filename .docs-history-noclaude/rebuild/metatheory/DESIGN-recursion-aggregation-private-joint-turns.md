# DESIGN — Recursion / Aggregation for Private Joint Turns

*Status: research + design. Read-only survey; no code changed. Grounded in code actually
read in `~/dev/proof-systems`, `~/dev/plonky3-recursion`, and `Dregg2/{Circuit,Privacy,
PrivacyKernel,CryptoKernel,Exec}`. Author: subagent for ember, 2026-06-06.*

This doc answers four questions: (1) honest comparison of **pickles-native recursion vs
plonky3-recursion vs bespoke** for our setting; (2) how aggregation maps **Silver (bundle
proof trees) → Gold (recursive/succinct)**; (3) a concrete circuit/recursion design for
**private joint turns** (inter-vat and intra-vat); (4) the **formal-verification hooks** —
the circuit⟺protocol soundness obligations recursion *adds* on top of what we already prove.

---

## 0. What we already have (ground truth, read this first)

The joint-turn machinery is real and proven at the **single-step, single-pair** level. The
crown-jewel triangle for a bilateral turn is already built:

- **Spec** (`Dregg2/Circuit/CoordinatedTurnRefinement.lean:42`):
  `BilateralTurnSpec kA kB step kA' kB'` ≜ `step.covenant.φ (view kA)(view kB)` ∧
  `jointApplyRec kA kB step.bt = some (kA', kB')` ∧ `step.bind.sidOfA = step.bind.sidOfB`.
  i.e. **covenant holds on the joint pre-state** ∧ **atomic bilateral state-transition** ∧
  **shared-binding consistency** (CG-2).
- **Circuit** (`Dregg2/Circuit/CoordinatedTurnEmit.lean`): a 21-wire,
  11-constraint `ConstraintSystem` (`coordinatedTurnCircuit`, line 307) with:
  4 public-input EQ gates (`rootA`/`rootB`/`charterHash`/`bindingHash`), per-leg
  rest/frame/moved digest EQ gates (the `StateCommit` pattern), and a covenant-φ guard bit.
  Serialized via `CircuitEmit.emit` to `emittedCoordinatedTurn` (`coordinatedTurnAirName =
  "dregg-coordinated-turn-v1"`).
- **Soundness** `coordinated_emitted_refines_spec` (`CoordinatedTurnEmit.lean:511`):
  emitted polynomial satisfaction on the honest encoder + half-edge commits + WF + covenant
  guard ⇒ `BilateralTurnSpec`. **Completeness** `coordinated_circuit_complete_of_digests`
  (line 449). Both `#assert_axioms`-clean.
- **Privacy tiers** (`Dregg2/Privacy.lean`, `Dregg2/PrivacyKernel.lean`): field
  (selective disclosure), value (Pedersen `committed_conservation_kernel` via `commit_hom`),
  graph (stealth/`ZkAuthChain`/`BlindedSet` + `GraphPrivacyKernel` k-anonymity), nullifier
  (`nullifier_no_double_spend`). All routed through `CryptoKernel` (`commit`/`hash`/`verify`/
  `nullifier` + `commit_hom` law; `Digest : AddCommGroup`).
- **Charter** (`Dregg2/Exec/CrossVatCharter.lean`): `covenant ∧ biscuitA ∧ biscuitB ∧
  bilateral commit`; macaroons rejected (`charter_macaroon_rejected`),
  `charter_discharge_sound`.

**The honest gaps relevant here** (already flagged in code):
- `hole_coordinated_covenant_guard` (`CoordinatedTurnEmit.lean:619`, open): the
  covenant φ is enforced by a **single `propBit` column**, not a full polynomial encoding.
- `coordinated_emitted_refines_execCoordinatedForestG` (line 627, open): the
  `RecordKernelState` lift to the *forest executor* is a Wave-6 front.
- The circuit is **one bilateral pair, one step**. There is **no aggregation, no
  recursion, and no privacy in the circuit yet** — `encodeCoordinatedTurn` exposes pre/post
  digests in the clear; the privacy tiers (`Privacy.lean`) are a *separate* algebraic layer
  not yet welded into `coordinatedTurnCircuit`. **Welding privacy INTO the joint-turn circuit
  and then making the joint turn RECURSIVE is exactly what this doc designs.**

---

## 1. Engine comparison — pickles vs plonky3-recursion vs bespoke

### 1a. What is actually in the two checkouts

**`~/dev/proof-systems` (Mina / o1-labs, v0.7.0, last commit 2026-04-15).** This is the
**Rust** proof-systems repo. Critically: **pickles itself is NOT here as runnable Rust** —
`find -iname '*pickles*'` returns only `book/docs/specs/pickles.md` (the spec) and
`o1vm/src/pickles/` (the o1vm zkVM's prover, *named* pickles-style but a STARK prover for the
MIPS VM, not the inductive composition layer). The real pickles (Step/Wrap over Pasta, the
`Prove_tock(Verify(Tick))` tick-tock recursion in `pickles.md`) lives in the **OCaml**
`mina` tree, not here. What *is* here as a working recursion/IVC engine in Rust:
- **`arrabbiata/`** — a **Nova-style folding / IVC** scheme over Pasta (Vesta/Pallas,
  "tick/tock"-amicable curves). `src/interpreter.rs` implements the augmented circuit
  (EC add/scalarmul gadgets, Poseidon sponge, folding via homogenized constraints +
  cross-terms through `mvpoly::compute_cross_terms`, message-passing/curve-cycling). The
  `decider/` is the final SNARK on the accumulator. **But**: the source is candid that it is
  WIP — 69 `FIXME/TODO/sketch` markers, and `lib.rs` literally says of the public-IO hash
  *"However, it doesn't make the protocol sound. We must absorb, in addition to that the
  index, the application inputs/outputs… left for the future as at this time, we're still
  sketching the verifier circuit."* **`VERIFIER_CIRCUIT_SIZE` is explicitly being grown
  "step by step."** This is a research-grade folding engine, not production-ready.
- **`kimchi/`** — the production PLONK-ish prover (the thing pickles wraps). Mature, but
  recursion = pickles = OCaml = not in this repo.

**`~/dev/plonky3-recursion` (Plonky3 org, last commit 2026-05-21).** A **56k-LOC, complete,
self-contained recursive STARK verifier in Rust.** `README.md` is honest: *"under active
development and hasn't been audited yet."* But the **code structure is complete and the API
is real**, which is what memory says to judge on (try the code, ignore the readme):
- `recursion/src/recursion.rs` — **unified `prove_next_layer` API**: `RecursionInput::{
  UniStark, BatchStark}` → `RecursionOutput(BatchStarkProof, CircuitProverData)`, chainable
  via `into_recursion_input::<BatchOnly>()`. A genuine recursion *loop*.
- **2-to-1 recursive aggregation**: `build_aggregation_layer_circuit(&input_1, &input_2,…)`
  + `prove_aggregation_layer(…)` (README "Recursive aggregation"), verifying **two possibly
  different child circuits** (uni-stark left, batch-stark right) in one parent. This is the
  **proof-tree node** primitive we need for Silver→Gold.
- `recursion/src/verifier/batch_stark.rs` — the FRI-based STARK verifier **written as a
  circuit** (`CircuitTablesAir`, `verify_p3_batch_proof_circuit`), provable in the next layer.
- `circuit/` — a `CircuitBuilder` with primitive ops (add/mul) + non-primitive ops (Poseidon2
  perm, MMCS/Merkle). **ZK supported** (README "Full support for Zero-Knowledge").
- Single field tower (KoalaBear/BabyBear/Goldilocks + degree-D extension), **no curve-cycle**
  — recursion is same-field STARK-in-STARK, much simpler to reason about than pickles' Pasta
  tick-tock or Nova's two-curve message passing.

### 1b. Honest verdict for OUR setting

Our setting is: **a tree of joint turns** (forests of `CoordinatedTurnStep`s, plus unilateral
turns), each step already having a proven `circuit ⟺ BilateralTurnSpec` bridge, that we want
to (a) make **private** (MASP-grade), and (b) **aggregate into one succinct proof** for a
block / bundle. We are STARK-shaped already: `coordinatedTurnCircuit` is an AIR-style
constraint system emitted to `EmittedDescriptor`, and the existing circuit stack
(per memory) is "STARK+Plonky3+Kimchi all connected."

| Criterion | pickles (OCaml, native) | plonky3-recursion | bespoke |
|---|---|---|---|
| **In a checkout we can run?** | ❌ OCaml only (Rust has docs+o1vm only) | ✅ 56k LOC Rust, builds | n/a |
| **Maturity** | production (Mina mainnet) but not here | unaudited, complete structure | nothing |
| **Matches our STARK/AIR shape** | ⚠️ PLONK/kimchi gates, Pasta cycle | ✅ STARK/AIR, FRI, same field | ✅ but we'd rebuild FRI-in-circuit |
| **Recursion model** | Pasta tick-tock (2 curves) | same-field STARK-in-STARK | ? |
| **Aggregation primitive** | Tick verifies 2 Tock (`pickles.md`) | 2-to-1 `prove_aggregation_layer` ✅ | hand-rolled |
| **ZK / privacy support** | ✅ mature | ✅ (README; needs verification) | bespoke |
| **Formal-verification surface** | huge (whole pickles), opaque to us | **one fixed verifier circuit** to model | unbounded |
| **MASP-grade privacy pull-in** | Mina-flavored, OCaml | Plonky3 ecosystem (memory: pull a component) | DON'T (Orchard forgery bug) |

**Recommendation (RANKED):**

1. **PRIMARY: plonky3-recursion as the recursion/aggregation engine.** It is the only one we
   can actually run and read end-to-end, it matches our STARK/AIR shape, its
   `prove_next_layer` + `prove_aggregation_layer` are exactly the **proof-tree node** and
   **chain** primitives Silver→Gold needs, and — decisively for the crown jewel — its
   recursion is a **single fixed verifier circuit** (`verify_p3_batch_proof_circuit`), which
   means the circuit⟺protocol obligation recursion adds is **bounded**: we model ONE verifier
   AIR, once, and prove it sound; everything else is the SAME `BilateralTurnSpec` triangle we
   already have. Pickles' or Nova's recursion would force us to model a curve-cycle / folding
   accumulator, a much larger and (for arrabbiata) **admittedly-unsound-today** surface.

2. **SECONDARY / watch: arrabbiata (folding/IVC) for the *streaming consensus* axis only.**
   Folding shines when you have a *long linear chain* of identical steps (a blockchain of
   blocks). Our **block-internal** structure is a *tree of heterogeneous turns* → aggregation
   (plonky3), not folding, is the right primitive. But the **block-over-block** chain (one
   block's proof folds into the next) is genuinely IVC-shaped, and arrabbiata is the
   in-house Pasta folding engine. **Do not adopt it now** (it says it's unsound today); keep
   it as the candidate for the *outer* chain once it matures, OR use plonky3 recursion for the
   outer chain too (one engine is better than two).

3. **REJECT: bespoke recursion.** Memory is explicit (Orchard value-forgery bug → formal
   verification vital; MASP-grade privacy = PULL IN a component, not bespoke). Rolling our own
   FRI-verifier-in-circuit is exactly the unbounded-soundness-surface trap.

**OPEN DECISION (ember):** *one engine or two?* Plonky3-recursion for both intra-block
aggregation AND inter-block chaining (simpler, one verifier to formally model) vs.
plonky3 for the tree + arrabbiata folding for the chain (matches IVC theory, but two unaudited
engines and a curve-cycle to model). **My lean: one engine (plonky3) until the formal model
of its verifier AIR is solid, then revisit folding for the chain as a perf optimization.**

---

## 2. Aggregation: Silver (bundle proof trees) → Gold (recursive/succinct)

Memory: *"Silver Vision = bundle proof TREES → Gold = fully recursive/succinct."* Here is the
concrete mapping onto the engine and our Lean spec.

### 2a. Silver — the proof tree (bundle, NOT yet succinct)

A **bundle** is a block's worth of turns. The leaves are per-turn proofs:
- a **unilateral** turn leaf = the existing single-cell turn circuit (`TurnEmit`/`StateCommit`),
- a **joint** turn leaf = `emittedCoordinatedTurn` proving `BilateralTurnSpec` for that pair.

Silver = **a tree whose internal nodes are 2-to-1 aggregation proofs**
(`prove_aggregation_layer`), each node verifying its two children's STARK proofs *as a
circuit* and re-exporting a digest of their joint public inputs. The bundle proof is the
**root** of this tree. At Silver, the root is still a (large) batch-STARK proof — you have
"bundled" N turns into log-depth recursion, but the verifier still does work proportional to
the tree shape. This is exactly memory's *"pre-algebraic integration-complete"* Silver: every
turn's proof is composed into one tree, no turn left unproven, but not yet a O(1) succinct
object.

**Lean shape of Silver.** We already have `TurnCircuitCompose.lean`. The aggregation node's
spec obligation is a **conjunction-preservation** law: if child-left proves `Spec_L` and
child-right proves `Spec_R`, the aggregation node proves `Spec_L ∧ Spec_R` (modulo the
public-input binding — see §4). For joint turns the leaf `Spec` is `BilateralTurnSpec`; for a
bundle of joint turns the root proves `⋀ᵢ BilateralTurnSpec(stepᵢ)` **plus** the cross-turn
gluing (turn i's post-root = turn i+1's pre-root — the chainlink, our `RecChainedState`).

### 2b. Gold — recursive / succinct

Gold = **fold the tree to a constant-size object** + **make it self-verifying**:
- **Succinctness**: wrap the Silver root in one more recursion layer
  (`prove_next_layer` on the root) until the proof is O(1) and the verifier circuit is fixed.
  In plonky3-recursion this is just "keep calling `prove_next_layer` until the layer is the
  fixed-point shrink layer." (Memory's *"folded DAG / fully algebraic constraint."*)
- **Recursive / inductive**: the Gold block proof embeds **verification of the previous
  block's Gold proof** (IVC over blocks). This is the genuine IVC step — and the one place
  folding (arrabbiata) *could* beat aggregation, because block-over-block is a linear chain.

**The Silver→Gold gradient is a depth/perf gradient, not a soundness gradient.** Each
aggregation layer adds the SAME `verify_p3_batch_proof_circuit` soundness obligation (§4); the
spec it carries is unchanged. So **we can ship Silver first** (bundle trees, verifier does
log-work) and tighten to Gold (one shrink wrap + inter-block IVC) as a pure perf/optimization
follow-up — *without re-opening the circuit⟺protocol soundness story*. This matches the
"aggregation = deferred perf" note in `project-dregg2-coverage-map`.

---

## 3. Private joint turns — the concrete circuit/recursion design

A **private joint turn**: two-plus vats coordinate a turn; each keeps its own state private;
the joint transition is proven without either vat revealing its private state to the other or
to the public. Today `encodeCoordinatedTurn` puts pre/post **digests** on public wires
(`vPubRootA`, `vRestDigPreA`, …) — those are already *commitments*, so the skeleton is
privacy-friendly, but the witness columns carry cleartext `RecordKernelState` values and the
covenant φ reads both *cleartext* kernel views (`recChainedKernelView`). We make it private by
(i) replacing cleartext state with MASP-grade commitments, (ii) splitting the joint proof into
**per-vat sub-proofs** that each prove only their own leg over their own private state, and
(iii) recursively **gluing** the legs through a public shared-binding commitment — so neither
leg's circuit ever sees the other's private witness.

### 3a. Inter-vat (cross-vat) private joint turn — the two-leaf-one-glue pattern

This is the headline. Structure as a **3-node recursion sub-tree per joint turn**:

```
                    [ GLUE node ]  (public: charterHash, bindingHash, rootA, rootB, nullifiers)
                    /            \
        [ LEG-A proof ]        [ LEG-B proof ]
   private: vat-A full state    private: vat-B full state
   proves: applyRecHalfOut      proves: applyRecHalfIn
           + value commit        + value commit
           + nullifier(s)        + note commit(s)
```

- **LEG-A circuit** (vat A's prover, sees only A's secrets): proves
  `applyRecHalfOut sA.kernel step.bt = some sA'` (the debit leg) over A's **private**
  `RecordKernelState`, exposes ONLY: `rootA` (pre-state commitment), `rootA'` (post),
  `outValueCommitment` (Pedersen `commit amt rₐ`), and the **half of the shared binding**
  `bindH` it controls. A's amounts and accounts are *witness-only*; the value tier
  (`PrivacyKernel.committed_conservation_kernel`) carries conservation on the commitment.
- **LEG-B circuit** (vat B's prover, sees only B's secrets): symmetric, proves
  `applyRecHalfIn` (the credit leg), exposes `rootB`, `rootB'`, `inValueCommitment`, its half
  of the binding.
- **GLUE node** = `prove_aggregation_layer(LEG-A, LEG-B)`: a recursion circuit that
  (1) **verifies both leg STARK proofs** (`verify_p3_batch_proof_circuit` ×2 — this is where
  plonky3-recursion does the work), (2) checks the **public binding agreement**
  `step.bind.sidOfA = step.bind.sidOfB` (CG-2, already in `BilateralTurnSpec`) by EQ-gate on
  the two legs' exported binding wires, (3) checks **committed conservation across the legs**:
  `outValueCommitment = inValueCommitment` (Pedersen homomorphism — `commit_hom` — so the
  amounts balance *without either leg revealing the amount*; this is `committed_conservation_
  kernel` lifted into the glue circuit), (4) checks the **covenant φ** on the *committed*
  joint view, and (5) exports the public `charterHash`, the four roots, and the **nullifier(s)**
  of any spent notes (for double-spend gating — `nullifier_no_double_spend`).

**What each party proves vs. what stays private:**

| | Leg-A prover sees | Leg-B prover sees | Public / glue sees |
|---|---|---|---|
| A's accounts & amounts | ✅ (witness) | ❌ | ❌ (only `rootA`, `commit amt rₐ`) |
| B's accounts & amounts | ❌ | ✅ (witness) | ❌ (only `rootB`, `commit amt r_b`) |
| transfer amount | ✅ | ✅ (it's shared) OR commitment-only | ❌ (only the commitment + balance) |
| shared binding `sid` | ✅ (its half) | ✅ (its half) | ✅ (the agreement EQ) |
| covenant φ truth | — | — | ✅ (one guard bit; φ over *commitments*) |
| nullifiers of spent notes | ✅ | — | ✅ (for the spent-set gate) |

The crucial privacy win of the **two-leaf split**: vat A's circuit witness *never contains*
vat B's state, and vice versa — so even the *prover* of one leg learns nothing of the other's
private state. The legs meet ONLY at the glue node, and only through **public commitments**
(`bindH`, value commitments, roots). This is strictly stronger than today's
`encodeCoordinatedTurn`, where a single prover holds *both* `sA` and `sB` cleartext.

**Where MASP-grade privacy components plug in (memory: PULL IN, don't bespoke):**
- **Value tier**: the `outValueCommitment`/`inValueCommitment` are Pedersen commitments from
  `CryptoKernel.commit` — the MASP/Sapling **value-commitment** primitive. The glue's balance
  check is `committed_conservation_kernel`. Pull the *circuit* for Pedersen value commitments
  + range proofs from the Plonky3/Sapling ecosystem (NOT bespoke — Orchard's forgery bug was
  a missing value-balance/range check; the range proof is non-optional).
- **Note/nullifier tier**: spent notes use the MASP **note commitment + nullifier** scheme
  (`CryptoKernel.nullifier`, `Privacy.Note`/`Nullifier`). The leg circuit proves
  `note ∈ commitmentTree` (a `BlindedSet`/Merkle membership — `Crypto/Merkle.lean`,
  `BlindedMembershipKernel`) and exports `nullifier(note)`; the glue gates against the spent
  set. **Pull the Merkle-membership + nullifier-derivation circuit from MASP/Sapling.**
- **Graph tier**: recipient addresses on the credit leg use **stealth addresses**
  (`Privacy.StealthAddr`, `GraphPrivacyKernel.unlinkable`) so the public transcript doesn't
  link two payments to the same vat. Pull EIP-5564/Sapling stealth derivation.
- **Field tier**: which *fields* of a record are public is the `FieldVisibility` mask
  (`Privacy.project`, `field_projection_hides_private`) — already cleanly ours, just needs to
  drive *which* witness columns are exposed in the leg circuits.

### 3b. Intra-vat private coordination

Intra-vat = one vat, multiple cells/compartments coordinating a turn, hiding *which cells*
participate and *their amounts* from other compartments and from the public, while still
proving the whole turn legal. This is **simpler** than inter-vat (one prover, one trust root,
no cross-prover privacy) but wants the **same value/note/graph tiers** plus:
- a **forest aggregation** (`execCoordinatedForestG`, the Wave-6 lift) where each cell's
  sub-turn is a leaf proof and the vat's turn is the aggregation root — the **Silver tree
  scoped to one vat**. Privacy: the **graph tier** hides which cells moved (the set of touched
  cells is committed, not revealed), and the **field tier** hides amounts.
- Here the legs CAN share a prover (same vat), so the two-leaf split is optional; you'd use it
  only to hide compartment-A's state from compartment-B's *operator* (a confidentiality
  boundary *within* a vat — the dregg4 "single-machine principle" relaxed to compartments).

### 3c. How recursion ties it together (the full picture)

```
              [ BLOCK Gold proof ]  ← (Gold: + verifies prev block, IVC)
                       |  prove_next_layer ×k  (shrink to O(1))
              [ Silver bundle root ]
                  /    |    \      ← 2-to-1 aggregation tree (prove_aggregation_layer)
                ...   ...   ...
                /        \
      [ joint-turn GLUE ]   [ unilateral turn leaf ]
        /        \
  [LEG-A]      [LEG-B]      ← private per-vat leaves (§3a)
```

Each `[…]` is a STARK proof; each parent **verifies its children as a circuit**. Privacy lives
at the **leaves** (MASP commitments in the leg circuits); recursion just **carries commitments
up** — a parent never re-opens a child's private witness, it only checks the child's *proof*
and re-exposes the child's *public commitments*. So **privacy and recursion compose cleanly**:
recursion is privacy-preserving *by construction* because the verifier-in-circuit only ever
touches public inputs + the proof, never the private witness (this is the same reason
`field_projection_hides_private` holds — the parent's view is a function of public data only).

---

## 4. Formal-verification hooks — what soundness obligations recursion ADDS

The crown jewel (memory) is **circuit⟺protocol soundness+completeness**. We have it for one
joint turn (`coordinated_emitted_refines_spec`). Recursion adds **exactly three** new
obligations on top — and the design above is chosen to keep each one **bounded and reusable**.

### H1 — Verifier-circuit soundness (the ONE big new obligation)

`prove_aggregation_layer` / `prove_next_layer` work by running
`verify_p3_batch_proof_circuit` *as a circuit*. The new soundness obligation is:

> **`recursive_verifier_sound`**: if the verifier-circuit (as a `ConstraintSystem`, emitted
> the same way `coordinatedTurnCircuit` is) is satisfied on an honest encoding of a child
> proof + child public inputs, then the child STARK proof actually verifies (the in-circuit
> FRI/STARK check ⟺ the native `p3` verifier's accept).

This is the **soundness of the recursion engine itself**, lifted to Lean. It is ONE theorem
about ONE fixed circuit (plonky3's verifier AIR), proved ONCE, reused at every node. **This is
the load-bearing new work** and the single biggest reason to prefer plonky3-recursion (fixed
verifier circuit) over pickles/Nova (curve-cycle / folding accumulator = a *much* larger
verifier to model, and arrabbiata's is admittedly unsound today). *Pragmatic stance*: H1 is
the boundary where we **trust the engine's audit + a differential/property-test** (the
`CryptoKernel.verify` §8 portal pattern) rather than fully re-proving FRI soundness in Lean —
but we must at least model the **public-input binding** part of it in Lean (H2), which is where
the real composition bugs hide.

### H2 — Public-input binding / no-mixing (the obligation that catches REAL bugs)

The aggregation node verifies two child proofs and re-exposes a digest of their public inputs.
The soundness obligation is that the parent's exported public inputs are **bound to** the
children it verified — you cannot verify proof-of-step-7 but export step-3's roots, and you
cannot **swap a leg** (verify leg-A of turn i against leg-B of turn j).

> **`aggregation_binds_children`**: `satisfied (aggregationCircuit) enc` ⇒
> `childRootA = exported.rootA ∧ childRootB = exported.rootB ∧
>  chainlink(child_i.post = child_{i+1}.pre) ∧ binding.sidOfA = binding.sidOfB`.

This is **exactly the `cCTPubRootA…cCTPubBinding` EQ-gate pattern we already have**
(`CoordinatedTurnEmit.lean:281-287`), lifted one level: the parent's public-EQ gates bind the
*children's exported roots* to the parent's wires. **This is provable in Lean today, with the
existing `StateCommit`/`encCT` machinery** — and it is where the memory's *"⚑ Conservation ≠
Full Semantic Correctness"* lesson bites hardest: an aggregation that checks conservation but
NOT the per-child root binding can be tricked into composing proofs of *different* states.
**H2 is the anti-ghost tooth for recursion** and should be the FIRST thing built (it needs no
trust in the engine internals, just the EQ-gate discipline we already prove).

### H3 — Privacy-in-circuit obligations (lifting `Privacy.lean` from algebra into the AIR)

Today `Privacy.lean`/`PrivacyKernel.lean` prove the privacy tiers **algebraically**, separate
from `coordinatedTurnCircuit`. The leg circuits in §3a must **weld** them in:

> **`leg_circuit_refines_private_spec`**: `satisfied (legACircuit) enc` ⇒
> `applyRecHalfOut sA … = some sA'` (state-transition, as now) **∧**
> `outValueCommitment = CryptoKernel.commit amt rₐ` (value tier) **∧**
> `nullifier-of-spent-note exported ∧ note ∈ commitmentTree` (note/membership tier) **∧**
> the witness is independent of the OTHER leg's private state (the privacy guarantee — a
> `field_projection_hides_private`-style independence lemma on the leg's public projection).

The new obligations vs. today: (a) the value-commitment gate must be a **real polynomial
identity** matching `commit_hom` (not the current single-bit φ-guard scaffold — this is the
same upgrade `hole_coordinated_covenant_guard` needs); (b) a **range proof** on the committed
amount (the Orchard-forgery lesson — non-optional); (c) a **membership** gate
(`Crypto/Merkle.lean` + `BlindedMembershipKernel`) for notes; (d) an **independence** lemma
that the leg's public outputs are a function of public inputs only (privacy = the recursion-
level analog of `field_projection_hides_private`).

### H4 — Completeness up the tree (don't lose honest provers)

Mirror of H2/H3: every honestly-executed joint turn forest must produce a satisfying
aggregation witness — `coordinated_circuit_complete_of_digests` lifted to the tree. Memory's
*"all protocol-acceptable behaviors are circuit-acceptable."* Provable by induction on the
tree using the per-node `…complete_of_digests` lemmas; structurally the easy direction, but
**required** for the crown jewel's completeness half.

### Build order (leverage-ranked)

1. **H2 first** — `aggregation_binds_children` EQ-gates. Pure reuse of `encCT`/`StateCommit`,
   no engine trust, catches the real composition/ghost bugs. *This is the recursion analog of
   the transfer triangle and should be the validated reference before any swarm.*
2. **H3** — weld `committed_conservation_kernel` + range + membership into the **leg** circuit
   (this also discharges `hole_coordinated_covenant_guard` by giving φ a real polynomial form
   over commitments). Resolve the `coordinated_emitted_refines_execCoordinatedForestG` lift
   along the way.
3. **H4** — completeness up the tree (induction over the existing per-node lemmas).
4. **H1** — model the plonky3 verifier AIR's public-input-binding fragment in Lean; treat the
   FRI-soundness core as a `CryptoKernel.verify`-style §8 portal backed by the engine's audit
   + differential tests. **Decide here (ember): how much of FRI to re-prove vs. trust.**

---

## 5. Open decisions for ember

1. **One engine or two?** plonky3-recursion for *both* intra-block aggregation and inter-block
   IVC (one fixed verifier to formally model), vs. plonky3 for the tree + arrabbiata folding
   for the block chain (matches IVC theory, but two unaudited engines + a curve-cycle to
   model). *My lean: one engine until H1 is solid.*
2. **H1 trust boundary**: re-prove the plonky3 FRI verifier sound in Lean (huge, but full
   crown jewel) vs. trust the engine's audit + model only the public-input-binding fragment
   (H2) + differential-test the rest (the §8 portal pattern). *My lean: portal + H2, revisit.*
3. **Two-leaf split vs. single-prover joint turn**: the §3a two-leaf design gives
   prover-vs-prover privacy (vat A's prover never sees vat B's state) at the cost of a 3-node
   sub-tree per joint turn. Do we need prover-vs-prover privacy (true cross-org), or is
   single-prover-hides-from-public enough for the first cut? *My lean: build single-prover
   private first (it reuses today's `encodeCoordinatedTurn` + privacy tiers directly), add the
   two-leaf split when cross-org confidentiality is a real requirement.*
4. **MASP component sourcing**: which concrete circuits to pull for value-commitment+range,
   note+nullifier, stealth — from the Plonky3 ecosystem vs. porting Sapling/MASP. (Memory:
   PULL IN, never bespoke; range proof non-optional.)
5. **Covenant φ in-circuit**: `hole_coordinated_covenant_guard` (single propBit today) must
   become a real polynomial φ over *committed* state for private joint turns. Scope of φ's
   expressible language is a design choice (what predicates can a private covenant assert over
   two hidden states?).

---

## Appendix — exact code references

- Joint-turn circuit + soundness: `Dregg2/Circuit/CoordinatedTurnEmit.lean`
  (`coordinatedTurnCircuit:307`, `coordinated_emitted_refines_spec:511`,
  holes `:619`,`:627`).
- Joint-turn spec: `Dregg2/Circuit/CoordinatedTurnRefinement.lean:42` (`BilateralTurnSpec`).
- Charter: `Dregg2/Exec/CrossVatCharter.lean` (`Charter`, `charter_discharge_sound`).
- Privacy tiers: `Dregg2/Privacy.lean` (field/value/graph/nullifier),
  `Dregg2/PrivacyKernel.lean` (`committed_conservation_kernel:98`,
  `nullifier_no_double_spend:137`).
- Crypto portal: `Dregg2/CryptoKernel.lean` (`CryptoKernel` class, `commit_hom`).
- plonky3-recursion: `~/dev/plonky3-recursion/recursion/src/recursion.rs`
  (`prove_next_layer`, `RecursionInput`, `RecursionOutput`), `recursion/src/verifier/
  batch_stark.rs` (`verify_p3_batch_proof_circuit`), `README.md` (aggregation API). 56k LOC,
  ZK-supporting, unaudited, complete structure.
- arrabbiata (Nova folding/IVC): `~/dev/proof-systems/arrabbiata/src/interpreter.rs`
  (folding §296, message-passing §327), `src/lib.rs` (WIP soundness caveats). 69 FIXME/sketch.
- pickles (spec only in Rust repo): `~/dev/proof-systems/book/docs/specs/pickles.md`
  (Step/Wrap tick-tock over Pasta); the engine is OCaml in the `mina` tree, not here.
