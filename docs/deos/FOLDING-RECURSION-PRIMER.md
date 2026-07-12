# Folding recursion — a primer, and what it means for dregg

*2026-07-12. Written to educate the architecture decision, not to propose a migration.
The honest headline: folding is the prover-speed frontier for IVC, but for dregg it
collides with TWO things dregg deliberately chose — post-quantum safety and the small
(BabyBear) field. So folding is the architecture to **watch and evaluate as PQ-folding
matures**, not a now-move. Meanwhile the hash-based wrap we just proved end-to-end
(native-hash + blowup-rebalance + GPU) is the PQ-preserving path.*

## 1. The problem folding solves: recursion is expensive

dregg does **IVC** (incrementally verifiable computation): each turn produces a proof,
and the chain of turns is folded into one apex proof. Today that recursion is
**STARK-in-STARK**: to fold, you *verify the previous STARK proof inside the next
circuit*. Verifying a FRI proof in-circuit is costly — it IS the apex, the BN254 shrink,
the whole wrap tower we just built. Every recursion step pays a "verify a proof" tax.

**Folding (a.k.a. accumulation) removes the per-step verification.** Instead of proving
"I verified the previous proof," you **fold** the previous *instance* (a claim about a
computation) with the current one into a single combined instance, using a cheap random
linear combination plus a commitment to one "cross term." No SNARK/STARK verification per
step. At the very end you prove the *single folded instance* once — the "decider." So:

- **Recursive verification** (dregg now): per step = verify a whole proof in-circuit (expensive).
- **Folding**: per step = a few group operations (~2 MSMs + a hash). Constant, tiny. One real proof at the end.

That is the entire appeal: collapse the apex→shrink→wrap tower into "fold cheaply N times,
prove once."

## 2. The scheme family (what "folding recursion" actually names)

- **Nova** (Kothapalli–Setty–Tzialla 2021) — folds two **R1CS** instances via *relaxed
  R1CS* (adds a slack/error term so the fold stays a valid instance). Witnesses are
  committed with a **homomorphic (Pedersen) commitment**, so folding witnesses = a linear
  combination. IVC augments the step circuit with a tiny constant-size "folding verifier"
  (just the fold arithmetic). Needs a **2-cycle of elliptic curves** (Pallas/Vesta,
  BN254/Grumpkin). Final proof = a Spartan zk-SNARK "decider" (or wrap to Groth16).
- **SuperNova** (2022) — Nova + **non-uniform IVC**: different step circuits (a CPU with
  opcodes); you only prove the instruction actually executed. The zkVM shape.
- **HyperNova** (2023) — folds **CCS** (Customizable Constraint Systems: a generalization
  that captures R1CS, Plonkish, and **AIR with high-degree gates**) via a multi-folding
  scheme built on **sum-check**. Handles high-degree gates *without the R1CS degree-2
  blowup*. ← the natural fit for AIR-shaped systems like dregg's.
- **ProtoStar** (Bünz–Chen 2023) — a general accumulation framework for any special-sound
  protocol; efficient with **high-degree gates AND lookups** (it accumulates lookup
  relations). dregg uses lookups heavily (the TID chip tables, range checks), so ProtoStar's
  lookup accumulation is directly relevant.
- **ProtoGalaxy** (2023) — ProtoStar-family, folds **many** instances at once (tree/parallel folding).
- **NeutronNova** (2024) — latest curve-based; folds via a zero-check/sum-check with better
  efficiency than HyperNova, small recursion.
- **LatticeFold / LatticeFold+** (Boneh–Chen 2024) — folding over **lattices (Ajtai
  commitments)** instead of curves → **POST-QUANTUM**. Research-stage, but this is the one
  that matters most for dregg (see §4). 

The common requirement: a **homomorphic commitment** (you fold witnesses by linear
combination). Hashes are *not* homomorphic — which is exactly why FRI/STARK can't fold this
way, and why folding schemes reach for curves (Pedersen) or lattices (Ajtai).

## 3. How it maps onto dregg (what changes, what's kept)

- **dregg today**: turn AIR (BabyBear + Poseidon2) → STARK → recursion verifies the prior
  STARK in-circuit → apex → BN254-native shrink → gnark → Groth16 → EVM. The recursion is
  the expensive part.
- **dregg with folding**: each turn's AIR → a CCS instance → fold turns with ~constant
  per-step cost (no FRI-per-step) → one decider SNARK at the end, directly EVM-friendly.
  The apex/shrink/wrap tower **collapses** into fold-cheaply + prove-once. The turn semantics,
  the effect-VM, the capability logic — unchanged; only the *recursion substrate* swaps.

That sounds like a pure win. It isn't, for dregg specifically, because of two frictions.

## 4. ⚑ Friction #1 (the load-bearing one): post-quantum safety

dregg's identity includes **quantum-safe finality** — the PQ metatheory, ML-DSA signatures,
and the hash-based FRI transparency (hashes are believed PQ-secure; the whole
`project-pq-metatheory-connected` thread rests on this). Curve-based folding
(Nova/SuperNova/HyperNova/ProtoStar/NeutronNova) commits with **elliptic-curve Pedersen
commitments — which are NOT post-quantum** (a quantum computer breaks discrete log). Moving
dregg's recursion to curve-folding would **break the PQ story for the recursion layer.**

Options:
- **(a) LatticeFold / PQ folding** — folding over Ajtai (lattice) commitments keeps the PQ
  guarantee. This is the dregg-appropriate frontier. Immature (2024 research) but the right
  target: it gets folding's speed *without* surrendering PQ.
- **(b) Hybrid** — fold the hot inner loop with curves (fast) but keep the *settlement*
  commitment PQ. Then the recursion itself isn't PQ — a partial retreat dregg may not accept.
- **(c) Stay hash-based (STARK-IVC) and optimize the wrap** — native-hash + blowup-rebalance
  + GPU (ICICLE). Keeps PQ fully, accepts the recursion cost. **This is what we are doing now.**

## 5. Friction #2 (the sneaky one): the field mismatch

dregg's AIRs are over **BabyBear (31-bit)** — chosen *for prover speed* (small field = fast
NTT/hash). Curve-folding works over the **curve's scalar field (~256-bit)**. So folding dregg
means either:
- **emulate BabyBear over the curve's big field** — the SAME emulation tax we just spent the
  whole wrap effort *escaping* (BabyBear-in-BN254 was 188M constraints). Self-defeating; or
- **re-express dregg's constraint systems natively over the curve/lattice field** — a large
  rewrite of the AIRs, and you lose BabyBear's small-field speed.

There is research on small-field folding, but the commitment field vs constraint field
mismatch is a real, deep friction — folding is not a drop-in for a BabyBear-native system.

## 6. Other tradeoffs (briefly)

- **Trusted setup**: the folding part (Nova) is transparent; the *decider* SNARK may need a
  setup (Groth16 does — dregg already has one for the EVM verifier; Spartan/HyperNova deciders
  can be transparent).
- **The curve cycle**: Nova needs a 2-cycle (Pallas/Vesta, BN254/Grumpkin) and the "other
  curve" arithmetic — added complexity.
- **Maturity**: Nova/SuperNova are production-ish (Lurk, Jolt-adjacent). HyperNova/ProtoStar/
  NeutronNova are newer. LatticeFold is research.

## 7. Implementations to look at

- **Sonobe** (PSE + 0xPARC) — Rust folding framework: **Nova, HyperNova, ProtoGalaxy**, with
  a **Groth16/Circom decider** for on-chain verification. The most usable multi-scheme library
  — the entry point if we ever prototype folding for dregg (HyperNova, since dregg's AIRs are
  high-degree CCS-shaped).
- **Arecibo** (Lurk Lab) — maintained Nova/SuperNova fork.
- **microsoft/Nova** — the reference Nova.
- **Jolt** (a16z) — Lasso lookups + Nova-style zkVM.
- **NeutronNova / LatticeFold** — papers + reference impls emerging.

## 8. Verdict for dregg

Folding is genuinely the prover-speed frontier — it collapses the recursion tower. But for
**dregg specifically** it collides with two deliberate choices: **PQ-safety** (curve-folding
isn't PQ) and the **BabyBear small field** (folding wants a big commitment field → re-import
the emulation tax we just escaped, or rewrite the AIRs).

So the dregg-honest path:
1. **Now**: keep optimizing the hash-based wrap — native-hash (done, proven end-to-end),
   blowup-rebalance (sweeping), GPU/ICICLE (prototyping), AIR-trace reduction. This preserves
   PQ + BabyBear speed and directly attacks the ~18-min shrink.
2. **Watch**: **LatticeFold / PQ folding** as it matures — it is the only folding path that
   keeps dregg's PQ guarantee. If it becomes practical, *that* is dregg's folding future.
3. **Prototype-when-worth-it**: a Sonobe/HyperNova spike would teach us the real numbers, but
   the PQ + field frictions make it a research evaluation, not a migration. Not now.

Folding is not a lever we pull today; it is the architecture we evaluate as PQ-folding
matures, precisely because dregg refuses to trade away quantum-safety for prover speed.
