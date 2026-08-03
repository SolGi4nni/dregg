# A fast Lean Kimchi (Mina) proof verifier + interchain state-query circuits — plan

*Goal (ember): a Mina proof verifier, as fast as possible, in Lean; interchain proofs as nice as possible;
bake circuits for specific verifiable state-queries from other chains. Built by a Claude+kimi hybrid swarm —
kimi does the bulk, Claude plans + reviews + directs.*

## Why this is tractable NOW (the substrate exists)
The 07-26 daysprint built a shared, forced, Lean-GENERATED crypto-gadget library: field-tower + curve-point
generators (`Bls12381Tower`/`TowerExt`/`Forcing`, `Ed25519Gadget`) over the deployed `AirBuilder.Head` vocabulary,
each proven to *force* the real field/curve op mod the prime. **Kimchi verification is the same pattern at a new
curve** — so the Pasta gadgets are "just express it," not greenfield. Plus `circuit-prove/sketches/mina-pasta-hash-
probe` already de-risks the Poseidon-over-Pasta transcript (dregg reproduces o1js `Poseidon.hash` natively).

## The verifier, bottom-up (each a metaprogramming gadget, mirror the BLS/Ed25519 modules)
1. **Pasta field arithmetic** — Fp (Pallas base = Vesta scalar) and Fq (Vesta base = Pallas scalar), the 2-cycle,
   both ~255-bit. 9 limbs × ~30 bits, quotient-witness reduction — a DIRECT crib of `Bls12381Tower`'s Fp (swap the
   prime). Forcing lemmas by the same congruence-over-ℤ discipline (`Bls12381Forcing`).
2. **Pallas/Vesta point ops** — the short-Weierstrass complete/incomplete add + double + the **endomorphism**
   (Pasta's `endo` — the fast-scalar-mul optimization Kimchi leans on; this is a big chunk of "as fast as
   possible"). Crib `Ed25519Gadget`'s curve-composes-over-field structure.
3. **Poseidon-over-Pasta transcript** — the Fiat-Shamir sponge (Mina's Kimchi params). Extend the pasta-hash-probe;
   it's a Poseidon permutation gadget (ARX-free, it's field muls/adds — cheaper to express than SHA).
4. **IPA opening verification** — the inner-product argument (Kimchi's PC is IPA/bulletproof over Pasta, NOT KZG).
   THE cost center: the multi-scalar-mult (MSM) of ~log(n) rounds + the final check. "As fast as possible" = a
   windowed/bucket MSM + the endo + batching openings. This is where kimi spends most effort.
5. **The Kimchi verify equation** — PLONK gate constraints + the permutation (copy-constraint) argument + Plookup +
   the linearization + the IPA check. THE SPEC IS the o1-labs `proof-systems` (kimchi) Rust verifier — crib it
   verbatim; formalize/generate its checks.
6. **Pickles/recursion tip** — Mina's state is a recursive Pickles proof over the 2-cycle; "verify Mina" = verify
   the tip Kimchi proof (Step/Wrap). Scope v1 to a single Kimchi proof; recursion is the follow-on.

## Two directions (ember: "as nice as possible" + "gas-efficient for those other protocols too")
- **INWARD — verify Mina in dregg** (the above): makes Mina a dregg lightclient + transitively any chain that
  settles a Kimchi proof to Mina (the internet-of-proofs bet; transitive set is small TODAY but this is the bet).
- **OUTWARD — settle dregg to Mina, gas-efficiently**: dregg's state as a Pickles-verifiable proof Mina checks
  cheaply. Needs a Pasta-native-MMCS terminal recursion (the pasta-hash-probe is the de-risked hash primitive).
  Gas-efficiency on Mina = fitting dregg's attestation into Kimchi's ~2^16 domain.

## State-query circuits (bake per query type)
On top of a verified Mina state root: a **verifiable-query gadget** — given the proven root, prove a specific
query (zkApp state field, account balance/nonce, token holding) via the Merkle/account path into the root. One
small circuit per query shape; composes with the LC (verify root → query under it). Same shape as the ETH
FIN/EXEC Merkle folds already built — the fold machinery generalizes.

## CRIB sources
o1-labs `proof-systems` (kimchi verifier — the spec) · `mina-poseidon` + `mina-curves` (Pasta arithmetic + Poseidon,
already a dep of dregg storage KZG) · the `mina-pasta-hash-probe` · the dregg crypto-gadget library (the pattern +
the forcing discipline) · =nil; Placeholder (the only prior cryptographic Kimchi-wrap — a cost reference).

## kimi task breakdown (Claude reviews each; verify-agent-claims: read the theorems, check #assert_axioms)
- **K1 (foundation):** Pasta Fp/Fq field gadgets + forcing — crib `Bls12381Tower`, swap the prime, KAT vs py `pasta`.
- **K2:** Pallas/Vesta point ops + the endomorphism — crib `Ed25519Gadget` curve structure.
- **K3:** the Poseidon-over-Pasta sponge gadget (extend the probe) + KAT vs o1js.
- **K4 (the big one):** the IPA opening MSM — windowed/endo/batched, gas-count-honest.
- **K5:** the Kimchi verify equation, cribbing the o1-labs Rust verifier check-by-check.
- **K6:** the state-query gadgets (per query type).
All on hbox (`swarm-build`), House Law #1 (Lean-authored/generated), named-file commits, honest KAT/forcing scope,
NO overclaiming a working pairing/verify until the whole chain composes. Claude gates each on axiom-cleanliness +
reading the actual theorem statements (not the summary).

## K4 design (kimi worked it out before hitting its quota; NOT yet built)
**Scalar-mult decision — one unified gadget, complete, no case splits.** kimi analyzed the a=0 short-Weierstrass
formulas and concluded: use the **RCB (Renes–Costello–Batina) complete addition** formula for BOTH the double and
the add step (add-2015-rcb is *strongly unified*, and RCB completeness holds for prime-order curves — Pasta has
cofactor 1). So `[k]P` via GLV/Shamir over the two ~128-bit halves is ONE curve-op gadget, exception-free (handles
P=±Q, O), avoiding the exceptional-case handling naive Jacobian doubling needs.
- Honest gate count: RCB-add ≈ 41 core gates (12 mul + 29 add) → full-generator ≈ 14.9K gates; the GLV scalar-mult
  ≈ 129 bits × (cAdd(acc,acc) + 2-way select + cAdd(acc,S)) ≈ **2.46M gates** — 3.4× better than naive
  constant-time (~8.3M). (Projective dbl-2015-rcb is ~expensive as the add, so unified-add-for-both is both simpler
  AND best.)
- ⚑ **AND WHAT "one gate per mul" MEANS AT BABYBEAR — the correction K1 as built does not carry into its own
  prices (recorded 2026-08-03).** The counts above charge ONE core gate per Pasta multiplication, which is exactly
  what `Dregg2.Circuit.Emit.PastaField.fpMulCore` emits: a single degree-2 gate over a 9×30 limb encoding, with
  `pastaLimbRange` emitted NOWHERE in the tree (its six caller wrappers have zero call sites) and no boolean pins
  on the carry/borrow columns. That gate does not enforce the multiply in the field the prover works in: its
  reduction witnesses are free columns whose coefficients are units mod `p_babybear`, so its mod-felt reading holds
  at **every** operand triple (`PastaField` §6.4, computed on the emitted descriptor bytes; the emitted RCB-add
  measured as 33 core gates, 14 multiply-shaped and 19 add/sub). ⚑ **A multiply that is SOUND at BabyBear is a
  different encoding.** `2b + log₂ k < log₂ p_babybear` fails at `b = 30, k = 9` (`63.17` against `30.91`) and holds
  at `b ≈ 13, k ≈ 20`, where one multiplication is `k² = 400` limb products plus a reduction and ~40 range-checked
  carry rungs — **≈10³ BabyBear constraints, not 1** (`LightClientMinaAir` §1b). So **every gate figure in this
  section is ~10³ low against a sound gadget**: an RCB-add is ≈1.6·10⁴ constraints, the full-generator ladder ~10⁷,
  and the GLV scalar-mult ~10⁹. That does not change K5's conclusion below — it strengthens it, because the leg to
  DEFER is now three orders further out of reach, and the reachable architecture is the Mina-side shrink terminal
  rather than an in-dregg Pasta ladder.
- The dbl-specific gadget is NOT worth building in this gate model (named micro-opt, saves nothing).

## K5 design crux (from KIMCHI-VERIFY-SPEC.md 63726f561): DEFER the MSM
The dominant cost (C9's s-vector MSM `⟨s,G⟩`) is a **65536-element non-native Vesta MSM ≈ 10^7–10^8 gates**, two
orders beyond everything else. **Pickles DEFERS it** (the `sg` split, ipa.rs:335-336) rather than verifying it
in-circuit — accumulated across recursion, checked once at the end. So K5 must be built **deferral-first**: verify
everything cheap in-circuit, ACCUMULATE the MSM as a deferred obligation, don't brute-force it. This is the whole
"as gas-efficient as possible" answer. (Design decision approved: derive the batching `rand_base` Fiat-Shamir from
the transcript, since in-circuit RNG is unavailable.)
