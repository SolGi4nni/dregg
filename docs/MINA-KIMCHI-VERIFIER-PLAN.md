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
