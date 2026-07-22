# Orientation: the EVM fair-market work vs. the existing DrEX/fhegg kernel

*Written 2026-07-19 after discovering — mid-build — that most of the "fair batch market"
vision was ALREADY BUILT in the Lean-first `Market/` (DrEX) + `fhegg-*` corpus. This corrects a
scope error (I built an EVM clearing layer before fully orienting on the record) and pins the
genuine additive line so future work COMPOSES with DrEX instead of re-deriving it. Discipline
tags: orient-from-the-record, integrator-must-not-compress-scope, describe-at-current-resolution.*

## What ALREADY EXISTS (mature) — DrEX / fhegg

**DrEX ("Dragon's Egg Exchange") — a Lean-first, proof-carrying, private, verify-not-find
uniform-price batch-clearing exchange.** It is NOT an FHE library to wire in; it is the vision,
substantially built:

- **`metatheory/Market/Clearing.lean`** (green in lake; `Market` is a defaultTarget) — the
  clearing RULES proven in Lean: `clearing_fair` (every cleared intent's predicate is satisfied),
  `clearing_conserves_per_asset` (conservation), `unfair_refused` / `mint_refused` (a
  pool-balanced-but-unfair, or would-mint, allocation is provably NOT a clearing). Multilateral
  intent-based clearing (categorical). This is DrEX rung 1 = execution soundness.
- **`Market/CertF.lean`, `CertQp.lean`, `CertQpRustDenotation.lean`** — the certificate IR
  (primal-dual / QP) + a **Lean↔Rust refinement of the deployed `CertQp::check`** (the residual
  is the honest f64/IEEE seam). Verify-not-find: an untrusted solver emits a certificate, a
  checked (Lean-verified) predicate validates it.
- **`fhegg-fhe/`** — the FHE stack: BFV/TFHE, `dark_amm.rs` (a constant-product AMM with HIDDEN
  reserves, invariant enforced homomorphically via one ct×ct multiply, opening only pass/fail),
  `threshold.rs` (n-of-n decrypt), `order_ingress.rs`, `convex_step.rs`, MPC. Dark-until-clear.
- **`fhegg-solver/`** — the fast untrusted solver (uniform-price aggregation + PDHG flow-LP),
  "the engine is defined by the CERTIFICATE, not the rule" (any convex clearing is a member).
- **`fhegg-rtl/lean/`** — VERIFIED FHE hardware (Netlist, Butterfly, Accumulator). `Bfv/` —
  Lean-first BFV with the wrap/noise silent-failure guards as theorems.
- **Roadmap gap (`FHEGG-MATURITY-ROADMAP.md`):** the FHE CRYPTO frontier — ct×ct multiply / T>1,
  the n-of-n threshold-decrypt smudging bound (`NoViewerKeyCustodyResidual`). NOT deployment.
- **No EVM / Solidity path.** DrEX/fhegg is Rust + Lean + FHE (off-chain private clearing
  kernel). There are no `.sol` contracts, no foundry.

## What THIS SESSION added (the genuine, non-duplicative contributions)

1. **The Verifereum EVM-BYTECODE proof layer (genuinely new, orthogonal to DrEX).** DrEX proves
   the exchange RULES in Lean at the spec/certificate level; nobody had proven a *deployed EVM
   contract over the real bytecode*. This session stood up Verifereum (HOL4 EVM semantics) on our
   HOL, proved the launch token's anti-rug core ∀-inputs over the actual 2003-byte runtime
   (`SPEC_mint_path_{notminter,alreadyminted,capexceeded}_reverts`, cheat/oracle-clean), fixed an
   upstream Verifereum cheat, and built **reusable path-proof automation** (`evmSpecAutomation*`).
   Files: `~/dev/verifereum/examples/{dreggLaunchToken,dreggMintGuard,dreggMintPaths,evmSpecAutomation*}.sml`.
2. **An EVM/Solidity deployable realization** — `BatchClearingVerifier.sol` (11/11), `BatchClearedMarket.sol`
   + `MockStockToken.sol` (5/5 e2e). fhegg is off-chain; an on-chain deployable market is a real gap.
   ⚠ HONEST OVERLAP: the clearing MATH (`CLEARING-FUNCTION-SPEC.md`) + the verifier RE-DERIVE
   DrEX's clearing at the EVM layer. Some of this duplicates the mature Lean corpus.
3. **The coin/stock / Robinhood-Chain product framing** — tokenized-stock quote asset, the Clark
   opportunity. Genuinely new application.

## The unification (compose, don't rebuild)

- **DrEX/fhegg = the private, Lean-verified, FHE clearing KERNEL** (off-chain; solver + certificate;
  threshold-decrypt for dark-until-clear).
- **The EVM layer (ours) = the on-chain deployable REALIZATION + the bytecode-proof assurance.**
  The right shape: the DrEX engine produces a clearing + a `CertF`/`CertQp` certificate; the
  on-chain contract should **CHECK that certificate on-chain** (reframe `BatchClearingVerifier`
  from re-deriving clearing to verifying a DrEX certificate) rather than re-implement the
  mechanism; Verifereum proves the on-chain checker over bytecode; coin/stock is the product;
  fhegg's threshold-decrypt provides dark-until-clear. This makes the EVM work ADDITIVE (an
  on-chain leg + a bytecode-proof layer DrEX lacked) instead of a parallel re-derivation.
- **OPEN (ember's steer):** was there an intended DrEX→EVM/on-chain path already? How should the
  on-chain settlement relate to fhegg's threshold-decrypt boundary? Which of this session's
  market-Solidity is a keeper (the certificate-check realization) vs. fold-back-into-DrEX?

## The lesson (for the record)

Orient on the WHOLE record before building — the `fhegg-*` + `Market/` corpus (47+ Lean files, a
mature private-clearing exchange) was in the tree the whole time; I referenced "fhegg" in the
design docs but treated it as a future FHE-wiring rung instead of the system that already IS the
vision. The genuinely-new work (Verifereum EVM bytecode proofs + reusable automation, the coin/
stock product) stands; the market-clearing re-derivation should fold into DrEX.
