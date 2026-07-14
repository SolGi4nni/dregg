//! # fhEgg Stage-1 fast UNTRUSTED solver
//!
//! The "fast untrusted search" half of the fhEgg engine. Two solvers over
//! PLAINTEXT inputs (the solver sees everything — privacy is the later
//! STARK-ZK/FHE stage, not here), each maximally fast, each producing an output
//! a separate VERIFIED checker validates:
//!
//! 1. [`clearing`] — the uniform-price aggregation clearing (fhEgg T=1):
//!    fold N orders into supply/demand curves over K price levels, cross once,
//!    emit the uniform price + conserving allocation
//!    (`docs/deos/FHEGG-KERNEL.md`).
//! 2. [`pdhg`] — the PDHG flow-LP solver (the Cert-F convex step): oblivious,
//!    fixed-T, topology-only-preconditioned primal-dual for the volume-max
//!    circulation LP `max wᵀf s.t. Af=0, 0≤f≤c`, emitting the
//!    [`cert::CertF`] primal-dual certificate
//!    (`docs/deos/PRIVATE-CONVEX-ENGINE.md`).
//!
//! [`gpu`] carries the wgpu paths (the aggregation fold + the PDHG matvec loop);
//! [`cert`] is the certificate IR + the bridge (JSON) to the Lean checker.
//!
//! ## The mechanism FAMILY (the engine is defined by the CERTIFICATE, not the rule)
//!
//! Uniform-price is the FLOOR, not the only clearing. Because the engine is
//! verify-not-find — an untrusted convex solve + a checked certificate — ANY
//! convex-program clearing is a member. Alongside [`clearing`] (uniform-price) and
//! [`pdhg`] (volume-max circulation) it also carries:
//!
//! 3. [`discriminatory`] — pay-as-bid clearing: the gains-from-trade
//!    winner-determination is a two-node flow-LP (reuses the linear [`cert::CertF`]),
//!    then each winner settles at its OWN limit (contrast with the single uniform
//!    price).
//! 4. [`fisher`] — welfare-max / Fisher-market equilibrium: the Eisenberg–Gale
//!    convex program `max Σ bᵢ log Uᵢ`, solved by proportional-response (mirror
//!    descent) with the [`fisher::CertEq`] competitive-equilibrium (KKT) certificate.
//!    The GENERAL competitive clearing — uniform-price is its linear-utility case.
//! 5. [`cfmm`] — CFMM optimal routing: `max Σ gᵢ(δᵢ) s.t. Σδ≤Δ` over public pool
//!    curves, solved by water-filling on the marginal price with the
//!    [`cfmm::CertRoute`] KKT certificate.
//! 6. [`qp`] — the Markowitz portfolio QP ([`qp::CertQp`]).
//! 7. [`package`] — the all-or-none / package combinatorial clearing by CERTIFIED
//!    APPROXIMATION: an untrusted integral packing + a Lagrangian dual bound, with
//!    the [`package::CertPackage`] certificate proving feasibility (indivisibility
//!    preserved, `x ∈ {0,1}`) + a near-optimality ratio `W ≤ W* ≤ UB(y)`.
//!
//! Cert-F/Aggregation certificates are LINEAR (Tier-0/1); CertEq is bilinear and
//! CertRoute nonlinear in the witness (both `O(size)`, Tier-1). The integer /
//! combinatorial exact clearing (all-or-none, indivisible assignment) is the
//! NP-hard boundary — the EXACT optimum stays NP-hard, but [`package`] answers it
//! the verify-not-find way: a feasible integral clearing plus a CHECKED weak-
//! duality bound certifying it is within a factor of optimal (Tier-1/Shielded).
//!
//! Trust model: the solver is UNTRUSTED. What makes its output trustworthy is
//! the [`cert::CertF`] certificate — a LINEAR primal-dual witness the verified
//! checker validates (translation validation for convex optimization). The
//! solver's job is to produce a small-gap certificate FAST; the checker decides.

pub mod air;
pub mod cert;
pub mod cfmm;
pub mod clearing;
pub mod discriminatory;
pub mod fisher;
pub mod gpu;
pub mod package;
pub mod pdhg;
pub mod pricecert;
pub mod qp;
