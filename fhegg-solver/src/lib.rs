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
//! Trust model: the solver is UNTRUSTED. What makes its output trustworthy is
//! the [`cert::CertF`] certificate — a LINEAR primal-dual witness the verified
//! checker validates (translation validation for convex optimization). The
//! solver's job is to produce a small-gap certificate FAST; the checker decides.

pub mod cert;
pub mod clearing;
pub mod gpu;
pub mod pdhg;
