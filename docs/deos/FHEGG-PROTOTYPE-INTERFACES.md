# fhEgg prototype — the fixed-interface decomposition for SAFE parallel swarm work

*Written 2026-07-18. The vision (`FHEGG-MATURITY-ROADMAP.md`) is 5 builds; ember wants all 5 prototyped in
parallel. Parallelizing crypto safely requires what our earlier swarms lacked: **disjoint module ownership +
fixed interfaces + pre-built shared files + an opus review layer.** This doc is the contract. Each lane owns
ONE new module and implements it against the signatures below; it touches NO shared file (I pre-create
`lib.rs` mods + Cargo deps + these stubs, so there is zero contention). Consuming lanes code against these
signatures, so a lane never re-derives another lane's design.*

## Why our earlier swarms tangled (the failures this fixes)
1. **Shared-file contention** — lanes concurrently edited `lib.rs`/`Cargo.toml`/`TESTQALOG` → sweeps + half-states. FIX: I pre-add every `mod` + dep + stub; lanes touch only their own file.
2. **Build starvation** — lanes burned their budget WAITING on the tfhe compile, returned unverified code. FIX: pre-warm the build (compile once, deps cached) before the swarm; lanes build incrementally.
3. **Task-level prompts, not interface-level** — lanes re-derived design and collided. FIX: fixed signatures below; a lane implements a body, it does not choose an interface.
4. **No insufficiency-catching layer** — I gated but nothing hunted vacuity/mirrors. FIX: an **opus review phase** after impl: each module reviewed by an independent opus agent for vacuous theorems, mirror-crypto (not oracle-anchored), faked integration, silent-failure gaps.

## The shared substrate (I pre-build + commit this BEFORE the swarm — no lane touches it)
- `fhegg-fhe/src/lib.rs`: `pub mod threshold; pub mod convex_engine; pub mod gpu_arena; pub mod fhir;` (all four, up front).
- `fhegg-fhe/Cargo.toml`: any new deps (mbfv is already in `fhe`; wgpu already added).
- Each module file created with the FIXED public signatures below + `todo!("lane owns this")` bodies that compile.
- The integration target (`fhegg-fhe/tests/e2e_private_derivative.rs`) scaffolded against these signatures.

## The five modules — disjoint files, fixed interfaces

### 1. `threshold.rs` — REAL no-viewer (keystone). Owns: the n-of-n collective threshold-decrypt with PROVEN smudging.
Anchor: fhe.rs `mbfv` (`DecryptionShare`, `PublicKeyShare`, `CommonRandomPoly`) is the crypto oracle; the smudging bound is proven in `Bfv/Smudging.lean` (module 1b). Consumes: a folded `LeanCiphertext`. Produces: the plaintext result, decryptable ONLY by an n-of-n quorum, no single party holding `sk`.
```
pub struct KeyShare { /* one party's share of the collective secret key */ }
pub struct DecryptShare { /* one party's smudged partial decryption */ }
/// n-of-n collective keygen (each party contributes; no dealer). Anchored to mbfv PublicKeyShare + CommonRandomPoly.
pub fn collective_keygen(n: usize, params: &BfvParams) -> (CollectivePublicKey, Vec<KeyShare>);
/// One party's SMUDGED partial decrypt of the folded aggregate. The smudging noise is sampled to the bound Bfv/Smudging.lean proves hides the key share (NOT fhe.rs mbfv's TODO fresh-noise).
pub fn partial_decrypt(share: &KeyShare, ct: &LeanCiphertext, smudge_bits: u32) -> DecryptShare;
/// Combine n partial decrypts → plaintext. Refuses if < n shares or params disagree.
pub fn combine(shares: &[DecryptShare], params: &BfvParams) -> Result<Vec<u64>>;
```
Tooth: encrypt with the collective key → fold → n parties partial-decrypt → combine == plaintext sum; AND a `k<n` quorum learns NOTHING (statistical test that the combined-minus-one distribution is smudge-independent, mirroring `Bfv/Smudging.lean`).

### 1b. `metatheory/Bfv/Smudging.lean` — the smudging SECURITY theorem (what fhe.rs's TODO lacks).
Prove: with smudging noise ≥ the stated bound (exponential in the ciphertext noise), a partial decryption is statistically independent of the key share (the no-viewer security property). FAILING-SIDE required: `smudge_too_small_leaks` (a sub-bound smudge is proved to leak). Kernel-clean, 0 sorry.

### 2. `convex_engine.rs` — the convex engine at T>1. Owns: iterated `x ← prox(x − τAx)` with a noise budget.
Consumes: `convex_step::{SignedCt, PublicLinearStep, convex_linear_step}` (T=1, already built + tested). Produces: `x_T` after T iterations.
```
/// T iterations of x ← prox(x − τ·A·x). `prox` is the bounded nonlinearity (box clamp); applied per iteration.
/// REFUSES loudly when the accumulated noise budget (from Bfv/Noise.lean's T-composition bound) would exceed
/// the decrypt margin — a T too deep for the params fails CLOSED, never silently mis-clears.
pub fn convex_solve(x0: &[SignedCt], step: &PublicLinearStep, prox_lo: i64, prox_hi: i64, iterations: u32, t: u64) -> Result<Vec<SignedCt>>;
pub fn max_iterations_for_params(step: &PublicLinearStep, t: u64) -> u32; // the proven-safe T ceiling
```
Depends on 2b (`Bfv/Noise.lean` extended with the T-deep composition bound). Tooth: differential vs a plaintext PDHG (the FHE `x_T` decrypts to the same as a cleartext T-iteration solve), on a real small convex program (e.g. a 2-asset portfolio rebalance).

### 2b. `metatheory/Bfv/Noise.lean` (extend) — the T-composition noise bound. `noise_after_T`, and `T_gt_ceiling_fails` (failing side).

### 3. `gpu_arena.rs` — the GPU-RESIDENT pipeline (performance north star). Owns: upload-once, compute-resident.
Wraps `bfv_gpu`. The fix for the transfer-bound "loss": data stays on-device across the whole pipeline.
```
pub struct Arena { /* wgpu device + a resident ciphertext buffer pool */ }
pub struct ResidentHandle { /* an on-device ciphertext-set, never downloaded until asked */ }
pub fn arena() -> Option<Arena>;                                   // None if no adapter
pub fn upload(&self, cts: &[LeanCiphertext]) -> ResidentHandle;    // the ONE transfer
pub fn fold_resident(&self, h: &ResidentHandle) -> ResidentHandle; // fold WITHOUT download (now free)
pub fn download(&self, h: &ResidentHandle) -> Vec<LeanCiphertext>; // the ONE readback
```
Tooth: a bench proving a RESIDENT fold-of-folds (upload once, fold K times on-device, download once) BEATS the CPU where the one-shot fold lost — the residency thesis, MEASURED. Parity: resident result == `bfv_lean::fold` bit-for-bit.

### 4. `fhegg-fhe/src/fhir/mod.rs` — the typed product DSL (the factory). FULLY DISJOINT from the crypto.
Implements the frontier-doc grammar (`FHEGG-PRODUCT-ORDER-FRONTIER.md`): three type axes (`visibility ∈ {public,committed,opened}` × `curvature ∈ {affine,convex,concave,discrete}` × `phase ∈ {payoff,price,clear,settle}`), the reject-list, and `compile(P) -> ClearingSpec`.
```
pub enum Visibility { Public, Committed, Opened }
pub enum Curvature { Affine, Convex, Concave, Discrete }
pub struct Program { /* the typed AST: affine/convex/constraint/trigger/order/program */ }
pub struct ClearingSpec { pub a: Vec<Vec<i64>>, pub tier: Tier, pub leakage_manifest: LeakageManifest /* ... */ }
/// The six-part admissibility judgement: admissible IFF it compiles + passes the resource manifest. Returns the
/// tier the program is well-typed at (Tier0 iff FHE-tractable, ...), or a NAMED rejection (the reject-list).
pub fn admissible(p: &Program) -> std::result::Result<Tier, Rejection>;
pub fn compile(p: &Program) -> std::result::Result<ClearingSpec, Rejection>;
```
Tooth: the frontier reject-list is enforced (private-matrix × secret-variable REJECTS; a binary decision inside the optimizer REJECTS; an affine public program at Tier2 COMPILES) — each with a test that BITES.

### 5. `fhegg-fhe/tests/e2e_private_derivative.rs` — the INTEGRATION proof. Codes against 1-4's signatures.
Pick ONE real derivative (a 2-asset portfolio rebalance, or an option payoff), express it in `fhir`, `compile` to a `ClearingSpec`, run `convex_solve` at Tier 0 over collective-key-encrypted state, threshold-`combine` the result, and assert it matches a plaintext reference. This is the vision's integration proof — it compiles against the stubs from day one and goes GREEN as the modules land. Owns no module; it is the north-star test.

## The swarm shape (against this contract)
- Phase IMPL: 4 crypto/lang lanes (threshold, convex_engine, gpu_arena, fhir) + 2 Lean lanes (Smudging, Noise-T) + 1 integration lane (e2e) — each owns its file, implements against the signature above. Fable.
- Phase REVIEW: 1 opus reviewer per module — reads the actual code/theorem STATEMENTS, hunts vacuity / mirror-crypto / faked integration / silent-failure gaps, reports CONFIRMED insufficiencies. (This is the layer we never had.)
- Supervisor (me): pre-build the substrate, pre-warm the compile, gate each verified module, act on the review findings.
