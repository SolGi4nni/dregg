//! The XM-VRF-family reference construction: a hash-based, key-updatable VRF.
//!
//! # What this is
//!
//! A verifiable random function `(keygen, eval, verify)` — the Micali–Rabin–Vadhan
//! triple modelled abstractly in `metatheory/Dregg2/Crypto/VRF.lean` — instantiated
//! from a collision-resistant hash and a PRG ONLY (no lattice, no pairing). It is
//! **key-updatable / forward-secure**: one key covers `2^height` epochs, and an
//! [`SecretKey::update`] ratchet advances the epoch while destroying the ability
//! to recompute past epochs' secrets.
//!
//! For leader sortition the VRF input is the epoch (slot) number: each epoch has
//! exactly one input, hence exactly one output — precisely the "at most one
//! output per `(pk, x)`" the consensus needs to stop a validator from grinding
//! several committee lotteries.
//!
//! # Construction (correctness-first reference)
//!
//! * **KeyGen(height):** sample a master seed `msk`. Derive a forward-secure seed
//!   chain `st_0 = PRG(msk, "st0")`, `st_{t+1} = PRG(st_t, "adv")`. For each epoch
//!   `t ∈ [0, 2^height)`: epoch key `ek_t = PRG(st_t, "ek")`, output
//!   `y_t = PRG(ek_t, "out")`, opening `r_t = PRG(ek_t, "rand")`, and Merkle leaf
//!   `leaf_t = H(t ‖ y_t ‖ r_t)`. The public key is the Merkle **root** over all
//!   leaves. `msk` is then DISCARDED and the running secret state is reset to
//!   `(epoch = 0, st_0, tree)`.
//! * **Eval(sk, epoch):** re-derive `ek_epoch → (y, r)` from the (forward-walked)
//!   chain state; the proof is `π = (r, auth_path(epoch))`.
//! * **Verify(pk, epoch, y, π):** recompute `leaf = H(epoch ‖ y ‖ r)` and check the
//!   Merkle path lands on `pk.root` at position `epoch`.
//! * **Update(sk):** `st ← PRG(st, "adv")`, `epoch += 1`, old `st` dropped.
//!
//! # Why UNIQUENESS holds — even under a maliciously chosen pk (the X-VRF fix)
//!
//! Fix ANY `pk` (root) — honest or adversarial — and any epoch `t`. Suppose
//! `(y₁, r₁, path₁)` and `(y₂, r₂, path₂)` both verify. Both paths authenticate a
//! leaf at position `t` to the SAME root, so by collision resistance of the Merkle
//! node hash the authenticated leaf value is unique:
//! `H(t ‖ y₁ ‖ r₁) = H(t ‖ y₂ ‖ r₂)`. If `y₁ ≠ y₂` (or `r₁ ≠ r₂`) that is a direct
//! blake3 collision. Hence `y₁ = y₂`: **at most one output verifies per `(pk, t)`,
//! with NO honest-keygen assumption** — the reduction is to hash collision
//! resistance alone. This is the `UniqueOutputs` predicate of the Lean framework;
//! its abstract "two verifying outputs refute uniqueness" tooth is
//! `two_outputs_break_uniqueness`.
//!
//! ## Contrast with the "Breaking X-VRF" (FC24) pitfall
//!
//! X-VRF derives its output from a WOTS+/XMSS one-time signature. WOTS+'s chaining
//! function is only ONE-WAY / 2nd-preimage-resistant, NOT collision-resistant, so a
//! maliciously crafted public key can admit two valid signatures — hence two valid
//! VRF outputs — for one input (Bodaghi, *Breaking the X-VRF*, FC24). The essence:
//! the chain does not collision-resistantly bind the output to `(pk, x)`. Here the
//! output is bound into a Merkle leaf by a FULL collision-resistant hash, so the
//! analogous "chain-shift" equivocation produces a non-verifying proof. The pitfall
//! is exhibited concretely in [`crate::naive_wots`] and contrasted in the tests.
//!
//! # References
//!
//! * *Key Updatable Hash Based VRF*, IACR ePrint **2026/052** — the XM-VRF family
//!   (hash + PRG, key-updatable, XMSS-derived) whose uniqueness this reference
//!   targets.
//! * A. Bodaghi et al., *Breaking the X-VRF* (a.k.a. *Breaking X-VRF*), Financial
//!   Cryptography **2024** — the uniqueness attack on X-VRF that motivates the fix.
//! * S. Micali, M. Rabin, S. Vadhan, *Verifiable Random Functions*, FOCS 1999 — the
//!   `(provability, uniqueness, pseudorandomness)` definitions.
//!
//! # HONEST BOUNDARY (read before relying on this)
//!
//! * This is a **correct-but-simplified** member of the XM-VRF family: a
//!   Merkle-committed hash VRF that gets FULL uniqueness right (reducing to blake3
//!   collision resistance). It is NOT a byte-faithful port of the ePrint 2026/052
//!   construction — in particular the exact XMSS internal-tree / L-tree structure,
//!   WOTS+ leaf compression, and bitmask/PRF-key schedule are abstracted into
//!   "one Merkle leaf per epoch committed with a CR hash". The security-relevant
//!   invariant XM-VRF adds over X-VRF (a CR commitment to the output, not a WOTS+
//!   chain) IS preserved and is what the uniqueness argument uses.
//! * **Reference parameters.** `height` bounds the number of epochs at `2^height`;
//!   the many-time bound and the tree depth are DOCUMENTED reference choices, not
//!   tuned deployment parameters.
//! * **Forward security** here means: after `update` past epoch `t`, `st_t` is gone
//!   and one-wayness of the PRG prevents recovering `ek_{<t}` (hence `y_{<t}`,
//!   `r_{<t}`) from the surviving state. It protects PAST epoch secrets against a
//!   later state compromise. It is the standard forward-secure-key guarantee; it is
//!   not analysed here against every adaptive model.
//! * **Proofs live in Lean.** The full uniqueness / pseudorandomness statements are
//!   in `Dregg2/Crypto/VRF.lean` and the cited papers; they are not re-proven in
//!   Rust. This crate is the executable reference, with tests exercising
//!   provability, uniqueness (incl. the X-VRF pitfall contrast), a pseudorandomness
//!   statistical smoke test, and key-update determinism.
//! * **Not deployment-grade / pre-audit.** No constant-time guarantees, no
//!   serialization format stability, no side-channel review.

use crate::hash::{hash_leaf, prg32, Bytes32};
use crate::merkle::{verify_path, MerkleTree};

/// Domain labels for the forward-secure chain and per-epoch derivations.
const L_ST0: &[u8] = b"XMVRF/st0";
const L_ADV: &[u8] = b"XMVRF/adv";
const L_EK: &[u8] = b"XMVRF/ek";
const L_OUT: &[u8] = b"XMVRF/out";
const L_RAND: &[u8] = b"XMVRF/rand";

/// The VRF output (32 bytes). Deterministic in `(sk, epoch)`.
pub type Output = Bytes32;

/// The public key: a Merkle root over the `2^height` epoch commitments, plus the
/// height (part of the public parameters). Everything needed to `verify`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct PublicKey {
    /// Merkle root committing every epoch's `(y, r)`.
    pub root: Bytes32,
    /// Tree height; the key covers epochs `[0, 2^height)`.
    pub height: u8,
}

/// A VRF proof: the leaf opening `r` and the Merkle authentication path binding
/// `H(epoch ‖ y ‖ r)` to the root.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Proof {
    /// Leaf opening randomness for this epoch.
    pub r: Bytes32,
    /// Merkle authentication path (siblings, leaf-layer up to the root).
    pub path: Vec<Bytes32>,
}

/// Errors from evaluation.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum EvalError {
    /// The requested epoch precedes the current (ratcheted-past) epoch — its
    /// secret state has been destroyed (forward security).
    EpochExpired {
        /// Current epoch pointer.
        current: u64,
        /// Requested epoch.
        requested: u64,
    },
    /// The requested epoch is `>= 2^height` — outside the key's lifetime.
    EpochOutOfRange {
        /// Requested epoch.
        requested: u64,
        /// One past the last valid epoch (`2^height`).
        capacity: u64,
    },
}

/// The running secret key. Holds the forward-secure chain state for the CURRENT
/// epoch, the epoch pointer, and the (public) Merkle tree used to build proofs.
/// The master seed is NOT retained.
#[derive(Clone, Debug)]
pub struct SecretKey {
    height: u8,
    /// Current epoch pointer; `eval` can serve epochs `>= epoch`.
    epoch: u64,
    /// Forward-secure chain state `st_epoch`. Advancing destroys the old value.
    st: Bytes32,
    /// Public Merkle tree (leaf hashes + internal nodes); needed to emit paths.
    tree: MerkleTree,
}

/// One forward step of the seed chain: `st_{t+1} = PRG(st_t, "adv")`. One-way, so
/// the predecessor is unrecoverable from the successor.
fn advance(st: &Bytes32) -> Bytes32 {
    prg32(st, L_ADV)
}

/// Derive `(y, r)` for the epoch whose chain state is `st`.
fn derive_epoch(st: &Bytes32) -> (Output, Bytes32) {
    let ek = prg32(st, L_EK);
    let y = prg32(&ek, L_OUT);
    let r = prg32(&ek, L_RAND);
    (y, r)
}

/// **KeyGen.** Deterministically derive a full key from a 32-byte master seed and
/// a tree `height` (epochs = `2^height`). The master seed is consumed to build the
/// tree and is not stored in the returned [`SecretKey`].
///
/// # Panics
/// If `height` is so large that `2^height` overflows `usize` on this platform.
pub fn keygen_from_seed(msk: &Bytes32, height: u8) -> (PublicKey, SecretKey) {
    let capacity = 1usize
        .checked_shl(height as u32)
        .expect("height too large for this platform");

    // Walk the forward-secure chain, committing each epoch's (y, r) as a leaf.
    let st0 = prg32(msk, L_ST0);
    let mut leaves = Vec::with_capacity(capacity);
    let mut st = st0;
    for epoch in 0..capacity {
        let (y, r) = derive_epoch(&st);
        leaves.push(hash_leaf(epoch as u64, &y, &r));
        st = advance(&st);
    }

    let tree = MerkleTree::build(height, leaves);
    let pk = PublicKey {
        root: tree.root(),
        height,
    };
    // Reset the running state to epoch 0; msk goes out of scope (discarded).
    let sk = SecretKey {
        height,
        epoch: 0,
        st: st0,
        tree,
    };
    (pk, sk)
}

impl SecretKey {
    /// Current epoch pointer.
    pub fn epoch(&self) -> u64 {
        self.epoch
    }

    /// Tree height; the key covers epochs `[0, 2^height)`.
    pub fn height(&self) -> u8 {
        self.height
    }

    /// **Key update (ratchet).** Advance to the next epoch, destroying the state
    /// needed to recompute the current (and any earlier) epoch's secrets. Returns
    /// `false` and does nothing if the key is exhausted (`epoch + 1 == 2^height`).
    pub fn update(&mut self) -> bool {
        let capacity = 1u64 << self.height;
        if self.epoch + 1 >= capacity {
            return false;
        }
        self.st = advance(&self.st);
        self.epoch += 1;
        true
    }

    /// **Eval.** Produce `(y, π)` for `epoch`. Forward-secure: `epoch` must be
    /// `>= self.epoch` (past epochs are destroyed) and `< 2^height`. Does not
    /// mutate the key — it forward-walks a *copy* of the chain state.
    pub fn eval(&self, epoch: u64) -> Result<(Output, Proof), EvalError> {
        let capacity = 1u64 << self.height;
        if epoch >= capacity {
            return Err(EvalError::EpochOutOfRange {
                requested: epoch,
                capacity,
            });
        }
        if epoch < self.epoch {
            return Err(EvalError::EpochExpired {
                current: self.epoch,
                requested: epoch,
            });
        }
        // Forward-walk (non-mutating) from the current state to the target epoch.
        let mut st = self.st;
        for _ in self.epoch..epoch {
            st = advance(&st);
        }
        let (y, r) = derive_epoch(&st);
        let path = self.tree.auth_path(epoch);
        Ok((y, Proof { r, path }))
    }
}

/// **Verify.** Check that `(y, π)` is the genuine VRF output for `epoch` under
/// `pk`: recompute the leaf and confirm the Merkle path reaches `pk.root`. Uses
/// only public data — no secret key.
///
/// UNIQUENESS: for a fixed `pk` and `epoch`, at most one `y` can pass this check
/// (a second would force a blake3 collision — see the module docs).
pub fn verify(pk: &PublicKey, epoch: u64, y: &Output, proof: &Proof) -> bool {
    let leaf = hash_leaf(epoch, y, &proof.r);
    verify_path(&pk.root, pk.height, epoch, &leaf, &proof.path)
}
