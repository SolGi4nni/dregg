//! # crypto-traccoon — a correctness-first REFERENCE implementation of
//! **Threshold Raccoon (TRaccoon)**, the 3-round lattice threshold signature.
//!
//! TRaccoon (Rafael del Pino, Thomas Espitau, Shuichi Katsumata, Mary Maller,
//! Fabrice Mouhartem, Thomas Prest, Markku-Juhani Saarinen, Kaoru Takemure —
//! *Threshold Raccoon: Practical Threshold Signatures from Standard Lattice
//! Assumptions*, **EUROCRYPT 2024**, <https://eprint.iacr.org/2024/184>) is a
//! `T`-of-`N` threshold signature over `R_q = ℤ_q[X]/(Xⁿ+1)` from **MLWE +
//! MSIS** in the ROM. It is "Schnorr over lattices" (Raccoon) lifted to the
//! threshold setting FROST/Sparkle-style, with the lattice-specific twist that
//! partial responses must be **masked** — blinded with fresh one-time additive
//! masks — to resist the attack that would otherwise recover a signer's share
//! from its partial signatures. Reference costs from the paper: **~13 KiB**
//! signature, **~40 KiB** communication per user, thresholds up to ~1024.
//!
//! This crate implements the protocol as presented in the authors' NIST Fifth
//! PQC Standardization Conference talk (the "Second attempt / Threshold
//! Raccoon" slide), mapped symbol-for-symbol in [`threshold`].
//!
//! ## Why THREE rounds (the key contrast with a 2-round scheme like Tanuki)
//!
//! A naive Raccoon transpose (Sparkle-style) is:
//! *round 1* commit `com_i = H_com(w_i,…)`; *round 2* reveal `w_i` and send the
//! response `z_i` together. TRaccoon **splits reveal and respond into two
//! rounds**, giving 1 (commit) + 1 (reveal) + 1 (respond):
//!
//! * **Round 1 — commit** closes **rushing / ROS**. Committing to `w_i` before
//!   anyone opens theirs prevents a rushing adversary from choosing its nonce as
//!   a function of the honest nonces — the ROS attack [DEF+19, BLL+22] that
//!   breaks the naive transpose. (This is also why Schnorr threshold schemes
//!   like Sparkle commit first.)
//! * **Round 2 — reveal** closes **binding**: openings are checked, so a party
//!   that changes its nonce after seeing the others is caught
//!   ([`threshold::check_openings`]).
//! * **Round 3 — respond** is where the **masking** happens. Only after the
//!   challenge `c` is fixed does each party emit the *masked* partial
//!   `z_i = r_i + c·λ_{i,S}·s_i + m*_i`. Emitting it in the same round as the
//!   reveal (2-round) is exactly what the masking + separate round is designed
//!   to make safe against the share-recovery attack; TRaccoon takes the
//!   conservative 3-round route with a clean proof.
//!
//! **The trade-off (3-round static vs. 2-round):** TRaccoon is a **3-round**
//! scheme proven **TS-UF** secure under **static** corruption in the ROM
//! (MLWE + MSIS; the Gaussian masks are argued via **Hint-MLWE → MLWE**
//! [KLSS23]). Two-round lattice threshold signatures exist and are the sibling
//! reference in this tree ([EKT24] "algebraic one-more LWE" + Ringtail, realized
//! in `crypto-tanuki`); they buy a round at the cost of a stronger/less-standard
//! assumption or extra machinery. The third round is what lets TRaccoon rest on
//! the *standard* lattice assumptions named in its title.
//!
//! ## Adaptive security & follow-up: "Unmasking TRaccoon" (2025)
//!
//! The EUROCRYPT-2024 paper proves security under **static** corruption (the
//! adversary fixes the corrupted set up front). Two follow-up concerns:
//!
//! * **Identifiable abort.** The original protocol aborts on misbehavior without
//!   pinning the culprit. *Unmasking TRaccoon: A Lattice-Based Threshold
//!   Signature with an Efficient Identifiable Abort Protocol* (CRYPTO 2025,
//!   <https://eprint.iacr.org/2025/849>) gives **TRaccoon-IA**, adding an
//!   efficient identifiable-abort protocol that names malicious signers when a
//!   session fails.
//! * **Adaptive corruption** (adversary corrupts parties mid-protocol) was left
//!   as a subtlety by the original static proof and is the harder target of the
//!   follow-up line of work. **FLAG:** the task brief attributes the *adaptive*
//!   closure to "Unmasking TRaccoon (2025)"; the paper we could verify
//!   (2025/849) is specifically about **identifiable abort**. We cite what we
//!   verified and flag the adaptive-security attribution as one to confirm
//!   against the exact follow-up the brief intends — we do not assert an
//!   adaptive-security result we did not read.
//!
//! Either way, **this crate implements the base EUROCRYPT-2024 static-corruption
//! TRaccoon** (no identifiable abort, no adaptive-security enhancement).
//!
//! ## HONEST BOUNDARY — what this crate is and is NOT
//!
//! This is a **correctness reference**: every structural feature of TRaccoon's
//! three rounds is present and exercised on concrete `R_q` numbers, so the
//! scheme's shape can be studied and benchmarked against `crypto-hermine` and
//! `crypto-tanuki`. It is NOT deployment-grade and must never sign live.
//!
//! * **The TS-UF security proof is CITED, not re-proven here.** TRaccoon's
//!   unforgeability (game-based TS-UF in the ROM under MLWE + MSIS, masks via
//!   Hint-MLWE → MLWE) is established in [dPKMMPST24] and refined by the
//!   follow-ups above. Nothing here re-derives it; the tests witness
//!   **correctness and structural binding**, not security.
//! * **Reference parameters** ([`threshold::Params::reference`]): `n=256`,
//!   `q=8380417` (Dilithium prime), `k=ℓ=4` (module `d=8`), `N=5`, `T=3`,
//!   challenge weight `ω=19`, half-widths `η_s=η_r=2`. Illustrative, NOT the
//!   parameter-searched NIST-grade sets (which target the ~13 KiB / 40 KiB
//!   costs and the real security level).
//! * **Acceptance bound** `B = z_bound` is calibrated so honest signatures pass
//!   with wide margin and garbage/reused-mask responses fail — it is NOT the
//!   security-derived `B`.
//! * **Reference samplers**: nonces/secrets use a biased, non-constant-time
//!   `mod (2η+1)` sampler over a blake3 XOF; the one-time masks are drawn
//!   **UNIFORM** over `R_q` (perfect statistical hiding — the simplest correct
//!   choice). Production TRaccoon uses discrete-**Gaussian** masks whose
//!   exactness feeds the **Hint-MLWE → MLWE** reduction; the uniform choice here
//!   is faithful to *cancellation and hiding* but not to that reduction. See
//!   [`hash`].
//! * **Trusted-dealer KeyGen + mask setup**: a dealer samples `sk`, Shamir-shares
//!   it, and hands all signers a common `mask_master` from which pairwise
//!   symmetric seeds are derived. Real TRaccoon distributes only a party's own
//!   pairwise keys (or runs a DKG). See [`threshold::SignerKey`].
//! * **No rounding, no hint — and that is faithful.** Because `vk = [A|I]·sk`
//!   folds the MLWE error into the secret, verification closes exactly
//!   (`[A|I]·z − c·t = w`); TRaccoon needs no Dilithium-style hint. (Contrast
//!   `crypto-tanuki`, which is a rounded scheme with a hint.)
//! * **Not constant-time; no zeroization of secrets.**
//!
//! ## FLAGGED / not implemented
//!
//! * Discrete-Gaussian masks + the Hint-MLWE parameter regime (uniform masks
//!   used instead — correct, but not the proof's exact distribution).
//! * NIST-grade parameters, bit-packed serialization (the ~13 KiB figure), and
//!   the security-derived acceptance bound.
//! * Identifiable abort (TRaccoon-IA) and any adaptive-security enhancement.
//! * A real DKG / distributed mask setup (trusted dealer used here).
//! * The adaptive-security attribution in the brief — see the note above.
//!
//! ## Module map
//!
//! * [`ring`] — `R_q` with exact NTT/schoolbook multiplication (no rounding).
//! * [`linalg`] — `PolyVec` / `PolyMatrix`, the augmented `Â = [A|I]`.
//! * [`shamir`] — Shamir sharing of `sk` over `R_q`, Lagrange reconstruction.
//! * [`hash`] — the oracles `H_com`, `H` (challenge), and the mask cells.
//! * [`threshold`] — KeyGen, the 3-round Sign ceremony, Verify.

pub mod hash;
pub mod linalg;
pub mod ring;
pub mod shamir;
pub mod threshold;
