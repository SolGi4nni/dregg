//! The proven credential core — attenuable, third-party-caveated,
//! offline-verifiable authorization tokens whose semantics are the
//! machine-checked ones in `metatheory/Dregg2/`.
//!
//! Chain-independent: this module depends on types + ed25519 + blake3 (and
//! postcard/base64 for the wire form) — no cell, no turn, no node, no circuit.
//!
//! ## The one API shape: granted ⊆ held
//!
//! A [`Credential`] is minted by a [`RootKey`] with caveats, narrowed by
//! [`Credential::attenuate`] (append caveats — the ONLY mutation), and decided
//! by [`Credential::verify`] against a caller-supplied [`Context`] — offline,
//! with nothing but the issuer's [`PublicKey`]. Widening is inexpressible:
//! no API removes a caveat, and the signature chain plus the
//! proof-of-possession check make removal unforgeable on the wire.
//!
//! ## Caveat ↔ Lean correspondence
//!
//! | here | Lean (`metatheory/Dregg2/…`) | the proved fact |
//! |---|---|---|
//! | [`Credential`] (caveats, meet) | `Authority/Caveat.lean` `Token`, `Token.admits` | admit = ALL caveats hold, fail-closed |
//! | [`Credential::attenuate`] | `Token.attenuate`, `attenuate_narrows`, `attenuate_subset` | appending can only shrink the admitted set |
//! | the ed25519 block chain | `Authority/BiscuitGraph.lean` | offline attenuation; forged/stripped blocks rejected |
//! | offline public-key verify | `Authority/Caveat.lean` `TokenKind.biscuit`, `biscuit_crossvat` | public-key tokens verify cross-vat |
//! | [`Caveat::FirstParty`] | `Caveat.local` | local predicate gate |
//! | [`Caveat::ThirdParty`] | `Caveat.thirdParty` | suspends on a gateway's discharge |
//! | [`Discharge`] + binding | `Authority/MacaroonDischarge.lean` `Discharge`, `bindTo`, `verifyDischarge` | discharge is its own signed object, bound to ONE credential |
//! | unbound rejection | `unbound_discharge_rejected` | fail-closed, unconditionally |
//! | bound-elsewhere rejection | `binding_not_replayable_to_other_root` | no cross-credential replay |
//! | [`Pred::True`]/[`Pred::False`] | `Exec/PredAlgebra.lean` `Pred.tt`/`Pred.ff` | top/bottom of the algebra |
//! | [`Pred::AllOf`]/[`Pred::AnyOf`]/[`Pred::Not`] | `Pred.allOf`/`anyOf`/`not` | Boolean algebra; `anyOf [] = false` (fail-closed) |
//! | [`Pred::AttrEq`] | `Exec/Program.lean` `SimpleConstraint.fieldEquals` | equality atom |
//! | [`Pred::AttrPrefix`] | `SimpleConstraint.prefixOf`, `evalSimple_prefixOf_iff` | prefix-containment atom |
//! | [`Pred::NotBefore`] | `Authority/TemporalAlgebra.lean` `TemporalAtom.afterHeight` | vesting gate, upward-closed |
//! | [`Pred::NotAfter`] | `TemporalAtom.beforeHeight` | expiry gate, downward-closed |
//! | [`Pred::Within`] | `TemporalAtom.withinWindow`, `withinWindow_eq_after_and_before` | window = meet of the two gates |
//! | [`Context`] | the `Ctx` binding-site of `Authority/Caveat.lean` | caveats evaluate against caller-supplied facts |
//!
//! ## The 60-second shape
//!
//! ```
//! use dregg_auth::credential::{Caveat, Context, Pred, RootKey};
//!
//! let root = RootKey::generate();
//!
//! // Mint: may use the `read` tool, until clock 2_000.
//! let cred = root.mint([
//!     Caveat::FirstParty(Pred::AttrEq { key: "tool".into(), value: "read".into() }),
//!     Caveat::FirstParty(Pred::NotAfter { at: 2_000 }),
//! ]);
//!
//! // Attenuate before handing to a sub-agent: tighter expiry. Never wider.
//! let narrowed = cred.attenuate([Caveat::FirstParty(Pred::NotAfter { at: 1_500 })]);
//! let encoded = narrowed.encode(); // `dga1_…`, header-safe
//!
//! // Verify offline: only the public key + the request facts.
//! let presented = dregg_auth::credential::Credential::decode(&encoded).unwrap();
//! let ctx = Context::new().at(1_400).attr("tool", "read");
//! assert!(presented.verify(&root.public(), &ctx).is_ok());
//!
//! // Past the attenuated expiry: refused, with the violated terms named.
//! let late = Context::new().at(1_600).attr("tool", "read");
//! assert!(presented.verify(&root.public(), &late).is_err());
//! ```

mod caveat;
mod chain;
mod pq;
mod pred;
mod wire;

pub use caveat::{Caveat, Context};
pub use chain::{
    Credential, Discharge, GatewayKey, HybridRootPublic, KeyError, PublicKey, Refusal, RootKey,
};
pub use pred::{Pred, Unbound};
pub use wire::{CREDENTIAL_PREFIX, DISCHARGE_PREFIX, WireError};

/// Lowercase hex of a 32-byte key (public helper for product surfaces that
/// persist root seeds / public keys as hex — e.g. [`crate::policy`]).
pub fn hex_pub(bytes: &[u8; 32]) -> String {
    hex(bytes)
}

/// Parse exactly 32 bytes of hex (public helper for product surfaces — e.g.
/// [`crate::policy::Policy::from_secret_hex`]). Errors on any non-64-hex input.
pub fn unhex32_pub(s: &str) -> Result<[u8; 32], KeyError> {
    unhex32(s)
}

/// Lowercase hex of arbitrary bytes (display / explain helper — no dep).
pub(crate) fn hex(bytes: &[u8]) -> String {
    const LUT: &[u8; 16] = b"0123456789abcdef";
    let mut s = String::with_capacity(bytes.len() * 2);
    for &b in bytes {
        s.push(LUT[(b >> 4) as usize] as char);
        s.push(LUT[(b & 0x0f) as usize] as char);
    }
    s
}

/// Parse exactly 32 bytes of hex.
pub(crate) fn unhex32(s: &str) -> Result<[u8; 32], KeyError> {
    if s.len() != 64 || !s.is_ascii() {
        return Err(KeyError("expected 64 hex characters".into()));
    }
    let mut out = [0u8; 32];
    for (i, chunk) in s.as_bytes().chunks_exact(2).enumerate() {
        let hi = (chunk[0] as char)
            .to_digit(16)
            .ok_or_else(|| KeyError("non-hex character".into()))?;
        let lo = (chunk[1] as char)
            .to_digit(16)
            .ok_or_else(|| KeyError("non-hex character".into()))?;
        out[i] = ((hi << 4) | lo) as u8;
    }
    Ok(out)
}
