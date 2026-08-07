//! The Multiparty BFV scheme, as described by Christian Mouchet et. al.
//! in [Multiparty Homomorphic Encryption from Ring-Learning-with-Errors](https://eprint.iacr.org/2020/304.pdf).

mod aggregate;
mod crp;
mod public_key_gen;
mod public_key_switch;
mod relin_key_gen;
pub mod round;
mod secret_key_switch;
/// DREGG ADDITIVE SEAM: a canonical wire codec for [`RelinKeyShare`], so the
/// relinearization ceremony can run between SEPARATE PROCESSES. Adds no
/// cryptography — see the module docs.
#[cfg(feature = "mbfv-share-codec")]
mod share_codec;

pub use aggregate::{Aggregate, AggregateIter};
pub use crp::CommonRandomPoly;
pub use public_key_gen::PublicKeyShare;
pub use public_key_switch::PublicKeySwitchShare;
pub use relin_key_gen::{RelinKeyGenerator, RelinKeyShare};
pub use secret_key_switch::{DecryptionShare, SecretKeySwitchShare};
