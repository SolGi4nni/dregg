//! DREGG ADDITIVE SEAM — a canonical wire codec for [`RelinKeyShare`].
//!
//! # Why this file exists
//!
//! Upstream `fhe` 0.1.1 makes the multiparty relinearization share COMPLETELY
//! opaque: `RelinKeyShare`'s `h0`/`h1` are `pub(crate)`, there is no accessor,
//! and no `Serialize`/`Deserialize` impl anywhere in `mbfv`. That is fine for
//! the documented usage (all parties in one process, shares moved as typed
//! values), and it is a hard wall for a committee whose parties are SEPARATE
//! PROCESSES: the share can neither be read out of the party nor rebuilt at the
//! coordinator, so the ceremony cannot cross a socket at all.
//!
//! This module is that wall removed and NOTHING ELSE. It adds no cryptography:
//! every polynomial goes over the wire through `Poly`'s OWN public, exact
//! round-trip codec (`fhe_math::rq::Poly: Serialize + DeserializeWithContext`,
//! which preserves `Representation` including `NttShoup`), and the reassembled
//! share is the same struct the in-process path builds. The protocol steps in
//! `relin_key_gen.rs` are byte-identical to upstream.
//!
//! # What the decoder refuses
//!
//! - a wrong or absent magic;
//! - a share whose round tag is not the round the caller asked for (an R1 share
//!   replayed where an R2 share belongs is the confusion this tag exists for);
//! - a share whose degree / modulus count disagrees with the parameters it is
//!   being decoded against;
//! - a poly-vector arity that is not exactly the ciphertext modulus count;
//! - any polynomial that does not parse under the level-0 context;
//! - an R2 share with no carried round-1 aggregate, or an R1 / R1Aggregated
//!   share that carries one;
//! - any trailing byte.
//!
//! Lengths are read before allocation and bounded by the parameters, so a
//! hostile length cannot force a large allocation.

use std::marker::PhantomData;
use std::sync::Arc;

use fhe_math::rq::Poly;
use fhe_traits::{DeserializeWithContext, Serialize as PolySerialize};

use crate::bfv::BfvParameters;
use crate::errors::{Error, Result};

use super::round::{R1Aggregated, Round, RoundTag};
use super::RelinKeyShare;

/// Wire magic. A change to the encoding below changes this.
const SHARE_MAGIC: &[u8; 8] = b"FHRKv001";

fn put_u64(out: &mut Vec<u8>, value: usize) {
    out.extend_from_slice(&(value as u64).to_le_bytes());
}

fn put_blob(out: &mut Vec<u8>, blob: &[u8]) {
    put_u64(out, blob.len());
    out.extend_from_slice(blob);
}

fn malformed(what: &'static str) -> Error {
    Error::DefaultError(format!("relin key share: {what}"))
}

/// A strict forward-only reader. Every `take` is bounds-checked before it can
/// index, and `finish` refuses trailing bytes.
struct Reader<'a> {
    bytes: &'a [u8],
    at: usize,
}

impl<'a> Reader<'a> {
    fn new(bytes: &'a [u8]) -> Self {
        Self { bytes, at: 0 }
    }

    fn take(&mut self, len: usize) -> Result<&'a [u8]> {
        let end = self
            .at
            .checked_add(len)
            .filter(|&end| end <= self.bytes.len())
            .ok_or_else(|| malformed("message truncated"))?;
        let out = &self.bytes[self.at..end];
        self.at = end;
        Ok(out)
    }

    fn u8(&mut self) -> Result<u8> {
        Ok(self.take(1)?[0])
    }

    fn u64(&mut self) -> Result<usize> {
        let raw = self.take(8)?;
        let value = u64::from_le_bytes(raw.try_into().expect("checked to be eight bytes"));
        usize::try_from(value).map_err(|_| malformed("length overflow"))
    }

    /// A length-prefixed blob. The length is validated against the REMAINING
    /// input before any allocation, so a hostile length cannot reserve memory.
    fn blob(&mut self) -> Result<&'a [u8]> {
        let len = self.u64()?;
        self.take(len)
    }

    fn finish(self) -> Result<()> {
        if self.at == self.bytes.len() {
            Ok(())
        } else {
            Err(malformed("trailing bytes"))
        }
    }
}

fn encode_polys(out: &mut Vec<u8>, polys: &[Poly]) {
    put_u64(out, polys.len());
    for poly in polys {
        put_blob(out, &poly.to_bytes());
    }
}

fn decode_polys(reader: &mut Reader<'_>, par: &Arc<BfvParameters>) -> Result<Box<[Poly]>> {
    let ctx = par.context_at_level(0)?;
    let expected = ctx.moduli().len();
    let count = reader.u64()?;
    if count != expected {
        return Err(malformed(
            "polynomial vector arity is not the ciphertext modulus count",
        ));
    }
    let mut polys = Vec::with_capacity(count);
    for _ in 0..count {
        let blob = reader.blob()?;
        polys.push(Poly::from_bytes(blob, ctx).map_err(Error::MathError)?);
    }
    Ok(polys.into_boxed_slice())
}

fn encode_share<R: RoundTag>(out: &mut Vec<u8>, share: &RelinKeyShare<R>) {
    out.extend_from_slice(SHARE_MAGIC);
    out.push(R::TAG);
    put_u64(out, share.par.degree());
    put_u64(out, share.par.moduli().len());
    encode_polys(out, &share.h0);
    encode_polys(out, &share.h1);
    match &share.last_round {
        None => out.push(0),
        Some(last) => {
            out.push(1);
            let mut inner = Vec::new();
            encode_share(&mut inner, last.as_ref());
            put_blob(out, &inner);
        }
    }
}

fn decode_share<R: RoundTag>(
    reader: &mut Reader<'_>,
    par: &Arc<BfvParameters>,
) -> Result<RelinKeyShare<R>> {
    if reader.take(SHARE_MAGIC.len())? != SHARE_MAGIC.as_slice() {
        return Err(malformed("wrong magic"));
    }
    let tag = reader.u8()?;
    if tag != R::TAG {
        return Err(malformed("share is from a different protocol round"));
    }
    if reader.u64()? != par.degree() {
        return Err(malformed("degree disagrees with the parameters"));
    }
    if reader.u64()? != par.moduli().len() {
        return Err(malformed("modulus count disagrees with the parameters"));
    }
    let h0 = decode_polys(reader, par)?;
    let h1 = decode_polys(reader, par)?;
    let last_round = match reader.u8()? {
        0 => None,
        1 => {
            let inner = reader.blob()?;
            let mut inner_reader = Reader::new(inner);
            let aggregated: RelinKeyShare<R1Aggregated> = decode_share(&mut inner_reader, par)?;
            inner_reader.finish()?;
            Some(Arc::new(aggregated))
        }
        _ => return Err(malformed("round-1-aggregate presence flag is not 0 or 1")),
    };
    // The round-2 share is the ONLY one that carries the round-1 aggregate, and
    // it cannot be assembled into a key without it (`RelinearizationKey::
    // from_shares` errors on a missing one). Pin the shape both ways so neither
    // a stripped nor a smuggled aggregate parses.
    if (R::TAG == <super::round::R2 as RoundTag>::TAG) != last_round.is_some() {
        return Err(malformed(
            "round-1-aggregate presence does not match the round",
        ));
    }
    Ok(RelinKeyShare {
        par: par.clone(),
        h0,
        h1,
        last_round,
        _phantom_data: PhantomData,
    })
}

impl<R: RoundTag> RelinKeyShare<R>
where
    R: Round,
{
    /// Canonical wire form of this share.
    ///
    /// The bytes carry only the PUBLIC protocol values (`h0`, `h1`, and for a
    /// round-2 share the round-1 aggregate it was computed against). The
    /// generator's secret-dependent ephemeral `u` and the party's secret key are
    /// not reachable from here and never enter the encoding.
    pub fn to_canonical_bytes(&self) -> Vec<u8> {
        let mut out = Vec::new();
        encode_share(&mut out, self);
        out
    }

    /// Rebuild a share from [`to_canonical_bytes`](Self::to_canonical_bytes).
    ///
    /// Fails closed on every mismatch listed in the module docs. `par` must be
    /// the parameters the share was produced under; a share encoded under
    /// different ones is refused rather than reinterpreted.
    pub fn from_canonical_bytes(bytes: &[u8], par: &Arc<BfvParameters>) -> Result<Self> {
        let mut reader = Reader::new(bytes);
        let share = decode_share(&mut reader, par)?;
        reader.finish()?;
        Ok(share)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::bfv::SecretKey;
    use crate::mbfv::round::{R1, R2};
    use crate::mbfv::{Aggregate, CommonRandomPoly, RelinKeyGenerator};
    use rand::rng;

    fn params() -> Arc<BfvParameters> {
        BfvParameters::default_arc(3, 16)
    }

    #[test]
    fn a_round_one_share_round_trips_exactly() {
        let mut rng = rng();
        let par = params();
        let sk = SecretKey::random(&par, &mut rng);
        let crp = CommonRandomPoly::new_vec(&par, &mut rng).unwrap();
        let generator = RelinKeyGenerator::new(&sk, &crp, &mut rng).unwrap();
        let share = generator.round_1(&mut rng).unwrap();

        let bytes = share.to_canonical_bytes();
        let back = RelinKeyShare::<R1>::from_canonical_bytes(&bytes, &par).unwrap();
        assert_eq!(share, back, "the decoded share is not the encoded one");
        assert_eq!(
            bytes,
            back.to_canonical_bytes(),
            "re-encoding is not stable"
        );
    }

    #[test]
    fn a_round_two_share_round_trips_with_its_carried_aggregate() {
        let mut rng = rng();
        let par = params();
        let sk = SecretKey::random(&par, &mut rng);
        let crp = CommonRandomPoly::new_vec(&par, &mut rng).unwrap();
        let generator = RelinKeyGenerator::new(&sk, &crp, &mut rng).unwrap();
        let r1 = generator.round_1(&mut rng).unwrap();
        let aggregated = Arc::new(RelinKeyShare::<R1Aggregated>::from_shares([r1]).unwrap());
        let r2 = generator.round_2(&aggregated, &mut rng).unwrap();

        let bytes = r2.to_canonical_bytes();
        let back = RelinKeyShare::<R2>::from_canonical_bytes(&bytes, &par).unwrap();
        assert_eq!(r2, back);
    }

    #[test]
    fn a_round_one_share_is_refused_where_round_two_is_expected() {
        let mut rng = rng();
        let par = params();
        let sk = SecretKey::random(&par, &mut rng);
        let crp = CommonRandomPoly::new_vec(&par, &mut rng).unwrap();
        let generator = RelinKeyGenerator::new(&sk, &crp, &mut rng).unwrap();
        let bytes = generator.round_1(&mut rng).unwrap().to_canonical_bytes();

        assert!(
            RelinKeyShare::<R2>::from_canonical_bytes(&bytes, &par).is_err(),
            "a round-1 share parsed as a round-2 share"
        );
    }

    #[test]
    fn a_truncated_or_extended_share_is_refused() {
        let mut rng = rng();
        let par = params();
        let sk = SecretKey::random(&par, &mut rng);
        let crp = CommonRandomPoly::new_vec(&par, &mut rng).unwrap();
        let generator = RelinKeyGenerator::new(&sk, &crp, &mut rng).unwrap();
        let bytes = generator.round_1(&mut rng).unwrap().to_canonical_bytes();

        assert!(
            RelinKeyShare::<R1>::from_canonical_bytes(&bytes[..bytes.len() - 1], &par).is_err()
        );
        let mut extended = bytes.clone();
        extended.push(0);
        assert!(RelinKeyShare::<R1>::from_canonical_bytes(&extended, &par).is_err());
        let mut wrong_magic = bytes;
        wrong_magic[0] ^= 0xff;
        assert!(RelinKeyShare::<R1>::from_canonical_bytes(&wrong_magic, &par).is_err());
    }
}
