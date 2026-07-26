//! The out-of-band SUBMISSION half of the private Dark Bazaar clearing.
//!
//! Everything else in this crate's private-Bazaar stack CONSUMES a
//! [`PrivateClearingReceipt`]: the authenticated source, the durable spool, the
//! listener, the supervisor. The producer —
//! `PrivateBazaarLiveDeployment::settle_private_clearing_verified` — exists and
//! runs the real Lean-descriptor relation, but until this module nothing in a
//! deployed process could hand it a book. The supervisor polled a source only a
//! test could ever fill.
//!
//! This is that missing half: a deployment-custodied, append-only, checksummed
//! queue of sealed ingress books, drained by the production supervisor loop.
//!
//! # Where the scale gate lives
//!
//! [`PrivateSealedIngressBook::new`] is the gate, and it is a TYPE gate: the
//! only way to hold that value is to have passed it. This module never bypasses
//! it. In particular the DECODER re-runs it on every record it reads, so a
//! hostile rewrite of the queue file — even one that recomputes the record
//! checksum — cannot widen the proved `N=4,K=4` family. The record deliberately
//! has room to EXPRESS an out-of-family book (`INGRESS_BID_SLOTS` is one more
//! than `PROVEN_MAX_SEALED_BIDS`) so that refusal is exercised rather than being
//! unrepresentable and therefore untested.
//!
//! # WHO bid is durable here
//!
//! The worker-private commitment binding in `dreggnet-market` pins the canonical
//! ORDER records — `(side, qty, limit)` — because that is what the circuit
//! commits to. Bidder identity is not in the relation at all. So the binding
//! alone cannot tell `{(alice,2),(bob,3)}` from `{(mallory,2),(eve,3)}`, while
//! the WINNER, and therefore the exact game consequence, differs. This queue
//! carries the identities, and the roster gate below refuses a bidder the
//! deployment's immutable policy does not name, so a restart replays the exact
//! submitted book rather than any book with the same multiset of limits.
//!
//! # Confidentiality boundary, stated plainly
//!
//! Bid limits are secrets and this file holds them in the clear, mode `0600`,
//! under the same deployment authority directory that already holds the
//! commitment blind. It is exactly as private as that blind: an operator with
//! the authority directory sees the book. This is the Tier-1 operator-visible
//! boundary the private clearing already documents, not a new one — but it is a
//! real one, and a submission stays readable until its market has settled.

use std::fs::{self, File};
use std::io::{Read, Seek, SeekFrom, Write};
use std::path::PathBuf;

use dreggnet_market::private_clearing::{
    PROVEN_MAX_SEALED_BIDS, PROVEN_PRICE_BUCKETS, PrivateClearingError, PrivateSealedIngressBook,
};
use dreggnet_offerings::DreggIdentity;

use crate::private_bazaar_live::PrivateBazaarLiveDeployment;
use crate::private_bazaar_worker::{
    PrivateBazaarSpoolScope, PrivateBazaarWorkerError, atomic_replace, checksum,
    ensure_private_directory, private_options, secure_private_file_handle, sync_directory,
    validate_private_file_handle,
};

const INGRESS_FILE_NAME: &str = "sealed-ingress-v1.queue";
const INGRESS_CURSOR_FILE_NAME: &str = "sealed-ingress-v1.cursor";
const INGRESS_MAGIC: &[u8; 8] = b"DBIQ0001";
const INGRESS_CURSOR_MAGIC: &[u8; 8] = b"DBIC0001";
const INGRESS_DOMAIN: &str = "dregg.private-bazaar-sealed-ingress.v1";
const INGRESS_CURSOR_DOMAIN: &str = "dregg.private-bazaar-sealed-ingress-cursor.v1";

/// A bidder handle longer than this cannot be submitted. The deployment roster
/// gate below is the real bound; this is the record's fixed slot width.
const MAX_INGRESS_ACTOR_BYTES: usize = 128;

/// One slot MORE than the proved family admits. See the module note: the
/// refusal of an out-of-family durable record must be reachable to be tested.
const INGRESS_BID_SLOTS: usize = PROVEN_MAX_SEALED_BIDS + 1;

const INGRESS_BID_SLOT_LEN: usize = 2 + MAX_INGRESS_ACTOR_BYTES + 8;
const INGRESS_RECORD_LEN: usize = 8 // magic/version
    + 8 // 1-based sequence
    + 32 // checksum of the physical predecessor record
    + 32 // deployment id
    + 32 // executor federation
    + 32 // policy id
    + 8 // deterministic hosted session seed
    + 1 // commitment-blinding presence flag
    + 32 // commitment blinding limbs
    + 1 // sealed bid count
    + (INGRESS_BID_SLOTS * INGRESS_BID_SLOT_LEN)
    + 32; // record checksum / next-record chain anchor
const INGRESS_CURSOR_LEN: usize = 8 + 8 + 32;

/// The most submissions one supervisor tick will settle. Each one mints a real
/// hiding proof, so the loop stays responsive to shutdown.
pub(crate) const MAX_INGRESS_SETTLES_PER_TICK: usize = 1;

/// Why a sealed ingress submission was refused. Every variant names the exact
/// limit that was exceeded; none of them leaves a partially applied book.
#[derive(Debug)]
pub enum PrivateBazaarIngressError {
    /// The book is outside the proved `N=4,K=4` family. Carries the exact
    /// construction refusal, which names the count or the price bucket.
    OutsideProvenFamily(PrivateClearingError),
    /// A bidder the deployment's immutable policy roster does not name. The
    /// ordinal, not the handle, is reported: a refusal must not leak a private
    /// bidder identity into an operator log.
    BidderNotInDeploymentRoster { ordinal: usize },
    /// The same roster member submitted twice in one book. The live auction
    /// would seat both, and the tie policy would silently pick one.
    DuplicateBidder { ordinal: usize },
    /// The handle does not fit the record's fixed slot.
    BidderHandleTooLong { ordinal: usize, limit: usize },
    /// Durable queue transport refusal.
    Queue(PrivateBazaarWorkerError),
}

impl std::fmt::Display for PrivateBazaarIngressError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::OutsideProvenFamily(PrivateClearingError::TooManyBids(found)) => write!(
                f,
                "private ingress refused: {found} sealed bids exceeds PROVEN_MAX_SEALED_BIDS = \
                 {PROVEN_MAX_SEALED_BIDS}, the largest book the emitted N=4,K=4 descriptor proves"
            ),
            Self::OutsideProvenFamily(PrivateClearingError::PriceOutsideFixedFamily(limit)) => {
                write!(
                    f,
                    "private ingress refused: bid limit {limit} is outside the proved price family \
                     0..{PROVEN_PRICE_BUCKETS}"
                )
            }
            Self::OutsideProvenFamily(PrivateClearingError::NoBids) => write!(
                f,
                "private ingress refused: an empty book has no clearing to prove"
            ),
            Self::OutsideProvenFamily(other) => {
                write!(f, "private ingress refused: {other:?}")
            }
            Self::BidderNotInDeploymentRoster { ordinal } => write!(
                f,
                "private ingress refused: sealed bid {ordinal} names a bidder outside the \
                 deployment's immutable policy roster"
            ),
            Self::DuplicateBidder { ordinal } => write!(
                f,
                "private ingress refused: sealed bid {ordinal} repeats a roster member already \
                 bidding in this book"
            ),
            Self::BidderHandleTooLong { ordinal, limit } => write!(
                f,
                "private ingress refused: sealed bid {ordinal} carries a handle longer than the \
                 {limit}-byte ingress slot"
            ),
            Self::Queue(error) => write!(f, "private ingress refused: {error:?}"),
        }
    }
}

impl std::error::Error for PrivateBazaarIngressError {}

impl From<PrivateBazaarWorkerError> for PrivateBazaarIngressError {
    fn from(error: PrivateBazaarWorkerError) -> Self {
        Self::Queue(error)
    }
}

/// Accepted submission evidence. It carries the queue position only; a caller
/// learns nothing it did not already supply.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct PrivateBazaarIngressSubmission {
    pub sequence: u64,
}

/// Operational progress of one supervisor drain. Counts only.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct PrivateBazaarIngressProgress {
    /// Submissions whose proof verified and whose executor SETTLE landed.
    pub settled: usize,
    /// Submissions found already terminal on the live market — the crash window
    /// between a landed settlement and its durable acknowledgement.
    pub already_terminal: usize,
    /// Submissions still queued after this drain.
    pub pending: u64,
}

/// One decoded, still-unsettled submission. Constructing it required the
/// [`PrivateSealedIngressBook`] gate to pass, so holding one is proof the book
/// is inside the proved family.
pub(crate) struct PendingSealedIngress {
    pub(crate) sequence: u64,
    pub(crate) session_seed: u64,
    pub(crate) book: PrivateSealedIngressBook,
    pub(crate) blinding: Option<[u32; 8]>,
}

/// Deployment-custodied append-only sealed-ingress queue.
///
/// The file is mode `0600`, chained by per-record checksums exactly like the
/// finalized-receipt spool, and scoped to one deployment/federation/policy so a
/// queue file cannot be moved between deployments.
pub struct PrivateBazaarSealedIngressQueue {
    path: PathBuf,
    cursor_path: PathBuf,
    root: PathBuf,
    scope: PrivateBazaarSpoolScope,
    roster: Vec<DreggIdentity>,
}

impl std::fmt::Debug for PrivateBazaarSealedIngressQueue {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("PrivateBazaarSealedIngressQueue")
            .field("path", &self.path)
            .field("books", &"<worker-private>")
            .finish()
    }
}

impl PrivateBazaarSealedIngressQueue {
    pub(crate) fn open(
        deployment: &PrivateBazaarLiveDeployment,
    ) -> Result<Self, PrivateBazaarWorkerError> {
        let root = deployment.private_ingress_root();
        fs::create_dir_all(&root)
            .map_err(|error| PrivateBazaarWorkerError::io("create sealed ingress queue", error))?;
        ensure_private_directory(&root)?;
        let root = fs::canonicalize(&root)
            .map_err(|error| PrivateBazaarWorkerError::io("pin sealed ingress directory", error))?;
        let queue = Self {
            path: root.join(INGRESS_FILE_NAME),
            cursor_path: root.join(INGRESS_CURSOR_FILE_NAME),
            root,
            scope: deployment.private_spool_scope(),
            roster: deployment
                .private_target_members()
                .into_iter()
                .map(|(actor, _)| actor)
                .collect(),
        };
        queue.validate_chain()?;
        Ok(queue)
    }

    /// THE PRODUCTION INGRESS. Accept one sealed book for one hosted market.
    ///
    /// Refusal order is load-bearing and every step happens BEFORE anything is
    /// written: the proved-family gate, the handle width, then the deployment
    /// roster. A refused submission leaves no durable trace and never reaches
    /// the executor board.
    pub fn submit(
        &mut self,
        session_seed: u64,
        bids: Vec<(DreggIdentity, i64)>,
        commitment_blinding: Option<[u32; 8]>,
    ) -> Result<PrivateBazaarIngressSubmission, PrivateBazaarIngressError> {
        let book = PrivateSealedIngressBook::new(bids)
            .map_err(PrivateBazaarIngressError::OutsideProvenFamily)?;
        self.validate_bidders(book.sealed_bids())?;

        let mut options = private_options();
        options.read(true).append(true).create(true);
        let mut file = options
            .open(&self.path)
            .map_err(|error| PrivateBazaarWorkerError::io("open sealed ingress queue", error))?;
        secure_private_file_handle(&file, &self.root).map_err(PrivateBazaarIngressError::Queue)?;
        // Two submitters must not interleave into one chained record stream: the
        // loser would append at a sequence the winner already used and wedge the
        // queue on a fork that nothing can repair.
        file.lock()
            .map_err(|error| PrivateBazaarWorkerError::io("lock sealed ingress queue", error))?;
        let appended = (|| {
            let count = self.record_count(&file)?;
            let sequence = count
                .checked_add(1)
                .ok_or(PrivateBazaarWorkerError::CursorOverflow)?;
            let previous = self.tail_checksum(&mut file, count)?;
            let bytes = encode_ingress_record(
                self.scope,
                previous,
                sequence,
                session_seed,
                &book,
                commitment_blinding,
            )?;
            file.write_all(&bytes).map_err(|error| {
                PrivateBazaarWorkerError::io("write sealed ingress record", error)
            })?;
            file.sync_all().map_err(|error| {
                PrivateBazaarWorkerError::io("sync sealed ingress record", error)
            })?;
            sync_directory(&self.root)?;
            Ok(sequence)
        })();
        let unlock = file
            .unlock()
            .map_err(|error| PrivateBazaarWorkerError::io("unlock sealed ingress queue", error));
        let sequence = match (appended, unlock) {
            (Ok(sequence), Ok(())) => sequence,
            (Err(error), _) | (Ok(_), Err(error)) => return Err(error.into()),
        };
        Ok(PrivateBazaarIngressSubmission { sequence })
    }

    /// Submissions accepted but not yet settled.
    pub fn pending(&self) -> Result<u64, PrivateBazaarWorkerError> {
        let Some(file) = self.open_queue()? else {
            return Ok(0);
        };
        Ok(self
            .record_count(&file)?
            .saturating_sub(self.read_cursor()?))
    }

    /// The next unsettled submission, read at its exact offset.
    ///
    /// Deliberately NOT a whole-file decode: this runs on every supervisor tick,
    /// and re-decoding (and re-gating) the entire history four times a second
    /// would make the queue quadratic in a deployment's lifetime traffic. The
    /// full historical chain is validated once, at [`Self::open`]. Each record
    /// read here still validates its own schema, checksum, scope, sequence, the
    /// link to its physical predecessor, and the proved-family type gate.
    pub(crate) fn next_pending(
        &self,
    ) -> Result<Option<PendingSealedIngress>, PrivateBazaarWorkerError> {
        let Some(mut file) = self.open_queue()? else {
            return Ok(None);
        };
        let count = self.record_count(&file)?;
        let index = self.read_cursor()?;
        if index >= count {
            return Ok(None);
        }
        let previous = self.tail_checksum(&mut file, index)?;
        let record = self.read_record(&mut file, index)?;
        if record.previous_checksum != previous {
            return Err(PrivateBazaarWorkerError::SpoolFork {
                expected: index
                    .checked_add(1)
                    .ok_or(PrivateBazaarWorkerError::CursorOverflow)?,
                found: record.pending.sequence,
            });
        }
        Ok(Some(record.pending))
    }

    pub(crate) fn acknowledge(&self, sequence: u64) -> Result<(), PrivateBazaarWorkerError> {
        let acknowledged = self.read_cursor()?;
        let expected = acknowledged
            .checked_add(1)
            .ok_or(PrivateBazaarWorkerError::CursorOverflow)?;
        if sequence != expected {
            return Err(PrivateBazaarWorkerError::NonContiguousCursor {
                expected,
                found: sequence,
            });
        }
        let mut bytes = Vec::with_capacity(INGRESS_CURSOR_LEN);
        bytes.extend_from_slice(INGRESS_CURSOR_MAGIC);
        bytes.extend_from_slice(&sequence.to_be_bytes());
        let sum = checksum(INGRESS_CURSOR_DOMAIN, &bytes);
        bytes.extend_from_slice(&sum);
        atomic_replace(&self.cursor_path, &bytes)
    }

    fn read_cursor(&self) -> Result<u64, PrivateBazaarWorkerError> {
        let bytes = match fs::read(&self.cursor_path) {
            Ok(bytes) => bytes,
            Err(error) if error.kind() == std::io::ErrorKind::NotFound => return Ok(0),
            Err(error) => {
                return Err(PrivateBazaarWorkerError::io(
                    "read sealed ingress cursor",
                    error,
                ));
            }
        };
        if bytes.len() != INGRESS_CURSOR_LEN || &bytes[..8] != INGRESS_CURSOR_MAGIC {
            return Err(PrivateBazaarWorkerError::Corrupt("sealed ingress cursor"));
        }
        if checksum(INGRESS_CURSOR_DOMAIN, &bytes[..INGRESS_CURSOR_LEN - 32])
            != bytes[INGRESS_CURSOR_LEN - 32..]
        {
            return Err(PrivateBazaarWorkerError::Corrupt(
                "sealed ingress cursor checksum",
            ));
        }
        Ok(u64::from_be_bytes(
            bytes[8..16]
                .try_into()
                .expect("fixed sealed ingress cursor length checked"),
        ))
    }

    fn open_queue(&self) -> Result<Option<File>, PrivateBazaarWorkerError> {
        let file = match File::open(&self.path) {
            Ok(file) => file,
            Err(error) if error.kind() == std::io::ErrorKind::NotFound => return Ok(None),
            Err(error) => {
                return Err(PrivateBazaarWorkerError::io(
                    "open sealed ingress queue",
                    error,
                ));
            }
        };
        validate_private_file_handle(&file, &self.root)?;
        Ok(Some(file))
    }

    fn record_count(&self, file: &File) -> Result<u64, PrivateBazaarWorkerError> {
        let length = file
            .metadata()
            .map_err(|error| PrivateBazaarWorkerError::io("stat sealed ingress queue", error))?
            .len();
        let record_len = INGRESS_RECORD_LEN as u64;
        if length % record_len != 0 {
            return Err(PrivateBazaarWorkerError::SpoolTrailingBytes {
                found: length % record_len,
            });
        }
        Ok(length / record_len)
    }

    /// The trailing chain anchor of record `count - 1`, or all zero when `count`
    /// is zero. Read directly rather than by decoding the predecessor.
    fn tail_checksum(
        &self,
        file: &mut File,
        count: u64,
    ) -> Result<[u8; 32], PrivateBazaarWorkerError> {
        if count == 0 {
            return Ok([0; 32]);
        }
        let at = count * (INGRESS_RECORD_LEN as u64) - 32;
        file.seek(SeekFrom::Start(at))
            .map_err(|error| PrivateBazaarWorkerError::io("seek sealed ingress queue", error))?;
        let mut anchor = [0; 32];
        file.read_exact(&mut anchor).map_err(|error| {
            PrivateBazaarWorkerError::io("read sealed ingress chain anchor", error)
        })?;
        Ok(anchor)
    }

    fn read_record(
        &self,
        file: &mut File,
        index: u64,
    ) -> Result<DecodedIngressRecord, PrivateBazaarWorkerError> {
        file.seek(SeekFrom::Start(index * (INGRESS_RECORD_LEN as u64)))
            .map_err(|error| PrivateBazaarWorkerError::io("seek sealed ingress queue", error))?;
        let mut bytes = vec![0; INGRESS_RECORD_LEN];
        file.read_exact(&mut bytes)
            .map_err(|error| PrivateBazaarWorkerError::io("read sealed ingress record", error))?;
        let record = decode_ingress_record(&bytes)?;
        if record.scope != self.scope {
            return Err(PrivateBazaarWorkerError::SpoolScopeMismatch);
        }
        let expected = index
            .checked_add(1)
            .ok_or(PrivateBazaarWorkerError::CursorOverflow)?;
        if record.pending.sequence != expected {
            return Err(PrivateBazaarWorkerError::NonContiguousCursor {
                expected,
                found: record.pending.sequence,
            });
        }
        Ok(record)
    }

    /// Validate the complete historical chain. Run once, at open, so a tampered
    /// or forked queue is refused before it can feed the relation.
    fn validate_chain(&self) -> Result<(), PrivateBazaarWorkerError> {
        let Some(mut file) = self.open_queue()? else {
            return Ok(());
        };
        let count = self.record_count(&file)?;
        let mut previous = [0; 32];
        for index in 0..count {
            let record = self.read_record(&mut file, index)?;
            if record.previous_checksum != previous {
                return Err(PrivateBazaarWorkerError::SpoolFork {
                    expected: index + 1,
                    found: record.pending.sequence,
                });
            }
            previous = record.checksum;
        }
        Ok(())
    }

    fn validate_bidders(
        &self,
        bids: &[(DreggIdentity, i64)],
    ) -> Result<(), PrivateBazaarIngressError> {
        let mut seen: Vec<&DreggIdentity> = Vec::with_capacity(bids.len());
        for (ordinal, (actor, _)) in bids.iter().enumerate() {
            if actor.0.len() > MAX_INGRESS_ACTOR_BYTES {
                return Err(PrivateBazaarIngressError::BidderHandleTooLong {
                    ordinal,
                    limit: MAX_INGRESS_ACTOR_BYTES,
                });
            }
            if !self.roster.contains(actor) {
                return Err(PrivateBazaarIngressError::BidderNotInDeploymentRoster { ordinal });
            }
            if seen.contains(&actor) {
                return Err(PrivateBazaarIngressError::DuplicateBidder { ordinal });
            }
            seen.push(actor);
        }
        Ok(())
    }
}

struct DecodedIngressRecord {
    scope: PrivateBazaarSpoolScope,
    previous_checksum: [u8; 32],
    checksum: [u8; 32],
    pending: PendingSealedIngress,
}

fn encode_ingress_record(
    scope: PrivateBazaarSpoolScope,
    previous_checksum: [u8; 32],
    sequence: u64,
    session_seed: u64,
    book: &PrivateSealedIngressBook,
    blinding: Option<[u32; 8]>,
) -> Result<Vec<u8>, PrivateBazaarWorkerError> {
    let bids = book.sealed_bids();
    if bids.is_empty() || bids.len() > PROVEN_MAX_SEALED_BIDS {
        return Err(PrivateBazaarWorkerError::Corrupt(
            "sealed ingress book arity",
        ));
    }
    let mut out = Vec::with_capacity(INGRESS_RECORD_LEN);
    out.extend_from_slice(INGRESS_MAGIC);
    out.extend_from_slice(&sequence.to_be_bytes());
    out.extend_from_slice(&previous_checksum);
    out.extend_from_slice(&scope.deployment_id());
    out.extend_from_slice(&scope.executor_federation());
    out.extend_from_slice(&scope.policy_id());
    out.extend_from_slice(&session_seed.to_be_bytes());
    match blinding {
        Some(limbs) => {
            out.push(1);
            for lane in limbs {
                out.extend_from_slice(&lane.to_be_bytes());
            }
        }
        None => {
            out.push(0);
            out.resize(out.len() + 32, 0);
        }
    }
    out.push(u8::try_from(bids.len()).expect("bounded sealed ingress arity fits u8"));
    for slot in 0..INGRESS_BID_SLOTS {
        match bids.get(slot) {
            Some((actor, limit)) => {
                let handle = actor.0.as_bytes();
                let handle_len = u16::try_from(handle.len())
                    .ok()
                    .filter(|found| *found != 0 && usize::from(*found) <= MAX_INGRESS_ACTOR_BYTES);
                let Some(handle_len) = handle_len else {
                    return Err(PrivateBazaarWorkerError::Corrupt(
                        "sealed ingress bidder handle length",
                    ));
                };
                out.extend_from_slice(&handle_len.to_be_bytes());
                out.extend_from_slice(handle);
                out.resize(out.len() + (MAX_INGRESS_ACTOR_BYTES - handle.len()), 0);
                out.extend_from_slice(&limit.to_be_bytes());
            }
            None => out.resize(out.len() + INGRESS_BID_SLOT_LEN, 0),
        }
    }
    let sum = checksum(INGRESS_DOMAIN, &out);
    out.extend_from_slice(&sum);
    if out.len() != INGRESS_RECORD_LEN {
        return Err(PrivateBazaarWorkerError::Corrupt(
            "sealed ingress encoder length",
        ));
    }
    // Refuse a noncanonical record before fsync rather than discovering it at
    // drain time, when the operator who could fix it is long gone.
    let _ = decode_ingress_record(&out)?;
    Ok(out)
}

/// Read the next `N` bytes of a fixed record. The record length is checked by
/// the caller before any call, so a short read is impossible.
fn take<const N: usize>(bytes: &[u8], offset: &mut usize) -> [u8; N] {
    let start = *offset;
    *offset += N;
    bytes[start..*offset]
        .try_into()
        .expect("fixed sealed ingress record length checked")
}

fn decode_ingress_record(bytes: &[u8]) -> Result<DecodedIngressRecord, PrivateBazaarWorkerError> {
    if bytes.len() != INGRESS_RECORD_LEN || &bytes[..8] != INGRESS_MAGIC {
        return Err(PrivateBazaarWorkerError::Corrupt(
            "sealed ingress record schema",
        ));
    }
    if checksum(INGRESS_DOMAIN, &bytes[..INGRESS_RECORD_LEN - 32])
        != bytes[INGRESS_RECORD_LEN - 32..]
    {
        return Err(PrivateBazaarWorkerError::Corrupt(
            "sealed ingress record checksum",
        ));
    }
    let mut offset = 8;
    let sequence = u64::from_be_bytes(take::<8>(bytes, &mut offset));
    let previous_checksum = take::<32>(bytes, &mut offset);
    let deployment_id = take::<32>(bytes, &mut offset);
    let executor_federation = take::<32>(bytes, &mut offset);
    let policy_id = take::<32>(bytes, &mut offset);
    let session_seed = u64::from_be_bytes(take::<8>(bytes, &mut offset));
    let blinding_flag = take::<1>(bytes, &mut offset)[0];
    let blinding_bytes = take::<32>(bytes, &mut offset);
    let blinding = match blinding_flag {
        0 if blinding_bytes == [0; 32] => None,
        1 => {
            let mut limbs = [0u32; 8];
            for (index, limb) in limbs.iter_mut().enumerate() {
                *limb = u32::from_be_bytes(
                    blinding_bytes[index * 4..(index + 1) * 4]
                        .try_into()
                        .expect("fixed field"),
                );
            }
            Some(limbs)
        }
        _ => {
            return Err(PrivateBazaarWorkerError::Corrupt(
                "sealed ingress blinding encoding",
            ));
        }
    };
    let bid_count = usize::from(take::<1>(bytes, &mut offset)[0]);
    if bid_count > INGRESS_BID_SLOTS {
        return Err(PrivateBazaarWorkerError::Corrupt(
            "sealed ingress bid count",
        ));
    }
    let mut bids = Vec::with_capacity(bid_count);
    for slot in 0..INGRESS_BID_SLOTS {
        let handle_len = usize::from(u16::from_be_bytes(take::<2>(bytes, &mut offset)));
        let handle_slot = take::<MAX_INGRESS_ACTOR_BYTES>(bytes, &mut offset);
        let limit = i64::from_be_bytes(take::<8>(bytes, &mut offset));
        if slot >= bid_count {
            if handle_len != 0 || handle_slot.iter().any(|byte| *byte != 0) || limit != 0 {
                return Err(PrivateBazaarWorkerError::Corrupt(
                    "sealed ingress unused bid slot",
                ));
            }
            continue;
        }
        if handle_len == 0 || handle_len > MAX_INGRESS_ACTOR_BYTES {
            return Err(PrivateBazaarWorkerError::Corrupt(
                "sealed ingress bidder handle length",
            ));
        }
        if handle_slot[handle_len..].iter().any(|byte| *byte != 0) {
            return Err(PrivateBazaarWorkerError::Corrupt(
                "sealed ingress bidder handle padding",
            ));
        }
        let handle = String::from_utf8(handle_slot[..handle_len].to_vec())
            .map_err(|_| PrivateBazaarWorkerError::Corrupt("sealed ingress bidder handle utf8"))?;
        bids.push((DreggIdentity(handle), limit));
    }
    // THE GATE, RE-RUN ON UNTRUSTED BYTES. A hostile queue file that recomputes
    // the record checksum still cannot widen the proved family: this is the same
    // constructor a production submitter must pass, and it refuses by name.
    let book = PrivateSealedIngressBook::new(bids).map_err(|error| match error {
        PrivateClearingError::TooManyBids(found) => PrivateBazaarWorkerError::SourceExceededBound {
            found,
            limit: PROVEN_MAX_SEALED_BIDS,
        },
        PrivateClearingError::PriceOutsideFixedFamily(_) => {
            PrivateBazaarWorkerError::Corrupt("sealed ingress bid limit outside proved family")
        }
        PrivateClearingError::NoBids => {
            PrivateBazaarWorkerError::Corrupt("sealed ingress empty book")
        }
        _ => PrivateBazaarWorkerError::Corrupt("sealed ingress book"),
    })?;
    Ok(DecodedIngressRecord {
        scope: PrivateBazaarSpoolScope::new(deployment_id, executor_federation, policy_id),
        previous_checksum,
        checksum: bytes[INGRESS_RECORD_LEN - 32..]
            .try_into()
            .expect("fixed field"),
        pending: PendingSealedIngress {
            sequence,
            session_seed,
            book,
            blinding,
        },
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    fn actor(name: &str) -> DreggIdentity {
        DreggIdentity(name.to_owned())
    }

    fn scope() -> PrivateBazaarSpoolScope {
        PrivateBazaarSpoolScope::new([0x11; 32], [0x22; 32], [0x33; 32])
    }

    fn book() -> PrivateSealedIngressBook {
        PrivateSealedIngressBook::new(vec![(actor("alice"), 2), (actor("bob"), 3)])
            .expect("in-family")
    }

    #[test]
    fn the_ingress_record_length_is_pinned() {
        assert_eq!(INGRESS_BID_SLOTS, PROVEN_MAX_SEALED_BIDS + 1);
        assert_eq!(INGRESS_BID_SLOT_LEN, 138);
        assert_eq!(INGRESS_RECORD_LEN, 770);
    }

    #[test]
    fn a_record_round_trips_its_exact_bidders_and_limits() {
        let bytes =
            encode_ingress_record(scope(), [0; 32], 1, 0xABCD, &book(), Some([7; 8])).unwrap();
        let decoded = decode_ingress_record(&bytes).unwrap();
        assert_eq!(decoded.pending.sequence, 1);
        assert_eq!(decoded.pending.session_seed, 0xABCD);
        assert_eq!(decoded.pending.blinding, Some([7; 8]));
        assert_eq!(
            decoded.pending.book.sealed_bids().to_vec(),
            vec![(actor("alice"), 2), (actor("bob"), 3)]
        );
    }

    /// THE FAMILY GATE HOLDS AGAINST A HOSTILE, CORRECTLY-CHECKSUMMED RECORD.
    ///
    /// The record has room for a fourth bid and for a limit of 4 precisely so
    /// this can be attempted. Both are refused; neither is truncated or clamped.
    #[test]
    fn a_tampered_record_cannot_widen_the_proved_family() {
        let base = encode_ingress_record(scope(), [0; 32], 1, 7, &book(), None).unwrap();
        let count_offset = 8 + 8 + 32 + 32 + 32 + 32 + 8 + 1 + 32;

        let mut too_many = base.clone();
        too_many[count_offset] = 4;
        // Fill the third and fourth slots so the unused-slot check is not what
        // fires; the arity gate must be.
        for slot in 2..4 {
            let at = count_offset + 1 + (slot * INGRESS_BID_SLOT_LEN);
            too_many[at..at + 2].copy_from_slice(&3u16.to_be_bytes());
            too_many[at + 2..at + 5].copy_from_slice(b"eve");
            let limit_at = at + 2 + MAX_INGRESS_ACTOR_BYTES;
            too_many[limit_at..limit_at + 8].copy_from_slice(&1i64.to_be_bytes());
        }
        reseal(&mut too_many);
        assert!(
            matches!(
                decode_ingress_record(&too_many),
                Err(PrivateBazaarWorkerError::SourceExceededBound { found: 4, limit: 3 })
            ),
            "a four-bid record must be refused by the proved-family gate"
        );

        let mut too_wide = base.clone();
        let limit_at = count_offset + 1 + 2 + MAX_INGRESS_ACTOR_BYTES;
        too_wide[limit_at..limit_at + 8]
            .copy_from_slice(&(PROVEN_PRICE_BUCKETS as i64).to_be_bytes());
        reseal(&mut too_wide);
        assert!(matches!(
            decode_ingress_record(&too_wide),
            Err(PrivateBazaarWorkerError::Corrupt(
                "sealed ingress bid limit outside proved family"
            ))
        ));

        let mut negative = base.clone();
        negative[limit_at..limit_at + 8].copy_from_slice(&(-1i64).to_be_bytes());
        reseal(&mut negative);
        assert!(matches!(
            decode_ingress_record(&negative),
            Err(PrivateBazaarWorkerError::Corrupt(
                "sealed ingress bid limit outside proved family"
            ))
        ));
    }

    #[test]
    fn a_record_without_a_recomputed_checksum_is_refused() {
        let mut bytes = encode_ingress_record(scope(), [0; 32], 1, 7, &book(), None).unwrap();
        let limit_at = 8 + 8 + 32 + 32 + 32 + 32 + 8 + 1 + 32 + 1 + 2 + MAX_INGRESS_ACTOR_BYTES;
        bytes[limit_at + 7] ^= 1;
        assert!(matches!(
            decode_ingress_record(&bytes),
            Err(PrivateBazaarWorkerError::Corrupt(
                "sealed ingress record checksum"
            ))
        ));
    }

    fn reseal(bytes: &mut [u8]) {
        let sum = checksum(INGRESS_DOMAIN, &bytes[..INGRESS_RECORD_LEN - 32]);
        bytes[INGRESS_RECORD_LEN - 32..].copy_from_slice(&sum);
    }
}
