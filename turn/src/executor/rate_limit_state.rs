//! Canonical persistence boundary for executor rate-limit consensus state.
//!
//! Node executors are deliberately short-lived. The maps backing
//! `RateLimit`/`RateLimitBySum` therefore need a deterministic durable image;
//! treating them as constructor-local caches resets every window on the next
//! submit. This module owns the typed, bounded encoding used at that boundary.
//!
//! Persistence must weld these bytes into the same database transaction as the
//! finalized turn and commit cursor. The codec intentionally performs no I/O:
//! writing it through a separate generic-config transaction would merely move
//! the crash-consistency gap.

use std::{collections::HashMap, fmt};

use dregg_cell::CellId;

use super::{RateLimitCounterKey, RateLimitSumKey, TurnExecutor};

const RATE_LIMIT_STATE_MAGIC_V1: &[u8; 20] = b"dregg-rate-state-v1\0";
const HEADER_BYTES: usize = RATE_LIMIT_STATE_MAGIC_V1.len() + 8;
const COUNT_ENTRY_BYTES: usize = 32 + 32 + 8 + 4;
const SUM_ENTRY_BYTES: usize = 32 + 1 + 8 + 8;
pub const MAX_RATE_LIMIT_STATE_ENTRIES: usize = 200_000;
pub const MAX_RATE_LIMIT_STATE_BYTES: usize = 32 * 1024 * 1024;

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct RateLimitCountEntry {
    pub cell: CellId,
    pub sender: [u8; 32],
    pub epoch: u64,
    pub count: u32,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct RateLimitSumEntry {
    pub cell: CellId,
    pub slot: u8,
    pub epoch: u64,
    pub sum: u64,
}

/// One complete, canonical post-turn rate-limit frontier.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct RateLimitStateSnapshot {
    pub counts: Vec<RateLimitCountEntry>,
    pub sums: Vec<RateLimitSumEntry>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum RateLimitStateCodecError {
    TooLarge { size: usize, max: usize },
    TooManyEntries { count: usize, max: usize },
    InvalidMagic,
    Truncated,
    TrailingBytes,
    NonCanonicalCounts,
    NonCanonicalSums,
    SizeOverflow,
}

impl fmt::Display for RateLimitStateCodecError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::TooLarge { size, max } => {
                write!(f, "rate-limit snapshot is {size} bytes (maximum {max})")
            }
            Self::TooManyEntries { count, max } => {
                write!(f, "rate-limit snapshot has {count} entries (maximum {max})")
            }
            Self::InvalidMagic => f.write_str("invalid rate-limit snapshot magic/version"),
            Self::Truncated => f.write_str("truncated rate-limit snapshot"),
            Self::TrailingBytes => f.write_str("rate-limit snapshot has trailing bytes"),
            Self::NonCanonicalCounts => {
                f.write_str("rate-limit count entries are not strictly sorted and unique")
            }
            Self::NonCanonicalSums => {
                f.write_str("rate-limit sum entries are not strictly sorted and unique")
            }
            Self::SizeOverflow => f.write_str("rate-limit snapshot size overflow"),
        }
    }
}

impl std::error::Error for RateLimitStateCodecError {}

impl RateLimitStateSnapshot {
    fn validate(&self) -> Result<(), RateLimitStateCodecError> {
        let total = self
            .counts
            .len()
            .checked_add(self.sums.len())
            .ok_or(RateLimitStateCodecError::SizeOverflow)?;
        if total > MAX_RATE_LIMIT_STATE_ENTRIES {
            return Err(RateLimitStateCodecError::TooManyEntries {
                count: total,
                max: MAX_RATE_LIMIT_STATE_ENTRIES,
            });
        }
        if !self.counts.windows(2).all(|pair| pair[0] < pair[1]) {
            return Err(RateLimitStateCodecError::NonCanonicalCounts);
        }
        if !self.sums.windows(2).all(|pair| pair[0] < pair[1]) {
            return Err(RateLimitStateCodecError::NonCanonicalSums);
        }
        Ok(())
    }

    fn encoded_len(&self) -> Result<usize, RateLimitStateCodecError> {
        HEADER_BYTES
            .checked_add(
                self.counts
                    .len()
                    .checked_mul(COUNT_ENTRY_BYTES)
                    .ok_or(RateLimitStateCodecError::SizeOverflow)?,
            )
            .and_then(|size| size.checked_add(self.sums.len().checked_mul(SUM_ENTRY_BYTES)?))
            .ok_or(RateLimitStateCodecError::SizeOverflow)
    }

    pub fn to_canonical_bytes(&self) -> Result<Vec<u8>, RateLimitStateCodecError> {
        self.validate()?;
        let size = self.encoded_len()?;
        if size > MAX_RATE_LIMIT_STATE_BYTES {
            return Err(RateLimitStateCodecError::TooLarge {
                size,
                max: MAX_RATE_LIMIT_STATE_BYTES,
            });
        }
        let count_len =
            u32::try_from(self.counts.len()).map_err(|_| RateLimitStateCodecError::SizeOverflow)?;
        let sum_len =
            u32::try_from(self.sums.len()).map_err(|_| RateLimitStateCodecError::SizeOverflow)?;
        let mut out = Vec::with_capacity(size);
        out.extend_from_slice(RATE_LIMIT_STATE_MAGIC_V1);
        out.extend_from_slice(&count_len.to_le_bytes());
        out.extend_from_slice(&sum_len.to_le_bytes());
        for entry in &self.counts {
            out.extend_from_slice(entry.cell.as_bytes());
            out.extend_from_slice(&entry.sender);
            out.extend_from_slice(&entry.epoch.to_le_bytes());
            out.extend_from_slice(&entry.count.to_le_bytes());
        }
        for entry in &self.sums {
            out.extend_from_slice(entry.cell.as_bytes());
            out.push(entry.slot);
            out.extend_from_slice(&entry.epoch.to_le_bytes());
            out.extend_from_slice(&entry.sum.to_le_bytes());
        }
        debug_assert_eq!(out.len(), size);
        Ok(out)
    }

    pub fn from_canonical_bytes(bytes: &[u8]) -> Result<Self, RateLimitStateCodecError> {
        if bytes.len() > MAX_RATE_LIMIT_STATE_BYTES {
            return Err(RateLimitStateCodecError::TooLarge {
                size: bytes.len(),
                max: MAX_RATE_LIMIT_STATE_BYTES,
            });
        }
        let header = bytes
            .get(..HEADER_BYTES)
            .ok_or(RateLimitStateCodecError::Truncated)?;
        if &header[..RATE_LIMIT_STATE_MAGIC_V1.len()] != RATE_LIMIT_STATE_MAGIC_V1 {
            return Err(RateLimitStateCodecError::InvalidMagic);
        }
        let count_len = u32::from_le_bytes(
            header[RATE_LIMIT_STATE_MAGIC_V1.len()..RATE_LIMIT_STATE_MAGIC_V1.len() + 4]
                .try_into()
                .expect("fixed header slice"),
        ) as usize;
        let sum_len = u32::from_le_bytes(
            header[RATE_LIMIT_STATE_MAGIC_V1.len() + 4..HEADER_BYTES]
                .try_into()
                .expect("fixed header slice"),
        ) as usize;
        let total = count_len
            .checked_add(sum_len)
            .ok_or(RateLimitStateCodecError::SizeOverflow)?;
        if total > MAX_RATE_LIMIT_STATE_ENTRIES {
            return Err(RateLimitStateCodecError::TooManyEntries {
                count: total,
                max: MAX_RATE_LIMIT_STATE_ENTRIES,
            });
        }
        let expected = HEADER_BYTES
            .checked_add(
                count_len
                    .checked_mul(COUNT_ENTRY_BYTES)
                    .ok_or(RateLimitStateCodecError::SizeOverflow)?,
            )
            .and_then(|size| size.checked_add(sum_len.checked_mul(SUM_ENTRY_BYTES)?))
            .ok_or(RateLimitStateCodecError::SizeOverflow)?;
        match bytes.len().cmp(&expected) {
            std::cmp::Ordering::Less => return Err(RateLimitStateCodecError::Truncated),
            std::cmp::Ordering::Greater => return Err(RateLimitStateCodecError::TrailingBytes),
            std::cmp::Ordering::Equal => {}
        }

        let mut offset = HEADER_BYTES;
        let mut counts = Vec::with_capacity(count_len);
        for _ in 0..count_len {
            let entry = &bytes[offset..offset + COUNT_ENTRY_BYTES];
            counts.push(RateLimitCountEntry {
                cell: CellId::from_bytes(entry[..32].try_into().expect("fixed entry slice")),
                sender: entry[32..64].try_into().expect("fixed entry slice"),
                epoch: u64::from_le_bytes(entry[64..72].try_into().expect("fixed entry slice")),
                count: u32::from_le_bytes(entry[72..76].try_into().expect("fixed entry slice")),
            });
            offset += COUNT_ENTRY_BYTES;
        }
        let mut sums = Vec::with_capacity(sum_len);
        for _ in 0..sum_len {
            let entry = &bytes[offset..offset + SUM_ENTRY_BYTES];
            sums.push(RateLimitSumEntry {
                cell: CellId::from_bytes(entry[..32].try_into().expect("fixed entry slice")),
                slot: entry[32],
                epoch: u64::from_le_bytes(entry[33..41].try_into().expect("fixed entry slice")),
                sum: u64::from_le_bytes(entry[41..49].try_into().expect("fixed entry slice")),
            });
            offset += SUM_ENTRY_BYTES;
        }
        let snapshot = Self { counts, sums };
        snapshot.validate()?;
        Ok(snapshot)
    }
}

impl TurnExecutor {
    /// Snapshot both committed maps under one lock order. Entries are sorted so
    /// equal consensus state has one byte representation on every host.
    pub fn rate_limit_state_snapshot(&self) -> RateLimitStateSnapshot {
        let counts = self.rate_limit_counters.lock().unwrap();
        let sums = self.rate_limit_sum_counters.lock().unwrap();
        let mut count_entries: Vec<_> = counts
            .iter()
            .map(|((cell, sender, epoch), count)| RateLimitCountEntry {
                cell: *cell,
                sender: *sender,
                epoch: *epoch,
                count: *count,
            })
            .collect();
        let mut sum_entries: Vec<_> = sums
            .iter()
            .map(|((cell, slot, epoch), sum)| RateLimitSumEntry {
                cell: *cell,
                slot: *slot,
                epoch: *epoch,
                sum: *sum,
            })
            .collect();
        count_entries.sort_unstable();
        sum_entries.sort_unstable();
        RateLimitStateSnapshot {
            counts: count_entries,
            sums: sum_entries,
        }
    }

    /// Replace a fresh executor's rate frontier with a validated durable image.
    /// The replacement is all-or-nothing with respect to readers taking the
    /// maps in the documented count-then-sum order.
    pub fn restore_rate_limit_state(
        &self,
        snapshot: &RateLimitStateSnapshot,
    ) -> Result<(), RateLimitStateCodecError> {
        snapshot.validate()?;
        let restored_counts: HashMap<RateLimitCounterKey, u32> = snapshot
            .counts
            .iter()
            .map(|entry| ((entry.cell, entry.sender, entry.epoch), entry.count))
            .collect();
        let restored_sums: HashMap<RateLimitSumKey, u64> = snapshot
            .sums
            .iter()
            .map(|entry| ((entry.cell, entry.slot, entry.epoch), entry.sum))
            .collect();
        let mut counts = self.rate_limit_counters.lock().unwrap();
        let mut sums = self.rate_limit_sum_counters.lock().unwrap();
        *counts = restored_counts;
        *sums = restored_sums;
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::executor::ComputronCosts;

    fn sample() -> RateLimitStateSnapshot {
        RateLimitStateSnapshot {
            counts: vec![
                RateLimitCountEntry {
                    cell: CellId::from_bytes([1; 32]),
                    sender: [2; 32],
                    epoch: 3,
                    count: 4,
                },
                RateLimitCountEntry {
                    cell: CellId::from_bytes([5; 32]),
                    sender: [6; 32],
                    epoch: u64::MAX,
                    count: u32::MAX,
                },
            ],
            sums: vec![RateLimitSumEntry {
                cell: CellId::from_bytes([7; 32]),
                slot: 15,
                epoch: 8,
                sum: u64::MAX,
            }],
        }
    }

    #[test]
    fn canonical_round_trip_is_exact_and_full_width() {
        let snapshot = sample();
        let bytes = snapshot.to_canonical_bytes().unwrap();
        assert_eq!(
            RateLimitStateSnapshot::from_canonical_bytes(&bytes).unwrap(),
            snapshot
        );
    }

    #[test]
    fn duplicate_unsorted_and_trailing_images_are_rejected() {
        let mut duplicate = sample();
        duplicate.counts.push(duplicate.counts[1]);
        assert_eq!(
            duplicate.to_canonical_bytes().unwrap_err(),
            RateLimitStateCodecError::NonCanonicalCounts
        );

        let mut trailing = sample().to_canonical_bytes().unwrap();
        trailing.push(0);
        assert_eq!(
            RateLimitStateSnapshot::from_canonical_bytes(&trailing).unwrap_err(),
            RateLimitStateCodecError::TrailingBytes
        );
    }

    #[test]
    fn executor_snapshot_restore_has_one_canonical_image() {
        let executor = TurnExecutor::new(ComputronCosts::zero());
        executor.restore_rate_limit_state(&sample()).unwrap();
        let first = executor
            .rate_limit_state_snapshot()
            .to_canonical_bytes()
            .unwrap();

        let restored = TurnExecutor::new(ComputronCosts::zero());
        restored
            .restore_rate_limit_state(
                &RateLimitStateSnapshot::from_canonical_bytes(&first).unwrap(),
            )
            .unwrap();
        let second = restored
            .rate_limit_state_snapshot()
            .to_canonical_bytes()
            .unwrap();
        assert_eq!(first, second);
    }
}
