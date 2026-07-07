//! Write-Ahead Log for MerkleQueue durability.
//!
//! Every mutation is logged BEFORE being applied in-memory.
//! On crash recovery: replay the log to reconstruct state.
//!
//! # Lean-spec status
//!
//! No Lean theorem specifies the WAL yet — nothing under
//! `metatheory/Dregg2/Storage/` covers durability logging (the theorems
//! there specify the bucket content commitment, erasure coding, PoR, and
//! availability). The contract pinned executably by the `prop_*` tests
//! below — replay conserves the appended record sequence across a crash;
//! a truncated tail replays as exactly the intact prefix; a corrupted
//! record is detected by its checksum and dropped without disturbing its
//! neighbors, never hallucinated — is the statement a future
//! `Dregg2/Storage/Wal.lean` should prove.

use std::fs::{self, File, OpenOptions};
use std::io::{self, BufRead, BufReader, BufWriter, Write};
use std::path::PathBuf;

/// Write-Ahead Log for MerkleQueue durability.
/// Every mutation is logged BEFORE being applied in-memory.
/// On crash recovery: replay the log to reconstruct state.
#[derive(Debug)]
pub struct WriteAheadLog {
    /// Path to the WAL file
    path: PathBuf,
    /// Buffered writer (fsync on commit)
    writer: Option<BufWriter<File>>,
    /// Sequence number (monotonically increasing)
    sequence: u64,
}

/// A single WAL entry representing a mutation.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum WalEntry {
    Enqueue {
        queue_id: [u8; 32],
        entry_hash: [u8; 32],
        data: Vec<u8>,
        sequence: u64,
    },
    Dequeue {
        queue_id: [u8; 32],
        position: usize,
        sequence: u64,
    },
    CreateQueue {
        queue_id: [u8; 32],
        capacity: usize,
        sequence: u64,
    },
    Checkpoint {
        queue_id: [u8; 32],
        root: [u8; 32],
        sequence: u64,
    },
}

impl WalEntry {
    /// Get the sequence number of this entry.
    pub fn sequence(&self) -> u64 {
        match self {
            WalEntry::Enqueue { sequence, .. } => *sequence,
            WalEntry::Dequeue { sequence, .. } => *sequence,
            WalEntry::CreateQueue { sequence, .. } => *sequence,
            WalEntry::Checkpoint { sequence, .. } => *sequence,
        }
    }

    /// Serialize to a line-based format with a checksum.
    /// Format: TYPE|hex_fields...|checksum\n
    fn serialize(&self) -> Vec<u8> {
        let payload = match self {
            WalEntry::Enqueue {
                queue_id,
                entry_hash,
                data,
                sequence,
            } => {
                format!(
                    "E|{}|{}|{}|{}",
                    hex_encode(queue_id),
                    hex_encode(entry_hash),
                    hex_encode(data),
                    sequence,
                )
            }
            WalEntry::Dequeue {
                queue_id,
                position,
                sequence,
            } => {
                format!("D|{}|{}|{}", hex_encode(queue_id), position, sequence,)
            }
            WalEntry::CreateQueue {
                queue_id,
                capacity,
                sequence,
            } => {
                format!("C|{}|{}|{}", hex_encode(queue_id), capacity, sequence,)
            }
            WalEntry::Checkpoint {
                queue_id,
                root,
                sequence,
            } => {
                format!(
                    "K|{}|{}|{}",
                    hex_encode(queue_id),
                    hex_encode(root),
                    sequence,
                )
            }
        };
        // Append a blake3 checksum of the payload for torn-write detection.
        let checksum = blake3::hash(payload.as_bytes());
        let line = format!("{}|{}\n", payload, hex_encode(checksum.as_bytes()));
        line.into_bytes()
    }

    /// Deserialize from a line. Returns None if the line is corrupt (bad checksum or parse error).
    fn deserialize(line: &str) -> Option<Self> {
        let line = line.trim_end_matches('\n');
        // Split off the last field as checksum.
        let last_pipe = line.rfind('|')?;
        let payload = &line[..last_pipe];
        let checksum_hex = &line[last_pipe + 1..];

        // Verify checksum.
        let expected_checksum = blake3::hash(payload.as_bytes());
        let expected_hex = hex_encode(expected_checksum.as_bytes());
        if checksum_hex != expected_hex {
            return None; // Torn write or corruption.
        }

        let parts: Vec<&str> = payload.split('|').collect();
        if parts.is_empty() {
            return None;
        }

        match parts[0] {
            "E" if parts.len() == 5 => {
                let queue_id = hex_decode_32(parts[1])?;
                let entry_hash = hex_decode_32(parts[2])?;
                let data = hex_decode_vec(parts[3])?;
                let sequence: u64 = parts[4].parse().ok()?;
                Some(WalEntry::Enqueue {
                    queue_id,
                    entry_hash,
                    data,
                    sequence,
                })
            }
            "D" if parts.len() == 4 => {
                let queue_id = hex_decode_32(parts[1])?;
                let position: usize = parts[2].parse().ok()?;
                let sequence: u64 = parts[3].parse().ok()?;
                Some(WalEntry::Dequeue {
                    queue_id,
                    position,
                    sequence,
                })
            }
            "C" if parts.len() == 4 => {
                let queue_id = hex_decode_32(parts[1])?;
                let capacity: usize = parts[2].parse().ok()?;
                let sequence: u64 = parts[3].parse().ok()?;
                Some(WalEntry::CreateQueue {
                    queue_id,
                    capacity,
                    sequence,
                })
            }
            "K" if parts.len() == 4 => {
                let queue_id = hex_decode_32(parts[1])?;
                let root = hex_decode_32(parts[2])?;
                let sequence: u64 = parts[3].parse().ok()?;
                Some(WalEntry::Checkpoint {
                    queue_id,
                    root,
                    sequence,
                })
            }
            _ => None,
        }
    }
}

impl WriteAheadLog {
    /// Open (or create) a WAL file at the given path.
    /// If the file already exists, the sequence number is derived from the last entry.
    pub fn open(path: PathBuf) -> io::Result<Self> {
        // Determine the current sequence from existing entries.
        let sequence = if path.exists() {
            let entries = Self::replay_from_path(&path)?;
            entries.last().map(|e| e.sequence() + 1).unwrap_or(0)
        } else {
            0
        };

        let file = OpenOptions::new().create(true).append(true).open(&path)?;
        let writer = BufWriter::new(file);

        Ok(Self {
            path,
            writer: Some(writer),
            sequence,
        })
    }

    /// Append a WAL entry. The entry's sequence field is set by the WAL.
    pub fn append(&mut self, entry: &WalEntry) -> io::Result<()> {
        let writer = self
            .writer
            .as_mut()
            .ok_or_else(|| io::Error::other("WAL writer closed"))?;
        let serialized = entry.serialize();
        writer.write_all(&serialized)?;
        self.sequence += 1;
        Ok(())
    }

    /// Flush and fsync the WAL to durable storage.
    pub fn sync(&mut self) -> io::Result<()> {
        let writer = self
            .writer
            .as_mut()
            .ok_or_else(|| io::Error::other("WAL writer closed"))?;
        writer.flush()?;
        writer.get_ref().sync_all()
    }

    /// Replay all valid entries from the WAL file.
    /// Entries with bad checksums (torn writes) are skipped.
    pub fn replay(&self) -> io::Result<Vec<WalEntry>> {
        Self::replay_from_path(&self.path)
    }

    /// Truncate the WAL, removing all entries with sequence < the given value.
    /// This is called after a checkpoint to reclaim space.
    pub fn truncate_before(&mut self, sequence: u64) -> io::Result<()> {
        // Read all entries, keep only those with sequence >= the given value.
        let entries = self.replay()?;
        let kept: Vec<&WalEntry> = entries
            .iter()
            .filter(|e| e.sequence() >= sequence)
            .collect();

        // Close the writer, rewrite the file, reopen.
        self.writer = None;

        let file = OpenOptions::new()
            .create(true)
            .write(true)
            .truncate(true)
            .open(&self.path)?;
        let mut writer = BufWriter::new(file);

        for entry in &kept {
            let serialized = entry.serialize();
            writer.write_all(&serialized)?;
        }
        writer.flush()?;
        writer.get_ref().sync_all()?;

        // Reopen in append mode.
        drop(writer);
        let file = OpenOptions::new().append(true).open(&self.path)?;
        self.writer = Some(BufWriter::new(file));

        Ok(())
    }

    /// Write a checkpoint entry and return its sequence number.
    pub fn checkpoint(&mut self, queue_id: &[u8; 32], root: &[u8; 32]) -> io::Result<u64> {
        let seq = self.sequence;
        let entry = WalEntry::Checkpoint {
            queue_id: *queue_id,
            root: *root,
            sequence: seq,
        };
        self.append(&entry)?;
        self.sync()?;
        Ok(seq)
    }

    /// Get the next sequence number that will be assigned.
    pub fn next_sequence(&self) -> u64 {
        self.sequence
    }

    /// Replay from a given path (internal helper).
    fn replay_from_path(path: &PathBuf) -> io::Result<Vec<WalEntry>> {
        if !path.exists() {
            return Ok(Vec::new());
        }
        let file = File::open(path)?;
        let reader = BufReader::new(file);
        let mut entries = Vec::new();

        for line in reader.lines() {
            let line = line?;
            if line.is_empty() {
                continue;
            }
            // Skip corrupt/torn entries silently (they represent incomplete writes).
            if let Some(entry) = WalEntry::deserialize(&line) {
                entries.push(entry);
            }
        }

        Ok(entries)
    }

    /// Close the WAL (flush and drop writer).
    pub fn close(&mut self) -> io::Result<()> {
        if let Some(ref mut writer) = self.writer {
            writer.flush()?;
            writer.get_ref().sync_all()?;
        }
        self.writer = None;
        Ok(())
    }

    /// Delete the WAL file (for cleanup in tests).
    pub fn destroy(mut self) -> io::Result<()> {
        self.close()?;
        if self.path.exists() {
            fs::remove_file(&self.path)?;
        }
        Ok(())
    }
}

// ============================================================================
// Hex encoding helpers (no external dependency needed)
// ============================================================================

fn hex_encode(bytes: &[u8]) -> String {
    bytes.iter().map(|b| format!("{b:02x}")).collect()
}

fn hex_decode_32(s: &str) -> Option<[u8; 32]> {
    let bytes = hex_decode_vec(s)?;
    if bytes.len() != 32 {
        return None;
    }
    let mut arr = [0u8; 32];
    arr.copy_from_slice(&bytes);
    Some(arr)
}

fn hex_decode_vec(s: &str) -> Option<Vec<u8>> {
    if !s.len().is_multiple_of(2) {
        return None;
    }
    (0..s.len())
        .step_by(2)
        .map(|i| u8::from_str_radix(&s[i..i + 2], 16).ok())
        .collect()
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::path::Path;

    fn temp_wal_path(name: &str) -> PathBuf {
        let dir = std::env::temp_dir().join("dregg_wal_tests");
        fs::create_dir_all(&dir).unwrap();
        dir.join(format!("{}.wal", name))
    }

    fn cleanup(path: &Path) {
        let _ = fs::remove_file(path);
    }

    #[test]
    fn wal_write_and_replay() {
        let path = temp_wal_path("write_replay");
        cleanup(&path);

        {
            let mut wal = WriteAheadLog::open(path.clone()).unwrap();
            let entry1 = WalEntry::CreateQueue {
                queue_id: [0xAA; 32],
                capacity: 100,
                sequence: wal.next_sequence(),
            };
            wal.append(&entry1).unwrap();

            let entry2 = WalEntry::Enqueue {
                queue_id: [0xAA; 32],
                entry_hash: [0xBB; 32],
                data: vec![1, 2, 3, 4, 5],
                sequence: wal.next_sequence(),
            };
            wal.append(&entry2).unwrap();
            wal.sync().unwrap();
        }
        // Writer dropped (simulates crash without close).

        // Replay should recover both entries.
        let wal = WriteAheadLog::open(path.clone()).unwrap();
        let entries = wal.replay().unwrap();
        assert_eq!(entries.len(), 2);

        match &entries[0] {
            WalEntry::CreateQueue {
                queue_id,
                capacity,
                sequence,
            } => {
                assert_eq!(queue_id, &[0xAA; 32]);
                assert_eq!(*capacity, 100);
                assert_eq!(*sequence, 0);
            }
            other => panic!("Expected CreateQueue, got {:?}", other),
        }

        match &entries[1] {
            WalEntry::Enqueue {
                queue_id,
                entry_hash,
                data,
                sequence,
            } => {
                assert_eq!(queue_id, &[0xAA; 32]);
                assert_eq!(entry_hash, &[0xBB; 32]);
                assert_eq!(data, &[1, 2, 3, 4, 5]);
                assert_eq!(*sequence, 1);
            }
            other => panic!("Expected Enqueue, got {:?}", other),
        }

        wal.destroy().unwrap();
    }

    #[test]
    fn wal_checkpoint_truncates_old_entries() {
        let path = temp_wal_path("checkpoint_truncate");
        cleanup(&path);

        let mut wal = WriteAheadLog::open(path.clone()).unwrap();

        // Write 5 entries.
        for i in 0..5u64 {
            let entry = WalEntry::Enqueue {
                queue_id: [0xAA; 32],
                entry_hash: [i as u8; 32],
                data: vec![i as u8],
                sequence: wal.next_sequence(),
            };
            wal.append(&entry).unwrap();
        }
        wal.sync().unwrap();

        // Checkpoint after sequence 3 (keep entries with seq >= 3).
        wal.truncate_before(3).unwrap();

        let entries = wal.replay().unwrap();
        assert_eq!(entries.len(), 2); // seq 3 and seq 4
        assert_eq!(entries[0].sequence(), 3);
        assert_eq!(entries[1].sequence(), 4);

        wal.destroy().unwrap();
    }

    #[test]
    fn wal_torn_write_recovery() {
        let path = temp_wal_path("torn_write");
        cleanup(&path);

        // Write a valid entry followed by a corrupt (torn) entry.
        {
            let mut wal = WriteAheadLog::open(path.clone()).unwrap();
            let entry = WalEntry::Enqueue {
                queue_id: [0x11; 32],
                entry_hash: [0x22; 32],
                data: vec![0xAA, 0xBB],
                sequence: wal.next_sequence(),
            };
            wal.append(&entry).unwrap();
            wal.sync().unwrap();
            wal.close().unwrap();
        }

        // Manually append a torn (incomplete) line to the file.
        {
            let mut file = OpenOptions::new().append(true).open(&path).unwrap();
            // This line has a bad checksum (simulates torn write).
            writeln!(file, "E|{0}|{0}|aabbcc|99|0000000000000000000000000000000000000000000000000000000000000000", hex_encode(&[0x33; 32])).unwrap();
        }

        // Replay should recover the valid entry and skip the torn one.
        let wal = WriteAheadLog::open(path.clone()).unwrap();
        let entries = wal.replay().unwrap();
        assert_eq!(entries.len(), 1);
        assert_eq!(entries[0].sequence(), 0);

        wal.destroy().unwrap();
    }

    #[test]
    fn wal_dequeue_entry_serialization() {
        let path = temp_wal_path("dequeue_ser");
        cleanup(&path);

        let mut wal = WriteAheadLog::open(path.clone()).unwrap();
        let entry = WalEntry::Dequeue {
            queue_id: [0xCC; 32],
            position: 42,
            sequence: wal.next_sequence(),
        };
        wal.append(&entry).unwrap();
        wal.sync().unwrap();

        let entries = wal.replay().unwrap();
        assert_eq!(entries.len(), 1);
        assert_eq!(entries[0], entry);

        wal.destroy().unwrap();
    }

    #[test]
    fn wal_checkpoint_entry_serialization() {
        let path = temp_wal_path("checkpoint_ser");
        cleanup(&path);

        let mut wal = WriteAheadLog::open(path.clone()).unwrap();
        let seq = wal.next_sequence();
        let entry = WalEntry::Checkpoint {
            queue_id: [0xDD; 32],
            root: [0xEE; 32],
            sequence: seq,
        };
        wal.append(&entry).unwrap();
        wal.sync().unwrap();

        let entries = wal.replay().unwrap();
        assert_eq!(entries.len(), 1);
        assert_eq!(entries[0], entry);

        wal.destroy().unwrap();
    }

    // ------------------------------------------------------------------
    // Property tests: the guarantees the WAL actually makes.
    //
    // Census note: no Lean theorem specifies the WAL (see the module
    // doc); these tests pin its conservation/detection contract
    // executably, ready to bind when a `Dregg2/Storage/Wal.lean` lands.
    // ------------------------------------------------------------------

    /// Build a mixed log of all four entry kinds. Returns the appended
    /// sequence for comparison against replay.
    fn append_mixed_entries(wal: &mut WriteAheadLog, n: u64) -> Vec<WalEntry> {
        let mut appended = Vec::new();
        for i in 0..n {
            let seq = wal.next_sequence();
            let entry = match i % 4 {
                0 => WalEntry::CreateQueue {
                    queue_id: [i as u8; 32],
                    capacity: i as usize + 1,
                    sequence: seq,
                },
                1 => WalEntry::Enqueue {
                    queue_id: [i as u8; 32],
                    entry_hash: [i as u8 + 1; 32],
                    data: (0..=i as u8).collect(),
                    sequence: seq,
                },
                2 => WalEntry::Dequeue {
                    queue_id: [i as u8; 32],
                    position: i as usize,
                    sequence: seq,
                },
                _ => WalEntry::Checkpoint {
                    queue_id: [i as u8; 32],
                    root: [i as u8 * 3; 32],
                    sequence: seq,
                },
            };
            wal.append(&entry).unwrap();
            appended.push(entry);
        }
        appended
    }

    /// Append/replay conserves the record sequence: a mixed log of all
    /// four entry kinds replays as EXACTLY the appended sequence (order
    /// and content), across a crash (writer dropped without `close`),
    /// and the reopened WAL continues numbering after the last record.
    /// The negative poles of this conservation — a truncated or
    /// corrupted log — are the two tests below.
    #[test]
    fn prop_append_replay_conserves_the_record_sequence() {
        let path = temp_wal_path("conserve_sequence");
        cleanup(&path);

        let appended = {
            let mut wal = WriteAheadLog::open(path.clone()).unwrap();
            let appended = append_mixed_entries(&mut wal, 20);
            wal.sync().unwrap();
            appended
        }; // Writer dropped without close() — simulated crash.

        let wal = WriteAheadLog::open(path.clone()).unwrap();
        assert_eq!(
            wal.replay().unwrap(),
            appended,
            "replay must return exactly the appended sequence"
        );
        assert_eq!(
            wal.next_sequence(),
            20,
            "the reopened WAL must continue numbering after the last record"
        );
        wal.destroy().unwrap();
    }

    /// A truncated log is detected: cutting into the final record's
    /// bytes (several cut depths) replays as EXACTLY the intact prefix —
    /// the torn record is never hallucinated and no earlier record is
    /// disturbed. Detection is CHECKSUM-based, not newline-based: a
    /// cut of exactly 1 byte removes only the trailing `\n`, leaves the
    /// payload+checksum intact, and the record correctly still replays
    /// (pinned below). Non-vacuity: the same log replays all 5 records
    /// before the cut.
    #[test]
    fn prop_truncated_tail_yields_exactly_the_intact_prefix() {
        // cut=1: only the line terminator is lost — the record survives.
        {
            let path = temp_wal_path("truncated_tail_newline_only");
            cleanup(&path);
            let appended = {
                let mut wal = WriteAheadLog::open(path.clone()).unwrap();
                let appended = append_mixed_entries(&mut wal, 5);
                wal.sync().unwrap();
                wal.close().unwrap();
                appended
            };
            let bytes = fs::read(&path).unwrap();
            assert_eq!(bytes.last(), Some(&b'\n'));
            fs::write(&path, &bytes[..bytes.len() - 1]).unwrap();
            let wal = WriteAheadLog::open(path.clone()).unwrap();
            assert_eq!(
                wal.replay().unwrap(),
                appended,
                "a lost trailing newline must not lose the (checksum-intact) record"
            );
            wal.destroy().unwrap();
        }

        // Cuts that tear into the final record's checksum/payload bytes.
        for &cut in &[2usize, 25, 150] {
            let path = temp_wal_path(&format!("truncated_tail_{cut}"));
            cleanup(&path);

            let appended = {
                let mut wal = WriteAheadLog::open(path.clone()).unwrap();
                let mut appended = append_mixed_entries(&mut wal, 4);
                // Final record: a wide Enqueue so every cut depth stays
                // within its line.
                let entry = WalEntry::Enqueue {
                    queue_id: [0xF0; 32],
                    entry_hash: [0xF1; 32],
                    data: vec![0x5A; 40],
                    sequence: wal.next_sequence(),
                };
                wal.append(&entry).unwrap();
                appended.push(entry);
                wal.sync().unwrap();
                wal.close().unwrap();
                appended
            };

            // Non-vacuity: intact log replays all 5 records.
            {
                let wal = WriteAheadLog::open(path.clone()).unwrap();
                assert_eq!(wal.replay().unwrap(), appended);
            }

            // Tear the tail: drop the last `cut` bytes mid-line.
            let bytes = fs::read(&path).unwrap();
            fs::write(&path, &bytes[..bytes.len() - cut]).unwrap();

            let wal = WriteAheadLog::open(path.clone()).unwrap();
            assert_eq!(
                wal.replay().unwrap(),
                appended[..4],
                "cut={cut}: replay must be exactly the intact prefix — the torn \
                 record must not be hallucinated"
            );
            wal.destroy().unwrap();
        }
    }

    /// A corrupted record is detected by its checksum: flipping one hex
    /// character in a MIDDLE record — in its payload or in its checksum
    /// field — drops EXACTLY that record on replay, while every other
    /// record survives intact. (A payload flip still parses as a
    /// well-formed record for a different queue_id; only the checksum
    /// refuses it — that is the tooth being tested.)
    #[test]
    fn prop_corrupted_record_dropped_others_survive() {
        for target in ["payload", "checksum"] {
            let path = temp_wal_path(&format!("corrupt_{target}"));
            cleanup(&path);

            let appended = {
                let mut wal = WriteAheadLog::open(path.clone()).unwrap();
                let appended = append_mixed_entries(&mut wal, 5);
                wal.sync().unwrap();
                wal.close().unwrap();
                appended
            };

            // Flip one hex char in line index 2.
            let text = fs::read_to_string(&path).unwrap();
            let mut lines: Vec<String> = text.lines().map(|l| l.to_string()).collect();
            assert_eq!(lines.len(), 5);
            let line = &lines[2];
            let pos = match target {
                // Char 4 sits inside the queue_id hex field.
                "payload" => 4,
                // The last char sits inside the checksum field.
                _ => line.len() - 1,
            };
            let old = line.as_bytes()[pos];
            let new = if old == b'0' { b'1' } else { b'0' };
            let mut mutated = line.clone().into_bytes();
            mutated[pos] = new;
            lines[2] = String::from_utf8(mutated).unwrap();
            fs::write(&path, format!("{}\n", lines.join("\n"))).unwrap();

            let mut expected = appended.clone();
            expected.remove(2);

            let wal = WriteAheadLog::open(path.clone()).unwrap();
            assert_eq!(
                wal.replay().unwrap(),
                expected,
                "{target} corruption: exactly the corrupted record must be \
                 dropped; its neighbors must survive"
            );
            wal.destroy().unwrap();
        }
    }
}
