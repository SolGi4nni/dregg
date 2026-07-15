//! Durable state — the registries survive a process restart.
//!
//! The retired gateway held every site, machine, and domain in an in-RAM
//! `Mutex<BTreeMap>`: a restart lost every tenant. Here each mutating store writes
//! through a **persistence seam** so its records are reloaded on the next boot.
//!
//! Two postures per store, injected (never a hidden global):
//!
//! * a **null** backend ([`NullMachines`] / [`NullSites`]) — in-RAM only, the dev /
//!   single-box default and what the pure unit tests use; and
//! * a **file** backend ([`JsonlMachines`] / [`JsonlSites`]) — an append-only op log
//!   (`JSONL`: one JSON op per line). Every create / state-change / delete appends one
//!   line and `fsync`s; boot replays the log into the last-writer-wins record set. A
//!   torn final line from a crash mid-append is skipped on load, not fatal — the store
//!   comes up on the last durable record.
//!
//! An append-only log (rather than rewriting a snapshot on every write) keeps a write
//! O(1) in the size of the change, and a crash can only ever lose the in-flight op, not
//! corrupt prior state. Compaction (fold the log to a snapshot) is a future operational
//! step; a log that grows with churn is the accepted tradeoff for crash-simplicity.

use std::fs::{File, OpenOptions};
use std::io::{BufRead, BufReader, Write};
use std::path::{Path, PathBuf};
use std::sync::Mutex;

use serde::{Deserialize, Serialize};

use crate::machines::Machine;
use crate::microsite::Microsite;
use crate::util::lock;

// ─────────────────────────────── machines ───────────────────────────────

/// The machine-store durability seam. A store writes through it on every mutation and
/// reloads from [`load`](MachinePersistence::load) at construction.
pub trait MachinePersistence: Send + Sync {
    /// The durable machine set to seed a fresh store with (last-writer-wins).
    fn load(&self) -> Vec<Machine>;
    /// Record a create / update (an upsert by id).
    fn upsert(&self, machine: &Machine);
    /// Record a destroy.
    fn remove(&self, id: &str);
}

/// In-RAM only: nothing is persisted (the dev / test default).
pub struct NullMachines;

impl MachinePersistence for NullMachines {
    fn load(&self) -> Vec<Machine> {
        Vec::new()
    }
    fn upsert(&self, _machine: &Machine) {}
    fn remove(&self, _id: &str) {}
}

#[derive(Serialize, Deserialize)]
#[serde(tag = "op", rename_all = "snake_case")]
enum MachineOp {
    Upsert { machine: Box<Machine> },
    Remove { id: String },
}

/// A file-backed append-only machine log.
pub struct JsonlMachines {
    file: Mutex<File>,
    path: PathBuf,
}

impl JsonlMachines {
    /// Open (creating if absent) the append log at `path`. Prior records are replayed
    /// by [`load`](MachinePersistence::load).
    pub fn open(path: impl AsRef<Path>) -> std::io::Result<JsonlMachines> {
        let path = path.as_ref().to_path_buf();
        let file = OpenOptions::new().create(true).append(true).open(&path)?;
        Ok(JsonlMachines {
            file: Mutex::new(file),
            path,
        })
    }

    fn append(&self, op: &MachineOp) {
        append_line(&self.file, op);
    }
}

impl MachinePersistence for JsonlMachines {
    fn load(&self) -> Vec<Machine> {
        let mut by_id: std::collections::BTreeMap<String, Machine> =
            std::collections::BTreeMap::new();
        for op in replay::<MachineOp>(&self.path) {
            match op {
                MachineOp::Upsert { machine } => {
                    by_id.insert(machine.id.clone(), *machine);
                }
                MachineOp::Remove { id } => {
                    by_id.remove(&id);
                }
            }
        }
        by_id.into_values().collect()
    }
    fn upsert(&self, machine: &Machine) {
        self.append(&MachineOp::Upsert {
            machine: Box::new(machine.clone()),
        });
    }
    fn remove(&self, id: &str) {
        self.append(&MachineOp::Remove { id: id.to_string() });
    }
}

// ──────────────────────────────── sites ─────────────────────────────────

/// The site-registry durability seam.
pub trait SitePersistence: Send + Sync {
    /// The durable sites to seed a fresh registry with.
    fn load(&self) -> Vec<Microsite>;
    /// Record a publish (an upsert by name).
    fn publish(&self, site: &Microsite);
    /// Record a takedown.
    fn remove(&self, name: &str);
}

/// In-RAM only.
pub struct NullSites;

impl SitePersistence for NullSites {
    fn load(&self) -> Vec<Microsite> {
        Vec::new()
    }
    fn publish(&self, _site: &Microsite) {}
    fn remove(&self, _name: &str) {}
}

#[derive(Serialize, Deserialize)]
#[serde(tag = "op", rename_all = "snake_case")]
enum SiteOp {
    Publish { site: Box<Microsite> },
    Remove { name: String },
}

/// A file-backed append-only site log.
pub struct JsonlSites {
    file: Mutex<File>,
    path: PathBuf,
}

impl JsonlSites {
    /// Open (creating if absent) the append log at `path`.
    pub fn open(path: impl AsRef<Path>) -> std::io::Result<JsonlSites> {
        let path = path.as_ref().to_path_buf();
        let file = OpenOptions::new().create(true).append(true).open(&path)?;
        Ok(JsonlSites {
            file: Mutex::new(file),
            path,
        })
    }
}

impl SitePersistence for JsonlSites {
    fn load(&self) -> Vec<Microsite> {
        let mut by_name: std::collections::BTreeMap<String, Microsite> =
            std::collections::BTreeMap::new();
        for op in replay::<SiteOp>(&self.path) {
            match op {
                SiteOp::Publish { site } => {
                    by_name.insert(site.name.clone(), *site);
                }
                SiteOp::Remove { name } => {
                    by_name.remove(&name);
                }
            }
        }
        by_name.into_values().collect()
    }
    fn publish(&self, site: &Microsite) {
        append_line(
            &self.file,
            &SiteOp::Publish {
                site: Box::new(site.clone()),
            },
        );
    }
    fn remove(&self, name: &str) {
        append_line(
            &self.file,
            &SiteOp::Remove {
                name: name.to_string(),
            },
        );
    }
}

// ─────────────────────────────── shared io ──────────────────────────────

/// Serialize `op` as one JSON line, append, and flush+`sync_data` so the record is
/// durable before the mutating call returns. A serialize/IO failure is logged to
/// stderr and dropped — persistence is best-effort-durable, never a request-failing
/// path (the in-RAM store remains authoritative for the live process).
fn append_line<T: Serialize>(file: &Mutex<File>, op: &T) {
    let mut line = match serde_json::to_vec(op) {
        Ok(v) => v,
        Err(e) => {
            eprintln!("host-gateway: persist serialize failed: {e}");
            return;
        }
    };
    line.push(b'\n');
    let mut guard = lock(file);
    if let Err(e) = guard.write_all(&line).and_then(|()| guard.sync_data()) {
        eprintln!("host-gateway: persist write failed: {e}");
    }
}

/// Replay an append log, yielding each parseable op in order. A blank or unparseable
/// line (e.g. a torn final record from a crash mid-append) is skipped — the store
/// recovers to the last durable op rather than refusing to boot.
fn replay<T: for<'de> Deserialize<'de>>(path: &Path) -> Vec<T> {
    let Ok(file) = File::open(path) else {
        return Vec::new();
    };
    let mut ops = Vec::new();
    for line in BufReader::new(file).lines() {
        let Ok(line) = line else { break };
        let line = line.trim();
        if line.is_empty() {
            continue;
        }
        match serde_json::from_str::<T>(line) {
            Ok(op) => ops.push(op),
            Err(_) => continue,
        }
    }
    ops
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::machines::{MachineConfig, MachineState};
    use crate::microsite::Microsite;

    fn tmp(name: &str) -> PathBuf {
        let mut p = std::env::temp_dir();
        p.push(format!(
            "host-gateway-persist-{}-{}.jsonl",
            name,
            crate::util::request_id()
        ));
        p
    }

    fn machine(id: &str, owner: &str, state: MachineState) -> Machine {
        Machine {
            id: id.into(),
            name: id.into(),
            app: "app".into(),
            owner: owner.into(),
            state,
            region: "iad".into(),
            config: MachineConfig::default(),
        }
    }

    #[test]
    fn machine_log_replays_last_writer_wins_and_honours_removes() {
        let path = tmp("mach");
        {
            let log = JsonlMachines::open(&path).unwrap();
            log.upsert(&machine("mch_a", "alice", MachineState::Started));
            log.upsert(&machine("mch_b", "bob", MachineState::Started));
            // Update a's state, then delete b.
            log.upsert(&machine("mch_a", "alice", MachineState::Stopped));
            log.remove("mch_b");
        }
        // A FRESH handle over the same path recovers durable state.
        let reopened = JsonlMachines::open(&path).unwrap();
        let mut loaded = reopened.load();
        loaded.sort_by(|a, b| a.id.cmp(&b.id));
        assert_eq!(loaded.len(), 1, "b was removed");
        assert_eq!(loaded[0].id, "mch_a");
        assert_eq!(loaded[0].state, MachineState::Stopped, "last write wins");
        let _ = std::fs::remove_file(&path);
    }

    #[test]
    fn a_torn_final_line_is_skipped_not_fatal() {
        let path = tmp("torn");
        {
            let log = JsonlMachines::open(&path).unwrap();
            log.upsert(&machine("mch_ok", "alice", MachineState::Started));
        }
        // Simulate a crash mid-append: a partial JSON line with no newline.
        {
            let mut f = OpenOptions::new().append(true).open(&path).unwrap();
            f.write_all(br#"{"op":"upsert","machine":{"id":"mch_tor"#)
                .unwrap();
        }
        let loaded = JsonlMachines::open(&path).unwrap().load();
        assert_eq!(
            loaded.len(),
            1,
            "the torn record is skipped, prior state survives"
        );
        assert_eq!(loaded[0].id, "mch_ok");
        let _ = std::fs::remove_file(&path);
    }

    #[test]
    fn site_log_round_trips() {
        let path = tmp("site");
        {
            let log = JsonlSites::open(&path).unwrap();
            log.publish(&Microsite::new("blog", "alice").with("/index.html", "<h1>hi</h1>"));
            log.publish(&Microsite::new("shop", "bob").with("/index.html", "shop"));
            log.remove("shop");
        }
        let loaded = JsonlSites::open(&path).unwrap().load();
        assert_eq!(loaded.len(), 1);
        assert_eq!(loaded[0].name, "blog");
        assert_eq!(loaded[0].serve("/").body, b"<h1>hi</h1>");
        let _ = std::fs::remove_file(&path);
    }
}
