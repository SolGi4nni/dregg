//! `dregg-node init` — make a data directory a RUNNABLE node.
//!
//! Until 2026-07-26 `init` wrote two things: an empty directory and a fresh
//! random `node.key`. Then `run` refused to start:
//!
//! ```text
//! ERROR blocklace requires consensus_genesis_unix_seconds + consensus_time_mode
//!       in the shared genesis.json; refusing an implicit clock policy
//! ```
//!
//! That gate (landed 2026-07-22) is right: a consensus clock policy must be a
//! published, shared coordinate, never something a node invents at boot. The
//! defect was that `init` never published one — README door A ("`init`, then
//! `run`") had not opened since the gate landed, and the failure surfaced only
//! after ~13 seconds of starbridge seeding, which reads as a hang.
//!
//! There was a second, quieter defect stacked on it. `init`'s random `node.key`
//! is not a member of any committee, so even a data dir hand-fed a genesis.json
//! booted and then failed EVERY durable commit with "faithful note-root
//! attestation has no valid author signature". The key and the committee have to
//! be minted together or they do not match.
//!
//! So `init` now mints a one-validator chain THROUGH THE SAME CODE the documented
//! `dregg-node genesis` command runs — [`crate::genesis::run_genesis`] with
//! `validators = 1`, straight into the data dir — and installs that committee
//! member's key as `node.key`. One implementation of genesis, not two; the clock
//! policy is a real published `consensus-time-v1` coordinate, not an implicit
//! one; and the node key IS the committee.
//!
//! What `init` will NOT do: overwrite. A `genesis.json` already in the directory
//! is left exactly as it is, and a `node.key` without a `genesis.json` is refused
//! rather than replaced — that is the shape of a validator waiting for its
//! federation's committee descriptor (`gen-validator-key` → operator admits you →
//! `join`), and silently handing it a private solo chain instead would look like
//! success while it talked to nobody.

use std::path::Path;

/// Epoch length + checkpoint interval for the solo chain `init` mints. These are
/// the defaults `Command::Genesis` declares, so `init` and `genesis --validators 1`
/// produce the same shape of chain.
const SOLO_EPOCH_LENGTH: u64 = 1000;
const SOLO_CHECKPOINT_INTERVAL: u64 = 100;

/// Initialize a data directory into a node that `dregg-node run` will actually start.
pub(crate) fn init_node(data_dir: &str) {
    let data_path = crate::expand_path(data_dir);
    let genesis_path = data_path.join("genesis.json");
    let key_path = data_path.join("node.key");

    if genesis_path.exists() {
        println!(
            "This data directory already carries a chain: {}",
            genesis_path.display()
        );
        println!("Leaving it alone (init never overwrites a genesis.json or a node.key).");
        if !key_path.exists() {
            println!();
            println!("  It has no node.key, though. If this is a committee genesis.json you were");
            println!("  sent, generate your key and get admitted:");
            println!("    dregg-node gen-validator-key --data-dir {data_dir}");
        } else {
            println!();
            println!("Start the node with:");
            println!("  dregg-node run --data-dir {data_dir}");
        }
        return;
    }

    if key_path.exists() {
        eprintln!(
            "error: {} holds a node.key but no genesis.json.",
            data_path.display()
        );
        eprintln!();
        eprintln!("A node key on its own cannot start a chain, and this one is not a member of");
        eprintln!("any committee. Two ways forward, and they are different chains:");
        eprintln!();
        eprintln!("  JOINING a federation — you are waiting for its committee descriptor. Ask the");
        eprintln!("  operator to admit your public key, drop the genesis.json they send you into");
        eprintln!("  {}, then:", data_path.display());
        eprintln!("    dregg-node join --bootstrap <host:9420> --data-dir {data_dir}");
        eprintln!();
        eprintln!("  A SOLO chain of your own — this key is not in it and will be replaced:");
        eprintln!("    rm {}", key_path.display());
        eprintln!("    dregg-node init --data-dir {data_dir}");
        std::process::exit(1);
    }

    // Mint the chain. `run_genesis` creates the directory, writes genesis.json +
    // the `.devnet` marker + `node-0.key` + the deterministic faucet / issuer-well
    // / fee-well / agent keys the boot-time starbridge seeding needs. Writing it
    // straight into the data dir (rather than copying two files out of a staging
    // dir, which is what every doc told operators to do) is why all ten starbridge
    // factory cells now get seeded instead of skipped for a missing agent key.
    crate::genesis::run_genesis(
        1,
        SOLO_EPOCH_LENGTH,
        SOLO_CHECKPOINT_INTERVAL,
        data_path.as_path(),
    );

    // The committee's sole member key becomes this node's key. Renamed, not
    // copied: one secret, one path.
    let committee_key = data_path.join("node-0.key");
    if let Err(e) = std::fs::rename(&committee_key, &key_path) {
        eprintln!(
            "error: failed to install the committee key as {}: {e}",
            key_path.display()
        );
        std::process::exit(1);
    }

    let pk_hex = match public_key_hex(&key_path) {
        Ok(hex) => hex,
        Err(e) => {
            eprintln!("error: could not read back {}: {e}", key_path.display());
            std::process::exit(1);
        }
    };

    println!();
    println!(
        "Initialized dregg-node data directory: {}",
        data_path.display()
    );
    println!("Node public key: {pk_hex}");
    println!("  (this key IS the committee — node.key is the renamed node-0.key above)");
    println!();
    println!("This is a SOLO chain of one validator, yours, with a devnet faucet supply.");
    println!("To join an EXISTING federation instead, use that federation's genesis.json:");
    println!("  dregg-node join --bootstrap <host:9420> --data-dir {data_dir}");
    println!();
    println!("Start the node with:");
    println!("  dregg-node run --data-dir {data_dir} --enable-faucet");
}

/// Read a raw 32-byte ed25519 seed back and render its public key as hex.
fn public_key_hex(key_path: &Path) -> Result<String, String> {
    let bytes = std::fs::read(key_path).map_err(|e| e.to_string())?;
    let seed: [u8; 32] = bytes
        .as_slice()
        .try_into()
        .map_err(|_| format!("expected a 32-byte key, found {} bytes", bytes.len()))?;
    let signing_key = ed25519_dalek::SigningKey::from_bytes(&seed);
    Ok(signing_key
        .verifying_key()
        .to_bytes()
        .iter()
        .map(|b| format!("{b:02x}"))
        .collect())
}

#[cfg(test)]
mod tests {
    use super::*;

    /// The whole point: after `init`, the file `run`'s blocklace gate reads
    /// exists and carries BOTH fields it refuses to start without.
    #[test]
    fn init_writes_a_genesis_with_an_explicit_consensus_clock_policy() {
        let tmp = tempfile::tempdir().expect("tempdir");
        let dir = tmp.path().join("fresh");
        init_node(dir.to_str().expect("utf-8 path"));

        let raw = std::fs::read_to_string(dir.join("genesis.json")).expect("genesis.json written");
        let genesis: serde_json::Value = serde_json::from_str(&raw).expect("valid JSON");
        assert!(
            genesis["consensus_genesis_unix_seconds"].is_i64(),
            "the blocklace gate demands a signed-integer consensus_genesis_unix_seconds"
        );
        assert!(
            genesis["consensus_time_mode"].is_string(),
            "the blocklace gate demands an explicit consensus_time_mode"
        );
        assert_eq!(
            genesis["validators"].as_array().map(Vec::len),
            Some(1),
            "init mints a committee of one"
        );
    }

    /// `node.key` is the committee member's key, not an unrelated random one —
    /// the difference between a node that commits and a node that boots and then
    /// fails every durable commit for want of a valid author signature.
    #[test]
    fn the_installed_node_key_is_the_committee_member() {
        let tmp = tempfile::tempdir().expect("tempdir");
        let dir = tmp.path().join("fresh");
        init_node(dir.to_str().expect("utf-8 path"));

        let pk = public_key_hex(&dir.join("node.key")).expect("read back node.key");
        let raw = std::fs::read_to_string(dir.join("genesis.json")).expect("genesis.json written");
        let genesis: serde_json::Value = serde_json::from_str(&raw).expect("valid JSON");
        assert_eq!(
            genesis["validators"][0]["public_key"].as_str(),
            Some(pk.as_str()),
            "node.key must be the sole committee member's key"
        );
        assert!(
            !dir.join("node-0.key").exists(),
            "the staging name is renamed, not duplicated — one secret, one path"
        );
    }

    /// A directory that already carries a chain is left byte-for-byte alone.
    #[test]
    fn init_never_overwrites_an_existing_genesis() {
        let tmp = tempfile::tempdir().expect("tempdir");
        let dir = tmp.path().join("fresh");
        init_node(dir.to_str().expect("utf-8 path"));

        let before = std::fs::read(dir.join("genesis.json")).expect("genesis.json");
        let key_before = std::fs::read(dir.join("node.key")).expect("node.key");
        init_node(dir.to_str().expect("utf-8 path"));
        assert_eq!(
            before,
            std::fs::read(dir.join("genesis.json")).expect("genesis.json"),
            "a second init must not re-roll the chain"
        );
        assert_eq!(
            key_before,
            std::fs::read(dir.join("node.key")).expect("node.key"),
            "a second init must not replace the node key"
        );
    }
}
