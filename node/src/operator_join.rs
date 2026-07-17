//! The operator onboarding dance: `gen-validator-key`, `join`, `add-validator`.
//!
//! This is the slick, reusable path an operator (or a homelab) walks to fold a
//! new `dregg-node` into a federation. It is grounded in the REAL committee
//! machinery, not a parallel abstraction:
//!
//! * a federation's identity is a *commitment to its committee* — the
//!   coupled-core HYBRID roster: `federation_id =
//!   derive_federation_id_hybrid_with_epoch(sorted committee, epoch)` over each
//!   member's `hybrid_id_commitment(ed25519, ml_dsa)`
//!   ([`dregg_federation::derive_federation_id_hybrid_with_epoch`], the exact
//!   function `dregg-node genesis` writes and the running node re-derives). A
//!   legacy federation with no enrolled ML-DSA roster falls back to the
//!   Ed25519-only [`dregg_federation::derive_federation_id_with_epoch`]; a reroll
//!   must speak the SAME projection or it diverges from genesis;
//! * the committee lives in `genesis.json` (`validators[].public_key` + the
//!   derived `federation_id` + `threshold`), every node deriving the same id
//!   from the same committee;
//! * the BFT `threshold` is the strict blocklace supermajority
//!   [`dregg_federation::quorum_threshold`] (`⌊2n/3⌋ + 1`): n=1→1, n=2→2,
//!   **n=3→3**, n=4→3, n=5→4.
//!
//! **The PRIMARY add path is LIVE, not a re-roll** (docs/guide/
//! FEDERATION-JOIN.md): a candidate's Join proposal goes on-chain
//! (`join` auto-proposes; `propose-epoch-transition` proposes on their
//! behalf), each committee operator admits with [`approve_membership`]
//! (`approve-membership` / `POST /membership/approve`), and at quorum the
//! committee advances live — chain continues, `federation_id` unchanged,
//! nothing restarts, and the amendment survives reboots
//! (`committee_replay::derive_from_lace`). The [`add_validator`] re-roll
//! below CHANGES the `federation_id` (new descriptor to every node +
//! coordinated restart) and remains only for bootstrapping a brand-new
//! federation and for disaster recovery.
//!
//! The three verbs:
//!
//! * [`gen_validator_key`] — generate (or read) this box's validator keypair and
//!   print its PUBLIC key. The operator hands that key to whoever runs
//!   `add-validator`.
//! * [`add_validator`] — the authority op: fold one or more validator pubkeys
//!   into the committee in this node's `genesis.json`, recompute the
//!   `federation_id` + `threshold`, and write the new committee descriptor. Run
//!   it on a federation node's data dir (filesystem access to the node IS the
//!   authority); distribute the result and restart.
//! * [`prepare_join`] — pre-flight a follower/validator join: ensure the data
//!   dir + `node.key` exist (auto-generating the key, printing the pubkey) and a
//!   committee `genesis.json` is present, then hand the daemon the bootstrap
//!   peer. The node syncs the blocklace from the bootstrap and — if its key is
//!   in the committee — votes; if not, it auto-proposes membership
//!   (`propose_join_if_needed`) and follows until an operator admits it.

use std::path::{Path, PathBuf};

use dregg_federation::frost::MlDsaPublicKey;
use dregg_federation::{
    derive_federation_id_hybrid_with_epoch, derive_federation_id_with_epoch, quorum_threshold,
};
use dregg_types::PublicKey;

/// One committee member as the reroll path sees it: its Ed25519 validator key and
/// its OPTIONAL published ML-DSA-65 key. The ML-DSA key is what makes the member's
/// canonical id the COUPLED-CORE `hybrid_id_commitment(ed, ml_dsa)` rather than the
/// bare Ed25519 key; genesis publishes it for every validator
/// (`genesis.rs` → `derive_federation_id_hybrid_with_epoch`), so a reroll that
/// dropped it would recompute a DIFFERENT federation_id than genesis and the
/// running node (which both re-derive over the hybrid roster).
#[derive(Clone, Debug)]
pub struct CommitteeMember {
    /// The validator's Ed25519 public key.
    pub ed: [u8; 32],
    /// The validator's published ML-DSA-65 key, when the federation is hybrid.
    /// `None` only for a legacy Ed25519-only federation (no enrolled PQ roster).
    pub ml_dsa: Option<MlDsaPublicKey>,
}

impl PartialEq for CommitteeMember {
    fn eq(&self, other: &Self) -> bool {
        self.ed == other.ed
    }
}
impl Eq for CommitteeMember {}

/// Parse an ML-DSA-65 public key from hex (FIPS 204 = `ML_DSA_PK_LEN` bytes).
pub fn parse_ml_dsa_pubkey(hex: &str) -> Result<MlDsaPublicKey, String> {
    let s = hex.trim();
    if !s.is_ascii() || s.len() % 2 != 0 {
        return Err(format!(
            "not hex ({} chars); an ML-DSA-65 public key is {} bytes = {} hex chars",
            s.len(),
            dregg_pq::ML_DSA_PK_LEN,
            dregg_pq::ML_DSA_PK_LEN * 2
        ));
    }
    let mut bytes = Vec::with_capacity(s.len() / 2);
    for i in 0..s.len() / 2 {
        bytes.push(
            u8::from_str_radix(s.get(i * 2..i * 2 + 2).unwrap_or(""), 16)
                .map_err(|e| format!("non-hex byte: {e}"))?,
        );
    }
    let arr: [u8; dregg_pq::ML_DSA_PK_LEN] = bytes.try_into().map_err(|v: Vec<u8>| {
        format!(
            "wrong length: got {} bytes, ML-DSA-65 public key is {} bytes",
            v.len(),
            dregg_pq::ML_DSA_PK_LEN
        )
    })?;
    Ok(MlDsaPublicKey(arr))
}

/// Hex-encode a 32-byte value (lower-case, no prefix).
pub fn hex32(bytes: &[u8; 32]) -> String {
    bytes.iter().map(|b| format!("{b:02x}")).collect()
}

/// Decode a 64-char hex string into `[u8; 32]`.
fn hex_decode_32(s: &str) -> Option<[u8; 32]> {
    let s = s.trim();
    if s.len() != 64 {
        return None;
    }
    let mut bytes = [0u8; 32];
    for (i, byte) in bytes.iter_mut().enumerate() {
        *byte = u8::from_str_radix(s.get(i * 2..i * 2 + 2)?, 16).ok()?;
    }
    Some(bytes)
}

/// Parse a validator public key from hex AND verify it is a valid Ed25519 point.
///
/// A 64-hex string that is not a valid compressed Ed25519 public key is rejected
/// here rather than silently admitted into the committee (where it would make the
/// federation_id a commitment to an unusable "member" and could never sign).
pub fn parse_validator_pubkey(hex: &str) -> Result<[u8; 32], String> {
    let bytes = hex_decode_32(hex).ok_or_else(|| {
        format!(
            "not a 32-byte hex public key (expected 64 hex chars, got {:?})",
            hex.trim()
        )
    })?;
    // Reject a non-canonical / non-curve point: a real validator key must be a
    // verifiable Ed25519 public key.
    ed25519_dalek::VerifyingKey::from_bytes(&bytes)
        .map_err(|e| format!("hex is 32 bytes but not a valid Ed25519 public key: {e}"))?;
    Ok(bytes)
}

/// Read the raw 32-byte `node.key` seed from disk (the Ed25519 seed the ML-DSA-65
/// key is ALSO deterministically derived from).
fn seed_from_key_file(key_path: &Path) -> Result<[u8; 32], String> {
    let raw = std::fs::read(key_path)
        .map_err(|e| format!("cannot read key file {}: {e}", key_path.display()))?;
    if raw.len() != 32 {
        return Err(format!(
            "key file {} is {} bytes; a node.key is a raw 32-byte Ed25519 seed",
            key_path.display(),
            raw.len()
        ));
    }
    let mut seed = [0u8; 32];
    seed.copy_from_slice(&raw);
    Ok(seed)
}

/// Derive the validator public key from a raw 32-byte `node.key` seed file.
pub fn pubkey_from_key_file(key_path: &Path) -> Result<[u8; 32], String> {
    let seed = seed_from_key_file(key_path)?;
    let signing = ed25519_dalek::SigningKey::from_bytes(&seed);
    Ok(signing.verifying_key().to_bytes())
}

/// Generate a raw 32-byte node key at `key_path` (0600) and return the seed.
fn generate_key_seed(key_path: &Path) -> Result<[u8; 32], String> {
    let mut seed = [0u8; 32];
    getrandom::fill(&mut seed).map_err(|e| format!("getrandom failed: {e}"))?;
    std::fs::write(key_path, seed)
        .map_err(|e| format!("failed to write key file {}: {e}", key_path.display()))?;
    #[cfg(unix)]
    {
        use std::os::unix::fs::PermissionsExt;
        std::fs::set_permissions(key_path, std::fs::Permissions::from_mode(0o600))
            .map_err(|e| format!("failed to 0600 {}: {e}", key_path.display()))?;
    }
    Ok(seed)
}

/// Generate a raw 32-byte node key at `key_path` (0600) and return its pubkey.
fn generate_key_file(key_path: &Path) -> Result<[u8; 32], String> {
    let seed = generate_key_seed(key_path)?;
    let signing = ed25519_dalek::SigningKey::from_bytes(&seed);
    Ok(signing.verifying_key().to_bytes())
}

/// The outcome of folding one or more members into a committee.
#[derive(Clone, Debug)]
pub struct CommitteeReroll {
    /// The new committee, the genesis-writer order preserved with new members
    /// appended (the federation_id derivation sorts internally, so on-disk order
    /// is cosmetic). Each entry carries its ML-DSA key so the descriptor written
    /// back keeps every member's hybrid enrollment.
    pub committee: Vec<CommitteeMember>,
    /// Members that were requested but already present (skipped, not an error).
    pub already_present: Vec<[u8; 32]>,
    /// The recomputed federation id over the new committee + `epoch`.
    pub federation_id: [u8; 32],
    /// The recomputed BFT threshold (`quorum_threshold(committee.len())`).
    pub threshold: usize,
    /// The committee epoch the id was minted for (unchanged by a static re-roll).
    pub epoch: u64,
    /// Whether the id was derived over the HYBRID roster (`true`, every member
    /// carries an ML-DSA key) or the legacy Ed25519-only projection (`false`).
    pub hybrid: bool,
}

/// Fold `additions` into `existing`, returning the new committee + its derived
/// `federation_id` and `threshold`.
///
/// * Already-present additions are skipped (recorded in `already_present`), so
///   re-running with an overlapping set is idempotent rather than an error.
/// * If *every* addition is already present (nothing to do), this is an error —
///   the caller asked for a change that wouldn't change anything.
/// * The id derivation is the SAME projection genesis and the running node use:
///   [`derive_federation_id_hybrid_with_epoch`] over the committee's HYBRID member
///   ids (`hybrid_id_commitment(ed, ml_dsa)`) when every member carries an ML-DSA
///   key, falling back to the legacy Ed25519-only id
///   ([`derive_federation_id_with_epoch`]) when the federation has no enrolled PQ
///   roster at all. A MIXED committee — some members hybrid, some not — is an
///   ERROR rather than a silent Ed25519-only downgrade: the running node's
///   `set_federation_keys_hybrid` rejects a partial ML-DSA set, so producing such
///   a descriptor would strip the PQ binding off the whole committee. The caller
///   must supply the ML-DSA key for any new member of a hybrid federation.
pub fn reroll_committee(
    existing: &[CommitteeMember],
    additions: &[CommitteeMember],
    epoch: u64,
) -> Result<CommitteeReroll, String> {
    let mut committee: Vec<CommitteeMember> = existing.to_vec();
    let mut already_present: Vec<[u8; 32]> = Vec::new();
    let mut added_any = false;

    for m in additions {
        if committee.iter().any(|c| c.ed == m.ed) {
            if !already_present.contains(&m.ed) {
                already_present.push(m.ed);
            }
            continue;
        }
        committee.push(m.clone());
        added_any = true;
    }

    if !added_any {
        return Err(
            "nothing to add: every requested validator is already in the committee".to_string(),
        );
    }

    // Choose the SAME identity projection genesis / the running node use. All
    // members hybrid → coupled-core id; none hybrid → legacy Ed25519-only id;
    // a mixed set is refused (it would silently downgrade the committee's PQ
    // identity — `set_federation_keys_hybrid` drops a partial ML-DSA set).
    let with_ml = committee.iter().filter(|m| m.ml_dsa.is_some()).count();
    let ed_keys: Vec<PublicKey> = committee.iter().map(|m| PublicKey(m.ed)).collect();
    let (federation_id, hybrid) = if with_ml == committee.len() {
        let ml: Vec<MlDsaPublicKey> = committee
            .iter()
            .map(|m| m.ml_dsa.clone().expect("checked all present"))
            .collect();
        (
            derive_federation_id_hybrid_with_epoch(&ed_keys, &ml, epoch),
            true,
        )
    } else if with_ml == 0 {
        (derive_federation_id_with_epoch(&ed_keys, epoch), false)
    } else {
        return Err(format!(
            "mixed committee: {with_ml}/{} members carry an ML-DSA key. This is a HYBRID \
             federation; supply the ML-DSA public key for every new validator \
             (`--ml-dsa-pubkey <hex>`, printed by `gen-validator-key`). Refusing to write a \
             descriptor that silently downgrades the committee to Ed25519-only identity.",
            committee.len()
        ));
    };
    let threshold = quorum_threshold(committee.len());

    Ok(CommitteeReroll {
        committee,
        already_present,
        federation_id,
        threshold,
        epoch,
        hybrid,
    })
}

/// Read the committee (`validators[].public_key` + optional
/// `validators[].ml_dsa_public_key`) + epoch from a parsed `genesis.json`.
/// Returns `(committee, epoch)`. Malformed validator entries are surfaced as an
/// error rather than silently dropped (a committee we can't read exactly must not
/// be re-rolled).
///
/// The ML-DSA key is preserved so the reroll re-derives the federation_id over the
/// SAME hybrid roster genesis committed to — dropping it would recompute a
/// divergent id and strip the committee's PQ enrollment. A validator whose
/// `ml_dsa_public_key` is present but undecodable is an error (a committee we
/// cannot read exactly), not a silent Ed25519-only fallback.
fn committee_from_genesis(
    genesis: &serde_json::Value,
) -> Result<(Vec<CommitteeMember>, u64), String> {
    let epoch = genesis
        .get("committee_epoch")
        .and_then(|v| v.as_u64())
        .unwrap_or(0);
    let validators = genesis
        .get("validators")
        .and_then(|v| v.as_array())
        .ok_or("genesis.json has no `validators` array")?;
    let mut committee = Vec::with_capacity(validators.len());
    for (i, v) in validators.iter().enumerate() {
        let pk_hex = v
            .get("public_key")
            .and_then(|p| p.as_str())
            .ok_or_else(|| format!("validator[{i}] has no string `public_key`"))?;
        let ed = hex_decode_32(pk_hex)
            .ok_or_else(|| format!("validator[{i}].public_key is not 32-byte hex"))?;
        let ml_dsa = match v.get("ml_dsa_public_key").and_then(|p| p.as_str()) {
            Some(h) => Some(parse_ml_dsa_pubkey(h).map_err(|e| {
                format!("validator[{i}].ml_dsa_public_key is present but undecodable: {e}")
            })?),
            None => None,
        };
        committee.push(CommitteeMember { ed, ml_dsa });
    }
    Ok((committee, epoch))
}

// =============================================================================
// gen-validator-key
// =============================================================================

/// Generate (or read) this box's validator keypair and print its public key.
///
/// Idempotent: if `node.key` already exists in the data dir its pubkey is read
/// and printed; otherwise a fresh 32-byte seed is generated (0600) first.
pub fn gen_validator_key(data_dir: &str, json: bool) -> Result<(), String> {
    let data_path = expand_path(data_dir);
    std::fs::create_dir_all(&data_path)
        .map_err(|e| format!("failed to create data dir {}: {e}", data_path.display()))?;
    let key_path = data_path.join("node.key");

    let (generated, seed) = if key_path.exists() {
        (false, seed_from_key_file(&key_path)?)
    } else {
        let seed = generate_key_seed(&key_path)?;
        (true, seed)
    };
    let signing = ed25519_dalek::SigningKey::from_bytes(&seed);
    let pubkey = signing.verifying_key().to_bytes();
    let pk_hex = hex32(&pubkey);
    // HYBRID-PQ: derive this box's ML-DSA-65 key DETERMINISTICALLY from the same
    // 32-byte node.key seed — exactly as `genesis.rs` does for a generated
    // committee — and publish the public key. The operator threads it into
    // `add-validator --ml-dsa-pubkey` so the committee identity stays the
    // coupled-core hybrid roster (the reroll re-derives the same federation_id
    // genesis and the running node do).
    let (ml_dsa_pk, _sk) = dregg_federation::frost::MlDsaSigningKey::from_seed(&seed);
    let ml_dsa_hex: String = ml_dsa_pk.0.iter().map(|b| format!("{b:02x}")).collect();

    if json {
        let j = serde_json::json!({
            "public_key": pk_hex,
            "ml_dsa_public_key": ml_dsa_hex,
            "key_file": key_path.display().to_string(),
            "generated": generated,
        });
        println!("{}", serde_json::to_string_pretty(&j).unwrap());
        return Ok(());
    }

    if generated {
        println!("Generated a fresh validator keypair.");
    } else {
        println!("Validator keypair already present (reusing it).");
    }
    println!("  Key file (secret, 0600): {}", key_path.display());
    println!();
    println!("  Validator public key (Ed25519):");
    println!("    {pk_hex}");
    println!();
    println!("  Validator public key (ML-DSA-65, post-quantum half):");
    println!("    {ml_dsa_hex}");
    println!();
    println!("Hand BOTH public keys to the federation operator. They admit you with:");
    println!("    dregg-node add-validator --pubkey {pk_hex} --ml-dsa-pubkey {ml_dsa_hex}");
    println!("(A legacy Ed25519-only federation omits --ml-dsa-pubkey.)");
    println!("…then send you back the resulting genesis.json so you can `dregg-node join`.");
    Ok(())
}

// =============================================================================
// add-validator
// =============================================================================

/// Fold one or more validator pubkeys into this node's committee.
///
/// Reads `genesis.json` from the data dir (the running federation node's
/// committee), recomputes `federation_id` + `threshold`, and writes the updated
/// descriptor back to `genesis.json` (plus a content-named sibling
/// `genesis-<fedid8>.json` for distribution). The node's own filesystem access
/// to its data dir IS the authority — there is no remote self-admit (that would
/// defeat BFT).
pub fn add_validator(
    data_dir: &str,
    pubkey_hexes: &[String],
    ml_dsa_pubkey_hexes: &[String],
    json: bool,
) -> Result<(), String> {
    let data_path = expand_path(data_dir);
    let genesis_path = data_path.join("genesis.json");
    if !genesis_path.exists() {
        return Err(format!(
            "no genesis.json in {} — point --data-dir at a federation node's data dir, or \
             generate a committee first with `dregg-node genesis`. (A pure-solo node with no \
             genesis has no committee to extend.)",
            data_path.display()
        ));
    }

    // Each `--ml-dsa-pubkey` pairs POSITIONALLY with the `--pubkey` at the same
    // index. Supply either none (a legacy Ed25519-only federation) or exactly one
    // per added validator (a hybrid federation) — a partial set can't be aligned.
    if !ml_dsa_pubkey_hexes.is_empty() && ml_dsa_pubkey_hexes.len() != pubkey_hexes.len() {
        return Err(format!(
            "{} --pubkey but {} --ml-dsa-pubkey: pass one --ml-dsa-pubkey per --pubkey \
             (positionally aligned), or none for a legacy Ed25519-only federation.",
            pubkey_hexes.len(),
            ml_dsa_pubkey_hexes.len()
        ));
    }

    // Parse the requested additions (hex + Ed25519 validity, and the ML-DSA key
    // when hybrid) up front so a bad key fails before we touch anything.
    let mut additions = Vec::with_capacity(pubkey_hexes.len());
    for (i, h) in pubkey_hexes.iter().enumerate() {
        let ed = parse_validator_pubkey(h).map_err(|e| format!("--pubkey {h}: {e}"))?;
        let ml_dsa = match ml_dsa_pubkey_hexes.get(i) {
            Some(mh) => {
                Some(parse_ml_dsa_pubkey(mh).map_err(|e| format!("--ml-dsa-pubkey for {h}: {e}"))?)
            }
            None => None,
        };
        additions.push(CommitteeMember { ed, ml_dsa });
    }

    let raw = std::fs::read_to_string(&genesis_path)
        .map_err(|e| format!("cannot read {}: {e}", genesis_path.display()))?;
    let mut genesis: serde_json::Value =
        serde_json::from_str(&raw).map_err(|e| format!("genesis.json is not valid JSON: {e}"))?;

    let (existing, epoch) = committee_from_genesis(&genesis)?;
    let reroll = reroll_committee(&existing, &additions, epoch)?;

    // Rewrite `validators`, `federation_id`, `threshold` in place; preserve every
    // other field (wells, initial_cells, starbridge_cells, intervals).
    let new_members: Vec<CommitteeMember> = reroll
        .committee
        .iter()
        .filter(|m| !existing.iter().any(|e| e.ed == m.ed))
        .cloned()
        .collect();
    if let Some(validators) = genesis.get_mut("validators").and_then(|v| v.as_array_mut()) {
        let base = validators.len();
        for (i, m) in new_members.iter().enumerate() {
            let pk_hex = hex32(&m.ed);
            // Derive a devnet XMSS-root placeholder the same way `genesis.rs`
            // does, so the entry shape matches a generated committee.
            let xmss_root = blake3::derive_key("dregg-devnet-xmss-root-v1", &m.ed);
            let mut entry = serde_json::json!({
                "name": format!("node-{}", base + i),
                "public_key": pk_hex,
                "xmss_root": hex32(&xmss_root),
            });
            // HYBRID: mirror `genesis.rs` and publish this member's ML-DSA key +
            // its coupled-core hybrid_id, so the descriptor keeps every member's
            // PQ enrollment and the running node re-derives the same id.
            if let Some(ml) = &m.ml_dsa {
                let hybrid_id = dregg_types::hybrid_id_commitment(&m.ed, &ml.0);
                entry["ml_dsa_public_key"] =
                    serde_json::Value::String(ml.0.iter().map(|b| format!("{b:02x}")).collect());
                entry["hybrid_id"] = serde_json::Value::String(hex32(&hybrid_id));
            }
            validators.push(entry);
        }
    }
    genesis["federation_id"] = serde_json::Value::String(hex32(&reroll.federation_id));
    genesis["threshold"] = serde_json::Value::Number(reroll.threshold.into());

    let pretty = serde_json::to_string_pretty(&genesis)
        .map_err(|e| format!("failed to serialize genesis: {e}"))?;
    std::fs::write(&genesis_path, &pretty)
        .map_err(|e| format!("failed to write {}: {e}", genesis_path.display()))?;
    // A content-named sibling makes the descriptor unambiguous to distribute.
    let fedid8 = &hex32(&reroll.federation_id)[..8];
    let descriptor_path = data_path.join(format!("genesis-{fedid8}.json"));
    let _ = std::fs::write(&descriptor_path, &pretty);

    if json {
        let j = serde_json::json!({
            "federation_id": hex32(&reroll.federation_id),
            "committee_epoch": reroll.epoch,
            "threshold": reroll.threshold,
            "committee_size": reroll.committee.len(),
            "added": new_members.iter().map(|m| hex32(&m.ed)).collect::<Vec<_>>(),
            "already_present": reroll.already_present.iter().map(hex32).collect::<Vec<_>>(),
            "hybrid": reroll.hybrid,
            "genesis": genesis_path.display().to_string(),
            "descriptor": descriptor_path.display().to_string(),
        });
        println!("{}", serde_json::to_string_pretty(&j).unwrap());
        return Ok(());
    }

    println!("Committee re-rolled.");
    for m in &new_members {
        println!("  + added    {}", hex32(&m.ed));
    }
    for pk in &reroll.already_present {
        println!("  · already  {} (skipped)", hex32(pk));
    }
    println!();
    println!("  New federation_id : {}", hex32(&reroll.federation_id));
    println!(
        "  Identity          : {}",
        if reroll.hybrid {
            "HYBRID (Ed25519 + ML-DSA-65 coupled-core roster)"
        } else {
            "legacy Ed25519-only (no enrolled PQ roster)"
        }
    );
    println!("  Committee size    : {}", reroll.committee.len());
    println!(
        "  BFT threshold     : {} (quorum_threshold({})) — f = {} faulty tolerated",
        reroll.threshold,
        reroll.committee.len(),
        reroll.committee.len() - reroll.threshold
    );
    println!();
    println!("  Wrote: {}", genesis_path.display());
    println!(
        "  Descriptor (distribute this): {}",
        descriptor_path.display()
    );
    println!();
    println!("Next (the re-roll is a COORDINATED act — the federation_id changed):");
    println!(
        "  1. Copy this genesis.json to EVERY committee node's data dir (keep each node's own node.key)."
    );
    println!(
        "  2. Restart each node with --federation-mode full --federation-peers <a-live-peer>:9420"
    );
    println!("     and --bind <its-overlay-ip> so authorized peers can sync (NOT 0.0.0.0).");
    println!(
        "  3. Each /status then shows federation_mode:full, the new federation_id, and peer_count rising."
    );
    Ok(())
}

// =============================================================================
// propose-epoch-transition (live, running-network path)
// =============================================================================

/// Propose a LIVE epoch transition (validator-set reconfiguration) to a RUNNING
/// node via its HTTP API.
///
/// Validates each pubkey locally (real Ed25519 point) BEFORE contacting the
/// node, then POSTs `{add, remove}` to `POST /epoch/propose-transition`. The node
/// creates one on-chain membership proposal per validator and disseminates it;
/// the change APPLIES only once a quorum of the CURRENT committee ratifies it
/// through finality (proposing is not authority — the committee's votes are).
///
/// Dependency-free: a raw HTTP/1.1 request over a loopback TCP socket, mirroring
/// `main.rs::check_status`. `token` is the node's bearer (omit on a loopback
/// devnet node with no passphrase).
pub async fn propose_epoch_transition(
    port: u16,
    token: Option<&str>,
    add: &[String],
    remove: &[String],
    json_out: bool,
) -> Result<(), String> {
    if add.is_empty() && remove.is_empty() {
        return Err(
            "nothing to propose: pass --add <pubkey>, --remove <pubkey>, or --rotate <old> <new>"
                .to_string(),
        );
    }
    // Validate every key up front (a bad key fails before we touch the node).
    let mut add_valid = Vec::with_capacity(add.len());
    for h in add {
        parse_validator_pubkey(h).map_err(|e| format!("--add {h}: {e}"))?;
        add_valid.push(h.trim().to_string());
    }
    let mut remove_valid = Vec::with_capacity(remove.len());
    for h in remove {
        parse_validator_pubkey(h).map_err(|e| format!("--remove {h}: {e}"))?;
        remove_valid.push(h.trim().to_string());
    }

    let body = serde_json::json!({ "add": add_valid, "remove": remove_valid }).to_string();
    let (status, resp_body) =
        http_post_localhost(port, "/epoch/propose-transition", token, &body).await?;

    if json_out {
        println!("{resp_body}");
        if !(200..300).contains(&status) {
            return Err(format!("node returned HTTP {status}"));
        }
        return Ok(());
    }

    if !(200..300).contains(&status) {
        return Err(format!(
            "node returned HTTP {status}: {resp_body}\n  \
             (a 401/403 means the node has a passphrase — pass --token <bearer>.)"
        ));
    }

    println!("Live epoch transition proposed on the running node (port {port}).");
    // Best-effort pretty print of the JSON proposal list.
    if let Ok(v) = serde_json::from_str::<serde_json::Value>(&resp_body) {
        if let Some(proposals) = v.get("proposals").and_then(|p| p.as_array()) {
            for p in proposals {
                let action = p.get("action").and_then(|a| a.as_str()).unwrap_or("?");
                let validator = p.get("validator").and_then(|a| a.as_str()).unwrap_or("?");
                let block = p
                    .get("proposal_block")
                    .and_then(|a| a.as_str())
                    .unwrap_or("?");
                println!(
                    "  {action:<6} {validator}  (proposal block {})",
                    &block[..block.len().min(16)]
                );
            }
        }
        if let (Some(size), Some(thr)) = (
            v.get("committee_size").and_then(|x| x.as_u64()),
            v.get("threshold").and_then(|x| x.as_u64()),
        ) {
            println!();
            println!("  Current committee size : {size}");
            println!("  Current BFT threshold  : {thr}");
        }
    }
    println!();
    println!("The proposal is now on-chain. It APPLIES once a quorum of the CURRENT");
    println!("committee ratifies it through finality — the chain keeps advancing, no");
    println!("federation_id change, no restart, no bot re-point. A new validator then");
    println!("joins live with: dregg-node join --bootstrap <a-live-peer>:9420");
    Ok(())
}

/// Approve a pending membership proposal on a RUNNING node
/// (`POST /membership/approve`) — the ADMIT half of the live epoch transition.
///
/// `propose-epoch-transition` (or a joiner's auto-proposed Join) registers the
/// proposal on-chain; each committee operator runs THIS against their own node
/// until the CURRENT committee's quorum is reached, at which point the
/// amendment applies live — no genesis re-roll, no restart, `federation_id`
/// unchanged. Pending proposals + their block ids: `GET /api/membership`.
pub async fn approve_membership(
    port: u16,
    token: Option<&str>,
    proposal_block: &str,
    json_out: bool,
) -> Result<(), String> {
    let pb = proposal_block.trim();
    if pb.len() != 64 || !pb.chars().all(|c| c.is_ascii_hexdigit()) {
        return Err(format!(
            "--proposal {pb}: must be the 64-hex proposal block id \
             (list pending proposals with GET /api/membership)"
        ));
    }
    let body = serde_json::json!({ "proposal_block": pb }).to_string();
    let (status, resp_body) =
        http_post_localhost(port, "/membership/approve", token, &body).await?;

    if json_out {
        println!("{resp_body}");
        if !(200..300).contains(&status) {
            return Err(format!("node returned HTTP {status}"));
        }
        return Ok(());
    }

    if !(200..300).contains(&status) {
        return Err(format!(
            "node returned HTTP {status}: {resp_body}\n  \
             (a 401/403 means the node has a passphrase — pass --token <bearer>; a 409 \
             carries the node's reason: not a participant / unknown / already applied.)"
        ));
    }

    println!("Approval vote cast and disseminated (port {port}).");
    println!("The amendment APPLIES once a quorum of the CURRENT committee has approved —");
    println!("watch it land: curl -s localhost:{port}/api/membership");
    Ok(())
}

/// Minimal dependency-free HTTP/1.1 POST to `http://127.0.0.1:<port><path>` with
/// a JSON body and optional bearer token. Returns `(status_code, body)`.
async fn http_post_localhost(
    port: u16,
    path: &str,
    token: Option<&str>,
    body: &str,
) -> Result<(u16, String), String> {
    use tokio::io::{AsyncReadExt, AsyncWriteExt};

    let addr = std::net::SocketAddr::new(std::net::Ipv4Addr::LOCALHOST.into(), port);
    let mut stream = tokio::net::TcpStream::connect(addr)
        .await
        .map_err(|e| format!("cannot connect to dregg-node on 127.0.0.1:{port}: {e}"))?;

    let auth = match token {
        Some(t) => format!("Authorization: Bearer {t}\r\n"),
        None => String::new(),
    };
    let req = format!(
        "POST {path} HTTP/1.1\r\n\
         Host: 127.0.0.1:{port}\r\n\
         {auth}\
         Content-Type: application/json\r\n\
         Content-Length: {len}\r\n\
         Connection: close\r\n\r\n\
         {body}",
        len = body.len(),
    );
    stream
        .write_all(req.as_bytes())
        .await
        .map_err(|e| format!("failed to send request: {e}"))?;
    stream
        .flush()
        .await
        .map_err(|e| format!("failed to flush request: {e}"))?;

    let mut raw = Vec::new();
    stream
        .read_to_end(&mut raw)
        .await
        .map_err(|e| format!("failed to read response: {e}"))?;
    let text = String::from_utf8_lossy(&raw);

    // Parse the status code from the response line ("HTTP/1.1 200 OK").
    let status = text
        .split_whitespace()
        .nth(1)
        .and_then(|s| s.parse::<u16>().ok())
        .ok_or_else(|| format!("malformed HTTP response from node: {text:.120}"))?;
    // Body follows the first blank line.
    let body = text
        .split_once("\r\n\r\n")
        .map(|(_, b)| b.to_string())
        .unwrap_or_default();
    Ok((status, body))
}

// =============================================================================
// join (pre-flight)
// =============================================================================

/// What [`prepare_join`] resolved: the bootstrap peer to dial and the key/genesis
/// state the daemon will run on.
#[derive(Debug, Clone)]
pub struct JoinPlan {
    /// The bootstrap peer `host:gossip_port` to put in `--federation-peers`.
    pub bootstrap: String,
    /// This node's validator public key (for the operator to admit).
    pub self_pubkey: [u8; 32],
    /// Whether this node's key is already in the committee genesis (→ voting
    /// validator) or not (→ follower that auto-proposes membership).
    pub in_committee: bool,
}

/// Pre-flight a join: ensure the data dir + `node.key` + committee `genesis.json`
/// are present, and report whether this node is already a committee member.
///
/// Returns an error (with operator guidance) when there is no committee
/// descriptor to follow — a node cannot verify a federation's blocks without its
/// committee, so `join` refuses rather than starting a node that trusts nobody.
pub fn prepare_join(data_dir: &str, bootstrap: &str, json: bool) -> Result<JoinPlan, String> {
    let bootstrap = bootstrap.trim();
    if !bootstrap.contains(':') {
        return Err(format!(
            "--bootstrap must be host:gossip_port (e.g. 100.64.0.1:9420), got {bootstrap:?}"
        ));
    }
    let data_path = expand_path(data_dir);
    std::fs::create_dir_all(&data_path)
        .map_err(|e| format!("failed to create data dir {}: {e}", data_path.display()))?;
    let key_path = data_path.join("node.key");

    let self_pubkey = if key_path.exists() {
        pubkey_from_key_file(&key_path)?
    } else {
        let pk = generate_key_file(&key_path)?;
        if !json {
            println!(
                "Generated this box's validator keypair: {}\n  (give it to the operator for `add-validator`)\n",
                hex32(&pk)
            );
        }
        pk
    };

    let genesis_path = data_path.join("genesis.json");
    if !genesis_path.exists() {
        return Err(format!(
            "no committee genesis.json in {data}.\n\
             You cannot follow a federation without its committee descriptor.\n\
             Steps:\n  \
               1. your validator pubkey is {pk}\n  \
               2. the operator runs `dregg-node add-validator --pubkey {pk}` and sends you the resulting genesis.json\n  \
               3. drop it in {data} and re-run `dregg-node join --bootstrap {bs}`.",
            data = data_path.display(),
            pk = hex32(&self_pubkey),
            bs = bootstrap,
        ));
    }

    let raw = std::fs::read_to_string(&genesis_path)
        .map_err(|e| format!("cannot read {}: {e}", genesis_path.display()))?;
    let genesis: serde_json::Value =
        serde_json::from_str(&raw).map_err(|e| format!("genesis.json is not valid JSON: {e}"))?;
    let (committee, _epoch) = committee_from_genesis(&genesis)?;
    let in_committee = committee.iter().any(|m| m.ed == self_pubkey);

    Ok(JoinPlan {
        bootstrap: bootstrap.to_string(),
        self_pubkey,
        in_committee,
    })
}

/// Print the human-facing summary of a join plan (before the daemon starts).
pub fn announce_join(plan: &JoinPlan, data_dir: &str, bind: &str) {
    println!("Joining federation via bootstrap {}", plan.bootstrap);
    println!("  Data dir          : {}", expand_path(data_dir).display());
    println!("  This validator    : {}", hex32(&plan.self_pubkey));
    println!("  Bind (read API)   : {bind}");
    if plan.in_committee {
        println!(
            "  Committee member  : YES — this node will sync the blocklace and cast finalization votes."
        );
    } else {
        println!(
            "  Committee member  : no — this node will sync as a FOLLOWER and auto-propose membership.\n  \
             It anchors no finality until an operator runs `add-validator` for your pubkey and\n  \
             re-distributes the committee genesis.json (the federation_id changes on admission)."
        );
    }
    if bind == "0.0.0.0" || bind == "::" {
        println!(
            "  ⚠ binding 0.0.0.0 exposes the API to every interface (red-team MESH-2). Prefer --bind <overlay-ip>."
        );
    }
    println!("  Starting node (full mode) — Ctrl-C to stop.\n");
}

/// Expand `~` in a path string (mirrors `main.rs::expand_path`).
fn expand_path(path: &str) -> PathBuf {
    if let Some(rest) = path.strip_prefix("~/")
        && let Some(home) = std::env::var_os("HOME")
    {
        return PathBuf::from(home).join(rest);
    }
    PathBuf::from(path)
}

#[cfg(test)]
mod tests {
    use super::*;
    use dregg_federation::derive_federation_id_with_epoch;
    use dregg_federation::frost::MlDsaSigningKey;
    use dregg_types::PublicKey;

    fn keypair() -> ([u8; 32], [u8; 32]) {
        let mut seed = [0u8; 32];
        getrandom::fill(&mut seed).unwrap();
        let sk = ed25519_dalek::SigningKey::from_bytes(&seed);
        (seed, sk.verifying_key().to_bytes())
    }

    /// A legacy (Ed25519-only) committee member.
    fn ed_member(ed: [u8; 32]) -> CommitteeMember {
        CommitteeMember { ed, ml_dsa: None }
    }

    /// A HYBRID member: Ed25519 pubkey + the ML-DSA-65 key deterministically
    /// derived from `seed` — exactly the pairing `genesis.rs` publishes.
    fn hybrid_member(seed: [u8; 32]) -> CommitteeMember {
        let ed = ed25519_dalek::SigningKey::from_bytes(&seed)
            .verifying_key()
            .to_bytes();
        let (ml, _) = MlDsaSigningKey::from_seed(&seed);
        CommitteeMember {
            ed,
            ml_dsa: Some(ml),
        }
    }

    #[test]
    fn parse_pubkey_rejects_garbage_and_non_curve() {
        assert!(parse_validator_pubkey("zz").is_err());
        assert!(parse_validator_pubkey(&"ff".repeat(31)).is_err()); // 62 chars, wrong length
        assert!(
            parse_validator_pubkey(
                "not-hex-at-all-but-the-right-length-padding-padding-padding-pad!"
            )
            .is_err()
        );
        // The POINT-VALIDATION tooth the name promises: 64 valid hex chars that
        // decode to 32 bytes (so length/hex gates pass) but do NOT encode a point
        // on the Ed25519 curve. Without the `VerifyingKey::from_bytes` check this
        // would be accepted as a "key". This vector encodes y = 2 (little-endian,
        // sign bit clear); for y = 2 the recovered x² = (y²-1)/(d·y²+1) is a
        // quadratic NON-residue mod 2²⁵⁵−19, so decompression fails — an off-curve
        // point. (Note: many 32-byte strings like 0xFF×32 ARE on-curve and would be
        // accepted, so the vector matters.)
        let off_curve = "0200000000000000000000000000000000000000000000000000000000000000";
        assert_eq!(off_curve.len(), 64);
        assert!(
            parse_validator_pubkey(off_curve).is_err(),
            "32-byte-but-off-curve hex must be rejected by point validation, not accepted"
        );
        let (_, pk) = keypair();
        assert_eq!(parse_validator_pubkey(&hex32(&pk)).unwrap(), pk);
    }

    #[test]
    fn pubkey_from_key_file_matches_ed25519() {
        let (seed, pk) = keypair();
        let dir = tempfile::tempdir().unwrap();
        let kp = dir.path().join("node.key");
        std::fs::write(&kp, seed).unwrap();
        assert_eq!(pubkey_from_key_file(&kp).unwrap(), pk);
    }

    #[test]
    fn reroll_matches_canonical_derivation_and_threshold() {
        let (_, edge) = keypair();
        let (_, persvati) = keypair();
        let (_, snoopy) = keypair();

        // edge-only → +persvati +snoopy = a 3-member committee (legacy Ed25519-only).
        let r = reroll_committee(
            &[ed_member(edge)],
            &[ed_member(persvati), ed_member(snoopy)],
            0,
        )
        .unwrap();
        assert_eq!(r.committee.len(), 3);
        assert!(!r.hybrid, "no ML-DSA keys → legacy Ed25519-only derivation");
        assert_eq!(r.threshold, quorum_threshold(3)); // = 3 (strict supermajority, f=0)
        assert_eq!(r.threshold, 3);

        // The id MUST equal the canonical derivation over the committee (order-independent).
        let pubkeys: Vec<PublicKey> = [edge, persvati, snoopy]
            .iter()
            .map(|b| PublicKey(*b))
            .collect();
        assert_eq!(
            r.federation_id,
            derive_federation_id_with_epoch(&pubkeys, 0)
        );
        // …and over a re-ordered committee (sorting is internal to the derivation).
        let reordered: Vec<PublicKey> = [snoopy, edge, persvati]
            .iter()
            .map(|b| PublicKey(*b))
            .collect();
        assert_eq!(
            r.federation_id,
            derive_federation_id_with_epoch(&reordered, 0)
        );
    }

    #[test]
    fn reroll_is_idempotent_on_overlap_and_errors_on_noop() {
        let (_, a) = keypair();
        let (_, b) = keypair();
        // adding b when {a} → {a,b}; re-adding b reports already_present.
        let r1 = reroll_committee(&[ed_member(a)], &[ed_member(b)], 0).unwrap();
        assert_eq!(r1.committee.len(), 2);
        let r2 = reroll_committee(&[ed_member(a), ed_member(b)], &[ed_member(b)], 0);
        assert!(
            r2.is_err(),
            "re-adding only-present members is a no-op error"
        );
        // a mixed batch (one present, one new) succeeds and records the present one.
        let (_, c) = keypair();
        let r3 = reroll_committee(
            &[ed_member(a), ed_member(b)],
            &[ed_member(b), ed_member(c)],
            0,
        )
        .unwrap();
        assert_eq!(r3.committee.len(), 3);
        assert_eq!(r3.already_present, vec![b]);
    }

    #[test]
    fn reroll_matches_genesis_hybrid_derivation_over_same_roster() {
        // THE WOUND'S REGRESSION GUARD: genesis derives the federation_id via
        // `derive_federation_id_hybrid_with_epoch` over the committee's HYBRID
        // roster. A reroll that added members must re-derive the id the SAME way,
        // or any membership change silently diverges from (and downgrades) the
        // committed PQ identity.
        let m0 = hybrid_member([0x11; 32]);
        let m1 = hybrid_member([0x22; 32]);
        let m2 = hybrid_member([0x33; 32]);

        // Reroll: existing {m0} + additions {m1, m2}.
        let r = reroll_committee(&[m0.clone()], &[m1.clone(), m2.clone()], 7).unwrap();
        assert_eq!(r.committee.len(), 3);
        assert!(r.hybrid, "every member carries an ML-DSA key → hybrid id");

        // GENESIS derivation over the SAME roster {m0, m1, m2}.
        let ed: Vec<PublicKey> = [&m0, &m1, &m2].iter().map(|m| PublicKey(m.ed)).collect();
        let ml: Vec<_> = [&m0, &m1, &m2]
            .iter()
            .map(|m| m.ml_dsa.clone().unwrap())
            .collect();
        let genesis_id = derive_federation_id_hybrid_with_epoch(&ed, &ml, 7);

        assert_eq!(
            r.federation_id, genesis_id,
            "reroll id MUST equal the genesis hybrid derivation over the same roster"
        );
        // And it must NOT equal the legacy Ed25519-only projection of the same
        // committee — proving the reroll actually commits to the ML-DSA roster.
        let ed_only = derive_federation_id_with_epoch(&ed, 7);
        assert_ne!(
            r.federation_id, ed_only,
            "hybrid-derived id must differ from the Ed25519-only id (PQ binding is live)"
        );
    }

    #[test]
    fn reroll_refuses_mixed_hybrid_and_legacy_committee() {
        // Adding an Ed25519-only member to a HYBRID committee would strip the PQ
        // binding off the whole committee (the running node drops a partial
        // ML-DSA set). The reroll must REFUSE rather than silently downgrade.
        let hybrid = hybrid_member([0x44; 32]);
        let (_, ed_only_pk) = keypair();
        let e = reroll_committee(&[hybrid], &[ed_member(ed_only_pk)], 0).unwrap_err();
        assert!(e.contains("mixed committee"), "{e}");
    }

    #[test]
    fn add_validator_rewrites_genesis_in_place_preserving_other_fields() {
        let (edge_seed, edge_pk) = keypair();
        let (_, new_pk) = keypair();
        let dir = tempfile::tempdir().unwrap();
        // Write node.key (so the dir looks like a node) + a minimal committee genesis.
        std::fs::write(dir.path().join("node.key"), edge_seed).unwrap();
        let genesis = serde_json::json!({
            "federation_id": hex32(&derive_federation_id_with_epoch(&[PublicKey(edge_pk)], 0)),
            "committee_epoch": 0,
            "threshold": 1,
            "epoch_length": 1000,
            "checkpoint_interval": 100,
            "validators": [ { "name": "node-0", "public_key": hex32(&edge_pk), "xmss_root": "00".repeat(32) } ],
            "issuer_well": "ab".repeat(32),
            "starbridge_cells": [ { "label": "keepme" } ],
        });
        std::fs::write(
            dir.path().join("genesis.json"),
            serde_json::to_string_pretty(&genesis).unwrap(),
        )
        .unwrap();

        // Legacy Ed25519-only federation (genesis carries no ml_dsa_public_key):
        // no --ml-dsa-pubkey, so the reroll stays on the legacy projection.
        add_validator(dir.path().to_str().unwrap(), &[hex32(&new_pk)], &[], true).unwrap();

        let after: serde_json::Value = serde_json::from_str(
            &std::fs::read_to_string(dir.path().join("genesis.json")).unwrap(),
        )
        .unwrap();
        // committee grew to 2, threshold recomputed, id re-derived, other fields intact.
        assert_eq!(after["validators"].as_array().unwrap().len(), 2);
        assert_eq!(after["threshold"], 2);
        assert_eq!(
            after["federation_id"],
            hex32(&derive_federation_id_with_epoch(
                &[PublicKey(edge_pk), PublicKey(new_pk)],
                0
            ))
        );
        assert_eq!(after["issuer_well"], "ab".repeat(32));
        assert_eq!(after["starbridge_cells"][0]["label"], "keepme");
        // the content-named descriptor sibling exists.
        let fedid8 = after["federation_id"].as_str().unwrap()[..8].to_string();
        assert!(dir.path().join(format!("genesis-{fedid8}.json")).exists());
    }

    #[test]
    fn add_validator_errors_without_genesis() {
        let dir = tempfile::tempdir().unwrap();
        let (_, pk) = keypair();
        let e = add_validator(dir.path().to_str().unwrap(), &[hex32(&pk)], &[], true).unwrap_err();
        assert!(e.contains("no genesis.json"), "{e}");
    }

    #[test]
    fn add_validator_on_hybrid_genesis_reproduces_the_hybrid_id_and_pins_the_new_member() {
        // A HYBRID genesis (every validator has an ml_dsa_public_key). Adding a
        // validator through `add-validator --ml-dsa-pubkey` must (a) re-derive the
        // federation_id the SAME way genesis + the running node do, (b) publish the
        // new member's ml_dsa_public_key + hybrid_id, keeping the committee's PQ
        // enrollment. This is the on-disk end of the genesis == reroll invariant.
        let existing = hybrid_member([0xA1; 32]);
        let addition = hybrid_member([0xB2; 32]);
        let add_ml_hex: String = addition
            .ml_dsa
            .as_ref()
            .unwrap()
            .0
            .iter()
            .map(|b| format!("{b:02x}"))
            .collect();
        let existing_ml_hex: String = existing
            .ml_dsa
            .as_ref()
            .unwrap()
            .0
            .iter()
            .map(|b| format!("{b:02x}"))
            .collect();
        let existing_hybrid_id =
            dregg_types::hybrid_id_commitment(&existing.ed, &existing.ml_dsa.as_ref().unwrap().0);

        let dir = tempfile::tempdir().unwrap();
        let genesis_id = derive_federation_id_hybrid_with_epoch(
            &[PublicKey(existing.ed)],
            &[existing.ml_dsa.clone().unwrap()],
            0,
        );
        let genesis = serde_json::json!({
            "federation_id": hex32(&genesis_id),
            "committee_epoch": 0,
            "threshold": 1,
            "validators": [ {
                "name": "node-0",
                "public_key": hex32(&existing.ed),
                "xmss_root": "00".repeat(32),
                "ml_dsa_public_key": existing_ml_hex,
                "hybrid_id": hex32(&existing_hybrid_id),
            } ],
        });
        std::fs::write(
            dir.path().join("genesis.json"),
            serde_json::to_string_pretty(&genesis).unwrap(),
        )
        .unwrap();

        add_validator(
            dir.path().to_str().unwrap(),
            &[hex32(&addition.ed)],
            &[add_ml_hex.clone()],
            true,
        )
        .unwrap();

        let after: serde_json::Value = serde_json::from_str(
            &std::fs::read_to_string(dir.path().join("genesis.json")).unwrap(),
        )
        .unwrap();

        // The written id equals the genesis hybrid derivation over the FULL roster —
        // exactly what the running node recomputes (`derive_federation_id_hybrid_with_epoch`).
        let expected = derive_federation_id_hybrid_with_epoch(
            &[PublicKey(existing.ed), PublicKey(addition.ed)],
            &[
                existing.ml_dsa.clone().unwrap(),
                addition.ml_dsa.clone().unwrap(),
            ],
            0,
        );
        assert_eq!(after["federation_id"], hex32(&expected));
        // …and it is NOT the Ed25519-only projection the OLD reroll would have written.
        let ed_only =
            derive_federation_id_with_epoch(&[PublicKey(existing.ed), PublicKey(addition.ed)], 0);
        assert_ne!(after["federation_id"], hex32(&ed_only));

        // The new member entry carries its ml_dsa_public_key + coupled-core hybrid_id.
        let v1 = &after["validators"][1];
        assert_eq!(v1["public_key"], hex32(&addition.ed));
        assert_eq!(v1["ml_dsa_public_key"], add_ml_hex);
        let expected_new_hybrid_id =
            dregg_types::hybrid_id_commitment(&addition.ed, &addition.ml_dsa.as_ref().unwrap().0);
        assert_eq!(v1["hybrid_id"], hex32(&expected_new_hybrid_id));
    }

    #[test]
    fn add_validator_on_hybrid_genesis_refuses_ed_only_addition() {
        // The downgrade guard on the on-disk path: adding to a hybrid federation
        // WITHOUT the new member's ML-DSA key is refused (would strip PQ identity).
        let existing = hybrid_member([0xC3; 32]);
        let (_, addition) = keypair();
        let existing_ml_hex: String = existing
            .ml_dsa
            .as_ref()
            .unwrap()
            .0
            .iter()
            .map(|b| format!("{b:02x}"))
            .collect();
        let dir = tempfile::tempdir().unwrap();
        let genesis = serde_json::json!({
            "committee_epoch": 0,
            "validators": [ {
                "name": "node-0",
                "public_key": hex32(&existing.ed),
                "xmss_root": "00".repeat(32),
                "ml_dsa_public_key": existing_ml_hex,
            } ],
        });
        std::fs::write(dir.path().join("genesis.json"), genesis.to_string()).unwrap();

        let e = add_validator(dir.path().to_str().unwrap(), &[hex32(&addition)], &[], true)
            .unwrap_err();
        assert!(e.contains("mixed committee"), "{e}");
    }

    #[test]
    fn prepare_join_requires_committee_descriptor() {
        let dir = tempfile::tempdir().unwrap();
        // No genesis yet → join refuses but DID generate the key (so the pubkey is printable).
        let e = prepare_join(dir.path().to_str().unwrap(), "100.64.0.1:9420", true).unwrap_err();
        assert!(
            e.contains("committee descriptor") || e.contains("genesis.json"),
            "{e}"
        );
        assert!(
            dir.path().join("node.key").exists(),
            "join generated the key"
        );
    }

    #[test]
    fn prepare_join_detects_membership() {
        let (seed, pk) = keypair();
        let (_, other) = keypair();
        let dir = tempfile::tempdir().unwrap();
        std::fs::write(dir.path().join("node.key"), seed).unwrap();
        // genesis whose committee includes THIS node → in_committee true.
        let genesis = serde_json::json!({
            "committee_epoch": 0,
            "validators": [
                { "name": "node-0", "public_key": hex32(&other), "xmss_root": "00".repeat(32) },
                { "name": "node-1", "public_key": hex32(&pk), "xmss_root": "00".repeat(32) }
            ],
        });
        std::fs::write(dir.path().join("genesis.json"), genesis.to_string()).unwrap();
        let plan = prepare_join(dir.path().to_str().unwrap(), "host:9420", true).unwrap();
        assert!(plan.in_committee);
        assert_eq!(plan.self_pubkey, pk);
    }

    #[test]
    fn bad_bootstrap_rejected() {
        let dir = tempfile::tempdir().unwrap();
        assert!(prepare_join(dir.path().to_str().unwrap(), "no-port", true).is_err());
    }
}
