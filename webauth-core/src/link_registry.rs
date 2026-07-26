//! # `link_registry` — the verified cross-platform link record + the `resolve_root` seam.
//!
//! After [`crate::link_claim::verify_link_claim`] proves that root key K controls a platform
//! account, the frontend RECORDS the binding here. Then anywhere the offerings stack compares
//! actors (leaderboards, council membership, session grants, a portfolio), it first
//! [`resolve_root`](LinkStore::resolve_root)s the custodial pubkey to its root — collapsing a
//! Discord-you and a Telegram-you (different custodial keys) into ONE human whenever both have
//! linked to the same K.
//!
//! Storage is an APPEND-ONLY TSV log (the cross-process-simplest shared store — all three dregg
//! processes on one box append to and read the same file; `O_APPEND` keeps concurrent writes from
//! interleaving a single record, and resolution is latest-record-wins). A relink or a rebind is
//! just another appended line; history is preserved (the deep version lifts this onto K's identity
//! cell so links become receipt-signed turns — see the design doc).
//!
//! The record binds the RAW pubkeys (hex), never a cell id: `link_claim` uses the framework
//! `"default"`-domain cell derivation while `account_id` uses `"dregg:account-identity:v1"` — same
//! key, two cell flavors, so the join key is the pubkey and each consumer derives its own cell id.

use std::io::{BufRead, BufReader, Write};
use std::path::{Path, PathBuf};

/// One verified link: root key K attests it controls `(platform, platform_uid)` whose custodial
/// dregg key is `custodial_pubkey_hex`, recorded at `verified_at` (unix seconds). All fields are
/// TAB- and NEWLINE-free by construction (hex / ascii-platform / decimal uid), so the TSV encoding
/// is injective.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct LinkRecord {
    /// The user-held ROOT key K's pubkey (lowercase hex) — the join key one human resolves to.
    pub root_pubkey_hex: String,
    /// The platform this link is for (`"discord"`, `"telegram"`, ...).
    pub platform: String,
    /// The platform account id (Discord/Telegram uid as a decimal string).
    pub platform_uid: String,
    /// The platform's CUSTODIAL dregg pubkey (lowercase hex) — what turns on that platform are
    /// signed/attributed under, and the key `resolve_root` maps FROM.
    pub custodial_pubkey_hex: String,
    /// When the link was verified (unix seconds).
    pub verified_at: u64,
}

impl LinkRecord {
    /// A field is storable iff it carries no TAB or NEWLINE (the TSV delimiters).
    fn field_ok(s: &str) -> bool {
        !s.as_bytes().iter().any(|&b| b == b'\t' || b == b'\n')
    }

    /// Render as one TSV line (no trailing newline). `None` if any field carries a delimiter.
    pub fn to_line(&self) -> Option<String> {
        for f in [
            &self.root_pubkey_hex,
            &self.platform,
            &self.platform_uid,
            &self.custodial_pubkey_hex,
        ] {
            if !Self::field_ok(f) {
                return None;
            }
        }
        Some(format!(
            "{}\t{}\t{}\t{}\t{}",
            self.root_pubkey_hex,
            self.platform,
            self.platform_uid,
            self.custodial_pubkey_hex,
            self.verified_at
        ))
    }

    /// Parse one TSV line. `None` on the wrong field count / a bad `verified_at` (a malformed
    /// line is skipped, never crashes resolution).
    pub fn from_line(line: &str) -> Option<LinkRecord> {
        let f: Vec<&str> = line.split('\t').collect();
        if f.len() != 5 {
            return None;
        }
        Some(LinkRecord {
            root_pubkey_hex: f[0].to_string(),
            platform: f[1].to_string(),
            platform_uid: f[2].to_string(),
            custodial_pubkey_hex: f[3].to_string(),
            verified_at: f[4].parse().ok()?,
        })
    }
}

/// The store both the frontends (append a verified link) and the offerings stack (resolve) use.
pub trait LinkStore {
    /// Append a verified link. The caller has ALREADY run `verify_link_claim` — this store does
    /// not re-verify (it is a record, not a gate).
    fn record(&mut self, rec: &LinkRecord) -> std::io::Result<()>;

    /// All records, oldest-first (the resolution helpers scan these).
    fn all(&self) -> std::io::Result<Vec<LinkRecord>>;

    /// Resolve a custodial pubkey to its ROOT pubkey — the LATEST link for that custodial wins
    /// (a rebind supersedes). `None` if the custodial key was never linked (it is then its own
    /// identity, unchanged — resolution is additive, never breaks the unlinked case).
    fn resolve_root(&self, custodial_pubkey_hex: &str) -> std::io::Result<Option<String>> {
        let mut latest: Option<(u64, String)> = None;
        for r in self.all()? {
            if r.custodial_pubkey_hex
                .eq_ignore_ascii_case(custodial_pubkey_hex)
            {
                match &latest {
                    // strict `>`: on a same-second tie the LATER file-order record wins, so a
                    // same-second rebind to a new K supersedes (the review's tie-break fix).
                    Some((t, _)) if *t > r.verified_at => {}
                    _ => latest = Some((r.verified_at, r.root_pubkey_hex)),
                }
            }
        }
        Ok(latest.map(|(_, root)| root))
    }

    /// Resolve a custodial pubkey to the ROTATION-READY stable account id of its root
    /// ([`account_id_of_root`]) — the deep-version join key, byte-identical to the identity cell's
    /// id. Additive over [`resolve_root`](LinkStore::resolve_root): a frontend adopts this as the
    /// unified-identity key when it wants the rotation story + forward-compatibility with the cell.
    /// `None` if unlinked (its own identity) or the stored root hex is malformed.
    fn resolve_root_account(&self, custodial_pubkey_hex: &str) -> std::io::Result<Option<String>> {
        Ok(self
            .resolve_root(custodial_pubkey_hex)?
            .and_then(|root| account_id_of_root(&root)))
    }

    /// **Every platform link currently attributed to a root key** — the exact inverse of
    /// [`resolve_root`](LinkStore::resolve_root): a record with custodial key C is returned for root
    /// R **iff** `resolve_root(C) == Some(R)`.
    ///
    /// ⚑ **That inverse property is the repair, and its absence was a real cross-account read, not a
    /// doc nicety.** This used to filter to `root == R` FIRST and only then take the latest per
    /// `(platform, uid)` — i.e. "latest wins" held only *within the records that already shared this
    /// root*. A binding recorded under R was therefore **never superseded** by a later binding of the
    /// same account under a different root, so the two directions disagreed: `resolve_root(C)` said C
    /// belonged to the newer human while `platforms_for_root(R)` still handed C to R. Consumers use
    /// the second direction to widen a view — `dreggnet-web`'s `/you` unions the custodial keys it
    /// returns into "your" history, and the link page prints them as yours — so a stale row meant one
    /// player's page counting ANOTHER human's tables and runs. That is how it bites: not as a wrong
    /// number, as somebody else's record on your page.
    ///
    /// The case that produces one is real and has no undo (see `identity_link`'s NO UN-LINK DOOR
    /// residual): a player who ran the ceremony on a code somebody handed them binds that stranger's
    /// account under their own root, with their own signature, and nothing removes the row. The
    /// stranger re-linking their account correctly now supersedes it in every direction at once.
    ///
    /// Keyed on the CUSTODIAL pubkey, and tie-broken with a strict `>` (later file-order wins on a
    /// same-second rebind), for one reason: those are the two things `resolve_root` does, and the
    /// inverse property is only true if both directions agree about what "latest" means.
    fn platforms_for_root(&self, root_pubkey_hex: &str) -> std::io::Result<Vec<LinkRecord>> {
        let mut latest: std::collections::HashMap<String, LinkRecord> =
            std::collections::HashMap::new();
        for r in self.all()? {
            let key = r.custodial_pubkey_hex.to_ascii_lowercase();
            match latest.get(&key) {
                Some(prev) if prev.verified_at > r.verified_at => {}
                _ => {
                    latest.insert(key, r);
                }
            }
        }
        Ok(latest
            .into_values()
            .filter(|r| r.root_pubkey_hex.eq_ignore_ascii_case(root_pubkey_hex))
            .collect())
    }
}

/// The cross-process shared store: an append-only TSV file. Point all frontends at ONE path.
pub struct FileLinkStore {
    path: PathBuf,
}

impl FileLinkStore {
    /// Open (creating the parent dir + file on first write) a store at `path`.
    pub fn new(path: impl AsRef<Path>) -> Self {
        FileLinkStore {
            path: path.as_ref().to_path_buf(),
        }
    }
}

/// The shared link-store path EVERY frontend points at: `$DREGG_LINK_DIR/links.tsv`, default
/// `$HOME/.local/state/dregg/links.tsv`. One file, so a link recorded on Discord resolves on
/// Telegram and the web (all three dregg processes on one box). Set `DREGG_LINK_DIR` in each
/// unit to the same directory.
pub fn default_store_path() -> PathBuf {
    let dir = std::env::var("DREGG_LINK_DIR").unwrap_or_else(|_| {
        std::env::var("HOME")
            .map(|h| format!("{h}/.local/state/dregg"))
            .unwrap_or_else(|_| ".".to_string())
    });
    PathBuf::from(dir).join("links.tsv")
}

/// The rotation-READY stable identity of a root pubkey: its inception-derived account id
/// ([`crate::account_id::account_id_hex`]). `None` on malformed hex.
///
/// This is the FIRST BRICK of the deep version (`docs/IDENTITY-LINK-DEEP-VERSION-DESIGN.md`): the
/// account id is byte-identical to the identity CELL's id (both are
/// `CellId::derive_raw(inception_pubkey, "dregg:account-identity:v1")`), so once links move onto
/// K's identity cell the resolution key needs no re-derivation — the raw pubkey the shallow TSV
/// stores maps to the same stable id the cell keys on. It also gives the resolution a rotation
/// story (the stable id survives a future signing-key rotation) instead of pinning a raw key.
pub fn account_id_of_root(root_pubkey_hex: &str) -> Option<String> {
    let bytes = hex::decode(root_pubkey_hex.trim()).ok()?;
    let arr: [u8; 32] = bytes.try_into().ok()?;
    Some(crate::account_id::account_id_hex(&arr))
}

impl LinkStore for FileLinkStore {
    fn record(&mut self, rec: &LinkRecord) -> std::io::Result<()> {
        let line = rec.to_line().ok_or_else(|| {
            std::io::Error::new(
                std::io::ErrorKind::InvalidInput,
                "link record field carries a TAB/NEWLINE delimiter",
            )
        })?;
        if let Some(parent) = self.path.parent() {
            std::fs::create_dir_all(parent)?;
        }
        let mut f = std::fs::OpenOptions::new()
            .create(true)
            .append(true)
            .open(&self.path)?;
        // ONE write_all of the whole record+newline: a single regular-file O_APPEND write is
        // atomic, so concurrent appends (a /tg/link and /da/link racing, or the three processes)
        // never interleave into a malformed line. (`writeln!` issued the line and the `\n` as two
        // separate syscalls — the interleave the maturation review caught as silent record loss.)
        f.write_all(format!("{line}\n").as_bytes())
    }

    fn all(&self) -> std::io::Result<Vec<LinkRecord>> {
        let f = match std::fs::File::open(&self.path) {
            Ok(f) => f,
            Err(e) if e.kind() == std::io::ErrorKind::NotFound => return Ok(Vec::new()),
            Err(e) => return Err(e),
        };
        let mut out = Vec::new();
        for line in BufReader::new(f).lines() {
            let line = line?;
            if line.trim().is_empty() {
                continue;
            }
            if let Some(r) = LinkRecord::from_line(&line) {
                out.push(r);
            }
        }
        Ok(out)
    }
}

/// A memory-backed store — for tests and single-process callers.
#[derive(Default)]
pub struct InMemoryLinkStore {
    records: Vec<LinkRecord>,
}

impl LinkStore for InMemoryLinkStore {
    fn record(&mut self, rec: &LinkRecord) -> std::io::Result<()> {
        self.records.push(rec.clone());
        Ok(())
    }
    fn all(&self) -> std::io::Result<Vec<LinkRecord>> {
        Ok(self.records.clone())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn rec(root: &str, plat: &str, uid: &str, cust: &str, at: u64) -> LinkRecord {
        LinkRecord {
            root_pubkey_hex: root.into(),
            platform: plat.into(),
            platform_uid: uid.into(),
            custodial_pubkey_hex: cust.into(),
            verified_at: at,
        }
    }

    /// THE payoff: a Discord custodial key and a Telegram custodial key, both linked to the SAME
    /// root K, resolve to ONE root — one human across platforms.
    #[test]
    fn two_platforms_linked_to_one_root_resolve_to_the_same_human() {
        let mut s = InMemoryLinkStore::default();
        s.record(&rec("K", "discord", "111", "custD", 100)).unwrap();
        s.record(&rec("K", "telegram", "222", "custT", 101))
            .unwrap();
        assert_eq!(s.resolve_root("custD").unwrap(), Some("K".into()));
        assert_eq!(s.resolve_root("custT").unwrap(), Some("K".into()));
        assert_eq!(s.platforms_for_root("K").unwrap().len(), 2);
    }

    /// ⚑ **THE TWO DIRECTIONS AGREE, so nobody's page counts another human's play.**
    ///
    /// `platforms_for_root` is the inverse of `resolve_root`, and it used to not be: it took "latest
    /// wins" only among records that already shared the root it was asked about, so a binding under
    /// an old root was never superseded by a later binding of the same account under a new one. A
    /// consumer that widens a view by it (`/you` unions these custodial keys into "your" history)
    /// would then count a key `resolve_root` says belongs to somebody else.
    ///
    /// Driven on the case that actually produces such a row: a player ran the ceremony on a code a
    /// stranger handed them (the phishing case the consent box guards against and the missing un-link
    /// door cannot tidy up), and the stranger later linked that account correctly.
    #[test]
    fn a_rebound_account_leaves_the_old_roots_view_in_both_directions() {
        let mut s = InMemoryLinkStore::default();
        // The bad row: the victim's root, the stranger's account, the victim's own signature.
        s.record(&rec("victimK", "discord", "111", "custD", 100))
            .unwrap();
        // NON-VACUOUS: while it is the only row it IS the victim's, in both directions.
        assert_eq!(s.resolve_root("custD").unwrap(), Some("victimK".into()));
        assert_eq!(s.platforms_for_root("victimK").unwrap().len(), 1);

        // The real owner links the same account to their own phrase, later.
        s.record(&rec("ownerK", "discord", "111", "custD", 200))
            .unwrap();
        assert_eq!(s.resolve_root("custD").unwrap(), Some("ownerK".into()));
        assert!(
            s.platforms_for_root("victimK").unwrap().is_empty(),
            "⚑ a superseded binding must leave the old root's view, or /you counts another human's \
             history as yours"
        );
        let owned = s.platforms_for_root("ownerK").unwrap();
        assert_eq!(owned.len(), 1);
        assert_eq!(owned[0].custodial_pubkey_hex, "custD");

        // The tie-break matches `resolve_root`'s strict `>`: on the SAME second, later file order
        // wins — so a same-second rebind moves in both directions or in neither.
        let mut tied = InMemoryLinkStore::default();
        tied.record(&rec("firstK", "discord", "7", "custX", 100))
            .unwrap();
        tied.record(&rec("secondK", "discord", "7", "custX", 100))
            .unwrap();
        assert_eq!(tied.resolve_root("custX").unwrap(), Some("secondK".into()));
        assert!(tied.platforms_for_root("firstK").unwrap().is_empty());
        assert_eq!(tied.platforms_for_root("secondK").unwrap().len(), 1);

        // A root's OTHER bindings are untouched by a rebind of one of them.
        let mut many = InMemoryLinkStore::default();
        many.record(&rec("K", "discord", "1", "custD", 100))
            .unwrap();
        many.record(&rec("K", "telegram", "2", "custT", 100))
            .unwrap();
        many.record(&rec("K", "web", "K", "K", 100)).unwrap();
        many.record(&rec("other", "discord", "1", "custD", 300))
            .unwrap();
        let mut left: Vec<String> = many
            .platforms_for_root("K")
            .unwrap()
            .into_iter()
            .map(|r| r.platform)
            .collect();
        left.sort();
        assert_eq!(left, vec!["telegram", "web"]);
    }

    /// An unlinked custodial key is its own identity — resolution is additive, never breaks the
    /// common case.
    #[test]
    fn an_unlinked_key_resolves_to_none() {
        let s = InMemoryLinkStore::default();
        assert_eq!(s.resolve_root("stranger").unwrap(), None);
    }

    /// The deep-version first brick: two platforms linked to one root resolve to the SAME stable
    /// account id (not the raw pubkey), and it is byte-identical to `account_id_of_root(K)` — the
    /// id the identity cell will key on.
    #[test]
    fn resolve_root_account_gives_one_stable_id_across_platforms() {
        let root_hex = "aa".repeat(32); // a 64-hex root pubkey
        let mut s = InMemoryLinkStore::default();
        s.record(&rec(&root_hex, "discord", "111", "custD", 100))
            .unwrap();
        s.record(&rec(&root_hex, "telegram", "222", "custT", 101))
            .unwrap();
        let acct = account_id_of_root(&root_hex).expect("valid hex derives an account id");
        assert_eq!(s.resolve_root_account("custD").unwrap(), Some(acct.clone()));
        assert_eq!(s.resolve_root_account("custT").unwrap(), Some(acct));
        // it is the DERIVED stable id, not the raw pubkey
        assert_ne!(
            s.resolve_root_account("custD").unwrap(),
            s.resolve_root("custD").unwrap()
        );
        assert_eq!(s.resolve_root_account("stranger").unwrap(), None); // unlinked
        assert_eq!(account_id_of_root("not-hex"), None); // malformed → None, no panic
    }

    /// A rebind supersedes: the LATEST link for a custodial key wins.
    #[test]
    fn the_latest_link_wins() {
        let mut s = InMemoryLinkStore::default();
        s.record(&rec("K1", "discord", "111", "custD", 100))
            .unwrap();
        s.record(&rec("K2", "discord", "111", "custD", 200))
            .unwrap();
        assert_eq!(s.resolve_root("custD").unwrap(), Some("K2".into()));
    }

    /// The file store round-trips + survives a reopen (durable, cross-process shape).
    #[test]
    fn file_store_persists_and_reopens() {
        let dir = std::env::temp_dir().join(format!("dregg-link-test-{}", std::process::id()));
        let path = dir.join("links.tsv");
        let _ = std::fs::remove_file(&path);
        {
            let mut s = FileLinkStore::new(&path);
            s.record(&rec("K", "discord", "111", "custD", 100)).unwrap();
            s.record(&rec("K", "telegram", "222", "custT", 101))
                .unwrap();
        }
        let s2 = FileLinkStore::new(&path); // a fresh handle = a different "process"
        assert_eq!(s2.resolve_root("custD").unwrap(), Some("K".into()));
        assert_eq!(s2.resolve_root("custT").unwrap(), Some("K".into()));
        assert_eq!(s2.all().unwrap().len(), 2);
        let _ = std::fs::remove_dir_all(&dir);
    }

    #[test]
    fn a_delimiter_in_a_field_is_refused_by_the_encoder() {
        assert!(rec("K", "dis\tcord", "1", "c", 1).to_line().is_none());
        assert!(rec("K", "discord", "1", "c", 1).to_line().is_some());
    }
}
