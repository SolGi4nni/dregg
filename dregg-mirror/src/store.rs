//! # THE STORE — content-addressed lookup, and the git-style short prefix.
//!
//! The mirror is a *resolver*, so the store is the one thing it needs from the world:
//! address → bytes. It is a trait so the deployed shape (a node/gateway fetch) and the
//! test shape (an in-memory map) drive the IDENTICAL routing + verification logic, exactly
//! as `netlayer.ts` injects its transport.
//!
//! ## THE SHORT PREFIX
//!
//! X truncates displayed link text, so the *published* link must be short enough to survive
//! being read off a screen. Git solved this: publish a prefix, resolve it against the
//! corpus, and refuse when it is ambiguous. [`ObjectStore::resolve_prefix`] is that, with
//! the floor at [`MIN_PREFIX_HEX`](crate::uri::MIN_PREFIX_HEX) hex characters.
//!
//! Ambiguity is a REFUSAL, never a pick. Serving "the first match" would mean a poster
//! could not know what their own link points at, and a later-added object could silently
//! change where a published link lands. The full address always stays canonical: the page
//! a short link resolves to prints, and links to, the FULL form.
//!
//! Prefixes are resolved WITHIN a kind. Two objects of different kinds sharing a prefix do
//! not collide, because the kind is in the path.

use std::collections::BTreeMap;
use std::path::{Path, PathBuf};

use crate::object::{Attestation, Envelope, content_addr};
use crate::uri::Kind;

/// What a short prefix resolved to.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum PrefixResolution {
    /// Exactly one object matched — the full 64-hex address.
    Unique(String),
    /// More than one matched. A REFUSAL (404), with the candidates so a human can
    /// disambiguate, git-style. Bounded so a huge corpus cannot make the page enormous.
    Ambiguous(Vec<String>),
    /// Nothing matched.
    None,
}

/// The mirror's view of the world: content address → envelope.
pub trait ObjectStore: Send + Sync {
    /// Fetch the envelope stored at a FULL address under `kind`, or `None`.
    fn get(&self, kind: Kind, addr_hex: &str) -> Option<Envelope>;

    /// Resolve a hex prefix within `kind`. See the module doc on why ambiguity refuses.
    fn resolve_prefix(&self, kind: Kind, prefix_hex: &str) -> PrefixResolution;

    /// Every full address held under `kind` — the index page's listing. Bounded by the
    /// caller; a store is free to return a truncated view.
    fn list(&self, kind: Kind) -> Vec<String>;
}

/// How many candidates an [`PrefixResolution::Ambiguous`] carries at most.
pub const MAX_AMBIGUOUS_SHOWN: usize = 8;

/// An in-memory store: the test substrate, and the shape a `--seed` demo run uses.
#[derive(Debug, Clone, Default)]
pub struct MemoryStore {
    objects: BTreeMap<(Kind, String), Envelope>,
}

impl MemoryStore {
    /// An empty store.
    pub fn new() -> MemoryStore {
        MemoryStore::default()
    }

    /// Insert content bytes under `kind`, returning the address they hash to. The address
    /// is DERIVED, never supplied — a store cannot be seeded with a lie about an address.
    pub fn insert(&mut self, kind: Kind, content: impl Into<Vec<u8>>) -> String {
        self.insert_attested(kind, content, None)
    }

    /// Insert with a federation attestation attached.
    pub fn insert_attested(
        &mut self,
        kind: Kind,
        content: impl Into<Vec<u8>>,
        attestation: Option<Attestation>,
    ) -> String {
        let content = content.into();
        let addr = content_addr(&content);
        self.objects.insert(
            (kind, addr.clone()),
            Envelope {
                content,
                attestation,
            },
        );
        addr
    }

    /// Insert bytes at a CALLER-CHOSEN address, which they need not hash to.
    ///
    /// The two fixtures that need this, and cannot be built any other way:
    ///
    /// * **hostile substitution** — bytes served under an address they do not hash to.
    ///   The router's content-address gate is exactly what must catch this.
    /// * **a prefix collision** — two objects sharing 8 hex of address. Finding a real one
    ///   costs ~2^32 blake3 evaluations, so the fixture places them. What is under test is
    ///   that the router REFUSES an ambiguous prefix rather than picking, not how the
    ///   collision arose.
    ///
    /// Never used by a serving path: the address a published object gets is always
    /// [`insert`](MemoryStore::insert)'s derived one.
    pub fn insert_at(&mut self, kind: Kind, addr_hex: &str, content: impl Into<Vec<u8>>) {
        self.objects.insert(
            (kind, addr_hex.to_ascii_lowercase()),
            Envelope::unattested(content),
        );
    }

    /// How many objects are held.
    pub fn len(&self) -> usize {
        self.objects.len()
    }

    /// Is the store empty?
    pub fn is_empty(&self) -> bool {
        self.objects.is_empty()
    }
}

impl ObjectStore for MemoryStore {
    fn get(&self, kind: Kind, addr_hex: &str) -> Option<Envelope> {
        self.objects
            .get(&(kind, addr_hex.to_ascii_lowercase()))
            .cloned()
    }

    fn resolve_prefix(&self, kind: Kind, prefix_hex: &str) -> PrefixResolution {
        let p = prefix_hex.to_ascii_lowercase();
        let mut hits: Vec<String> = self
            .objects
            .keys()
            .filter(|(k, a)| *k == kind && a.starts_with(&p))
            .map(|(_, a)| a.clone())
            .collect();
        match hits.len() {
            0 => PrefixResolution::None,
            1 => PrefixResolution::Unique(hits.remove(0)),
            _ => {
                hits.truncate(MAX_AMBIGUOUS_SHOWN);
                PrefixResolution::Ambiguous(hits)
            }
        }
    }

    fn list(&self, kind: Kind) -> Vec<String> {
        self.objects
            .keys()
            .filter(|(k, _)| *k == kind)
            .map(|(_, a)| a.clone())
            .collect()
    }
}

/// A filesystem store — the deployed shape until a node/gateway fetch replaces it.
///
/// Layout: `<root>/<kind>/<64-hex>.json` are the content bytes; an optional sibling
/// `<64-hex>.att.json` is the attestation. The FILENAME is not trusted: the router
/// re-hashes the bytes and refuses if they do not hash to the address that was asked for,
/// so a mis-named or tampered file fails closed rather than serving as something else.
#[derive(Debug, Clone)]
pub struct DirStore {
    root: PathBuf,
}

impl DirStore {
    /// A store rooted at `root`. The directory need not exist yet (a missing kind
    /// directory simply holds nothing).
    pub fn new(root: impl Into<PathBuf>) -> DirStore {
        DirStore { root: root.into() }
    }

    fn kind_dir(&self, kind: Kind) -> PathBuf {
        self.root.join(kind.as_str())
    }

    /// Full addresses under `kind`, read from the directory listing. Non-conforming
    /// filenames are ignored rather than guessed at.
    fn addrs(&self, kind: Kind) -> Vec<String> {
        let Ok(entries) = std::fs::read_dir(self.kind_dir(kind)) else {
            return Vec::new();
        };
        let mut out: Vec<String> = entries
            .flatten()
            .filter_map(|e| {
                let name = e.file_name().to_string_lossy().into_owned();
                let stem = name.strip_suffix(".json")?;
                if stem.ends_with(".att") {
                    return None;
                }
                let stem = stem.to_ascii_lowercase();
                (stem.len() == crate::uri::FULL_ADDR_HEX
                    && stem.chars().all(|c| c.is_ascii_hexdigit()))
                .then_some(stem)
            })
            .collect();
        out.sort();
        out
    }

    fn read(&self, dir: &Path, addr_hex: &str) -> Option<Envelope> {
        let content = std::fs::read(dir.join(format!("{addr_hex}.json"))).ok()?;
        let attestation = std::fs::read(dir.join(format!("{addr_hex}.att.json")))
            .ok()
            .and_then(|b| serde_json::from_slice::<Attestation>(&b).ok());
        Some(Envelope {
            content,
            attestation,
        })
    }
}

impl ObjectStore for DirStore {
    fn get(&self, kind: Kind, addr_hex: &str) -> Option<Envelope> {
        let addr = addr_hex.to_ascii_lowercase();
        // Path-traversal floor: only a full lowercase hex address ever becomes a path
        // component, so a crafted addr can never escape the kind directory.
        if addr.len() != crate::uri::FULL_ADDR_HEX || !addr.chars().all(|c| c.is_ascii_hexdigit()) {
            return None;
        }
        self.read(&self.kind_dir(kind), &addr)
    }

    fn resolve_prefix(&self, kind: Kind, prefix_hex: &str) -> PrefixResolution {
        let p = prefix_hex.to_ascii_lowercase();
        let mut hits: Vec<String> = self
            .addrs(kind)
            .into_iter()
            .filter(|a| a.starts_with(&p))
            .collect();
        match hits.len() {
            0 => PrefixResolution::None,
            1 => PrefixResolution::Unique(hits.remove(0)),
            _ => {
                hits.truncate(MAX_AMBIGUOUS_SHOWN);
                PrefixResolution::Ambiguous(hits)
            }
        }
    }

    fn list(&self, kind: Kind) -> Vec<String> {
        self.addrs(kind)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn prefix_refuses_rather_than_picking() {
        let mut s = MemoryStore::new();
        // Two objects whose addresses are DERIVED; find a shared prefix by construction.
        let a = s.insert(Kind::Poll, b"one".to_vec());
        let b = s.insert(Kind::Poll, b"two".to_vec());
        assert_ne!(a, b);
        // A 1-char prefix that both share (if any) must be Ambiguous; the empty prefix
        // always is, and is what the classifier would already have refused as too short.
        assert_eq!(
            s.resolve_prefix(Kind::Poll, ""),
            PrefixResolution::Ambiguous(vec![a.clone().min(b.clone()), a.clone().max(b.clone())])
        );
        assert_eq!(
            s.resolve_prefix(Kind::Poll, &a[..16]),
            PrefixResolution::Unique(a)
        );
    }

    #[test]
    fn prefixes_do_not_collide_across_kinds() {
        let mut s = MemoryStore::new();
        let a = s.insert(Kind::Poll, b"same bytes".to_vec());
        let b = s.insert(Kind::Story, b"same bytes".to_vec());
        assert_eq!(a, b, "same bytes ⇒ same address");
        assert_eq!(
            s.resolve_prefix(Kind::Poll, &a[..8]),
            PrefixResolution::Unique(a.clone())
        );
        assert_eq!(
            s.resolve_prefix(Kind::Story, &a[..8]),
            PrefixResolution::Unique(a)
        );
    }

    #[test]
    fn dir_store_refuses_a_traversal_addr() {
        let s = DirStore::new("/nonexistent-mirror-root");
        assert!(s.get(Kind::Poll, "../../etc/passwd").is_none());
    }
}
