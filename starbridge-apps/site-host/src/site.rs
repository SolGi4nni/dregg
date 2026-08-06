//! The content model of a hosted minisite and its deterministic commitment.
//!
//! A hosted site is a path -> [`Asset`] map ([`SiteContent`]). Its [`content_root`]
//! is the kernel's REAL sorted-Poseidon2 heap commitment (the same hash family,
//! heap-root function, and 8-felt faithful widening the kernel commits an umem cell
//! heap with), so a stranger re-witnesses the served bytes against the same
//! collision-resistant root the kernel understands. There is no non-cryptographic
//! fallback: the commitment is real Poseidon2 on every build.

use std::collections::BTreeMap;

use serde::{Deserialize, Serialize};

/// One static asset within a site: the served bytes plus the `Content-Type`.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct Asset {
    /// The `Content-Type` header value for this asset.
    pub content_type: String,
    /// The asset bytes (HTML/CSS/JS/image/…).
    pub body: Vec<u8>,
}

impl Asset {
    /// An asset with an explicit content-type.
    pub fn new(content_type: impl Into<String>, body: impl Into<Vec<u8>>) -> Asset {
        Asset {
            content_type: content_type.into(),
            body: body.into(),
        }
    }

    /// An asset whose content-type is inferred from `path`'s extension.
    pub fn at(path: &str, body: impl Into<Vec<u8>>) -> Asset {
        Asset {
            content_type: content_type_for(path).to_string(),
            body: body.into(),
        }
    }
}

/// The content of a hosted minisite: request-path -> [`Asset`].
///
/// Keys are absolute request paths (`/`, `/index.html`, `/style.css`, …). A
/// [`BTreeMap`] so the content — and thus its [`content_root`] — is canonically
/// ordered regardless of insertion order.
#[derive(Debug, Clone, Default, PartialEq, Eq, Serialize, Deserialize)]
pub struct SiteContent {
    /// path -> asset, canonically ordered.
    pub assets: BTreeMap<String, Asset>,
}

impl SiteContent {
    /// Empty content.
    pub fn new() -> SiteContent {
        SiteContent {
            assets: BTreeMap::new(),
        }
    }

    /// Add an asset at `path`, content-type inferred from the extension.
    pub fn with(mut self, path: impl Into<String>, body: impl Into<Vec<u8>>) -> SiteContent {
        let path = path.into();
        let asset = Asset::at(&path, body);
        self.assets.insert(normalize_key(&path), asset);
        self
    }

    /// Add an asset at `path` with an explicit content-type.
    pub fn with_typed(
        mut self,
        path: impl Into<String>,
        content_type: impl Into<String>,
        body: impl Into<Vec<u8>>,
    ) -> SiteContent {
        let path = path.into();
        self.assets
            .insert(normalize_key(&path), Asset::new(content_type, body));
        self
    }

    /// Whether the site has no assets (an empty site cannot be published).
    pub fn is_empty(&self) -> bool {
        self.assets.is_empty()
    }

    /// Number of assets.
    pub fn len(&self) -> usize {
        self.assets.len()
    }

    /// Resolve a request `path` to an asset, applying static-host conventions:
    /// `/` (or empty) -> `/index.html`; an extension-less directory-style path that
    /// misses -> `<path>/index.html`.
    pub fn resolve(&self, path: &str) -> Option<&Asset> {
        let key = normalize_key(path);
        if let Some(a) = self.assets.get(&key) {
            return Some(a);
        }
        if !key.ends_with('/') && !key.ends_with(".html") {
            let dir_index = format!("{key}/index.html");
            if let Some(a) = self.assets.get(&dir_index) {
                return Some(a);
            }
        }
        None
    }
}

/// Whether `name` is a usable subdomain label: non-empty, ≤63 chars, only
/// `[a-z0-9-]`, not starting/ending with `-`. Keeps a site name a valid DNS label
/// and a clean commitment key.
pub fn is_valid_name(name: &str) -> bool {
    if name.is_empty() || name.len() > 63 {
        return false;
    }
    if name.starts_with('-') || name.ends_with('-') {
        return false;
    }
    name.bytes()
        .all(|b| b.is_ascii_lowercase() || b.is_ascii_digit() || b == b'-')
}

/// Normalize a request/content path to a canonical content key: `""`/`"/"` ->
/// `/index.html`; a trailing slash -> `…/index.html`; otherwise a leading `/` ensured.
pub fn normalize_key(path: &str) -> String {
    let path = path.trim();
    if path.is_empty() || path == "/" {
        return "/index.html".to_string();
    }
    let with_slash = if path.starts_with('/') {
        path.to_string()
    } else {
        format!("/{path}")
    };
    if with_slash.ends_with('/') {
        format!("{with_slash}index.html")
    } else {
        with_slash
    }
}

/// A deterministic content commitment over a site's content — the REAL
/// sorted-Poseidon2 cell-heap commitment (see [`poseidon2::content_root`]).
///
/// This makes the hosted content's commitment real Poseidon2 and locally
/// re-witnessable: a stranger recomputes it from the served bytes and matches the
/// published root with no trust in the host. The remaining seam — an on-chain
/// `Effect::Write` committing this heap to a node and a light client witnessing that
/// write in-circuit — is the circuit epoch, deliberately not done here; the
/// off-chain commitment is real today.
pub fn content_root(content: &SiteContent) -> String {
    poseidon2::content_root(content)
}

/// The REAL sorted-Poseidon2 site-content commitment.
///
/// A site's content (path -> asset) is committed the way the kernel commits a
/// cell's umem heap:
///
/// 1. each asset is hashed to a WIDE 8-felt (~124-bit) Poseidon2 digest binding the
///    length-delimited `(path, content_type, body)`;
/// 2. those 8 felts are placed in the canonical SORTED Poseidon2 Merkle heap keyed
///    by `(collection = path, key = limb-index)` and the kernel's heap-root function
///    folds the root;
/// 3. the published `content_root` is the kernel's 8-felt faithful widening over the
///    per-asset wide limbs with the heap root as the final `iroot` — a WIDE carrier
///    chain with no 31-bit intermediate, so the commitment matches the proof's
///    ~130-bit FRI soundness (not the ~31-bit floor a single felt would be).
///
/// Real Poseidon2, locally re-witnessable.
pub mod poseidon2 {
    use super::SiteContent;
    use dregg_circuit::field::BabyBear;
    use dregg_circuit::heap_root::compute_heap_root_entries;
    use dregg_circuit::poseidon2::{hash_bytes, hash_many_8, wire_commit_8};

    /// Domain separation for the site-content commitment (distinct from any other
    /// heap use). Brand-neutral: this crate is public substrate.
    const DOMAIN: &[u8] = b"site-host-content-root-v1";

    /// The published site content commitment — see the module docs.
    pub fn content_root(content: &SiteContent) -> String {
        let mut entries: Vec<((BabyBear, BabyBear), BabyBear)> = Vec::new();
        let mut limbs: Vec<BabyBear> = Vec::new();
        for (path, asset) in &content.assets {
            let d8 = asset_digest8(path, &asset.content_type, &asset.body);
            // ⚑ CLASS (B) — a ONE-FELT `hash_bytes` image, deliberately. **The byte-exact
            // companion is `asset_digest8` on the line above** (this file): it absorbs the path
            // through `absorb_len_delimited` — a byte-length felt then the INJECTIVE 3-bytes-per
            // -felt packing — so the path is bound at eight lanes inside `d8`, whose limbs are
            // pushed into `limbs` and absorbed by `wire_commit_8(&pre, heap_root)` below. Two
            // paths colliding under `hash_bytes` therefore still produce different `pre`, and
            // `content_root` separates them at 2^123.63 rather than this felt's 2^15.45. `coll`
            // reaches only `heap_root`, which enters as the `iroot` argument.
            //
            // ⚠ Written here because the argument is invisible from the call site: what makes
            // this (B) and not (A) is that the path is bound TWICE. A future opening that serves
            // a Merkle PATH through this heap (rather than the whole limb vector) would address
            // the leaf by `coll` alone and make it (A). Sibling with the identical argument and
            // the identical shape: `storage/src/bucket_commitment.rs`'s `fold_leaves`.
            //
            // ⓘ What the collision DOES buy, and why this site needs no repair where the sibling
            // did (2026-08-06). Two paths colliding here land eight entries on the same
            // `heap_addr(coll, i)` coordinates, and `heap_root::assert_addr_unique` PANICS on a
            // duplicated address — refusing to publish an ambiguous root, which is the correct
            // fail-closed producer behaviour. `storage`'s twin had the SAME fold reachable from
            // `verify_opening`, whose `ObjectOpening` is `Deserialize`-derived UNTRUSTED input, so
            // there it was an unauthenticated remote abort and now refuses at a leg-(0) check.
            // There is no such verifier here: `content_root` is only ever called on the host's own
            // `SiteContent`, never on a stranger's leaf list. If one is ever added, it must not
            // fold a supplied list before checking it — see
            // `storage/tests/bucket_opening_coll_collision_dos.rs`.
            let coll = hash_bytes(path.as_bytes());
            for (i, &limb) in d8.iter().enumerate() {
                entries.push(((coll, BabyBear::new(i as u32)), limb));
                limbs.push(limb);
            }
        }
        let heap_root = compute_heap_root_entries(&entries);
        // The faithful 8-felt commitment: a WIDE-carrier fold over the per-asset wide
        // limbs (no 31-bit intermediate), bound to the heap root, the asset count, and
        // a domain tag. The 4-felt domain header keeps the fold total when content is
        // empty (the publish path forbids that, belt-and-braces).
        let mut pre = vec![
            // ⚑ CLASS (C) — no attacker input. `DOMAIN` is a compile-time constant with no free
            // parameter, so no search exists at any price; the a-priori chance of clashing with
            // the one byte-identically-shaped sibling scheme
            // (`storage::bucket_commitment`'s `b"dregg-bucket-content-root-v1"`) is 2^-30.906891
            // and is settled by inspection, not by an adversary. The 2^15.45 birthday figure
            // does NOT apply: birthday needs a chooser on both sides and there is none.
            hash_bytes(DOMAIN),
            BabyBear::new(content.assets.len() as u32),
            BabyBear::ZERO,
            BabyBear::ZERO,
        ];
        pre.extend_from_slice(&limbs);
        felts8_to_hex(&wire_commit_8(&pre, heap_root))
    }

    /// The per-asset WIDE (8-felt, ~124-bit) Poseidon2 digest over the
    /// length-delimited `(path, content_type, body)`.
    fn asset_digest8(path: &str, content_type: &str, body: &[u8]) -> [BabyBear; 8] {
        let mut input: Vec<BabyBear> = Vec::new();
        absorb_len_delimited(&mut input, path.as_bytes());
        absorb_len_delimited(&mut input, content_type.as_bytes());
        absorb_len_delimited(&mut input, body);
        hash_many_8(&input)
    }

    /// Push a length felt then the packed bytes, so field-domain concatenation is
    /// unambiguous (a server cannot shift bytes between fields without moving the
    /// digest). Bytes are packed with the INJECTIVE [`pack_bytes`].
    fn absorb_len_delimited(out: &mut Vec<BabyBear>, bytes: &[u8]) {
        out.push(BabyBear::new(bytes.len() as u32));
        out.extend(pack_bytes(bytes));
    }

    /// INJECTIVE byte -> field packing for the content commitment.
    ///
    /// Packs 3 little-endian bytes per element (a u24 value `< 2^24 ≤ p`, so
    /// `BabyBear::new` performs no modular reduction). Deliberately NOT the shared
    /// 4-byte packing that reduces `% p`: since `p ≈ 2^30.9 < 2^32`, ~53% of 4-byte
    /// chunks alias their `+p` partner, so two distinct equal-length byte strings
    /// could produce the identical `content_root`. With 3 bytes/felt there is no
    /// wraparound; combined with the length prefix the map is injective for same- and
    /// different-length inputs alike.
    fn pack_bytes(bytes: &[u8]) -> Vec<BabyBear> {
        let mut out = Vec::with_capacity(bytes.len() / 3 + 1);
        for chunk in bytes.chunks(3) {
            let mut val: u32 = 0;
            for (j, &b) in chunk.iter().enumerate() {
                val |= (b as u32) << (j * 8);
            }
            out.push(BabyBear::new(val));
        }
        out
    }

    /// Lower-hex encode an 8-felt digest (8 × u32 -> 64 hex chars; ~124-bit
    /// collision resistance, matching the proof's FRI soundness floor).
    fn felts8_to_hex(f: &[BabyBear; 8]) -> String {
        use std::fmt::Write as _;
        let mut s = String::with_capacity(64);
        for x in f {
            let _ = write!(s, "{:08x}", x.as_u32());
        }
        s
    }
}

/// Infer a `Content-Type` from a path's file extension. Unknown extensions get
/// `application/octet-stream` (a safe, downloadable default).
pub fn content_type_for(path: &str) -> &'static str {
    let ext = path.rsplit('.').next().unwrap_or("").to_ascii_lowercase();
    match ext.as_str() {
        "html" | "htm" => "text/html; charset=utf-8",
        "css" => "text/css; charset=utf-8",
        "js" | "mjs" => "text/javascript; charset=utf-8",
        "json" => "application/json",
        "wasm" => "application/wasm",
        "svg" => "image/svg+xml",
        "png" => "image/png",
        "jpg" | "jpeg" => "image/jpeg",
        "gif" => "image/gif",
        "webp" => "image/webp",
        "avif" => "image/avif",
        "ico" => "image/x-icon",
        "txt" | "text" => "text/plain; charset=utf-8",
        "xml" => "application/xml",
        "pdf" => "application/pdf",
        "woff2" => "font/woff2",
        "woff" => "font/woff",
        "ttf" => "font/ttf",
        "otf" => "font/otf",
        "map" => "application/json",
        "webmanifest" => "application/manifest+json",
        _ => "application/octet-stream",
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn content_type_inference() {
        assert_eq!(content_type_for("/index.html"), "text/html; charset=utf-8");
        assert_eq!(content_type_for("/a/style.css"), "text/css; charset=utf-8");
        assert_eq!(
            content_type_for("/app.js"),
            "text/javascript; charset=utf-8"
        );
        assert_eq!(content_type_for("/logo.png"), "image/png");
        assert_eq!(content_type_for("/data.bin"), "application/octet-stream");
        assert_eq!(content_type_for("/noext"), "application/octet-stream");
    }

    #[test]
    fn name_validation() {
        assert!(is_valid_name("blog"));
        assert!(is_valid_name("my-site-2"));
        assert!(!is_valid_name(""));
        assert!(!is_valid_name("-x"));
        assert!(!is_valid_name("x-"));
        assert!(!is_valid_name("Has.Dot"));
        assert!(!is_valid_name("has space"));
    }

    #[test]
    fn content_root_is_deterministic_order_independent_and_sensitive() {
        let a = SiteContent::new()
            .with("/index.html", "hi")
            .with("/x.css", "body{}");
        let b = SiteContent::new()
            .with("/x.css", "body{}")
            .with("/index.html", "hi");
        assert_eq!(
            content_root(&a),
            content_root(&b),
            "BTreeMap canonical order"
        );
        assert_eq!(content_root(&a).len(), 64, "wide 8-felt commitment");

        // A single flipped byte moves the root.
        let c = SiteContent::new()
            .with("/index.html", "hí")
            .with("/x.css", "body{}");
        assert_ne!(content_root(&a), content_root(&c));
    }

    #[test]
    fn resolve_applies_index_conventions() {
        let s = SiteContent::new()
            .with("/index.html", "root")
            .with("/docs/index.html", "docs");
        assert_eq!(s.resolve("/").unwrap().body, b"root");
        assert_eq!(s.resolve("").unwrap().body, b"root");
        assert_eq!(s.resolve("/docs").unwrap().body, b"docs");
        assert_eq!(s.resolve("/docs/").unwrap().body, b"docs");
        assert!(s.resolve("/missing").is_none());
    }
}
