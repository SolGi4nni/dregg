//! **Cap-gate STORAGE.** The confined Android app's scoped-storage / `MediaStore` /
//! file-URI reach reforged from an ambient per-UID filesystem + media database into a
//! cap-bounded, spotter-resolved, receipted reach to a **named storage cell** —
//! `GRAPHIDEOS.md §1` (the storage-model row) made real, in the same shape as the proven
//! [`crate::contentgate`] / [`crate::organgate`] / [`crate::permgate`] gates and the
//! `APPS-AS-CELLS.md §1` `Fs` → `FirmamentFs` → turns seam.
//!
//! # What Android does (the ambient mechanism deos replaces)
//!
//! Stock Android storage is two ambient surfaces over one per-UID filesystem:
//!
//! 1. **Scoped storage + DAC-per-UID.** Each app's files live under a UID-owned tree
//!    (`/data/data/<pkg>`, `/storage/emulated/0/Android/data/<pkg>`); the Linux DAC owns
//!    them by UID. An app reaches its OWN scope freely (no permission), but the boundary
//!    is the kernel's UID check, not a cap — and a `MANAGE_EXTERNAL_STORAGE` /
//!    `READ_EXTERNAL_STORAGE` grant re-opens a *device-wide* ambient view.
//! 2. **`MediaStore` — the shared media database.** The `Images`/`Video`/`Audio`/
//!    `Downloads` collections are reached through a `content://media/...` URI routed by the
//!    privileged `MediaProvider` against the whole device's media index. A read is gated by
//!    `READ_MEDIA_*`/`READ_EXTERNAL_STORAGE`; a write to another app's item needs a
//!    `RecoverableSecurityException`/`createWriteRequest` user-consent dance. The backend
//!    is a standing ambient authority over *all* media on the device.
//!
//! Either way the authority is ambient: a path or a `content://media/...` URI names a
//! location, and a UID flag / framework grant decides — there is no cap in the app's hand.
//!
//! # What graphideOS does (the cap-over-cell-graph reforge)
//!
//! `GRAPHIDEOS.md §1`: *"files/media are cells (or substances of cells); a read is
//! authority-checked, a write is a receipted turn; no ambient FS."* `APPS-AS-CELLS.md §1`
//! grounds the shape: a storage tree is a `DirectoryCell`, `load(path)` is an
//! authority-checked read over the dir cap, `save(path, c)` is a **dregg TURN** spending a
//! write cap (Σδ=0 over the content cell, the receipt is the "saved" ack). This module is
//! the android-cell face of that, in the same shape as the sibling gates:
//!
//! 1. **Resolution is over the cap-reachable storage neighborhood, not the device FS.** The
//!    [`StorageResolver`] holds exactly the storage-volume cells the android-cell was
//!    *granted* a cap to reach — decidedly NOT a device-wide filesystem or `MediaProvider`.
//!    A path/URI whose [`StorageVolume`] no cap-reachable cell holds is
//!    [`StorageDecision::RefusedUnreachable`]: **the app cannot read storage it was never
//!    handed a cap to** (no ambient FS; another app's scope is simply not in the
//!    neighborhood). An app reaches its OWN scope because — and only because — it holds a
//!    cap to its own storage cell, born at install.
//! 2. **A read is a cap-bounded authorized query; a write is a receipted turn.** Faithful to
//!    `APPS-AS-CELLS.md §1`: a [`StorageAccess::Read`] is an authority-checked `load` over
//!    the granted storage cell; a [`StorageAccess::Write`] is a `save` that commits as a
//!    **receipted turn** against the storage cell (and needs a write-granting cap).
//! 3. **Write authority is the attenuation tooth.** A *write* against a volume the holder was
//!    granted only **read** ([`StorageGrant::ReadOnly`]) is [`StorageDecision::RefusedReadOnly`]
//!    — a read cap does not amplify to a write (the `granted ⊆ held` lattice, storage-side).
//!    AOSP's `READ_EXTERNAL_STORAGE` vs `WRITE_EXTERNAL_STORAGE` split becomes a cap
//!    attenuation checked at the gate, before any byte is touched.
//! 4. **Ambiguity is an explicit chooser, never a silent route.** Two cap-reachable cells
//!    claiming one volume ⟹ [`StorageDecision::Ambiguous`] (the powerbox-style ceremony) —
//!    e.g. two providers both claiming the media-images collection; deos refuses to silently
//!    pick.
//!
//! Every decision leaves a content-addressed [`StorageReceipt`], so the android-cell's
//! storage traffic is auditable end to end exactly like the content / service / intent
//! receipts.
//!
//! # The depth (honest, like the content + service gates')
//!
//! This is the **reach-and-authority** layer: the gate decides, against the granted storage
//! set + its grants, whether (and how) a storage access may proceed, and records it. The
//! remaining frontier — interposing the *actual* `MediaProvider` binder transaction + the
//! VFS/FUSE `open(2)` the confined runtime issues so the device kernel itself routes only
//! cap-admitted reads/writes (the HAL/binder leg the sibling gates name), and binding a
//! write's receipt to a real `FirmamentFs` `save` turn on-device — is the same not-yet-claimed
//! depth. What IS real today: the reach-resolution algebra over scoped paths AND
//! `content://media/...` URIs + the read/write attenuation teeth + the receipt, testable on
//! any node with no device.

use dregg_firmament::CellId;

/// A shared `MediaStore` collection — the cross-app media buckets AOSP's `MediaProvider`
/// indexes (`MediaStore.Images`/`Video`/`Audio`/`Downloads`). Each becomes a deos storage
/// cell; the SET an android-cell holds a cap to is the entire shared-media authority it may
/// ever reach (no ambient `MediaProvider`).
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum MediaKind {
    /// `MediaStore.Images` (`content://media/external/images`, the `DCIM`/`Pictures` dirs).
    Images,
    /// `MediaStore.Video` (`content://media/external/video`, the `Movies`/`DCIM` dirs).
    Video,
    /// `MediaStore.Audio` (`content://media/external/audio`, the `Music` dir).
    Audio,
    /// `MediaStore.Downloads` (`content://media/external/downloads`, the `Download` dir).
    Downloads,
}

impl MediaKind {
    /// The `MediaStore` collection token as it appears in a `content://media/<vol>/<token>`
    /// URI (lower-cased) — the stable key a storage cell answers on.
    pub fn token(&self) -> &'static str {
        match self {
            MediaKind::Images => "images",
            MediaKind::Video => "video",
            MediaKind::Audio => "audio",
            MediaKind::Downloads => "downloads",
        }
    }

    /// Classify a `MediaStore` collection token (the `images`/`video`/`audio`/`downloads`
    /// segment of a `content://media/...` URI, or a shared-dir name). `None` for an
    /// unrecognised token (the caller refuses — fail-closed, no ambient media reach).
    pub fn from_token(token: &str) -> Option<Self> {
        match token.to_ascii_lowercase().as_str() {
            "images" | "image" | "pictures" | "dcim" => Some(MediaKind::Images),
            "video" | "movies" => Some(MediaKind::Video),
            "audio" | "music" => Some(MediaKind::Audio),
            "downloads" | "download" => Some(MediaKind::Downloads),
            _ => None,
        }
    }

    /// The full standard set of media collections — the device's shared-media roster.
    pub fn all() -> [MediaKind; 4] {
        [
            MediaKind::Images,
            MediaKind::Video,
            MediaKind::Audio,
            MediaKind::Downloads,
        ]
    }
}

/// **A storage volume — the unit the cap graph scopes, and the spotter's match key.** Either
/// the app's own scoped-storage sandbox (`getFilesDir`/`getExternalFilesDir` — owner = the
/// app, reachable because it holds a cap to its OWN storage cell), a shared `MediaStore`
/// collection (cross-app, permission-gated in AOSP → cap-gated here), or a named long-tail
/// volume (a SAF document tree, an OTHER physical volume).
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum StorageVolume {
    /// The app's own scoped-storage sandbox, keyed by package (the `/Android/data/<pkg>`
    /// tree). In AOSP an app reaches this with NO permission; in graphideOS it reaches it
    /// because it holds a cap to its own storage cell (granted at install) — never an ambient
    /// UID owner-check.
    AppScope { package: String },
    /// A shared `MediaStore` collection — cross-app shared media, permission-gated in AOSP and
    /// cap-gated here.
    Media(MediaKind),
    /// Any other named storage tree (a SAF document tree, an other-volume root) — the long tail.
    Other(String),
}

impl StorageVolume {
    /// A stable lower-case key for matching, the receipt digest, and the status line.
    pub fn key(&self) -> String {
        match self {
            StorageVolume::AppScope { package } => format!("app:{}", package.to_ascii_lowercase()),
            StorageVolume::Media(kind) => format!("media:{}", kind.token()),
            StorageVolume::Other(s) => format!("other:{}", s.to_ascii_lowercase()),
        }
    }

    /// **The device's storage cell for this volume** — derived deterministically from the
    /// volume key, so distinct volumes (an app scope vs the media-images collection) target
    /// distinct cells and a resolver's storage set distinguishes them. On a real device the
    /// boot resolves these to the actual `DirectoryCell`s (`APPS-AS-CELLS.md §1`); the
    /// key-derived id is the stable stand-in identity, in the SAME spirit as
    /// [`crate::organgate::SystemService::organ_cell`] (a distinct derive-key namespace so a
    /// storage cell and a service organ never alias).
    pub fn storage_cell(&self) -> CellId {
        let mut h = blake3::Hasher::new_derive_key("graphideos-storage-volume-cell-v1");
        h.update(self.key().as_bytes());
        CellId::from_bytes(*h.finalize().as_bytes())
    }

    /// A short human label for the chooser / status line.
    pub fn label(&self) -> String {
        match self {
            StorageVolume::AppScope { package } => format!("{package} (app storage)"),
            StorageVolume::Media(MediaKind::Images) => "Images".into(),
            StorageVolume::Media(MediaKind::Video) => "Video".into(),
            StorageVolume::Media(MediaKind::Audio) => "Audio".into(),
            StorageVolume::Media(MediaKind::Downloads) => "Downloads".into(),
            StorageVolume::Other(s) => s.clone(),
        }
    }
}

/// **A parsed storage reach — a scoped path OR a `content://media/...` URI resolved to its
/// [`StorageVolume`] + the sub-path within it.** The unit the gate routes on: AOSP routes a
/// `MediaStore` URI on its collection and a file on its UID-owned tree; graphideOS routes
/// BOTH on the [`StorageVolume`] (the storage cell key), so one uniform spotter covers both
/// the scoped-storage and the `MediaStore` surface.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct StorageReach {
    /// The volume this reach lands in (the spotter match key).
    pub volume: StorageVolume,
    /// The sub-path within the volume (carried for the receipt + the eventual in-cell
    /// sub-grant); may be empty (the volume root).
    pub path: String,
}

impl StorageReach {
    /// **Parse a storage reach** — either a `content://media/...` `MediaStore` URI or a
    /// filesystem path — into its [`StorageVolume`] + sub-path. Returns `None` for an empty
    /// reach. An unclassifiable filesystem path resolves to a [`StorageVolume::Other`] keyed
    /// by the path (so it is refused unless a cap to exactly that volume was granted — no
    /// ambient FS).
    pub fn parse(reach: &str) -> Option<Self> {
        if reach.is_empty() {
            return None;
        }
        if let Some(rest) = reach.strip_prefix("content://media/") {
            return Some(Self::parse_media_uri(rest));
        }
        Some(Self::parse_path(reach))
    }

    /// Parse the tail of a `content://media/<volume>/<collection>/...` URI. The first segment
    /// is the storage volume name (`external`/`internal`), the second the collection token
    /// (`images`/`video`/…). An unrecognised collection ⟹ [`StorageVolume::Other`] keyed by
    /// the whole tail (refused unless explicitly granted).
    fn parse_media_uri(tail: &str) -> Self {
        let mut segs = tail.split('/').filter(|s| !s.is_empty());
        let _vol = segs.next(); // external / internal — the physical volume (carried implicitly)
        let collection = segs.next().unwrap_or("");
        let volume = match MediaKind::from_token(collection) {
            Some(kind) => StorageVolume::Media(kind),
            None => StorageVolume::Other(format!("media/{tail}")),
        };
        StorageReach {
            volume,
            path: tail.to_string(),
        }
    }

    /// Classify a filesystem path into a [`StorageVolume`]:
    /// - a path under `/Android/data/<pkg>` (or `/Android/obb/<pkg>`) ⟹ that app's scope;
    /// - a shared-media dir (`/DCIM`, `/Pictures`, `/Movies`, `/Music`, `/Download`) ⟹ the
    ///   matching [`MediaKind`] collection;
    /// - anything else ⟹ [`StorageVolume::Other`] keyed by the path (no ambient FS — refused
    ///   unless a cap to exactly that volume was granted).
    fn parse_path(path: &str) -> Self {
        let lower = path.to_ascii_lowercase();
        // App scope: /Android/data/<pkg>/... or /Android/obb/<pkg>/...
        if let Some(pkg) = app_scope_package(&lower) {
            return StorageReach {
                volume: StorageVolume::AppScope { package: pkg },
                path: path.to_string(),
            };
        }
        // Shared-media dirs map to their MediaStore collection.
        for seg in lower.split('/').filter(|s| !s.is_empty()) {
            if let Some(kind) = MediaKind::from_token(seg) {
                return StorageReach {
                    volume: StorageVolume::Media(kind),
                    path: path.to_string(),
                };
            }
        }
        StorageReach {
            volume: StorageVolume::Other(lower),
            path: path.to_string(),
        }
    }

    /// A short tag for the receipt digest + status line.
    fn tag(&self) -> String {
        if self.path.is_empty() {
            self.volume.key()
        } else {
            format!("{}::{}", self.volume.key(), self.path)
        }
    }
}

/// Extract the package from a `/Android/data/<pkg>/...` or `/Android/obb/<pkg>/...` scoped path.
fn app_scope_package(lower_path: &str) -> Option<String> {
    for marker in ["/android/data/", "/android/obb/"] {
        if let Some(idx) = lower_path.find(marker) {
            let after = &lower_path[idx + marker.len()..];
            let pkg = after.split('/').next().unwrap_or("");
            if !pkg.is_empty() {
                return Some(pkg.to_string());
            }
        }
    }
    None
}

/// The access an app requests against a storage reach. AOSP's `load`/`query`/`openInputStream`
/// is a **read**; `save`/`insert`/`openOutputStream`/`delete` is a **write** (it mutates the
/// volume's content). The read/write split is exactly the grant attenuation this gate enforces.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum StorageAccess {
    /// A `load` / `openInputStream` — an authority-checked read of the storage cell's content.
    Read,
    /// A `save` / `openOutputStream` / `delete` — a mutation, which in deos is a **receipted
    /// turn** against the storage cell (and needs a write-granting cap).
    Write,
}

impl StorageAccess {
    fn tag(&self) -> &'static str {
        match self {
            StorageAccess::Read => "read",
            StorageAccess::Write => "write",
        }
    }
}

/// What a holder was granted over a storage volume — the deos form of AOSP's
/// `READ_EXTERNAL_STORAGE` / `WRITE_EXTERNAL_STORAGE` split, expressed as a cap attenuation. A
/// [`ReadOnly`](Self::ReadOnly) grant cannot amplify to a write.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum StorageGrant {
    /// The holder may read the volume only — a write is refused (the attenuation tooth).
    ReadOnly,
    /// The holder may read AND write (a write commits as a receipted turn against the
    /// storage cell).
    ReadWrite,
}

impl StorageGrant {
    /// Does this grant admit `access`? `ReadOnly` admits only [`StorageAccess::Read`].
    pub fn admits(&self, access: StorageAccess) -> bool {
        match (self, access) {
            (StorageGrant::ReadWrite, _) => true,
            (StorageGrant::ReadOnly, StorageAccess::Read) => true,
            (StorageGrant::ReadOnly, StorageAccess::Write) => false,
        }
    }
}

/// A cap-reachable storage cell in the android-cell's bounded neighborhood — the deos form of
/// a `DirectoryCell` (`APPS-AS-CELLS.md §1`) for one [`StorageVolume`]. The content IS the
/// cell's substance/subgraph; a read is authority-checked, a write is a receipted turn against
/// it. Held by the [`StorageResolver`] only for volumes the android-cell holds a cap to.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct StorageCell {
    /// The storage cell — the named capability holder whose substance the content is.
    pub cell: CellId,
    /// The volume this cell holds (the spotter match key).
    pub volume: StorageVolume,
    /// A short human label for the chooser / status line.
    pub label: String,
    /// The access the holder was granted over this volume (the cap attenuation).
    pub grant: StorageGrant,
}

impl StorageCell {
    /// A storage cell for an explicit cell + volume + grant.
    pub fn new(cell: CellId, volume: StorageVolume, grant: StorageGrant) -> Self {
        let label = volume.label();
        StorageCell {
            cell,
            volume,
            label,
            grant,
        }
    }

    /// **The device's standard storage cell for `volume`** with the given grant — the cell is
    /// `volume.storage_cell()` (the key-derived storage-cell identity). The unit a boot's
    /// storage roster + a granted-permission bridge builds from.
    pub fn standard(volume: StorageVolume, grant: StorageGrant) -> Self {
        let cell = volume.storage_cell();
        StorageCell::new(cell, volume, grant)
    }

    /// Does this cell hold `volume`? (The reach-match key — volume identity.)
    pub fn answers(&self, volume: &StorageVolume) -> bool {
        &self.volume == volume
    }
}

/// The four distinguishable ends a storage reach can hit — the storage-side analogue of
/// [`crate::contentgate::ContentDecision`] / [`crate::organgate::ServiceDecision`].
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum StorageDecision {
    /// Exactly one cap-reachable storage cell held the volume AND the grant admits the access:
    /// a cap-bounded hand to the storage (a read = an authorized query; a write = a receipted
    /// turn against the storage cell).
    Granted {
        storage_cell: CellId,
        label: String,
        access: StorageAccess,
    },
    /// Two+ cap-reachable cells held one volume: deos refuses to silently route and surfaces
    /// the candidates for an explicit chooser.
    Ambiguous { candidates: Vec<(CellId, String)> },
    /// NO cap-reachable storage cell held this volume — the no-ambient-FS property: the app
    /// cannot read storage it was never granted a cap to (another app's scope is simply not in
    /// the neighborhood).
    RefusedUnreachable { volume: String },
    /// A WRITE against a volume the holder was granted only READ — refused by the cap
    /// attenuation (a read cap does not amplify to a write).
    RefusedReadOnly {
        storage_cell: CellId,
        volume: String,
    },
}

impl StorageDecision {
    pub fn granted(&self) -> bool {
        matches!(self, StorageDecision::Granted { .. })
    }
    pub fn refused_unreachable(&self) -> bool {
        matches!(self, StorageDecision::RefusedUnreachable { .. })
    }
    pub fn refused_read_only(&self) -> bool {
        matches!(self, StorageDecision::RefusedReadOnly { .. })
    }
    pub fn ambiguous(&self) -> bool {
        matches!(self, StorageDecision::Ambiguous { .. })
    }
}

/// **The receipt left by a gated storage reach.** Every decision produces one, so the
/// android-cell's storage traffic is auditable end to end exactly like the content / service /
/// intent receipts. Content-addressed:
/// `decision_digest = blake3(cell? ‖ reach_tag ‖ access ‖ outcome ‖ storage_cell?)`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct StorageReceipt {
    /// The android-cell whose held cap + granted storage set decided this reach.
    pub cell: Option<CellId>,
    /// The storage reach the confined app issued.
    pub reach: StorageReach,
    /// The access the app requested.
    pub access: StorageAccess,
    /// The decision reached.
    pub decision: StorageDecision,
    /// `blake3(…)[..32]` — the content-addressed witness a verifier reconstructs.
    pub decision_digest: [u8; 32],
}

impl StorageReceipt {
    fn digest(
        cell: Option<CellId>,
        reach: &StorageReach,
        access: StorageAccess,
        decision: &StorageDecision,
    ) -> [u8; 32] {
        let mut h = blake3::Hasher::new();
        h.update(b"graphideos-storage-v1");
        if let Some(c) = cell {
            h.update(b"\x01cell");
            h.update(c.as_bytes());
        }
        h.update(reach.tag().as_bytes());
        h.update(b"\x00");
        h.update(access.tag().as_bytes());
        match decision {
            StorageDecision::Granted {
                storage_cell,
                access,
                ..
            } => {
                h.update(b"\x01granted");
                h.update(storage_cell.as_bytes());
                h.update(access.tag().as_bytes());
            }
            StorageDecision::Ambiguous { candidates } => {
                h.update(b"\x02ambiguous");
                for (c, _) in candidates {
                    h.update(c.as_bytes());
                }
            }
            StorageDecision::RefusedUnreachable { volume } => {
                h.update(b"\x03refused-unreachable");
                h.update(volume.as_bytes());
            }
            StorageDecision::RefusedReadOnly {
                storage_cell,
                volume,
            } => {
                h.update(b"\x04refused-read-only");
                h.update(storage_cell.as_bytes());
                h.update(volume.as_bytes());
            }
        }
        *h.finalize().as_bytes()
    }

    /// A one-line audit truth for the cockpit status line — which end, named exactly.
    pub fn status_line(&self) -> String {
        match &self.decision {
            StorageDecision::Granted { label, access, .. } => format!(
                "android-storage: ✔ {} {} → granted over «{label}» as a cap-bounded {} — a named storage cell, not an ambient filesystem",
                self.access.tag(),
                self.reach.tag(),
                match access {
                    StorageAccess::Read => "query",
                    StorageAccess::Write => "receipted turn",
                }
            ),
            StorageDecision::Ambiguous { candidates } => format!(
                "android-storage: ◈ {} matches {} cap-reachable storage cells — surfaced for an explicit chooser (no silent route)",
                self.reach.tag(),
                candidates.len()
            ),
            StorageDecision::RefusedUnreachable { volume } => format!(
                "android-storage: ✖ {} REFUSED — no cap-reachable storage cell holds «{volume}» (the app cannot read storage it was never granted)",
                self.reach.tag()
            ),
            StorageDecision::RefusedReadOnly { volume, .. } => format!(
                "android-storage: ✖ write {} REFUSED — the held cap grants only READ over «{volume}» (a read cap does not amplify to a write)",
                self.reach.tag()
            ),
        }
    }
}

/// The cap-gated storage resolver for one android-cell — **the spotter over the cell's
/// bounded, cap-reachable storage neighborhood**, NOT a device-wide filesystem or
/// `MediaProvider`. Holds the granted storage-cell set + the cell it speaks for; holds NO
/// ambient authority — every [`resolve`](Self::resolve) is a pure function of its storage cells.
pub struct StorageResolver {
    cells: Vec<StorageCell>,
    cell: Option<CellId>,
}

impl StorageResolver {
    /// Build a resolver over the granted storage neighborhood and the cell it speaks for.
    pub fn new(cells: impl IntoIterator<Item = StorageCell>, cell: Option<CellId>) -> Self {
        StorageResolver {
            cells: cells.into_iter().collect(),
            cell,
        }
    }

    /// The granted storage neighborhood (the cap-reachable set the spotter ranges over).
    pub fn cells(&self) -> &[StorageCell] {
        &self.cells
    }

    /// **THE STORAGE GATE.** The confined app reached `reach` with `access` (a scoped path or a
    /// `content://media/...` URI). Decide against the granted storage set + its grants, and
    /// return the decision AND its [`StorageReceipt`].
    ///
    /// Order of teeth (fail-closed):
    /// 1. **Spotter over the cap-reachable set** — match `reach`'s volume against the granted
    ///    storage cells. Zero ⟹ [`StorageDecision::RefusedUnreachable`] (no ambient FS); two+ ⟹
    ///    [`StorageDecision::Ambiguous`] (the explicit chooser).
    /// 2. **The grant attenuation** — one match, but a WRITE against a `ReadOnly` grant ⟹
    ///    [`StorageDecision::RefusedReadOnly`]. Otherwise [`StorageDecision::Granted`].
    pub fn resolve(&self, reach: &StorageReach, access: StorageAccess) -> StorageReceipt {
        let mut matches: Vec<&StorageCell> = self
            .cells
            .iter()
            .filter(|c| c.answers(&reach.volume))
            .collect();
        matches.sort_by(|a, b| a.cell.as_bytes().cmp(b.cell.as_bytes()));
        matches.dedup_by(|a, b| a.cell == b.cell);

        let decision = match matches.len() {
            0 => StorageDecision::RefusedUnreachable {
                volume: reach.volume.key(),
            },
            1 => {
                let c = matches[0];
                if c.grant.admits(access) {
                    StorageDecision::Granted {
                        storage_cell: c.cell,
                        label: c.label.clone(),
                        access,
                    }
                } else {
                    StorageDecision::RefusedReadOnly {
                        storage_cell: c.cell,
                        volume: reach.volume.key(),
                    }
                }
            }
            _ => StorageDecision::Ambiguous {
                candidates: matches.iter().map(|c| (c.cell, c.label.clone())).collect(),
            },
        };
        self.receipt(reach, access, decision)
    }

    fn receipt(
        &self,
        reach: &StorageReach,
        access: StorageAccess,
        decision: StorageDecision,
    ) -> StorageReceipt {
        let decision_digest = StorageReceipt::digest(self.cell, reach, access, &decision);
        StorageReceipt {
            cell: self.cell,
            reach: reach.clone(),
            access,
            decision,
            decision_digest,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use dregg_firmament::cell_seed;

    fn own_scope() -> StorageCell {
        StorageCell::standard(
            StorageVolume::AppScope {
                package: "com.example.notes".into(),
            },
            StorageGrant::ReadWrite,
        )
    }
    fn images_ro() -> StorageCell {
        StorageCell::standard(
            StorageVolume::Media(MediaKind::Images),
            StorageGrant::ReadOnly,
        )
    }

    #[test]
    fn reach_parse_is_faithful() {
        // A MediaStore URI resolves on its collection.
        let u = StorageReach::parse("content://media/external/images/media/42").unwrap();
        assert_eq!(u.volume, StorageVolume::Media(MediaKind::Images));
        assert_eq!(u.path, "external/images/media/42");

        // A shared-media dir path maps to the same collection.
        let p = StorageReach::parse("/storage/emulated/0/Pictures/cat.jpg").unwrap();
        assert_eq!(p.volume, StorageVolume::Media(MediaKind::Images));

        // An app-scoped path resolves to that package's scope.
        let s =
            StorageReach::parse("/storage/emulated/0/Android/data/com.example.notes/files/n.txt")
                .unwrap();
        assert_eq!(
            s.volume,
            StorageVolume::AppScope {
                package: "com.example.notes".into()
            }
        );

        // An arbitrary path is an Other volume (refused unless explicitly granted).
        let o = StorageReach::parse("/etc/hosts").unwrap();
        assert!(matches!(o.volume, StorageVolume::Other(_)));

        // An empty reach carries no volume.
        assert!(StorageReach::parse("").is_none());
    }

    /// **THE LOAD-BEARING TEST: a reach whose volume no cap-reachable cell holds is refused —
    /// the app cannot read storage it was never granted (no ambient FS; another app's scope is
    /// not in the neighborhood).**
    #[test]
    fn unreachable_volume_is_refused() {
        let me = cell_seed(9);
        // The neighborhood holds only my own scope — no media, no other app's scope.
        let resolver = StorageResolver::new([own_scope()], Some(me));

        // The shared images collection has no cap-reachable cell here.
        let media = StorageReach::parse("content://media/external/images/media/7").unwrap();
        let r0 = resolver.resolve(&media, StorageAccess::Read);
        assert!(r0.decision.refused_unreachable());
        assert!(r0.status_line().contains("never granted"));
        assert_eq!(
            r0.decision_digest,
            StorageReceipt::digest(Some(me), &media, StorageAccess::Read, &r0.decision)
        );

        // ANOTHER app's scope is not in the neighborhood either.
        let other =
            StorageReach::parse("/storage/emulated/0/Android/data/com.other.app/files/secret.txt")
                .unwrap();
        assert!(
            resolver
                .resolve(&other, StorageAccess::Read)
                .decision
                .refused_unreachable(),
            "another app's scope is unreachable (no ambient FS)"
        );
    }

    /// An app reaches its OWN scope (read AND write) because it holds a ReadWrite cap to its
    /// own storage cell — a write is a receipted turn.
    #[test]
    fn own_scope_read_and_write_are_granted() {
        let me = cell_seed(9);
        let resolver = StorageResolver::new([own_scope()], Some(me));
        let reach =
            StorageReach::parse("/storage/emulated/0/Android/data/com.example.notes/files/n.txt")
                .unwrap();

        let rd = resolver.resolve(&reach, StorageAccess::Read);
        assert!(rd.decision.granted());
        assert!(rd.status_line().contains("cap-bounded query"));

        let wr = resolver.resolve(&reach, StorageAccess::Write);
        assert!(wr.decision.granted());
        assert!(wr.status_line().contains("receipted turn"));
    }

    /// **THE ATTENUATION TOOTH: a WRITE against a ReadOnly grant is refused — a read cap does
    /// not amplify to a write.**
    #[test]
    fn write_against_read_only_grant_is_refused() {
        let me = cell_seed(9);
        let resolver = StorageResolver::new([images_ro()], Some(me));
        let reach = StorageReach::parse("content://media/external/images/media/42").unwrap();

        // A read of the granted images collection is fine...
        assert!(
            resolver
                .resolve(&reach, StorageAccess::Read)
                .decision
                .granted()
        );
        // ...but a write against the read-only grant is refused (no amplification).
        let w = resolver.resolve(&reach, StorageAccess::Write);
        assert!(w.decision.refused_read_only());
        assert!(w.status_line().contains("does not amplify to a write"));
        assert_eq!(
            w.decision,
            StorageDecision::RefusedReadOnly {
                storage_cell: StorageVolume::Media(MediaKind::Images).storage_cell(),
                volume: "media:images".into(),
            }
        );
    }

    /// A ReadWrite media grant admits a write (which commits as a receipted turn).
    #[test]
    fn write_against_read_write_grant_is_a_receipted_turn() {
        let me = cell_seed(9);
        let dl = StorageCell::standard(
            StorageVolume::Media(MediaKind::Downloads),
            StorageGrant::ReadWrite,
        );
        let resolver = StorageResolver::new([dl], Some(me));
        let reach = StorageReach::parse("/storage/emulated/0/Download/report.pdf").unwrap();
        let w = resolver.resolve(&reach, StorageAccess::Write);
        assert!(w.decision.granted());
        assert!(w.status_line().contains("receipted turn"));
    }

    /// Two cap-reachable cells holding one volume ⟹ an EXPLICIT chooser, never a silent route.
    #[test]
    fn duplicate_volume_surfaces_a_chooser() {
        let me = cell_seed(9);
        let other_images = StorageCell::new(
            cell_seed(0x7A),
            StorageVolume::Media(MediaKind::Images),
            StorageGrant::ReadOnly,
        );
        let resolver = StorageResolver::new([images_ro(), other_images], Some(me));
        let reach = StorageReach::parse("content://media/external/images/media/1").unwrap();
        let r = resolver.resolve(&reach, StorageAccess::Read);
        match &r.decision {
            StorageDecision::Ambiguous { candidates } => assert_eq!(candidates.len(), 2),
            other => panic!("expected Ambiguous, got {other:?}"),
        }
        assert!(r.status_line().contains("explicit chooser"));
    }

    /// Distinct volumes target distinct storage cells (the reach distinguishes them), and the
    /// derivation is stable.
    #[test]
    fn storage_cells_are_distinct_and_stable() {
        assert_ne!(
            StorageVolume::Media(MediaKind::Images).storage_cell(),
            StorageVolume::Media(MediaKind::Audio).storage_cell()
        );
        assert_ne!(
            StorageVolume::AppScope {
                package: "a".into()
            }
            .storage_cell(),
            StorageVolume::AppScope {
                package: "b".into()
            }
            .storage_cell()
        );
        assert_eq!(
            StorageVolume::Media(MediaKind::Images).storage_cell(),
            StorageVolume::Media(MediaKind::Images).storage_cell()
        );
    }
}
