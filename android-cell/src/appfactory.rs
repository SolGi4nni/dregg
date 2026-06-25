//! **The package manager → cell factory reforge.** "Installing an app" becomes
//! **minting an android-cell from a [`FactoryDescriptor`]** — a provable, cap-gated
//! birth whose authority is EXACTLY the APK manifest's declared permissions, nothing
//! ambient. `GRAPHIDEOS.md §1` (the package-manager row) made real.
//!
//! # What Android does (the ambient mechanism deos replaces)
//!
//! Stock Android's `PackageManager` installs an APK by verifying its signature and
//! registering its `AndroidManifest.xml`: the declared `<uses-permission>`s, the
//! components, the `<intent-filter>`s. The app then runs under a UID that the framework
//! grants those permissions to — **ambiently at runtime** (the dangerous ones behind a
//! dialog, the normal ones automatically). The install is a privileged framework act
//! and the resulting authority is a UID-scoped ambient grant.
//!
//! # What graphideOS does (the cap-gated birth)
//!
//! `GRAPHIDEOS.md §1`: *"installing an app = minting a cell from a factory descriptor (a
//! provable, cap-gated birth); a foreign APK = minting an android-cell whose cap-set
//! scopes its I/O."* This module is that translation, in the REAL [`dregg_cell`] factory
//! vocabulary:
//!
//! - An [`AndroidManifest`] (package · declared permissions · component intent-filters ·
//!   sovereign-vs-hosted) is translated by [`AndroidManifest::to_factory_descriptor`]
//!   into a [`FactoryDescriptor`] whose [`allowed_cap_templates`](FactoryDescriptor::allowed_cap_templates)
//!   are **exactly** the manifest's declared permissions, each as a typed [`CapTemplate`].
//! - **The load-bearing property: a permission the manifest does not declare yields NO
//!   cap template, so the minted android-cell can never hold that authority** — there is
//!   no runtime escalation, no ambient UID grant. The cell is born bounded by its
//!   manifest and the factory's `validate_creation` enforces it on every birth.
//! - The descriptor is content-addressed ([`FactoryDescriptor::hash`]): "what authority
//!   does installing this APK confer?" is an auditable, reproducible question, answered
//!   by a hash, not a buried UID grant.
//! - The manifest's component `<intent-filter>`s become the published [`IntentFilter`]s
//!   the installed app advertises — exactly the handler filters the [`crate::intentgate`]
//!   resolver ranges over when ANOTHER cell fires an intent. Install and intent-dispatch
//!   close the loop: an app is reachable as a handler only because its manifest declared
//!   the filter AND the resolving cell holds a cap to it.
//!
//! # The depth (honest, like the net/intent gates')
//!
//! This is the **install-as-birth translation**: manifest → descriptor → the cap-set a
//! cell is born with. The remaining frontier — the in-circuit constructor proof that a
//! given android-cell was minted by THIS descriptor (the `child_vk` derivation the
//! factory subsystem already formalizes for native cells) carried onto the foreign-APK
//! birth, and the device-side APK signature verification rooted in the Titan-M2 secure
//! element (`GRAPHIDEOS.md §0`) — is named, not claimed. What IS real today: the
//! manifest→descriptor map + the exactly-the-manifest cap-set property + the
//! content-addressed audit, testable on any node.

use std::collections::BTreeSet;

use dregg_cell::{AuthRequired, CapTarget, CapTemplate, CellId, CellMode, FactoryDescriptor};

use crate::intentgate::IntentFilter;

/// The device organ cell a sensor/resource permission targets — derived deterministically
/// from the permission's AOSP name, so distinct permissions (camera vs location) target
/// distinct organs and the descriptor's cap-set distinguishes them. On a real device the
/// install resolves these to the actual HAL-organ cells (`GRAPHIDEOS.md §1`, the
/// services-as-cells row); the name-derived id is the stable stand-in identity.
fn organ_cell(permission_name: &str) -> CellId {
    let mut h = blake3::Hasher::new_derive_key("graphideos-android-organ-cell-v1");
    h.update(permission_name.as_bytes());
    CellId::from_bytes(*h.finalize().as_bytes())
}

/// An Android permission an APK declares in `<uses-permission>` — a representative set
/// of the install-time/runtime permissions, plus an `Other` long-tail. Each maps to a
/// typed deos [`CapTemplate`] (see [`AndroidPermission::cap_template`]); the SET a
/// manifest declares is the entire authority the minted cell may ever hold.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum AndroidPermission {
    /// `android.permission.INTERNET` — outbound network. Becomes a net cap, then
    /// narrowed at runtime by the held `SurfaceCapability` origin allowlist (the
    /// [`crate::netgate`] tooth). Targets any peer (the allowlist is the attenuation).
    Internet,
    /// `android.permission.ACCESS_FINE_LOCATION` — the location organ.
    AccessFineLocation,
    /// `android.permission.CAMERA` — the camera organ.
    Camera,
    /// `android.permission.RECORD_AUDIO` — the microphone organ.
    RecordAudio,
    /// `android.permission.READ_CONTACTS` — the contacts cell-graph.
    ReadContacts,
    /// `android.permission.READ_EXTERNAL_STORAGE` — a file-root cap.
    ReadExternalStorage,
    /// `android.permission.WRITE_EXTERNAL_STORAGE` — a writable file-root cap.
    WriteExternalStorage,
    /// Any other declared permission (the long tail), carried by name.
    Other(String),
}

impl AndroidPermission {
    /// The fully-qualified Android permission string (`android.permission.INTERNET`, …)
    /// — what the manifest actually writes, and the stable name the cap template binds.
    pub fn android_name(&self) -> String {
        match self {
            AndroidPermission::Internet => "android.permission.INTERNET".into(),
            AndroidPermission::AccessFineLocation => {
                "android.permission.ACCESS_FINE_LOCATION".into()
            }
            AndroidPermission::Camera => "android.permission.CAMERA".into(),
            AndroidPermission::RecordAudio => "android.permission.RECORD_AUDIO".into(),
            AndroidPermission::ReadContacts => "android.permission.READ_CONTACTS".into(),
            AndroidPermission::ReadExternalStorage => {
                "android.permission.READ_EXTERNAL_STORAGE".into()
            }
            AndroidPermission::WriteExternalStorage => {
                "android.permission.WRITE_EXTERNAL_STORAGE".into()
            }
            AndroidPermission::Other(s) => s.clone(),
        }
    }

    /// **The AOSP protection level** — the faithful classification that decides whether
    /// *declaring* a permission suffices (a `Normal` permission is auto-granted at install,
    /// no dialog) or whether it needs an explicit runtime grant (a `Dangerous` / `Signature`
    /// permission is declared-but-not-held until the user/system hands it over). This is the
    /// load-bearing faithfulness the [`crate::permgate`] cap-badge layer renders: a `Normal`
    /// badge lights at install, a `Dangerous` badge stays dim until the receipted hand-over.
    ///
    /// An [`Other`](AndroidPermission::Other) (custom) permission is **fail-closed** to
    /// `Dangerous` — AOSP defaults an unspecified custom permission to `normal`, but graphideOS
    /// refuses to auto-hold an unrecognised authority: it requires an explicit receipted
    /// hand-over (the same fail-closed-toward-more-authority stance `organgate` takes for an
    /// unknown method).
    pub fn protection_level(&self) -> ProtectionLevel {
        match self {
            // INTERNET is a `normal` permission — auto-granted at install, never a dialog.
            AndroidPermission::Internet => ProtectionLevel::Normal,
            // The sensor/storage/contacts permissions are AOSP `dangerous` — runtime-granted.
            AndroidPermission::AccessFineLocation
            | AndroidPermission::Camera
            | AndroidPermission::RecordAudio
            | AndroidPermission::ReadContacts
            | AndroidPermission::ReadExternalStorage
            | AndroidPermission::WriteExternalStorage => ProtectionLevel::Dangerous,
            // A custom permission fails closed to `dangerous` (needs an explicit hand-over).
            AndroidPermission::Other(_) => ProtectionLevel::Dangerous,
        }
    }

    /// The standard roster of named permissions (sans the `Other` long tail) — the full set a
    /// cap-badge surface lights/dims over, before unioning an app's declared custom permissions.
    pub fn all_standard() -> Vec<AndroidPermission> {
        vec![
            AndroidPermission::Internet,
            AndroidPermission::AccessFineLocation,
            AndroidPermission::Camera,
            AndroidPermission::RecordAudio,
            AndroidPermission::ReadContacts,
            AndroidPermission::ReadExternalStorage,
            AndroidPermission::WriteExternalStorage,
        ]
    }

    /// **The permission → cap-template map.** Each declared permission becomes ONE typed
    /// [`CapTemplate`] in the factory descriptor — the authority the minted cell is born
    /// holding. The `target` types the resource (network is `Any`-peer, narrowed by the
    /// runtime origin allowlist; a sensor/organ permission targets `Any` organ cell the
    /// install resolves; storage is over the cell's own file-root, `SelfCell`); the
    /// `max_permissions` is the ceiling the factory may grant; `attenuatable` lets the
    /// app hand a strictly-narrower slice onward (the no-amplification lattice).
    pub fn cap_template(&self) -> CapTemplate {
        match self {
            // Network: the app may reach peers, but the held SurfaceCapability origin
            // allowlist is the real attenuation (the netgate tooth). Attenuatable so the
            // app can hand a child a narrower origin set.
            AndroidPermission::Internet => CapTemplate {
                target: CapTarget::Any,
                max_permissions: AuthRequired::Either,
                attenuatable: true,
            },
            // Sensor/organ permissions: a cap over the SPECIFIC resource organ (the
            // device's location/camera/mic/contacts organ cell, name-derived so camera
            // and location are distinct authorities). Not freely re-delegable by default
            // — a sensor grant should not silently spread.
            AndroidPermission::AccessFineLocation
            | AndroidPermission::Camera
            | AndroidPermission::RecordAudio
            | AndroidPermission::ReadContacts => CapTemplate {
                target: CapTarget::Specific(organ_cell(&self.android_name())),
                max_permissions: AuthRequired::Signature,
                attenuatable: false,
            },
            // Storage: a cap over the cell's own bind-mounted file-root (no ambient FS).
            AndroidPermission::ReadExternalStorage => CapTemplate {
                target: CapTarget::SelfCell,
                max_permissions: AuthRequired::Signature,
                attenuatable: false,
            },
            AndroidPermission::WriteExternalStorage => CapTemplate {
                target: CapTarget::SelfCell,
                max_permissions: AuthRequired::Either,
                attenuatable: false,
            },
            // The long tail: a conservative self-scoped signature cap, named by string.
            AndroidPermission::Other(_) => CapTemplate {
                target: CapTarget::SelfCell,
                max_permissions: AuthRequired::Signature,
                attenuatable: false,
            },
        }
    }

    /// **The concrete cell a real hand-over of this permission grants a cap
    /// reaching** — the resolution of [`Self::cap_template`]'s [`CapTarget`]
    /// against the grantee `app_cell`. The [`crate::permgate::PermWorld`] kernel
    /// path mints a real `Effect::GrantCapability` toward exactly this cell:
    ///
    /// - a sensor/organ permission ([`CapTarget::Specific`]) targets its
    ///   name-derived device organ ([`organ_cell`]) — camera and location are
    ///   distinct authorities, so the granted cap reaches distinct cells;
    /// - a storage/custom permission ([`CapTarget::SelfCell`]) targets the
    ///   android-cell's own file-root, which is the `app_cell` itself;
    /// - a network permission ([`CapTarget::Any`]) anchors on the `app_cell`
    ///   (INTERNET is `Normal` and never reaches the hand-over path anyway).
    pub fn grant_target(&self, app_cell: CellId) -> CellId {
        match self.cap_template().target {
            CapTarget::Specific(id) => id,
            CapTarget::SelfCell | CapTarget::Any => app_cell,
        }
    }
}

/// **The AOSP permission protection level** — `normal` (auto-granted at install, no dialog),
/// `dangerous` (runtime-granted: the app must explicitly request it and the user grant it), or
/// `signature` (granted only to an app signed with the declaring cert). The faithful split the
/// [`crate::permgate`] cap-badge layer reforges: a `Normal` permission's badge lights at
/// install; a `Dangerous`/`Signature` permission's badge stays dim until a receipted hand-over
/// turn (the deos form of the runtime dialog).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ProtectionLevel {
    /// Auto-granted at install — declaring it in the manifest is enough (no dialog, no
    /// hand-over). The badge lights the moment the cell is minted.
    Normal,
    /// Runtime-granted — declared in the manifest but NOT held until an explicit hand-over.
    /// The badge stays dim until the [`crate::permgate`] ceremony lights it.
    Dangerous,
    /// Signature-protected — granted only under the device/signing authority. Treated like
    /// `Dangerous` by the badge layer (declared-but-dim until the authority hands it over);
    /// the AOSP signature condition is the granter's held-authority check.
    Signature,
}

impl ProtectionLevel {
    /// Is this permission held the moment the app is installed (a `Normal` permission), with no
    /// runtime hand-over needed? `Dangerous`/`Signature` permissions are NOT auto-held.
    pub fn held_at_install(&self) -> bool {
        matches!(self, ProtectionLevel::Normal)
    }
}

/// The deos-relevant projection of an `AndroidManifest.xml`: the package, the declared
/// `<uses-permission>`s, the component `<intent-filter>`s, and whether the app runs as a
/// sovereign cell or a hosted one. The unit "installing an app" mints a cell from.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AndroidManifest {
    /// The APK package name (`com.example.maps`) — the cell's human handle.
    pub package: String,
    /// The `<uses-permission>` set the APK declares — the ENTIRE authority the minted
    /// cell may ever hold (a `BTreeSet`, so duplicates collapse and the order is stable
    /// for a reproducible descriptor hash).
    pub uses_permissions: BTreeSet<AndroidPermission>,
    /// The component `<intent-filter>`s the app publishes — what makes it a reachable
    /// handler in another cell's [`crate::intentgate::IntentResolver`] (closing the
    /// install ↔ intent-dispatch loop).
    pub intent_filters: Vec<IntentFilter>,
    /// The `<provider android:authorities=…>` this app publishes — what makes it a
    /// reachable content provider in another cell's [`crate::contentgate::ContentResolver`]
    /// (closing the install ↔ content loop, exactly as `intent_filters` closes the
    /// intent loop). A `BTreeSet` so duplicates collapse and the order is stable.
    pub content_authorities: BTreeSet<String>,
    /// Whether the app runs as a sovereign cell (its own root authority) or hosted under
    /// a parent (the common confined-foreign-app case).
    pub sovereign: bool,
}

impl AndroidManifest {
    /// A minimal manifest: a package + its declared permissions, hosted, no published
    /// filters (the builder; add filters / sovereignty after).
    pub fn new(
        package: impl Into<String>,
        permissions: impl IntoIterator<Item = AndroidPermission>,
    ) -> Self {
        AndroidManifest {
            package: package.into(),
            uses_permissions: permissions.into_iter().collect(),
            intent_filters: Vec::new(),
            content_authorities: BTreeSet::new(),
            sovereign: false,
        }
    }

    /// Publish the component intent-filters (builder).
    pub fn with_intent_filters(mut self, filters: impl IntoIterator<Item = IntentFilter>) -> Self {
        self.intent_filters = filters.into_iter().collect();
        self
    }

    /// Publish the `<provider>` content authorities (builder) — what makes this app a
    /// reachable content provider in a granted cell's [`crate::contentgate::ContentResolver`].
    pub fn with_content_authorities(
        mut self,
        authorities: impl IntoIterator<Item = impl Into<String>>,
    ) -> Self {
        self.content_authorities = authorities
            .into_iter()
            .map(|a| a.into().to_ascii_lowercase())
            .collect();
        self
    }

    /// Mark the app sovereign (builder).
    pub fn sovereign(mut self) -> Self {
        self.sovereign = true;
        self
    }

    /// **THE INSTALL = THE BIRTH.** Translate this manifest into the [`FactoryDescriptor`]
    /// that mints the android-cell. `factory_vk` identifies the install authority (the
    /// device's package-manager-cell). The descriptor's `allowed_cap_templates` are
    /// EXACTLY [`Self::uses_permissions`] mapped through [`AndroidPermission::cap_template`]
    /// — so the minted cell is born holding precisely the manifest's declared authority,
    /// and the factory's `validate_creation` refuses any birth that asks for more. No
    /// ambient UID grant, no runtime escalation; the authority is the manifest, provably.
    pub fn to_factory_descriptor(&self, factory_vk: [u8; 32]) -> FactoryDescriptor {
        let allowed_cap_templates: Vec<CapTemplate> = self
            .uses_permissions
            .iter()
            .map(AndroidPermission::cap_template)
            .collect();
        FactoryDescriptor {
            factory_vk,
            // The foreign-APK child carries no native deos program VK; its "program" is
            // the confined Android runtime, not a deos circuit. The constructor-proof
            // binding of a foreign child is the named frontier (see the module note).
            child_program_vk: None,
            child_vk_strategy: None,
            allowed_cap_templates,
            // No creation-time field constraints; the cell's substance is the runtime's
            // surface tile, not deos fields.
            field_constraints: Vec::new(),
            // No perpetual slot caveats by default (the runtime is opaque to the kernel).
            state_constraints: Vec::new(),
            default_mode: if self.sovereign {
                CellMode::Sovereign
            } else {
                CellMode::Hosted
            },
            // One descriptor mints one app-cell at a time; installs are individual.
            creation_budget: Some(1),
        }
    }

    /// Does the manifest declare `permission`? The authority predicate the install
    /// honours — a permission NOT here yields no cap template, so the minted cell can
    /// never hold it (the no-ambient-escalation property, in one call).
    pub fn declares(&self, permission: &AndroidPermission) -> bool {
        self.uses_permissions.contains(permission)
    }

    /// The published intent-filters this installed app advertises — to be registered as
    /// a handler in the resolvers of cells granted a cap to it (the install ↔
    /// intent-dispatch bridge).
    pub fn published_filters(&self) -> &[IntentFilter] {
        &self.intent_filters
    }

    /// The published content authorities this installed app advertises — to be registered
    /// as a [`crate::contentgate::ContentProvider`] in the resolvers of cells granted a cap
    /// to it (the install ↔ content bridge).
    pub fn published_authorities(&self) -> &BTreeSet<String> {
        &self.content_authorities
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn maps_manifest() -> AndroidManifest {
        AndroidManifest::new(
            "com.example.maps",
            [
                AndroidPermission::Internet,
                AndroidPermission::AccessFineLocation,
            ],
        )
        .with_intent_filters([IntentFilter::new(["android.intent.action.VIEW"], ["geo"])])
    }

    /// **THE LOAD-BEARING TEST: the minted cell's authority is EXACTLY the manifest's
    /// declared permissions — a permission not declared yields no cap, no escalation.**
    #[test]
    fn descriptor_cap_set_is_exactly_the_manifest() {
        let manifest = maps_manifest();
        let desc = manifest.to_factory_descriptor([0x11; 32]);

        // Two declared permissions ⟹ exactly two cap templates.
        assert_eq!(
            desc.allowed_cap_templates.len(),
            2,
            "the descriptor grants exactly the two declared permissions"
        );
        // The declared ones are present as their typed templates.
        assert!(
            desc.allowed_cap_templates
                .contains(&AndroidPermission::Internet.cap_template())
        );
        assert!(
            desc.allowed_cap_templates
                .contains(&AndroidPermission::AccessFineLocation.cap_template())
        );
        // A permission the manifest did NOT declare (camera) is absent — the minted cell
        // can never hold camera authority. No ambient escalation.
        assert!(!manifest.declares(&AndroidPermission::Camera));
        assert!(
            !desc
                .allowed_cap_templates
                .contains(&AndroidPermission::Camera.cap_template())
        );
    }

    /// A foreign-APK child is hosted + carries no native program VK (its program is the
    /// confined runtime), and is born minting one app-cell.
    #[test]
    fn foreign_apk_child_shape() {
        let desc = maps_manifest().to_factory_descriptor([0x11; 32]);
        assert_eq!(desc.default_mode, CellMode::Hosted);
        assert!(desc.child_program_vk.is_none());
        assert_eq!(desc.creation_budget, Some(1));

        // A sovereign manifest mints a sovereign cell.
        let sov = maps_manifest()
            .sovereign()
            .to_factory_descriptor([0x11; 32]);
        assert_eq!(sov.default_mode, CellMode::Sovereign);
    }

    /// The descriptor is content-addressed: the SAME manifest yields the SAME hash (an
    /// auditable, reproducible "what does installing this confer?"), and an EXTRA
    /// permission changes it (more authority ⟹ a different, visible identity).
    #[test]
    fn descriptor_is_content_addressed_and_authority_sensitive() {
        let a = maps_manifest().to_factory_descriptor([0x11; 32]);
        let b = maps_manifest().to_factory_descriptor([0x11; 32]);
        assert_eq!(a.hash(), b.hash(), "same manifest ⟹ same descriptor hash");

        // Adding CAMERA changes the descriptor's identity (more authority is visible).
        let mut perms = maps_manifest().uses_permissions;
        perms.insert(AndroidPermission::Camera);
        let wider = AndroidManifest {
            uses_permissions: perms,
            ..maps_manifest()
        }
        .to_factory_descriptor([0x11; 32]);
        assert_ne!(
            a.hash(),
            wider.hash(),
            "a manifest declaring more authority has a different descriptor hash"
        );
    }

    /// The install ↔ intent-dispatch loop: the manifest's published filters are exactly
    /// the handler filters the intent resolver ranges over for this app.
    #[test]
    fn published_filters_feed_the_intent_resolver() {
        let manifest = maps_manifest();
        let filters = manifest.published_filters();
        assert_eq!(filters.len(), 1);
        // The published filter matches the geo VIEW intent (so the installed app would be
        // a candidate handler in a resolver that holds a cap to it).
        let intent =
            crate::intentgate::AndroidIntent::view("android.intent.action.VIEW", "geo:0,0?q=x");
        assert!(filters[0].matches(&intent));
    }

    /// Permission names round-trip to their AOSP strings (what the manifest writes / the
    /// cap binds).
    #[test]
    fn permission_android_names() {
        assert_eq!(
            AndroidPermission::Internet.android_name(),
            "android.permission.INTERNET"
        );
        assert_eq!(
            AndroidPermission::Camera.android_name(),
            "android.permission.CAMERA"
        );
        assert_eq!(
            AndroidPermission::Other("com.example.CUSTOM".into()).android_name(),
            "com.example.CUSTOM"
        );
    }
}
