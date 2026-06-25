//! **The installed-app registry — the install↔launch↔intent (and content) bridge.** The
//! state that makes the [`crate::appfactory`] birth, the [`crate::intentgate`] resolution,
//! and the [`crate::contentgate`] resolution one coherent loop: an app is *installed* (minted
//! as an android-cell from its manifest descriptor), it is *launched* on a runtime, and a
//! live app's outbound intents / `content://` accesses resolve over the **cap-reachable
//! neighborhood of installed apps** — NOT a device-wide `PackageManager`/`ContentResolver`.
//!
//! # The loop, closed
//!
//! `GRAPHIDEOS.md §1` makes installing an app a cap-gated birth and an intent a turn over a
//! cap you hold. Those two are the same fact seen twice: an installed app is reachable as a
//! handler/provider **iff** (a) its manifest *declared* the `<intent-filter>` / `<provider>`
//! AND (b) the resolving cell *holds a cap* to it. The [`InstalledApps`] registry is where
//! both halves meet:
//!
//! - [`InstalledApps::install`] records `(cell, manifest, launch)` and returns the
//!   [`FactoryDescriptor`] the appfactory mints from the manifest — the install IS the
//!   cap-gated birth (the descriptor's `allowed_cap_templates` are EXACTLY the manifest's
//!   declared permissions) AND the registry entry, in one act.
//! - [`InstalledApps::resolver_for`] builds an [`IntentResolver`] for a *launching* cell over
//!   only the installed apps it was granted a cap to (`granted`). Each published
//!   `<intent-filter>` becomes an [`IntentHandler`] named to the publishing app's cell.
//! - [`InstalledApps::content_resolver_for`] does the same for `content://` providers,
//!   building a [`ContentResolver`] over the cap-reachable apps' published authorities.
//!
//! So an app the launching cell holds no cap to is, by construction, NOT a candidate — the
//! no-ambient-`startActivity` / no-ambient-`ContentResolver` property, sourced from the real
//! installed-app set rather than a hand-built handler list.

use std::collections::BTreeSet;

use dregg_cell::FactoryDescriptor;
use dregg_firmament::CellId;

use crate::appfactory::AndroidManifest;
use crate::appfactory::AndroidPermission;
use crate::broadcastgate::{BroadcastReceiver, BroadcastRouter};
use crate::contentgate::{ContentProvider, ContentResolver, ProviderGrant};
use crate::intentgate::{IntentHandler, IntentResolver};
use crate::notifgate::{
    ChannelCap, NotifPoster, NotificationChannel, POST_NOTIFICATIONS, PostGrant,
};
use crate::organgate::{ServiceGrant, ServiceOrgan, ServiceResolver, SystemService};
use crate::permgate::PermBox;
use crate::runtime::AppLaunch;
use crate::storagegate::{MediaKind, StorageCell, StorageGrant, StorageResolver, StorageVolume};

/// One installed app — the android-cell minted from a manifest, plus how to launch it.
#[derive(Clone, Debug)]
pub struct InstalledApp {
    /// The android-cell this app was minted as (the handler/provider identity another cell
    /// resolves to).
    pub cell: CellId,
    /// The manifest the cell was born from — the source of its published `<intent-filter>`s
    /// and `<provider>` authorities (and, via the appfactory, its cap-set).
    pub manifest: AndroidManifest,
    /// How the runtime launches this app's program (`am start` component or package).
    pub launch: AppLaunch,
}

/// **The installed-app registry.** The set of android-cells the device has minted, the unit
/// the launch + intent + content loops range over. Holds NO ambient authority — a resolver
/// it builds is always *restricted to a caller-supplied `granted` neighborhood*, so the
/// registry being device-wide does not make resolution device-wide.
#[derive(Default)]
pub struct InstalledApps {
    apps: Vec<InstalledApp>,
}

impl InstalledApps {
    pub fn new() -> Self {
        InstalledApps { apps: Vec::new() }
    }

    /// **INSTALL = THE CAP-GATED BIRTH + THE REGISTRY ENTRY.** Mint `manifest`'s
    /// [`FactoryDescriptor`] (the appfactory birth — its `allowed_cap_templates` are exactly
    /// the manifest's declared permissions) and register the app under `cell` with how to
    /// `launch` it. Returns the descriptor so the install's conferred authority is the same
    /// auditable, content-addressed artifact the appfactory produces.
    pub fn install(
        &mut self,
        cell: CellId,
        manifest: AndroidManifest,
        launch: AppLaunch,
        factory_vk: [u8; 32],
    ) -> FactoryDescriptor {
        let descriptor = manifest.to_factory_descriptor(factory_vk);
        self.apps.push(InstalledApp {
            cell,
            manifest,
            launch,
        });
        descriptor
    }

    /// The installed apps (the device's minted android-cells).
    pub fn apps(&self) -> &[InstalledApp] {
        &self.apps
    }

    /// The installed app minted as `cell`, if any.
    pub fn get(&self, cell: CellId) -> Option<&InstalledApp> {
        self.apps.iter().find(|a| a.cell == cell)
    }

    /// **Build the [`IntentResolver`] for `launching_cell`** over only the installed apps it
    /// holds a cap to (`granted`). Each published `<intent-filter>` becomes an
    /// [`IntentHandler`] named to the publishing app's cell + package label — so an app is a
    /// candidate handler iff its manifest declared the filter AND `launching_cell` holds a cap
    /// to it. This is the install↔intent loop, sourced from the real installed-app set.
    pub fn resolver_for(
        &self,
        launching_cell: CellId,
        granted: &BTreeSet<CellId>,
    ) -> IntentResolver {
        let handlers = self
            .apps
            .iter()
            .filter(|a| granted.contains(&a.cell))
            .flat_map(|a| {
                let cell = a.cell;
                let label = a.manifest.package.clone();
                a.manifest
                    .intent_filters
                    .iter()
                    .cloned()
                    .map(move |filter| IntentHandler::new(cell, label.clone(), filter))
            })
            .collect::<Vec<_>>();
        IntentResolver::new(handlers, Some(launching_cell))
    }

    /// **Build the [`ContentResolver`] for `launching_cell`** over only the installed apps it
    /// holds a cap to (`granted`). Each published `<provider>` authority becomes a
    /// [`ContentProvider`] named to the publishing app's cell. `grant` is the access the
    /// launching cell was handed over those providers (the cap attenuation — a strictly
    /// narrower per-provider grant is the powerbox hand-over). The install↔content loop.
    pub fn content_resolver_for(
        &self,
        launching_cell: CellId,
        granted: &BTreeSet<CellId>,
        grant: ProviderGrant,
    ) -> ContentResolver {
        let providers = self
            .apps
            .iter()
            .filter(|a| granted.contains(&a.cell))
            .flat_map(|a| {
                let cell = a.cell;
                let label = a.manifest.package.clone();
                a.manifest
                    .content_authorities
                    .iter()
                    .cloned()
                    .map(move |authority| {
                        ContentProvider::new(cell, authority, label.clone(), grant)
                    })
            })
            .collect::<Vec<_>>();
        ContentResolver::new(providers, Some(launching_cell))
    }

    /// **Build the [`ServiceResolver`] for `launching_cell`** over the system-service organs its
    /// OWN manifest's declared permissions grant a cap to — the install↔service loop. Each
    /// declared permission that names a [`SystemService`] (via
    /// [`SystemService::required_permission`]'s inverse) becomes a cap-reachable
    /// [`ServiceOrgan`] at the caller-supplied `grant` (the cap attenuation — a strictly
    /// narrower per-organ grant is the powerbox hand-over).
    ///
    /// This is the no-ambient-`getSystemService` property sourced from the real installed-app
    /// set: an app that did NOT declare a service's required permission has NO cap-reachable
    /// organ for it, so the resolver refuses the reach (`RefusedNoOrgan`) — the AOSP "get the
    /// manager freely, throw at the call" loophole closed at the reach. An unknown
    /// `launching_cell` yields an empty resolver (it reaches no organ).
    pub fn service_resolver_for(
        &self,
        launching_cell: CellId,
        grant: ServiceGrant,
    ) -> ServiceResolver {
        let organs = self
            .get(launching_cell)
            .into_iter()
            .flat_map(|app| {
                let perms = app.manifest.uses_permissions.clone();
                SystemService::all_standard()
                    .into_iter()
                    .filter(move |svc| {
                        svc.required_permission()
                            .map(|p| perms.contains(&p))
                            .unwrap_or(false)
                    })
            })
            .map(|svc| ServiceOrgan::standard(svc, grant))
            .collect::<Vec<_>>();
        ServiceResolver::new(organs, Some(launching_cell))
    }

    /// **Build the [`BroadcastRouter`] for `sending_cell`** over only the installed apps it
    /// holds a cap to (`granted`). Each published `<receiver>` filter becomes a
    /// [`BroadcastReceiver`] named to the publishing app's cell — so an app receives a
    /// broadcast iff its manifest declared the `<receiver>` filter AND `sending_cell` holds a
    /// cap to it. This is the install↔broadcast loop, sourced from the real installed-app set:
    /// a broadcast fans out over a BOUNDED neighborhood, not the device's global receiver
    /// table (the no-ambient-global-broadcast property). The receivers carry no per-receiver
    /// permission requirement here (the cap to reach the app IS the authority); the richer
    /// `<receiver android:permission>` / `sendBroadcast(receiverPermission)` legs are set
    /// directly on a [`BroadcastReceiver`] / [`crate::broadcastgate::Broadcast`].
    pub fn broadcast_router_for(
        &self,
        sending_cell: CellId,
        granted: &BTreeSet<CellId>,
    ) -> BroadcastRouter {
        let receivers = self
            .apps
            .iter()
            .filter(|a| granted.contains(&a.cell))
            .flat_map(|a| {
                let cell = a.cell;
                let label = a.manifest.package.clone();
                a.manifest
                    .broadcast_receivers
                    .iter()
                    .cloned()
                    .map(move |filter| BroadcastReceiver::new(cell, label.clone(), filter))
            })
            .collect::<Vec<_>>();
        BroadcastRouter::new(receivers, Some(sending_cell))
    }

    /// **Build the [`StorageResolver`] for an installed `cell`** over the storage volumes its
    /// OWN manifest grants a cap to — the install↔storage loop (`GRAPHIDEOS.md §1`, the
    /// storage-model row). Mirrors [`Self::service_resolver_for`]: the cap-set is sourced from
    /// the app's declared authority, NOT an ambient filesystem.
    ///
    /// Two grants, faithful to AOSP scoped storage:
    /// 1. **Its own scope, always** — every app gets a `ReadWrite` cap to its OWN
    ///    [`StorageVolume::AppScope`] storage cell (keyed by package), born at install with no
    ///    permission, exactly as AOSP grants an app free access to its private dir. This is the
    ///    ONLY storage an app with no storage permission can reach (no ambient FS; another app's
    ///    scope is never in the neighborhood).
    /// 2. **The shared `MediaStore` collections, by declared permission** — a declared
    ///    `READ_EXTERNAL_STORAGE` grants a `ReadOnly` cap to each [`MediaKind`] collection; a
    ///    declared `WRITE_EXTERNAL_STORAGE` grants `ReadWrite`. An app declaring neither reaches
    ///    no shared media (the `RefusedUnreachable` end) — the AOSP "no permission, no shared
    ///    media" rule as a cap attenuation. An unknown `cell` yields an empty resolver.
    pub fn storage_resolver_for(&self, cell: CellId) -> StorageResolver {
        let mut cells: Vec<StorageCell> = Vec::new();
        if let Some(app) = self.get(cell) {
            // 1. The app's own scope — always a ReadWrite cap (scoped storage, no permission).
            cells.push(StorageCell::standard(
                StorageVolume::AppScope {
                    package: app.manifest.package.clone(),
                },
                StorageGrant::ReadWrite,
            ));
            // 2. The shared MediaStore collections, gated by the declared storage permission
            //    (WRITE wins over READ — the strictly-wider grant).
            let perms = &app.manifest.uses_permissions;
            let media_grant = if perms.contains(&AndroidPermission::WriteExternalStorage) {
                Some(StorageGrant::ReadWrite)
            } else if perms.contains(&AndroidPermission::ReadExternalStorage) {
                Some(StorageGrant::ReadOnly)
            } else {
                None
            };
            if let Some(grant) = media_grant {
                for kind in MediaKind::all() {
                    cells.push(StorageCell::standard(StorageVolume::Media(kind), grant));
                }
            }
        }
        StorageResolver::new(cells, Some(cell))
    }

    /// **Build the [`PermBox`] for an installed `cell`** — the cap-badge + hand-over surface
    /// over the app's own manifest (its declared permissions are the only grantable ones), with
    /// `principal` the granting identity holding `principal_holds`. The install↔permission loop:
    /// the install's manifest (whose `<uses-permission>`s the appfactory turned into cap
    /// templates) is exactly what the badge set renders — a `Normal` permission lit at install,
    /// a `Dangerous` one dim until a receipted hand-over. `None` for an uninstalled cell (it has
    /// no manifest, so there is no authority to render). This parallels [`Self::resolver_for`] /
    /// [`Self::content_resolver_for`] / [`Self::service_resolver_for`], closing the last
    /// framework-reforge loop (`GRAPHIDEOS.md §1`, the permission-model row).
    pub fn permbox_for(
        &self,
        cell: CellId,
        principal: CellId,
        principal_holds: impl IntoIterator<Item = AndroidPermission>,
    ) -> Option<PermBox> {
        let app = self.get(cell)?;
        Some(PermBox::new(
            cell,
            app.manifest.clone(),
            principal,
            principal_holds,
        ))
    }

    /// **Build the [`NotifPoster`] for an installed `cell`** over the notification channels it
    /// created at runtime — the install↔notification loop (`GRAPHIDEOS.md §1`, the
    /// notification-system / SystemUI-shade row). Mirrors [`Self::service_resolver_for`]: the
    /// authority to reach the shade is sourced from the app's real declared permission, NOT an
    /// ambient push.
    ///
    /// Two legs, faithful to AOSP:
    /// 1. **The notification-organ (shade) cap, by declared permission** — the app holds the cap to
    ///    the notification shade organ iff it declared the `POST_NOTIFICATIONS` runtime permission
    ///    (Android 13+'s only door to the shade). An app that never declared it cannot post at all
    ///    (the [`crate::notifgate::NotifDecision::RefusedNoOrgan`] end — no ambient post).
    /// 2. **The channels, from the runtime** — a `NotificationChannel` is created at runtime
    ///    (`createNotificationChannel`), so the caller supplies the channels the app created; each
    ///    becomes a [`ChannelCap`] at the caller-supplied `grant` ceiling (the cap attenuation — a
    ///    `Priority` grant is the heads-up / full-screen-intent hand-over). A post to a channel not
    ///    in this set is refused (the app holds no cap to it).
    ///
    /// An unknown `cell` (uninstalled) holds no organ cap and no channels — it posts nothing.
    pub fn notif_poster_for(
        &self,
        cell: CellId,
        channels: impl IntoIterator<Item = NotificationChannel>,
        grant: PostGrant,
    ) -> NotifPoster {
        let holds_organ_cap = self
            .get(cell)
            .map(|app| {
                app.manifest
                    .uses_permissions
                    .iter()
                    .any(|p| p.android_name() == POST_NOTIFICATIONS)
            })
            .unwrap_or(false);
        let caps = channels.into_iter().map(|c| ChannelCap::standard(c, grant));
        NotifPoster::new(holds_organ_cap, caps, Some(cell))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::appfactory::AndroidPermission;
    use crate::contentgate::{ContentAccess, ContentUri};
    use crate::intentgate::{AndroidIntent, IntentFilter};
    use dregg_firmament::cell_seed;
    use starbridge_web_surface::{AuthRequired, SurfaceCapability};

    fn maps() -> (CellId, AndroidManifest) {
        (
            cell_seed(0x51),
            AndroidManifest::new(
                "com.example.maps",
                [
                    AndroidPermission::Internet,
                    AndroidPermission::AccessFineLocation,
                ],
            )
            .with_intent_filters([IntentFilter::new(["android.intent.action.VIEW"], ["geo"])]),
        )
    }
    fn browser() -> (CellId, AndroidManifest) {
        (
            cell_seed(0x52),
            AndroidManifest::new("com.example.browser", [AndroidPermission::Internet])
                .with_intent_filters([IntentFilter::new(
                    ["android.intent.action.VIEW"],
                    ["http", "https"],
                )]),
        )
    }
    fn contacts() -> (CellId, AndroidManifest) {
        (
            cell_seed(0x53),
            AndroidManifest::new("com.android.contacts", [AndroidPermission::ReadContacts])
                .with_content_authorities(["com.android.contacts"])
                .with_broadcast_receivers([IntentFilter::new(
                    ["com.example.SYNC"],
                    Vec::<String>::new(),
                )]),
        )
    }

    fn registry() -> InstalledApps {
        let mut apps = InstalledApps::new();
        for (cell, manifest) in [maps(), browser(), contacts()] {
            apps.install(cell, manifest, AppLaunch::Package("pkg".into()), [0x11; 32]);
        }
        apps
    }

    /// Install returns the appfactory descriptor (the cap-gated birth) AND registers the app.
    #[test]
    fn install_is_the_birth_plus_the_registry_entry() {
        let mut apps = InstalledApps::new();
        let (cell, manifest) = maps();
        let desc = apps.install(
            cell,
            manifest,
            AppLaunch::Package("com.example.maps".into()),
            [0x11; 32],
        );
        // Two declared permissions ⟹ exactly two cap templates (the appfactory property).
        assert_eq!(desc.allowed_cap_templates.len(), 2);
        // And the app is now installed.
        assert!(apps.get(cell).is_some());
        assert_eq!(apps.apps().len(), 1);
    }

    /// **THE LOAD-BEARING TEST: the resolver a launching cell gets ranges ONLY over the
    /// installed apps it holds a cap to — an app it was never granted is not a candidate.**
    #[test]
    fn resolver_ranges_only_over_the_granted_neighborhood() {
        let apps = registry();
        let me = cell_seed(9);
        let (maps_cell, _) = maps();
        let (browser_cell, _) = browser();

        // Granted maps only.
        let granted: BTreeSet<CellId> = [maps_cell].into_iter().collect();
        let resolver = apps.resolver_for(me, &granted);
        let surface = SurfaceCapability::root(me, AuthRequired::Either);

        // A geo VIEW resolves to maps (granted + its manifest published the geo filter).
        let geo = AndroidIntent::view("android.intent.action.VIEW", "geo:0,0?q=cafe");
        assert!(resolver.resolve(&surface, &geo).decision.resolved());

        // An https VIEW reaches NOTHING — the browser is installed but NOT granted, so it
        // is not in this cell's neighborhood (no ambient device-wide resolution).
        let web = AndroidIntent::view("android.intent.action.VIEW", "https://example.com");
        assert!(
            resolver
                .resolve(&surface, &web)
                .decision
                .refused_no_handler(),
            "the browser is installed but ungranted — not a candidate"
        );

        // Granting the browser too brings it into the neighborhood.
        let granted2: BTreeSet<CellId> = [maps_cell, browser_cell].into_iter().collect();
        let resolver2 = apps.resolver_for(me, &granted2);
        assert!(resolver2.resolve(&surface, &web).decision.resolved());
    }

    /// **THE FULL LOOP, no device: install → launch → fire intent → route to a cap-reachable
    /// handler on the runtime.** Exercises `launch_installed_app` welding the resolver to the
    /// `CapturedFrameRuntime` as the intent sink (via the `&mut S` impl), proving the launched
    /// app's outbound intent reaches ONLY a granted handler's `am start`.
    #[test]
    fn launch_then_dispatch_routes_to_a_granted_handler_on_the_runtime() {
        use crate::intentgate::AndroidIntentGate;
        use crate::runtime::{CapturedFrameRuntime, launch_installed_app};

        let apps = registry();
        let me = cell_seed(9);
        let (maps_cell, _) = maps();
        let (browser_cell, _) = browser();
        let granted: BTreeSet<CellId> = [maps_cell, browser_cell].into_iter().collect();

        let mut rt = CapturedFrameRuntime::from_screencap_raw(Vec::new());
        // Launch the maps app as `me`; the resolver is built over `me`'s cap-reachable apps.
        let resolver = launch_installed_app(&mut rt, &apps, maps_cell, &granted)
            .expect("the installed maps app launches + yields a resolver");

        // Weld the resolver to the runtime as the intent sink; dispatch a geo VIEW.
        let surface = SurfaceCapability::root(me, AuthRequired::Either);
        {
            let mut gate = AndroidIntentGate::new(resolver, &mut rt);
            let geo = AndroidIntent::view("android.intent.action.VIEW", "geo:0,0?q=cafe");
            let r = gate.dispatch(&surface, geo);
            assert!(r.decision.resolved(), "the geo VIEW resolves");

            // A SEND/mailto reaches nothing — no granted handler published that filter.
            let mail = AndroidIntent::view("android.intent.action.SEND", "mailto:x@y.z");
            assert!(gate.dispatch(&surface, mail).decision.refused_no_handler());
        }

        // Only the resolved geo VIEW reached the runtime's `am start` (recorded by the sink).
        assert_eq!(
            rt.intents_dispatched.len(),
            1,
            "only the resolved intent dispatched"
        );
        assert_eq!(
            rt.intents_dispatched[0].1, maps_cell,
            "routed to the maps handler cell"
        );
    }

    /// Launching a cell that was never installed is an error (not a silent empty resolver).
    #[test]
    fn launch_unknown_app_errors() {
        use crate::runtime::{CapturedFrameRuntime, launch_installed_app};
        let apps = registry();
        let mut rt = CapturedFrameRuntime::from_screencap_raw(Vec::new());
        let granted: BTreeSet<CellId> = BTreeSet::new();
        let err = launch_installed_app(&mut rt, &apps, cell_seed(0xFE), &granted);
        assert!(matches!(
            err,
            Err(crate::runtime::RuntimeError::AppNotInstalled { .. })
        ));
    }

    /// The install↔content loop: a granted provider-app's published authority is a
    /// cap-reachable [`ContentProvider`]; an ungranted one is not.
    #[test]
    fn content_resolver_ranges_only_over_the_granted_neighborhood() {
        let apps = registry();
        let me = cell_seed(9);
        let (contacts_cell, _) = contacts();

        // Ungranted: the contacts provider is unreachable.
        let none: BTreeSet<CellId> = BTreeSet::new();
        let r0 = apps.content_resolver_for(me, &none, ProviderGrant::ReadOnly);
        let uri = ContentUri::parse("content://com.android.contacts/people").unwrap();
        assert!(
            r0.resolve(&uri, ContentAccess::Read)
                .decision
                .refused_no_provider()
        );

        // Granted (read): a read is granted, but a write is refused by the read-only grant.
        let granted: BTreeSet<CellId> = [contacts_cell].into_iter().collect();
        let r1 = apps.content_resolver_for(me, &granted, ProviderGrant::ReadOnly);
        assert!(r1.resolve(&uri, ContentAccess::Read).decision.granted());
        assert!(
            r1.resolve(&uri, ContentAccess::Write)
                .decision
                .refused_read_only(),
            "a read-only grant does not amplify to a write"
        );
    }

    /// The install↔service loop: an app's declared permissions grant a cap to the matching
    /// system-service organs; a service whose permission was NOT declared is unreachable.
    #[test]
    fn service_resolver_ranges_over_the_declared_permission_organs() {
        use crate::organgate::{ServiceGrant, ServiceOp, SystemService};

        let apps = registry();
        // `maps` declared INTERNET + ACCESS_FINE_LOCATION ⟹ a cap to Location (+ Connectivity).
        let (maps_cell, _) = maps();
        let resolver = apps.service_resolver_for(maps_cell, ServiceGrant::ReadOnly);

        // A location read is granted (the location permission was declared).
        let loc = ServiceOp::query(SystemService::Location, "getLastKnownLocation");
        assert!(resolver.resolve(&loc).decision.granted());

        // The camera organ is NOT reachable — maps never declared the CAMERA permission.
        let cam = ServiceOp::query(SystemService::Camera, "getCameraIdList");
        assert!(
            resolver.resolve(&cam).decision.refused_no_organ(),
            "no cap-reachable camera organ — the permission was never declared"
        );

        // A read-only grant does not amplify to a state-changing location call.
        let upd = ServiceOp::resolve(SystemService::Location, "requestLocationUpdates");
        assert!(resolver.resolve(&upd).decision.refused_read_only());
    }

    /// The install↔broadcast loop: a broadcast fans out over only the granted apps that
    /// published a matching `<receiver>` filter; an ungranted app is never a candidate (the
    /// no-ambient-global-broadcast property, sourced from the real installed-app set).
    #[test]
    fn broadcast_router_ranges_only_over_the_granted_neighborhood() {
        use crate::broadcastgate::{Broadcast, Sender};

        let apps = registry();
        let me = cell_seed(9);
        let (contacts_cell, _) = contacts();

        // Ungranted: the contacts app's SYNC receiver is unreachable — fan-out delivers to
        // nothing.
        let none: BTreeSet<CellId> = BTreeSet::new();
        let r0 = apps.broadcast_router_for(me, &none);
        let bc = Broadcast::action("com.example.SYNC");
        let sender = Sender::app(me, []);
        assert!(
            r0.send(&sender, &bc).decision.delivered_to().is_empty(),
            "an ungranted receiver never receives (no ambient broadcast)"
        );

        // Granted: the contacts app's SYNC receiver is now a cap-reachable delivery target.
        let granted: BTreeSet<CellId> = [contacts_cell].into_iter().collect();
        let r1 = apps.broadcast_router_for(me, &granted);
        let receipt = r1.send(&sender, &bc);
        assert!(receipt.decision.fanned_out());
        assert_eq!(receipt.decision.delivered_to(), vec![contacts_cell]);
    }

    /// The install↔storage loop: an app always reaches its OWN scope (ReadWrite, no permission),
    /// reaches the shared MediaStore collections only if it declared a storage permission (READ
    /// → ReadOnly, WRITE → ReadWrite), and never reaches another app's scope (no ambient FS).
    #[test]
    fn storage_resolver_ranges_over_the_declared_storage_grants() {
        use crate::storagegate::{StorageAccess, StorageReach};

        let mut apps = registry();
        // A gallery app declaring READ_EXTERNAL_STORAGE (shared media, read-only).
        let gallery_cell = cell_seed(0x54);
        apps.install(
            gallery_cell,
            AndroidManifest::new(
                "com.example.gallery",
                [AndroidPermission::ReadExternalStorage],
            ),
            AppLaunch::Package("pkg".into()),
            [0x11; 32],
        );

        // `maps` declared no storage permission ⟹ only its own scope, no shared media.
        let (maps_cell, _) = maps();
        let maps_store = apps.storage_resolver_for(maps_cell);

        let own = StorageReach::parse(
            "/storage/emulated/0/Android/data/com.example.maps/files/cache.bin",
        )
        .unwrap();
        assert!(
            maps_store
                .resolve(&own, StorageAccess::Write)
                .decision
                .granted(),
            "an app always read/writes its OWN scope"
        );

        let images = StorageReach::parse("content://media/external/images/media/1").unwrap();
        assert!(
            maps_store
                .resolve(&images, StorageAccess::Read)
                .decision
                .refused_unreachable(),
            "no storage permission ⟹ shared media is unreachable (no ambient FS)"
        );

        // The gallery reaches shared images read-only; a write does not amplify.
        let gallery_store = apps.storage_resolver_for(gallery_cell);
        assert!(
            gallery_store
                .resolve(&images, StorageAccess::Read)
                .decision
                .granted(),
            "READ_EXTERNAL_STORAGE grants a read cap to the media collections"
        );
        assert!(
            gallery_store
                .resolve(&images, StorageAccess::Write)
                .decision
                .refused_read_only(),
            "a read cap does not amplify to a write"
        );

        // Neither app reaches the OTHER's private scope.
        let maps_secret = StorageReach::parse(
            "/storage/emulated/0/Android/data/com.example.maps/files/cache.bin",
        )
        .unwrap();
        assert!(
            gallery_store
                .resolve(&maps_secret, StorageAccess::Read)
                .decision
                .refused_unreachable(),
            "the gallery cannot read the maps app's private scope"
        );
    }

    /// The install↔permission loop: an installed app's manifest is exactly what the cap-badge
    /// surface renders — its normal permission lit at install, its dangerous permission dim
    /// until a receipted hand-over; an uninstalled cell has no permbox.
    #[test]
    fn permbox_for_renders_the_installed_apps_badges() {
        use crate::permgate::BadgeState;

        let apps = registry();
        let (maps_cell, _) = maps();
        let principal = cell_seed(0x01);

        // No permbox for a cell that was never installed.
        assert!(
            apps.permbox_for(cell_seed(0xFE), principal, []).is_none(),
            "an uninstalled cell has no manifest, so no badge surface"
        );

        // The maps app declared INTERNET (normal) + ACCESS_FINE_LOCATION (dangerous); the
        // principal holds the location authority.
        let mut pb = apps
            .permbox_for(
                maps_cell,
                principal,
                [AndroidPermission::AccessFineLocation],
            )
            .expect("the installed maps app has a badge surface");

        // INTERNET is lit at install; ACCESS_FINE_LOCATION is dim until handed over.
        assert!(pb.holds(&AndroidPermission::Internet));
        assert!(!pb.holds(&AndroidPermission::AccessFineLocation));

        // The hand-over (the dialog, reforged) lights the location badge with a receipt.
        let receipt = pb.grant(AndroidPermission::AccessFineLocation);
        assert!(receipt.decision.granted());
        assert!(pb.holds(&AndroidPermission::AccessFineLocation));

        // CAMERA was never declared → its badge is dim and a hand-over is refused.
        let cam = pb
            .badges()
            .badges
            .into_iter()
            .find(|b| b.permission == AndroidPermission::Camera)
            .expect("camera is shown in the roster (never hidden)");
        assert_eq!(cam.state, BadgeState::Dim);
    }

    /// **THE INSTALL↔NOTIFICATION LOOP: the shade cap is sourced from the declared
    /// `POST_NOTIFICATIONS` permission — an app that never declared it cannot post (no ambient
    /// push), and a posting app reaches only the channels it created.**
    #[test]
    fn notif_poster_sources_the_shade_cap_from_the_declared_permission() {
        use crate::notifgate::{NotificationChannel, NotificationImportance, PostGrant};

        let mut apps = InstalledApps::new();
        // A messenger app that DID declare POST_NOTIFICATIONS (the Android 13+ door).
        let messenger = cell_seed(0x71);
        apps.install(
            messenger,
            AndroidManifest::new(
                "com.example.messenger",
                [
                    AndroidPermission::Internet,
                    AndroidPermission::Other(POST_NOTIFICATIONS.into()),
                ],
            ),
            AppLaunch::Package("com.example.messenger".into()),
            [0x11; 32],
        );
        // The maps app did NOT declare it.
        let (maps_cell, maps_manifest) = maps();
        apps.install(
            maps_cell,
            maps_manifest,
            AppLaunch::Package("m".into()),
            [0x11; 32],
        );

        let channels = [NotificationChannel::new(
            "messages",
            NotificationImportance::Default,
            "Messages",
        )];

        // The messenger holds the shade cap (declared) → a post to its channel is receipted.
        let messenger_poster =
            apps.notif_poster_for(messenger, channels.clone(), PostGrant::Standard);
        assert!(messenger_poster.holds_organ_cap());
        let posted = messenger_poster.post(&crate::notifgate::Notification::on("messages"));
        assert!(posted.decision.posted());

        // The maps app did NOT declare POST_NOTIFICATIONS → it holds no shade cap, every post
        // refused (no ambient post), even to the same channel set.
        let maps_poster = apps.notif_poster_for(maps_cell, channels, PostGrant::Standard);
        assert!(!maps_poster.holds_organ_cap());
        assert!(
            maps_poster
                .post(&crate::notifgate::Notification::on("messages"))
                .decision
                .refused_no_organ()
        );
    }
}
