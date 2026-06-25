//! `android-cell` — an Android app as a cap-confined deos cell-surface.
//!
//! # The one paragraph
//!
//! An android-cell runs a foreign runtime (an Android app) the SAME way the webcell
//! runs Servo: a confined renderer paints into a surface deos grabs as an **RGBA8
//! tile** ([`RgbaFrame`]), presents through the **UNCHANGED** `present_frame` /
//! `CompositorPd` gate (the T1 non-overlap / T2 label-binding / T3 focus teeth),
//! drives its **I/O through cap-gated effects with no ambient authority**, and leaves
//! a **receipt** for every gated act — `servo : web :: android-runtime : android`.
//! See `docs/deos/ANDROID-CELL.md`.
//!
//! # What is reuse and what is new
//!
//! The expensive half — tile → glass — is **free**: [`servo_render::present_frame`]
//! and `CompositorPd` take ANY [`RgbaFrame`] unchanged; an android frame is just a
//! different source. The NEW work is exactly the two seams that were runtime-specific:
//!
//! 1. **The runtime** ([`runtime`]) — a host-adaptive [`AndroidRuntime`] that boots a
//!    device, runs an app, and exposes its surface as an [`RgbaFrame`], with one impl
//!    per host. On **macOS** the simulator host is the **Android Emulator** (Google's,
//!    runs via Hypervisor.framework — NO Linux `binder`/`ashmem` modules needed); on
//!    **Linux** the natural impl is **redroid** (the container path the original doc
//!    named). This crate ships the macOS-emulator impl ([`runtime::MacOsEmulatorRuntime`])
//!    first since it is the dev host, plus a host-independent [`runtime::CapturedFrameRuntime`]
//!    stand-in (a saved screencap or PNG) so the seam compiles + tests on any node.
//!
//! 2. **The I/O gate** ([`netgate`]) — the app's outbound network bound to the held
//!    [`SurfaceCapability`] through `Netlayer::dial`, exactly the webcell's
//!    `NetcapConnector` discipline: a cap-denied origin is `RefusedByCap` **before any
//!    socket**, and reaches nothing on the glass; each decision is an [`IoReceipt`].
//!
//! # The honest macOS correction
//!
//! `ANDROID-CELL.md` originally called macOS a hard wall ("Android containers need
//! Linux `binder`/`ashmem`"). That is true of *containers* (redroid/Waydroid) — but
//! NOT of *emulators*. The Android Emulator runs a full guest kernel under
//! Hypervisor.framework, so it is a real, confining Android runtime on the macOS dev
//! host. The wall was a container-vs-emulator distinction; the simulator host crosses
//! it. The deep per-syscall I/O gate (sensor/intent at HAL/binder granularity) remains
//! the named frontier on BOTH hosts; the shallow net gate is real today (§5).

pub mod appfactory;
pub mod apps;
pub mod broadcastgate;
pub mod checkpoint;
pub mod checkpointed_runtime;
pub mod contentgate;
pub mod frame;
pub mod input;
pub mod intentgate;
pub mod netgate;
pub mod notifgate;
pub mod organgate;
pub mod permgate;
pub mod present;
pub mod runtime;
pub mod storagegate;

pub use appfactory::{AndroidManifest, AndroidPermission, ProtectionLevel};
pub use apps::{InstalledApp, InstalledApps};
pub use broadcastgate::{
    Broadcast, BroadcastDecision, BroadcastReceipt, BroadcastReceiver, BroadcastRouter, Delivery,
    DeliveryOutcome, Sender, is_protected_action,
};
pub use checkpoint::{
    ServiceCellCheckpoint, UDomain, UKey, UProjection, UVal, UmemKind, UmemOp,
    diff as checkpoint_diff, emit_boundary_trace, fold as checkpoint_fold,
};
pub use checkpointed_runtime::{CheckpointError, CheckpointedRuntime};
pub use contentgate::{
    ContentAccess, ContentDecision, ContentProvider, ContentReceipt, ContentResolver, ContentUri,
    ProviderGrant,
};
pub use frame::{ANDROID_SCREENCAP_HEADER_LEN, ScreencapError, screencap_to_rgba};
pub use input::{
    AndroidInput, AndroidInputGate, AndroidInputSink, InputDecision, InputError, InputReceipt,
    RecordingInputSink, cap_admits_input,
};
pub use intentgate::{
    AndroidIntent, AndroidIntentGate, AndroidIntentSink, IntentDecision, IntentError, IntentFilter,
    IntentHandler, IntentReceipt, IntentResolver, RecordingIntentSink,
};
pub use netgate::{AndroidNetGate, IoDecision, IoReceipt};
pub use notifgate::{
    ChannelCap, NotifDecision, NotifPoster, NotifReceipt, Notification, NotificationChannel,
    NotificationImportance, PostClass, PostGrant, notification_shade_organ,
};
pub use organgate::{
    ServiceCallKind, ServiceDecision, ServiceGrant, ServiceOp, ServiceOrgan, ServiceReceipt,
    ServiceResolver, SystemService,
};
pub use permgate::{
    BadgeReason, BadgeState, CapBadge, CapBadgeSet, KernelGrantOutcome, PermBox, PermCheckReceipt,
    PermDecision, PermReceipt, PermWorld, PermissionCheck,
};
pub use present::{AndroidPresentation, present_android_frame};
pub use runtime::{
    AndroidRuntime, AppLaunch, CapturedFrameRuntime, DeviceSpec, RuntimeError, RuntimeKind,
    launch_installed_app,
};
pub use storagegate::{
    MediaKind, StorageAccess, StorageCell, StorageDecision, StorageGrant, StorageReach,
    StorageReceipt, StorageResolver, StorageVolume,
};

#[cfg(target_os = "macos")]
pub use runtime::MacOsEmulatorRuntime;

// Re-export the reused compositor vocabulary so a caller wires the android-cell
// without separately depending on servo-render / firmament for these types.
pub use servo_render::RgbaFrame;
