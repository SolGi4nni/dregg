//! **Cap-gate the NOTIFICATION POST.** The confined Android app's
//! `NotificationManager.notify(channel, notification)` reforged from an ambient push to a
//! privileged shade into a **cap-bounded, receipted post against a named notification organ
//! cell** — `GRAPHIDEOS.md §1` (the notification-system / SystemUI-shade row) made real, in the
//! same shape as the proven [`crate::organgate`] / [`crate::contentgate`] / [`crate::broadcastgate`]
//! / [`crate::permgate`] gates.
//!
//! # What Android does (the ambient mechanism deos replaces)
//!
//! In stock Android an app calls `getSystemService(NOTIFICATION_SERVICE)` and then
//! `NotificationManager.notify(id, notification)`. The framework's **`NotificationManagerService`**
//! — a privileged `system_server` component — accepts the post and pushes it into the global
//! **notification shade** (SystemUI), where it is shown device-wide: a heads-up peek, a status-bar
//! icon, a sound, possibly a **full-screen intent** that seizes the whole display. Since Android O
//! every post must name a **`NotificationChannel`** (created via `createNotificationChannel`) whose
//! **importance** (`IMPORTANCE_NONE`…`IMPORTANCE_MAX`) decides how loudly it intrudes. The ambient
//! shape: any app holding `NotificationManager` (pre-13: every app) can push to the *shared* shade;
//! Android 13+ adds the `POST_NOTIFICATIONS` runtime permission as the only door, and
//! `USE_FULL_SCREEN_INTENT` gates the most intrusive class — but the shade itself is a single
//! privileged sink every app reaches by name, not by a cap.
//!
//! # What graphideOS does (the cap-bounded reforge)
//!
//! `GRAPHIDEOS.md §1`: *"a notification is an `EmittedEvent` on a turn's receipt; the shade is a
//! view over recent receipts you hold caps to."* This module is that, in the same shape as the
//! sibling gates and over the [`crate::organgate`] organ-cell vocabulary — the notification shade
//! is the **same notification organ** `organgate` names ([`notification_shade_organ`] binds the two):
//!
//! 1. **Posting requires a cap to the notification organ — no ambient post.** A
//!    [`NotifPoster`] that does not hold the notification-organ (shade) cap refuses EVERY post
//!    ([`NotifDecision::RefusedNoOrgan`]): a confined app cannot reach the shade it was never handed
//!    a cap to (the deos form of `POST_NOTIFICATIONS` as a held cap, not an ambient `notify`).
//! 2. **A channel the app holds no cap to is refused.** A post routes to a
//!    [`NotificationChannel`] by id; the poster ranges over only the **cap-reachable channel
//!    neighborhood** (the channels the app created / was granted), NOT the device's channel table.
//!    A post to a channel no [`ChannelCap`] answers is [`NotifDecision::RefusedNoChannel`] —
//!    faithful to AOSP, where a post to a non-existent channel is dropped.
//! 3. **Each admitted post is a receipted turn — the `EmittedEvent` on the organ cell.** Exactly
//!    one cap-reachable channel answers AND the grant admits the post's class ⟹
//!    [`NotifDecision::Posted`]: a cap-bounded, content-addressed [`NotifReceipt`] landing the
//!    notification as a receipted event on the named notification organ cell, not an ambient push.
//! 4. **High-priority / full-screen-intent classes need a stronger cap (the attenuation tooth).**
//!    A post whose [`PostClass`] is [`PostClass::Priority`] — a heads-up–importance channel
//!    (`IMPORTANCE_HIGH`/`MAX`) OR a notification carrying a **full-screen intent** — against a
//!    channel cap granted only [`PostGrant::Standard`] is [`NotifDecision::RefusedUnderprivileged`]:
//!    a standard post cap does not amplify to a heads-up / screen-seizing post (the `granted ⊆ held`
//!    lattice, notification-side). AOSP's `USE_FULL_SCREEN_INTENT` / importance split becomes a cap
//!    attenuation checked at the gate, before the shade is touched.
//!
//! Every decision leaves a content-addressed [`NotifReceipt`], so the android-cell's
//! notification-post traffic is auditable end to end exactly like the organ / content / broadcast /
//! permission receipts.
//!
//! # The depth (honest, like the sibling gates')
//!
//! This is the **post-and-authority** layer: the gate decides, against the held organ cap + the
//! granted channel set + their grants, whether (and at what class) a `notify` may reach the shade,
//! and records it. The remaining frontier — interposing the *actual* binder
//! `INotificationManager.enqueueNotificationWithTag` transaction inside the confined runtime so the
//! device's SystemUI itself renders only cap-admitted posts (the HAL/binder leg the sibling gates
//! also name), and the in-circuit constructor proof that a given organ cell IS the device's
//! notification shade — are the same not-yet-claimed depth. What IS real today: the post-resolution
//! algebra + the organ-cap and channel teeth + the class attenuation + the faithful AOSP importance
//! classification + the receipt, testable on any node with no device.

use dregg_firmament::CellId;

/// The AOSP `POST_NOTIFICATIONS` runtime permission (Android 13+) — the only door to the shade.
/// A confined app's hold of THIS permission is what grants the notification-organ (shade) cap; an
/// app that never declared it cannot post at all (the [`NotifDecision::RefusedNoOrgan`] end).
pub const POST_NOTIFICATIONS: &str = "android.permission.POST_NOTIFICATIONS";

/// The AOSP `USE_FULL_SCREEN_INTENT` permission — the door to the most intrusive post class (a
/// notification that seizes the whole display). Modeled here as the per-post [`PostClass::Priority`]
/// the [`PostGrant::Priority`] cap is required to clear.
pub const USE_FULL_SCREEN_INTENT: &str = "android.permission.USE_FULL_SCREEN_INTENT";

/// **The device's notification shade organ cell** — the named capability holder a post is landed
/// on. Bound to [`crate::organgate::SystemService::Notification`]'s organ cell so the
/// notification gate and the system-service gate name the SAME organ (a post through `notifgate`
/// and a `getSystemService(NOTIFICATION_SERVICE)` reach through `organgate` resolve to one organ
/// identity). On a real device the boot resolves this to the reforged SystemUI shade cell.
pub fn notification_shade_organ() -> CellId {
    crate::organgate::SystemService::Notification.organ_cell()
}

/// **An AOSP `NotificationChannel` importance** — `NotificationManager.IMPORTANCE_*`. The
/// per-channel knob that decides how loudly a post intrudes (and, in deos, whether it is a
/// [`PostClass::Priority`] post needing the stronger cap). Faithful to the AOSP constants.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum NotificationImportance {
    /// `IMPORTANCE_NONE` (0) — the channel is blocked; nothing shows.
    None,
    /// `IMPORTANCE_MIN` (1) — no sound, no status-bar icon.
    Min,
    /// `IMPORTANCE_LOW` (2) — no sound.
    Low,
    /// `IMPORTANCE_DEFAULT` (3) — makes a sound, no heads-up peek.
    Default,
    /// `IMPORTANCE_HIGH` (4) — makes a sound AND a heads-up peek (intrudes).
    High,
    /// `IMPORTANCE_MAX` (5) — the loudest; heads-up + full intrusion.
    Max,
}

impl NotificationImportance {
    /// The exact AOSP `NotificationManager.IMPORTANCE_*` int the framework uses.
    pub fn aosp_code(&self) -> i32 {
        match self {
            NotificationImportance::None => 0,
            NotificationImportance::Min => 1,
            NotificationImportance::Low => 2,
            NotificationImportance::Default => 3,
            NotificationImportance::High => 4,
            NotificationImportance::Max => 5,
        }
    }

    /// Does a channel of this importance produce a **heads-up peek** (an intrusive interruption)?
    /// Faithful to AOSP: a heads-up notification needs `IMPORTANCE_HIGH` or above. A heads-up post
    /// is a [`PostClass::Priority`] post (needs the stronger cap).
    pub fn is_heads_up(&self) -> bool {
        matches!(
            self,
            NotificationImportance::High | NotificationImportance::Max
        )
    }
}

/// **An AOSP `NotificationChannel`** — the routing + importance unit a post names. graphideOS
/// routes a post on the **channel id** (the stable per-app key, case-sensitive in AOSP); the
/// importance decides the [`PostClass`] the cap must clear. The app holds a [`ChannelCap`] over
/// each channel it may post to (no ambient channel).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct NotificationChannel {
    /// The channel id — the stable routing key a `notify` names (`createNotificationChannel`'s id).
    pub id: String,
    /// The channel's importance — its heads-up / intrusion level (and the [`PostClass`] driver).
    pub importance: NotificationImportance,
    /// A short human label for the chooser / status line (the channel's user-visible name).
    pub label: String,
}

impl NotificationChannel {
    /// A channel with an explicit id + importance + label.
    pub fn new(
        id: impl Into<String>,
        importance: NotificationImportance,
        label: impl Into<String>,
    ) -> Self {
        NotificationChannel {
            id: id.into(),
            importance,
            label: label.into(),
        }
    }

    /// Does this channel answer `channel_id`? (The AOSP channel-match key — exact id, case-sensitive.)
    pub fn answers(&self, channel_id: &str) -> bool {
        self.id == channel_id
    }
}

/// **The class of a notification post** — the deos form of AOSP's heads-up / full-screen-intent
/// intrusion split, the thing the cap attenuation gates. Derived from the target channel's
/// importance + whether the notification carries a full-screen intent (see
/// [`Notification::requested_class`]).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum PostClass {
    /// An ordinary post — a non-heads-up channel (`IMPORTANCE` below `HIGH`) and no full-screen
    /// intent. Cleared by any [`PostGrant`].
    Standard,
    /// A high-intrusion post — a heads-up–importance channel (`IMPORTANCE_HIGH`/`MAX`) OR a
    /// notification carrying a **full-screen intent** (which seizes the display). Cleared ONLY by a
    /// [`PostGrant::Priority`] cap (the attenuation tooth).
    Priority,
}

impl PostClass {
    pub fn is_priority(&self) -> bool {
        matches!(self, PostClass::Priority)
    }

    fn tag(&self) -> &'static str {
        match self {
            PostClass::Standard => "standard",
            PostClass::Priority => "priority",
        }
    }
}

/// What a holder was granted over a notification channel — the deos form of AOSP's
/// importance / `USE_FULL_SCREEN_INTENT` split, expressed as a cap attenuation. A
/// [`Standard`](Self::Standard) grant cannot amplify to a [`PostClass::Priority`] post.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum PostGrant {
    /// The holder may post **ordinary** notifications only — a heads-up / full-screen-intent post
    /// is refused (the attenuation tooth).
    Standard,
    /// The holder may post ordinary AND high-intrusion (heads-up / full-screen-intent)
    /// notifications — the stronger cap.
    Priority,
}

impl PostGrant {
    /// Does this grant admit a post of `class`? `Standard` admits only [`PostClass::Standard`].
    pub fn admits(&self, class: PostClass) -> bool {
        match (self, class) {
            (PostGrant::Priority, _) => true,
            (PostGrant::Standard, PostClass::Standard) => true,
            (PostGrant::Standard, PostClass::Priority) => false,
        }
    }
}

/// **A notification the confined app tried to post** — the channel it targets, an optional tag (the
/// AOSP `notify(tag, id)` dedup key), and whether it carries a **full-screen intent**. The unit the
/// [`NotifPoster`] gates: the deos form of a `NotificationManager.notify(…)` call.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Notification {
    /// The channel id the post routes to (`Notification.Builder(context, channelId)`).
    pub channel_id: String,
    /// A short tag for the post (the AOSP `notify(tag, id)` key) — carried for the receipt.
    pub tag: String,
    /// Whether the notification carries a **full-screen intent** (`Notification.fullScreenIntent`)
    /// — the most intrusive class, which forces the post to [`PostClass::Priority`] regardless of
    /// the channel's importance (AOSP gates this with `USE_FULL_SCREEN_INTENT`).
    pub full_screen_intent: bool,
}

impl Notification {
    /// A bare post to `channel_id` (the common `notify(id, builder.build())` shape) — no
    /// full-screen intent.
    pub fn on(channel_id: impl Into<String>) -> Self {
        Notification {
            channel_id: channel_id.into(),
            tag: String::new(),
            full_screen_intent: false,
        }
    }

    /// Tag the post (the AOSP `notify(tag, id)` key — builder).
    pub fn tagged(mut self, tag: impl Into<String>) -> Self {
        self.tag = tag.into();
        self
    }

    /// Mark the post as carrying a **full-screen intent** (builder) — forces [`PostClass::Priority`].
    pub fn with_full_screen_intent(mut self) -> Self {
        self.full_screen_intent = true;
        self
    }

    /// **The post's [`PostClass`]** against its target `channel` — `Priority` iff the notification
    /// carries a full-screen intent OR the channel's importance is heads-up (`HIGH`/`MAX`),
    /// `Standard` otherwise. The faithful AOSP intrusion split the cap attenuation gates.
    pub fn requested_class(&self, channel: &NotificationChannel) -> PostClass {
        if self.full_screen_intent || channel.importance.is_heads_up() {
            PostClass::Priority
        } else {
            PostClass::Standard
        }
    }

    /// A short tag for the receipt digest + status line.
    fn id_tag(&self) -> String {
        if self.tag.is_empty() {
            self.channel_id.clone()
        } else {
            format!("{}#{}", self.channel_id, self.tag)
        }
    }
}

/// **A cap-reachable notification channel in the android-cell's bounded neighborhood** — the deos
/// form of a `NotificationChannel` the app created / was granted a post cap to. Held by the
/// [`NotifPoster`] only for channels the app holds a cap to (NOT the device's channel table). A
/// post to it lands a receipted event on the notification organ cell.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ChannelCap {
    /// The notification organ cell the post lands on (the shade) — [`notification_shade_organ`].
    pub cell: CellId,
    /// The channel this cap admits posting to.
    pub channel: NotificationChannel,
    /// The post authority the holder was granted over this channel (the cap attenuation).
    pub grant: PostGrant,
}

impl ChannelCap {
    /// A channel cap for an explicit organ cell + channel + grant.
    pub fn new(cell: CellId, channel: NotificationChannel, grant: PostGrant) -> Self {
        ChannelCap {
            cell,
            channel,
            grant,
        }
    }

    /// **A channel cap over the device's standard notification shade organ** with the given grant —
    /// the organ cell is [`notification_shade_organ`]. The unit a runtime's `createNotificationChannel`
    /// + a granted post-cap builds from.
    pub fn standard(channel: NotificationChannel, grant: PostGrant) -> Self {
        ChannelCap::new(notification_shade_organ(), channel, grant)
    }

    /// Does this cap answer `channel_id`? (The channel-match key — channel identity.)
    pub fn answers(&self, channel_id: &str) -> bool {
        self.channel.answers(channel_id)
    }
}

/// The four distinguishable ends a notification post can hit — the notification-side analogue of
/// [`crate::organgate::ServiceDecision`]. There is no `Ambiguous` end: AOSP channel ids are unique
/// per app, so a post routes to at most one channel (no chooser).
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum NotifDecision {
    /// The app holds the organ cap AND a cap-reachable channel answered AND the grant admits the
    /// post's class: a cap-bounded, receipted post to the shade organ (a receipted event on the
    /// notification organ cell).
    Posted {
        organ: CellId,
        channel_id: String,
        class: PostClass,
    },
    /// NO cap to the notification organ — the no-ambient-post property: the app cannot reach the
    /// shade it was never granted a cap to (the deos form of a missing `POST_NOTIFICATIONS`).
    RefusedNoOrgan,
    /// The app holds the organ cap, but NO cap-reachable channel answers this id — faithful to
    /// AOSP, where a post to a non-existent channel is dropped.
    RefusedNoChannel { channel_id: String },
    /// A [`PostClass::Priority`] post (heads-up / full-screen-intent) against a channel the holder
    /// was granted only [`PostGrant::Standard`] — refused by the cap attenuation (a standard post
    /// cap does not amplify to a heads-up / screen-seizing post).
    RefusedUnderprivileged {
        organ: CellId,
        channel_id: String,
        class: PostClass,
    },
}

impl NotifDecision {
    pub fn posted(&self) -> bool {
        matches!(self, NotifDecision::Posted { .. })
    }
    pub fn refused_no_organ(&self) -> bool {
        matches!(self, NotifDecision::RefusedNoOrgan)
    }
    pub fn refused_no_channel(&self) -> bool {
        matches!(self, NotifDecision::RefusedNoChannel { .. })
    }
    pub fn refused_underprivileged(&self) -> bool {
        matches!(self, NotifDecision::RefusedUnderprivileged { .. })
    }

    fn tag(&self) -> &'static str {
        match self {
            NotifDecision::Posted { .. } => "posted",
            NotifDecision::RefusedNoOrgan => "refused-no-organ",
            NotifDecision::RefusedNoChannel { .. } => "refused-no-channel",
            NotifDecision::RefusedUnderprivileged { .. } => "refused-underprivileged",
        }
    }
}

/// **The receipt left by a gated notification post.** Every decision produces one, so the
/// android-cell's `notify` traffic is auditable end to end exactly like the organ / content /
/// broadcast / permission receipts. Content-addressed:
/// `decision_digest = blake3(cell? ‖ post_tag ‖ fsi ‖ outcome ‖ organ? ‖ class?)`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct NotifReceipt {
    /// The android-cell whose held organ cap + granted channel set decided this post.
    pub cell: Option<CellId>,
    /// The notification the confined app tried to post.
    pub notification: Notification,
    /// The decision reached.
    pub decision: NotifDecision,
    /// `blake3(…)[..32]` — the content-addressed witness a verifier reconstructs.
    pub decision_digest: [u8; 32],
}

impl NotifReceipt {
    fn digest(cell: Option<CellId>, n: &Notification, decision: &NotifDecision) -> [u8; 32] {
        let mut h = blake3::Hasher::new();
        h.update(b"graphideos-notif-post-v1");
        if let Some(c) = cell {
            h.update(b"\x01cell");
            h.update(c.as_bytes());
        }
        h.update(n.id_tag().as_bytes());
        h.update(b"\x00");
        h.update(if n.full_screen_intent {
            b"\x01fsi"
        } else {
            b"\x00fsi"
        });
        h.update(decision.tag().as_bytes());
        match decision {
            NotifDecision::Posted {
                organ,
                channel_id,
                class,
            }
            | NotifDecision::RefusedUnderprivileged {
                organ,
                channel_id,
                class,
            } => {
                h.update(organ.as_bytes());
                h.update(channel_id.as_bytes());
                h.update(class.tag().as_bytes());
            }
            NotifDecision::RefusedNoChannel { channel_id } => {
                h.update(channel_id.as_bytes());
            }
            NotifDecision::RefusedNoOrgan => {}
        }
        *h.finalize().as_bytes()
    }

    /// A one-line audit truth for the cockpit status line — which end, named exactly.
    pub fn status_line(&self) -> String {
        match &self.decision {
            NotifDecision::Posted {
                channel_id, class, ..
            } => format!(
                "android-notif: ✔ notify «{channel_id}» → posted to the shade organ as a receipted {} event — a named organ cell, not an ambient push",
                match class {
                    PostClass::Standard => "standard",
                    PostClass::Priority => "high-priority",
                }
            ),
            NotifDecision::RefusedNoOrgan => format!(
                "android-notif: ✖ notify «{}» REFUSED — the app holds no cap to the notification organ (no ambient post; the POST_NOTIFICATIONS door was never handed over)",
                self.notification.channel_id
            ),
            NotifDecision::RefusedNoChannel { channel_id } => format!(
                "android-notif: ✖ notify «{channel_id}» REFUSED — no cap-reachable channel answers «{channel_id}» (the app cannot post to a channel it holds no cap to)"
            ),
            NotifDecision::RefusedUnderprivileged { channel_id, .. } => format!(
                "android-notif: ✖ notify «{channel_id}» REFUSED — a high-priority / full-screen-intent post needs a stronger cap (a standard post cap does not amplify to a heads-up post)"
            ),
        }
    }
}

/// **The cap-gated notification poster for one android-cell — the post surface over the cell's
/// bounded, cap-reachable channel neighborhood**, NOT the device's global
/// `NotificationManagerService`. Holds whether the cell holds the notification-organ (shade) cap,
/// the granted channel set, and the cell it speaks for; holds NO ambient authority — every
/// [`post`](Self::post) is a pure function of its organ cap + channels.
pub struct NotifPoster {
    /// Whether the cell holds the notification-organ (shade) cap — the no-ambient-post door.
    holds_organ_cap: bool,
    channels: Vec<ChannelCap>,
    cell: Option<CellId>,
}

impl NotifPoster {
    /// Build a poster: `holds_organ_cap` (does the cell hold the notification-organ/shade cap), the
    /// granted channel neighborhood, and the cell it speaks for. Channels are deduped by id (a
    /// channel granted twice is one routing key); a confined app with no organ cap or no channels
    /// posts nothing.
    pub fn new(
        holds_organ_cap: bool,
        channels: impl IntoIterator<Item = ChannelCap>,
        cell: Option<CellId>,
    ) -> Self {
        let mut channels: Vec<ChannelCap> = channels.into_iter().collect();
        // Stable order + dedup by channel id (AOSP channel ids are unique per app).
        channels.sort_by(|a, b| a.channel.id.cmp(&b.channel.id));
        channels.dedup_by(|a, b| a.channel.id == b.channel.id);
        NotifPoster {
            holds_organ_cap,
            channels,
            cell,
        }
    }

    /// Does the cell hold the notification-organ (shade) cap?
    pub fn holds_organ_cap(&self) -> bool {
        self.holds_organ_cap
    }

    /// The granted channel neighborhood (the cap-reachable set a post may route to).
    pub fn channels(&self) -> &[ChannelCap] {
        &self.channels
    }

    /// **THE NOTIFICATION GATE.** The confined app tried to post `notification` (a
    /// `NotificationManager.notify(…)`). Decide against the held organ cap + the granted channel
    /// set + their grants, and return the decision AND its [`NotifReceipt`].
    ///
    /// Order of teeth (fail-closed):
    /// 1. **The organ cap** — no cap to the notification organ ⟹ [`NotifDecision::RefusedNoOrgan`]
    ///    (no ambient post).
    /// 2. **The channel match** — no cap-reachable channel answers the id ⟹
    ///    [`NotifDecision::RefusedNoChannel`].
    /// 3. **The class attenuation** — a [`PostClass::Priority`] post against a [`PostGrant::Standard`]
    ///    channel cap ⟹ [`NotifDecision::RefusedUnderprivileged`]. Otherwise [`NotifDecision::Posted`].
    pub fn post(&self, notification: &Notification) -> NotifReceipt {
        // TOOTH 1 — THE ORGAN CAP. No cap to the shade organ, no post.
        if !self.holds_organ_cap {
            return self.receipt(notification, NotifDecision::RefusedNoOrgan);
        }

        // TOOTH 2 — THE CHANNEL MATCH. Range ONLY over the cap-reachable channels.
        let cap = self
            .channels
            .iter()
            .find(|c| c.answers(&notification.channel_id));
        let Some(cap) = cap else {
            return self.receipt(
                notification,
                NotifDecision::RefusedNoChannel {
                    channel_id: notification.channel_id.clone(),
                },
            );
        };

        // TOOTH 3 — THE CLASS ATTENUATION. A heads-up / full-screen-intent post needs the stronger cap.
        let class = notification.requested_class(&cap.channel);
        let decision = if cap.grant.admits(class) {
            NotifDecision::Posted {
                organ: cap.cell,
                channel_id: notification.channel_id.clone(),
                class,
            }
        } else {
            NotifDecision::RefusedUnderprivileged {
                organ: cap.cell,
                channel_id: notification.channel_id.clone(),
                class,
            }
        };
        self.receipt(notification, decision)
    }

    fn receipt(&self, notification: &Notification, decision: NotifDecision) -> NotifReceipt {
        let decision_digest = NotifReceipt::digest(self.cell, notification, &decision);
        NotifReceipt {
            cell: self.cell,
            notification: notification.clone(),
            decision,
            decision_digest,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use dregg_firmament::cell_seed;

    fn updates_channel() -> NotificationChannel {
        NotificationChannel::new("updates", NotificationImportance::Default, "App updates")
    }
    fn alarms_channel() -> NotificationChannel {
        NotificationChannel::new("alarms", NotificationImportance::High, "Alarms")
    }

    /// **THE LOAD-BEARING TEST: an app holding no cap to the notification organ cannot post — no
    /// ambient post to the shade.**
    #[test]
    fn no_organ_cap_refuses_every_post() {
        let me = cell_seed(9);
        // The app even "has" a channel, but holds NO organ cap — it still cannot post.
        let poster = NotifPoster::new(
            false,
            [ChannelCap::standard(updates_channel(), PostGrant::Standard)],
            Some(me),
        );
        let n = Notification::on("updates");
        let receipt = poster.post(&n);

        assert!(
            receipt.decision.refused_no_organ(),
            "no shade cap ⟹ no post (no ambient notify)"
        );
        assert_eq!(receipt.cell, Some(me));
        assert!(receipt.status_line().contains("no ambient post"));
        assert_eq!(
            receipt.decision_digest,
            NotifReceipt::digest(Some(me), &n, &receipt.decision)
        );
    }

    /// A standard post to a granted ordinary channel, with the organ cap held ⟹ a receipted post.
    #[test]
    fn standard_post_to_a_granted_channel_is_receipted() {
        let me = cell_seed(9);
        let poster = NotifPoster::new(
            true,
            [ChannelCap::standard(updates_channel(), PostGrant::Standard)],
            Some(me),
        );
        let receipt = poster.post(&Notification::on("updates").tagged("sync-done"));
        match &receipt.decision {
            NotifDecision::Posted {
                organ,
                channel_id,
                class,
            } => {
                assert_eq!(*organ, notification_shade_organ());
                assert_eq!(channel_id, "updates");
                assert_eq!(*class, PostClass::Standard);
            }
            other => panic!("expected Posted, got {other:?}"),
        }
        assert!(receipt.status_line().contains("receipted standard event"));
    }

    /// **A channel the app holds no cap to is refused — the app cannot post to a channel it was
    /// never granted (faithful AOSP: a post to a non-existent channel is dropped).**
    #[test]
    fn post_to_an_ungranted_channel_is_refused() {
        let me = cell_seed(9);
        let poster = NotifPoster::new(
            true,
            [ChannelCap::standard(updates_channel(), PostGrant::Standard)],
            Some(me),
        );
        // The app holds "updates" only — "promos" is not in the neighborhood.
        let receipt = poster.post(&Notification::on("promos"));
        assert!(receipt.decision.refused_no_channel());
        assert!(receipt.status_line().contains("holds no cap"));
        assert_eq!(
            receipt.decision,
            NotifDecision::RefusedNoChannel {
                channel_id: "promos".into()
            }
        );
    }

    /// **THE ATTENUATION TOOTH: a heads-up (IMPORTANCE_HIGH) post against a Standard channel cap is
    /// refused — a standard post cap does not amplify to a heads-up post.**
    #[test]
    fn heads_up_post_against_a_standard_grant_is_refused() {
        let me = cell_seed(9);
        // The alarms channel is IMPORTANCE_HIGH (heads-up), but the cap is only Standard.
        let poster = NotifPoster::new(
            true,
            [ChannelCap::standard(alarms_channel(), PostGrant::Standard)],
            Some(me),
        );
        let n = Notification::on("alarms");
        // The class is Priority because the channel importance is heads-up.
        assert_eq!(n.requested_class(&alarms_channel()), PostClass::Priority);
        let receipt = poster.post(&n);
        assert!(receipt.decision.refused_underprivileged());
        assert!(receipt.status_line().contains("stronger cap"));
        assert_eq!(
            receipt.decision,
            NotifDecision::RefusedUnderprivileged {
                organ: notification_shade_organ(),
                channel_id: "alarms".into(),
                class: PostClass::Priority,
            }
        );
    }

    /// A Priority channel cap admits a heads-up post (which commits as a receipted high-priority event).
    #[test]
    fn heads_up_post_against_a_priority_grant_is_posted() {
        let me = cell_seed(9);
        let poster = NotifPoster::new(
            true,
            [ChannelCap::standard(alarms_channel(), PostGrant::Priority)],
            Some(me),
        );
        let receipt = poster.post(&Notification::on("alarms"));
        assert!(receipt.decision.posted());
        assert!(receipt.status_line().contains("high-priority"));
    }

    /// **THE FULL-SCREEN-INTENT TOOTH: a full-screen-intent post forces the Priority class even on
    /// an ordinary (DEFAULT-importance) channel — a Standard cap is refused, a Priority cap posts.**
    #[test]
    fn full_screen_intent_forces_priority_class() {
        let me = cell_seed(9);
        // The "updates" channel is only DEFAULT importance, but the post carries a full-screen intent.
        let fsi = Notification::on("updates").with_full_screen_intent();
        assert_eq!(
            fsi.requested_class(&updates_channel()),
            PostClass::Priority,
            "a full-screen intent forces Priority regardless of channel importance"
        );

        // A Standard cap refuses the full-screen-intent post...
        let weak = NotifPoster::new(
            true,
            [ChannelCap::standard(updates_channel(), PostGrant::Standard)],
            Some(me),
        );
        assert!(weak.post(&fsi).decision.refused_underprivileged());

        // ...but a Priority cap admits it.
        let strong = NotifPoster::new(
            true,
            [ChannelCap::standard(updates_channel(), PostGrant::Priority)],
            Some(me),
        );
        assert!(strong.post(&fsi).decision.posted());
    }

    /// The notification gate names the SAME organ the system-service gate does (one organ identity).
    #[test]
    fn shade_organ_is_bound_to_the_system_service_organ() {
        assert_eq!(
            notification_shade_organ(),
            crate::organgate::SystemService::Notification.organ_cell(),
            "the notification shade organ IS organgate's notification organ"
        );
    }

    /// The AOSP importance classification is faithful (heads-up iff HIGH/MAX) and the codes match.
    #[test]
    fn importance_classification_is_faithful() {
        assert!(!NotificationImportance::None.is_heads_up());
        assert!(!NotificationImportance::Default.is_heads_up());
        assert!(NotificationImportance::High.is_heads_up());
        assert!(NotificationImportance::Max.is_heads_up());
        assert_eq!(NotificationImportance::Default.aosp_code(), 3);
        assert_eq!(NotificationImportance::High.aosp_code(), 4);
        assert_eq!(NotificationImportance::Max.aosp_code(), 5);
    }

    /// The receipt is content-addressed and stable across construction order (channels deduped +
    /// sorted by id).
    #[test]
    fn receipt_is_content_addressed_and_stable() {
        let me = cell_seed(9);
        let p1 = NotifPoster::new(
            true,
            [
                ChannelCap::standard(updates_channel(), PostGrant::Standard),
                ChannelCap::standard(alarms_channel(), PostGrant::Priority),
            ],
            Some(me),
        );
        let p2 = NotifPoster::new(
            true,
            [
                ChannelCap::standard(alarms_channel(), PostGrant::Priority),
                ChannelCap::standard(updates_channel(), PostGrant::Standard),
            ],
            Some(me),
        );
        let n = Notification::on("updates").tagged("x");
        assert_eq!(
            p1.post(&n).decision_digest,
            p2.post(&n).decision_digest,
            "the post digest is order-independent (channels sorted + deduped by id)"
        );
    }
}
