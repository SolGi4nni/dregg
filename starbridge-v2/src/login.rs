//! The deos **LOGIN CEREMONY** as a RUNNING gpui surface — the boot front door.
//!
//! deos boots into THIS surface, not the cockpit. Picking an identity runs the
//! real ceremony from [`crate::session`] — authenticate (a held-key stand-in;
//! the live manager runs a key challenge / KERI pre-rotation), derive the root
//! identity cell, and grant the per-user [`CapTemplate`] FROM the deos image's
//! **system principal** via a REAL `Effect::GrantCapability` turn through the
//! embedded executor — yielding a live [`Session`]. On success the window root
//! swaps to the cockpit, wrapped in a thin [`SessionShell`] that names the
//! logged-in principal and carries the **Logout** action.
//!
//! Logout is one move: [`LoginManager::logout`] revokes the session root, the
//! whole cap-tree goes dark synchronously (`n = 1`), and the root swaps back to
//! this login surface. The model, made operable:
//!
//! > **login = receiving your root capability · a session = the cap-tree you
//! > hold · logout = revoking it.**
//!
//! This module is the gpui (visual) layer — gated on `gpui-ui`, like
//! [`crate::cockpit`]. The flow it drives is the gpui-free, `cargo test`-able
//! [`crate::session`]; this only paints the picker + wires the click → ceremony
//! → root-swap. See `docs/deos/SESSION-LOGIN.md`.

use std::cell::RefCell;
use std::rc::Rc;
use std::time::Duration;

use gpui::{
    div, prelude::*, px, App, Context, Entity, FocusHandle, IntoElement, MouseButton,
    ParentElement, Render, SharedString, Styled, Window,
};

use crate::cockpit::Cockpit;
use crate::views::theme;
use starbridge_v2::reflect;
use starbridge_v2::session::{
    demo_identities, open_session_world, provision_system_principal, session_base_dir,
    start_fresh_session_world, DemoIdentity, IdentityKeystore, IdentityKind, LoginManager,
    LoginOutcome, Session,
};
use starbridge_v2::world::{self, World};

/// The LOGIN SURFACE — the boot front door. Holds everything the post-login
/// transition needs to construct the cockpit (the shared world, the anchors, the
/// pending demo-seed plan, the optional live-node URL), the [`LoginManager`] (the
/// trusted session cell over the image's system principal), and the identity
/// roster the picker shows. A failed/refused login leaves an in-surface message.
pub struct LoginSurface {
    world: Rc<RefCell<World>>,
    #[allow(dead_code)] // carried for cockpit construction on a successful login
    anchors: [dregg_cell::CellId; 3],
    seed: Option<world::DemoSeed>,
    node_url: Option<String>,
    manager: LoginManager,
    identities: Vec<DemoIdentity>,
    focus: FocusHandle,
    /// The last refusal/error to show under the picker (the in-band "denied").
    message: Option<String>,
    /// THE RECOVERY PHRASE shown ONCE after a NEW identity's keypair is minted —
    /// the owner's 24-word key in human form, to write down and keep. deos persists
    /// only the derived seed (encrypted at rest), never this phrase, so this is the
    /// single moment it is visible. `None` for a returning user (their key is
    /// already custodied) and once dismissed.
    recovery: Option<String>,
    /// When opening the durable image was UNSALVAGEABLE (recovery itself failed),
    /// the identity the owner was logging in as — so the surface can offer an
    /// explicit "start fresh" choice (quarantine the corrupt image, provision a
    /// new one) instead of dead-ending. `None` in the normal case.
    fresh_offer: Option<DemoIdentity>,
    /// THE FRONT DOOR vs the FULL PICKER. A first-timer should not meet a debug
    /// roster — they meet a warm welcome with ONE inviting way in (`Welcome`).
    /// The roster (ember / guest / Hermes) is still *reachable*, one quiet click
    /// away (`Picker`) — the power reveals progressively, it is not shoved.
    stage: WelcomeStage,
}

/// Which face the login surface is showing. The boot face is the warm `Welcome`
/// (one inviting "begin"); a quiet "other ways in" reveals the full `Picker`
/// (the ember / guest / Hermes roster) for those who want it. The Jobs/Woz bar:
/// a first-timer is greeted, not handed a control panel.
#[derive(Clone, Copy, PartialEq, Eq)]
enum WelcomeStage {
    /// The warm front door — a greeting + one "begin"/"welcome back" affordance,
    /// plus a quiet link to the roster.
    Welcome,
    /// The full identity roster (the held-key stand-in picker) — reachable, not
    /// shoved. The recovery / "start fresh" choices live here too.
    Picker,
}

impl LoginSurface {
    /// Build the login surface over the boot image. Provisions the deos image's
    /// **system principal** (the root identity holding the anchor caps a fresh
    /// session is drawn from) into the world via the genesis path, then offers
    /// the demo identity roster.
    pub fn boot(
        world: Rc<RefCell<World>>,
        anchors: [dregg_cell::CellId; 3],
        seed: world::DemoSeed,
        node_url: Option<String>,
        focus: FocusHandle,
    ) -> Self {
        let system_principal = {
            let mut w = world.borrow_mut();
            provision_system_principal(&mut w, &anchors)
        };
        LoginSurface {
            world,
            anchors,
            seed: Some(seed),
            node_url,
            manager: LoginManager::new(system_principal),
            identities: demo_identities(),
            focus,
            message: None,
            recovery: None,
            fresh_offer: None,
            // Boot into the warm front door — the welcome, not the roster.
            stage: WelcomeStage::Welcome,
        }
    }

    /// The stable secret-store LABEL of the primary human owner — the key
    /// [`IdentityKeystore`] mints/loads for the warm "begin". Fixed (`"ember"`) so
    /// the SAME keypair is re-derived every launch (one owner, one persistent key).
    const PRIMARY_LABEL: &'static str = "ember";

    /// The deos image's identity keystore — durable key custody over `dregg-secrets`
    /// under the deos image root. Cheap to build (a file-store handle); constructed
    /// on demand rather than threaded through every constructor.
    fn keystore(&self) -> Option<IdentityKeystore> {
        IdentityKeystore::default_for(&session_base_dir()).ok()
    }

    /// The PRIMARY identity the warm "begin" mints/presents — the human owner. This
    /// is the REAL key ceremony: a returning owner's persisted keypair is loaded
    /// from the keystore; a brand-new owner has a keypair MINTED + persisted (the
    /// recovery phrase is surfaced once). Returns the key-backed [`DemoIdentity`] and
    /// the recovery phrase to show ON A FRESH MINT (`None` on return). Falls back to
    /// the fixed dev identity if the keystore is unavailable (so login never
    /// dead-ends on a missing secret store — the held-key stand-in still works).
    fn primary_identity(&self) -> (DemoIdentity, Option<String>) {
        let fallback = || {
            self.identities
                .iter()
                .find(|i| matches!(i.kind, IdentityKind::User))
                .cloned()
                .unwrap_or_else(|| self.identities[0].clone())
        };
        let Some(ks) = self.keystore() else {
            return (fallback(), None);
        };
        match ks.identity_for(
            Self::PRIMARY_LABEL,
            "ember",
            IdentityKind::User,
            "you — your minted root key, your sovereign world",
        ) {
            Ok((id, recovery)) => (id, recovery),
            // The store is unreadable (a permissions / disk fault) — fall back to the
            // dev identity rather than block the door. The session is still real; it
            // just isn't custodied in the encrypted store this launch.
            Err(_) => (fallback(), None),
        }
    }

    /// Whether the primary owner has a custodied key already — i.e. this is a
    /// RETURNING owner (greet "welcome back" + present the key) rather than a
    /// brand-new one (greet "this is your world" + mint the key). Checked *before*
    /// login so the front door's words fit. Consults the keystore (key presence is
    /// the real "have you been here"); a missing key reads as new — the inviting
    /// default. Never fails: it only chooses a greeting.
    fn is_returning(&self) -> bool {
        self.keystore()
            .map(|ks| ks.has_identity(Self::PRIMARY_LABEL))
            .unwrap_or(false)
    }

    /// **THE WARM "BEGIN" — run the real key ceremony.** Mint-or-present the primary
    /// owner's key via the keystore, then enter their world:
    ///
    /// - **New owner (a keypair was just minted):** surface the 24-word RECOVERY
    ///   PHRASE and STOP, requiring an explicit acknowledgement ("I've saved it")
    ///   before proceeding — the owner must see their key once, since deos persists
    ///   only the derived seed. The ack ([`Self::acknowledge_recovery`]) re-enters
    ///   here; the key now exists, so this resolves to the returning-user path and
    ///   logs in.
    /// - **Returning owner (the key was loaded):** run [`Self::login_as`] straight
    ///   away — present the custodied key, re-derive the same root cell + session.
    fn begin(&mut self, window: &mut Window, cx: &mut Context<Self>) {
        let (identity, recovery) = self.primary_identity();
        if let Some(phrase) = recovery {
            // A FRESH MINT: show the recovery phrase and wait for acknowledgement
            // before entering (do NOT swap the root away while the phrase is unseen).
            self.recovery = Some(phrase);
            cx.notify();
            return;
        }
        // Returning owner (or the phrase was just acknowledged) — present the key.
        self.login_as(identity, window, cx);
    }

    /// Acknowledge the freshly-minted recovery phrase ("I've saved it, continue") —
    /// clear it and re-enter [`Self::begin`]. The key is now persisted, so `begin`
    /// resolves to the returning-user path and logs the new owner in.
    fn acknowledge_recovery(&mut self, window: &mut Window, cx: &mut Context<Self>) {
        self.recovery = None;
        self.begin(window, cx);
    }

    /// Focus the login surface on open so it receives keystrokes.
    pub fn focus_on_open(&self, window: &mut Window, cx: &mut Context<Self>) {
        window.focus(&self.focus, cx);
    }

    /// Run the ceremony for the picked identity and, on a live session, SWAP the
    /// window root to the cockpit (wrapped in a [`SessionShell`]). On a refusal
    /// (auth failed / an over-grant the system principal cannot make) the surface
    /// shows the executor's reason and stays put — auth gates everything.
    fn login_as(&mut self, identity: DemoIdentity, window: &mut Window, cx: &mut Context<Self>) {
        // AUTHENTICATE — the held-key stand-in (picking the identity IS the proof
        // of possession in the demo; the live manager runs a key challenge). The
        // flow is exact: no principal ⟹ nothing downstream runs.
        let Some(principal) = self.manager.authenticate(identity.pubkey, true) else {
            self.message = Some(format!("authentication failed for {}", identity.name));
            cx.notify();
            return;
        };

        // OPEN THE PER-USER DURABLE WORLD — SESSION RESUME (Houyhnhnm orthogonal
        // persistence). The session runs over the principal's OWN durable image
        // (`deos-session-<root>.redb`), not the shared boot/demo world: on first
        // login it is provisioned (anchors + system principal, durably mirrored);
        // on a relaunch `World::open_recovering` recovers the exact cell graph +
        // balances + history — and RECOVERS a torn/divergent image (truncating the
        // divergent tail to the last consistent state) rather than refusing it, so
        // the owner is never stranded. Only a wholly-unsalvageable image errs here,
        // which we surface as the explicit "start fresh" choice below (never a
        // dead-end). The shared `Rc<RefCell<World>>` the cockpit renders is swapped
        // to it, so the cockpit renders the resumed (or recovered) image.
        let base_dir = session_base_dir();
        // The demo / desktop image meters free (matching `World::new`), so the
        // per-user durable image opens under the same zero-cost model (the receipts
        // re-derive bit-identically only under the cost model the image was made
        // with — zero here, the demo desktop's).
        let costs = dregg_turn::ComputronCosts::zero();
        let opened = open_session_world(&base_dir, &principal, costs);
        let (user_world, anchors, manager, fresh) = match opened {
            Ok(t) => t,
            Err(e) => {
                // Recovery itself was impossible — DO NOT dead-end. Offer the owner
                // an explicit "start fresh" choice (quarantine the corrupt image,
                // provision a new one); they can always log in.
                self.message = Some(format!(
                    "could not open your durable image: {e}\n\
                     your last session couldn't be salvaged — start fresh? \
                     (the corrupt image is kept aside for recovery)"
                ));
                self.fresh_offer = Some(identity);
                cx.notify();
                return;
            }
        };
        self.fresh_offer = None;
        self.finish_login(
            user_world, anchors, manager, fresh, principal, identity, window, cx,
        );
    }

    /// Start a FRESH durable image for the picked identity after recovery was
    /// impossible: quarantine the unsalvageable image aside and provision a new
    /// one, then run the ceremony. The owner is never stranded — recovered when
    /// possible (the normal `login_as` path), fresh when not (this path).
    fn start_fresh(&mut self, identity: DemoIdentity, window: &mut Window, cx: &mut Context<Self>) {
        let Some(principal) = self.manager.authenticate(identity.pubkey, true) else {
            self.message = Some(format!("authentication failed for {}", identity.name));
            cx.notify();
            return;
        };
        let base_dir = session_base_dir();
        let costs = dregg_turn::ComputronCosts::zero();
        let (user_world, anchors, manager, fresh) =
            match start_fresh_session_world(&base_dir, &principal, costs) {
                Ok(t) => t,
                Err(e) => {
                    // A fresh provision should not fail; if it does, report honestly
                    // (the disk/path is unwritable) — still not a silent dead-end.
                    self.message = Some(format!("could not start a fresh durable image: {e}"));
                    cx.notify();
                    return;
                }
            };
        self.fresh_offer = None;
        self.message = None;
        self.finish_login(
            user_world, anchors, manager, fresh, principal, identity, window, cx,
        );
    }

    /// The shared post-open ceremony: resume/grant the session over the (recovered,
    /// resumed, or freshly-provisioned) durable world, attach the signing seed,
    /// swap the shared world, and transition to the cockpit. Reached by both the
    /// normal `login_as` and the `start_fresh` recovery branch.
    #[allow(clippy::too_many_arguments)]
    fn finish_login(
        &mut self,
        mut user_world: World,
        anchors: [dregg_cell::CellId; 3],
        manager: LoginManager,
        fresh: bool,
        principal: starbridge_v2::session::Principal,
        identity: DemoIdentity,
        window: &mut Window,
        cx: &mut Context<Self>,
    ) {
        // LOGIN, RESUMABLE — resume a live durable session if the image carries
        // one (no re-grant), else run the full grant ceremony FROM the per-user
        // system principal and persist the session record. A revoked record does
        // NOT resume (it re-runs the ceremony — the logout darkening is honored).
        let template = identity.template(anchors);
        let session = match manager.login_resumable(&mut user_world, principal, &template) {
            LoginOutcome::Session(s) => s,
            LoginOutcome::Denied { reason } => {
                self.message = Some(format!("login refused: {reason}"));
                cx.notify();
                return;
            }
        };
        // CARRY THE SIGNING CAPABILITY — attach the picked identity's DEV signing
        // seed to the session so the cockpit can CLIENT-SIGN turns as the logged-in
        // identity (`session.user_clerk()` / `session.user_default_cell()`). The
        // grant ceremony / durable resume know only the proven principal (a pubkey);
        // the seed is re-derived here from the identity the user actually picked. A
        // dev seed — honest convenience, NOT production key custody.
        let session = session.with_signing_seed(identity.dev_seed);

        // Swap the shared world to the principal's durable image — the cockpit the
        // session shell builds renders THIS image (resumed or freshly provisioned).
        *self.world.borrow_mut() = user_world;

        // SUCCESS — transition to the session. Swap the window root to the cockpit
        // over the (now per-user durable) shared world, wrapped in the session
        // shell. The demo seed turns run ONLY on a FRESH image (a relaunch resumes
        // its real history, so the illustrative seed must not re-run / mismatch the
        // per-user anchors); carry the base dir so logout writes the revoked record.
        let world = self.world.clone();
        let seed = if fresh { self.seed.take() } else { None };
        let node_url = self.node_url.clone();
        let identities = self.identities.clone();
        // The deos image root dir (deterministic) — where logout writes the revoked
        // session record into the principal's durable image.
        let base_dir = session_base_dir();

        SessionShell::open(
            window, cx, world, anchors, seed, node_url, manager, identities, session, identity,
            base_dir, fresh,
        );
    }

    fn identity_card(&self, identity: &DemoIdentity, cx: &mut Context<Self>) -> impl IntoElement {
        let id = identity.clone();
        let name = identity.name.to_string();
        let blurb = identity.blurb.to_string();
        let (glyph, tag, tag_color) = match identity.kind {
            IdentityKind::User => ("@", "user", theme::accent()),
            IdentityKind::Agent => ("#", "agent", theme::warn()),
        };
        div()
            .id(SharedString::from(format!("login-{}", identity.name)))
            .flex()
            .flex_col()
            .gap_1()
            .w(px(420.))
            .px_3()
            .py_2()
            .rounded_md()
            .bg(theme::panel())
            .border_1()
            .border_color(theme::border())
            .cursor_pointer()
            .hover(|s| s.bg(theme::panel_hi()))
            .on_mouse_down(
                MouseButton::Left,
                cx.listener(move |this, _ev, window, cx| {
                    this.login_as(id.clone(), window, cx);
                }),
            )
            .child(
                div()
                    .flex()
                    .justify_between()
                    .items_center()
                    .child(
                        div()
                            .text_color(theme::text())
                            .child(format!("{glyph}  {name}")),
                    )
                    .child(crate::views::pill(tag, tag_color)),
            )
            .child(div().text_xs().text_color(theme::muted()).child(blurb))
    }
}

impl LoginSurface {
    /// THE WARM FRONT DOOR (`WelcomeStage::Welcome`) — what a first-timer meets:
    /// not a debug roster, but a greeting + ONE inviting way in. A NEW owner is
    /// told "this is your world" and offered **Begin** (which mints their identity
    /// and root capability under the hood). A RETURNING owner is greeted **Welcome
    /// back** and resumes their durable image. The full roster (guest / Hermes /
    /// explicit ember) is one quiet "other ways in" click away — reachable, not
    /// shoved. The recovery / "start fresh" choice, when present, is surfaced here
    /// too (never a dead-end).
    fn welcome_view(&self, cx: &mut Context<Self>) -> impl IntoElement {
        let returning = self.is_returning();
        let (greeting, sub, begin_label) = if returning {
            (
                "welcome back",
                "your world is as you left it — receive it again.",
                "welcome back",
            )
        } else {
            (
                "this is your world",
                "a sovereign, verifiable place that is yours alone. step in.",
                "begin",
            )
        };

        div()
            .key_context("Login")
            .track_focus(&self.focus)
            .size_full()
            .flex()
            .flex_col()
            .items_center()
            .justify_center()
            .gap_6()
            .bg(theme::bg())
            .text_color(theme::text())
            // The mark + the one-line spirit (login = receiving your world).
            .child(
                div()
                    .flex()
                    .flex_col()
                    .items_center()
                    .gap_2()
                    .child(div().text_3xl().text_color(theme::accent()).child("deos"))
                    .child(
                        div()
                            .text_xl()
                            .text_color(theme::text())
                            .child(SharedString::from(greeting)),
                    )
                    .child(
                        div()
                            .max_w(px(420.))
                            .text_sm()
                            .text_color(theme::muted())
                            .child(SharedString::from(sub)),
                    ),
            )
            // THE ONE INVITING WAY IN — Begin / Welcome back. A single warm button
            // that runs the REAL key ceremony under the hood: a new owner has a
            // keypair MINTED + persisted (the recovery phrase surfaces once); a
            // returning owner PRESENTS their custodied key. The whole ceremony runs
            // from this one click; no chooser is in the way.
            .child(
                div()
                    .id("welcome-begin")
                    .px(px(28.))
                    .py(px(12.))
                    .rounded_md()
                    .bg(theme::accent())
                    .text_color(theme::bg())
                    .cursor_pointer()
                    .hover(|s| s.opacity(0.9))
                    .on_mouse_down(
                        MouseButton::Left,
                        cx.listener(move |this, _ev, window, cx| {
                            this.begin(window, cx);
                        }),
                    )
                    .child(SharedString::from(begin_label)),
            )
            // The quiet door to the full roster — present, not shoved (progressive
            // disclosure: the power is one click away when wanted).
            .child(
                div()
                    .id("welcome-other-ways")
                    .text_xs()
                    .text_color(theme::muted())
                    .cursor_pointer()
                    .hover(|s| s.text_color(theme::accent()))
                    .on_mouse_down(
                        MouseButton::Left,
                        cx.listener(|this, _ev, _w, cx| {
                            this.stage = WelcomeStage::Picker;
                            cx.notify();
                        }),
                    )
                    .child("other ways in · guest · an agent →"),
            )
            // A refusal / recovery message stays visible on the welcome face too.
            .when_some(self.message.clone(), |el, msg| {
                el.child(
                    div()
                        .max_w(px(420.))
                        .px_3()
                        .py_2()
                        .rounded_md()
                        .bg(theme::panel())
                        .text_xs()
                        .text_color(theme::bad())
                        .child(msg),
                )
            })
            // THE NEVER-DEAD-END CHOICE — when recovery itself was impossible, the
            // explicit "start fresh" affordance is surfaced here too.
            .when_some(self.fresh_offer.clone(), |el, identity| {
                el.child(self.start_fresh_button(identity, cx))
            })
            // THE RECOVERY PHRASE — shown ONCE after a fresh keypair is minted. The
            // owner's 24-word key; they save it, then acknowledge to enter. deos
            // persists only the derived seed, so this is the single moment it shows.
            .when_some(self.recovery.clone(), |el, phrase| {
                el.child(self.recovery_panel(phrase, cx))
            })
    }

    /// THE RECOVERY-PHRASE PANEL — the one-time reveal of a freshly-minted owner's
    /// 24-word key, with the "I've saved it, continue" acknowledgement that enters
    /// their world. The genuine key-custody moment: deos stores only the derived
    /// seed (encrypted at rest), so this phrase is the owner's own recovery path and
    /// is shown exactly once, here.
    fn recovery_panel(&self, phrase: String, cx: &mut Context<Self>) -> impl IntoElement {
        div()
            .flex()
            .flex_col()
            .items_center()
            .gap_3()
            .max_w(px(520.))
            .px_4()
            .py_3()
            .rounded_md()
            .bg(theme::panel())
            .border_1()
            .border_color(theme::accent())
            .child(
                div()
                    .text_sm()
                    .text_color(theme::text())
                    .child("your recovery phrase — write it down, keep it safe"),
            )
            .child(div().text_xs().text_color(theme::muted()).child(
                "this is your key. deos keeps only the derived seed (encrypted); \
                         this phrase is shown once and is yours to hold.",
            ))
            .child(
                div()
                    .w_full()
                    .px_3()
                    .py_2()
                    .rounded_md()
                    .bg(theme::bg())
                    .text_color(theme::accent())
                    .child(SharedString::from(phrase)),
            )
            .child(
                div()
                    .id("recovery-ack")
                    .px(px(20.))
                    .py(px(8.))
                    .rounded_md()
                    .bg(theme::accent())
                    .text_color(theme::bg())
                    .cursor_pointer()
                    .hover(|s| s.opacity(0.9))
                    .on_mouse_down(
                        MouseButton::Left,
                        cx.listener(|this, _ev, window, cx| {
                            this.acknowledge_recovery(window, cx);
                        }),
                    )
                    .child("I've saved it — enter my world"),
            )
    }

    /// THE FULL PICKER (`WelcomeStage::Picker`) — the identity roster (the held-key
    /// stand-in). Reachable from the warm welcome via "other ways in"; carries a
    /// quiet "← back" to the front door. This is the original boot face, now one
    /// layer of disclosure deeper.
    fn picker_view(&self, cx: &mut Context<Self>) -> impl IntoElement {
        let cards: Vec<_> = self
            .identities
            .clone()
            .iter()
            .map(|i| self.identity_card(i, cx).into_any_element())
            .collect();

        div()
            .key_context("Login")
            .track_focus(&self.focus)
            .size_full()
            .flex()
            .flex_col()
            .items_center()
            .justify_center()
            .gap_4()
            .bg(theme::bg())
            .text_color(theme::text())
            .child(
                div()
                    .flex()
                    .flex_col()
                    .items_center()
                    .gap_1()
                    .child(div().text_2xl().text_color(theme::accent()).child("deos"))
                    .child(
                        div()
                            .text_sm()
                            .text_color(theme::muted())
                            .child("login = receiving your root capability"),
                    ),
            )
            // A quiet "← back" to the warm front door.
            .child(
                div()
                    .id("picker-back")
                    .text_xs()
                    .text_color(theme::muted())
                    .cursor_pointer()
                    .hover(|s| s.text_color(theme::accent()))
                    .on_mouse_down(
                        MouseButton::Left,
                        cx.listener(|this, _ev, _w, cx| {
                            this.stage = WelcomeStage::Welcome;
                            cx.notify();
                        }),
                    )
                    .child("← back"),
            )
            .child(
                div()
                    .text_xs()
                    .text_color(theme::muted())
                    .child("choose an identity (the demo's held-key stand-in)"),
            )
            .child(div().flex().flex_col().gap_2().children(cards))
            .when_some(self.message.clone(), |el, msg| {
                el.child(
                    div()
                        .w(px(420.))
                        .px_3()
                        .py_2()
                        .rounded_md()
                        .bg(theme::panel())
                        .text_xs()
                        .text_color(theme::bad())
                        .child(msg),
                )
            })
            // THE NEVER-DEAD-END CHOICE: when the durable image was unsalvageable
            // (recovery itself failed), offer an explicit "start fresh" button —
            // it quarantines the corrupt image aside and provisions a new one, so
            // the owner can ALWAYS proceed to a session.
            .when_some(self.fresh_offer.clone(), |el, identity| {
                el.child(self.start_fresh_button(identity, cx))
            })
    }

    /// The explicit "start fresh" button (the never-dead-end recovery choice) —
    /// shared by both the welcome and the picker faces.
    fn start_fresh_button(
        &self,
        identity: DemoIdentity,
        cx: &mut Context<Self>,
    ) -> impl IntoElement {
        let id = identity.clone();
        div()
            .id("start-fresh")
            .w(px(420.))
            .px_3()
            .py_2()
            .rounded_md()
            .bg(theme::panel_hi())
            .text_xs()
            .text_color(theme::warn())
            .cursor_pointer()
            .hover(|s| s.bg(theme::border()))
            .on_mouse_down(
                MouseButton::Left,
                cx.listener(move |this, _ev, window, cx| {
                    this.start_fresh(id.clone(), window, cx);
                }),
            )
            .child(format!(
                "start fresh as {} (quarantines the corrupt image)",
                identity.name
            ))
    }
}

impl Render for LoginSurface {
    fn render(&mut self, _window: &mut Window, cx: &mut Context<Self>) -> impl IntoElement {
        match self.stage {
            WelcomeStage::Welcome => self.welcome_view(cx).into_any_element(),
            WelcomeStage::Picker => self.picker_view(cx).into_any_element(),
        }
    }
}

/// THE SESSION SHELL — the post-login root view: a thin session bar (the
/// logged-in principal + the **Logout** action) over the full cockpit. It owns
/// the cockpit [`Entity`] so the post-paint seeding/live-pump tasks can drive it,
/// and everything logout needs to (a) revoke the session root and (b) swap the
/// window root back to a fresh [`LoginSurface`].
///
/// This wrapper is the minimal post-login launch piece: it touches NO cockpit
/// internals — it embeds the cockpit entity and adds the session chrome around it.
pub struct SessionShell {
    cockpit: Entity<Cockpit>,
    world: Rc<RefCell<World>>,
    anchors: [dregg_cell::CellId; 3],
    node_url: Option<String>,
    manager: LoginManager,
    #[allow(dead_code)] // identity roster carried alongside the active session
    identities: Vec<DemoIdentity>,
    session: Session,
    identity: DemoIdentity,
    /// The deos image root dir — where the principal's durable session image lives,
    /// so logout can write the REVOKED record into it (SESSION RESUME).
    #[allow(dead_code)] // held for the logout-revoke write into the session image
    base_dir: std::path::PathBuf,
    focus: FocusHandle,
}

impl SessionShell {
    /// Construct the cockpit over the session's world and SWAP the window root to
    /// this shell. Spawns the cockpit's post-paint demo-seeding + live-node pump
    /// tasks (the same ones `run_window` used to spawn around a bare cockpit), now
    /// that the cockpit is the live root.
    #[allow(clippy::too_many_arguments)]
    pub fn open(
        window: &mut Window,
        cx: &mut App,
        world: Rc<RefCell<World>>,
        anchors: [dregg_cell::CellId; 3],
        seed: Option<world::DemoSeed>,
        node_url: Option<String>,
        manager: LoginManager,
        identities: Vec<DemoIdentity>,
        session: Session,
        identity: DemoIdentity,
        base_dir: std::path::PathBuf,
        // FIRST RUN — `true` on a brand-new image (this principal's first login),
        // so the cockpit boots into the calm sparse first-view rather than the full
        // 5-mode wall. A returning owner's wall is familiar (`false`).
        first_run: bool,
    ) {
        let world_for_root = world.clone();
        let node_for_root = node_url.clone();
        let manager_for_root = manager.clone();
        let identities_for_root = identities.clone();
        let session_for_root = session.clone();
        let identity_for_root = identity.clone();
        let base_dir_for_root = base_dir.clone();

        // THE WINDOW-ROOT WELD (docs/deos/COCKPIT-UX.md) — the window root must be a
        // gpui-component `Root`, or any kit text INPUT a surface bears (web-shell URL
        // bar, the editor/composer/agent prompts, …) ABORTS on first paint via
        // `Root::read(window).unwrap()`. So the new root is a `Root` wrapping the
        // `SessionShell`; we stash the inner shell entity (captured out of the builder)
        // for the post-paint seeding / live-node pump tasks below.
        let mut shell_slot: Option<Entity<SessionShell>> = None;
        window.replace_root(cx, |window, cx| {
            // Build the cockpit over the SAME shared world the login provisioned —
            // the session's cap-tree governs what it renders.
            let cockpit = cx.new(|c_cx| {
                let focus = c_cx.focus_handle();
                Cockpit::with_node(
                    world_for_root.clone(),
                    anchors,
                    focus,
                    node_for_root.clone(),
                    seed,
                )
            });
            // FIRST RUN — flip the cockpit into the calm sparse first-view for a
            // brand-new owner (the warm landing, not the wall). One click ("explore"
            // / a cell / "try this") reveals the full frame.
            cockpit.update(cx, |c, _c_cx| c.set_first_run(first_run));
            // THE ROLODEX POSSESSION WIRE — hand the cockpit the LIVE session so
            // the launcher's gadget rolodex partitions Held/Discoverable against
            // the real cap-tree (`Session::reaches` over the live ledger).
            cockpit.update(cx, |c, _c_cx| c.set_session(session_for_root.clone()));
            cockpit.update(cx, |c, c_cx| c.focus_on_open(window, c_cx));

            let session_shell = cx.new(|s_cx| {
                let focus = s_cx.focus_handle();
                SessionShell {
                    cockpit,
                    world: world_for_root,
                    anchors,
                    node_url: node_for_root,
                    manager: manager_for_root,
                    identities: identities_for_root,
                    session: session_for_root,
                    identity: identity_for_root,
                    base_dir: base_dir_for_root,
                    focus,
                }
            });
            shell_slot = Some(session_shell.clone());
            crate::cockpit::root::wrap_root(session_shell, window, cx)
        });
        let shell = shell_slot.expect("the Root builder ran and stashed the shell");

        // THE POST-PAINT SEEDING TASK — drive the demo seed turns one at a time,
        // a beat between each (so each committed turn paints), against the cockpit
        // entity the shell holds. Ends when the image is fully seeded or the shell
        // is gone.
        // WEAK handles so these tasks STOP when the cockpit entity is released
        // (logout swaps the root away → the cockpit drops → `update` errs → break).
        let seeding_cockpit = shell.read(cx).cockpit.downgrade();
        cx.spawn(async move |cx| {
            loop {
                cx.background_executor()
                    .timer(Duration::from_millis(60))
                    .await;
                let more = match seeding_cockpit.update(cx, |c, c_cx| c.seed_next_demo_turn(c_cx)) {
                    Ok(more) => more,
                    // The cockpit entity is gone (logged out / window closed) — stop.
                    Err(_) => break,
                };
                if !more {
                    break;
                }
            }
        })
        .detach();

        // THE LIVE-NODE PUMP — drain a connected node's SSE receipt stream off the
        // async executor (no-op + self-stopping for the embedded-only image).
        let pump_cockpit = shell.read(cx).cockpit.downgrade();
        cx.spawn(async move |cx| loop {
            cx.background_executor()
                .timer(Duration::from_millis(120))
                .await;
            let keep = match pump_cockpit.update(cx, |c, c_cx| c.pump_live(c_cx)) {
                Ok(keep) => keep,
                Err(_) => break,
            };
            if !keep {
                break;
            }
        })
        .detach();

        // THE WORLD-BRIDGE PUMP — drain the cross-process `WorldSink` socket (the
        // `deos_hermes` MCP subprocess's hands on the LIVE World) on the
        // World-owning foreground loop, the same timer idiom as the live-node
        // pump above. Env-gated at construction (`DEOS_WORLD_BRIDGE_SOCKET`): with
        // no bridge bound the first tick returns `false` and the task self-stops
        // (unset ⇒ zero behavior change). A shorter beat than the SSE pump so a
        // bridge round-trip (crawl → fire → receipt) stays snappy for the agent.
        #[cfg(all(feature = "agent-js", unix))]
        {
            let bridge_cockpit = shell.read(cx).cockpit.downgrade();
            cx.spawn(async move |cx| loop {
                cx.background_executor()
                    .timer(Duration::from_millis(50))
                    .await;
                let keep = match bridge_cockpit.update(cx, |c, c_cx| c.pump_world_bridge(c_cx)) {
                    Ok(keep) => keep,
                    Err(_) => break,
                };
                if !keep {
                    break;
                }
            })
            .detach();
        }
    }

    /// LOGOUT — revoke the session root (the whole cap-tree goes dark, synchronous
    /// at `n = 1`) and swap the window root back to a fresh login surface. The
    /// authority simply ceases to exist; there is no stale session to expire.
    fn logout(&mut self, window: &mut Window, cx: &mut Context<Self>) {
        {
            let mut w = self.world.borrow_mut();
            // DURABLE LOGOUT — revoke the cap-tree AND stamp the durable session
            // record REVOKED, so a relaunch does NOT silently resume this session
            // (SESSION RESUME's load-bearing security property). Then flush a
            // checkpoint so the revoked record + the darkened tree are on disk.
            self.manager.logout_durable(&mut w, &self.session);
            w.checkpoint_now();
            // RELEASE THE DURABLE HANDLE — redb is single-writer per file, so the
            // per-user image must be closed before a re-login (same identity) can
            // reopen it. Swap in a fresh ephemeral world; the next `login_as` opens
            // the durable image afresh (which then RESUMES the revoked→re-granted
            // session). The committed history stays on disk; this only drops RAM.
            *w = World::new();
        }
        let world = self.world.clone();
        let anchors = self.anchors;
        let node_url = self.node_url.clone();
        let system_principal = self.manager.system_principal;

        window.replace_root(cx, |window, cx| {
            // THE WINDOW-ROOT WELD — the next root is a `Root` wrapping the fresh
            // login surface (so any kit input the login/relaunched cockpit bears
            // paints without the `Root::read` unwrap-abort).
            let login = cx.new(|l_cx| {
                let focus = l_cx.focus_handle();
                // The image is already seeded from the first session (the world keeps
                // its committed history; logout darkens the session cap-tree, it does
                // not wipe cells). The next login reuses the same system principal.
                LoginSurface {
                    world,
                    anchors,
                    seed: None,
                    node_url,
                    manager: LoginManager::new(system_principal),
                    identities: demo_identities(),
                    focus,
                    message: Some("logged out — the session cap-tree is dark".into()),
                    recovery: None,
                    fresh_offer: None,
                    // A logout returns to the warm front door, not the roster — the
                    // owner is greeted "welcome back", one click from in again.
                    stage: WelcomeStage::Welcome,
                }
            });
            crate::cockpit::root::wrap_root(login, window, cx)
        });
    }
}

impl Render for SessionShell {
    fn render(&mut self, _window: &mut Window, cx: &mut Context<Self>) -> impl IntoElement {
        let who = self.identity.name.to_string();
        let root_short = reflect::short_hex(self.session.root_cell.as_bytes());
        let caps = self.session.granted.len();
        let kind_tag = match self.identity.kind {
            IdentityKind::User => "session",
            IdentityKind::Agent => "agent session",
        };

        div()
            .key_context("Session")
            .track_focus(&self.focus)
            .size_full()
            .flex()
            .flex_col()
            .bg(theme::bg())
            .child(
                // The session bar — who is logged in + the logout action.
                div()
                    .flex()
                    .items_center()
                    .justify_between()
                    .px_3()
                    .py_1()
                    .bg(theme::panel())
                    .border_b_1()
                    .border_color(theme::border())
                    .child(
                        div()
                            .flex()
                            .items_center()
                            .gap_2()
                            .child(crate::views::pill(kind_tag, theme::accent()))
                            .child(
                                div()
                                    .text_xs()
                                    .text_color(theme::text())
                                    .child(format!("{who} · root {root_short} · {caps} caps")),
                            ),
                    )
                    .child(
                        div()
                            .id("logout")
                            .px_2()
                            .py_0p5()
                            .rounded_md()
                            .bg(theme::panel_hi())
                            .text_xs()
                            .text_color(theme::bad())
                            .cursor_pointer()
                            .hover(|s| s.bg(theme::border()))
                            .on_mouse_down(
                                MouseButton::Left,
                                cx.listener(|this, _ev, window, cx| {
                                    this.logout(window, cx);
                                }),
                            )
                            .child("logout"),
                    ),
            )
            // The cockpit fills the rest — the WM renders exactly what the session
            // root cap authorizes.
            .child(div().flex_1().child(self.cockpit.clone()))
    }
}
