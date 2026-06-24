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
    DemoIdentity, IdentityKind, LoginManager, LoginOutcome, Session,
};
use starbridge_v2::world::{self, World};

/// The LOGIN SURFACE — the boot front door. Holds everything the post-login
/// transition needs to construct the cockpit (the shared world, the anchors, the
/// pending demo-seed plan, the optional live-node URL), the [`LoginManager`] (the
/// trusted session cell over the image's system principal), and the identity
/// roster the picker shows. A failed/refused login leaves an in-surface message.
pub struct LoginSurface {
    world: Rc<RefCell<World>>,
    anchors: [dregg_cell::CellId; 3],
    seed: Option<world::DemoSeed>,
    node_url: Option<String>,
    manager: LoginManager,
    identities: Vec<DemoIdentity>,
    focus: FocusHandle,
    /// The last refusal/error to show under the picker (the in-band "denied").
    message: Option<String>,
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
        }
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
        // on a relaunch `World::open` recovers the exact cell graph + balances +
        // history. The shared `Rc<RefCell<World>>` the cockpit renders is swapped
        // to it, so the cockpit renders the resumed image.
        let base_dir = session_base_dir();
        // The demo / desktop image meters free (matching `World::new`), so the
        // per-user durable image opens under the same zero-cost model (the receipts
        // re-derive bit-identically only under the cost model the image was made
        // with — zero here, the demo desktop's).
        let costs = dregg_turn::ComputronCosts::zero();
        let (mut user_world, anchors, manager, fresh) =
            match open_session_world(&base_dir, &principal, costs) {
                Ok(t) => t,
                Err(e) => {
                    self.message = Some(format!("could not open your durable image: {e}"));
                    cx.notify();
                    return;
                }
            };

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

        SessionShell::open(
            window, cx, world, anchors, seed, node_url, manager, identities, session, identity,
            base_dir,
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

impl Render for LoginSurface {
    fn render(&mut self, _window: &mut Window, cx: &mut Context<Self>) -> impl IntoElement {
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
    identities: Vec<DemoIdentity>,
    session: Session,
    identity: DemoIdentity,
    /// The deos image root dir — where the principal's durable session image lives,
    /// so logout can write the REVOKED record into it (SESSION RESUME).
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
