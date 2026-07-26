//! **The REAL web surface, driven.**
//!
//! `dreggnet_web::catalog_router` over a real `CatalogState`, called through
//! `tower::ServiceExt::oneshot` — the same no-listener drive every one of the crate's own 55 test
//! files uses. There is no port, and there is also no shortcut: the request goes through the
//! visitor-identity middleware, the game-epoch route authority, the seat lock, and the executor.
//!
//! ## The four hidden fields, and why the driver must scrape them
//!
//! For any spined key — and all three shipped keys are spined — `POST …/act` demands
//! `game_host_incarnation`, `game_session_generation`, `game_expected_pre_head`, and
//! `game_form_token`. A bare `turn=&arg=` is answered `409 invalid game reference` and the
//! executor is never reached. The form token is a keyed MAC under a process-local random key, so
//! the ONLY way to hold one is to read it off the viewer's own live page, which is what a browser
//! does. So `press` re-reads the authority (a live tab) and `stale` replays the authority captured
//! in an earlier frame (a tab left open across a redeploy). Those are different experiments and
//! the driver keeps them different.
//!
//! Nothing here is unreachable: the whole surface is in-process.

use std::path::PathBuf;
use std::sync::Arc;

use axum::Router;
use axum::body::Body;
use axum::http::{Request, StatusCode};
use dreggnet_catalog::{GameEpochLedger, PlayerWorlds};
use dreggnet_web::{CatalogState, catalog_router, demo_host_resumed_from};
use tower::ServiceExt;

use crate::out::{Control, Frame, Paint, PaintHow, pills_in_html, visible_text};
use crate::surface::DrivenSurface;

/// The four route-authority fields a spined game's act form carries.
const AUTHORITY: [&str; 4] = [
    "game_host_incarnation",
    "game_session_generation",
    "game_expected_pre_head",
    "game_form_token",
];

/// The refusals the server answers a POST that presented NO authority at all. A driver that
/// silently ate one would report every later observation as a fact about a turn that never
/// happened, so it is named loudly instead.
const DARK_ACT: [&str; 4] = [
    "missing or malformed game_host_incarnation",
    "missing game_session_generation",
    "missing or malformed 32-byte game_expected_pre_head",
    "missing or malformed game_form_token",
];

/// A frame's control set plus the route authority that was live when it was read.
#[derive(Debug, Clone, Default)]
struct Offered {
    /// `&name=value…` — the authority suffix as of that frame.
    authority: String,
    controls: Vec<Control>,
}

/// The driven web surface.
pub struct WebDriver {
    rt: tokio::runtime::Runtime,
    dir: PathBuf,
    key: String,
    session: String,
    viewer: String,
    app: Option<Router>,
    catalog: Option<Arc<CatalogState>>,
    current: Offered,
    previous: Offered,
    restarts: usize,
}

impl WebDriver {
    /// Build the driver over a durable state directory.
    pub fn new(dir: PathBuf, key: &str, session: &str, viewer: &str) -> Result<Self, String> {
        let rt = tokio::runtime::Builder::new_current_thread()
            .enable_all()
            .build()
            .map_err(|e| format!("cannot build the driver runtime: {e}"))?;
        std::fs::create_dir_all(dir.join("sessions"))
            .map_err(|e| format!("cannot create {}: {e}", dir.join("sessions").display()))?;
        let (app, catalog) = build_app(&dir)?;
        Ok(WebDriver {
            rt,
            dir,
            key: key.to_string(),
            session: session.to_string(),
            viewer: viewer.to_string(),
            app: Some(app),
            catalog: Some(catalog),
            current: Offered::default(),
            previous: Offered::default(),
            restarts: 0,
        })
    }

    fn surface_uri(&self) -> String {
        format!("/offerings/{}/session/{}", self.key, self.session)
    }

    fn act_uri(&self) -> String {
        format!("{}/act", self.surface_uri())
    }

    fn cookie(&self) -> String {
        format!("dregg_user={}", self.viewer)
    }

    fn app(&self) -> Router {
        self.app
            .as_ref()
            .expect("the app is only absent mid-restart")
            .clone()
    }

    fn get(&self, uri: &str) -> (StatusCode, String) {
        let app = self.app();
        let cookie = self.cookie();
        let uri = uri.to_string();
        self.rt.block_on(async move {
            let response = app
                .oneshot(
                    Request::builder()
                        .uri(&uri)
                        .header("cookie", &cookie)
                        .body(Body::empty())
                        .expect("a GET request builds"),
                )
                .await
                .expect("the in-process router answers");
            let status = response.status();
            let bytes = axum::body::to_bytes(response.into_body(), usize::MAX)
                .await
                .unwrap_or_default();
            (status, String::from_utf8_lossy(&bytes).to_string())
        })
    }

    fn post_act(&self, body: String) -> (StatusCode, String) {
        let app = self.app();
        let cookie = self.cookie();
        let uri = self.act_uri();
        self.rt.block_on(async move {
            let response = app
                .oneshot(
                    Request::builder()
                        .method("POST")
                        .uri(&uri)
                        .header("content-type", "application/x-www-form-urlencoded")
                        .header("cookie", &cookie)
                        .body(Body::from(body))
                        .expect("a POST request builds"),
                )
                .await
                .expect("the in-process router answers");
            let status = response.status();
            let bytes = axum::body::to_bytes(response.into_body(), usize::MAX)
                .await
                .unwrap_or_default();
            (status, String::from_utf8_lossy(&bytes).to_string())
        })
    }

    /// The authority suffix read off the viewer's own live page — exactly what their browser
    /// holds. Empty for an unspined offering, whose act route asks for none.
    fn live_authority(&self) -> String {
        let (_, html) = self.get(&self.surface_uri());
        authority_of(&html)
    }

    /// Turn one page into a frame: the visible text, the acts it offers, its pills.
    fn frame_from_page(
        &mut self,
        verb: &str,
        status: StatusCode,
        html: String,
        how: PaintHow,
    ) -> Frame {
        let mut frame = Frame::new(verb);
        frame.paints.push(Paint {
            how,
            body: visible_text(&html),
        });
        frame.pills = pills_in_html(&html);

        let controls = offered_acts(&html);
        let authority = authority_of(&html);
        if controls.iter().any(|c| !c.enabled) {
            frame.note(
                "a `✗` control is rendered disabled — the cap tooth shown, not hidden. The \
                 executor is still the referee, so a raw `act` on it is a real refusal.",
            );
        }
        if authority.is_empty() && dreggnet_catalog::game_kind(&self.key).is_some() {
            frame.note(format!(
                "⚠ this page carries NO route authority for the spined key `{}` — every act \
                 posted from it will be refused before reaching the executor.",
                self.key
            ));
        }
        let offered = Offered {
            authority,
            controls,
        };
        frame.controls = offered.controls.clone();
        self.previous = std::mem::replace(&mut self.current, offered);
        if !status.is_success() {
            frame.note(format!("⚠ HTTP {status}"));
        }
        frame.flag_silence();
        frame
    }

    fn fire(&mut self, verb: &str, turn: &str, arg: i64, authority: String, label: &str) -> Frame {
        let body = format!("turn={turn}&arg={arg}{authority}");
        let (status, html) = self.post_act(body);
        let dark = status == StatusCode::CONFLICT && DARK_ACT.iter().any(|m| html.contains(m));
        // ⚑ The page's OWN answer to this action. `notice_html` puts it in a
        // `<div class="notice …" role="status">` at the very top of the swappable fragment, and it
        // is the only place the surface ever says "Turn committed —" or "Refused: …". Lifting it
        // into REPLY is what makes an act's outcome legible at a glance — and makes its ABSENCE
        // legible too, which is a defect a reader scanning the whole page body would miss.
        let notice = notice_of(&html);
        let mut frame = self.frame_from_page(
            verb,
            status,
            html,
            PaintHow::Fresh(format!("POST {} → {}", self.act_uri(), status)),
        );
        frame.reply = Some(match &notice {
            Some(n) => format!("HTTP {status}\n{n}"),
            None => format!(
                "HTTP {status}\n(the page carried NO `notice` — it does not say what happened)"
            ),
        });
        if notice.is_none() && status.is_success() {
            frame.note(
                "⚠ NO NOTICE ON A 200 — the act returned a normal page that never says whether \
                 the turn landed or was refused. A player cannot tell the difference.",
            );
        }
        frame.note(format!("posted {turn}/{arg} — “{label}”"));
        if authority.is_empty() {
            frame.note("no route authority was attached to this POST.");
        }
        if dark {
            frame.note(
                "⚠⚠ DARK ACT — the POST presented no usable route authority, so the executor was \
                 NEVER REACHED. Nothing after this observed a turn.",
            );
        }
        frame
    }
}

/// Read the four hidden authority fields off a page, as `&name=value…`. Empty if any is absent.
fn authority_of(html: &str) -> String {
    AUTHORITY
        .iter()
        .map(|name| hidden_value(html, name).map(|v| format!("&{name}={v}")))
        .collect::<Option<String>>()
        .unwrap_or_default()
}

/// The surface's own status line — the `<div class="notice …" role="status">…</div>` the act path
/// stamps at the top of the fragment. `None` means the page said nothing about what just happened.
fn notice_of(html: &str) -> Option<String> {
    let (_, rest) = html.split_once("class=\"notice")?;
    let (_, body) = rest.split_once('>')?;
    let (inner, _) = body.split_once("</div>")?;
    let text = visible_text(inner).replace('\n', " ");
    let text = text.split_whitespace().collect::<Vec<_>>().join(" ");
    (!text.is_empty()).then_some(text)
}

fn hidden_value<'a>(html: &'a str, name: &str) -> Option<&'a str> {
    let marker = format!("name=\"{name}\" value=\"");
    Some(html.split_once(&marker)?.1.split_once('"')?.0)
}

/// **Every act a rendered page offers**, in document order — the affordance forms AND the
/// clickable board cells, since a `CoordGrid` square is a real POST form too. Ported from the
/// crate's own test-side reader (`dreggnet-web/tests/common/mod.rs::offered_acts`), which is
/// `#[cfg(test)]`-only and so cannot be imported; the parsing rule is the renderer's, not ours.
fn offered_acts(html: &str) -> Vec<Control> {
    let mut out = Vec::new();
    for chunk in html.split("<form ").skip(1) {
        let form = chunk.split_once("</form>").map(|(f, _)| f).unwrap_or(chunk);
        let Some(turn) = form_attr(form, "turn") else {
            continue;
        };
        let Some(arg) = form_attr(form, "arg").and_then(|a| a.parse::<i64>().ok()) else {
            continue;
        };
        let enabled = !form.contains(" disabled");
        let label = form
            .split_once("<button")
            .and_then(|(_, rest)| rest.split_once('>'))
            .and_then(|(_, rest)| rest.split_once("</button>"))
            .map(|(inner, _)| visible_text(inner).replace('\n', " "))
            .unwrap_or_default();
        let index = out.len();
        out.push(Control {
            index,
            label: label.split_whitespace().collect::<Vec<_>>().join(" "),
            turn: turn.clone(),
            arg,
            enabled,
            wire: format!("turn={turn}&arg={arg}"),
        });
    }
    out
}

fn form_attr(form: &str, name: &str) -> Option<String> {
    let marker = format!("name=\"{name}\" value=\"");
    let (_, rest) = form.split_once(&marker)?;
    let (value, _) = rest.split_once('"')?;
    Some(value.to_string())
}

fn build_app(dir: &PathBuf) -> Result<(Router, Arc<CatalogState>), String> {
    let sessions = dir.join("sessions");
    let epochs = GameEpochLedger::open(dir.join("epochs"))
        .map_err(|e| format!("cannot open the durable game-epoch ledger: {e}"))?;
    let catalog = Arc::new(CatalogState::with_hosts_and_game_epochs(
        move || demo_host_resumed_from(sessions),
        PlayerWorlds::new,
        epochs,
    ));
    Ok((catalog_router(Arc::clone(&catalog)), catalog))
}

impl DrivenSurface for WebDriver {
    fn provenance(&self) -> String {
        format!(
            "web — REAL. `dreggnet_web::catalog_router` over a real `CatalogState` \
             (`demo_host_resumed_from({store})`), driven by `tower::ServiceExt::oneshot`: no \
             listener, no port, but the visitor-identity middleware, the game-epoch route \
             authority, the seat lock and the executor are all on the path. Viewer identity is \
             the `dregg_user` cookie. NOTHING here is unreachable. NOT covered: the wasm \
             `/descent/play` page and the OBS overlay, which are browser-side surfaces.",
            store = self.dir.join("sessions").display()
        )
    }

    fn open(&mut self) -> Frame {
        let uri = self.surface_uri();
        let (status, html) = self.get(&uri);
        let mut frame = self.frame_from_page(
            "open",
            status,
            html,
            PaintHow::Read(format!("GET {uri} → {status}")),
        );
        frame.note("a GET on the play surface opens the session lazily — this IS the open.");
        frame
    }

    fn again(&mut self) -> Frame {
        let uri = self.surface_uri();
        let (status, html) = self.get(&uri);
        self.frame_from_page(
            "again",
            status,
            html,
            PaintHow::Read(format!("GET {uri} → {status}")),
        )
    }

    fn press(&mut self, index: usize) -> Frame {
        let Some(control) = self.current.controls.get(index).cloned() else {
            return Frame::driver_note(
                "press",
                format!(
                    "no control at index {index} — {} on offer.",
                    self.current.controls.len()
                ),
            );
        };
        // A live browser re-reads the authority off the page it is submitting from.
        let authority = self.live_authority();
        let mut frame = self.fire(
            "press",
            &control.turn,
            control.arg,
            authority,
            &control.label,
        );
        if !control.enabled {
            frame.note("this control was rendered DISABLED — a refusal is the correct outcome.");
        }
        frame
    }

    fn press_stale(&mut self, index: usize) -> Frame {
        let from = self.previous.clone();
        let Some(control) = from.controls.get(index).cloned() else {
            return Frame::driver_note("stale", "no previous frame to press from yet.");
        };
        let mut frame = self.fire(
            "stale",
            &control.turn,
            control.arg,
            from.authority.clone(),
            &control.label,
        );
        frame.note(
            "this replayed the PREVIOUS frame's control AND its captured route authority — a tab \
             left open. A refusal here must name what to do; a silent 409 is a dead page.",
        );
        frame
    }

    fn act(&mut self, turn: &str, arg: i64) -> Frame {
        let authority = self.live_authority();
        self.fire("act", turn, arg, authority, "(raw)")
    }

    fn send(&mut self, text: &str) -> Frame {
        Frame::driver_note(
            "send",
            format!(
                "the web surface has no free-text channel: `{text}` has nowhere to go. Every \
                 input is a form POST — use `act <turn> <arg>` or `press <n>`. (This is itself \
                 a cross-surface asymmetry worth noting: a chat surface routes prose, this one \
                 cannot, so any offering whose affordance sets `wants_text` has no web path here.)"
            ),
        )
    }

    fn become_viewer(&mut self, who: &str) -> Frame {
        let was = std::mem::replace(&mut self.viewer, who.to_string());
        let mut frame = Frame::new("as");
        frame.controls = self.current.controls.clone();
        frame.note(format!(
            "viewer {was} → {who} (cookie `dregg_user={who}`). NO state was touched — same \
             session, same durable log. Re-request with `again` to see their projection."
        ));
        frame
    }

    fn restart(&mut self) -> Frame {
        let on_screen = self.current.clone();
        // Drop the router AND the state: the host thread and the durable ledger both go with it,
        // exactly as a redeploy tears them down.
        self.app = None;
        self.catalog = None;
        match build_app(&self.dir) {
            Ok((app, catalog)) => {
                self.app = Some(app);
                self.catalog = Some(catalog);
                self.restarts += 1;
                self.current = on_screen.clone();
                self.previous = Offered::default();
                let mut frame = Frame::new("restart");
                frame.controls = on_screen.controls.clone();
                frame.note(format!(
                    "RESTART #{n}: the router, the host thread and the epoch ledger were dropped \
                     and rebuilt from {store}. The viewer's open TAB still shows the {c} \
                     control(s) above, with the authority it was served — `stale <n>` presses one \
                     with THAT authority, `press <n>` re-reads a fresh one.",
                    n = self.restarts,
                    store = self.dir.join("sessions").display(),
                    c = on_screen.controls.len()
                ));
                // A stale press after a restart is the whole point, so keep the pre-restart
                // authority reachable as `previous`.
                self.previous = on_screen;
                frame
            }
            Err(why) => Frame::driver_note("restart", format!("could not rebuild the app: {why}")),
        }
    }

    fn verify(&mut self) -> Frame {
        let uri = format!("{}/verify", self.surface_uri());
        let (status, body) = self.get(&uri);
        let mut frame = Frame::new("verify");
        frame.reply = Some(format!("HTTP {status}\n{}", body.trim()));
        frame.controls = self.current.controls.clone();
        frame.note(format!(
            "GET {uri} — the offering's own replay re-verifier."
        ));
        frame
    }

    fn controls(&self) -> Vec<Control> {
        self.current.controls.clone()
    }

    fn viewer(&self) -> String {
        self.viewer.clone()
    }
}
