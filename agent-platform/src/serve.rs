//! Serve the AgentPlatform over HTTP — rent, drive, watch, share, and verify a
//! grain over the mesh. The agent twin of the webcell platform's control endpoint:
//! a `POST` to `control_host` `/rent` provisions a confined agent grain, then per
//! grain host, gated fail-closed by the caller's role on the grain (owner = Admin;
//! a non-member 404s — no existence oracle):
//!
//! | route                    | method   | role required        |
//! |--------------------------|----------|----------------------|
//! | `/drive`                 | POST     | Driver+ (spends)     |
//! | `/transcript`            | GET/POST | Viewer+ (SSE watch)  |
//! | `/verify` (`?r2`) · `/attest` | GET | Viewer+ (read)       |
//! | `/checkpoint` (offer)    | GET      | Viewer+              |
//! | `/checkpoint` (submit)   | POST     | Admin (R1)           |
//! | `/share` · `/unshare`    | POST     | Admin                |
//! | `/clock` (control host)  | POST     | the configured operator subject |
//!
//! `/transcript` streams the drive as an SSE `text/event-stream` (meta/step/done,
//! see [`crate::transcript`]); `/drive` needs a live model (`--features live-brain`
//! + a key). Roles are the [`crate::share`] facet lattice, keyed on the verified
//! `X-Dregg-Subject`.
//!
//! `POST control_host /clock` is how the block height REACHES a served platform
//! (without it, `drive`'s rent-schedule audit runs against a clock frozen at 0 and
//! no grain ever lapses — free hosting forever). It is operator-only: refused
//! entirely (404) when no operator subject is configured, and gated on the
//! verified `X-Dregg-Subject` equaling the configured operator. The platform
//! clock is monotone ([`AgentPlatform::set_clock`]) — a regression is ignored.

use std::path::{Path, PathBuf};
use std::sync::Arc;

use dregg_cell::CellId;
use hosted_lease::LeaseTerms;
use http_serve::{HttpMethod, ServeRequest, WebResponse as HttpResponse, serve_http};
use serde::Deserialize;

use crate::AgentPlatform;

/// A remote request to rent an agent grain (POSTed to the control endpoint). The
/// grain runs as — and is owned by — the caller's verified `X-Dregg-Subject`, not
/// any body-supplied account (which would be forgeable).
#[derive(Debug, Clone, Deserialize)]
pub struct RentRequest {
    /// The grain's host, e.g. `alice.agents.dregg`.
    pub host: String,
    /// The cap bundle (hosted-safe — a raw `shell` is refused), e.g. `"fs"`.
    pub caps: String,
    /// The grain's spend budget.
    pub budget: i64,
    /// Rent owed per period.
    pub rent_per_period: u64,
    /// Period length in blocks.
    pub period: i64,
    /// **R1** — the renter's genesis nonce (hex, 32 bytes), pinned into the grain so
    /// the renter recognizes their own session in every attestation. Optional; when
    /// absent the grain is tamper-evident only (no R1).
    #[serde(default)]
    pub renter_nonce: Option<String>,
    /// **R1** — the renter's ed25519 pubkey (hex, 32 bytes) the platform pins
    /// checkpoint countersignatures against. Optional; required for the
    /// `/checkpoint` protocol.
    #[serde(default)]
    pub renter_pubkey: Option<String>,
}

/// A remote request to drive a grain (POSTed to the grain's host).
#[derive(Debug, Clone, Deserialize)]
pub struct DriveRequest {
    /// The natural-language goal for the live model.
    pub goal: String,
    /// The grain's granted tool names the model may call (a subset of its caps).
    #[serde(default)]
    pub tools: Vec<String>,
}

/// **BYOK — a remote request to take ONE proposed action on a grain** (POSTed to
/// the grain's host). This is the seam that lets the model run in the RENTER's
/// browser under the RENTER's own API key: the browser proposes a single tool
/// call, and only THIS — never the key — reaches the host, which cap-gates,
/// meters, mints, and receipts it exactly like a host-driven action. The host
/// executes the action (it holds the workdir) and sees the proposed action + its
/// result; it never sees the model or the key.
#[derive(Debug, Clone, Deserialize)]
pub struct ActRequest {
    /// The operator tool the model proposed (`fs_write`, `fs_read`, `list_dir`,
    /// `mkdir`, … — one of [`dregg_agent::agent::op`]). Cap-gated per resource; a
    /// tool outside the grain's caps is honestly `cap_refused`, not an error.
    pub tool: String,
    /// The tool's string arguments (`path`/`content` for fs, etc.), the exact arg
    /// keys [`dregg_agent::agent::ToolCall`] expects.
    #[serde(default)]
    pub args: std::collections::BTreeMap<String, String>,
    /// An optional goal label for the transcript (defaults to `byok:<tool>`).
    #[serde(default)]
    pub goal: Option<String>,
}

/// A remote request to share a grain (POSTed to the grain's host by an Admin).
#[derive(Debug, Clone, Deserialize)]
pub struct ShareRequest {
    /// The verified subject to grant a role to (a `dga1_`/webauth account id).
    pub subject: String,
    /// The role name (`viewer` / `driver` / `admin`; an unknown role is refused).
    pub role: String,
}

/// A remote request to revoke a grain share (POSTed by an Admin).
#[derive(Debug, Clone, Deserialize)]
pub struct UnshareRequest {
    /// The subject whose share is revoked.
    pub subject: String,
}

/// A remote clock tick (POSTed to the control endpoint by the operator): the
/// current block height from the node, which `drive`'s rent-schedule audit runs
/// against. Monotone on apply — a regression is ignored.
#[derive(Debug, Clone, Deserialize)]
pub struct ClockRequest {
    /// The current block height.
    pub block: i64,
}

impl AgentPlatform {
    /// Dispatch one request: `POST control_host /rent` provisions a grain (deriving
    /// its lease cell from the host, billed to `provider`/`asset`, workdir under
    /// `workdir_base`); `POST control_host /clock` ticks the block height (only
    /// when `operator` is configured AND the verified subject IS the operator);
    /// `POST <grain-host> /drive` runs a goal on it; `GET <grain-host> /verify`
    /// re-witnesses it. The self-serve front door.
    pub fn handle_request(
        &self,
        control_host: &str,
        provider: CellId,
        asset: CellId,
        workdir_base: &Path,
        operator: Option<&str>,
        req: &ServeRequest,
    ) -> HttpResponse {
        // The browser driver page, served same-origin so its `fetch`/`EventSource`
        // calls reach this very server with no CORS. Host-independent + public (a
        // page, like the marketing site); the API routes below still gate on the
        // verified subject. Placed before the shim + auth so `/` is never a grain
        // route (grains expose no `/`).
        if req.method == HttpMethod::Get {
            let p = req.target.split('?').next().unwrap_or(&req.target);
            if matches!(p, "/" | "/grain" | "/grain/" | "/index.html") {
                return HttpResponse {
                    status: 200,
                    content_type: "text/html; charset=utf-8".to_string(),
                    body: GRAIN_PAGE.as_bytes().to_vec(),
                };
            }
        }

        // Apply the browser-friendly routing shim: a browser cannot set the `Host`
        // header from `fetch`/`EventSource`, so the effective grain-host (and, for
        // header-less `EventSource`, the subject) may arrive from a browser-settable
        // source. Falls back to the real `Host` header, so existing programmatic
        // callers are byte-for-byte untouched (the shim returns `None`).
        let shimmed;
        let req = match resolve_browser_shim(req) {
            Some(r) => {
                shimmed = r;
                &shimmed
            }
            None => req,
        };

        let path = req.target.split('?').next().unwrap_or(&req.target);
        let query = req.target.split('?').nth(1).unwrap_or("");

        // The operator's clock tick — how the block height reaches a served
        // platform, so delinquent grains actually lapse. Fail-closed: with no
        // operator configured the route does not exist (404); a non-operator
        // subject is refused (403); the tick itself is monotone.
        if req.host == control_host && req.method == HttpMethod::Post && path == "/clock" {
            let Some(operator) = operator else {
                return HttpResponse::error(404, format!("no route for {} {}", req.method, path));
            };
            let Some(subject) = req.header("x-dregg-subject") else {
                return HttpResponse::error(
                    401,
                    "ticking the clock requires a verified X-Dregg-Subject",
                );
            };
            if subject != operator {
                return HttpResponse::error(403, "ticking the clock requires the operator subject");
            }
            let spec: ClockRequest = match serde_json::from_slice(&req.body) {
                Ok(s) => s,
                Err(e) => return HttpResponse::error(400, format!("bad clock request: {e}")),
            };
            let effective = self.set_clock(spec.block);
            return HttpResponse::json(format!("{{\"clock\":{effective}}}").into_bytes());
        }

        if req.host == control_host && req.method == HttpMethod::Post && path == "/rent" {
            // The grain is owned by the VERIFIED subject (a proxy-set, duplicate-safe
            // header), never a body-supplied account.
            let Some(subject) = req.header("x-dregg-subject").map(str::to_string) else {
                return HttpResponse::error(401, "renting requires a verified X-Dregg-Subject");
            };
            let spec: RentRequest = match serde_json::from_slice(&req.body) {
                Ok(s) => s,
                Err(e) => return HttpResponse::error(400, format!("bad rent request: {e}")),
            };
            // The control endpoint is not rentable: a grain occupying the control
            // host would shadow-confuse the platform's own routes.
            if spec.host == control_host {
                return HttpResponse::error(400, "the control host is not rentable");
            }
            let lease_cell = CellId::from_bytes(*blake3::hash(spec.host.as_bytes()).as_bytes());
            // First rent falls due one period out from the CURRENT clock — a grace
            // window so a freshly-rented grain is never instantly "behind" (which,
            // with drive's schedule audit, would lapse it on its first drive).
            let terms = LeaseTerms::new(
                provider,
                lease_cell,
                asset,
                spec.rent_per_period,
                spec.period,
                self.clock() + spec.period.max(1),
                0,
            );
            let workdir = workdir_base.join(sanitize(&spec.host));
            if std::fs::create_dir_all(&workdir).is_err() {
                return HttpResponse::error(500, "could not create grain workdir");
            }
            // R1: parse the optional renter anchor (hex → 32 bytes). A malformed hex
            // is a client error, not a silent drop — and the anchor is BOTH fields
            // or NEITHER (`RenterAnchor` is whole on purpose: the R1 teeth need the
            // nonce AND the countersign key; half an anchor would read as anchored
            // while conferring nothing).
            let anchor = match (spec.renter_nonce.as_deref(), spec.renter_pubkey.as_deref()) {
                (None, None) => None,
                (Some(n), Some(k)) => {
                    let nonce = match parse_hex32(n) {
                        Ok(v) => v,
                        Err(e) => {
                            return HttpResponse::error(400, format!("bad renter_nonce: {e}"));
                        }
                    };
                    let pubkey = match parse_hex32(k) {
                        Ok(v) => v,
                        Err(e) => {
                            return HttpResponse::error(400, format!("bad renter_pubkey: {e}"));
                        }
                    };
                    Some(crate::RenterAnchor { nonce, pubkey })
                }
                _ => {
                    return HttpResponse::error(
                        400,
                        "the R1 renter anchor is renter_nonce AND renter_pubkey together (or neither)",
                    );
                }
            };
            return match self.rent(
                &spec.host,
                &subject,
                &spec.caps,
                spec.budget,
                workdir.to_str().unwrap_or("."),
                terms,
                anchor,
            ) {
                Ok(host) => HttpResponse::json(
                    format!("{{\"endpoint\":\"{host}\",\"owner\":\"{subject}\"}}").into_bytes(),
                ),
                Err(crate::AgentPlatformError::GrainOccupied(_)) => {
                    HttpResponse::error(409, "a grain is already hosted at that host")
                }
                Err(crate::AgentPlatformError::BadTerms(e)) => HttpResponse::error(400, e),
                Err(e) => HttpResponse::error(500, e.to_string()),
            };
        }

        if req.method == HttpMethod::Post && path == "/drive" {
            // Driver-or-higher may drive (spend the grain's budget + key). A member
            // Viewer gets 403; a non-member 404s (no existence oracle).
            let role = match self.authorize(req) {
                Ok((_, r)) => r,
                Err(resp) => return resp,
            };
            if !role.can_drive() {
                return HttpResponse::error(403, "driving this grain requires the driver role");
            }
            let spec: DriveRequest = match serde_json::from_slice(&req.body) {
                Ok(s) => s,
                Err(e) => return HttpResponse::error(400, format!("bad drive request: {e}")),
            };
            return self.drive_over_http(&req.host, spec);
        }

        // **BYOK — POST /act: cap-gate + meter + mint + receipt ONE proposed
        // action.** Same Driver+ gate as `/drive` (it spends): a Viewer 403s, a
        // non-member 404s. The model that PROPOSED this action ran in the renter's
        // browser under the renter's own key — the host never sees the key, only the
        // single action it now gates. NO host LLM key needed, so this path works on a
        // stock build (unlike `/drive`).
        if req.method == HttpMethod::Post && path == "/act" {
            let role = match self.authorize(req) {
                Ok((_, r)) => r,
                Err(resp) => return resp,
            };
            if !role.can_drive() {
                return HttpResponse::error(403, "acting on this grain requires the driver role");
            }
            let spec: ActRequest = match serde_json::from_slice(&req.body) {
                Ok(s) => s,
                Err(e) => return HttpResponse::error(400, format!("bad act request: {e}")),
            };
            return self.act_over_http(&req.host, spec);
        }

        // The live drive transcript — any member (Viewer+) may WATCH the grain work:
        // an SSE `text/event-stream` of meta/step/done frames. GET or POST.
        if (req.method == HttpMethod::Get || req.method == HttpMethod::Post)
            && path == "/transcript"
        {
            let _role = match self.authorize(req) {
                Ok((_, r)) => r, // membership (can_read) is implied by being a member
                Err(resp) => return resp,
            };
            return match self.transcript(&req.host) {
                Ok(sse) => HttpResponse {
                    status: 200,
                    content_type: "text/event-stream".to_string(),
                    body: sse.into_bytes(),
                },
                Err(crate::AgentPlatformError::NoSuchGrain(_)) => {
                    HttpResponse::error(404, "no grain hosted here")
                }
                Err(e) => HttpResponse::error(500, e.to_string()),
            };
        }

        // Share / unshare the grain — owner or Admin only.
        if req.method == HttpMethod::Post && path == "/share" {
            let (caller, role) = match self.authorize(req) {
                Ok(pair) => pair,
                Err(resp) => return resp,
            };
            if !role.can_admin() {
                return HttpResponse::error(403, "sharing this grain requires the admin role");
            }
            let spec: ShareRequest = match serde_json::from_slice(&req.body) {
                Ok(s) => s,
                Err(e) => return HttpResponse::error(400, format!("bad share request: {e}")),
            };
            // An unknown role name confers nothing — reject it, never silently default.
            let Some(new_role) = crate::Role::parse(&spec.role) else {
                return HttpResponse::error(400, format!("unknown role `{}`", spec.role));
            };
            return match self.share(&req.host, &caller, &spec.subject, new_role) {
                Ok(()) => HttpResponse::json(
                    format!(
                        "{{\"shared\":\"{}\",\"role\":\"{}\"}}",
                        spec.subject,
                        new_role.as_str()
                    )
                    .into_bytes(),
                ),
                Err(crate::AgentPlatformError::Unauthorized(_)) => {
                    HttpResponse::error(403, "sharing this grain requires the admin role")
                }
                Err(crate::AgentPlatformError::NoSuchGrain(_)) => {
                    HttpResponse::error(404, "no grain hosted here")
                }
                Err(e) => HttpResponse::error(500, e.to_string()),
            };
        }

        if req.method == HttpMethod::Post && path == "/unshare" {
            let (caller, role) = match self.authorize(req) {
                Ok(pair) => pair,
                Err(resp) => return resp,
            };
            if !role.can_admin() {
                return HttpResponse::error(403, "unsharing this grain requires the admin role");
            }
            let spec: UnshareRequest = match serde_json::from_slice(&req.body) {
                Ok(s) => s,
                Err(e) => return HttpResponse::error(400, format!("bad unshare request: {e}")),
            };
            return match self.unshare(&req.host, &caller, &spec.subject) {
                Ok(()) => HttpResponse::json(
                    format!("{{\"unshared\":\"{}\"}}", spec.subject).into_bytes(),
                ),
                Err(crate::AgentPlatformError::Unauthorized(_)) => {
                    HttpResponse::error(403, "unsharing this grain requires the admin role")
                }
                Err(crate::AgentPlatformError::NoSuchGrain(_)) => {
                    HttpResponse::error(404, "no grain hosted here")
                }
                Err(e) => HttpResponse::error(500, e.to_string()),
            };
        }

        // R1 — the renter finality anchor's countersign protocol.
        if path == "/checkpoint" {
            // GET: hand a member the current (head_root, num_turns) to countersign.
            if req.method == HttpMethod::Get {
                if let Err(resp) = self.authorize(req) {
                    return resp;
                }
                return match self.checkpoint_offer(&req.host) {
                    Ok(cp) => match serde_json::to_vec(&cp) {
                        Ok(body) => HttpResponse::json(body),
                        Err(e) => HttpResponse::error(500, format!("checkpoint encode: {e}")),
                    },
                    Err(crate::AgentPlatformError::NoSuchGrain(_)) => {
                        HttpResponse::error(404, "no grain hosted here")
                    }
                    Err(crate::AgentPlatformError::Checkpoint(e)) => HttpResponse::error(409, e),
                    Err(e) => HttpResponse::error(500, e.to_string()),
                };
            }
            // POST: accept + store the renter's countersignature (owner/Admin only).
            if req.method == HttpMethod::Post {
                let role = match self.authorize(req) {
                    Ok((_, r)) => r,
                    Err(resp) => return resp,
                };
                if !role.can_admin() {
                    return HttpResponse::error(
                        403,
                        "countersigning this grain requires the admin role",
                    );
                }
                let cs: grain_verify::CountersignedCheckpoint =
                    match serde_json::from_slice(&req.body) {
                        Ok(c) => c,
                        Err(e) => {
                            return HttpResponse::error(
                                400,
                                format!("bad countersigned checkpoint: {e}"),
                            );
                        }
                    };
                return match self.submit_checkpoint(&req.host, cs) {
                    Ok(()) => HttpResponse::json(b"{\"stored\":true}".to_vec()),
                    Err(crate::AgentPlatformError::NoSuchGrain(_)) => {
                        HttpResponse::error(404, "no grain hosted here")
                    }
                    Err(crate::AgentPlatformError::Checkpoint(e)) => HttpResponse::error(422, e),
                    Err(e) => HttpResponse::error(500, e.to_string()),
                };
            }
        }

        if req.method == HttpMethod::Get && path == "/attest" {
            // Readable by any member (Viewer+); a non-member 404s.
            if let Err(resp) = self.authorize(req) {
                return resp;
            }
            return match self.attest(&req.host) {
                Ok(att) => match serde_json::to_vec(&att) {
                    Ok(body) => HttpResponse::json(body),
                    Err(e) => HttpResponse::error(500, format!("attestation encode: {e}")),
                },
                Err(crate::AgentPlatformError::NoSuchGrain(_)) => {
                    HttpResponse::error(404, "no grain hosted here")
                }
                Err(e) => HttpResponse::error(500, e.to_string()),
            };
        }

        if req.method == HttpMethod::Get && path == "/verify" {
            // Readable by any member (Viewer+); a non-member 404s.
            if let Err(resp) = self.authorize(req) {
                return resp;
            }
            // `?r2` — the R2 rung: every receipt must be a view over a kernel turn
            // the platform's minter committed. A grain driven unminted honestly
            // FAILS this (422); plain /verify is the R0 tamper-evidence rung.
            if query
                .split('&')
                .any(|kv| kv == "r2" || kv.starts_with("r2="))
            {
                return match self.verify_r2(&req.host) {
                    Ok(v) => HttpResponse::json(
                        format!(
                            "{{\"verified\":true,\"rung\":\"r2\",\"actions\":{},\"linked\":{}}}",
                            v.base.actions, v.linked
                        )
                        .into_bytes(),
                    ),
                    Err(crate::AgentPlatformError::NoSuchGrain(_)) => {
                        HttpResponse::error(404, "no grain hosted here")
                    }
                    Err(e) => HttpResponse::error(422, e.to_string()),
                };
            }
            return match self.verify(&req.host) {
                Ok(v) => HttpResponse::json(
                    format!("{{\"verified\":true,\"actions\":{}}}", v.actions).into_bytes(),
                ),
                Err(crate::AgentPlatformError::NoSuchGrain(_)) => {
                    HttpResponse::error(404, "no grain hosted here")
                }
                Err(e) => HttpResponse::error(422, e.to_string()),
            };
        }

        HttpResponse::error(404, format!("no route for {} {}", req.method, path))
    }

    /// Resolve the caller's role on the grain named by `req.host`, fail-closed: a
    /// missing `X-Dregg-Subject` is a `401`; a non-member — or no grain here — is a
    /// `404` (no existence oracle: a grain that is not yours reads the same as a
    /// grain that is not there). `Ok((subject, role))` for a member.
    fn authorize(&self, req: &ServeRequest) -> Result<(String, crate::Role), HttpResponse> {
        let Some(subject) = req.header("x-dregg-subject") else {
            return Err(HttpResponse::error(
                401,
                "this route requires a verified X-Dregg-Subject",
            ));
        };
        match self.role_of(&req.host, subject) {
            Some(role) => Ok((subject.to_string(), role)),
            None => Err(HttpResponse::error(404, "no grain hosted here")),
        }
    }

    /// Run a driven goal and shape the HTTP reply. Requires the live brain.
    #[cfg(feature = "live-brain")]
    fn drive_over_http(&self, host: &str, spec: DriveRequest) -> HttpResponse {
        match self.drive_live(host, spec.goal, &spec.tools) {
            Ok(r) => HttpResponse::json(
                format!(
                    "{{\"admitted\":{},\"cap_refused\":{},\"budget_refused\":{},\"consumed\":{}}}",
                    r.admitted, r.cap_refused, r.budget_refused, r.consumed
                )
                .into_bytes(),
            ),
            Err(crate::AgentPlatformError::Lapsed) => {
                HttpResponse::error(402, "the hosting lease has lapsed: grain reclaimed")
            }
            Err(crate::AgentPlatformError::NoSuchGrain(_)) => {
                HttpResponse::error(404, "no grain hosted here")
            }
            Err(e) => HttpResponse::error(500, e.to_string()),
        }
    }

    /// Without the live brain, driving over HTTP is unavailable — a goal needs a
    /// model, and the hermetic default has only the recorded `PlannedBrain`.
    #[cfg(not(feature = "live-brain"))]
    fn drive_over_http(&self, _host: &str, _spec: DriveRequest) -> HttpResponse {
        HttpResponse::error(
            503,
            "no live brain: rebuild the platform with --features live-brain and set an LLM key",
        )
    }

    /// **BYOK — mint ONE renter-proposed action and shape the HTTP reply.** Wrap the
    /// single proposed tool call in a ONE-SHOT [`PlannedBrain`] (exactly this action
    /// at step 0, then `None`) and hand it to the EXISTING
    /// [`drive_serving`](AgentPlatform::drive_serving) — so the whole cap-gate / meter
    /// / mint / receipt path runs UNCHANGED, with zero new trust surface and no
    /// bypass. A cap- or budget-refused action comes back HONESTLY (`cap_refused` /
    /// `budget_refused` counted, `admitted:0`), never a 4xx/5xx error — the model
    /// proposed, the capabilities disposed. On success the reply mirrors `/attest`'s
    /// receipt view (the last committed receipt: seq / action / cost / consumed_after
    /// / cell_root). No host LLM key is ever consulted on this path.
    fn act_over_http(&self, host: &str, spec: ActRequest) -> HttpResponse {
        use dregg_agent::agent::{AgentAction, PlannedBrain, ToolCall};
        let goal = spec
            .goal
            .clone()
            .unwrap_or_else(|| format!("byok:{}", spec.tool));
        let action = AgentAction::Op(ToolCall::new(spec.tool, spec.args));
        let mut brain = PlannedBrain::new(vec![action]);
        match self.drive_serving(host, goal, &mut brain) {
            Ok(report) => {
                // The last committed receipt is THIS action when it was admitted (the
                // minted receipt is appended); on a refusal it is the grain's prior
                // tip (or `null` on a fresh grain) — the honest reflection of state.
                let last = self
                    .attest(host)
                    .ok()
                    .and_then(|a| a.report.receipts.last().cloned());
                HttpResponse::json(act_response_json(&report, last.as_ref()))
            }
            Err(crate::AgentPlatformError::Lapsed) => {
                HttpResponse::error(402, "the hosting lease has lapsed: grain reclaimed")
            }
            Err(crate::AgentPlatformError::NoSuchGrain(_)) => {
                HttpResponse::error(404, "no grain hosted here")
            }
            Err(e) => HttpResponse::error(500, e.to_string()),
        }
    }
}

/// Shape the `/act` reply: the goal's admit/refuse counts + running meter, plus the
/// last committed receipt as a `/attest`-mirroring view (seq / action / cost /
/// consumed_after / cell_root), or `null` when the grain has committed nothing.
fn act_response_json(
    report: &dregg_agent::session::GoalReport,
    receipt: Option<&dregg_agent::agent::AgentReceipt>,
) -> Vec<u8> {
    let receipt_json = match receipt {
        Some(r) => format!(
            "{{\"seq\":{},\"action\":{},\"cost\":{},\"consumed_after\":{},\"cell_root\":\"{}\"}}",
            r.seq,
            serde_json::to_string(&r.action).unwrap_or_else(|_| "\"\"".to_string()),
            r.cost,
            r.consumed_after,
            hex32_str(&r.cell_root),
        ),
        None => "null".to_string(),
    };
    format!(
        "{{\"admitted\":{},\"cap_refused\":{},\"budget_refused\":{},\"consumed\":{},\"receipt\":{}}}",
        report.admitted, report.cap_refused, report.budget_refused, report.consumed, receipt_json
    )
    .into_bytes()
}

/// Lowercase hex of a 32-byte commitment (the receipt's `cell_root` on the wire).
fn hex32_str(b: &[u8; 32]) -> String {
    let mut s = String::with_capacity(64);
    for x in b {
        s.push_str(&format!("{x:02x}"));
    }
    s
}

/// Parse a 64-char hex string into 32 bytes (for the R1 renter nonce / pubkey on
/// the wire). Fail-closed on any non-hex or wrong length.
fn parse_hex32(s: &str) -> Result<[u8; 32], String> {
    let s = s.strip_prefix("0x").unwrap_or(s);
    if s.len() != 64 {
        return Err(format!("expected 64 hex chars, got {}", s.len()));
    }
    let mut out = [0u8; 32];
    for (i, b) in out.iter_mut().enumerate() {
        *b = u8::from_str_radix(&s[i * 2..i * 2 + 2], 16).map_err(|e| e.to_string())?;
    }
    Ok(out)
}

/// The self-contained browser driver page, served same-origin at `GET /`. Editing
/// `site/grain/index.html` reshapes it; it is compiled in so a deployed bin needs no
/// sidecar files.
const GRAIN_PAGE: &str = include_str!("../../site/grain/index.html");

/// **The browser-friendly routing shim.** A browser cannot set the HTTP `Host`
/// header from `fetch`/`EventSource`, and `EventSource` cannot set request headers at
/// all — so the effective grain-host (and, for SSE, the subject) may arrive from a
/// browser-settable source, with the programmatic `Host`-header form left as the
/// fallback:
///
/// - **the grain-host** — the `X-Dregg-Grain-Host` header, else the `host` query
///   param, else the real `Host` header (existing programmatic callers untouched);
/// - **the subject** — SSE convenience *only*, since `EventSource` sets no headers:
///   the `X-Dregg-Subject` header stays primary and duplicate-safe; a `subject` query
///   param is injected ONLY when NO `x-dregg-subject` header is present at all (a
///   duplicated/ambiguous header still fails closed to `None`, never to the query).
///
/// This widens only the grain-HOST *source*; it never weakens auth — the subject is
/// still whatever the caller supplies, role gating is unchanged, and a browser naming
/// a grain it is not a member of still `404`s (no existence oracle). Returns `None`
/// when no browser shim is in play, so the programmatic path is byte-identical.
fn resolve_browser_shim(req: &ServeRequest) -> Option<ServeRequest> {
    let hdr_host = req.header("x-dregg-grain-host").map(str::to_string);

    let query = req.target.split('?').nth(1).unwrap_or("");
    let mut q_host: Option<String> = None;
    let mut q_subject: Option<String> = None;
    for pair in query.split('&').filter(|s| !s.is_empty()) {
        let (k, v) = pair.split_once('=').unwrap_or((pair, ""));
        match k {
            "host" if q_host.is_none() => q_host = Some(v.to_string()),
            "subject" if q_subject.is_none() => q_subject = Some(v.to_string()),
            _ => {}
        }
    }

    let eff_host = hdr_host.or(q_host);
    // Inject the query subject ONLY when no x-dregg-subject header appears at all —
    // a present-but-duplicated header keeps its fail-closed `None` (the query never
    // becomes an escape hatch around the duplicate-smuggling guard).
    let has_subject_header = req.headers.iter().any(|(n, _)| n == "x-dregg-subject");
    let inject_subject = if has_subject_header { None } else { q_subject };

    if eff_host.is_none() && inject_subject.is_none() {
        return None; // no browser shim — the programmatic Host-header path, untouched
    }

    let mut headers = req.headers.clone();
    if let Some(s) = inject_subject {
        headers.push(("x-dregg-subject".to_string(), s));
    }
    Some(ServeRequest {
        method: req.method,
        host: eff_host.unwrap_or_else(|| req.host.clone()),
        target: req.target.clone(),
        body: req.body.clone(),
        headers,
    })
}

/// A filesystem-safe grain workdir segment from a host.
fn sanitize(host: &str) -> String {
    host.chars()
        .map(|c| {
            if c.is_ascii_alphanumeric() || c == '-' || c == '.' {
                c
            } else {
                '_'
            }
        })
        .collect()
}

/// Serve the platform over HTTP with the self-serve control endpoint. `operator`
/// is the verified subject allowed to tick the block clock (`POST /clock`);
/// `None` disables the route entirely (fail-closed — but then NO grain ever
/// lapses on a served platform, so a production deploy should set one). Returns
/// only on a fatal bind/accept error.
pub fn serve_platform(
    bind: &str,
    control_host: String,
    provider: CellId,
    asset: CellId,
    workdir_base: PathBuf,
    operator: Option<String>,
    platform: Arc<AgentPlatform>,
) -> std::io::Result<()> {
    serve_http(bind, move |req: &ServeRequest| {
        platform.handle_request(
            &control_host,
            provider,
            asset,
            &workdir_base,
            operator.as_deref(),
            req,
        )
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use dregg_agent::agent::{AgentAction, PlannedBrain, ToolCall};

    const CONTROL: &str = "control.localhost";
    const GRAIN: &str = "g.agents.dregg";
    const OWNER: &str = "dga1_owner";
    const VIEWER: &str = "dga1_viewer";
    const DRIVER: &str = "dga1_driver";
    const MALLORY: &str = "dga1_mallory";

    fn cid(n: u8) -> CellId {
        CellId::from_bytes([n; 32])
    }

    fn workdir() -> PathBuf {
        let p = std::env::temp_dir().join(format!("dregg-grain-serve-{}", std::process::id()));
        std::fs::create_dir_all(&p).unwrap();
        p
    }

    /// Build a request with an optional verified `X-Dregg-Subject` header.
    fn req(
        method: HttpMethod,
        host: &str,
        target: &str,
        subject: Option<&str>,
        body: &str,
    ) -> ServeRequest {
        let mut headers = Vec::new();
        if let Some(s) = subject {
            headers.push(("x-dregg-subject".to_string(), s.to_string()));
        }
        ServeRequest {
            method,
            host: host.to_string(),
            target: target.to_string(),
            body: body.as_bytes().to_vec(),
            headers,
        }
    }

    /// Build a request with an arbitrary set of extra headers (for the browser-shim
    /// smoke test: `X-Dregg-Grain-Host` + a real `Host` that is NOT the target).
    fn req_hdrs(
        method: HttpMethod,
        host: &str,
        target: &str,
        extra: &[(&str, &str)],
        body: &str,
    ) -> ServeRequest {
        let headers = extra
            .iter()
            .map(|(n, v)| (n.to_ascii_lowercase(), v.to_string()))
            .collect();
        ServeRequest {
            method,
            host: host.to_string(),
            target: target.to_string(),
            body: body.as_bytes().to_vec(),
            headers,
        }
    }

    /// **The browser-friendly routing shim, end-to-end WITHOUT a model.** A browser
    /// cannot set the `Host` header, so it names the grain-host via
    /// `X-Dregg-Grain-Host` (with a real `Host` that is a dead-end) — and the
    /// header-less `EventSource` transcript names it via `?host=&subject=` query
    /// params. Proven here: rent via the header shim (Host ≠ control) → 200; verify
    /// R0/R2 + attest via the header shim → the honest verdicts; watch the transcript
    /// via the query-param shim → the SSE meta/step/done; a non-member via the SAME
    /// shim still 404s (the widened HOST source never weakened auth); and `GET /`
    /// serves the driver page. None of this needs a live brain.
    #[test]
    fn the_browser_shim_routes_rent_verify_and_watch_without_a_model() {
        let wd = workdir();
        let platform = AgentPlatform::new();
        // The browser's real Host is a dead-end (e.g. the page origin); the target is
        // carried entirely by X-Dregg-Grain-Host.
        const BROWSER_HOST: &str = "127.0.0.1:8903";
        let grain = "shimmed.grain";
        let rent_body = format!(
            "{{\"host\":\"{grain}\",\"caps\":\"fs\",\"budget\":100000,\"rent_per_period\":100,\"period\":50}}"
        );

        // ── rent via the X-Dregg-Grain-Host shim (points at the CONTROL host) ─────
        let r = call(
            &platform,
            &wd,
            req_hdrs(
                HttpMethod::Post,
                BROWSER_HOST,
                "/rent",
                &[("x-dregg-subject", OWNER), ("x-dregg-grain-host", CONTROL)],
                &rent_body,
            ),
        );
        assert_eq!(r.status, 200, "rent via header shim: {}", r.body_str());
        assert_eq!(platform.owner_of(grain).as_deref(), Some(OWNER));

        // Drive it directly (no live brain) so the transcript + verify have real work.
        let plan = vec![AgentAction::Op(ToolCall::new(
            "fs_write",
            [
                ("path".to_string(), "s.txt".to_string()),
                ("content".to_string(), "hi".to_string()),
            ],
        ))];
        let mut brain = PlannedBrain::new(plan);
        platform.drive(grain, "write", &mut brain).expect("drive");

        // ── verify R0 / R2 / attest via the header shim ──────────────────────────
        let v0 = call(
            &platform,
            &wd,
            req_hdrs(
                HttpMethod::Get,
                BROWSER_HOST,
                "/verify",
                &[("x-dregg-subject", OWNER), ("x-dregg-grain-host", grain)],
                "",
            ),
        );
        assert_eq!(v0.status, 200, "R0 verify via shim");
        let v2 = call(
            &platform,
            &wd,
            req_hdrs(
                HttpMethod::Get,
                BROWSER_HOST,
                "/verify?r2",
                &[("x-dregg-subject", OWNER), ("x-dregg-grain-host", grain)],
                "",
            ),
        );
        assert_eq!(
            v2.status, 422,
            "an unminted grain honestly fails R2 via shim"
        );
        let att = call(
            &platform,
            &wd,
            req_hdrs(
                HttpMethod::Get,
                BROWSER_HOST,
                "/attest",
                &[("x-dregg-subject", OWNER), ("x-dregg-grain-host", grain)],
                "",
            ),
        );
        assert_eq!(att.status, 200, "attest via shim");
        assert!(!att.body.is_empty(), "attestation has bytes to keep");

        // ── watch the transcript via the QUERY-PARAM shim (EventSource form) ─────
        let t = call(
            &platform,
            &wd,
            req_hdrs(
                HttpMethod::Get,
                BROWSER_HOST,
                &format!("/transcript?host={grain}&subject={OWNER}"),
                &[], // no headers at all — exactly what EventSource can send
                "",
            ),
        );
        assert_eq!(t.status, 200, "transcript via query-param shim");
        assert_eq!(t.content_type, "text/event-stream");
        assert!(t.body_str().contains("event: meta"), "SSE meta frame");
        assert!(
            t.body_str().contains("event: step"),
            "SSE step frame (real work)"
        );
        assert!(t.body_str().contains("event: done"), "SSE done frame");

        // ── the widened HOST source did NOT weaken auth: a non-member still 404s ──
        let mal = call(
            &platform,
            &wd,
            req_hdrs(
                HttpMethod::Get,
                BROWSER_HOST,
                "/verify",
                &[("x-dregg-subject", MALLORY), ("x-dregg-grain-host", grain)],
                "",
            ),
        );
        assert_eq!(
            mal.status, 404,
            "a non-member 404s through the shim (no oracle)"
        );
        // …and via the query-param form too.
        let mal_q = call(
            &platform,
            &wd,
            req_hdrs(
                HttpMethod::Get,
                BROWSER_HOST,
                &format!("/transcript?host={grain}&subject={MALLORY}"),
                &[],
                "",
            ),
        );
        assert_eq!(
            mal_q.status, 404,
            "a non-member 404s through the query shim"
        );
        // A query subject is NOT injected when a header subject is present (the
        // header stays primary): a header MALLORY is not silently overridden.
        let both = call(
            &platform,
            &wd,
            req_hdrs(
                HttpMethod::Get,
                BROWSER_HOST,
                &format!("/verify?host={grain}&subject={OWNER}"),
                &[("x-dregg-subject", MALLORY), ("x-dregg-grain-host", grain)],
                "",
            ),
        );
        assert_eq!(
            both.status, 404,
            "the header subject wins over the query subject"
        );

        // ── GET / serves the driver page (host-independent, public) ──────────────
        let page = call(
            &platform,
            &wd,
            req_hdrs(HttpMethod::Get, BROWSER_HOST, "/", &[], ""),
        );
        assert_eq!(page.status, 200, "the driver page is served at /");
        assert!(page.content_type.starts_with("text/html"), "html page");
        assert!(
            page.body_str().contains("Drive a grain"),
            "the driver page body"
        );
    }

    /// A platform with one grain rented (owner = OWNER) that has done real work, so
    /// the transcript has steps and `verify` re-witnesses a genuine chain.
    /// Provisioned via the direct `rent` API with a future first-due block (rent
    /// not yet owed at clock 0), so the grain is drivable — the HTTP `/rent` front
    /// door (which grants a one-period grace from the current clock) is exercised
    /// by [`the_rent_front_door_provisions_a_drivable_grain`].
    fn rented_platform(wd: &Path) -> AgentPlatform {
        let platform = AgentPlatform::new();
        // provider=2, lease=7, asset=9; rent 100 every 50 blocks from block 1000.
        let terms = LeaseTerms::new(cid(2), cid(7), cid(9), 100, 50, 1000, 0);
        platform
            .rent(
                GRAIN,
                OWNER,
                "fs",
                100_000,
                wd.to_str().unwrap(),
                terms,
                None,
            )
            .expect("rent the grain");

        // Drive it directly (no live brain needed) to populate genuine steps.
        let plan = vec![AgentAction::Op(ToolCall::new(
            "fs_write",
            [
                ("path".to_string(), "notes.txt".to_string()),
                ("content".to_string(), "hello".to_string()),
            ],
        ))];
        let mut brain = PlannedBrain::new(plan);
        platform
            .drive(GRAIN, "write notes", &mut brain)
            .expect("drive");
        platform
    }

    const OPERATOR: &str = "dga1_operator";

    fn call(platform: &AgentPlatform, wd: &Path, r: ServeRequest) -> HttpResponse {
        platform.handle_request(CONTROL, cid(2), cid(9), wd, Some(OPERATOR), &r)
    }

    /// A shared Viewer may READ (/transcript + /attest + /verify) but may NOT /drive
    /// (403); a Driver share drives (passes the gate); a non-member 404s on
    /// everything; the owner is Admin; an unknown role fails closed.
    #[test]
    fn the_share_role_gate_is_fail_closed_over_the_routes() {
        let wd = workdir();
        let platform = rented_platform(&wd);

        // ── owner (Admin) shares a Viewer and a Driver ──────────────────────────
        assert_eq!(
            call(
                &platform,
                &wd,
                req(
                    HttpMethod::Post,
                    GRAIN,
                    "/share",
                    Some(OWNER),
                    &format!("{{\"subject\":\"{VIEWER}\",\"role\":\"viewer\"}}")
                )
            )
            .status,
            200,
            "owner shares a viewer"
        );
        assert_eq!(
            call(
                &platform,
                &wd,
                req(
                    HttpMethod::Post,
                    GRAIN,
                    "/share",
                    Some(OWNER),
                    &format!("{{\"subject\":\"{DRIVER}\",\"role\":\"driver\"}}")
                )
            )
            .status,
            200,
            "owner shares a driver"
        );

        // ── the Viewer READS but cannot DRIVE ───────────────────────────────────
        let t = call(
            &platform,
            &wd,
            req(HttpMethod::Get, GRAIN, "/transcript", Some(VIEWER), ""),
        );
        assert_eq!(t.status, 200, "viewer reads the transcript");
        assert_eq!(t.content_type, "text/event-stream");
        assert!(t.body_str().contains("event: meta"), "SSE meta frame");
        assert!(
            t.body_str().contains("event: step"),
            "SSE step frame (real work)"
        );
        assert!(t.body_str().contains("event: done"), "SSE done frame");
        assert_eq!(
            call(
                &platform,
                &wd,
                req(HttpMethod::Get, GRAIN, "/attest", Some(VIEWER), "")
            )
            .status,
            200,
            "viewer reads attest"
        );
        assert_eq!(
            call(
                &platform,
                &wd,
                req(HttpMethod::Get, GRAIN, "/verify", Some(VIEWER), "")
            )
            .status,
            200,
            "viewer re-witnesses"
        );
        // TOOTH: a Viewer POSTing /drive is refused 403 (never reaches the brain).
        assert_eq!(
            call(
                &platform,
                &wd,
                req(
                    HttpMethod::Post,
                    GRAIN,
                    "/drive",
                    Some(VIEWER),
                    "{\"goal\":\"go\"}"
                )
            )
            .status,
            403,
            "a viewer cannot drive"
        );

        // ── the Driver PASSES the drive gate ────────────────────────────────────
        // Without the live brain, the gated route falls through to 503 (no model),
        // NOT 403/404 — proving the driver role cleared the gate.
        let d = call(
            &platform,
            &wd,
            req(
                HttpMethod::Post,
                GRAIN,
                "/drive",
                Some(DRIVER),
                "{\"goal\":\"go\",\"tools\":[\"fs_write\"]}",
            ),
        );
        assert!(
            d.status != 403 && d.status != 404,
            "a driver clears the drive gate (got {})",
            d.status
        );
        #[cfg(not(feature = "live-brain"))]
        assert_eq!(d.status, 503, "no live brain in the default build");

        // ── a non-member 404s on EVERYTHING (no existence oracle) ───────────────
        for (m, p, b) in [
            (HttpMethod::Get, "/transcript", ""),
            (HttpMethod::Get, "/verify", ""),
            (HttpMethod::Get, "/attest", ""),
            (HttpMethod::Post, "/drive", "{\"goal\":\"x\"}"),
            (
                HttpMethod::Post,
                "/share",
                "{\"subject\":\"x\",\"role\":\"viewer\"}",
            ),
            (HttpMethod::Post, "/unshare", "{\"subject\":\"x\"}"),
        ] {
            assert_eq!(
                call(&platform, &wd, req(m, GRAIN, p, Some(MALLORY), b)).status,
                404,
                "non-member 404s on {p}"
            );
        }

        // ── the owner is Admin (can share + read + drive-gate) ──────────────────
        assert_eq!(
            call(
                &platform,
                &wd,
                req(HttpMethod::Get, GRAIN, "/verify", Some(OWNER), "")
            )
            .status,
            200,
            "owner reads"
        );

        // ── a member below Admin cannot share (403, not 404 — they ARE a member) ─
        assert_eq!(
            call(
                &platform,
                &wd,
                req(
                    HttpMethod::Post,
                    GRAIN,
                    "/share",
                    Some(VIEWER),
                    &format!("{{\"subject\":\"{MALLORY}\",\"role\":\"viewer\"}}")
                )
            )
            .status,
            403,
            "a viewer cannot share"
        );

        // ── an unknown role fails closed (400) ──────────────────────────────────
        assert_eq!(
            call(
                &platform,
                &wd,
                req(
                    HttpMethod::Post,
                    GRAIN,
                    "/share",
                    Some(OWNER),
                    &format!("{{\"subject\":\"{MALLORY}\",\"role\":\"root\"}}")
                )
            )
            .status,
            400,
            "an unknown role is refused"
        );

        // ── unshare denies: revoke the Viewer → they 404 again ──────────────────
        assert_eq!(
            call(
                &platform,
                &wd,
                req(
                    HttpMethod::Post,
                    GRAIN,
                    "/unshare",
                    Some(OWNER),
                    &format!("{{\"subject\":\"{VIEWER}\"}}")
                )
            )
            .status,
            200,
            "owner revokes the viewer"
        );
        assert_eq!(
            call(
                &platform,
                &wd,
                req(HttpMethod::Get, GRAIN, "/transcript", Some(VIEWER), "")
            )
            .status,
            404,
            "the revoked viewer is a non-member again"
        );

        // ── an unauthenticated request (no subject) is 401 ──────────────────────
        assert_eq!(
            call(
                &platform,
                &wd,
                req(HttpMethod::Get, GRAIN, "/transcript", None, "")
            )
            .status,
            401,
            "no verified subject → 401"
        );
    }

    /// **BYOK — `POST /act` cap-gates + meters + mints ONE renter-proposed action,
    /// with NO host LLM key.** The model ran in the renter's browser under the
    /// renter's key; only the single proposed action reaches the host. Proven here:
    /// a valid `fs_write` on a fresh grain → `admitted:1`, `consumed:1`, and a receipt
    /// whose `action` is `fs_write:<path>` (a genuine minted receipt, `/attest`'s
    /// view); a Viewer is refused (403 — `/act` spends, so it is Driver+); a
    /// non-member 404s (no existence oracle); no verified subject → 401; and an action
    /// OUTSIDE the grain's caps (`http_get` under an `fs`-only grain) comes back an
    /// HONEST `cap_refused:1` / `admitted:0` at 200 — the capabilities disposed of
    /// what the model proposed — never a 4xx/5xx error.
    #[test]
    fn the_act_route_gates_and_mints_one_proposed_action() {
        let wd = workdir();
        let platform = AgentPlatform::new();
        // A FRESH grain (no prior drive) so the meter reads exactly this action.
        let terms = LeaseTerms::new(cid(2), cid(7), cid(9), 100, 50, 1000, 0);
        platform
            .rent(
                GRAIN,
                OWNER,
                "fs",
                100_000,
                wd.to_str().unwrap(),
                terms,
                None,
            )
            .expect("rent the grain");
        // Share a Driver (may act) and a Viewer (may not).
        platform
            .share(GRAIN, OWNER, DRIVER, crate::Role::Driver)
            .expect("share driver");
        platform
            .share(GRAIN, OWNER, VIEWER, crate::Role::Viewer)
            .expect("share viewer");

        // ── a valid proposed fs_write is minted: admitted + a real receipt ────────
        let act_body = "{\"tool\":\"fs_write\",\"args\":{\"path\":\"haiku.txt\",\"content\":\"a grain wakes\"}}";
        let a = call(
            &platform,
            &wd,
            req(HttpMethod::Post, GRAIN, "/act", Some(OWNER), act_body),
        );
        assert_eq!(
            a.status,
            200,
            "the proposed action is minted: {}",
            a.body_str()
        );
        let body = a.body_str();
        assert!(
            body.contains("\"admitted\":1,"),
            "admitted one action: {body}"
        );
        assert!(body.contains("\"cap_refused\":0"), "no cap refusal: {body}");
        assert!(
            body.contains("\"consumed\":1,"),
            "meter drew one unit: {body}"
        );
        assert!(
            body.contains("\"action\":\"fs_write:haiku.txt\""),
            "the receipt is a view of the fs_write: {body}"
        );
        assert!(
            body.contains("\"consumed_after\":1"),
            "receipt meter: {body}"
        );
        // The action actually ran (the host executes it — it holds the workdir).
        assert!(
            wd.join("haiku.txt").exists(),
            "the fs_write reached the grain's workdir"
        );
        // R2: the minted action is a view over a committed kernel turn.
        let v2 = call(
            &platform,
            &wd,
            req(HttpMethod::Get, GRAIN, "/verify?r2", Some(OWNER), ""),
        );
        assert_eq!(v2.status, 200, "the minted /act turn verifies at R2");
        assert!(v2.body_str().contains("\"linked\":1"), "one linked receipt");

        // ── a Viewer cannot /act (403 — it spends), a non-member 404s ─────────────
        assert_eq!(
            call(
                &platform,
                &wd,
                req(HttpMethod::Post, GRAIN, "/act", Some(VIEWER), act_body)
            )
            .status,
            403,
            "a viewer cannot act"
        );
        assert_eq!(
            call(
                &platform,
                &wd,
                req(HttpMethod::Post, GRAIN, "/act", Some(MALLORY), act_body)
            )
            .status,
            404,
            "a non-member 404s (no existence oracle)"
        );
        // ── no verified subject → 401 ─────────────────────────────────────────────
        assert_eq!(
            call(
                &platform,
                &wd,
                req(HttpMethod::Post, GRAIN, "/act", None, act_body)
            )
            .status,
            401,
            "acting requires a verified subject"
        );

        // ── an action OUTSIDE the grain's caps is an honest cap_refused, not error ─
        let outside = "{\"tool\":\"http_get\",\"args\":{\"url\":\"https://example.com/\"}}";
        let ref_resp = call(
            &platform,
            &wd,
            req(HttpMethod::Post, GRAIN, "/act", Some(DRIVER), outside),
        );
        assert_eq!(
            ref_resp.status, 200,
            "a capability refusal is reported honestly at 200, not an error"
        );
        let rb = ref_resp.body_str();
        assert!(rb.contains("\"admitted\":0"), "nothing admitted: {rb}");
        assert!(rb.contains("\"cap_refused\":1"), "the cap gate bit: {rb}");
    }

    /// The platform-level ACL directly: owner is implicit Admin, a shared subject
    /// gets its role, unshare removes it, a non-member is None, and only an Admin
    /// may share (a Viewer's share attempt is Unauthorized).
    #[test]
    fn the_acl_grants_and_revokes_roles() {
        let wd = workdir();
        let platform = rented_platform(&wd);
        assert_eq!(
            platform.role_of(GRAIN, OWNER),
            Some(crate::Role::Admin),
            "owner is admin"
        );
        assert_eq!(
            platform.role_of(GRAIN, MALLORY),
            None,
            "stranger is a non-member"
        );

        platform
            .share(GRAIN, OWNER, VIEWER, crate::Role::Viewer)
            .expect("owner shares");
        assert_eq!(platform.role_of(GRAIN, VIEWER), Some(crate::Role::Viewer));
        assert!(!platform.role_of(GRAIN, VIEWER).unwrap().can_drive());

        // A Viewer cannot share (below Admin) — Unauthorized, not a silent success.
        assert!(matches!(
            platform.share(GRAIN, VIEWER, MALLORY, crate::Role::Viewer),
            Err(crate::AgentPlatformError::Unauthorized(_))
        ));
        // A non-member sharing is NoSuchGrain (no existence oracle).
        assert!(matches!(
            platform.share(GRAIN, MALLORY, VIEWER, crate::Role::Admin),
            Err(crate::AgentPlatformError::NoSuchGrain(_))
        ));

        platform
            .unshare(GRAIN, OWNER, VIEWER)
            .expect("owner revokes");
        assert_eq!(
            platform.role_of(GRAIN, VIEWER),
            None,
            "revoked → non-member"
        );
    }

    /// **The HTTP /rent front door, both polarities.** No verified subject → 401
    /// (the owner is never body-supplied). A well-formed rent → 200, owned by the
    /// verified subject, and DRIVABLE (the one-period grace from the current clock
    /// means a fresh grain is not instantly behind on rent). Renting an occupied
    /// host → 409. A HALF R1 anchor (nonce without pubkey) → 400: the anchor is
    /// both-or-nothing, never a grain that reads as anchored but confers nothing.
    #[test]
    fn the_rent_front_door_provisions_a_drivable_grain() {
        let wd = workdir();
        let platform = AgentPlatform::new();
        let body = "{\"host\":\"fresh.agents.dregg\",\"caps\":\"fs\",\"budget\":100000,\"rent_per_period\":100,\"period\":50}";

        // No verified subject → 401.
        assert_eq!(
            call(
                &platform,
                &wd,
                req(HttpMethod::Post, CONTROL, "/rent", None, body)
            )
            .status,
            401,
            "renting requires a verified subject"
        );

        // A verified subject rents; the grain is owned by that subject.
        let r = call(
            &platform,
            &wd,
            req(HttpMethod::Post, CONTROL, "/rent", Some(OWNER), body),
        );
        assert_eq!(r.status, 200, "the front door provisions: {}", r.body_str());
        assert_eq!(
            platform.owner_of("fresh.agents.dregg").as_deref(),
            Some(OWNER)
        );

        // The grace window: a freshly-rented grain is immediately drivable (not
        // lapsed on first use by an already-due first period).
        let plan = vec![AgentAction::Op(ToolCall::new(
            "fs_write",
            [
                ("path".to_string(), "fresh.txt".to_string()),
                ("content".to_string(), "grain".to_string()),
            ],
        ))];
        let mut brain = PlannedBrain::new(plan);
        let report = platform
            .drive("fresh.agents.dregg", "write", &mut brain)
            .expect("a fresh front-door grain drives inside the grace window");
        assert!(report.admitted > 0);

        // Renting the same host again is refused, never a silent eviction.
        assert_eq!(
            call(
                &platform,
                &wd,
                req(HttpMethod::Post, CONTROL, "/rent", Some(MALLORY), body)
            )
            .status,
            409,
            "an occupied host is refused"
        );

        // The control host itself is not rentable (route shadowing).
        let control_grab = "{\"host\":\"control.localhost\",\"caps\":\"fs\",\"budget\":1000,\"rent_per_period\":100,\"period\":50}";
        assert_eq!(
            call(
                &platform,
                &wd,
                req(
                    HttpMethod::Post,
                    CONTROL,
                    "/rent",
                    Some(MALLORY),
                    control_grab
                )
            )
            .status,
            400,
            "the control host cannot be occupied by a grain"
        );

        // A HALF anchor is refused (both-or-nothing).
        let half = format!(
            "{{\"host\":\"half.agents.dregg\",\"caps\":\"fs\",\"budget\":1000,\"rent_per_period\":100,\"period\":50,\"renter_nonce\":\"{}\"}}",
            "11".repeat(32)
        );
        assert_eq!(
            call(
                &platform,
                &wd,
                req(HttpMethod::Post, CONTROL, "/rent", Some(OWNER), &half)
            )
            .status,
            400,
            "half an R1 anchor is refused"
        );
    }

    /// **The operator clock route, fail-closed both ways.** Unconfigured operator →
    /// the route does not exist (404). Wrong subject → 403; no subject → 401; the
    /// operator ticks it → 200 and the platform clock advances MONOTONELY (a
    /// regression is ignored, so a rewound node cannot re-extend credit).
    #[test]
    fn the_clock_route_is_operator_only_and_monotone() {
        let wd = workdir();
        let platform = AgentPlatform::new();

        // No operator configured → the route does not exist.
        let r = platform.handle_request(
            CONTROL,
            cid(2),
            cid(9),
            &wd,
            None,
            &req(
                HttpMethod::Post,
                CONTROL,
                "/clock",
                Some(OPERATOR),
                "{\"block\":10}",
            ),
        );
        assert_eq!(r.status, 404, "no operator configured → no clock route");

        // No subject → 401; a non-operator subject → 403; neither ticks the clock.
        assert_eq!(
            call(
                &platform,
                &wd,
                req(HttpMethod::Post, CONTROL, "/clock", None, "{\"block\":10}")
            )
            .status,
            401
        );
        assert_eq!(
            call(
                &platform,
                &wd,
                req(
                    HttpMethod::Post,
                    CONTROL,
                    "/clock",
                    Some(MALLORY),
                    "{\"block\":10}"
                )
            )
            .status,
            403
        );
        assert_eq!(platform.clock(), 0, "refused ticks do not move the clock");

        // The operator ticks it; a later regression is ignored (monotone).
        let ok = call(
            &platform,
            &wd,
            req(
                HttpMethod::Post,
                CONTROL,
                "/clock",
                Some(OPERATOR),
                "{\"block\":1100}",
            ),
        );
        assert_eq!(ok.status, 200);
        assert!(ok.body_str().contains("\"clock\":1100"));
        let back = call(
            &platform,
            &wd,
            req(
                HttpMethod::Post,
                CONTROL,
                "/clock",
                Some(OPERATOR),
                "{\"block\":900}",
            ),
        );
        assert_eq!(back.status, 200);
        assert!(
            back.body_str().contains("\"clock\":1100"),
            "a clock regression is ignored"
        );
        assert_eq!(platform.clock(), 1100);
    }

    /// `GET /verify?r2` is honest about the rung: a grain driven UNMINTED fails R2
    /// (422 — its receipts are not views over committed kernel turns) while plain
    /// `/verify` (the R0 tamper-evidence rung) passes. Membership still gates both
    /// (a non-member 404s).
    #[test]
    fn the_verify_r2_route_refuses_an_unminted_grain() {
        let wd = workdir();
        let platform = rented_platform(&wd);
        assert_eq!(
            call(
                &platform,
                &wd,
                req(HttpMethod::Get, GRAIN, "/verify", Some(OWNER), "")
            )
            .status,
            200,
            "R0 verify passes"
        );
        assert_eq!(
            call(
                &platform,
                &wd,
                req(HttpMethod::Get, GRAIN, "/verify?r2", Some(OWNER), "")
            )
            .status,
            422,
            "an unminted grain does not pass R2"
        );
        assert_eq!(
            call(
                &platform,
                &wd,
                req(HttpMethod::Get, GRAIN, "/verify?r2", Some(MALLORY), "")
            )
            .status,
            404,
            "a non-member still 404s"
        );
    }
}
