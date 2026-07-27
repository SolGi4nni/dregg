//! # THE ROUTER — resolve, verify, render. Or refuse, honestly.
//!
//! One handler, `Fn(&WebRequest) -> WebResponse`, so the tests drive the EXACT code path
//! the socket does; the binary only adds a listener.
//!
//! ## THE PATH, END TO END
//!
//! ```text
//!   GET /poll/7f2a9c4d
//!     ├─ parse the path with the ONE grammar (uri.rs, mirrored from port.ts)
//!     ├─ registry lookup on the kind        → unregistered ⇒ 404, never a guess
//!     ├─ classify the addr token            → malformed / too short ⇒ 400
//!     ├─ disambiguate the prefix            → ambiguous ⇒ 404 with the candidates
//!     ├─ run the verification ladder        → any refusal ⇒ 502, object NEVER rendered
//!     ├─ parse the object + its view-tree   → unreadable ⇒ 502
//!     ├─ the object's kind == the URL kind  → mismatch ⇒ 502
//!     └─ render through deos-view, under the tier-`server` label
//! ```
//!
//! Every arm that is not the last one produces a rendered, human-readable refusal page —
//! never a blank, never a bare status code, never an optimistic default (brief §5).

use http_serve::{HttpMethod, WebRequest, WebResponse};

use crate::object::{self, Committee, MirrorObject};
use crate::page::{self, PageConfig};
use crate::store::{ObjectStore, PrefixResolution};
use crate::trust;
use crate::uri::{self, AddrError, AddrToken, Kind};

/// The mirror's configuration.
#[derive(Debug, Clone, Default)]
pub struct MirrorConfig {
    /// Origin + upgrade-path settings for the rendered pages.
    pub page: PageConfig,
    /// The TRUSTED committee for the anchored quorum gate. From configuration only —
    /// never read from a fetched object (`netlayer.ts`'s standing rule). Empty ⇒ the
    /// structural gate, and the page says the signatures were counted, not anchored.
    pub committee: Committee,
}

/// The service: a store plus a config. `handle` is the whole surface.
pub struct Mirror<S: ObjectStore> {
    store: S,
    cfg: MirrorConfig,
}

impl<S: ObjectStore> Mirror<S> {
    /// Build a mirror over `store`.
    ///
    /// The configured origin is normalized to a bare host here, once, so every page names
    /// the party the reader is trusting the same way no matter which form the deployment
    /// wrote (see [`page::normalize_origin`]).
    pub fn new(store: S, mut cfg: MirrorConfig) -> Mirror<S> {
        cfg.page.origin = page::normalize_origin(&cfg.page.origin);
        Mirror { store, cfg }
    }

    /// The store, for a caller that seeds or inspects it.
    pub fn store(&self) -> &S {
        &self.store
    }

    /// Handle one request.
    pub fn handle(&self, req: &WebRequest) -> WebResponse {
        if req.method != HttpMethod::Get && req.method != HttpMethod::Head {
            return self.refuse(
                405,
                "This mirror only reads",
                "The mirror serves <code>GET</code>. Acting on a dregg object is a cap-gated \
                 turn that needs custody, and custody is never on this server, so there is \
                 nothing here to <code>POST</code> to.",
                None,
                None,
            );
        }

        match req.path.as_str() {
            "" | "/" => self.index(),
            "/healthz" => WebResponse::text("ok"),
            "/robots.txt" => WebResponse::text("User-agent: *\nAllow: /\n"),
            path => self.resolve(path),
        }
    }

    fn index(&self) -> WebResponse {
        let counts: Vec<(Kind, usize)> = Kind::ALL
            .iter()
            .map(|k| (*k, self.store.list(*k).len()))
            .collect();
        html(200, page::index_page(&self.cfg.page, &counts))
    }

    fn resolve(&self, path: &str) -> WebResponse {
        // ── the ONE grammar ───────────────────────────────────────────────────
        let Some(dref) = uri::parse_mirror_path(path) else {
            return self.refuse(
                404,
                "Not a dregg reference",
                &format!(
                    "<code>{}</code> is not a dregg mirror path. A reference looks like \
                     <code>/&lt;kind&gt;/&lt;address&gt;</code>, for example \
                     <code>/poll/7f2a9c4d</code>.",
                    page::esc(path)
                ),
                None,
                None,
            );
        };

        // ── the KIND REGISTRY: unregistered is a clean 404, never a guess ──────
        let Some(kind) = Kind::parse(&dref.kind) else {
            let known = Kind::ALL
                .iter()
                .map(|k| format!("<code>{k}</code>"))
                .collect::<Vec<_>>()
                .join(", ");
            return self.refuse(
                404,
                "Unknown kind",
                &format!(
                    "This mirror has no renderer for a <code>{}</code>. It renders: {known}. \
                     It will not guess a surface for a kind it does not know: a guessed \
                     render is a claim about an object nobody made.",
                    page::esc(&dref.kind)
                ),
                None,
                None,
            );
        };

        // ── the address token ─────────────────────────────────────────────────
        let token = match uri::classify_addr(&dref.addr) {
            Ok(t) => t,
            Err(AddrError::Malformed) => {
                return self.refuse(
                    400,
                    "Malformed address",
                    "A dregg content address is a blake3 digest in hex, optionally tagged \
                     <code>b3_</code>. This one is not hex.",
                    None,
                    None,
                );
            }
            Err(AddrError::TooShort { got, need }) => {
                return self.refuse(
                    400,
                    "Address too short",
                    &format!(
                        "A short address needs at least {need} hex characters; this link \
                         carried {got}. Shorter prefixes collide too easily to be worth \
                         resolving, so this mirror refuses them rather than picking one."
                    ),
                    None,
                    None,
                );
            }
            Err(AddrError::TooLong) => {
                return self.refuse(
                    400,
                    "Malformed address",
                    "This is longer than a blake3 digest, so it is not an address.",
                    None,
                    None,
                );
            }
        };

        // ── the git-style prefix: unique, or refuse ────────────────────────────
        let addr_hex = match token {
            AddrToken::Full(hex) => hex,
            AddrToken::Prefix(p) => match self.store.resolve_prefix(kind, &p) {
                PrefixResolution::Unique(full) => full,
                PrefixResolution::Ambiguous(cands) => {
                    let list = cands
                        .iter()
                        .map(|c| {
                            format!(
                                "<li><code>{}</code></li>",
                                page::esc(&uri::mirror_url(
                                    &self.cfg.page.origin,
                                    kind.as_str(),
                                    c
                                ))
                            )
                        })
                        .collect::<String>();
                    return self.refuse(
                        404,
                        "Ambiguous address",
                        &format!(
                            "More than one <code>{kind}</code> starts with \
                             <code>{p}</code>, so this mirror does not know which one the \
                             link meant, and it will not pick. Use more of the address:\
                             <ul class=\"mirror-cands\">{list}</ul>",
                            kind = kind,
                            p = page::esc(&p),
                            list = list
                        ),
                        None,
                        None,
                    );
                }
                PrefixResolution::None => {
                    return self.not_found(kind, &p);
                }
            },
        };

        let canonical = trust::canonical_for(kind.as_str(), &addr_hex);

        // ── fetch ─────────────────────────────────────────────────────────────
        let Some(env) = self.store.get(kind, &addr_hex) else {
            return self.not_found(kind, &addr_hex);
        };

        // ── the verification ladder — refuse renders NOTHING of the object ────
        let report = object::verify(&env, &addr_hex, &self.cfg.committee);
        if let Some((gate, why)) = report.refusal() {
            return self.refuse(
                502,
                "This object did not verify",
                "The bytes served for this address failed a check, so the mirror is showing \
                 you nothing of the object. This is the fail-closed case: an object that \
                 does not verify is never rendered as if it did.",
                Some(&canonical),
                Some(&format!("{}\n  → {why}", gate.label())),
            );
        }

        // ── decode: the object, then its view-tree ────────────────────────────
        let obj: MirrorObject = match serde_json::from_slice(&env.content) {
            Ok(o) => o,
            Err(e) => {
                return self.refuse(
                    502,
                    "Unreadable object",
                    "The bytes at this address hash correctly, but they are not an object \
                     this mirror can read. It will not render a partial guess at them.",
                    Some(&canonical),
                    Some(&e.to_string()),
                );
            }
        };

        // The kind in the object must be the kind in the link. Otherwise a link's visible
        // kind could lie about what the reader is being shown.
        if obj.kind.to_ascii_lowercase() != kind.as_str() {
            return self.refuse(
                502,
                "Kind mismatch",
                &format!(
                    "The link says <code>{kind}</code>, but the object at that address says \
                     <code>{got}</code>. The mirror refuses rather than letting a link's \
                     visible kind disagree with what it shows.",
                    kind = kind,
                    got = page::esc(&obj.kind)
                ),
                Some(&canonical),
                None,
            );
        }

        let tree = match deos_view::parse_view_tree(&obj.view.to_string()) {
            Ok(t) => t,
            Err(e) => {
                return self.refuse(
                    502,
                    "Unreadable view",
                    "The object carries a view this mirror cannot parse. Rendering a \
                     half-parsed surface would show a shape the object never committed to, \
                     so it renders none of it.",
                    Some(&canonical),
                    Some(&e),
                );
            }
        };

        html(
            200,
            page::object_page(
                &self.cfg.page,
                kind,
                &addr_hex,
                &obj.title,
                obj.note.as_deref(),
                &tree,
                &obj.binds,
                &report,
            ),
        )
    }

    fn not_found(&self, kind: Kind, addr_frag: &str) -> WebResponse {
        self.refuse(
            404,
            "No object at that reference",
            &format!(
                "This mirror holds no <code>{kind}</code> at <code>{addr}</code>. A dregg \
                 reference names an object by its hash, so a reference nothing answers is \
                 an honest dead end, not a hint that something else nearby is what you \
                 wanted.",
                kind = kind,
                addr = page::esc(addr_frag)
            ),
            Some(&uri::canonical_uri(kind.as_str(), addr_frag)),
            None,
        )
    }

    fn refuse(
        &self,
        status: u16,
        headline: &str,
        reason_html: &str,
        canonical: Option<&str>,
        detail: Option<&str>,
    ) -> WebResponse {
        html(
            status,
            page::error_page(&self.cfg.page, headline, reason_html, canonical, detail),
        )
    }
}

/// An HTML response at `status`.
fn html(status: u16, body: String) -> WebResponse {
    WebResponse {
        status,
        content_type: "text/html; charset=utf-8".to_string(),
        body: body.into_bytes(),
    }
}
