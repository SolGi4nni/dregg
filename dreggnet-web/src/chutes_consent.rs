//! Viewer-blind HTML adapters for explicit Chutes consent and public receipt provenance.
//!
//! These fragments accept only the shared public disclosure types. There is no viewer, actor,
//! balance, prompt, narration source, private result, or token-count parameter to accidentally
//! reflect into a shared page.

use dreggnet_offerings::chutes_consent::{
    CHUTES_CONSENT_WIRE, ChutesReplaySurface, ViewerBlindChutesConsent, ViewerBlindChutesReceipt,
};

/// A local public route. Query strings/fragments are deliberately forbidden so consent controls
/// cannot copy identity or private input into the shared HTML wire.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ChutesPublicPath(String);

impl ChutesPublicPath {
    pub fn new(path: impl Into<String>) -> Result<Self, &'static str> {
        let path = path.into();
        let valid = path.starts_with('/')
            && !path.starts_with("//")
            && path.len() <= 256
            && path
                .split('/')
                .all(|segment| !matches!(segment, "." | ".."))
            && path.bytes().all(|byte| {
                byte.is_ascii_alphanumeric() || matches!(byte, b'/' | b'-' | b'_' | b'.')
            });
        valid
            .then_some(Self(path))
            .ok_or("Chutes disclosure route must be a bounded local path without query/fragment")
    }

    pub fn as_str(&self) -> &str {
        &self.0
    }
}

fn escape_html(value: &str) -> String {
    value
        .replace('&', "&amp;")
        .replace('<', "&lt;")
        .replace('>', "&gt;")
        .replace('"', "&quot;")
        .replace('\'', "&#39;")
}

/// Render a pre-call consent card. The only submitted value is the exact versioned affirmative
/// consent; viewer identity remains in the platform's authenticated envelope, never the form.
pub fn render_chutes_consent(
    disclosure: &ViewerBlindChutesConsent,
    action: &ChutesPublicPath,
) -> String {
    format!(
        "<section class=\"chutes-consent\" data-audience=\"viewer-blind\" data-provider=\"chutes\"><h2>Optional Chutes narration</h2><p>{}</p><form method=\"post\" action=\"{}\"><input type=\"hidden\" name=\"consent\" value=\"{}\"><button type=\"submit\">{}</button></form></section>",
        escape_html(&disclosure.compact_text()),
        escape_html(action.as_str()),
        CHUTES_CONSENT_WIRE,
        escape_html(disclosure.button_label()),
    )
}

/// Render public post-call provenance with a replay-verification link. No per-viewer account fact
/// is accepted or rendered.
pub fn render_chutes_receipt(
    disclosure: &ViewerBlindChutesReceipt,
    verify: &ChutesPublicPath,
) -> String {
    format!(
        "<aside class=\"chutes-receipt\" data-audience=\"viewer-blind\" data-provider=\"chutes\"><p>{}</p><a rel=\"nofollow\" href=\"{}\">Replay-verify this session</a></aside>",
        escape_html(&disclosure.compact_text(ChutesReplaySurface::Web)),
        escape_html(verify.as_str()),
    )
}
