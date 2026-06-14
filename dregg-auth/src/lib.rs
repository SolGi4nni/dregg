//! # dregg-auth — scoped agent permissions you can prove (and verify offline)
//!
//! **The guarantee:** prove your agent *cannot exceed the grant*. dregg-auth
//! issues a scoped, time-boxed, delegatable, revocable token for an agent, and
//! lets anyone holding only a **public key** decide — *offline, with no network,
//! no node, no wallet, no blockchain* — whether a given tool call is inside the
//! grant. Attenuation can only ever *narrow* a grant; it can never amplify.
//!
//! This is the friendly face of dregg's `token` layer (the biscuit /
//! ed25519 / Datalog path), pointed squarely at the acute modern need:
//! agents (MCP, sub-agents, CI bots) that are handed unscoped API keys today.
//! dregg-auth is the aspirin: scoped agent access as a one-liner.
//!
//! ## The 30-second shape (the product surface: [`policy`])
//! ```
//! use dregg_auth::policy::{Grant, Policy, Verifier, Call};
//!
//! // A root authority. Keep the secret seed; publish the public key.
//! let polis = Policy::generate();
//!
//! // Grant an agent read + pr-create, expiring at a clock reading. The token
//! // IS a machine-checked credential (the `dga1_…` form).
//! let token = polis.issue(
//!     Grant::to("ci-bot").tools(["read", "pr-create"]).until(1_900_000_000),
//! ).unwrap().encode();
//!
//! // A gateway holding ONLY the public key admits/denies each call, OFFLINE.
//! let gate = Verifier::new(polis.public_key_hex());
//! assert!( gate.admit(&token, &Call::tool("read").at(1_800_000_000)).admitted());
//! assert!(!gate.admit(&token, &Call::tool("delete-repo").at(1_800_000_000)).admitted());
//! ```
//!
//! ## What L1 deliberately is NOT
//! No node. No wallet. No blockchain. No ontology. The whole path is pure and
//! offline — issuance and verification touch no network, no node, no circuit,
//! at compile time *or* runtime (`cargo tree -i dregg-circuit -p dregg-auth`
//! shows no path). The adoption quotient stands: the polis is PULL, never TOLL.
//!
//! ## The proven credential core ([`credential`]) and the product ([`policy`])
//! The [`credential`] module is the standalone token scheme whose semantics
//! are the machine-checked ones in `metatheory/Dregg2/` — an ed25519 caveat
//! chain ([`credential::Credential`]) with the proven caveat algebra
//! ([`credential::Pred`]), third-party discharge with the macaroon binding
//! discipline ([`credential::Discharge`]), a versioned postcard/base64url
//! wire form (`dga1_…`), and `explain()` everywhere. Each type's doc comment
//! names its Lean counterpart.
//!
//! The [`policy`] module is the productized grant + verifying-middleware shape
//! *on that proven core*: [`policy::Policy`] issues, [`policy::Grant`] is the
//! `grant <agent> --tools … --until …` vocabulary, and [`policy::Verifier`] is
//! the offline middleware a gateway runs in front of an agent — the path the
//! CLI rides. The first-cut `Root`/[`Grant`]/[`Token`] surface below (the
//! `eb2_` biscuit/Datalog wedge, with the [`mcp`] gate) remains for back-compat.

use biscuit_auth::{Algorithm, KeyPair, PrivateKey, PublicKey};
use dregg_token::{AuthRequest, AuthToken, BiscuitToken, TokenError};

pub mod credential;
mod grant;
pub mod mcp;
pub mod policy;

pub use grant::{Grant, Rate};

/// An error from dregg-auth. Thin wrapper carrying a human-readable reason —
/// the "explain" seed: every denial should be able to say *why*.
#[derive(Debug, thiserror::Error)]
pub enum AuthError {
    /// A key (private or public) could not be parsed.
    #[error("invalid key: {0}")]
    Key(String),
    /// Token minting / attenuation / encoding failed.
    #[error("token error: {0}")]
    Token(#[from] TokenError),
    /// A grant was malformed (e.g., no tools, bad tool name).
    #[error("invalid grant: {0}")]
    Grant(String),
}

// =============================================================================
// Root — the issuing authority
// =============================================================================

/// The issuing authority: an ed25519 keypair. The **private** half signs
/// (issues) grants; the **public** half is all anyone needs to verify offline.
///
/// Persist [`Root::private_key_hex`] locally (e.g. `~/.dregg-auth/root.key`);
/// publish [`Root::public_key_hex`] anywhere verifiers can read it.
pub struct Root {
    keypair: KeyPair,
}

impl Root {
    /// Generate a fresh root authority (ed25519).
    pub fn generate() -> Self {
        Self {
            keypair: KeyPair::new_with_algorithm(Algorithm::Ed25519),
        }
    }

    /// Reconstruct a root from a hex-encoded ed25519 private key
    /// (as produced by [`Root::private_key_hex`]).
    pub fn from_private_hex(hex: &str) -> Result<Self, AuthError> {
        let sk = PrivateKey::from_bytes_hex(hex.trim(), Algorithm::Ed25519)
            .map_err(|e| AuthError::Key(e.to_string()))?;
        Ok(Self {
            keypair: KeyPair::from(&sk),
        })
    }

    /// The hex-encoded private key. **Secret** — store it where the root keeps
    /// secrets; never hand it to a verifier.
    pub fn private_key_hex(&self) -> String {
        self.keypair.private().to_bytes_hex()
    }

    /// The hex-encoded public key. Safe to publish; this is the *only* thing a
    /// verifier needs to check a token offline.
    pub fn public_key_hex(&self) -> String {
        self.keypair.public().to_bytes_hex()
    }

    /// Issue a scoped token for a [`Grant`].
    pub fn issue(&self, grant: &Grant) -> Result<Token, AuthError> {
        grant.issue_with(&self.keypair)
    }
}

// =============================================================================
// Token — a granted (or attenuated) capability
// =============================================================================

/// A scoped agent token. Print it ([`Token::encode`]), attenuate it
/// ([`Token::attenuate`]), or verify a request against it ([`Token::verify`]).
///
/// The token carries its own root [`PublicKey`] so that offline verification
/// and re-wrapping after attenuation need nothing external.
pub struct Token {
    inner: BiscuitToken,
    root_pub: PublicKey,
}

impl Token {
    pub(crate) fn new(inner: BiscuitToken, root_pub: PublicKey) -> Self {
        Self { inner, root_pub }
    }

    /// Encode to the printable `eb2_`-prefixed base64 wire form.
    pub fn encode(&self) -> Result<String, AuthError> {
        Ok(self.inner.to_encoded()?)
    }

    /// Parse and cryptographically verify a token against a public key, OFFLINE.
    ///
    /// Returns the [`Token`] if (and only if) the signature chain checks out
    /// against `public_key_hex`. No network, no node, no wallet.
    pub fn parse(encoded: &str, public_key_hex: &str) -> Result<Token, AuthError> {
        let pk = PublicKey::from_bytes_hex(public_key_hex.trim(), Algorithm::Ed25519)
            .map_err(|e| AuthError::Key(e.to_string()))?;
        let inner = BiscuitToken::from_encoded(encoded.trim(), pk)?;
        Ok(Token {
            inner,
            root_pub: pk,
        })
    }

    /// The hex public key this token verifies under.
    pub fn root_public_key_hex(&self) -> String {
        self.root_pub.to_bytes_hex()
    }

    /// Narrow this token to a subset of tools (and/or a tighter expiry).
    ///
    /// Attenuation can only ever *remove* reach. A token narrowed to `read`
    /// can never regain `pr-create` — that's the structural no-amplify property
    /// the whole product rests on.
    ///
    /// # Tool confinement
    /// We append a biscuit block that **confines the request**, not one that
    /// merely asserts a grant exists. The token crate's structured `apps`
    /// attenuation emits `check if app("read", ...)` — which is trivially true
    /// for any token that *holds* a read grant and therefore does NOT remove
    /// other tools. To genuinely confine, we install
    /// `allowed_tool("read"); check if request_app($t), allowed_tool($t);`
    /// so the check fails for any requested tool outside the narrowed set.
    pub fn attenuate(&self, narrow: &Grant) -> Result<Token, AuthError> {
        let code = grant::confining_block_datalog(narrow)?;
        if code.is_empty() {
            return Err(AuthError::Grant(
                "attenuation must narrow at least one dimension (tools and/or expiry)".into(),
            ));
        }
        let block = biscuit_auth::builder::BlockBuilder::new()
            .code(&code)
            .map_err(|e| AuthError::Token(TokenError::Datalog(e.to_string())))?;
        let appended = self
            .inner
            .inner()
            .append(block)
            .map_err(|e| AuthError::Token(TokenError::Crypto(e.to_string())))?;
        Ok(Token {
            inner: BiscuitToken::new(appended, self.root_pub),
            root_pub: self.root_pub,
        })
    }

    /// Verify a request against this (already-cryptographically-valid) token.
    ///
    /// This is the authorization decision: does the grant permit `request`?
    pub fn verify(&self, request: &Request) -> Decision {
        let auth_req = request.to_auth_request();
        match self.inner.verify(&auth_req) {
            Ok(clearance) => Decision::allow(clearance.matched_policy, clearance.subject),
            Err(e) => Decision::deny(explain_denial(&e, request)),
        }
    }
}

// =============================================================================
// Request + Decision
// =============================================================================

/// A request to authorize: a tool call (+ optional args + a clock reading).
///
/// `args` are advisory at L1 (the structural grant is over *tools*); they ride
/// along into receipts and into the L2 per-arg gate. `now` is the verifier's
/// clock — supply it explicitly for deterministic offline checks (tests,
/// reproducible audits); omit it to use wall-clock.
#[derive(Clone, Debug, Default)]
pub struct Request {
    /// The tool being invoked (e.g. `pr-create`).
    pub tool: String,
    /// The action verb (defaults to `use`); maps to the token's action mask.
    pub action: String,
    /// Free-form args, carried into receipts (advisory at L1).
    pub args: Vec<String>,
    /// The verifier's clock (unix seconds). `None` = wall-clock.
    pub now: Option<i64>,
}

impl Request {
    /// A request to use `tool` (action defaults to `use`).
    pub fn tool(tool: &str) -> Self {
        Self {
            tool: tool.to_string(),
            action: "use".to_string(),
            ..Default::default()
        }
    }

    /// Override the action verb (defaults to `use`).
    pub fn action(mut self, action: &str) -> Self {
        self.action = action.to_string();
        self
    }

    /// Set the verifier's clock for a deterministic offline check.
    pub fn at(mut self, now: i64) -> Self {
        self.now = Some(now);
        self
    }

    /// Attach advisory args (carried into the receipt / L2 gate).
    pub fn with_args<I, S>(mut self, args: I) -> Self
    where
        I: IntoIterator<Item = S>,
        S: Into<String>,
    {
        self.args = args.into_iter().map(Into::into).collect();
        self
    }

    fn to_auth_request(&self) -> AuthRequest {
        // A tool maps onto an `app(tool, actions)` grant. The requested action
        // is matched against the granted action mask by the underlying Datalog.
        AuthRequest {
            app_id: Some(self.tool.clone()),
            action: Some(self.action.clone()),
            now: self.now,
            ..Default::default()
        }
    }
}

/// The result of an authorization check: allow or deny, always with a reason.
#[derive(Clone, Debug)]
pub struct Decision {
    allowed: bool,
    reason: String,
    subject: Option<String>,
}

impl Decision {
    fn allow(matched: Option<String>, subject: Option<String>) -> Self {
        Self {
            allowed: true,
            reason: matched
                .map(|p| format!("allowed (matched {p})"))
                .unwrap_or_else(|| "allowed".to_string()),
            subject,
        }
    }
    fn deny(reason: String) -> Self {
        Self {
            allowed: false,
            reason,
            subject: None,
        }
    }
    /// Was the request inside the grant?
    pub fn allowed(&self) -> bool {
        self.allowed
    }
    /// A human-readable reason — allow, or *which* constraint failed.
    pub fn reason(&self) -> &str {
        &self.reason
    }
    /// The subject (agent) the token was confined to, when recoverable.
    pub fn subject(&self) -> Option<&str> {
        self.subject.as_deref()
    }
}

/// Turn a token-crate denial into an agent-legible reason (the explain seed).
fn explain_denial(e: &TokenError, request: &Request) -> String {
    match e {
        TokenError::Denied(_) => format!(
            "denied: tool `{}` (action `{}`) is outside this grant, or the grant has expired",
            request.tool, request.action
        ),
        TokenError::Expired => "denied: the grant has expired".to_string(),
        other => format!("denied: {other}"),
    }
}

// =============================================================================
// Top-level offline verify (the one-liner)
// =============================================================================

/// Verify a printable token against a public key + a request — fully OFFLINE.
///
/// This is the product's headline call: a gateway holding only the issuer's
/// public key decides allow/deny for a `(tool, args)` with no network.
pub fn verify_offline(encoded: &str, public_key_hex: &str, request: &Request) -> Decision {
    match Token::parse(encoded, public_key_hex) {
        Ok(token) => token.verify(request),
        Err(e) => Decision::deny(format!("denied: {e}")),
    }
}
