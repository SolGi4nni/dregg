//! `policy` — the productized grant + verifying-middleware shape, on the
//! **proven** credential core.
//!
//! This is the adoption wedge the product ladder calls L1: *auth as the gateway
//! drug.* An agent (an MCP server, a sub-agent, a CI bot) is handed a scoped,
//! time-boxed, attenuable token instead of an unscoped API key; a gateway
//! holding only the issuer's **public key** decides — offline — whether each
//! tool call is inside the grant, and logs a receipt. The polis is *pull*, never
//! *toll*: nothing here reaches a node, a wallet, a chain, or an ontology.
//!
//! ## Why this module exists (and what it supersedes)
//!
//! The crate's first cut shipped an agent-grant surface ([`crate::Grant`] /
//! [`crate::Token`], the `eb2_` biscuit/Datalog path) under [`crate::mcp`]. That
//! surface decides with *Datalog checks*. This module instead compiles a grant
//! straight onto the [`credential`](crate::credential) core, whose every
//! operation — *attenuation only narrows*, *verification is the fail-closed meet
//! of all caveats*, *missing data refuses rather than reads as false* — is the
//! machine-checked one in `metatheory/Dregg2/`. The product's headline claim
//! ("prove your agent cannot exceed the grant") is therefore literally true on
//! the path a stranger actually touches: the grant a `Policy` issues IS a proven
//! [`Credential`](crate::credential::Credential), and the gate that admits it IS
//! [`Credential::verify`](crate::credential::Credential::verify).
//!
//! ## The 60-second shape
//!
//! ```
//! use dregg_auth::policy::{Grant, Policy, Verifier, Call};
//!
//! // A root authority. Keep the secret seed; publish the public key.
//! let polis = Policy::generate();
//!
//! // Grant an agent read + pr-create, expiring at a clock reading.
//! let token = polis.issue(
//!     Grant::to("ci-bot").tools(["read", "pr-create"]).until(1_900_000_000),
//! ).unwrap().encode();
//!
//! // A gateway holding ONLY the public key admits/denies each tool call, offline.
//! let gate = Verifier::new(polis.public_key_hex());
//! let allow = gate.admit(&token, &Call::tool("read").at(1_800_000_000));
//! assert!(allow.admitted());
//! assert_eq!(allow.receipt.subject.as_deref(), Some("ci-bot"));
//!
//! let deny = gate.admit(&token, &Call::tool("delete-repo").at(1_800_000_000));
//! assert!(!deny.admitted());
//! ```
//!
//! ## How a grant becomes proven caveats
//!
//! `Grant::to("ci-bot").tools(["read","pr-create"]).until(t)` compiles to a
//! credential carrying three first-party caveats (all on the root block):
//!
//! * `subject == "ci-bot"` — the agent identity, pinned as a *checked* fact
//!   (`Pred::AttrEq`). The [`Verifier`] binds the subject from the token itself
//!   before evaluating, so this gate passes for the right agent and is
//!   recoverable for the receipt — stronger than an advisory `user()` annotation.
//! * `tool ∈ {read, pr-create}` — the tool allowlist, as the fail-closed
//!   disjunction `Pred::AnyOf([AttrEq{tool,read}, AttrEq{tool,pr-create}])`
//!   (the empty allowlist is `AnyOf([])`, which *refuses* — you cannot mint an
//!   unscoped agent token).
//! * `clock ≤ until` — the expiry, as `Pred::NotAfter` (downward-closed:
//!   once expired, every check refuses).
//!
//! Narrowing ([`Policy`]-free, holder-side) is [`Grant::attenuate_token`]: it
//! appends a confining block (a tighter tool allowlist and/or a tighter expiry).
//! Because the core only ever *appends*, the dropped reach is gone for good —
//! the no-amplify property, structural and unforgeable on the wire.

use crate::credential::{Caveat, Context, Credential, Pred, PublicKey, RootKey, WireError};

/// The attribute key under which the [`Verifier`] binds the requested tool.
pub const TOOL_KEY: &str = "tool";
/// The attribute key under which the agent identity is pinned and bound.
pub const SUBJECT_KEY: &str = "subject";

// =============================================================================
// Policy — the issuing authority (proven-core RootKey, product-named)
// =============================================================================

/// The issuing authority: an ed25519 root over the proven credential core.
///
/// The secret seed signs (issues) grants; the public key is all a [`Verifier`]
/// needs. This is exactly [`RootKey`] with the product's vocabulary; persist
/// [`Policy::secret_hex`], publish [`Policy::public_key_hex`].
pub struct Policy {
    root: RootKey,
}

impl Policy {
    /// Generate a fresh authority from operating-system randomness.
    pub fn generate() -> Self {
        Self {
            root: RootKey::generate(),
        }
    }

    /// Reconstruct from a 32-byte hex secret seed (as [`Policy::secret_hex`]
    /// prints). The golden-vector / persisted-root path.
    pub fn from_secret_hex(hex: &str) -> Result<Self, PolicyError> {
        let seed = crate::credential::unhex32_pub(hex.trim())
            .map_err(|e| PolicyError::Key(e.to_string()))?;
        Ok(Self {
            root: RootKey::from_seed(seed),
        })
    }

    /// The 32-byte secret seed, hex-encoded. **Secret** — store it where the
    /// authority keeps secrets; never hand it to a verifier.
    pub fn secret_hex(&self) -> String {
        crate::credential::hex_pub(&self.root.secret_bytes())
    }

    /// The public key, hex-encoded. Safe to publish; the only thing a
    /// [`Verifier`] needs.
    pub fn public_key_hex(&self) -> String {
        self.root.public().to_hex()
    }

    /// The public key as the proven-core [`PublicKey`].
    pub fn public(&self) -> PublicKey {
        self.root.public()
    }

    /// Issue a [`Grant`] as a proven [`GrantToken`]. Refuses an unscoped grant
    /// (no tools) — minting an unscoped agent token is the very thing the
    /// product exists to prevent.
    ///
    /// # Panics-free contract
    /// This returns a [`GrantToken`] only for a well-formed grant; an unscoped
    /// grant yields [`PolicyError::Unscoped`]. (The `AnyOf([])` allowlist would
    /// also refuse at *verify* time, fail-closed — this is the earlier, kinder
    /// refusal.)
    pub fn issue(&self, grant: Grant) -> Result<GrantToken, PolicyError> {
        if grant.tools.is_empty() {
            return Err(PolicyError::Unscoped);
        }
        let cred = self.root.mint(grant.to_caveats());
        Ok(GrantToken {
            cred,
            subject: grant.subject,
        })
    }
}

// =============================================================================
// Grant — the ergonomic vocabulary (the `dregg grant <agent> --tools …` shape)
// =============================================================================

/// A scoped agent permission, built fluently — the productized
/// `grant <agent> --tools read,pr --until friday` shape.
///
/// `Grant::to("ci-bot").tools(["read","pr-create"]).until(t)` says: *the agent
/// `ci-bot` may use `read` or `pr-create`, until clock `t`.* It compiles to the
/// proven caveats described in the [module docs](self).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Grant {
    /// The agent the token is issued to (an MCP server / sub-agent identity).
    pub subject: String,
    /// The tools the agent may use.
    pub tools: Vec<String>,
    /// Absolute expiry on the deployment's monotone clock. `None` = no expiry
    /// (discouraged for agent tokens; prefer short windows + re-issue).
    pub until: Option<u64>,
}

impl Grant {
    /// Begin a grant *to* `subject`. Add tools with [`Grant::tool`] /
    /// [`Grant::tools`]; set a deadline with [`Grant::until`].
    pub fn to(subject: &str) -> Self {
        Self {
            subject: subject.to_string(),
            tools: Vec::new(),
            until: None,
        }
    }

    /// Add a single tool.
    pub fn tool(mut self, tool: &str) -> Self {
        self.tools.push(tool.to_string());
        self
    }

    /// Add several tools.
    pub fn tools<I, S>(mut self, tools: I) -> Self
    where
        I: IntoIterator<Item = S>,
        S: Into<String>,
    {
        self.tools.extend(tools.into_iter().map(Into::into));
        self
    }

    /// Set the absolute expiry (deployment clock — unix seconds or block
    /// height; mint and verify must agree on the unit). After it, every check
    /// refuses.
    pub fn until(mut self, clock: u64) -> Self {
        self.until = Some(clock);
        self
    }

    /// The proven caveats this grant installs on the credential's root block:
    /// the subject gate, the tool allowlist (fail-closed disjunction), and the
    /// optional expiry. The order is stable (subject, tools, expiry) so the
    /// signed digest is reproducible.
    pub fn to_caveats(&self) -> Vec<Caveat> {
        let mut caveats = Vec::with_capacity(3);
        // Subject: a checked fact the Verifier binds from the token itself.
        caveats.push(Caveat::FirstParty(Pred::AttrEq {
            key: SUBJECT_KEY.into(),
            value: self.subject.clone(),
        }));
        // Tool allowlist: AnyOf of equalities. AnyOf([]) refuses (fail-closed),
        // so an empty allowlist is an unscoped token that cannot verify.
        caveats.push(Caveat::FirstParty(tool_allowlist(&self.tools)));
        // Expiry, when present.
        if let Some(until) = self.until {
            caveats.push(Caveat::FirstParty(Pred::NotAfter { at: until }));
        }
        caveats
    }

    /// Narrow an already-issued token: append a confining block carrying a
    /// tighter tool allowlist and/or a tighter expiry. Holder-side, offline —
    /// no contact with the [`Policy`]. Attenuation can only ever *remove* reach
    /// (the proven `attenuate_narrows`): a token narrowed to `read` can never
    /// regain `pr-create`.
    ///
    /// At least one dimension must narrow; an empty narrowing is
    /// [`PolicyError::EmptyNarrowing`] (the trivial `True` attenuation is a
    /// no-op on authority and so is rejected here as a likely mistake — use the
    /// core's [`Credential::attenuate`] directly if you truly want a key
    /// rotation).
    pub fn attenuate_token(
        token: GrantToken,
        tools: Option<&[String]>,
        until: Option<u64>,
    ) -> Result<GrantToken, PolicyError> {
        let GrantToken { cred, subject } = token;
        let mut caveats: Vec<Caveat> = Vec::new();
        match tools {
            Some(ts) if !ts.is_empty() => {
                caveats.push(Caveat::FirstParty(tool_allowlist(ts)));
            }
            Some(_) => {
                // An explicit empty narrowing would be AnyOf([]) — it refuses
                // EVERYTHING, which is a footgun, not an attenuation. Reject.
                return Err(PolicyError::EmptyNarrowing);
            }
            None => {}
        }
        if let Some(at) = until {
            caveats.push(Caveat::FirstParty(Pred::NotAfter { at }));
        }
        if caveats.is_empty() {
            return Err(PolicyError::EmptyNarrowing);
        }
        Ok(GrantToken {
            cred: cred.attenuate(caveats),
            subject,
        })
    }
}

/// Build the fail-closed tool allowlist predicate for a set of tools:
/// `AnyOf([AttrEq{tool,t} for t in tools])`. The empty set is `AnyOf([])`,
/// which refuses (`Pred.evalAny [] = false`).
fn tool_allowlist(tools: &[String]) -> Pred {
    Pred::AnyOf(
        tools
            .iter()
            .map(|t| Pred::AttrEq {
                key: TOOL_KEY.into(),
                value: t.clone(),
            })
            .collect(),
    )
}

// =============================================================================
// GrantToken — an issued (or attenuated) proven credential, with its subject
// =============================================================================

/// A scoped agent token: a proven [`Credential`] plus the agent identity it was
/// issued to (carried alongside so the [`Verifier`] can bind it and so receipts
/// can name it without re-deriving it from the chain).
///
/// Encode it ([`GrantToken::encode`], the bearer `dga1_…` form), attenuate it
/// ([`Grant::attenuate_token`]), or hand it to a [`Verifier`].
pub struct GrantToken {
    cred: Credential,
    subject: String,
}

impl GrantToken {
    /// The agent identity this token was issued to.
    pub fn subject(&self) -> &str {
        &self.subject
    }

    /// The proven credential underneath (for direct core operations / explain).
    pub fn credential(&self) -> &Credential {
        &self.cred
    }

    /// Encode to the bearer `dga1_…` string form.
    ///
    /// **Bearer**: the encoded form carries the right to present *and* to
    /// attenuate further (the proven core's tail-key discipline). The subject
    /// is *not* a separate field on the wire — it is a verified fact carried as
    /// the `subject == …` caveat, so [`GrantToken::decode`] recovers it from the
    /// credential itself. Transmit the token like the capability it is.
    pub fn encode(&self) -> String {
        self.cred.encode()
    }

    /// Decode a bearer `dga1_…` token, recovering its subject from the
    /// credential's caveats. Structural validation only (the proven core's
    /// `decode`); the authorization decision is [`Verifier::admit`]. The
    /// recovered subject is whatever the `subject == …` caveat names, or the
    /// empty string for a raw core credential carrying no subject gate.
    pub fn decode(encoded: &str) -> Result<GrantToken, WireError> {
        let cred = Credential::decode(encoded)?;
        let subject = recover_subject(&cred).unwrap_or_default();
        Ok(GrantToken { cred, subject })
    }

    /// Human-readable terms, block by block (the proven core's `explain`),
    /// prefixed with the subject line.
    pub fn explain(&self) -> String {
        format!("grant to `{}`\n{}", self.subject, self.cred.explain())
    }
}

// =============================================================================
// Verifier — the verifying middleware (holds ONLY the public key)
// =============================================================================

/// An incoming tool call: the tool name, its arguments (advisory, carried into
/// the receipt), and the gateway's clock.
///
/// `now` is supplied explicitly for deterministic offline checks; the proven
/// core never reads wall-time (verification is reproducible). A call with no
/// clock cannot satisfy any expiry caveat — fail-closed.
#[derive(Clone, Debug, Default)]
pub struct Call {
    /// The tool being invoked (e.g. `pr-create`).
    pub tool: String,
    /// Advisory `(name, value)` arguments, carried into the receipt.
    pub args: Vec<(String, String)>,
    /// The gateway clock (deployment clock). `None` ⇒ expiry caveats refuse.
    pub now: Option<u64>,
}

impl Call {
    /// A bare call to `tool` (no args, no clock).
    pub fn tool(tool: &str) -> Self {
        Self {
            tool: tool.to_string(),
            ..Default::default()
        }
    }

    /// Pin the gateway clock for a deterministic decision.
    pub fn at(mut self, now: u64) -> Self {
        self.now = Some(now);
        self
    }

    /// Attach an advisory `(name, value)` argument (carried into the receipt).
    pub fn arg(mut self, name: &str, value: &str) -> Self {
        self.args.push((name.to_string(), value.to_string()));
        self
    }
}

/// The verifying middleware: holds **only** the issuer's public key and decides
/// each tool call offline, against the proven credential core.
///
/// Drop it in front of an MCP server / tool-dispatch host: for every call,
/// [`Verifier::admit`] parses the agent's token (signature chain checked under
/// the held key), binds the call's tool + the token's own subject into the
/// proven verification context, runs [`Credential::verify`] (the fail-closed
/// meet of every caveat), and returns a [`Verdict`] carrying the decision and an
/// audit [`Receipt`]. No network, no node, no wallet — the polis is pull.
pub struct Verifier {
    public_key_hex: String,
}

impl Verifier {
    /// Build a verifier that checks tokens against `public_key_hex`.
    pub fn new(public_key_hex: impl Into<String>) -> Self {
        Self {
            public_key_hex: public_key_hex.into(),
        }
    }

    /// The public key this verifier checks against.
    pub fn public_key_hex(&self) -> &str {
        &self.public_key_hex
    }

    /// Parse a `dga1_…` token and recover its subject (the agent identity),
    /// without yet evaluating a request. Subject recovery reads the first
    /// `subject == …` caveat on the chain — the fact a [`Grant`] pins on the
    /// root block.
    ///
    /// Structural validation only (the proven core's `decode`); the
    /// authorization decision is [`Verifier::admit`].
    pub fn parse(&self, token_encoded: &str) -> Result<(Credential, Option<String>), WireError> {
        let cred = Credential::decode(token_encoded)?;
        let subject = recover_subject(&cred);
        Ok((cred, subject))
    }

    /// Decide whether `call` (carried by `token_encoded`) is admitted, and
    /// produce an audit [`Receipt`] either way (allow and deny are both
    /// auditable). Fully offline.
    ///
    /// The decision is exactly the proven [`Credential::verify`]: the signature
    /// chain must verify under the held public key, the carried proof key must
    /// match the tail, and **every** caveat must hold — the subject gate
    /// (against the subject bound from the token itself), the tool allowlist
    /// (against the call's tool), and the expiry (against the call's clock).
    pub fn admit(&self, token_encoded: &str, call: &Call) -> Verdict {
        // Parse + recover subject. A malformed/unknown token denies with a
        // reason and a subjectless receipt.
        let (cred, subject) = match self.parse(token_encoded) {
            Ok(v) => v,
            Err(e) => return Verdict::denied_parse(call, e),
        };

        let pk = match PublicKey::from_hex(&self.public_key_hex) {
            Ok(pk) => pk,
            Err(e) => return Verdict::denied_key(call, subject, e.to_string()),
        };

        // Build the proven verification context: the requested tool, the
        // subject bound FROM THE TOKEN (so the agent-identity gate is checked,
        // not merely asserted by the caller), the clock, and any args that look
        // like attribute bindings are NOT trusted as gates here — args are
        // advisory at L1; only `tool` and `subject` gate.
        let mut ctx = Context::new().attr(TOOL_KEY, &call.tool);
        if let Some(ref s) = subject {
            ctx = ctx.attr(SUBJECT_KEY, s);
        }
        if let Some(now) = call.now {
            ctx = ctx.at(now);
        }

        let decision = cred.verify(&pk, &ctx);
        Verdict::from_decision(call, subject, decision)
    }
}

/// Recover the subject from a credential: the value of the first
/// `subject == …` first-party caveat on the chain (what [`Grant::to_caveats`]
/// pins on the root block). `None` if the credential carries no subject gate
/// (e.g. a raw core credential not minted through [`Policy::issue`]).
fn recover_subject(cred: &Credential) -> Option<String> {
    for (_, caveat) in cred.caveats() {
        if let Caveat::FirstParty(Pred::AttrEq { key, value }) = caveat {
            if key == SUBJECT_KEY {
                return Some(value.clone());
            }
        }
    }
    None
}

// =============================================================================
// Verdict + Receipt — the decision and its audit line (the L2 seed)
// =============================================================================

/// The outcome of a gated tool call: the allow/deny decision (with a reason)
/// plus the audit [`Receipt`].
#[derive(Clone, Debug)]
pub struct Verdict {
    allowed: bool,
    /// The audit receipt for this call (emit it to a log — the L2 seed).
    pub receipt: Receipt,
}

impl Verdict {
    /// Was the call admitted?
    pub fn admitted(&self) -> bool {
        self.allowed
    }

    /// The human-readable reason — allow, or *which* constraint failed.
    pub fn reason(&self) -> &str {
        &self.receipt.reason
    }

    fn from_decision(
        call: &Call,
        subject: Option<String>,
        decision: Result<(), crate::credential::Refusal>,
    ) -> Self {
        let (allowed, reason) = match decision {
            Ok(()) => (true, "allowed".to_string()),
            // The proven Refusal already names which requirement failed.
            Err(r) => (false, r.to_string()),
        };
        Verdict {
            allowed,
            receipt: Receipt::new(call, subject, allowed, reason),
        }
    }

    fn denied_parse(call: &Call, e: WireError) -> Self {
        Verdict {
            allowed: false,
            receipt: Receipt::new(call, None, false, format!("denied: malformed token: {e}")),
        }
    }

    fn denied_key(call: &Call, subject: Option<String>, e: String) -> Self {
        Verdict {
            allowed: false,
            receipt: Receipt::new(
                call,
                subject,
                false,
                format!("denied: bad verifier key: {e}"),
            ),
        }
    }
}

/// One audit receipt: who asked for what, when, and what was decided.
///
/// Intentionally plain and serializable; a chain of these is an agent's
/// behavioral ledger (the L2 seed). The gateway emits one line per call.
#[derive(Clone, Debug, serde::Serialize, serde::Deserialize)]
pub struct Receipt {
    /// The agent the token was issued to, recovered from the token (not from
    /// the caller). `None` if the token carried no subject.
    pub subject: Option<String>,
    /// The tool that was requested.
    pub tool: String,
    /// The advisory arguments (`name=value`).
    pub args: Vec<String>,
    /// The gateway clock used, if pinned.
    pub at: Option<u64>,
    /// Whether the call was admitted.
    pub allowed: bool,
    /// The human-readable reason (allow, or which constraint failed).
    pub reason: String,
}

impl Receipt {
    fn new(call: &Call, subject: Option<String>, allowed: bool, reason: String) -> Self {
        Receipt {
            subject,
            tool: call.tool.clone(),
            args: call.args.iter().map(|(k, v)| format!("{k}={v}")).collect(),
            at: call.now,
            allowed,
            reason,
        }
    }

    /// Render as a single audit line.
    pub fn line(&self) -> String {
        let verdict = if self.allowed { "ALLOW" } else { "DENY " };
        let subj = self.subject.as_deref().unwrap_or("?");
        let args = if self.args.is_empty() {
            String::new()
        } else {
            format!(" [{}]", self.args.join(", "))
        };
        format!(
            "{verdict} subject={subj} tool={}{args} :: {}",
            self.tool, self.reason
        )
    }

    /// Render as a JSON line (for structured log ingestion).
    pub fn json(&self) -> String {
        serde_json::to_string(self).unwrap_or_else(|e| format!("{{\"receipt_error\":\"{e}\"}}"))
    }
}

// =============================================================================
// Errors
// =============================================================================

/// An error from the policy surface.
#[derive(Debug, thiserror::Error)]
pub enum PolicyError {
    /// A key could not be parsed.
    #[error("invalid key: {0}")]
    Key(String),
    /// A grant scoped no tools — an unscoped agent token is the very thing this
    /// product exists to prevent.
    #[error(
        "a grant must scope at least one tool (an unscoped agent token is the thing we prevent)"
    )]
    Unscoped,
    /// An attenuation narrowed nothing (no tools, no tighter expiry).
    #[error("attenuation must narrow at least one dimension (tools and/or expiry)")]
    EmptyNarrowing,
}
