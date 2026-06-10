//! The [`Grant`] builder — the ergonomic vocabulary of agent permissions.
//!
//! A grant says: *this subject may use these tools, until this time, optionally
//! at this rate.* It compiles down to a biscuit token where each tool is an
//! `app(tool, actions)` authority fact, the subject is a `user(subject)` fact,
//! and the expiry is a `check if time($t) < until` caveat installed via a
//! narrowing block — so the same machinery that powers attenuation powers
//! time-boxing.

use biscuit_auth::KeyPair;
use dregg_token::{Attenuation, AuthToken, BiscuitToken};

use crate::{AuthError, Token};

/// A rate limit annotation: `count` requests per `window` (e.g. `30/h`).
///
/// At L1 the rate is **advisory** — it rides into the token as metadata and is
/// surfaced in receipts for the L2 (stateful) gate to enforce. L1 is stateless
/// and offline, so it cannot itself count requests; it records the intent.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Rate {
    /// Permitted request count per window.
    pub count: u64,
    /// Window unit: one of `s`, `m`, `h`, `d`.
    pub per: char,
}

impl Rate {
    /// Render as the canonical `30/h` form.
    pub fn render(&self) -> String {
        format!("{}/{}", self.count, self.per)
    }

    /// Parse a `30/h` style rate spec.
    pub fn parse(s: &str) -> Result<Rate, AuthError> {
        let (count, per) = s
            .split_once('/')
            .ok_or_else(|| AuthError::Grant(format!("rate `{s}` must look like `30/h`")))?;
        let count: u64 = count
            .trim()
            .parse()
            .map_err(|_| AuthError::Grant(format!("rate count `{count}` is not a number")))?;
        let per = per.trim();
        let per_ch = match per {
            "s" | "sec" | "second" => 's',
            "m" | "min" | "minute" => 'm',
            "h" | "hr" | "hour" => 'h',
            "d" | "day" => 'd',
            other => {
                return Err(AuthError::Grant(format!(
                    "rate window `{other}` must be one of s/m/h/d"
                )));
            }
        };
        Ok(Rate {
            count,
            per: per_ch,
        })
    }
}

/// A scoped agent permission, built fluently.
///
/// ```
/// use dregg_auth::Grant;
/// let g = Grant::new("ci-bot").tools(["read", "pr-create"]).until(1_900_000_000);
/// assert_eq!(g.tools.len(), 2);
/// ```
#[derive(Clone, Debug)]
pub struct Grant {
    /// The subject the token is confined to (an agent / sub-agent identity).
    pub subject: String,
    /// The tools the subject may use (`read`, `pr-create`, ...).
    pub tools: Vec<String>,
    /// The action mask granted on each tool (defaults to `use`).
    pub actions: String,
    /// Absolute expiry, unix seconds. `None` = no expiry (discouraged).
    pub until: Option<i64>,
    /// Advisory rate limit (enforced at L2).
    pub rate: Option<Rate>,
}

impl Grant {
    /// Begin a grant for `subject`. Add tools with [`Grant::tool`] /
    /// [`Grant::tools`], a deadline with [`Grant::until`], a rate with
    /// [`Grant::rate`].
    pub fn new(subject: &str) -> Self {
        Self {
            subject: subject.to_string(),
            tools: Vec::new(),
            actions: "use".to_string(),
            until: None,
            rate: None,
        }
    }

    /// Add a single tool to the grant.
    pub fn tool(mut self, tool: &str) -> Self {
        self.tools.push(tool.to_string());
        self
    }

    /// Add several tools to the grant.
    pub fn tools<I, S>(mut self, tools: I) -> Self
    where
        I: IntoIterator<Item = S>,
        S: Into<String>,
    {
        self.tools.extend(tools.into_iter().map(Into::into));
        self
    }

    /// Set the action mask granted on each tool (default `use`). Used when a
    /// tool distinguishes verbs (e.g. `r` vs `rw`).
    pub fn with_actions(mut self, actions: &str) -> Self {
        self.actions = actions.to_string();
        self
    }

    /// Set the absolute expiry (unix seconds). After this, every check denies.
    pub fn until(mut self, unix_secs: i64) -> Self {
        self.until = Some(unix_secs);
        self
    }

    /// Attach an advisory rate limit (enforced at L2).
    pub fn rate(mut self, rate: Rate) -> Self {
        self.rate = Some(rate);
        self
    }

    /// Issue this grant as a token signed by `keypair`.
    pub(crate) fn issue_with(&self, keypair: &KeyPair) -> Result<Token, AuthError> {
        if self.tools.is_empty() {
            return Err(AuthError::Grant(
                "a grant must scope at least one tool (an unscoped agent token is the very thing we exist to prevent)".into(),
            ));
        }

        // Each tool becomes an `app(tool, actions)` authority fact. The subject
        // becomes the confined `user`. Rate rides in as a `feature` annotation.
        let apps: Vec<(String, String)> = self
            .tools
            .iter()
            .map(|t| (t.clone(), self.actions.clone()))
            .collect();
        let features: Vec<String> = self
            .rate
            .map(|r| vec![format!("rate:{}", r.render())])
            .unwrap_or_default();

        let minted = BiscuitToken::mint_dregg(
            keypair,
            &apps,
            &[], // no service grants — agent tools are apps
            &features,
            &[], // no oauth providers
            &[], // no oauth scopes
            Some(&self.subject),
        )?;

        // Time-boxing: install the expiry as a narrowing block (the same caveat
        // machinery attenuation uses). A token without an expiry skips this.
        let token = if let Some(until) = self.until {
            let expiry = Attenuation {
                not_after: Some(until),
                ..Default::default()
            };
            let boxed = minted.attenuate(&expiry)?;
            let encoded = boxed.to_encoded()?;
            BiscuitToken::from_encoded(&encoded, keypair.public())?
        } else {
            minted
        };

        Ok(Token::new(token, keypair.public()))
    }

}

/// Strict allowlist sanitizer for values interpolated into biscuit Datalog.
///
/// Mirrors the token crate's own `sanitize_datalog_string` discipline: only
/// alphanumerics + a small safe-punctuation set, so two distinct inputs can
/// never collapse to the same Datalog string (identity-confusion / injection
/// safety). Raw Datalog is never accepted.
fn sanitize(s: &str) -> Result<&str, AuthError> {
    const SAFE: &str = " -_./:@";
    if s.chars().all(|c| c.is_alphanumeric() || SAFE.contains(c)) {
        Ok(s)
    } else {
        Err(AuthError::Grant(format!(
            "tool/value `{s}` contains characters not safe for an authorization caveat"
        )))
    }
}

/// Build the **confining** biscuit block for narrowing a grant.
///
/// Unlike the token crate's structured `apps` attenuation (which asserts a grant
/// *exists*), this confines the *request*: it installs `allowed_tool(t)` facts
/// for the narrowed set plus `check if request_app($t), allowed_tool($t)`, so the
/// block's check fails for any requested tool outside the set — genuine
/// no-amplify. Expiry, when present, is added as `check if time($t), $t < until`.
pub(crate) fn confining_block_datalog(narrow: &Grant) -> Result<String, AuthError> {
    if narrow.tools.is_empty() && narrow.until.is_none() {
        return Ok(String::new());
    }
    let mut code = String::new();
    if !narrow.tools.is_empty() {
        for tool in &narrow.tools {
            code.push_str(&format!("allowed_tool(\"{}\");\n", sanitize(tool)?));
        }
        code.push_str("check if request_app($t), allowed_tool($t);\n");
    }
    if let Some(until) = narrow.until {
        code.push_str(&format!("check if time($t), $t < {until};\n"));
    }
    Ok(code)
}
