//! `agent-host` — the **SSH-attach hosting layer** for hosted agent sessions.
//!
//! The distribution model: instead of a user installing the runtime, an operator
//! **hosts** a cap-bounded, budget-bounded, receipted agent and the user
//! **attaches over SSH** (the portal is a sibling lane). This crate is the thin
//! identity/edge glue that makes the attach real:
//!
//! - an [`AccountRecord`] binds an **SSH public key** (the user's identity at the
//!   edge) to a **`dga1_` cap-account** id, a **budget** (the spend ceiling), and
//!   a **cap bundle** (which tools/vendors the session may use);
//! - the [`AgentHostRegistry`] persists those records and emits the OpenSSH
//!   [`authorized_keys`](AgentHostRegistry::authorized_keys) content — one
//!   **forced-command** line per enrolled key that drops the connecting user
//!   straight into THEIR `dregg-agent attach` session, locked down so the SSH
//!   session *is* the agent REPL and nothing else (no shell on the host, no
//!   forwarding).
//!
//! The session itself — the reason→act→observe loop, the brain, the cap-gate ·
//! budget · receipt rail, `verify` — lives in the `dregg-agent` crate (the
//! `attach` subcommand the forced-command names). So this crate owns the *who
//! attaches with what authority* mapping; the `dregg-agent` binary owns the
//! *confined run*. Multi-user isolation is the shape of the construction: each
//! account gets its own session (its own root + meter + cap bundle), so one
//! user's session cannot touch another's.
//!
//! ## Real vs the reviewed-go step (honest)
//!
//! - **Real (this crate, tested):** the key→account→budget→caps mapping, the caps
//!   validation against the real grant vocabulary at enrol time, the durable
//!   record store, and the exact `authorized_keys` forced-command + lock-down line
//!   generation a real sshd consumes.
//! - **The reviewed-go step:** standing up the live edge — a real `sshd` (or a
//!   custom SSH server) whose `AuthorizedKeysFile` (or `AuthorizedKeysCommand`) is
//!   fed by this registry. The forced-command target and the per-user confinement
//!   are proven here; the public hosting is the deploy.

use std::path::Path;

use serde::{Deserialize, Serialize};

pub mod isolation;

/// The default binary an enrolled key's forced-command invokes. A deploy can
/// override it (an absolute path on the host) via [`AgentHostRegistry::with_attach_bin`].
pub const DEFAULT_ATTACH_BIN: &str = "dregg-agent";

/// The default cap an `agent-hostctl enroll` grants when `--caps` is omitted: the
/// **lexically-confined** hosted starter bundle (workdir fs + GitHub egress), NO
/// raw `shell`. A hosted box also holds the operator's keys, so a raw shell would
/// let a tenant read them past the in-process env-scrub — `shell` is restored only
/// behind per-tenant OS isolation (see [`isolation`]).
pub const DEFAULT_HOSTED_CAPS: &str = "fs,http:api.github.com";

/// The per-account live-session quota a hosting deploy enforces (cap concurrent
/// sessions per enrolled subject) — the exhaustion-vector backstop. A real deploy
/// also bounds total SSH connections at the sshd; this is the app-level cap.
pub const DEFAULT_SESSIONS_PER_ACCOUNT: u32 = 8;

/// Why an enrolment / registry op failed.
#[derive(Debug, thiserror::Error)]
pub enum HostError {
    /// The caps string did not parse against the real grant vocabulary.
    #[error("invalid caps `{caps}`: {reason}")]
    BadCaps {
        /// The offending caps string.
        caps: String,
        /// The parser's reason.
        reason: String,
    },
    /// The budget was not a positive number of cents.
    #[error("budget must be > 0 cents (got {0})")]
    BadBudget(i64),
    /// The SSH public key was empty or obviously malformed (not `type base64 …`).
    #[error("malformed ssh public key (expected `ssh-ed25519 AAAA… [comment]`)")]
    BadSshKey,
    /// The account id was empty.
    #[error("account id must not be empty")]
    EmptyAccount,
    /// A record for this SSH key already exists (re-enrol with [`AgentHostRegistry::upsert`]).
    #[error("an account is already enrolled for this ssh key (use upsert to replace)")]
    DuplicateKey,
    /// This account already holds the maximum number of enrolled sessions (the
    /// per-account quota — the exhaustion-vector backstop).
    #[error("account `{account}` is at its session quota ({limit}); revoke one to enrol another")]
    QuotaExceeded {
        /// The account at its ceiling.
        account: String,
        /// The per-account ceiling.
        limit: u32,
    },
    /// Persistence failed.
    #[error("registry io: {0}")]
    Io(String),
}

/// One enrolled user: the SSH identity at the edge bound to the cap-account +
/// budget + cap bundle their hosted session runs under.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct AccountRecord {
    /// The `dga1_` cap-account id this user's session is scoped to (the meter
    /// subject + the receipt identity the `dregg-agent` session derives from).
    pub account: String,
    /// The user's SSH public key (the full authorized_keys key field, e.g.
    /// `ssh-ed25519 AAAA… alice@laptop`). The identity that authenticates the attach.
    pub ssh_pubkey: String,
    /// The session budget ceiling, in USD-cents (the hard spend bound the whole
    /// session — across every goal — draws down from).
    pub budget_cents: i64,
    /// The cap bundle this session may use, as the `dregg-agent` caps string
    /// (e.g. `fs,http:api.github.com,pay:openai`). Validated at enrol time under the
    /// hosted confinement posture — a raw `shell` is ALWAYS refused (the hosted box
    /// holds the operator's keys and per-tenant OS isolation is not yet wired).
    pub caps: String,
    /// The brain the session drives (`nemotron` / `hermes` / a recorded replay tag).
    /// Carried into the forced command. Empty = the `dregg-agent` default.
    #[serde(default)]
    pub brain: String,
}

impl AccountRecord {
    /// The OpenSSH `authorized_keys` line that drops a connecting user into THEIR
    /// confined session: a `command=` forced-command running `dregg-agent attach`
    /// scoped to this account + budget + caps, plus the lock-down options that make
    /// the SSH session *be* the agent REPL and nothing else.
    ///
    /// `restrict` disables agent/port/X11 forwarding and PTY-less extras by
    /// default (fail-closed); `pty` re-enables a terminal so the REPL is usable.
    /// The forced command IGNORES whatever the client asked to run — except that
    /// `dregg-agent attach` reads `SSH_ORIGINAL_COMMAND`, so `ssh acct@host "goal"`
    /// runs that one goal non-interactively.
    ///
    /// The line NEVER carries `--os-isolation`: a hosted session is always
    /// shell-disabled (the box holds the operator's keys and the per-tenant OS jail
    /// in [`isolation`] is not yet wired into any run path — `dregg-agent` hard-errors
    /// on the flag).
    pub fn authorized_keys_line(&self, attach_bin: &str) -> String {
        let mut cmd = format!(
            "{attach_bin} attach --account {acct} --budget {budget} --caps {caps}",
            acct = shell_quote(&self.account),
            budget = self.budget_cents,
            caps = shell_quote(&self.caps),
        );
        if !self.brain.is_empty() {
            cmd.push_str(" --brain ");
            cmd.push_str(&shell_quote(&self.brain));
        }
        // The `command="…"` value is double-quoted in authorized_keys; escape any
        // `"`/`\` in it per the OpenSSH rule (a backslash escapes the next char).
        let escaped = cmd.replace('\\', "\\\\").replace('"', "\\\"");
        format!(
            "command=\"{escaped}\",restrict,pty {key}",
            key = self.ssh_pubkey.trim()
        )
    }
}

/// The host registry: the durable map from SSH keys to confined sessions, and the
/// `authorized_keys` generator a real sshd consumes.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct AgentHostRegistry {
    /// The enrolled accounts, in enrol order.
    records: Vec<AccountRecord>,
    /// The attach binary the forced commands invoke (default [`DEFAULT_ATTACH_BIN`]).
    #[serde(default = "default_attach_bin")]
    attach_bin: String,
}

fn default_attach_bin() -> String {
    DEFAULT_ATTACH_BIN.to_string()
}

impl Default for AgentHostRegistry {
    fn default() -> Self {
        AgentHostRegistry::new()
    }
}

impl AgentHostRegistry {
    /// A fresh, empty registry using the default attach binary. Enrolments are
    /// always validated under the HOSTED posture (fail-closed): a raw `shell` cap is
    /// refused, because the hosted box holds the operator's keys and the per-tenant
    /// OS jail ([`isolation`]) is not yet wired into any run path.
    pub fn new() -> AgentHostRegistry {
        AgentHostRegistry {
            records: Vec::new(),
            attach_bin: default_attach_bin(),
        }
    }

    /// Set the attach binary the forced commands invoke (an absolute path on the
    /// host, e.g. `/usr/local/bin/dregg-agent`).
    pub fn with_attach_bin(mut self, bin: impl Into<String>) -> AgentHostRegistry {
        self.attach_bin = bin.into();
        self
    }

    /// The confinement posture enrolments are validated under: always
    /// [`Hosted`](dregg_agent::session::Confinement::Hosted) — a raw `shell` is
    /// refused. A hosted box holds the operator's keys, and the per-tenant OS jail
    /// that would make `shell` safe again ([`isolation`]) is not yet wired into a run
    /// path, so there is no posture under which a hosted session grants a raw shell.
    fn confinement(&self) -> dregg_agent::session::Confinement {
        dregg_agent::session::Confinement::Hosted
    }

    /// The attach binary the forced commands invoke.
    pub fn attach_bin(&self) -> &str {
        &self.attach_bin
    }

    /// The enrolled accounts.
    pub fn records(&self) -> &[AccountRecord] {
        &self.records
    }

    /// **Enrol** a user: bind their SSH key to an account + budget + caps. Fails if
    /// the caps/budget/key are invalid, or if the key is already enrolled (use
    /// [`upsert`](AgentHostRegistry::upsert) to replace). The caps string is
    /// validated against the REAL `dregg-agent` grant vocabulary, so a bad bundle
    /// is rejected here rather than at the next SSH login.
    pub fn enroll(
        &mut self,
        account: impl Into<String>,
        ssh_pubkey: impl Into<String>,
        budget_cents: i64,
        caps: impl Into<String>,
    ) -> Result<&AccountRecord, HostError> {
        self.enroll_with_brain(account, ssh_pubkey, budget_cents, caps, "")
    }

    /// [`enroll`](AgentHostRegistry::enroll) selecting the session brain.
    pub fn enroll_with_brain(
        &mut self,
        account: impl Into<String>,
        ssh_pubkey: impl Into<String>,
        budget_cents: i64,
        caps: impl Into<String>,
        brain: impl Into<String>,
    ) -> Result<&AccountRecord, HostError> {
        let rec = validate(
            account.into(),
            ssh_pubkey.into(),
            budget_cents,
            caps.into(),
            brain.into(),
            self.confinement(),
        )?;
        if self.find_by_key(&rec.ssh_pubkey).is_some() {
            return Err(HostError::DuplicateKey);
        }
        // Per-account session quota (the exhaustion-vector backstop): cap how many
        // distinct keys/sessions one subject may enrol, so one tenant cannot pin
        // unbounded concurrent hosted sessions.
        let live = self
            .records
            .iter()
            .filter(|r| r.account == rec.account)
            .count() as u32;
        if live >= DEFAULT_SESSIONS_PER_ACCOUNT {
            return Err(HostError::QuotaExceeded {
                account: rec.account.clone(),
                limit: DEFAULT_SESSIONS_PER_ACCOUNT,
            });
        }
        self.records.push(rec);
        Ok(self.records.last().expect("just pushed"))
    }

    /// Enrol or replace by SSH key (idempotent re-enrol).
    pub fn upsert(
        &mut self,
        account: impl Into<String>,
        ssh_pubkey: impl Into<String>,
        budget_cents: i64,
        caps: impl Into<String>,
        brain: impl Into<String>,
    ) -> Result<&AccountRecord, HostError> {
        let rec = validate(
            account.into(),
            ssh_pubkey.into(),
            budget_cents,
            caps.into(),
            brain.into(),
            self.confinement(),
        )?;
        let key = normalize_key(&rec.ssh_pubkey);
        let idx = match self
            .records
            .iter()
            .position(|r| normalize_key(&r.ssh_pubkey) == key)
        {
            Some(i) => {
                self.records[i] = rec;
                i
            }
            None => {
                self.records.push(rec);
                self.records.len() - 1
            }
        };
        Ok(&self.records[idx])
    }

    /// Remove the account enrolled for `ssh_pubkey` (by the key's type+blob, the
    /// comment ignored). Returns the removed record if there was one.
    pub fn revoke(&mut self, ssh_pubkey: &str) -> Option<AccountRecord> {
        let key = normalize_key(ssh_pubkey);
        let i = self
            .records
            .iter()
            .position(|r| normalize_key(&r.ssh_pubkey) == key)?;
        Some(self.records.remove(i))
    }

    /// Look up the account for an SSH key (by its type+blob, the comment ignored) —
    /// what an `AuthorizedKeysCommand` would resolve on each login.
    pub fn find_by_key(&self, ssh_pubkey: &str) -> Option<&AccountRecord> {
        let key = normalize_key(ssh_pubkey);
        self.records
            .iter()
            .find(|r| normalize_key(&r.ssh_pubkey) == key)
    }

    /// Look up by account id.
    pub fn find_by_account(&self, account: &str) -> Option<&AccountRecord> {
        self.records.iter().find(|r| r.account == account)
    }

    /// The full OpenSSH `authorized_keys` content — one forced-command line per
    /// enrolled key. Drop this at `~/.ssh/authorized_keys` of the host's agent
    /// user (or serve it from an `AuthorizedKeysCommand`), and every enrolled SSH
    /// key, on login, lands in its OWN confined `dregg-agent attach` session.
    pub fn authorized_keys(&self) -> String {
        let mut s = String::new();
        s.push_str(
            "# Generated by agent-host. Each line drops the connecting key into\n\
             # its OWN cap-bounded, budget-bounded, receipted `dregg-agent attach` session.\n\
             # The forced command + `restrict` make the SSH session BE the agent REPL.\n",
        );
        for r in &self.records {
            s.push_str(&r.authorized_keys_line(&self.attach_bin));
            s.push('\n');
        }
        s
    }

    /// Persist the registry to `path` (pretty JSON).
    pub fn save(&self, path: impl AsRef<Path>) -> Result<(), HostError> {
        let json = serde_json::to_string_pretty(self).map_err(|e| HostError::Io(e.to_string()))?;
        std::fs::write(path, json).map_err(|e| HostError::Io(e.to_string()))
    }

    /// Load a registry from `path` (or a fresh empty one if it does not exist).
    pub fn load(path: impl AsRef<Path>) -> Result<AgentHostRegistry, HostError> {
        let path = path.as_ref();
        if !path.exists() {
            return Ok(AgentHostRegistry::new());
        }
        let raw = std::fs::read_to_string(path).map_err(|e| HostError::Io(e.to_string()))?;
        serde_json::from_str(&raw).map_err(|e| HostError::Io(e.to_string()))
    }
}

/// Validate the parts of an enrolment and build the record.
fn validate(
    account: String,
    ssh_pubkey: String,
    budget_cents: i64,
    caps: String,
    brain: String,
    confinement: dregg_agent::session::Confinement,
) -> Result<AccountRecord, HostError> {
    if account.trim().is_empty() {
        return Err(HostError::EmptyAccount);
    }
    if budget_cents <= 0 {
        return Err(HostError::BadBudget(budget_cents));
    }
    if !looks_like_ssh_key(&ssh_pubkey) {
        return Err(HostError::BadSshKey);
    }
    // Validate the caps against the REAL grant vocabulary (the same parser the
    // session itself uses) UNDER THE HOST'S CONFINEMENT POSTURE, so a bad bundle —
    // or a `shell` cap on a host without per-tenant OS isolation — is rejected at
    // enrol, not at login.
    dregg_agent::session::parse_caps_confined(
        &caps,
        "agent:session",
        budget_cents,
        "/workdir",
        confinement,
    )
    .map_err(|reason| HostError::BadCaps {
        caps: caps.clone(),
        reason,
    })?;
    Ok(AccountRecord {
        account: account.trim().to_string(),
        ssh_pubkey: ssh_pubkey.trim().to_string(),
        budget_cents,
        caps,
        brain: brain.trim().to_string(),
    })
}

/// A minimal SSH public-key shape check: `type base64blob [comment]`, the type a
/// known key algorithm and the blob non-empty. Not a cryptographic validation —
/// the sshd does that; this catches obvious enrol-time fat-fingers.
fn looks_like_ssh_key(s: &str) -> bool {
    let s = s.trim();
    let mut parts = s.split_whitespace();
    let (Some(kind), Some(blob)) = (parts.next(), parts.next()) else {
        return false;
    };
    const KINDS: &[&str] = &[
        "ssh-ed25519",
        "ssh-rsa",
        "ecdsa-sha2-nistp256",
        "ecdsa-sha2-nistp384",
        "ecdsa-sha2-nistp521",
        "sk-ssh-ed25519@openssh.com",
        "sk-ecdsa-sha2-nistp256@openssh.com",
    ];
    KINDS.contains(&kind) && blob.len() >= 16 && blob.bytes().all(|b| b != b'"')
}

/// Normalize an SSH key to its identity (type + blob), dropping the comment, so
/// re-enrol / lookup match regardless of the trailing comment.
fn normalize_key(s: &str) -> String {
    let mut parts = s.split_whitespace();
    match (parts.next(), parts.next()) {
        (Some(kind), Some(blob)) => format!("{kind} {blob}"),
        _ => s.trim().to_string(),
    }
}

/// Single-quote a value for the forced command (the command runs under the user's
/// login shell). A value containing `'` is wrapped with the `'\''` idiom. Our
/// values (account ids, caps tokens, brain names) are tame, but quote defensively.
fn shell_quote(s: &str) -> String {
    if !s.is_empty()
        && s.bytes()
            .all(|b| b.is_ascii_alphanumeric() || b":._/-,@".contains(&b))
    {
        return s.to_string();
    }
    format!("'{}'", s.replace('\'', "'\\''"))
}

#[cfg(test)]
mod tests {
    use super::*;

    const ALICE_KEY: &str = "ssh-ed25519 AAAAC3NzaC1lZDI1NTE5AAAAIAlIcEoZ1ENESf0Kk6zc8alICEforAlIcEkeyblob alice@laptop";
    const BOB_KEY: &str =
        "ssh-ed25519 AAAAC3NzaC1lZDI1NTE5AAAAIBobBobBobBobBobBobBobBobBobBobBobBobBobx bob@desktop";

    #[test]
    fn enrol_validates_and_emits_a_scoped_forced_command() {
        let mut reg = AgentHostRegistry::new();
        // Hosted default: the lexically-confined bundle (NO raw shell).
        reg.enroll("dga1_alice", ALICE_KEY, 500, "fs,http:api.github.com")
            .unwrap();

        let ak = reg.authorized_keys();
        // The forced command scopes to THIS account + budget + caps.
        assert!(ak.contains("dregg-agent attach --account dga1_alice --budget 500"));
        assert!(ak.contains("--caps fs,http:api.github.com"));
        // The hosted forced command carries NO raw shell (the critical fix) and no
        // --os-isolation flag (no jail declared).
        assert!(
            !ak.contains("--caps shell"),
            "no raw shell on the hosted line"
        );
        assert!(
            !ak.contains("--os-isolation"),
            "no jail declared by default"
        );
        // The session is locked down to the REPL (no host shell, no forwarding).
        assert!(ak.contains("command=\""), "no forced command");
        assert!(ak.contains(",restrict,pty "), "not locked down");
        // The user's key rides at the end of the line.
        assert!(ak.contains("alice@laptop"));
    }

    // ── THE CRITICAL: a `shell` cap is ALWAYS refused at enrol (hosted) ───────
    #[test]
    fn a_shell_cap_is_refused_at_enrol() {
        let mut reg = AgentHostRegistry::new();
        let err = reg
            .enroll("dga1_alice", ALICE_KEY, 500, "shell,fs")
            .expect_err("a hosted box must refuse the shell cap");
        match err {
            HostError::BadCaps { reason, .. } => {
                assert!(reason.contains("shell"), "the reason names the shell cap");
            }
            other => panic!("expected BadCaps, got {other:?}"),
        }
        assert!(reg.records().is_empty(), "nothing enrolled");
    }

    // ── the decorative `--os-isolation` flag is GONE — no forced command ever
    // carries it, and there is no posture under which a hosted `shell` is granted.
    // The per-tenant jail (isolation.rs) is not yet wired into any run path, so a
    // hosted session is always shell-disabled. ─────────────────────────────────
    #[test]
    fn no_forced_command_ever_carries_the_os_isolation_flag() {
        let mut reg = AgentHostRegistry::new();
        reg.enroll("dga1_alice", ALICE_KEY, 500, "fs,http:api.github.com")
            .unwrap();
        let ak = reg.authorized_keys();
        assert!(
            !ak.contains("--os-isolation"),
            "the decorative isolation flag is never emitted"
        );
        // And a shell cap remains refused regardless of how the registry is built.
        assert!(
            reg.enroll("dga1_bob", BOB_KEY, 500, "shell,fs").is_err(),
            "a hosted shell is always refused"
        );
    }

    // ── the per-account session quota bounds the exhaustion vector ────────────
    #[test]
    fn a_per_account_session_quota_is_enforced() {
        let mut reg = AgentHostRegistry::new();
        // Enrol up to the ceiling under one account (distinct keys per session).
        for i in 0..DEFAULT_SESSIONS_PER_ACCOUNT {
            let key = format!("ssh-ed25519 AAAAC3NzaC1lZDI1NTE5AAAAIQuota{i:034}key quota{i}@host");
            reg.enroll("dga1_quota", &key, 100, "fs").unwrap();
        }
        // One more for the SAME account is refused.
        let over = format!(
            "ssh-ed25519 AAAAC3NzaC1lZDI1NTE5AAAAIQuotaOVERoverOVERoverOVERoverover over@host"
        );
        assert!(matches!(
            reg.enroll("dga1_quota", &over, 100, "fs"),
            Err(HostError::QuotaExceeded { .. })
        ));
        // A DIFFERENT account is unaffected by the first account's quota.
        reg.enroll("dga1_other", &over, 100, "fs").unwrap();
    }

    #[test]
    fn a_bad_caps_bundle_is_rejected_at_enrol() {
        let mut reg = AgentHostRegistry::new();
        // Caps validation runs the real parser; an empty bundle is fine, but a
        // budget <= 0 is rejected, and an obviously broken key is rejected.
        assert!(matches!(
            reg.enroll("dga1_x", ALICE_KEY, 0, "shell"),
            Err(HostError::BadBudget(0))
        ));
        assert!(matches!(
            reg.enroll("dga1_x", "not-a-key", 100, "shell"),
            Err(HostError::BadSshKey)
        ));
        assert!(matches!(
            reg.enroll("", ALICE_KEY, 100, "shell"),
            Err(HostError::EmptyAccount)
        ));
    }

    #[test]
    fn two_users_get_two_isolated_scoped_lines() {
        let mut reg = AgentHostRegistry::new();
        reg.enroll("dga1_alice", ALICE_KEY, 200, "fs").unwrap();
        reg.enroll("dga1_bob", BOB_KEY, 5000, "fs,pay:openai")
            .unwrap();

        let ak = reg.authorized_keys();
        let lines: Vec<&str> = ak.lines().filter(|l| l.starts_with("command=")).collect();
        assert_eq!(lines.len(), 2, "one forced-command line per user");

        // Each line scopes to its OWN account + budget + caps — the isolation is in
        // the construction (each lands in its own confined session).
        let alice = lines.iter().find(|l| l.contains("dga1_alice")).unwrap();
        let bob = lines.iter().find(|l| l.contains("dga1_bob")).unwrap();
        assert!(alice.contains("--budget 200") && alice.contains("--caps fs"));
        assert!(!alice.contains("pay:openai"), "alice has no pay cap");
        assert!(bob.contains("--budget 5000") && bob.contains("pay:openai"));
    }

    #[test]
    fn duplicate_key_is_rejected_but_upsert_replaces() {
        let mut reg = AgentHostRegistry::new();
        reg.enroll("dga1_alice", ALICE_KEY, 200, "fs").unwrap();
        // Same key (even with a different trailing comment) → duplicate.
        let same_key_diff_comment = "ssh-ed25519 AAAAC3NzaC1lZDI1NTE5AAAAIAlIcEoZ1ENESf0Kk6zc8alICEforAlIcEkeyblob alice@phone";
        assert!(matches!(
            reg.enroll("dga1_alice2", same_key_diff_comment, 200, "fs"),
            Err(HostError::DuplicateKey)
        ));
        // Upsert replaces the budget/caps for that identity.
        reg.upsert(
            "dga1_alice",
            ALICE_KEY,
            999,
            "fs,http:api.github.com",
            "hermes",
        )
        .unwrap();
        assert_eq!(reg.records().len(), 1);
        let r = reg.find_by_key(ALICE_KEY).unwrap();
        assert_eq!(r.budget_cents, 999);
        assert_eq!(r.brain, "hermes");
        // The brain rides into the forced command.
        assert!(reg.authorized_keys().contains("--brain hermes"));
    }

    #[test]
    fn registry_round_trips_through_disk() {
        let dir = tempfile::tempdir().unwrap();
        let path = dir.path().join("registry.json");
        let mut reg = AgentHostRegistry::new().with_attach_bin("/usr/local/bin/dregg-agent");
        reg.enroll("dga1_alice", ALICE_KEY, 200, "fs").unwrap();
        reg.enroll("dga1_bob", BOB_KEY, 5000, "fs,http:api.github.com")
            .unwrap();
        reg.save(&path).unwrap();

        let loaded = AgentHostRegistry::load(&path).unwrap();
        assert_eq!(loaded.records(), reg.records());
        assert_eq!(loaded.attach_bin(), "/usr/local/bin/dregg-agent");
        assert!(
            loaded
                .authorized_keys()
                .contains("/usr/local/bin/dregg-agent attach")
        );
        // Revoke removes by key identity.
        let mut loaded = loaded;
        assert!(loaded.revoke(BOB_KEY).is_some());
        assert_eq!(loaded.records().len(), 1);
        assert!(loaded.find_by_account("dga1_bob").is_none());
    }
}
