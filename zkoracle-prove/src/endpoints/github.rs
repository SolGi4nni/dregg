//! **The GitHub commit oracle** — prove a public commit fact trustlessly.
//!
//! `GET https://api.github.com/repos/{owner}/{repo}/commits/{sha}` needs no auth; the
//! zkOracle attestation certifies that the response is a genuine `api.github.com` TLS
//! session (authentic) whose body is well-formed JSON (real CFG parse certificate) bound to
//! ONE response (the cross-leg content commitment), and that the returned commit matches the
//! requested `{sha}`. The extracted [`GithubCommitFact`] is: the commit `sha` exists, by
//! `{author}`, at `{date}`, with `{message}`.
//!
//! ## The injection-free leg is N/A here
//!
//! The injection-free leg guards a USER-SUPPLIED field against the `{{` handlebars breakout
//! before it is spliced into a prompt template. A read-only commit lookup has no such field,
//! so this endpoint attests with an EMPTY field: the leg is vacuously satisfied and the
//! honest teeth are authentic ∧ well-formed ∧ weld ∧ the sha cross-check. (A consumer that
//! wants to splice the commit `{message}` into a prompt can run the same injection leg over
//! it — the machinery is shared — but that is the consumer's policy, not this fact.)

use serde::Deserialize;

use crate::attestation::{ProveError, ZkOracleAttestation, prove_zkoracle, verify_zkoracle};
use crate::authentic::{EndpointConfig, EndpointPresentation, EndpointSpec};
use crate::endpoints::request_target;

/// The pinned GitHub API host.
pub const GITHUB_SERVER_NAME: &str = "api.github.com";

/// **The GitHub commit endpoint spec** — pin `api.github.com`, `GET`, no secret header
/// (public, read-only). A new endpoint is exactly this: DATA.
pub fn github_commit_spec() -> EndpointSpec {
    EndpointSpec {
        id: "github-commit".to_string(),
        server_name: GITHUB_SERVER_NAME.to_string(),
        method: "GET".to_string(),
        secret_header: None,
    }
}

/// The request path for a commit lookup: `/repos/{owner}/{repo}/commits/{sha}`.
pub fn github_commit_path(owner: &str, repo: &str, sha: &str) -> String {
    format!("/repos/{owner}/{repo}/commits/{sha}")
}

/// A verified GitHub commit fact — what the attestation authenticates about the commit.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct GithubCommitFact {
    /// The repository owner (from the authenticated request target).
    pub owner: String,
    /// The repository name (from the authenticated request target).
    pub repo: String,
    /// The commit hash (the top-level `sha` of the response; equals the requested sha).
    pub sha: String,
    /// The commit author name (`commit.author.name`).
    pub author: String,
    /// The authoring date (`commit.author.date`, ISO-8601).
    pub date: String,
    /// The commit message (`commit.message`).
    pub message: String,
}

/// Why a GitHub commit attestation is refused.
#[derive(Clone, Debug)]
pub enum GithubError {
    /// The underlying zkOracle attestation (authentic / well-formed / weld) refused.
    NotVerified(crate::attestation::ZkOracleError),
    /// The authenticated request target is not a `/repos/{owner}/{repo}/commits/{sha}` path.
    BadRequestTarget { got: String },
    /// The response body is not the expected GitHub commit schema.
    BadSchema { reason: String },
    /// The response's commit `sha` does not match the requested `sha` — the response is
    /// about a DIFFERENT commit than asked for.
    ShaMismatch { requested: String, got: String },
}

impl core::fmt::Display for GithubError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            GithubError::NotVerified(e) => write!(f, "github attestation not verified: {e}"),
            GithubError::BadRequestTarget { got } => {
                write!(
                    f,
                    "authenticated request target {got:?} is not a commit path"
                )
            }
            GithubError::BadSchema { reason } => write!(f, "github commit schema: {reason}"),
            GithubError::ShaMismatch { requested, got } => write!(
                f,
                "response sha {got:?} does not match requested sha {requested:?}"
            ),
        }
    }
}

impl std::error::Error for GithubError {}

// The response schema (the disclosed fields we authenticate).
#[derive(Deserialize)]
struct CommitAuthor {
    name: String,
    date: String,
}
#[derive(Deserialize)]
struct CommitObject {
    author: CommitAuthor,
    message: String,
}
#[derive(Deserialize)]
struct CommitResponse {
    sha: String,
    commit: CommitObject,
}

/// A canned but realistic GitHub commit response body (the disclosed evidence). Used by the
/// fixture path and tests; the live body has the same schema, more fields.
pub fn github_commit_body(sha: &str, author: &str, date: &str, message: &str) -> String {
    // serde_json builds a valid JSON body (proper string escaping for the message).
    serde_json::json!({
        "sha": sha,
        "commit": {
            "author": { "name": author, "email": "noreply@example.com", "date": date },
            "committer": { "name": author, "email": "noreply@example.com", "date": date },
            "message": message,
        },
        "html_url": format!("https://github.com/example/{sha}"),
    })
    .to_string()
}

/// **PRODUCE a GitHub commit attestation** from a presentation of the commit session.
///
/// The injection-free leg is n/a (empty field); the attestation's teeth are authentic ∧
/// well-formed ∧ the cross-leg weld. Returns a [`ZkOracleAttestation`] that
/// [`verify_github_commit`] accepts (and forgeries reject).
pub fn prove_github_commit(
    presentation: EndpointPresentation,
    config: &EndpointConfig,
) -> Result<ZkOracleAttestation, ProveError> {
    // Read-only fact: no user field. The empty field is a committed (zero-length) substring
    // of the body at offset 0, trivially injection-free.
    prove_zkoracle(presentation, Vec::new(), config)
}

/// **VERIFY a GitHub commit attestation** → the [`GithubCommitFact`].
///
/// Runs the full [`verify_zkoracle`] (authentic + well-formed + weld), parses `owner`/`repo`
/// /`sha` from the authenticated request target, parses `author`/`date`/`message`/`sha` from
/// the authenticated response body, and cross-checks the two `sha`s agree — so the response
/// is provably about the commit that was asked for.
pub fn verify_github_commit(
    att: &ZkOracleAttestation,
    config: &EndpointConfig,
) -> Result<GithubCommitFact, GithubError> {
    let verified = verify_zkoracle(att, config).map_err(GithubError::NotVerified)?;

    // owner/repo/sha from the authenticated request target.
    let target = request_target(&att.presentation.sent)
        .ok_or_else(|| GithubError::BadRequestTarget { got: String::new() })?;
    let (owner, repo, requested_sha) =
        parse_commit_target(&target).ok_or_else(|| GithubError::BadRequestTarget {
            got: target.clone(),
        })?;

    // author/date/message/sha from the authenticated response body.
    let parsed: CommitResponse =
        serde_json::from_slice(&verified.session.response_body).map_err(|e| {
            GithubError::BadSchema {
                reason: e.to_string(),
            }
        })?;

    // The response must be about the commit that was requested.
    if parsed.sha != requested_sha {
        return Err(GithubError::ShaMismatch {
            requested: requested_sha,
            got: parsed.sha,
        });
    }

    Ok(GithubCommitFact {
        owner,
        repo,
        sha: parsed.sha,
        author: parsed.commit.author.name,
        date: parsed.commit.author.date,
        message: parsed.commit.message,
    })
}

/// Parse `/repos/{owner}/{repo}/commits/{sha}` → `(owner, repo, sha)`.
fn parse_commit_target(target: &str) -> Option<(String, String, String)> {
    let segs: Vec<&str> = target.trim_start_matches('/').split('/').collect();
    // ["repos", owner, repo, "commits", sha]
    if segs.len() == 5 && segs[0] == "repos" && segs[3] == "commits" {
        Some((
            segs[1].to_string(),
            segs[2].to_string(),
            segs[4].to_string(),
        ))
    } else {
        None
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::attestation::ZkOracleError;
    use crate::authentic::{AuthenticError, EndpointConfig, FixtureNotary, build_endpoint_fixture};

    const SHA: &str = "6dcb09b5b57875f334f61aebed695e2e4193db5e";
    const AUTHOR: &str = "Monalisa Octocat";
    const DATE: &str = "2011-04-14T16:00:49Z";
    const MESSAGE: &str = "Fix all the bugs";

    fn setup() -> (FixtureNotary, EndpointConfig, EndpointPresentation) {
        let notary = FixtureNotary::from_seed(&[71u8; 32]);
        let spec = github_commit_spec();
        let config = EndpointConfig::new(spec.clone(), notary.verifying_key());
        let body = github_commit_body(SHA, AUTHOR, DATE, MESSAGE);
        let path = github_commit_path("octocat", "hello-world", SHA);
        let pres = build_endpoint_fixture(&notary, &spec, &path, &body, 1_700_000_100);
        (notary, config, pres)
    }

    /// THE DELIVERABLE — a genuine public GitHub commit session verifies to the fact.
    #[test]
    fn github_commit_attestation_verifies_to_the_fact() {
        let (_n, config, pres) = setup();
        let att = prove_github_commit(pres, &config).expect("commit attestation");
        let fact = verify_github_commit(&att, &config).expect("verifies");
        assert_eq!(fact.owner, "octocat");
        assert_eq!(fact.repo, "hello-world");
        assert_eq!(fact.sha, SHA);
        assert_eq!(fact.author, AUTHOR);
        assert_eq!(fact.date, DATE);
        assert_eq!(fact.message, MESSAGE);
    }

    /// A FORGED/tampered session (a flipped authenticated body byte) is refused — the
    /// notary signature breaks.
    #[test]
    fn tampered_session_is_refused() {
        let (_n, config, mut pres) = setup();
        let k = pres.recv.len() - 6;
        pres.recv[k] ^= 0xFF;
        let att = ZkOracleAttestation {
            presentation: pres.clone(),
            cfg_cert: crate::cfg::prove_cfg_compact(
                &github_commit_body(SHA, AUTHOR, DATE, MESSAGE).into_bytes(),
            )
            .unwrap(),
            field_span: crate::attestation::FieldSpan { offset: 0, len: 0 },
            content_commit: crate::attestation::content_commitment(
                github_commit_body(SHA, AUTHOR, DATE, MESSAGE).as_bytes(),
            ),
            zk_injection: None,
            tlsn_presentation: None,
        };
        assert!(matches!(
            verify_github_commit(&att, &config),
            Err(GithubError::NotVerified(ZkOracleError::NotAuthentic(
                AuthenticError::BadNotarySignature
            )))
        ));
    }

    /// A WRONG-COMMIT response (the body is a genuine session but for a DIFFERENT sha than
    /// the request asked for) is refused by the sha cross-check.
    #[test]
    fn wrong_commit_hash_is_refused() {
        let notary = FixtureNotary::from_seed(&[72u8; 32]);
        let spec = github_commit_spec();
        let config = EndpointConfig::new(spec.clone(), notary.verifying_key());
        // The request asks for SHA; the response authenticates a different sha.
        let other_sha = "0000000000000000000000000000000000000000";
        let body = github_commit_body(other_sha, AUTHOR, DATE, MESSAGE);
        let path = github_commit_path("octocat", "hello-world", SHA);
        let pres = build_endpoint_fixture(&notary, &spec, &path, &body, 1);
        let att = prove_github_commit(pres, &config).expect("attestation (authentic body)");
        assert!(matches!(
            verify_github_commit(&att, &config),
            Err(GithubError::ShaMismatch { .. })
        ));
    }

    /// A MALFORMED body yields no CFG certificate — the well-formed leg refuses.
    #[test]
    fn malformed_body_is_refused() {
        let notary = FixtureNotary::from_seed(&[73u8; 32]);
        let spec = github_commit_spec();
        let config = EndpointConfig::new(spec.clone(), notary.verifying_key());
        let malformed = r#"{"sha":"abc","commit":{"author":"#; // truncated
        let path = github_commit_path("octocat", "hello-world", "abc");
        let pres = build_endpoint_fixture(&notary, &spec, &path, malformed, 1);
        assert!(matches!(
            prove_github_commit(pres, &config),
            Err(ProveError::NotWellFormed(_))
        ));
    }

    /// The wrong server pin is refused (a session with a non-GitHub host).
    #[test]
    fn wrong_server_is_refused() {
        let (notary, config, mut pres) = setup();
        pres.server_name = "evil.example.com".to_string();
        let resigned = notary.sign(pres);
        let att = prove_github_commit(resigned, &config);
        assert!(matches!(att, Err(ProveError::NotAuthentic(_))));
    }
}
