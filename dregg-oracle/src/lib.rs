//! **dregg-oracle** — trustless web facts you can reuse.
//!
//! [`prove`] runs a genuine MPC-TLS 2PC session against a real HTTPS endpoint and
//! returns a [`ProofEnvelope`] — a *portable* proof (the real `tlsn` presentation
//! bytes + the pinned notary key) that anyone can re-check with [`verify_envelope`],
//! trusting only the endpoint's genuine TLS cert chain + the pinned notary key.
//!
//! The portable proof carries ONLY the authenticated evidence; verification
//! re-derives the zkOracle legs (well-formed CFG certificate, injection-free) over
//! the authenticated body and runs the genuine verifier fail-closed.

use anyhow::{anyhow, bail, Context, Result};
use serde::{Deserialize, Serialize};

/// A public web fact to prove.
#[derive(Clone)]
pub enum Endpoint {
    /// Coinbase spot price for a pair, e.g. `BTC-USD`.
    Coinbase { asset: String },
    /// A GitHub commit.
    Github {
        owner: String,
        repo: String,
        sha: String,
    },
    /// Any public HTTPS JSON GET — prove a field of the response.
    Url {
        host: String,
        path: String,
        field: String,
    },
}

impl Endpoint {
    pub fn server_name(&self) -> &'static str {
        match self {
            Endpoint::Coinbase { .. } => "api.coinbase.com",
            Endpoint::Github { .. } => "api.github.com",
            Endpoint::Url { .. } => "the pinned host",
        }
    }

    pub fn label(&self) -> String {
        match self {
            Endpoint::Coinbase { asset } => format!("coinbase spot {asset}"),
            Endpoint::Github { owner, repo, sha } => format!("github {owner}/{repo}@{sha}"),
            Endpoint::Url { host, path, field } => format!("{host}{path} · {field}"),
        }
    }

    fn tag(&self) -> EndpointTag {
        match self {
            Endpoint::Coinbase { asset } => EndpointTag::Coinbase {
                asset: asset.clone(),
            },
            Endpoint::Github { owner, repo, sha } => EndpointTag::Github {
                owner: owner.clone(),
                repo: repo.clone(),
                sha: sha.clone(),
            },
            Endpoint::Url { host, path, field } => EndpointTag::Url {
                host: host.clone(),
                path: path.clone(),
                field: field.clone(),
            },
        }
    }
}

/// Serde-friendly endpoint tag stored in the portable proof.
#[derive(Serialize, Deserialize, Clone)]
#[serde(tag = "kind", rename_all = "snake_case")]
pub enum EndpointTag {
    Coinbase {
        asset: String,
    },
    Github {
        owner: String,
        repo: String,
        sha: String,
    },
    /// Any public HTTPS JSON GET — prove a field of the response.
    Url {
        host: String,
        path: String,
        field: String,
    },
}

impl EndpointTag {
    pub fn label(&self) -> String {
        match self {
            EndpointTag::Coinbase { asset } => format!("coinbase spot {asset}"),
            EndpointTag::Github { owner, repo, sha } => format!("github {owner}/{repo}@{sha}"),
            EndpointTag::Url { host, path, field } => format!("{host}{path} · {field}"),
        }
    }
}

/// The portable proof — self-describing JSON anyone can re-verify.
#[derive(Serialize, Deserialize)]
pub struct ProofEnvelope {
    /// Format tag.
    pub scheme: String,
    /// The pinned HTTPS server this proof is about.
    pub server: String,
    /// The authentication carrier (a real tlsn MPC-TLS 2PC presentation).
    pub carrier: String,
    /// Which fact.
    pub endpoint: EndpointTag,
    /// The tool + version that produced this proof.
    pub tool: String,
    /// Hex of the bincode `tlsn` `Presentation` (the real cryptographic evidence).
    pub presentation_hex: String,
    /// Hex of the bincode notary `VerifyingKey` this proof pins to.
    pub notary_key_hex: String,
}

impl ProofEnvelope {
    pub fn to_json(&self) -> Result<String> {
        serde_json::to_string_pretty(self).context("serialize proof")
    }
    pub fn from_json(s: &str) -> Result<ProofEnvelope> {
        let env: ProofEnvelope = serde_json::from_str(s).context("parse proof json")?;
        if env.scheme != SCHEME {
            bail!("unknown proof scheme {:?} (expected {SCHEME})", env.scheme);
        }
        Ok(env)
    }
}

const SCHEME: &str = "dregg-oracle/1";
const TOOL: &str = concat!("dregg-oracle ", env!("CARGO_PKG_VERSION"));
const TRUST_NOTE: &str = "trustless: a self-hosted tlsn notary co-witnessed the MPC-TLS 2PC session (it saw no plaintext); verification re-derives the well-formed + injection-free legs over the authenticated body. You trust only the pinned server's genuine TLS cert chain + the pinned notary key.";

/// The verified fact a proof attests.
pub struct Attested {
    pub value: String,
    pub endpoint: String,
    pub server_pinned: String,
    pub carrier: String,
    pub time: u64,
    /// The verification legs that held. Verification is fail-closed, so every
    /// entry here is a property the genuine verifier enforced before returning.
    pub legs: Vec<Leg>,
    pub trust_note: String,
}

/// One verification leg that held.
pub struct Leg {
    /// Short name, e.g. `authentic`, `well-formed`, `injection-free`.
    pub name: &'static str,
    /// Human-readable detail of what was checked.
    pub detail: String,
}

#[cfg(feature = "live")]
impl Leg {
    fn new(name: &'static str, detail: impl Into<String>) -> Leg {
        Leg {
            name,
            detail: detail.into(),
        }
    }
}

/// The transport-bound legs every dregg-oracle proof re-derives over the
/// authenticated body (all three held whenever verification returns `Ok`).
#[cfg(feature = "live")]
fn transport_legs() -> Vec<Leg> {
    vec![
        Leg::new(
            "authentic",
            "MPC-TLS 2PC presentation verified against the pinned notary key and the server's genuine TLS cert chain",
        ),
        Leg::new(
            "well-formed",
            "the authenticated response body carries a JSON CFG parse certificate",
        ),
        Leg::new(
            "injection-free",
            "no control-plane injection over the authenticated bytes",
        ),
    ]
}

// ── prove ────────────────────────────────────────────────────────────────────

#[cfg(feature = "live")]
pub fn prove(ep: &Endpoint) -> Result<ProofEnvelope> {
    match ep {
        Endpoint::Coinbase { asset } => {
            let (pres, key) =
                dregg_zkoracle_prove::endpoints::price::prove_coinbase_portable(asset)
                    .map_err(|e| anyhow!("live proof failed: {e:?}"))?;
            Ok(ProofEnvelope {
                scheme: SCHEME.to_string(),
                server: "api.coinbase.com".to_string(),
                carrier: "live-mpc-tls (tlsn 2PC, self-hosted notary)".to_string(),
                endpoint: ep.tag(),
                tool: TOOL.to_string(),
                presentation_hex: hex::encode(&pres),
                notary_key_hex: hex::encode(&key),
            })
        }
        Endpoint::Github { owner, repo, sha } => {
            let (pres, key) =
                dregg_zkoracle_prove::endpoints::github::prove_github_portable(owner, repo, sha)
                    .map_err(|e| anyhow!("live github proof failed: {e:?}"))?;
            Ok(ProofEnvelope {
                scheme: SCHEME.to_string(),
                server: "api.github.com".to_string(),
                carrier: "live-mpc-tls (tlsn 2PC, self-hosted notary)".to_string(),
                endpoint: ep.tag(),
                tool: TOOL.to_string(),
                presentation_hex: hex::encode(&pres),
                notary_key_hex: hex::encode(&key),
            })
        }
        Endpoint::Url { host, path, .. } => {
            let (pres, key) =
                dregg_zkoracle_prove::endpoints::generic::prove_url_portable(host, path)
                    .map_err(|e| anyhow!("live url proof failed: {e:?}"))?;
            Ok(ProofEnvelope {
                scheme: SCHEME.to_string(),
                server: host.clone(),
                carrier: "live-mpc-tls (tlsn 2PC, self-hosted notary)".to_string(),
                endpoint: ep.tag(),
                tool: TOOL.to_string(),
                presentation_hex: hex::encode(&pres),
                notary_key_hex: hex::encode(&key),
            })
        }
    }
}

#[cfg(not(feature = "live"))]
pub fn prove(_ep: &Endpoint) -> Result<ProofEnvelope> {
    bail!("built without the `live` feature — rebuild with `--features live` to prove")
}

// ── verify ───────────────────────────────────────────────────────────────────

pub fn verify_envelope(env: &ProofEnvelope) -> Result<Attested> {
    match &env.endpoint {
        EndpointTag::Coinbase { .. } => verify_coinbase(env),
        EndpointTag::Github { .. } => verify_github(env),
        EndpointTag::Url { .. } => verify_url(env),
    }
}

#[cfg(feature = "live")]
fn verify_coinbase(env: &ProofEnvelope) -> Result<Attested> {
    let pres = hex::decode(&env.presentation_hex).context("decode presentation hex")?;
    let key = hex::decode(&env.notary_key_hex).context("decode notary key hex")?;
    let price = dregg_zkoracle_prove::endpoints::price::verify_coinbase_portable_bytes(&pres, &key)
        .map_err(|e| anyhow!("VERIFY FAILED (fail-closed): {e:?}"))?;
    Ok(Attested {
        value: format!("{} = {}", price.asset, price.amount),
        endpoint: "coinbase spot price".to_string(),
        server_pinned: env.server.clone(),
        carrier: env.carrier.clone(),
        time: price.time,
        legs: transport_legs(),
        trust_note: TRUST_NOTE.to_string(),
    })
}

#[cfg(not(feature = "live"))]
fn verify_coinbase(_env: &ProofEnvelope) -> Result<Attested> {
    bail!("built without `live` — rebuild with `--features live` to verify a live-carrier proof")
}

#[cfg(feature = "live")]
fn verify_github(env: &ProofEnvelope) -> Result<Attested> {
    let pres = hex::decode(&env.presentation_hex).context("decode presentation hex")?;
    let key = hex::decode(&env.notary_key_hex).context("decode notary key hex")?;
    let fact = dregg_zkoracle_prove::endpoints::github::verify_github_portable_bytes(&pres, &key)
        .map_err(|e| anyhow!("VERIFY FAILED (fail-closed): {e:?}"))?;
    let short = &fact.sha[..fact.sha.len().min(12)];
    let subject = fact.message.lines().next().unwrap_or("").trim();
    Ok(Attested {
        value: format!("{}/{}@{short} \u{2014} {subject}", fact.owner, fact.repo),
        endpoint: format!("github commit (by {}, {})", fact.author, fact.date),
        server_pinned: env.server.clone(),
        carrier: env.carrier.clone(),
        time: 0,
        legs: transport_legs(),
        trust_note: TRUST_NOTE.to_string(),
    })
}

#[cfg(not(feature = "live"))]
fn verify_github(_env: &ProofEnvelope) -> Result<Attested> {
    bail!("built without `live` — rebuild with `--features live` to verify a live-carrier proof")
}

#[cfg(feature = "live")]
fn verify_url(env: &ProofEnvelope) -> Result<Attested> {
    let field = match &env.endpoint {
        EndpointTag::Url { field, .. } => field.clone(),
        _ => bail!("not a url proof"),
    };
    let pres = hex::decode(&env.presentation_hex).context("decode presentation hex")?;
    let key = hex::decode(&env.notary_key_hex).context("decode notary key hex")?;
    let body = dregg_zkoracle_prove::endpoints::generic::verify_url_body_portable_bytes(
        &pres,
        &key,
        &env.server,
    )
    .map_err(|e| anyhow!("VERIFY FAILED (fail-closed): {e:?}"))?;
    let value = extract_field(&body, &field)?;
    let mut legs = transport_legs();
    legs.push(Leg::new(
        "field-bound",
        format!("field path '{field}' resolved over the authenticated body"),
    ));
    Ok(Attested {
        value: format!("{field} = {value}"),
        endpoint: format!("{} (json field)", env.server),
        server_pinned: env.server.clone(),
        carrier: env.carrier.clone(),
        time: 0,
        legs,
        trust_note: TRUST_NOTE.to_string(),
    })
}

#[cfg(not(feature = "live"))]
fn verify_url(_env: &ProofEnvelope) -> Result<Attested> {
    bail!("built without `live` — rebuild with `--features live` to verify a live-carrier proof")
}

// ── field extraction ─────────────────────────────────────────────────────────
//
// A dotted path walks object keys, numeric array indices, and `*` wildcards
// (which fan out over every element of an array / every value of an object).
// Guards bound the body size and path depth so a hostile-but-authenticated
// body can't blow the walker up. Errors name the segment and the node type so a
// wrong `--field` is obvious.

/// Max authenticated body we will parse for field extraction (1 MiB).
#[cfg(any(feature = "live", test))]
const MAX_BODY_BYTES: usize = 1 << 20;
/// Max number of dotted path segments we will walk.
#[cfg(any(feature = "live", test))]
const MAX_PATH_DEPTH: usize = 64;

/// Walk a dotted path (object keys, numeric array indices, and `*` wildcards)
/// into a JSON body and render the selected value(s). A wildcard fans out and
/// its matches are joined with `, `. An empty path yields the whole document.
#[cfg(any(feature = "live", test))]
fn extract_field(body: &str, field: &str) -> Result<String> {
    if body.len() > MAX_BODY_BYTES {
        bail!(
            "response body is {} bytes, over the {MAX_BODY_BYTES}-byte extraction guard",
            body.len()
        );
    }
    let v: serde_json::Value = serde_json::from_str(body).context("response body is not JSON")?;
    let segs: Vec<&str> = if field.is_empty() {
        Vec::new()
    } else {
        field.split('.').collect()
    };
    if segs.len() > MAX_PATH_DEPTH {
        bail!(
            "field path '{field}' has {} segments, over the max depth of {MAX_PATH_DEPTH}",
            segs.len()
        );
    }
    let hits = walk(&v, &segs, field)?;
    match hits.as_slice() {
        [] => bail!("field path '{field}' (wildcard) matched no values"),
        [one] => Ok(render_value(one)),
        many => Ok(many
            .iter()
            .map(|x| render_value(x))
            .collect::<Vec<_>>()
            .join(", ")),
    }
}

/// Recursive walker. Decides key-vs-index by the *node* type, so a numeric
/// segment against an object is a key lookup (not a failed array index).
#[cfg(any(feature = "live", test))]
fn walk<'a>(
    cur: &'a serde_json::Value,
    segs: &[&str],
    full: &str,
) -> Result<Vec<&'a serde_json::Value>> {
    let Some((seg, rest)) = segs.split_first() else {
        return Ok(vec![cur]);
    };
    match cur {
        serde_json::Value::Array(items) => {
            if *seg == "*" {
                let mut out = Vec::new();
                for item in items {
                    out.extend(walk(item, rest, full)?);
                }
                Ok(out)
            } else if let Ok(i) = seg.parse::<usize>() {
                let next = items.get(i).ok_or_else(|| {
                    anyhow!(
                        "field path '{full}': index {i} is out of bounds (array has {} element(s))",
                        items.len()
                    )
                })?;
                walk(next, rest, full)
            } else {
                bail!(
                    "field path '{full}': '{seg}' is not an array index (array has {} element(s); use a number or '*')",
                    items.len()
                )
            }
        }
        serde_json::Value::Object(map) => {
            if *seg == "*" {
                let mut out = Vec::new();
                for item in map.values() {
                    out.extend(walk(item, rest, full)?);
                }
                Ok(out)
            } else {
                let next = map.get(*seg).ok_or_else(|| {
                    anyhow!(
                        "field path '{full}': key '{seg}' not found (available keys: {})",
                        object_keys(map)
                    )
                })?;
                walk(next, rest, full)
            }
        }
        other => bail!(
            "field path '{full}': cannot descend into {} with '{seg}'",
            type_name(other)
        ),
    }
}

#[cfg(any(feature = "live", test))]
fn render_value(v: &serde_json::Value) -> String {
    match v {
        serde_json::Value::String(s) => s.clone(),
        other => other.to_string(),
    }
}

#[cfg(any(feature = "live", test))]
fn type_name(v: &serde_json::Value) -> &'static str {
    match v {
        serde_json::Value::Null => "null",
        serde_json::Value::Bool(_) => "boolean",
        serde_json::Value::Number(_) => "number",
        serde_json::Value::String(_) => "string",
        serde_json::Value::Array(_) => "array",
        serde_json::Value::Object(_) => "object",
    }
}

/// A bounded, human-readable list of an object's keys for error messages.
#[cfg(any(feature = "live", test))]
fn object_keys(map: &serde_json::Map<String, serde_json::Value>) -> String {
    let shown: Vec<&str> = map.keys().map(String::as_str).take(16).collect();
    let joined = shown.join(", ");
    if map.len() > shown.len() {
        format!("{joined}, \u{2026}")
    } else {
        joined
    }
}

#[cfg(test)]
mod tests {
    use super::extract_field;

    #[test]
    fn simple_key() {
        assert_eq!(extract_field(r#"{"a":"hi"}"#, "a").unwrap(), "hi");
    }

    #[test]
    fn nested_key() {
        assert_eq!(
            extract_field(r#"{"data":{"priceUsd":"42.5"}}"#, "data.priceUsd").unwrap(),
            "42.5"
        );
    }

    #[test]
    fn number_is_rendered_raw() {
        assert_eq!(extract_field(r#"{"n":42}"#, "n").unwrap(), "42");
    }

    #[test]
    fn array_index() {
        assert_eq!(extract_field(r#"{"xs":[10,20,30]}"#, "xs.1").unwrap(), "20");
    }

    #[test]
    fn array_of_objects() {
        assert_eq!(
            extract_field(r#"{"xs":[{"v":1},{"v":2}]}"#, "xs.1.v").unwrap(),
            "2"
        );
    }

    #[test]
    fn wildcard_over_array() {
        assert_eq!(
            extract_field(r#"{"xs":[{"v":1},{"v":2},{"v":3}]}"#, "xs.*.v").unwrap(),
            "1, 2, 3"
        );
    }

    #[test]
    fn wildcard_over_object_values() {
        // Map order is backend-dependent (BTreeMap vs preserve_order), so sort.
        let out = extract_field(r#"{"m":{"a":"x","b":"y"}}"#, "m.*").unwrap();
        let mut parts: Vec<&str> = out.split(", ").collect();
        parts.sort();
        assert_eq!(parts, vec!["x", "y"]);
    }

    #[test]
    fn numeric_key_on_object() {
        // A numeric segment against an OBJECT is a key lookup, not an index.
        assert_eq!(extract_field(r#"{"123":"ok"}"#, "123").unwrap(), "ok");
    }

    #[test]
    fn empty_path_returns_whole_document() {
        assert_eq!(extract_field(r#"{"a":1}"#, "").unwrap(), r#"{"a":1}"#);
    }

    #[test]
    fn missing_key_errs() {
        let e = extract_field(r#"{"a":1}"#, "b").unwrap_err().to_string();
        assert!(e.contains("key 'b' not found"), "{e}");
        assert!(e.contains("available keys"), "{e}");
    }

    #[test]
    fn index_out_of_bounds_errs() {
        let e = extract_field(r#"{"xs":[1,2]}"#, "xs.5")
            .unwrap_err()
            .to_string();
        assert!(e.contains("out of bounds"), "{e}");
    }

    #[test]
    fn bad_array_index_token_errs() {
        let e = extract_field(r#"{"xs":[1,2]}"#, "xs.foo")
            .unwrap_err()
            .to_string();
        assert!(e.contains("not an array index"), "{e}");
    }

    #[test]
    fn descend_into_scalar_errs() {
        let e = extract_field(r#"{"a":"scalar"}"#, "a.b")
            .unwrap_err()
            .to_string();
        assert!(e.contains("cannot descend into string"), "{e}");
    }

    #[test]
    fn non_json_body_errs() {
        let e = extract_field("not json at all", "a")
            .unwrap_err()
            .to_string();
        assert!(e.contains("not JSON"), "{e}");
    }

    #[test]
    fn body_too_large_errs() {
        let big = format!(r#"{{"a":"{}"}}"#, "x".repeat(2 * 1024 * 1024));
        let e = extract_field(&big, "a").unwrap_err().to_string();
        assert!(e.contains("extraction guard"), "{e}");
    }

    #[test]
    fn path_too_deep_errs() {
        let deep = vec!["a"; 100].join(".");
        let e = extract_field(r#"{"a":1}"#, &deep).unwrap_err().to_string();
        assert!(e.contains("max depth"), "{e}");
    }
}
