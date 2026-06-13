//! # `dregg` — the Python face of the dregg SDK's two-noun surface.
//!
//! ```python
//! import dregg
//!
//! ident = dregg.Identity.from_profile("ember")      # ~/.dregg/profiles, shared with the CLI
//! receipt = (ident.turn("https://devnet.dregg.fg-goose.online")
//!                 .transfer("28c2cba0…", 100)
//!                 .sign()
//!                 .submit())
//! print(receipt.turn_hash, receipt.has_proof)
//!
//! for r in dregg.subscribe(node_url, kind="transfer"):
//!     print(r.turn_hash)
//! ```
//!
//! The shape is the Rust SDK's authorization-first surface, verbatim:
//! `Identity → .turn() → typed verbs → .sign() → .submit() → Receipt`.
//! An unauthorized act is inexpressible here — by the time anything leaves
//! `.sign()` it is a real Ed25519-signed canonical `SignedTurn`, and the
//! node ingress (`POST /api/turns/submit-signed`) verifies it.
//!
//! Refusals raise [`DreggRefused`] carrying the node's reason AND the
//! clerk's faithful explanation of what was signed — the system teaches
//! when it says no.

use std::collections::VecDeque;
use std::io::Read;
use std::time::Duration;

use pyo3::exceptions::{PyKeyError, PyTypeError, PyValueError};
use pyo3::prelude::*;
use pyo3::types::{PyBytes, PyDict, PyList};

use dregg_cell::program::{HashKind, SimpleStateConstraint, StateConstraint};
use dregg_cell::{AuthRequired, CapabilityRef, field_from_u64};
use dregg_sdk::cipherclerk::{AgentCipherclerk, SignedTurn};
use dregg_sdk::explain::{explain_action, explain_turn};
use dregg_sdk::profiles;
use dregg_types::CellId;
use dregg_turn::Effect;

// ─── exceptions ───

pyo3::create_exception!(
    dregg,
    DreggError,
    pyo3::exceptions::PyException,
    "Base error for the dregg SDK (I/O, profile store, node transport)."
);
pyo3::create_exception!(
    dregg,
    DreggRefused,
    DreggError,
    "The system said no — a refusal from the signing surface or the node, \
     carrying the reason and the faithful explanation of what was attempted."
);

fn err(msg: impl Into<String>) -> PyErr {
    DreggError::new_err(msg.into())
}

fn refused(msg: impl Into<String>) -> PyErr {
    DreggRefused::new_err(msg.into())
}

// ─── small codecs ───

/// Accept a 32-byte identifier as a hex `str` or 32-byte `bytes`.
fn parse_32(obj: &Bound<'_, PyAny>, what: &str) -> PyResult<[u8; 32]> {
    if let Ok(s) = obj.extract::<&str>() {
        let bytes = hex::decode(s.trim())
            .map_err(|e| PyValueError::new_err(format!("{what}: invalid hex: {e}")))?;
        return bytes.as_slice().try_into().map_err(|_| {
            PyValueError::new_err(format!("{what}: expected 32 bytes, got {}", bytes.len()))
        });
    }
    if let Ok(b) = obj.extract::<&[u8]>() {
        return b.try_into().map_err(|_| {
            PyValueError::new_err(format!("{what}: expected 32 bytes, got {}", b.len()))
        });
    }
    Err(PyTypeError::new_err(format!(
        "{what}: expected a hex str or 32-byte bytes"
    )))
}

fn parse_cell(obj: &Bound<'_, PyAny>, what: &str) -> PyResult<CellId> {
    Ok(CellId(parse_32(obj, what)?))
}

fn parse_auth_required(s: &str) -> PyResult<AuthRequired> {
    match s.to_ascii_lowercase().as_str() {
        "none" => Ok(AuthRequired::None),
        "signature" => Ok(AuthRequired::Signature),
        "proof" => Ok(AuthRequired::Proof),
        "either" => Ok(AuthRequired::Either),
        "impossible" => Ok(AuthRequired::Impossible),
        other => Err(PyValueError::new_err(format!(
            "permissions: expected one of none/signature/proof/either/impossible, got {other:?}"
        ))),
    }
}

/// serde_json → Python objects (dicts/lists/str/int/float/bool/None).
fn json_to_py<'py>(py: Python<'py>, v: &serde_json::Value) -> PyResult<Bound<'py, PyAny>> {
    Ok(match v {
        serde_json::Value::Null => py.None().into_bound(py),
        serde_json::Value::Bool(b) => b.into_pyobject(py)?.to_owned().into_any(),
        serde_json::Value::Number(n) => {
            if let Some(i) = n.as_i64() {
                i.into_pyobject(py)?.into_any()
            } else if let Some(u) = n.as_u64() {
                u.into_pyobject(py)?.into_any()
            } else {
                n.as_f64().unwrap_or(f64::NAN).into_pyobject(py)?.into_any()
            }
        }
        serde_json::Value::String(s) => s.into_pyobject(py)?.into_any(),
        serde_json::Value::Array(items) => {
            let list = PyList::empty(py);
            for item in items {
                list.append(json_to_py(py, item)?)?;
            }
            list.into_any()
        }
        serde_json::Value::Object(map) => {
            let dict = PyDict::new(py);
            for (k, val) in map {
                dict.set_item(k, json_to_py(py, val)?)?;
            }
            dict.into_any()
        }
    })
}

// ─── blocking HTTP (the binding's own thin transport; no tokio) ───

fn http_agent() -> ureq::Agent {
    ureq::AgentBuilder::new()
        .timeout_connect(Duration::from_secs(10))
        .timeout(Duration::from_secs(30))
        .build()
}

fn get_json(url: &str) -> Result<serde_json::Value, String> {
    let resp = http_agent()
        .get(url)
        .call()
        .map_err(|e| format!("GET {url}: {e}"))?;
    resp.into_json().map_err(|e| format!("GET {url}: {e}"))
}

/// The devnet gate key (operator credential) → sent as both `X-Devnet-Key` and
/// `Authorization: Bearer`. Mirrors the TS `NodeClient.devnetKey`: the
/// signed-turn ingress and the operator-gated organ routes (trustline /
/// channels) are protected behind it on the shared devnet. Resolved from the
/// explicit argument, else `$DREGG_API_TOKEN`.
fn resolve_devnet_key(explicit: Option<&str>) -> Option<String> {
    explicit
        .map(str::to_string)
        .or_else(|| std::env::var("DREGG_API_TOKEN").ok())
        .map(|t| t.trim().to_string())
        .filter(|t| !t.is_empty())
}

fn apply_devnet_key(mut req: ureq::Request, key: Option<&str>) -> ureq::Request {
    if let Some(k) = key {
        req = req
            .set("x-devnet-key", k)
            .set("authorization", &format!("Bearer {k}"));
    }
    req
}

/// `GET {base}{path}` (devnet-keyed) → parsed JSON. The read used by the organ
/// status routes + attested-query.
fn http_get_json(base: &str, path: &str, key: Option<&str>) -> Result<serde_json::Value, String> {
    let url = format!("{}{}", base.trim_end_matches('/'), path);
    let req = apply_devnet_key(http_agent().get(&url), key);
    match req.call() {
        Ok(resp) => resp.into_json().map_err(|e| format!("GET {url}: {e}")),
        Err(ureq::Error::Status(code, resp)) => {
            let text = resp.into_string().unwrap_or_default();
            Err(format!("GET {url}: HTTP {code}: {text}"))
        }
        Err(e) => Err(format!("GET {url}: {e}")),
    }
}

/// `{method} {base}{path}` with a JSON body (devnet-keyed) → parsed JSON. The
/// generic write used by the organ clients (mirrors TS `NodeClient.postJson`).
fn http_send_json(
    method: &str,
    base: &str,
    path: &str,
    body: &serde_json::Value,
    key: Option<&str>,
) -> Result<serde_json::Value, String> {
    let url = format!("{}{}", base.trim_end_matches('/'), path);
    let req = apply_devnet_key(
        http_agent()
            .request(method, &url)
            .set("content-type", "application/json"),
        key,
    );
    let payload = serde_json::to_vec(body).map_err(|e| format!("encode body: {e}"))?;
    match req.send_bytes(&payload) {
        Ok(resp) => resp.into_json().map_err(|e| format!("{method} {url}: {e}")),
        Err(ureq::Error::Status(code, resp)) => {
            let text = resp.into_string().unwrap_or_default();
            Err(format!("{method} {url}: HTTP {code}: {text}"))
        }
        Err(e) => Err(format!("{method} {url}: {e}")),
    }
}

/// The node's executor federation id: `blake3(node operator pubkey)` on a
/// solo/unconfigured node — the same derivation `federation_id_for_executor`
/// uses (and the discord-bot's startup check asserts). Configured
/// multi-member federations pass `federation_id=` explicitly.
fn fetch_federation_id(node_url: &str) -> Result<[u8; 32], String> {
    let v = get_json(&format!("{node_url}/api/node/identity"))?;
    let pk_hex = v
        .get("public_key")
        .and_then(|p| p.as_str())
        .ok_or_else(|| "node identity response missing public_key".to_string())?;
    let pk: [u8; 32] = hex::decode(pk_hex)
        .map_err(|e| format!("node public_key: {e}"))?
        .as_slice()
        .try_into()
        .map_err(|_| "node public_key is not 32 bytes".to_string())?;
    Ok(*blake3::hash(&pk).as_bytes())
}

fn fetch_cell_nonce(node_url: &str, cell_hex: &str) -> u64 {
    get_json(&format!("{node_url}/api/cell/{cell_hex}"))
        .ok()
        .and_then(|v| v.get("nonce").and_then(|n| n.as_u64()))
        .unwrap_or(0)
}

fn post_signed_turn(
    node_url: &str,
    body: &[u8],
    key: Option<&str>,
) -> Result<serde_json::Value, String> {
    let url = format!("{node_url}/api/turns/submit-signed");
    let req = apply_devnet_key(
        http_agent()
            .post(&url)
            .set("content-type", "application/octet-stream"),
        // The shared devnet protects the /api/turns/* ingress behind a bearer;
        // fall back to $DREGG_API_TOKEN when no key was pinned on .turn().
        resolve_devnet_key(key).as_deref(),
    );
    match req.send_bytes(body) {
        Ok(resp) => resp.into_json().map_err(|e| format!("POST {url}: {e}")),
        Err(ureq::Error::Status(code, resp)) => {
            let text = resp.into_string().unwrap_or_default();
            Err(format!("POST {url}: HTTP {code}: {text}"))
        }
        Err(e) => Err(format!("POST {url}: {e}")),
    }
}

fn now_secs() -> i64 {
    std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .map(|d| d.as_secs() as i64)
        .unwrap_or(0)
}

/// Stamped so the wire marshal accepts the envelope and the turn rides the
/// verified Lean producer (mirrors the node's `default_valid_until`).
const TURN_VALIDITY_HORIZON_SECS: i64 = 3600;

// ─── Identity ───

/// A named local identity — an Ed25519 key from the shared `$DREGG_HOME`
/// profile store (`~/.dregg/profiles/<name>.json`, the same files
/// `dregg id create/use` and the Rust SDK read).
#[pyclass(unsendable, module = "dregg")]
struct Identity {
    clerk: AgentCipherclerk,
    name: Option<String>,
}

#[pymethods]
impl Identity {
    /// Load a named profile from the local store.
    #[staticmethod]
    fn from_profile(name: &str) -> PyResult<Self> {
        let clerk = profiles::load(name).map_err(|e| err(e.to_string()))?;
        Ok(Identity {
            clerk,
            name: Some(name.to_string()),
        })
    }

    /// Create a named profile with a fresh random seed (refuses an existing
    /// name) and return its identity. Does not change the active profile.
    #[staticmethod]
    fn create(name: &str) -> PyResult<Self> {
        profiles::create(name).map_err(|e| refused(e.to_string()))?;
        Self::from_profile(name)
    }

    /// The active profile (`DREGG_PROFILE` env override → the persistent
    /// `dregg id use` default). Raises DreggError when none is configured.
    #[staticmethod]
    fn active() -> PyResult<Self> {
        let name = profiles::active_name();
        match profiles::load_active().map_err(|e| err(e.to_string()))? {
            Some(clerk) => Ok(Identity { clerk, name }),
            None => Err(err(
                "no active profile configured — `dregg id create <name> && dregg id use <name>` \
                 (or dregg.Identity.create(name)), or set DREGG_PROFILE",
            )),
        }
    }

    /// The profile name this identity was loaded from (None for `active()`
    /// resolved purely from the env in an edge case, or future anonymous
    /// constructions).
    #[getter]
    fn name(&self) -> Option<String> {
        self.name.clone()
    }

    /// Hex Ed25519 public key.
    #[getter]
    fn public_key(&self) -> String {
        hex::encode(self.clerk.public_key().0)
    }

    /// Hex CellId in the default federation domain — the agent cell this
    /// identity acts and pays as (what the node derives from the signer key).
    #[getter]
    fn cell_id(&self) -> String {
        hex::encode(self.clerk.cell_id("default").0)
    }

    /// Open a turn builder against `node_url`.
    ///
    /// `federation_id` (hex str or 32 bytes) pins the signing domain
    /// explicitly; when omitted, `.sign()` fetches the node's identity and
    /// derives the solo-node executor domain `blake3(node_pubkey)`.
    ///
    /// `devnet_key` is the operator credential for the gated ingress (sent as
    /// `X-Devnet-Key` + `Authorization: Bearer`); when omitted, `.submit()`
    /// falls back to `$DREGG_API_TOKEN`.
    #[pyo3(signature = (node_url, federation_id=None, devnet_key=None))]
    fn turn(
        slf: &Bound<'_, Self>,
        node_url: &str,
        federation_id: Option<&Bound<'_, PyAny>>,
        devnet_key: Option<&str>,
    ) -> PyResult<TurnBuilder> {
        let federation_id = federation_id
            .map(|f| parse_32(f, "federation_id"))
            .transpose()?;
        Ok(TurnBuilder {
            identity: slf.clone().unbind(),
            node_url: node_url.trim_end_matches('/').to_string(),
            method: "execute".to_string(),
            effects: Vec::new(),
            fee: None,
            memo: None,
            nonce: None,
            valid_until: None,
            federation_id,
            devnet_key: devnet_key.map(str::to_string),
        })
    }

    /// The **trustline** organ (`docs/ORGANS.md` §1) bound to `node_url`,
    /// acting as the issuer under this identity's operator credential. See
    /// [`Trustline`].
    #[pyo3(signature = (node_url, devnet_key=None))]
    fn trustline(&self, node_url: &str, devnet_key: Option<&str>) -> Trustline {
        Trustline {
            node_url: node_url.trim_end_matches('/').to_string(),
            devnet_key: devnet_key.map(str::to_string),
        }
    }

    /// The **channels** organ (`docs/ORGANS.md` §4) bound to `node_url`. See
    /// [`Channels`].
    #[pyo3(signature = (node_url, devnet_key=None))]
    fn channels(&self, node_url: &str, devnet_key: Option<&str>) -> Channels {
        Channels {
            node_url: node_url.trim_end_matches('/').to_string(),
            devnet_key: devnet_key.map(str::to_string),
        }
    }

    /// This identity's **mailbox** (`docs/ORGANS.md` §2) on the relay at
    /// `relay_url`. Membership ops are Ed25519-signed by this identity. See
    /// [`Mailbox`].
    fn mailbox(slf: &Bound<'_, Self>, relay_url: &str) -> Mailbox {
        Mailbox {
            identity: slf.clone().unbind(),
            base_url: relay_url.trim_end_matches('/').to_string(),
        }
    }

    fn __repr__(&self) -> String {
        format!(
            "Identity(name={:?}, cell_id={:?})",
            self.name,
            self.cell_id()
        )
    }
}

// ─── TurnBuilder ───

/// The typed verb builder: stage effects, then `.sign()`.
///
/// Every verb returns the builder for chaining. There is no submit on this
/// type — only a signed turn can travel.
#[pyclass(unsendable, module = "dregg")]
struct TurnBuilder {
    identity: Py<Identity>,
    node_url: String,
    method: String,
    effects: Vec<Effect>,
    fee: Option<u64>,
    memo: Option<String>,
    nonce: Option<u64>,
    valid_until: Option<i64>,
    federation_id: Option<[u8; 32]>,
    devnet_key: Option<String>,
}

impl TurnBuilder {
    fn acting_cell(&self, py: Python<'_>) -> CellId {
        self.identity.borrow(py).clerk.cell_id("default")
    }
}

#[pymethods]
impl TurnBuilder {
    /// Transfer `amount` computrons from the acting cell to `to`.
    fn transfer<'py>(
        mut slf: PyRefMut<'py, Self>,
        to: &Bound<'py, PyAny>,
        amount: u64,
    ) -> PyResult<PyRefMut<'py, Self>> {
        let to = parse_cell(to, "to")?;
        let from = slf.acting_cell(slf.py());
        slf.effects.push(Effect::Transfer { from, to, amount });
        Ok(slf)
    }

    /// Transfer with an explicit source cell (must still be within this
    /// identity's authority — the executor checks, not the builder).
    fn transfer_from<'py>(
        mut slf: PyRefMut<'py, Self>,
        from: &Bound<'py, PyAny>,
        to: &Bound<'py, PyAny>,
        amount: u64,
    ) -> PyResult<PyRefMut<'py, Self>> {
        let from = parse_cell(from, "from")?;
        let to = parse_cell(to, "to")?;
        slf.effects.push(Effect::Transfer { from, to, amount });
        Ok(slf)
    }

    /// Write state slot `index` of the acting cell. `value` is an int
    /// (encoded little-endian like the Rust `field_from_u64`) or 32 bytes /
    /// hex (a full field element).
    fn write<'py>(
        mut slf: PyRefMut<'py, Self>,
        index: usize,
        value: &Bound<'py, PyAny>,
    ) -> PyResult<PyRefMut<'py, Self>> {
        let value = if let Ok(n) = value.extract::<u64>() {
            field_from_u64(n)
        } else {
            parse_32(value, "value")?
        };
        let cell = slf.acting_cell(slf.py());
        slf.effects.push(Effect::SetField { cell, index, value });
        Ok(slf)
    }

    /// `write` with a numeric value (explicit-name twin of the Rust verb).
    fn write_u64(mut slf: PyRefMut<'_, Self>, index: usize, value: u64) -> PyRefMut<'_, Self> {
        let cell = slf.acting_cell(slf.py());
        slf.effects.push(Effect::SetField {
            cell,
            index,
            value: field_from_u64(value),
        });
        slf
    }

    /// Grant a capability from the acting cell to `to` (non-amplifying: the
    /// executor admits only grants within held authority). `target` is the
    /// cell the capability points at (defaults to the acting cell);
    /// `permissions` is one of none/signature/proof/either/impossible.
    #[pyo3(signature = (to, target=None, permissions="signature", slot=0, expires_at=None))]
    fn grant<'py>(
        mut slf: PyRefMut<'py, Self>,
        to: &Bound<'py, PyAny>,
        target: Option<&Bound<'py, PyAny>>,
        permissions: &str,
        slot: u32,
        expires_at: Option<u64>,
    ) -> PyResult<PyRefMut<'py, Self>> {
        let to = parse_cell(to, "to")?;
        let from = slf.acting_cell(slf.py());
        let target = target
            .map(|t| parse_cell(t, "target"))
            .transpose()?
            .unwrap_or(from);
        let cap = CapabilityRef {
            target,
            slot,
            permissions: parse_auth_required(permissions)?,
            breadstuff: None,
            expires_at,
            allowed_effects: None,
            stored_epoch: None,
        };
        slf.effects.push(Effect::GrantCapability { from, to, cap });
        Ok(slf)
    }

    /// Bump the acting cell's nonce (a deliberate no-op state advance).
    fn increment_nonce(mut slf: PyRefMut<'_, Self>) -> PyRefMut<'_, Self> {
        let cell = slf.acting_cell(slf.py());
        slf.effects.push(Effect::IncrementNonce { cell });
        slf
    }

    /// Set the action's method verb (default "execute").
    fn method<'py>(mut slf: PyRefMut<'py, Self>, name: &str) -> PyRefMut<'py, Self> {
        slf.method = name.to_string();
        slf
    }

    /// Set the turn fee (computron budget; default 10_000).
    fn fee(mut slf: PyRefMut<'_, Self>, fee: u64) -> PyRefMut<'_, Self> {
        slf.fee = Some(fee);
        slf
    }

    /// Attach a memo string.
    fn memo<'py>(mut slf: PyRefMut<'py, Self>, memo: &str) -> PyRefMut<'py, Self> {
        slf.memo = Some(memo.to_string());
        slf
    }

    /// Pin the turn nonce explicitly. When omitted, `.sign()` fetches the
    /// acting cell's live nonce from the node.
    fn nonce(mut slf: PyRefMut<'_, Self>, nonce: u64) -> PyRefMut<'_, Self> {
        slf.nonce = Some(nonce);
        slf
    }

    /// Pin the validity horizon (unix seconds). Default: now + 3600 — the
    /// same horizon the node stamps so turns ride the verified producer.
    fn valid_until(mut slf: PyRefMut<'_, Self>, unix_secs: i64) -> PyRefMut<'_, Self> {
        slf.valid_until = Some(unix_secs);
        slf
    }

    /// Number of staged effects.
    fn __len__(&self) -> usize {
        self.effects.len()
    }

    /// Sign the staged turn with this identity's Ed25519 key, yielding an
    /// AuthorizedTurn ready to `.submit()`. After this point the act is
    /// credentialed; there is no way back to an unauthorized shape.
    ///
    /// Refuses an empty turn. Fetches the federation id and live nonce from
    /// the node unless both were pinned (`federation_id=` on `.turn()`,
    /// `.nonce(n)`) — pin both for fully offline construction.
    fn sign(&self, py: Python<'_>) -> PyResult<AuthorizedTurn> {
        if self.effects.is_empty() {
            return Err(refused(
                "refusing to sign an empty turn (no effects staged) — stage a verb first \
                 (.transfer / .write / .grant / .increment_nonce)",
            ));
        }

        let node_url = self.node_url.clone();
        let federation_id = match self.federation_id {
            Some(fid) => fid,
            None => py
                .detach(|| fetch_federation_id(&node_url))
                .map_err(err)?,
        };

        let ident = self.identity.borrow(py);
        let agent_hex = hex::encode(ident.clerk.cell_id("default").0);
        let nonce = match self.nonce {
            Some(n) => n,
            None => py.detach(|| fetch_cell_nonce(&node_url, &agent_hex)),
        };

        let action = ident.clerk.make_action(
            ident.clerk.cell_id("default"),
            &self.method,
            self.effects.clone(),
            &federation_id,
        );
        let mut turn = ident.clerk.make_turn_for("default", action);
        turn.nonce = nonce;
        turn.fee = self.fee.unwrap_or(10_000);
        turn.memo = self.memo.clone();
        turn.valid_until = Some(
            self.valid_until
                .unwrap_or_else(|| now_secs() + TURN_VALIDITY_HORIZON_SECS),
        );

        let signed = ident.clerk.sign_turn(&turn);
        Ok(AuthorizedTurn {
            signed,
            node_url: self.node_url.clone(),
            devnet_key: self.devnet_key.clone(),
        })
    }

    fn __repr__(&self, py: Python<'_>) -> String {
        format!(
            "TurnBuilder(agent={}, method={:?}, effects={})",
            hex::encode(self.acting_cell(py).0),
            self.method,
            self.effects.len()
        )
    }
}

// ─── AuthorizedTurn ───

/// A signed, ready-to-submit turn. Inspect with `.explain()` (the clerk's
/// faithful, total, anti-blind-signing rendering); execute with `.submit()`.
#[pyclass(unsendable, module = "dregg")]
struct AuthorizedTurn {
    signed: SignedTurn,
    node_url: String,
    devnet_key: Option<String>,
}

#[pymethods]
impl AuthorizedTurn {
    /// The clerk's faithful, total explanation of exactly what was signed.
    fn explain(&self) -> String {
        explain_turn(&self.signed.turn)
    }

    /// Hex hash of the signed turn (what the signature covers, and what the
    /// receipt will name).
    #[getter]
    fn turn_hash(&self) -> String {
        hex::encode(self.signed.turn.hash())
    }

    /// Hex signer public key.
    #[getter]
    fn signer(&self) -> String {
        hex::encode(self.signed.signer.0)
    }

    /// The canonical wire bytes (postcard `SignedTurn`) — exactly the body
    /// `.submit()` POSTs to `/api/turns/submit-signed`.
    fn to_bytes<'py>(&self, py: Python<'py>) -> PyResult<Bound<'py, PyBytes>> {
        let bytes = postcard::to_stdvec(&self.signed)
            .map_err(|e| err(format!("failed to encode signed turn: {e}")))?;
        Ok(PyBytes::new(py, &bytes))
    }

    /// Execute the turn on the node and return the Receipt.
    ///
    /// Raises DreggRefused when the node rejects — the message carries the
    /// node's reason and the faithful explanation of what was signed.
    fn submit(&self, py: Python<'_>) -> PyResult<Receipt> {
        let body = postcard::to_stdvec(&self.signed)
            .map_err(|e| err(format!("failed to encode signed turn: {e}")))?;
        let node_url = self.node_url.clone();
        let key = self.devnet_key.clone();
        let response = py
            .detach(|| post_signed_turn(&node_url, &body, key.as_deref()))
            .map_err(err)?;

        let accepted = response
            .get("accepted")
            .and_then(|a| a.as_bool())
            .unwrap_or(false);
        if !accepted {
            let reason = response
                .get("error")
                .and_then(|e| e.as_str())
                .unwrap_or("turn did not commit")
                .to_string();
            return Err(refused(format!(
                "{reason}\n\nwhat was signed:\n{}",
                self.explain()
            )));
        }
        Ok(Receipt {
            data: response,
            node_url: Some(self.node_url.clone()),
            proof: None,
        })
    }

    fn __repr__(&self) -> String {
        format!("AuthorizedTurn(turn_hash={:?})", self.turn_hash())
    }
}

// ─── Receipt ───

/// **The receipt noun** — proof-of-execution for one committed turn,
/// dict-like over the node's JSON, with the STARK proof lazily fetched
/// (receipts are born proofless; the proof is additive attestation).
#[pyclass(unsendable, module = "dregg")]
struct Receipt {
    data: serde_json::Value,
    node_url: Option<String>,
    proof: Option<serde_json::Value>,
}

impl Receipt {
    fn str_field(&self, key: &str) -> Option<String> {
        self.data
            .get(key)
            .and_then(|v| v.as_str())
            .map(str::to_string)
    }
}

#[pymethods]
impl Receipt {
    /// Hex hash of the committed turn.
    #[getter]
    fn turn_hash(&self) -> PyResult<String> {
        self.str_field("turn_hash")
            .ok_or_else(|| err("receipt carries no turn_hash"))
    }

    /// Hex receipt-chain hash, when the source surface carried one (the
    /// event stream does; the submit acknowledgement does not).
    #[getter]
    fn receipt_hash(&self) -> Option<String> {
        self.str_field("receipt_hash")
    }

    /// Whether a proof was already attached at the time this receipt was
    /// observed (`.proof()` may still fetch one that landed later).
    #[getter]
    fn has_proof(&self) -> bool {
        self.data
            .get("has_proof")
            .and_then(|v| v.as_bool())
            .unwrap_or(false)
    }

    /// Lazily fetch the composed full-turn STARK for this receipt's turn
    /// from `GET /api/turn/{hash}/proof`. Returns a dict
    /// (`turn_hash` / `proof_len` / `proof_hex`) or None while the node's
    /// async prove pool hasn't attached one. The fetch is cached.
    #[pyo3(signature = (node_url=None))]
    fn proof<'py>(
        &mut self,
        py: Python<'py>,
        node_url: Option<&str>,
    ) -> PyResult<Option<Bound<'py, PyAny>>> {
        if self.proof.is_none() {
            let base = node_url
                .map(str::to_string)
                .or_else(|| self.node_url.clone())
                .ok_or_else(|| {
                    err("this receipt has no node_url; pass proof(node_url=...) explicitly")
                })?;
            let hash = self.turn_hash()?;
            let url = format!("{}/api/turn/{}/proof", base.trim_end_matches('/'), hash);
            let fetched = py.detach(move || match http_agent().get(&url).call() {
                Ok(resp) => resp
                    .into_json::<serde_json::Value>()
                    .map(Some)
                    .map_err(|e| format!("GET {url}: {e}")),
                Err(ureq::Error::Status(404, _)) => Ok(None),
                Err(e) => Err(format!("GET {url}: {e}")),
            });
            match fetched.map_err(err)? {
                Some(v) => self.proof = Some(v),
                None => return Ok(None),
            }
        }
        self.proof
            .as_ref()
            .map(|v| json_to_py(py, v))
            .transpose()
    }

    /// The receipt's full JSON as a plain dict.
    fn to_dict<'py>(&self, py: Python<'py>) -> PyResult<Bound<'py, PyAny>> {
        json_to_py(py, &self.data)
    }

    fn keys(&self) -> Vec<String> {
        match self.data.as_object() {
            Some(map) => map.keys().cloned().collect(),
            None => Vec::new(),
        }
    }

    #[pyo3(signature = (key, default=None))]
    fn get<'py>(
        &self,
        py: Python<'py>,
        key: &str,
        default: Option<Bound<'py, PyAny>>,
    ) -> PyResult<Bound<'py, PyAny>> {
        match self.data.get(key) {
            Some(v) => json_to_py(py, v),
            None => Ok(default.unwrap_or_else(|| py.None().into_bound(py))),
        }
    }

    fn __getitem__<'py>(&self, py: Python<'py>, key: &str) -> PyResult<Bound<'py, PyAny>> {
        match self.data.get(key) {
            Some(v) => json_to_py(py, v),
            None => Err(PyKeyError::new_err(key.to_string())),
        }
    }

    fn __contains__(&self, key: &str) -> bool {
        self.data.get(key).is_some()
    }

    fn __len__(&self) -> usize {
        self.data.as_object().map(|m| m.len()).unwrap_or(0)
    }

    fn __repr__(&self) -> String {
        format!(
            "Receipt(turn_hash={:?}, has_proof={})",
            self.str_field("turn_hash").unwrap_or_default(),
            self.has_proof()
        )
    }
}

// ─── subscribe: the receipt nervous system, blocking-iterator edition ───

#[derive(Default)]
struct SseEvent {
    id: Option<String>,
    name: Option<String>,
    data: String,
}

/// Minimal SSE parser (same field semantics as `sdk/src/events.rs`): splits
/// on blank lines, honors `id:` / `event:` / `data:`, ignores `:` heartbeats.
#[derive(Default)]
struct SseParser {
    buf: String,
    current: SseEvent,
}

impl SseParser {
    fn push(&mut self, chunk: &[u8]) -> Vec<SseEvent> {
        self.buf.push_str(&String::from_utf8_lossy(chunk));
        let mut done = Vec::new();
        while let Some(nl) = self.buf.find('\n') {
            let line: String = self.buf.drain(..=nl).collect();
            let line = line.trim_end_matches(['\n', '\r']);
            if line.is_empty() {
                let event = std::mem::take(&mut self.current);
                if !event.data.is_empty() {
                    done.push(event);
                }
                continue;
            }
            if line.starts_with(':') {
                continue; // heartbeat / comment
            }
            let (field, value) = match line.split_once(':') {
                Some((f, v)) => (f, v.strip_prefix(' ').unwrap_or(v)),
                None => (line, ""),
            };
            match field {
                "id" => self.current.id = Some(value.to_string()),
                "event" => self.current.name = Some(value.to_string()),
                "data" => {
                    if !self.current.data.is_empty() {
                        self.current.data.push('\n');
                    }
                    self.current.data.push_str(value);
                }
                _ => {}
            }
        }
        done
    }
}

/// The live receipt feed: a blocking iterator of Receipts over the node's
/// `GET /api/events/stream` SSE broadcast. Reconnects with exponential
/// backoff and `Last-Event-ID` resume; iterate forever or `break`.
/// Delivery is at-least-once across reconnects — dedupe by `receipt_hash`
/// if it matters.
#[pyclass(unsendable, module = "dregg")]
struct ReceiptStream {
    node_url: String,
    query: Vec<(String, String)>,
    last_event_id: Option<String>,
    reader: Option<Box<dyn Read + Send>>,
    parser: SseParser,
    pending: VecDeque<serde_json::Value>,
    backoff_ms: u64,
}

impl ReceiptStream {
    fn connect(&mut self) -> Result<(), String> {
        let agent = ureq::AgentBuilder::new()
            .timeout_connect(Duration::from_secs(10))
            // No overall timeout: the stream lives forever. The read timeout
            // sits just above the node's 30s heartbeat so a dead connection
            // is detected (and Ctrl-C is honored) within ~40s worst case.
            .timeout_read(Duration::from_secs(40))
            .build();
        let mut req = agent
            .get(&format!("{}/api/events/stream", self.node_url))
            .set("accept", "text/event-stream");
        for (k, v) in &self.query {
            req = req.query(k, v);
        }
        if let Some(id) = &self.last_event_id {
            req = req.set("last-event-id", id);
        }
        let resp = req.call().map_err(|e| e.to_string())?;
        self.reader = Some(Box::new(resp.into_reader()));
        Ok(())
    }
}

#[pymethods]
impl ReceiptStream {
    fn __iter__(slf: PyRef<'_, Self>) -> PyRef<'_, Self> {
        slf
    }

    fn __next__(&mut self, py: Python<'_>) -> PyResult<Receipt> {
        loop {
            py.check_signals()?;

            if let Some(value) = self.pending.pop_front() {
                return Ok(Receipt {
                    data: value,
                    node_url: Some(self.node_url.clone()),
                    proof: None,
                });
            }

            if self.reader.is_none() {
                let res = py.detach(|| self.connect());
                if res.is_err() {
                    let backoff = self.backoff_ms;
                    py.detach(|| std::thread::sleep(Duration::from_millis(backoff)));
                    self.backoff_ms = (self.backoff_ms * 2).min(15_000);
                    continue;
                }
            }

            let mut buf = [0u8; 8192];
            let reader = self.reader.as_mut().expect("connected above");
            let n = py.detach(|| reader.read(&mut buf));
            match n {
                Ok(0) | Err(_) => {
                    // EOF or transport error: reconnect with backoff.
                    self.reader = None;
                    let backoff = self.backoff_ms;
                    py.detach(|| std::thread::sleep(Duration::from_millis(backoff)));
                    self.backoff_ms = (self.backoff_ms * 2).min(15_000);
                    continue;
                }
                Ok(n) => {
                    for event in self.parser.push(&buf[..n]) {
                        if let Some(id) = &event.id {
                            self.last_event_id = Some(id.clone());
                        }
                        if event.name.as_deref() != Some("receipt") {
                            continue;
                        }
                        if let Ok(value) = serde_json::from_str(&event.data) {
                            self.pending.push_back(value);
                        }
                    }
                    if !self.pending.is_empty() {
                        self.backoff_ms = 500;
                    }
                }
            }
        }
    }

    fn __repr__(&self) -> String {
        format!("ReceiptStream(node_url={:?})", self.node_url)
    }
}

/// Subscribe to a node's committed-receipt broadcast as a blocking iterator
/// of Receipts. `cell` filters to receipts touching one cell; `kind` to one
/// effect kind (e.g. "transfer", "set_field").
#[pyfunction]
#[pyo3(signature = (node_url, cell=None, kind=None))]
fn subscribe(
    node_url: &str,
    cell: Option<&Bound<'_, PyAny>>,
    kind: Option<&str>,
) -> PyResult<ReceiptStream> {
    let mut query = Vec::new();
    if let Some(c) = cell {
        // Accept hex/bytes (validated) — straight from an explorer URL works.
        query.push(("cell".to_string(), hex::encode(parse_32(c, "cell")?)));
    }
    if let Some(k) = kind {
        query.push(("kind".to_string(), k.to_string()));
    }
    Ok(ReceiptStream {
        node_url: node_url.trim_end_matches('/').to_string(),
        query,
        last_event_id: None,
        reader: None,
        parser: SseParser::default(),
        pending: VecDeque::new(),
        backoff_ms: 500,
    })
}

// ─── explain ───

/// The clerk's faithful rendering of a turn: pass an AuthorizedTurn (exactly
/// what was signed) or a TurnBuilder (a DRAFT rendering of the staged
/// effects — not yet a credentialed act).
#[pyfunction]
fn explain(turn: &Bound<'_, PyAny>) -> PyResult<String> {
    if let Ok(authorized) = turn.cast::<AuthorizedTurn>() {
        return Ok(authorized.borrow().explain());
    }
    if let Ok(builder) = turn.cast::<TurnBuilder>() {
        let builder = builder.borrow();
        let py = turn.py();
        let ident = builder.identity.borrow(py);
        // Render the draft as the unsigned action it would become — the same
        // explain the signed turn will carry, marked as a draft.
        let action = dregg_sdk::raw::unsigned_action_named(
            ident.clerk.cell_id("default"),
            &builder.method,
            builder.effects.clone(),
        );
        return Ok(format!("DRAFT (unsigned):\n{}", explain_action(&action)));
    }
    Err(PyTypeError::new_err(
        "explain() takes an AuthorizedTurn or a TurnBuilder",
    ))
}

// ─── profiles listing ───

/// List the local profile store (name / public_key / created_at / active).
#[pyfunction]
fn list_profiles(py: Python<'_>) -> PyResult<Bound<'_, PyList>> {
    let infos = profiles::list().map_err(|e| err(e.to_string()))?;
    let out = PyList::empty(py);
    for p in infos {
        let d = PyDict::new(py);
        d.set_item("name", p.name)?;
        d.set_item("public_key", p.public_key_hex)?;
        d.set_item("created_at", p.created_at)?;
        d.set_item("active", p.active)?;
        out.append(d)?;
    }
    Ok(out)
}

// ─── program: the constraint language at the builder surface ───

/// One cell-program constraint atom (a `StateConstraint`). Compose lists of
/// these into a content-addressed factory descriptor via
/// `dregg.program.descriptor([...])`.
#[pyclass(unsendable, module = "dregg.program", name = "Constraint", from_py_object)]
#[derive(Clone)]
struct PyConstraint {
    inner: StateConstraint,
}

#[pymethods]
impl PyConstraint {
    fn __repr__(&self) -> String {
        format!("Constraint({:?})", self.inner)
    }
}

fn parse_hash_kind(kind: &str) -> PyResult<HashKind> {
    match kind.to_ascii_lowercase().as_str() {
        "blake3" => Ok(HashKind::Blake3),
        "poseidon2" => Ok(HashKind::Poseidon2),
        other => Err(PyValueError::new_err(format!(
            "hash_kind: expected blake3 or poseidon2, got {other:?}"
        ))),
    }
}

/// The turn's sender must be exactly `pk` (actor binding; fail-closed).
#[pyfunction]
fn sender_is(pk: &Bound<'_, PyAny>) -> PyResult<PyConstraint> {
    Ok(PyConstraint {
        inner: dregg_sdk::program::sender_is(parse_32(pk, "pk")?),
    })
}

/// The sender must equal the 32-byte identity stored in slot `index` (the
/// dynamic-owner actor binding).
#[pyfunction]
fn sender_in_slot(index: u8) -> PyConstraint {
    PyConstraint {
        inner: dregg_sdk::program::sender_in_slot(index),
    }
}

/// Post-turn own-balance floor (`balance >= min`).
#[pyfunction]
fn balance_gte(min: u64) -> PyConstraint {
    PyConstraint {
        inner: dregg_sdk::program::balance_gte(min),
    }
}

/// Post-turn own-balance ceiling (`balance <= max`).
#[pyfunction]
fn balance_lte(max: u64) -> PyConstraint {
    PyConstraint {
        inner: dregg_sdk::program::balance_lte(max),
    }
}

/// Knowledge gate: the turn must exhibit a witness whose hash equals the
/// commitment stored in slot `commitment_index`.
#[pyfunction]
#[pyo3(signature = (commitment_index, hash_kind="blake3"))]
fn preimage_gate(commitment_index: u8, hash_kind: &str) -> PyResult<PyConstraint> {
    Ok(PyConstraint {
        inner: dregg_sdk::program::preimage_gate(commitment_index, parse_hash_kind(hash_kind)?),
    })
}

/// Slot `index` may never change once the cell is born.
#[pyfunction]
fn immutable(index: u8) -> PyConstraint {
    PyConstraint {
        inner: dregg_sdk::program::immutable(index),
    }
}

/// Slot `index` may be written at most once (from zero).
#[pyfunction]
fn write_once(index: u8) -> PyConstraint {
    PyConstraint {
        inner: dregg_sdk::program::write_once(index),
    }
}

/// Disjunction over simple atoms (sender_is / sender_in_slot / balance_gte /
/// balance_lte / preimage_gate / write_once / immutable).
#[pyfunction]
fn any_of(variants: Vec<PyConstraint>) -> PyResult<PyConstraint> {
    let simples = variants
        .into_iter()
        .map(|c| simple_of(&c.inner))
        .collect::<PyResult<Vec<_>>>()?;
    Ok(PyConstraint {
        inner: dregg_sdk::program::any_of(simples),
    })
}

fn simple_of(c: &StateConstraint) -> PyResult<SimpleStateConstraint> {
    Ok(match c {
        StateConstraint::SenderIs { pk } => SimpleStateConstraint::SenderIs { pk: *pk },
        StateConstraint::SenderInSlot { index } => {
            SimpleStateConstraint::SenderInSlot { index: *index }
        }
        StateConstraint::BalanceGte { min } => SimpleStateConstraint::BalanceGte { min: *min },
        StateConstraint::BalanceLte { max } => SimpleStateConstraint::BalanceLte { max: *max },
        StateConstraint::PreimageGate {
            commitment_index,
            hash_kind,
        } => SimpleStateConstraint::PreimageGate {
            commitment_index: *commitment_index,
            hash_kind: *hash_kind,
        },
        StateConstraint::WriteOnce { index } => SimpleStateConstraint::WriteOnce { index: *index },
        StateConstraint::Immutable { index } => SimpleStateConstraint::Immutable { index: *index },
        other => {
            return Err(PyTypeError::new_err(format!(
                "constraint {other:?} has no simple-atom form for any_of"
            )));
        }
    })
}

/// Publish a constraint list as a content-addressed factory descriptor:
/// returns `{"factory_vk": hex, "child_program_vk": hex, "constraints": n}`.
/// Anyone can recompute these from the published constraints and verify a
/// cell's law. (The safety is the executor's program gate, not this dict.)
#[pyfunction]
fn descriptor<'py>(
    py: Python<'py>,
    constraints: Vec<PyConstraint>,
) -> PyResult<Bound<'py, PyDict>> {
    let list: Vec<StateConstraint> = constraints.into_iter().map(|c| c.inner).collect();
    let n = list.len();
    let desc = dregg_sdk::program::programmed_cell_descriptor(list);
    let d = PyDict::new(py);
    d.set_item("factory_vk", hex::encode(desc.factory_vk))?;
    d.set_item(
        "child_program_vk",
        desc.child_program_vk.map(hex::encode),
    )?;
    d.set_item("constraints", n)?;
    Ok(d)
}

// ─── organs: the higher primitives (docs/ORGANS.md), as ergonomic HTTP faces ───
//
// Each organ is the Python face of a node service — the same routes the TS
// SDK's organ clients drive. The node computes the per-cell factory
// descriptors and seal fan-outs the wire layer does not carry; these clients
// drive them. The enforcement tooth is the executor-installed cell program
// either way (see each method's route). Operator-gated organs (trustline,
// channels) carry a devnet key; the relay (mailbox) is owner-signed.

/// **Trustline** — the bilateral line of credit (`docs/ORGANS.md` §1).
///
/// A line `issuer → holder` of N is an ATTENUATED CAPABILITY whose exercise
/// debits a shared counter; the executor-installed cell program enforces
/// `drawn ≤ ceiling` for life. The node operator IS the issuer — these routes
/// are operator-gated (pass `devnet_key=` on `Identity.trustline()`).
///
/// ```python
/// tl = ident.trustline("https://devnet.example", devnet_key="…")
/// line = tl.open(holder_cell_hex, 1000)        # four-turn funded birth
/// tl.draw(line["trustline"], 250)              # debit the shared counter
/// tl.repay(line["trustline"], 100)             # restore the line
/// tl.status(line["trustline"])                 # {line, drawn, remaining, escrow, open, …}
/// tl.settle(line["trustline"]); tl.close(line["trustline"])
/// ```
#[pyclass(module = "dregg")]
struct Trustline {
    node_url: String,
    devnet_key: Option<String>,
}

impl Trustline {
    fn post<'py>(
        &self,
        py: Python<'py>,
        path: &str,
        body: serde_json::Value,
    ) -> PyResult<Bound<'py, PyAny>> {
        let base = self.node_url.clone();
        let key = self.devnet_key.clone();
        let v = py
            .detach(|| http_send_json("POST", &base, path, &body, key.as_deref()))
            .map_err(refused)?;
        json_to_py(py, &v)
    }
}

#[pymethods]
impl Trustline {
    /// Open a directional line `operator → holder` of `line`, escrowed in full
    /// (`POST /trustline/open`; four-turn funded birth). `salt` disambiguates
    /// multiple lines to the same holder.
    #[pyo3(signature = (holder, line, salt=None))]
    fn open<'py>(
        &self,
        py: Python<'py>,
        holder: &Bound<'_, PyAny>,
        line: u64,
        salt: Option<&str>,
    ) -> PyResult<Bound<'py, PyAny>> {
        let mut body = serde_json::json!({ "holder": hex::encode(parse_32(holder, "holder")?), "line": line });
        if let Some(s) = salt {
            body["salt"] = serde_json::Value::String(s.to_string());
        }
        self.post(py, "/trustline/open", body)
    }

    /// Draw `amount` against the line (`POST /trustline/draw`; one-shot per
    /// digest — supply `digest=` for client-side replay protection).
    #[pyo3(signature = (trustline, amount, digest=None))]
    fn draw<'py>(
        &self,
        py: Python<'py>,
        trustline: &Bound<'_, PyAny>,
        amount: u64,
        digest: Option<&str>,
    ) -> PyResult<Bound<'py, PyAny>> {
        let mut body = serde_json::json!({ "trustline": hex::encode(parse_32(trustline, "trustline")?), "amount": amount });
        if let Some(d) = digest {
            body["digest"] = serde_json::Value::String(d.to_string());
        }
        self.post(py, "/trustline/draw", body)
    }

    /// Repay `amount`, restoring the line (`POST /trustline/repay`).
    fn repay<'py>(&self, py: Python<'py>, trustline: &Bound<'_, PyAny>, amount: u64) -> PyResult<Bound<'py, PyAny>> {
        let body = serde_json::json!({ "trustline": hex::encode(parse_32(trustline, "trustline")?), "amount": amount });
        self.post(py, "/trustline/repay", body)
    }

    /// Settle outstanding draws to the holders (`POST /trustline/settle`).
    fn settle<'py>(&self, py: Python<'py>, trustline: &Bound<'_, PyAny>) -> PyResult<Bound<'py, PyAny>> {
        let body = serde_json::json!({ "trustline": hex::encode(parse_32(trustline, "trustline")?) });
        self.post(py, "/trustline/settle", body)
    }

    /// Close the line: settle outstanding to holder, residual to issuer
    /// (`POST /trustline/close`).
    fn close<'py>(&self, py: Python<'py>, trustline: &Bound<'_, PyAny>) -> PyResult<Bound<'py, PyAny>> {
        let body = serde_json::json!({ "trustline": hex::encode(parse_32(trustline, "trustline")?) });
        self.post(py, "/trustline/close", body)
    }

    /// Live position (`GET /trustline/status/{cell}`):
    /// `{line, drawn, settled, remaining, escrow, open, coordinator_*}`.
    fn status<'py>(&self, py: Python<'py>, trustline: &Bound<'_, PyAny>) -> PyResult<Bound<'py, PyAny>> {
        let cell = hex::encode(parse_32(trustline, "trustline")?);
        let base = self.node_url.clone();
        let key = self.devnet_key.clone();
        let path = format!("/trustline/status/{cell}");
        let v = py
            .detach(|| http_get_json(&base, &path, key.as_deref()))
            .map_err(err)?;
        json_to_py(py, &v)
    }

    fn __repr__(&self) -> String {
        format!("Trustline(node_url={:?})", self.node_url)
    }
}

/// **Channels** — the group-key epoch lift (`docs/ORGANS.md` §4).
///
/// A group is a CELL: membership root, key epoch, and key commitment live
/// on-cell. `remove(m)` darkens BOTH m's forward-read ability AND m's
/// group-held capabilities in ONE atomic epoch step (the `epochs_unified`
/// keystone). Message bodies never touch the chain — encrypt under the current
/// epoch key client-side and `post()` only ciphertext. Operator-gated.
///
/// ```python
/// ch = ident.channels("https://devnet.example", devnet_key="…")
/// g = ch.create(7, [{"cell": alice_hex, "seal_pk": alice_seal_hex}])
/// ch.join(g["channel"], {"cell": bob_hex, "seal_pk": bob_seal_hex})  # fresh fan_out
/// ch.post(g["channel"], g["epoch"], nonce_hex, ciphertext_hex)        # ciphertext only
/// ch.remove(g["channel"], bob_hex)                                    # bob darkened in ONE turn
/// for m in ch.messages(g["channel"]): ...                             # SSE delivery
/// ```
#[pyclass(module = "dregg")]
struct Channels {
    node_url: String,
    devnet_key: Option<String>,
}

/// Normalize a member spec (`{"cell": hex|bytes, "seal_pk": hex|bytes}`) to the
/// wire JSON `{cell, seal_pk}`.
fn member_json(m: &Bound<'_, PyAny>) -> PyResult<serde_json::Value> {
    let dict = m
        .cast::<PyDict>()
        .map_err(|_| PyTypeError::new_err("member: expected a dict {cell, seal_pk}"))?;
    let cell = dict
        .get_item("cell")?
        .ok_or_else(|| PyValueError::new_err("member: missing 'cell'"))?;
    let seal = dict
        .get_item("seal_pk")
        .ok()
        .flatten()
        .or(dict.get_item("sealPk").ok().flatten())
        .ok_or_else(|| PyValueError::new_err("member: missing 'seal_pk'"))?;
    let cell_hex = hex::encode(parse_32(&cell, "member.cell")?);
    let seal_hex = if let Ok(s) = seal.extract::<&str>() {
        s.trim().to_string()
    } else if let Ok(b) = seal.extract::<&[u8]>() {
        hex::encode(b)
    } else {
        return Err(PyTypeError::new_err("member.seal_pk: expected hex str or bytes"));
    };
    Ok(serde_json::json!({ "cell": cell_hex, "seal_pk": seal_hex }))
}

impl Channels {
    fn post<'py>(
        &self,
        py: Python<'py>,
        path: &str,
        body: serde_json::Value,
    ) -> PyResult<Bound<'py, PyAny>> {
        let base = self.node_url.clone();
        let key = self.devnet_key.clone();
        let v = py
            .detach(|| http_send_json("POST", &base, path, &body, key.as_deref()))
            .map_err(refused)?;
        json_to_py(py, &v)
    }
}

#[pymethods]
impl Channels {
    /// Birth the group at epoch 1 with `members` as founders (`POST
    /// /channels/create`). `tag` (u64) names the group among the operator's
    /// groups. Returns the first sealed key fan-out.
    fn create<'py>(
        &self,
        py: Python<'py>,
        tag: u64,
        members: Vec<Bound<'_, PyAny>>,
    ) -> PyResult<Bound<'py, PyAny>> {
        let members = members
            .iter()
            .map(member_json)
            .collect::<PyResult<Vec<_>>>()?;
        self.post(py, "/channels/create", serde_json::json!({ "tag": tag, "members": members }))
    }

    /// Add a member — one unified epoch step (`POST /channels/join`); returns
    /// the fresh fan-out.
    fn join<'py>(&self, py: Python<'py>, channel: &Bound<'_, PyAny>, member: &Bound<'_, PyAny>) -> PyResult<Bound<'py, PyAny>> {
        let body = serde_json::json!({ "channel": hex::encode(parse_32(channel, "channel")?), "member": member_json(member)? });
        self.post(py, "/channels/join", body)
    }

    /// Remove a member — one unified epoch step that darkens both their
    /// forward-read ability and their group-held capabilities (`POST
    /// /channels/remove`). The removed member is absent from the returned
    /// fan-out.
    fn remove<'py>(&self, py: Python<'py>, channel: &Bound<'_, PyAny>, member: &Bound<'_, PyAny>) -> PyResult<Bound<'py, PyAny>> {
        let body = serde_json::json!({ "channel": hex::encode(parse_32(channel, "channel")?), "member": hex::encode(parse_32(member, "member")?) });
        self.post(py, "/channels/remove", body)
    }

    /// Advance the epoch without a membership change (`POST /channels/rekey`;
    /// a fresh key fan-out).
    fn rekey<'py>(&self, py: Python<'py>, channel: &Bound<'_, PyAny>) -> PyResult<Bound<'py, PyAny>> {
        let body = serde_json::json!({ "channel": hex::encode(parse_32(channel, "channel")?) });
        self.post(py, "/channels/rekey", body)
    }

    /// Post a message body (`POST /channels/post`). Encrypt client-side under
    /// the CURRENT epoch key, then pass only `nonce` + `ciphertext` (hex str or
    /// bytes). The body never touches the chain.
    #[pyo3(name = "post")]
    fn post_message<'py>(
        &self,
        py: Python<'py>,
        channel: &Bound<'_, PyAny>,
        epoch: u64,
        nonce: &Bound<'_, PyAny>,
        ciphertext: &Bound<'_, PyAny>,
    ) -> PyResult<Bound<'py, PyAny>> {
        let body = serde_json::json!({
            "channel": hex::encode(parse_32(channel, "channel")?),
            "epoch": epoch,
            "nonce": hex_or_bytes(nonce, "nonce")?,
            "ciphertext": hex_or_bytes(ciphertext, "ciphertext")?,
        });
        self.post(py, "/channels/post", body)
    }

    /// Live group state (`GET /channels/status/{cell}`): epoch, roster
    /// commitment, and the `epochs_unified` invariant tooth.
    fn status<'py>(&self, py: Python<'py>, channel: &Bound<'_, PyAny>) -> PyResult<Bound<'py, PyAny>> {
        let cell = hex::encode(parse_32(channel, "channel")?);
        let base = self.node_url.clone();
        let key = self.devnet_key.clone();
        let path = format!("/channels/status/{cell}");
        let v = py
            .detach(|| http_get_json(&base, &path, key.as_deref()))
            .map_err(err)?;
        json_to_py(py, &v)
    }

    /// Subscribe to the group's message stream (`GET /channels/messages/{cell}`,
    /// SSE) as a blocking iterator of ciphertext-envelope dicts
    /// (`{seq, epoch, nonce, ciphertext}`). Open each body with the epoch key
    /// you hold from the fan-out. Reconnects with backoff + `Last-Event-ID`.
    fn messages(&self, channel: &Bound<'_, PyAny>) -> PyResult<SseJsonStream> {
        let cell = hex::encode(parse_32(channel, "channel")?);
        Ok(SseJsonStream::open(
            &self.node_url,
            &format!("/channels/messages/{cell}"),
        ))
    }

    fn __repr__(&self) -> String {
        format!("Channels(node_url={:?})", self.node_url)
    }
}

/// A blocking iterator over a node SSE route, yielding each event's `data:`
/// JSON payload as a Python object. The generic twin of [`ReceiptStream`] (no
/// `event:` name filter) used by the channels message stream. Reconnects with
/// exponential backoff and `Last-Event-ID` resume.
#[pyclass(unsendable, module = "dregg")]
struct SseJsonStream {
    url: String,
    last_event_id: Option<String>,
    reader: Option<Box<dyn Read + Send>>,
    parser: SseParser,
    pending: VecDeque<serde_json::Value>,
    backoff_ms: u64,
}

impl SseJsonStream {
    fn open(base: &str, path: &str) -> Self {
        SseJsonStream {
            url: format!("{}{}", base.trim_end_matches('/'), path),
            last_event_id: None,
            reader: None,
            parser: SseParser::default(),
            pending: VecDeque::new(),
            backoff_ms: 500,
        }
    }

    fn connect(&mut self) -> Result<(), String> {
        let agent = ureq::AgentBuilder::new()
            .timeout_connect(Duration::from_secs(10))
            .timeout_read(Duration::from_secs(40))
            .build();
        let mut req = agent.get(&self.url).set("accept", "text/event-stream");
        if let Some(id) = &self.last_event_id {
            req = req.set("last-event-id", id);
        }
        let resp = req.call().map_err(|e| e.to_string())?;
        self.reader = Some(Box::new(resp.into_reader()));
        Ok(())
    }
}

#[pymethods]
impl SseJsonStream {
    fn __iter__(slf: PyRef<'_, Self>) -> PyRef<'_, Self> {
        slf
    }

    fn __next__(&mut self, py: Python<'_>) -> PyResult<Py<PyAny>> {
        loop {
            py.check_signals()?;
            if let Some(value) = self.pending.pop_front() {
                return Ok(json_to_py(py, &value)?.unbind());
            }
            if self.reader.is_none() {
                if py.detach(|| self.connect()).is_err() {
                    let backoff = self.backoff_ms;
                    py.detach(|| std::thread::sleep(Duration::from_millis(backoff)));
                    self.backoff_ms = (self.backoff_ms * 2).min(15_000);
                    continue;
                }
            }
            let mut buf = [0u8; 8192];
            let reader = self.reader.as_mut().expect("connected above");
            match py.detach(|| reader.read(&mut buf)) {
                Ok(0) | Err(_) => {
                    self.reader = None;
                    let backoff = self.backoff_ms;
                    py.detach(|| std::thread::sleep(Duration::from_millis(backoff)));
                    self.backoff_ms = (self.backoff_ms * 2).min(15_000);
                }
                Ok(n) => {
                    for event in self.parser.push(&buf[..n]) {
                        if let Some(id) = &event.id {
                            self.last_event_id = Some(id.clone());
                        }
                        if let Ok(value) = serde_json::from_str(&event.data) {
                            self.pending.push_back(value);
                        }
                    }
                    if !self.pending.is_empty() {
                        self.backoff_ms = 500;
                    }
                }
            }
        }
    }

    fn __repr__(&self) -> String {
        format!("SseJsonStream(url={:?})", self.url)
    }
}

/// Accept a hex `str` or `bytes`, returning a hex string (no length pin — used
/// for variable-length nonces/ciphertexts).
fn hex_or_bytes(obj: &Bound<'_, PyAny>, what: &str) -> PyResult<String> {
    if let Ok(s) = obj.extract::<&str>() {
        return Ok(s.trim().to_string());
    }
    if let Ok(b) = obj.extract::<&[u8]>() {
        return Ok(hex::encode(b));
    }
    Err(PyTypeError::new_err(format!("{what}: expected hex str or bytes")))
}

/// **Mailbox** — a hosted inbox over the relay (`docs/ORGANS.md` §2).
///
/// Store-and-forward: senders enqueue sealed bodies to your inbox; you drain
/// them with a custody proof. The relay sees only ciphertext. Membership ops
/// (`subscribe` / `unsubscribe` / `drain`) are Ed25519-signed by the inbox
/// OWNER (this client signs them); `send` is open.
///
/// Honest scope: sealing (X25519 → ChaCha20-Poly1305) and re-running the
/// dequeue Merkle verifier are NOT done here — bring already-sealed ciphertext
/// to `send()`, and recompute each drained body's `content_hash` before
/// trusting it.
///
/// ```python
/// mb = ident.mailbox("http://relay.example:3100")
/// mb.subscribe()                       # create your hosted inbox
/// # … a sender elsewhere: other.send(my_pubkey_hex, sealed_ciphertext, 100) …
/// out = mb.drain(50)                   # each carries a dequeue (custody) proof
/// mb.unsubscribe()
/// ```
#[pyclass(unsendable, module = "dregg")]
struct Mailbox {
    identity: Py<Identity>,
    base_url: String,
}

const RELAY_SUBSCRIBE_DOMAIN: &[u8] = b"dregg-relay-subscribe-v1";
const RELAY_UNSUBSCRIBE_DOMAIN: &[u8] = b"dregg-relay-unsubscribe-v1";
const RELAY_DRAIN_DOMAIN: &[u8] = b"dregg-relay-drain-v1";

impl Mailbox {
    fn owner_hex(&self, py: Python<'_>) -> String {
        hex::encode(self.identity.borrow(py).clerk.public_key().0)
    }

    /// Sign `domain || owner_pk || nonce [|| extra]` with the owner key,
    /// returning `(owner_hex, nonce_hex, signature_hex)`.
    fn signed_tuple(&self, py: Python<'_>, domain: &[u8], extra: &[u8]) -> (String, String, String) {
        let ident = self.identity.borrow(py);
        let owner = ident.clerk.public_key().0;
        let mut nonce = [0u8; 8];
        getrandom_fill(&mut nonce);
        let mut msg = Vec::with_capacity(domain.len() + 32 + 8 + extra.len());
        msg.extend_from_slice(domain);
        msg.extend_from_slice(&owner);
        msg.extend_from_slice(&nonce);
        msg.extend_from_slice(extra);
        let sig = ident.clerk.sign_bytes(&msg);
        (hex::encode(owner), hex::encode(nonce), hex::encode(sig.0))
    }
}

#[pymethods]
impl Mailbox {
    /// The owner public key (hex) — the inbox id.
    #[getter]
    fn owner(&self, py: Python<'_>) -> String {
        self.owner_hex(py)
    }

    /// `GET /relay/status` — the relay operator's identity + bond.
    fn relay_status<'py>(&self, py: Python<'py>) -> PyResult<Bound<'py, PyAny>> {
        let base = self.base_url.clone();
        let v = py
            .detach(|| http_get_json(&base, "/relay/status", None))
            .map_err(err)?;
        json_to_py(py, &v)
    }

    /// `POST /relay/subscribe` — create this owner's hosted inbox (owner-signed
    /// under `dregg-relay-subscribe-v1`).
    #[pyo3(signature = (capacity=None, min_deposit=None))]
    fn subscribe<'py>(
        &self,
        py: Python<'py>,
        capacity: Option<u64>,
        min_deposit: Option<u64>,
    ) -> PyResult<Bound<'py, PyAny>> {
        let (owner, nonce, sig) = self.signed_tuple(py, RELAY_SUBSCRIBE_DOMAIN, &[]);
        let mut body = serde_json::json!({ "owner": owner, "nonce": nonce, "signature": sig });
        if let Some(c) = capacity {
            body["capacity"] = serde_json::json!(c);
        }
        if let Some(d) = min_deposit {
            body["min_deposit"] = serde_json::json!(d);
        }
        let base = self.base_url.clone();
        let v = py
            .detach(|| http_send_json("POST", &base, "/relay/subscribe", &body, None))
            .map_err(refused)?;
        json_to_py(py, &v)
    }

    /// `DELETE /relay/unsubscribe` — remove this owner's inbox (owner-signed
    /// under `dregg-relay-unsubscribe-v1`).
    fn unsubscribe<'py>(&self, py: Python<'py>) -> PyResult<Bound<'py, PyAny>> {
        let (owner, nonce, sig) = self.signed_tuple(py, RELAY_UNSUBSCRIBE_DOMAIN, &[]);
        let body = serde_json::json!({ "owner": owner, "nonce": nonce, "signature": sig });
        let base = self.base_url.clone();
        let v = py
            .detach(|| http_send_json("DELETE", &base, "/relay/unsubscribe", &body, None))
            .map_err(refused)?;
        json_to_py(py, &v)
    }

    /// `POST /relay/send/{dest}` — enqueue an ALREADY-SEALED `ciphertext`
    /// (hex str or bytes) to `dest`'s inbox, paying `deposit`. Unauthenticated.
    fn send<'py>(
        &self,
        py: Python<'py>,
        dest: &Bound<'_, PyAny>,
        ciphertext: &Bound<'_, PyAny>,
        deposit: u64,
    ) -> PyResult<Bound<'py, PyAny>> {
        let dest_hex = hex::encode(parse_32(dest, "dest")?);
        use base64::Engine;
        let payload_b64 = base64::engine::general_purpose::STANDARD.encode(ciphertext_bytes(ciphertext)?);
        let body = serde_json::json!({ "sender": self.owner_hex(py), "payload": payload_b64, "deposit": deposit });
        let base = self.base_url.clone();
        let path = format!("/relay/send/{dest_hex}");
        let v = py
            .detach(|| http_send_json("POST", &base, &path, &body, None))
            .map_err(err)?;
        json_to_py(py, &v)
    }

    /// `GET /relay/drain` — drain up to `max` messages (owner-signed under
    /// `dregg-relay-drain-v1` over `owner || nonce || max_le(u64)`), each with
    /// its full dequeue (custody) proof. Recompute each body's `content_hash`
    /// before trusting it.
    #[pyo3(signature = (max=100))]
    fn drain<'py>(&self, py: Python<'py>, max: u64) -> PyResult<Bound<'py, PyAny>> {
        let (owner, nonce, sig) = self.signed_tuple(py, RELAY_DRAIN_DOMAIN, &max.to_le_bytes());
        let base = self.base_url.clone();
        let path = format!("/relay/drain?owner={owner}&nonce={nonce}&max={max}&signature={sig}");
        let v = py
            .detach(|| http_get_json(&base, &path, None))
            .map_err(err)?;
        json_to_py(py, &v)
    }

    /// `GET /relay/inbox/{id}/status` — this inbox's queue depth + root.
    fn inbox_status<'py>(&self, py: Python<'py>) -> PyResult<Bound<'py, PyAny>> {
        let owner = self.owner_hex(py);
        let base = self.base_url.clone();
        let path = format!("/relay/inbox/{owner}/status");
        let v = py
            .detach(|| http_get_json(&base, &path, None))
            .map_err(err)?;
        json_to_py(py, &v)
    }

    fn __repr__(&self, py: Python<'_>) -> String {
        format!("Mailbox(owner={:?}, relay={:?})", self.owner_hex(py), self.base_url)
    }
}

fn ciphertext_bytes(obj: &Bound<'_, PyAny>) -> PyResult<Vec<u8>> {
    if let Ok(b) = obj.extract::<&[u8]>() {
        return Ok(b.to_vec());
    }
    if let Ok(s) = obj.extract::<&str>() {
        return hex::decode(s.trim())
            .map_err(|e| PyValueError::new_err(format!("ciphertext: invalid hex: {e}")));
    }
    Err(PyTypeError::new_err("ciphertext: expected bytes or hex str"))
}

/// Minimal getrandom fill (the binding already pulls `rand` transitively via
/// the SDK; use the OS source directly to avoid a new dep surface).
fn getrandom_fill(buf: &mut [u8]) {
    // `ureq`/`rustls` already pull `getrandom`; reuse it.
    getrandom::getrandom(buf).expect("OS RNG unavailable");
}

/// **Attested query** — the light-client read surface (Noun 2's Python face).
///
/// No identity, no signing. Fetches the federation-attested state roots,
/// finalized checkpoints, and a committed turn's full-turn STARK so a caller
/// can hand them to a verifier or trust them under the federation's signature
/// threshold.
///
/// Honest scope: verifying a STARK or a threshold signature is a Rust/Lean
/// operation — this surfaces the artifacts to verify elsewhere, it does not
/// return a checked verdict on its own. (The `signatures` / `qc_votes` count is
/// the trust signal.)
///
/// ```python
/// aq = dregg.AttestedQuery("https://devnet.example")
/// aq.attested_roots()        # federation-signed state roots (+ signature count)
/// aq.checkpoint()            # latest finalized checkpoint (+ qc votes)
/// aq.turn_proof(turn_hash)   # full-turn STARK bytes (verify elsewhere) or None
/// ```
#[pyclass(module = "dregg")]
struct AttestedQuery {
    node_url: String,
}

#[pymethods]
impl AttestedQuery {
    #[new]
    fn new(node_url: &str) -> Self {
        AttestedQuery {
            node_url: node_url.trim_end_matches('/').to_string(),
        }
    }

    fn get<'py>(&self, py: Python<'py>, path: String) -> PyResult<Bound<'py, PyAny>> {
        let base = self.node_url.clone();
        let v = py
            .detach(move || http_get_json(&base, &path, None))
            .map_err(err)?;
        json_to_py(py, &v)
    }

    /// `GET /federation/roots` — the federation-attested state roots.
    fn attested_roots<'py>(&self, py: Python<'py>) -> PyResult<Bound<'py, PyAny>> {
        self.get(py, "/federation/roots".to_string())
    }

    /// `GET /checkpoint/latest` — the latest finalized checkpoint.
    fn checkpoint<'py>(&self, py: Python<'py>) -> PyResult<Bound<'py, PyAny>> {
        self.get(py, "/checkpoint/latest".to_string())
    }

    /// `GET /checkpoint/{height}` — the finalized checkpoint at `height`.
    fn checkpoint_at<'py>(&self, py: Python<'py>, height: u64) -> PyResult<Bound<'py, PyAny>> {
        self.get(py, format!("/checkpoint/{height}"))
    }

    /// `GET /api/turn/{hash}/proof` — the full-turn STARK for a committed turn,
    /// or `None` while the node's prove pool is still producing it. The proof
    /// is BYTES — verify it with the Rust/Lean `verify_full_turn`, not here.
    fn turn_proof<'py>(&self, py: Python<'py>, turn_hash: &str) -> PyResult<Option<Bound<'py, PyAny>>> {
        let base = self.node_url.clone();
        let url = format!("{}/api/turn/{}/proof", base.trim_end_matches('/'), turn_hash.trim());
        let fetched = py.detach(move || match http_agent().get(&url).call() {
            Ok(resp) => resp
                .into_json::<serde_json::Value>()
                .map(Some)
                .map_err(|e| format!("GET {url}: {e}")),
            Err(ureq::Error::Status(404, _)) => Ok(None),
            Err(e) => Err(format!("GET {url}: {e}")),
        });
        match fetched.map_err(err)? {
            Some(v) => Ok(Some(json_to_py(py, &v)?)),
            None => Ok(None),
        }
    }

    fn __repr__(&self) -> String {
        format!("AttestedQuery(node_url={:?})", self.node_url)
    }
}

/// Devnet faucet (`POST /api/faucet`): materialize a hosted cell and/or claim
/// computrons (max 10000 per request). Pass `public_key=` to install a
/// canonical hosted cell with a real owner key — REQUIRED before that cell can
/// pass Ed25519 turn authorization.
///
/// ```python
/// dregg.faucet(node_url, ident.cell_id, 2000, public_key=ident.public_key)
/// ```
#[pyfunction]
#[pyo3(signature = (node_url, recipient, amount, public_key=None, devnet_key=None))]
fn faucet<'py>(
    py: Python<'py>,
    node_url: &str,
    recipient: &Bound<'_, PyAny>,
    amount: u64,
    public_key: Option<&Bound<'_, PyAny>>,
    devnet_key: Option<&str>,
) -> PyResult<Bound<'py, PyAny>> {
    let recipient_hex = hex::encode(parse_32(recipient, "recipient")?);
    let mut body = serde_json::json!({ "recipient": recipient_hex, "amount": amount });
    if let Some(pk) = public_key {
        body["public_key"] = serde_json::Value::String(hex::encode(parse_32(pk, "public_key")?));
    }
    let base = node_url.trim_end_matches('/').to_string();
    let key = resolve_devnet_key(devnet_key);
    let v = py
        .detach(move || http_send_json("POST", &base, "/api/faucet", &body, key.as_deref()))
        .map_err(refused)?;
    json_to_py(py, &v)
}

// ─── kernel: which executor this module embeds (the verified Lean kernel, or not) ───

/// The canonical mini-wire for the proof-of-execution probe: two cells
/// (1: balance 50, 2: balance 10), actor 1 transfers 5 from 1 to 2. The verified
/// `Exec.recKExec` must accept (`"ok":1`) and move the balances to 45/15. The grammar is
/// `Dregg2.Exec.FFI.parseInput`'s (the same wire the state differential drives).
const KERNEL_PROBE_WIRE: &str = "{\"cells\":[[1,{\"rec\":[[\"balance\",{\"int\":50}]]}],\
                                 [2,{\"rec\":[[\"balance\",{\"int\":10}]]}]],\
                                 \"actor\":1,\"src\":1,\"dst\":2,\"amt\":5}";

/// Report which kernel this extension module embeds — and PROVE it by running one
/// verified transfer step through it.
///
/// Returns a dict:
///   * `"lean"`            — the verified Lean kernel is linked and its runtime
///                           initialized (this module links `libleanshared` +
///                           `libdregg_lean.a`; False means the Rust fallback).
///   * `"producer"`        — `"lean"` when the verified executor is the authoritative
///                           state producer (the SWAP default; `DREGG_LEAN_PRODUCER=0`
///                           opts out), else `"rust"`.
///   * `"verified_step_ok"`  — a REAL call: one transfer driven through the PROVED
///                           `Exec.recKExec` (`dregg_record_kernel_step`) accepted and
///                           conserved balances. Not a link bit — the kernel executed.
///   * `"verified_step_out"` — the raw output wire from that call (evidence).
#[pyfunction]
fn kernel(py: Python<'_>) -> PyResult<Bound<'_, PyDict>> {
    let d = PyDict::new(py);
    let lean = dregg_lean_ffi::lean_available();
    d.set_item("lean", lean)?;
    d.set_item(
        "producer",
        if lean && dregg_sdk::runtime::lean_producer_env_enabled() {
            "lean"
        } else {
            "rust"
        },
    )?;
    if lean {
        match dregg_lean_ffi::shadow_record_kernel_step(KERNEL_PROBE_WIRE) {
            Ok(out) => {
                // Accept (`"ok":1`) AND the verified post-balances (45/15) — a kernel that
                // answered but computed the wrong state must not read as ok.
                let ok = out.contains("\"ok\":1")
                    && out.contains("[\"balance\",{\"int\":45}]")
                    && out.contains("[\"balance\",{\"int\":15}]");
                d.set_item("verified_step_ok", ok)?;
                d.set_item("verified_step_out", out)?;
            }
            Err(e) => {
                d.set_item("verified_step_ok", false)?;
                d.set_item("verified_step_out", format!("error: {e}"))?;
            }
        }
    } else {
        d.set_item("verified_step_ok", false)?;
        d.set_item("verified_step_out", "lean kernel not linked (rust fallback)")?;
    }
    Ok(d)
}

// ─── module ───

#[pymodule]
fn dregg(py: Python<'_>, m: &Bound<'_, PyModule>) -> PyResult<()> {
    // Embedded-cdylib Lean runtime init: perform the one-time C-embedding ritual
    // (`lean_initialize_runtime_module` + the Dregg2 module initializers +
    // `lean_io_mark_end_initialization`, via the ffi crate's `dregg_ffi_init` under a
    // OnceLock) NOW, at `import dregg` on the importing thread — not lazily from
    // whichever thread first touches a verified path. A build without the kernel (or a
    // failed init) leaves the module importable; `kernel()` then reports the fallback.
    let _ = dregg_lean_ffi::lean_available();
    m.add_class::<Identity>()?;
    m.add_class::<TurnBuilder>()?;
    m.add_class::<AuthorizedTurn>()?;
    m.add_class::<Receipt>()?;
    m.add_class::<ReceiptStream>()?;
    m.add_class::<Trustline>()?;
    m.add_class::<Channels>()?;
    m.add_class::<Mailbox>()?;
    m.add_class::<AttestedQuery>()?;
    m.add_class::<SseJsonStream>()?;
    m.add_function(wrap_pyfunction!(subscribe, m)?)?;
    m.add_function(wrap_pyfunction!(faucet, m)?)?;
    m.add_function(wrap_pyfunction!(explain, m)?)?;
    m.add_function(wrap_pyfunction!(list_profiles, m)?)?;
    m.add_function(wrap_pyfunction!(kernel, m)?)?;
    m.add("DreggError", py.get_type::<DreggError>())?;
    m.add("DreggRefused", py.get_type::<DreggRefused>())?;

    // dregg.program — the constraint-language atoms.
    let program = PyModule::new(py, "program")?;
    program.add_class::<PyConstraint>()?;
    program.add_function(wrap_pyfunction!(sender_is, &program)?)?;
    program.add_function(wrap_pyfunction!(sender_in_slot, &program)?)?;
    program.add_function(wrap_pyfunction!(balance_gte, &program)?)?;
    program.add_function(wrap_pyfunction!(balance_lte, &program)?)?;
    program.add_function(wrap_pyfunction!(preimage_gate, &program)?)?;
    program.add_function(wrap_pyfunction!(immutable, &program)?)?;
    program.add_function(wrap_pyfunction!(write_once, &program)?)?;
    program.add_function(wrap_pyfunction!(any_of, &program)?)?;
    program.add_function(wrap_pyfunction!(descriptor, &program)?)?;
    m.add_submodule(&program)?;
    // Make `import dregg.program` / `from dregg import program` resolve.
    py.import("sys")?
        .getattr("modules")?
        .set_item("dregg.program", &program)?;

    Ok(())
}
