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

fn post_signed_turn(node_url: &str, body: &[u8]) -> Result<serde_json::Value, String> {
    let url = format!("{node_url}/api/turns/submit-signed");
    let mut req = http_agent()
        .post(&url)
        .set("content-type", "application/octet-stream");
    // The shared devnet protects the /api/turns/* aliases behind a bearer.
    if let Ok(token) = std::env::var("DREGG_API_TOKEN") {
        let token = token.trim().to_string();
        if !token.is_empty() {
            req = req.set("authorization", &format!("Bearer {token}"));
        }
    }
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
    #[pyo3(signature = (node_url, federation_id=None))]
    fn turn(
        slf: &Bound<'_, Self>,
        node_url: &str,
        federation_id: Option<&Bound<'_, PyAny>>,
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
        })
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
        let response = py
            .detach(|| post_signed_turn(&node_url, &body))
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

// ─── module ───

#[pymodule]
fn dregg(py: Python<'_>, m: &Bound<'_, PyModule>) -> PyResult<()> {
    m.add_class::<Identity>()?;
    m.add_class::<TurnBuilder>()?;
    m.add_class::<AuthorizedTurn>()?;
    m.add_class::<Receipt>()?;
    m.add_class::<ReceiptStream>()?;
    m.add_function(wrap_pyfunction!(subscribe, m)?)?;
    m.add_function(wrap_pyfunction!(explain, m)?)?;
    m.add_function(wrap_pyfunction!(list_profiles, m)?)?;
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
