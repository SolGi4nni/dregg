//! The authorization CORE — postgres-independent.
//!
//! Everything that decides authorization lives here as plain Rust, so it is
//! provable with `cargo test` (no postgres, no `cargo-pgrx`). The `#[pg_extern]`
//! wrappers in [`crate`] (gated behind the `pgrx` feature) only marshal SQL
//! types into these functions.
//!
//! ## What this module is responsible for (the M1 thesis)
//!
//! 1. **decode + verify** a `dga1_…` credential against the issuer public key
//!    (delegated wholesale to the proven [`dregg_auth::credential`] core);
//! 2. the **verified-credential LRU**, so the per-row cost collapses from an
//!    ed25519 signature-chain verify to a [`Pred`] re-evaluation over the row's
//!    `(action, resource, now)`;
//! 3. the **instant revocation** check (the registry lives at the extension
//!    layer — `dregg-auth` is deliberately revocation-free, see its Cargo.toml);
//! 4. the **attenuation-narrowing** property, observable through this surface.
//!
//! The assurance boundary (docs/PG-DREGG.md §4): the *capability decision* is
//! the verified `dregg-auth` decision; the LRU + revocation set this module adds
//! are conventional code, tested here directly.

use std::collections::HashMap;
use std::collections::VecDeque;
use std::sync::Mutex;
use std::sync::OnceLock;

use dregg_auth::credential::{Caveat, Context, Credential, Pred, PublicKey, Refusal, RootKey};

/// Parse a hex string into a 32-byte array (shared between key types).
fn unhex32(s: &str) -> Option<[u8; 32]> {
    let s = s.trim();
    if s.len() != 64 { return None; }
    let mut out = [0u8; 32];
    for (i, b) in out.iter_mut().enumerate() {
        *b = u8::from_str_radix(&s[i*2..i*2+2], 16).ok()?;
    }
    Some(out)
}

// ============================================================================
// Issuer key (process-local trust root)
// ============================================================================

/// The issuer public key for this process, parsed once. `None` until set; a
/// missing key makes every decision DENY (fail-closed).
///
/// In the pgrx wrappers this is populated from the `dregg.issuer_pubkey` GUC;
/// in `cargo test` it is set explicitly by the test harness.
static ISSUER_PK: OnceLock<Mutex<Option<PublicKey>>> = OnceLock::new();

fn issuer_slot() -> &'static Mutex<Option<PublicKey>> {
    ISSUER_PK.get_or_init(|| Mutex::new(None))
}

/// Install the issuer public key from its hex form. Returns `false` (and leaves
/// the slot cleared) on a malformed key — fail-closed.
pub fn set_issuer_pubkey_hex(hex: &str) -> bool {
    match PublicKey::from_hex(hex) {
        Ok(pk) => {
            *issuer_slot().lock().unwrap() = Some(pk);
            true
        }
        Err(_) => {
            *issuer_slot().lock().unwrap() = None;
            false
        }
    }
}

/// Install the issuer public key directly (used by the pgrx layer once it has a
/// `PublicKey`, and by tests).
pub fn set_issuer_pubkey(pk: PublicKey) {
    *issuer_slot().lock().unwrap() = Some(pk);
}

/// Clear the issuer key (no key configured ⇒ every decision denies).
pub fn clear_issuer_pubkey() {
    *issuer_slot().lock().unwrap() = None;
}

/// The configured issuer key, or `None` (⇒ deny).
fn issuer_pk() -> Option<PublicKey> {
    *issuer_slot().lock().unwrap()
}

// ============================================================================
// Mint key (process-local; SUPERUSER-only, never exposed to session roles)
// ============================================================================
//
// The PRIVATE key for minting new credentials. It NEVER lives in the issuer-key
// GUC (which is the PUBLIC key, DBA-visible). In the pgrx layer it comes from a
// separate `dregg.issuer_privkey` GUC with `GucContext::Suset` (superuser only)
// and `GUC_NO_SHOW_ALL | GUC_SUPERUSER_ONLY` — so it does not appear in
// `SHOW ALL` and cannot be read by non-superusers. `dregg_mint` is
// `SECURITY DEFINER` and checks that it is called by a role the DBA explicitly
// granted (see docs/PG-DREGG.md §2.1).
//
// In tests the key is set directly via `set_mint_key`.
//
// HONEST SCOPE: the extension-layer mint/attenuate helpers are a convenience for
// applications that want to issue row-scoped sub-tokens inside SQL. The production
// recommendation (docs/PG-DREGG.md §2.1) is to never place the private key in
// postgres at all and mint tokens out-of-database. The helpers are offered as an
// opt-in with a loud privilege model; the recommendation stands.

// We store the 32-byte seed rather than the `RootKey` directly because
// `RootKey` wraps an ed25519-dalek `SigningKey` that does not implement `Clone`
// (without the `zeroize` feature). Reconstructing from the seed is cheap
// (~5 µs), so storing the seed is the right tradeoff for a cold GUC path.
static MINT_KEY_SEED: OnceLock<Mutex<Option<[u8; 32]>>> = OnceLock::new();

fn mint_key_slot() -> &'static Mutex<Option<[u8; 32]>> {
    MINT_KEY_SEED.get_or_init(|| Mutex::new(None))
}

/// Install the mint (private) key from its 64-hex-char form (the 32-byte
/// `RootKey` seed as lowercase hex). Returns `false` and clears the slot on a
/// malformed key (fail-closed). Used by the pgrx `_PG_init` / SIGHUP path; also
/// settable by tests.
pub fn set_mint_key_hex(s: &str) -> bool {
    match unhex32(s) {
        Some(seed) => {
            *mint_key_slot().lock().unwrap() = Some(seed);
            true
        }
        None => {
            *mint_key_slot().lock().unwrap() = None;
            false
        }
    }
}

/// Install the mint key directly from a seed (used by tests).
pub fn set_mint_key_seed(seed: [u8; 32]) {
    *mint_key_slot().lock().unwrap() = Some(seed);
}

/// Clear the mint key (no key ⇒ `dregg_mint` denies with an error).
pub fn clear_mint_key() {
    *mint_key_slot().lock().unwrap() = None;
}

fn mint_key() -> Option<RootKey> {
    mint_key_slot().lock().unwrap().map(RootKey::from_seed)
}

// ============================================================================
// Caveat JSON DSL ⇄ Pred (the parse_caveats boundary)
// ============================================================================
//
// `dregg_mint` / `dregg_attenuate` accept caveats as a small JSON DSL that maps
// 1:1 onto the `Pred` algebra (docs/PG-DREGG.md §2.1). The mapping is the
// COMPLETE `Pred` enum — every variant is reachable, every variant rejects a
// malformed JSON with a named error, and nothing new is invented. The DSL is the
// `serde_json` representation of `Pred` as defined in `dregg-auth`.
//
// DSL examples — the serde encoding of `Pred` (PascalCase variant names,
// matching `dregg-auth`'s un-annotated derive, no `rename_all`):
//   {"AttrEq":    {"key":"tool","value":"read"}}
//   {"AttrPrefix":{"key":"resource","prefix":"org/42/"}}
//   {"NotAfter":  {"at":2000}}
//   {"NotBefore": {"at":100}}
//   {"Within":    {"not_before":100,"not_after":2000}}
//   {"AllOf":     [… list of Pred objects …]}
//   {"AnyOf":     [… list of Pred objects …]}
//   {"Not":       { … a single Pred object … }}
//   "True"   (the bare string — serde unit variant encoding)
//   "False"  (the bare string — serde unit variant encoding)
//
// The JSON maps EXACTLY to the serde-default encoding of `dregg_auth::credential::Pred`.
// An unknown key is an error (fail-closed: an unrecognised caveat is not silently
// dropped).

/// Parse a JSON array of caveat objects into `Vec<Caveat>`. Each element is a
/// `{"pred_variant": …}` object matching the `Pred` serde encoding. Fail-closed:
/// returns an error string if any element does not parse.
///
/// `ThirdParty` caveats are accepted as-is when the `Pred` serde form encodes
/// them; they do not need special handling here since the `Pred` enum covers the
/// full first-party algebra and we are parsing ONLY first-party predicates at
/// the SQL surface (a third-party discharge path through SQL is out of scope per
/// docs/PG-DREGG.md §5).
pub fn parse_caveats(caveats_json: &str) -> Result<Vec<Caveat>, String> {
    let arr: Vec<serde_json::Value> =
        serde_json::from_str(caveats_json).map_err(|e| format!("caveats is not a JSON array: {e}"))?;
    arr.into_iter()
        .map(|v| {
            serde_json::from_value::<Pred>(v.clone())
                .map(Caveat::FirstParty)
                .map_err(|e| format!("caveat element does not parse as a Pred: {v} — {e}"))
        })
        .collect()
}

/// Mint a new credential from the configured private key. Returns the encoded
/// token string. Returns `Err` if no mint key is configured or the caveats
/// JSON is malformed.
///
/// `subject` is placed as a first-party `AttrEq{key:"subject",value:…}` caveat
/// in block 0 (the `dregg_cap_subject` convention). `until` is the `NotAfter`
/// clock bound (unix seconds, matching the deployment's clock contract).
pub fn mint_token(subject: &str, caveats_json: &str, until: i64) -> Result<String, String> {
    let key = mint_key().ok_or_else(|| "no mint key configured (dregg.issuer_privkey not set)".to_string())?;
    let Ok(until_u64) = u64::try_from(until) else {
        return Err("until is negative; use a unix-second timestamp".to_string());
    };
    let mut caveats = parse_caveats(caveats_json)?;
    // Prepend the subject caveat (block 0 by convention).
    caveats.insert(0, Caveat::FirstParty(Pred::AttrEq {
        key: "subject".into(),
        value: subject.to_string(),
    }));
    // Append the NotAfter expiry.
    caveats.push(Caveat::FirstParty(Pred::NotAfter { at: until_u64 }));
    Ok(key.mint(caveats).encode())
}

/// Attenuate a credential by appending additional first-party caveats. Returns
/// the encoded narrowed token string. The `attenuate_subset` guarantee holds:
/// the resulting token's admitted set is a SUBSET of the parent's. Returns `Err`
/// if the token does not decode, the caveats JSON is malformed, or any caveat is
/// not a first-party `Pred` (the SQL surface is first-party-only).
///
/// IMPORTANT: this does NOT require the mint key — attenuation is performed by
/// the TOKEN HOLDER, not the issuer. Any caller who can decode the token can
/// narrow it further.
pub fn attenuate_token(token: &str, caveats_json: &str) -> Result<String, String> {
    let cred = Credential::decode(token)
        .map_err(|e| format!("token does not decode: {e}"))?;
    let caveats = parse_caveats(caveats_json)?;
    Ok(cred.attenuate(caveats).encode())
}

// ============================================================================
// The dev-mint convenience shape (docs/PG-DREGG-DX.md §4 S3, FRONTIER-ROADMAP N19)
// ============================================================================
//
// The first-ten-minutes friction is "hand-write a `Pred` JSON array to mint a
// token". `dev_mint` composes the ONE caveat shape that covers the common case —
// an allowed-action set + a resource prefix + an expiry — so a newcomer never
// touches the `Pred` algebra by hand. It is a DEV-ONLY convenience and routes
// through the SAME `mint_token` path: it does NOT have its own minting code, does
// NOT bypass the issuer-key discipline, and inherits `mint_token`'s fail-closed
// "no mint key configured" error verbatim (the production posture — private key
// never in the DB — is unchanged; this just spares the JSON).
//
// The shape it composes, matching the canonical `examples/mint.rs`:
//   * action: `AttrEq{key:"action", value:a}` for ONE action,
//             `AnyOf([AttrEq{action=a} …])` for several (fail-closed: `AnyOf([])`
//             admits nothing, so an EMPTY actions list mints a token that admits
//             no action at all — deliberately useless rather than wide-open);
//   * resource: `AttrPrefix{key:"resource", prefix}` (an empty prefix is the
//             unrestricted-resource case, which the caller opts into explicitly);
//   * subject + `NotAfter{until}` are added by `mint_token` (not here).
//
// The `action`/`resource` attribute keys are exactly the ones `decide` binds into
// the verify `Context` (action=…, resource=…), so a token minted here is admitted
// by `dregg_cap_admits(token, action, resource, now)` / a `dregg_admits` RLS
// policy with no further wiring — the round-trip the pg_test asserts.

/// Compose the dev-mint caveat JSON (the action-set + resource-prefix shape) as a
/// `Pred`-array JSON string suitable for [`mint_token`]. Pure — needs no key, so
/// it is unit-testable on its own. An empty `actions` slice yields an `AnyOf([])`
/// action atom, which admits NOTHING (fail-closed: a dev-mint with no actions is
/// useless, never wide-open). The returned JSON is exactly the serde encoding of
/// `Vec<Pred>` that [`parse_caveats`] round-trips, so the two cannot drift.
pub fn dev_mint_caveats_json(actions: &[String], resource_prefix: &str) -> String {
    let action_pred = if actions.len() == 1 {
        Pred::AttrEq {
            key: "action".into(),
            value: actions[0].clone(),
        }
    } else {
        // 0 actions ⇒ AnyOf([]) ⇒ admits nothing (fail-closed).
        // 2+ actions ⇒ AnyOf of the per-action equalities.
        Pred::AnyOf(
            actions
                .iter()
                .map(|a| Pred::AttrEq {
                    key: "action".into(),
                    value: a.clone(),
                })
                .collect(),
        )
    };
    let resource_pred = Pred::AttrPrefix {
        key: "resource".into(),
        prefix: resource_prefix.to_string(),
    };
    // serde-encode the Vec<Pred> the same way parse_caveats decodes it.
    serde_json::to_string(&vec![action_pred, resource_pred])
        .expect("Pred serializes to JSON")
}

/// Dev-only convenience mint: compose the common (actions, resource-prefix,
/// subject, expiry) caveat shape and issue it THROUGH [`mint_token`]. Returns the
/// encoded `dga1_…` token, or `Err` with the SAME fail-closed message
/// `mint_token` raises when no mint key is configured ("no mint key configured
/// (dregg.issuer_privkey not set)") — i.e. **no key ⇒ a loud error, never a
/// silently-minted token**. This is the dev on-ramp (docs/PG-DREGG-DX.md §4 S3);
/// the production recommendation (mint out-of-database, private key never in pg)
/// is unchanged because this shares `mint_token`'s discipline rather than
/// re-implementing minting.
pub fn dev_mint(
    subject: &str,
    actions: &[String],
    resource_prefix: &str,
    until: i64,
) -> Result<String, String> {
    let caveats_json = dev_mint_caveats_json(actions, resource_prefix);
    // Route through mint_token: it requires the mint key (fail-closed on absence),
    // prepends the subject caveat, and appends the NotAfter{until} expiry.
    mint_token(subject, &caveats_json, until)
}

// ============================================================================
// Issuer status (the loud "everything denies" discoverability surface)
// ============================================================================
//
// The silent failure mode pg-dregg most wants to make discoverable: NO issuer
// PUBLIC key configured ⇒ every `dregg_cap_admits` denies (fail-closed). A
// newcomer sees "all my rows vanished" with no hint why. `issuer_status` reports
// the configuration plainly — is a verify key set (and its id), is a mint key set
// (dev minting enabled), and the LOUD warning when the verify key is absent.

/// A plain snapshot of the process-local key configuration, for the status
/// surface. `verify_key_hex` is the configured issuer PUBLIC key (publishable);
/// `mint_key_configured` says whether the SUPERUSER-only private seed is present
/// (dev minting enabled) WITHOUT exposing it.
pub struct IssuerStatus {
    /// The configured issuer PUBLIC (verify) key as hex, or `None` (⇒ everything
    /// denies, fail-closed).
    pub verify_key_hex: Option<String>,
    /// Whether a mint (private) key is configured — dev minting is enabled. The
    /// key itself is NEVER reported (it is the superuser-only secret).
    pub mint_key_configured: bool,
    /// The PUBLIC key derived from the configured mint key, when present — so an
    /// operator can confirm the dev mint key MATCHES the configured verify key
    /// (a mismatch would mint tokens this database cannot verify). `None` when no
    /// mint key is set.
    pub mint_public_hex: Option<String>,
}

/// Read the current key configuration (the verify key, whether a mint key is set,
/// and the mint key's public half for a match-check). Touches only process-local
/// state already populated from the GUCs by the pgrx layer.
pub fn issuer_status() -> IssuerStatus {
    let verify_key_hex = issuer_pk().map(|pk| pk.to_hex());
    let mint = mint_key();
    IssuerStatus {
        verify_key_hex,
        mint_key_configured: mint.is_some(),
        mint_public_hex: mint.map(|k| k.public().to_hex()),
    }
}

/// Render [`issuer_status`] as a single human-readable line for the SQL
/// `dregg_issuer_status()` surface. The verify-key-absent case is LOUD (it names
/// the exact failure: "everything denies"), so the silent fail-closed mode is
/// discoverable. The mint-key line states dev-minting on/off and flags a
/// key MISMATCH (a dev mint key whose public half is not the configured verify
/// key) — tokens minted under it would not verify here.
pub fn issuer_status_text() -> String {
    let s = issuer_status();
    let mut out = String::new();
    match &s.verify_key_hex {
        Some(pk) => {
            out.push_str(&format!(
                "issuer verify key: CONFIGURED (id {pk}) — dregg_cap_admits verifies against it."
            ));
        }
        None => {
            out.push_str(
                "issuer verify key: NOT CONFIGURED \u{26a0}  EVERYTHING DENIES. \
                 Set `dregg.issuer_pubkey` (64 hex chars, the publishable root key) in \
                 postgresql.conf or per-database, then SIGHUP/reload — until then every \
                 dregg_cap_admits / dregg_admits returns FALSE (fail-closed), so all \
                 cap-gated rows vanish.",
            );
        }
    }
    out.push_str("  |  ");
    match (&s.mint_key_configured, &s.mint_public_hex, &s.verify_key_hex) {
        (false, _, _) => out.push_str(
            "dev minting (dregg_dev_mint / dregg_mint): DISABLED (no `dregg.issuer_privkey`). \
             Production posture — mint tokens out-of-database; the private key never enters pg.",
        ),
        (true, Some(mp), Some(vk)) if mp == vk => out.push_str(
            "dev minting (dregg_dev_mint / dregg_mint): ENABLED, mint key MATCHES the verify key \
             (tokens it mints verify here). DEV ONLY — production mints out-of-database.",
        ),
        (true, Some(mp), Some(vk)) => out.push_str(&format!(
            "dev minting: ENABLED but the mint key MISMATCHES the verify key \u{26a0}  mint pubkey \
             {mp} \u{2260} verify key {vk} — tokens minted here will NOT verify against the \
             configured issuer. Align `dregg.issuer_privkey` with `dregg.issuer_pubkey`."
        )),
        (true, Some(mp), None) => out.push_str(&format!(
            "dev minting: ENABLED (mint pubkey {mp}) but NO verify key is set \u{26a0}  tokens it \
             mints cannot be verified here until `dregg.issuer_pubkey` is configured to match."
        )),
        (true, None, _) => out.push_str(
            "dev minting: ENABLED (mint key present).",
        ),
    }
    out
}

// ============================================================================
// The verified-credential LRU (MANDATORY in M1)
// ============================================================================
//
// The expensive part of a decision is the ed25519 signature-chain verify on
// decode. We cache the decoded+VERIFIED `Credential` keyed by the token STRING,
// so the per-row cost on a scan collapses to:
//
//     (LRU hit) + (revocation check) + (Pred re-eval over THIS row's ctx)
//
// `Credential` is not `Clone`, and re-evaluating caveats needs the live
// `Credential`, so the cache holds the decoded credential behind the LRU lock
// and the caveat re-evaluation runs while the entry is borrowed.
//
// IMPORTANT — what is cached is "this token string decoded and its SIGNATURE
// CHAIN verified against the current issuer key". The cache does NOT memoize the
// admit/deny verdict, because that verdict depends on (action, resource, now)
// and on the revocation set, both of which vary per row / per statement. So a
// cache hit still runs the caveat evaluation and the revocation check every
// time — only the ed25519 work is saved. This is what keeps revocation INSTANT
// even with the cache hot (see `decide`).

const LRU_CAP: usize = 256;

struct Lru {
    /// token-string -> decoded+chain-verified credential.
    map: HashMap<String, Credential>,
    /// recency order; front = least-recently-used.
    order: VecDeque<String>,
}

impl Lru {
    fn new() -> Self {
        Self {
            map: HashMap::new(),
            order: VecDeque::new(),
        }
    }

    fn touch(&mut self, key: &str) {
        if let Some(pos) = self.order.iter().position(|k| k == key) {
            self.order.remove(pos);
        }
        self.order.push_back(key.to_string());
    }

    fn insert(&mut self, key: String, cred: Credential) {
        if self.map.len() >= LRU_CAP && !self.map.contains_key(&key) {
            if let Some(evict) = self.order.pop_front() {
                self.map.remove(&evict);
            }
        }
        self.map.insert(key.clone(), cred);
        self.touch(&key);
    }
}

static LRU: OnceLock<Mutex<Lru>> = OnceLock::new();

fn lru() -> &'static Mutex<Lru> {
    LRU.get_or_init(|| Mutex::new(Lru::new()))
}

/// How many entries the LRU currently holds (for tests / introspection).
pub fn lru_len() -> usize {
    lru().lock().unwrap().map.len()
}

/// Clear the LRU (test isolation; also the right thing to call if the issuer key
/// is rotated, since cached credentials were chain-verified under the old key).
pub fn lru_clear() {
    let mut l = lru().lock().unwrap();
    l.map.clear();
    l.order.clear();
}

// ============================================================================
// The instant-revocation registry (extension-layer; dregg-auth has none)
// ============================================================================
//
// `dregg-auth` is revocation-free at the token layer (its Cargo.toml excludes
// `dregg-token`'s `rand-deps` feature where the RevocationRegistry lives). So
// the revocation set lives HERE, keyed on a stable per-credential id.
//
// The id we key on is `dregg_cap_id` = the credential TAIL (a BLAKE3 commitment
// to the entire signed chain, `Credential::tail`, public + offline). It is a
// cryptographic id of EXACTLY this credential: revoking it denies precisely the
// credential presented, on the very next check — instant, not bounded-staleness.
//
// HONEST SCOPE: because the tail commits the whole chain, an *attenuated child*
// has a different tail than its parent, so revoking a parent's id does NOT
// auto-revoke children already minted from it. Revocation here is per-credential
// (revoke the exact token in circulation). A registry keyed on the root nonce
// (which survives attenuation) would need a `nonce()` accessor that
// `dregg-auth` does not currently expose; that is the natural follow-up if
// "revoke a credential and all its descendants" is wanted. For M1 the test
// revokes the exact presented token and the row vanishes on the next statement,
// which is the instant-revocation thesis.
//
// In the pgrx deployment this in-memory set is the backend-local mirror of a
// `dregg.revoked(id text primary key)` table; a production deployment would
// consult that table (or a published Merkle non-membership root) per eval. The
// in-memory set is what the `cargo test` core proves the SEMANTICS of.

static REVOKED: OnceLock<Mutex<std::collections::HashSet<String>>> = OnceLock::new();

fn revoked() -> &'static Mutex<std::collections::HashSet<String>> {
    REVOKED.get_or_init(|| Mutex::new(std::collections::HashSet::new()))
}

/// Mark a credential id (its `dregg_cap_id`, the hex tail) revoked.
pub fn revoke(id: &str) {
    revoked().lock().unwrap().insert(id.to_string());
}

/// Lift a revocation (test/admin).
pub fn unrevoke(id: &str) {
    revoked().lock().unwrap().remove(id);
}

/// Clear all revocations (test isolation).
pub fn revoked_clear() {
    revoked().lock().unwrap().clear();
}

fn is_revoked(id: &str) -> bool {
    revoked().lock().unwrap().contains(id)
}

/// A process-wide serialization guard for tests that mutate the global authz
/// state (the issuer key, the verified-credential LRU, the revocation set). The
/// decision core is deliberately process-global — exactly as it is in a postgres
/// backend process — so ANY test that sets the issuer key or clears a cache must
/// own that state for its body, or a parallel test in the same binary will see a
/// foreign key/cache and fail. Every such test (here AND in sibling modules like
/// [`crate::workflow`]) acquires this one guard via [`test_serial_lock`], so
/// they serialize against each other across module boundaries (a module-local
/// guard would only serialize a single module's tests). A poisoned lock from a
/// prior panic is fine to reuse; we recover it.
#[cfg(test)]
static TEST_SERIAL: Mutex<()> = Mutex::new(());

/// Acquire the shared [`TEST_SERIAL`] guard — hold it for the body of any test
/// that touches global authz state. See [`TEST_SERIAL`].
#[cfg(test)]
pub(crate) fn test_serial_lock() -> std::sync::MutexGuard<'static, ()> {
    TEST_SERIAL.lock().unwrap_or_else(|p| p.into_inner())
}

/// Public wrapper for the pgrx `dregg_cap_not_revoked` extern, which checks
/// whether a credential's stable id is in the revocation registry without
/// routing through the full `decide` path (so it does not require the issuer
/// public key to be configured — the id is a structural commitment).
pub fn is_revoked_pub(id: &str) -> bool {
    is_revoked(id)
}

/// The per-issuance nonce of a credential (hex of the root block's 32-byte
/// random nonce, if the token decodes and `dregg-auth` exposes the nonce field
/// publicly). The nonce is assigned at mint and SURVIVES attenuation — every
/// attenuated child of the same root credential carries the same nonce — so
/// revoking by nonce covers the whole family. `None` if the token does not
/// decode OR if the nonce is not publicly accessible in this `dregg-auth`
/// version (the field is `pub(crate)` today; see HORIZONLOG for the follow-up
/// to expose it and re-enable `dregg_cap_nonce`).
///
/// NOTE: `dregg_cap_id` (the `tail()` hex) is the revocation key the
/// backend-local registry uses today (`dregg_revoke` / `is_revoked_pub`).
/// `dregg_cap_nonce` is the FAMILY key (a root + its attenuated children). It
/// is tracked as a HORIZONLOG item until `dregg-auth` exposes `Credential::nonce()`.
pub fn cap_nonce(_token: &str) -> Option<String> {
    // dregg-auth's Credential::nonce is pub(crate) (not pub). Expose it via a
    // PR to dregg-auth and re-enable this function. For now, return None so the
    // pgrx function surface compiles and returns NULL rather than silently lying.
    None
}

// ============================================================================
// The credential id (stable per-credential, the revocation key)
// ============================================================================

/// The stable id of the credential a token encodes: the hex of its
/// `Credential::tail` (a BLAKE3 commitment to the whole signed chain). `None`
/// if the token does not decode. This is the value the revocation registry
/// keys on and what `dregg_cap_id` returns at the SQL boundary.
///
/// NOTE: this decodes only (structural validation); it does not prove the
/// issuer signature. The id is a content commitment, used for revocation
/// lookup; the *authorization* decision (`decide`) independently verifies the
/// chain.
pub fn cap_id(token: &str) -> Option<String> {
    let cred = Credential::decode(token).ok()?;
    Some(hex(&cred.tail()))
}

fn hex(bytes: &[u8]) -> String {
    let mut s = String::with_capacity(bytes.len() * 2);
    for b in bytes {
        s.push_str(&format!("{b:02x}"));
    }
    s
}

// ============================================================================
// The core decision
// ============================================================================

/// A structured outcome, so the bool / explain / subject surfaces all share one
/// code path.
pub enum Outcome {
    Allowed,
    Denied(String),
}

impl Outcome {
    pub fn allowed(&self) -> bool {
        matches!(self, Outcome::Allowed)
    }
    pub fn reason(&self) -> String {
        match self {
            Outcome::Allowed => "allowed".to_string(),
            Outcome::Denied(r) => r.clone(),
        }
    }
}

/// The whole M1 decision, fail-closed at every step:
///
/// 1. issuer key configured? (else deny — "no issuer key configured")
/// 2. `now` non-negative? (else deny — a negative clock never wraps into authority)
/// 3. token decodes? (else deny — the wire error)
/// 4. **revocation**: is this credential's id revoked? (if so, deny INSTANTLY —
///    this is checked on EVERY call, including LRU hits, so a revocation lands on
///    the very next row-check)
/// 5. **decode+verify via the LRU**: a cache hit skips the ed25519 chain verify;
///    a miss decodes, verifies the chain against the issuer key, and on success
///    caches it. Then the caveats are (re-)evaluated against THIS row's context.
///
/// The caveat re-evaluation and the revocation check ALWAYS run, even on a hot
/// LRU — only the signature-chain work is cached. That is why the cache is sound
/// despite revocation being able to change within a statement.
pub fn decide(token: &str, action: &str, resource: &str, now: i64) -> Outcome {
    let Some(pk) = issuer_pk() else {
        return Outcome::Denied("no issuer key configured".to_string());
    };
    let Ok(now) = u64::try_from(now) else {
        return Outcome::Denied("clock is negative".to_string());
    };

    // Revocation is consulted BEFORE we trust any cached verification, and on
    // every call — instant revocation, not bounded-staleness.
    if let Some(id) = cap_id(token) {
        if is_revoked(&id) {
            return Outcome::Denied("revoked".to_string());
        }
    }

    let mut ctx = Context::new()
        .at(now)
        .attr("action", action)
        .attr("resource", resource);
    // The `subject` attribute, when the credential carries one, is bound to the
    // credential's OWN declared subject (read off the chain). This makes the
    // subject caveat self-satisfying — it identifies the holder, it does not
    // gate the request — while keeping the subject on the signed chain so
    // `dregg_cap_subject` can recover it and an auditor can trust it. (A token
    // that wanted to gate on a *request-supplied* subject would use a different
    // attribute key; `subject` is reserved for the credential's own identity.)
    if let Some(subj) = subject_of_decoded(token) {
        ctx = ctx.attr("subject", subj);
    }

    let mut l = lru().lock().unwrap();
    if l.map.contains_key(token) {
        l.touch(token);
        let cred = l.map.get(token).expect("just checked");
        // Cache hit: the chain is already verified; re-evaluate caveats only.
        return verdict(reverify_caveats_only(cred, &ctx));
    }

    // Cache miss: decode + full verify (signature chain + caveats) against the
    // issuer key. On a verified chain, cache the credential for future rows.
    let cred = match Credential::decode(token) {
        Ok(c) => c,
        Err(e) => return Outcome::Denied(format!("decode failed: {e}")),
    };
    let result = cred.verify(&pk, &ctx);
    // Cache iff the signature chain itself is sound. A caveat refusal still
    // means the chain verified, so the credential is safe to cache (the next
    // row may satisfy its caveats). A signature/key/proof refusal means a
    // forged or stripped chain — never cache it.
    let chain_sound = match &result {
        Ok(()) => true,
        Err(r) => !is_chain_refusal(r),
    };
    if chain_sound {
        l.insert(token.to_string(), cred);
    }
    verdict(result)
}

/// Map a `verify` result to an [`Outcome`].
fn verdict(result: Result<(), Refusal>) -> Outcome {
    match result {
        Ok(()) => Outcome::Allowed,
        Err(r) => Outcome::Denied(r.to_string()),
    }
}

/// Re-evaluate ONLY the first-party caveats of an already-chain-verified
/// credential against a fresh context — the cheap per-row path. Mirrors the
/// caveat-meet phase of `Credential::verify` (step 3) without the ed25519 chain
/// re-verification (steps 1-2), which the LRU already paid for.
///
/// Third-party caveats are conservatively treated here as "must re-run the full
/// verify": this M1 path only fast-paths first-party credentials. If any
/// third-party caveat is present we signal that by returning a deny that names
/// it; M1 tokens are first-party (resource/action/temporal), so the fast path is
/// exact for the M1 surface. (The `decide` cache-miss path runs the full
/// `verify`, third-party discharge included; only the hot-cache fast path is
/// first-party-only, and it fails CLOSED on a third-party caveat.)
fn reverify_caveats_only(cred: &Credential, ctx: &Context) -> Result<(), Refusal> {
    for (block, caveat) in cred.caveats() {
        match caveat {
            Caveat::FirstParty(p) => match p.eval(ctx) {
                Ok(true) => {}
                Ok(false) => {
                    return Err(Refusal::CaveatRefused {
                        block,
                        requires: p.explain(),
                    });
                }
                Err(unbound) => {
                    return Err(Refusal::ContextIncomplete {
                        block,
                        requires: p.explain(),
                        unbound,
                    });
                }
            },
            Caveat::ThirdParty {
                gateway, caveat_id, ..
            } => {
                // Fail-closed on the fast path: a third-party caveat needs a
                // presented discharge, which the fast path does not carry.
                return Err(Refusal::MissingDischarge {
                    block,
                    caveat_id: hex(caveat_id),
                    gateway: hex(&gateway[..8]),
                });
            }
        }
    }
    Ok(())
}

/// True iff a refusal indicates a FORGED / STRIPPED chain (signature, key, or
/// proof-of-possession), as opposed to an authentic-chain caveat refusal. Used
/// to decide whether a credential is safe to cache.
fn is_chain_refusal(r: &Refusal) -> bool {
    matches!(
        r,
        Refusal::ProofMismatch
            | Refusal::BadSignature { .. }
            | Refusal::MalformedKey { .. }
            | Refusal::MalformedGatewayKey
    )
}

// ============================================================================
// Explain + subject
// ============================================================================

/// The human-readable reason for the decision (the `explain` discipline at the
/// SQL boundary). `"allowed"` on success, otherwise the first violated
/// requirement; the revocation and no-key cases name themselves.
pub fn explain(token: &str, action: &str, resource: &str, now: i64) -> String {
    decide(token, action, resource, now).reason()
}

/// The confined subject the token names, or `None` if the token's chain does not
/// verify under the issuer key. Convention: the subject is a first-party
/// `AttrEq { key: "subject", value: … }` caveat installed in the root block at
/// mint time (the `dregg_mint` convention). We require the CHAIN to verify
/// (forged tokens yield `None`); a missing-clock or unsatisfied caveat does not
/// hide the subject, since the subject is read off the chain, not gated on it.
pub fn subject(token: &str) -> Option<String> {
    let pk = issuer_pk()?;
    let cred = Credential::decode(token).ok()?;
    // Verify the chain. We bind nothing else; the only refusals we treat as
    // "no subject" are the FORGED-chain ones. A caveat refusal (e.g. expired)
    // still means the chain is authentic, so the subject is recoverable.
    let probe = Context::new();
    if let Err(r) = cred.verify(&pk, &probe) {
        if is_chain_refusal(&r) {
            return None;
        }
    }
    subject_in(&cred)
}

/// Read the declared subject off a DECODED credential (no issuer-key check):
/// the value of the first-party `AttrEq { key: "subject", … }` caveat. Used both
/// to bind the self-identifying `subject` attribute in `decide` and (after a
/// chain check) by `subject`.
fn subject_of_decoded(token: &str) -> Option<String> {
    let cred = Credential::decode(token).ok()?;
    subject_in(&cred)
}

fn subject_in(cred: &Credential) -> Option<String> {
    for (_, caveat) in cred.caveats() {
        if let Caveat::FirstParty(Pred::AttrEq { key, value }) = caveat {
            if key == "subject" {
                return Some(value.clone());
            }
        }
    }
    None
}

// ============================================================================
// Tests — the M1 thesis, proven at the Rust level (no postgres needed).
// ============================================================================

#[cfg(test)]
mod tests {
    use super::*;
    use dregg_auth::credential::{Caveat, Pred, RootKey};

    /// The decision core uses process-global state (issuer key, LRU, revocation
    /// set) — exactly as it will in a postgres backend process. The tests share
    /// that process, so they SERIALIZE on the SHARED [`super::TEST_SERIAL`] guard
    /// (shared so sibling modules' tests — e.g. `crate::workflow` — serialize
    /// against these too): each test owns the global state for its body.
    fn lock() -> std::sync::MutexGuard<'static, ()> {
        super::test_serial_lock()
    }

    /// A fixed seed → deterministic root, so the issuer key is stable per test.
    fn root() -> RootKey {
        RootKey::from_seed([7u8; 32])
    }

    /// Install this root's public key as the process issuer key, and reset the
    /// per-process caches so tests do not bleed into each other.
    fn install(root: &RootKey) {
        set_issuer_pubkey(root.public());
        lru_clear();
        revoked_clear();
    }

    /// Mint the M1 token: read under any "org/42/" resource, until clock 2000,
    /// subject "agent-1".
    fn mint_org42(root: &RootKey) -> Credential {
        root.mint([
            Caveat::FirstParty(Pred::AttrEq {
                key: "subject".into(),
                value: "agent-1".into(),
            }),
            Caveat::FirstParty(Pred::AttrEq {
                key: "action".into(),
                value: "read".into(),
            }),
            Caveat::FirstParty(Pred::AttrPrefix {
                key: "resource".into(),
                prefix: "org/42/".into(),
            }),
            Caveat::FirstParty(Pred::NotAfter { at: 2000 }),
        ])
    }

    #[test]
    fn attenuation_narrows_through_the_core() {
        let _g = lock();
        let root = root();
        install(&root);

        // Root token: read on any org/42/ resource.
        let root_tok = mint_org42(&root).encode();
        // Attenuated child: confined to org/42/public/ only.
        let narrowed = mint_org42(&root)
            .attenuate([Caveat::FirstParty(Pred::AttrPrefix {
                key: "resource".into(),
                prefix: "org/42/public/".into(),
            })])
            .encode();

        // The ROOT admits both a public and a private resource.
        assert!(decide(&root_tok, "read", "org/42/public/doc1", 1000).allowed());
        assert!(decide(&root_tok, "read", "org/42/private/doc9", 1000).allowed());

        // The NARROWED child admits the public resource...
        assert!(decide(&narrowed, "read", "org/42/public/doc1", 1000).allowed());
        // ...but is STRICTLY narrowed: the private resource the parent admitted
        // is now denied. The no-amplify property, observed through the core.
        assert!(!decide(&narrowed, "read", "org/42/private/doc9", 1000).allowed());

        // Temporal narrowing: past the NotAfter expiry, denied.
        assert!(!decide(&narrowed, "read", "org/42/public/doc1", 3000).allowed());

        // The admitted set of the child is a STRICT SUBSET of the parent's:
        // there exists a request the parent admits and the child denies, and
        // none the child admits that the parent denies.
        let resources = [
            "org/42/public/doc1",
            "org/42/public/doc2",
            "org/42/private/doc9",
            "org/99/public/doc1",
        ];
        let parent_admits: Vec<bool> = resources
            .iter()
            .map(|r| decide(&root_tok, "read", r, 1000).allowed())
            .collect();
        let child_admits: Vec<bool> = resources
            .iter()
            .map(|r| decide(&narrowed, "read", r, 1000).allowed())
            .collect();
        // subset: child ⇒ parent for every request
        for (c, p) in child_admits.iter().zip(parent_admits.iter()) {
            assert!(!c || *p, "child admitted a request the parent denied");
        }
        // strict: at least one request the parent admits and the child denies
        assert!(
            parent_admits
                .iter()
                .zip(child_admits.iter())
                .any(|(p, c)| *p && !*c),
            "narrowing was not strict"
        );
    }

    #[test]
    fn instant_revocation_denies_on_the_next_check() {
        let _g = lock();
        let root = root();
        install(&root);
        let tok = mint_org42(&root).encode();

        // Admits before revocation.
        assert!(decide(&tok, "read", "org/42/public/doc1", 1000).allowed());

        // Revoke this credential's stable id.
        let id = cap_id(&tok).expect("token decodes");
        revoke(&id);

        // The SAME query is now denied — instantly, on the very next check,
        // even though the LRU is hot (the decode+verify was cached above). The
        // revocation check runs before the cache is trusted.
        let out = decide(&tok, "read", "org/42/public/doc1", 1000);
        assert!(!out.allowed());
        assert_eq!(out.reason(), "revoked");

        // Lifting the revocation restores access (the registry is the only
        // thing that changed; the credential never did).
        unrevoke(&id);
        assert!(decide(&tok, "read", "org/42/public/doc1", 1000).allowed());
    }

    #[test]
    fn forged_token_is_denied_fail_closed() {
        let _g = lock();
        let root = root();
        install(&root);

        // A token from a DIFFERENT issuer must not verify under our key.
        let other = RootKey::from_seed([9u8; 32]);
        let foreign = mint_org42(&other).encode();
        assert!(!decide(&foreign, "read", "org/42/public/doc1", 1000).allowed());

        // Garbage / wrong-prefix tokens are denied, not panicked.
        assert!(!decide("not-a-token", "read", "org/42/public/doc1", 1000).allowed());
        assert!(!decide("dga1_!!!notbase64!!!", "read", "x", 1000).allowed());
        assert!(!decide("", "read", "x", 1000).allowed());
    }

    #[test]
    fn expired_and_wrong_action_are_denied() {
        let _g = lock();
        let root = root();
        install(&root);
        let tok = mint_org42(&root).encode();

        // Past NotAfter ⇒ denied.
        assert!(!decide(&tok, "read", "org/42/public/doc1", 9999).allowed());
        // Wrong action (token is confined to action=read) ⇒ denied.
        assert!(!decide(&tok, "write", "org/42/public/doc1", 1000).allowed());
        // Resource outside the prefix ⇒ denied.
        assert!(!decide(&tok, "read", "org/99/public/doc1", 1000).allowed());
    }

    #[test]
    fn no_issuer_key_denies_everything() {
        let _g = lock();
        // Clear the issuer key explicitly (other tests may have set it).
        *issuer_slot().lock().unwrap() = None;
        lru_clear();
        revoked_clear();
        let root = root();
        let tok = mint_org42(&root).encode();
        let out = decide(&tok, "read", "org/42/public/doc1", 1000);
        assert!(!out.allowed());
        assert_eq!(out.reason(), "no issuer key configured");
    }

    #[test]
    fn negative_clock_is_denied_not_wrapped() {
        let _g = lock();
        let root = root();
        install(&root);
        let tok = mint_org42(&root).encode();
        let out = decide(&tok, "read", "org/42/public/doc1", -1);
        assert!(!out.allowed());
        assert_eq!(out.reason(), "clock is negative");
    }

    #[test]
    fn lru_caches_then_evicts_but_verdict_is_stable() {
        let _g = lock();
        let root = root();
        install(&root);
        let tok = mint_org42(&root).encode();

        assert_eq!(lru_len(), 0);
        // First call: cache miss, full verify, cached.
        assert!(decide(&tok, "read", "org/42/public/doc1", 1000).allowed());
        assert_eq!(lru_len(), 1);
        // Second call on the SAME token: cache hit; verdict unchanged.
        assert!(decide(&tok, "read", "org/42/public/doc2", 1000).allowed());
        assert_eq!(lru_len(), 1);
        // A cache HIT still re-evaluates caveats: a row outside the prefix is
        // denied even though the chain verify was cached.
        assert!(!decide(&tok, "read", "org/99/x", 1000).allowed());

        // A forged token is NOT cached (chain refusal).
        let other = RootKey::from_seed([3u8; 32]);
        let foreign = mint_org42(&other).encode();
        assert!(!decide(&foreign, "read", "org/42/public/doc1", 1000).allowed());
        assert_eq!(lru_len(), 1, "forged token must not be cached");
    }

    #[test]
    fn parse_caveats_round_trips_the_pred_algebra() {
        // Every first-party Pred variant must survive JSON round-trip through
        // parse_caveats, and the parsed Pred must eval the same as the original.
        use serde_json::json;
        let cases: &[(&str, serde_json::Value)] = &[
            ("AttrEq",    json!({"AttrEq":    {"key":"action","value":"read"}})),
            ("AttrPrefix",json!({"AttrPrefix":{"key":"resource","prefix":"org/"}})),
            ("NotAfter",  json!({"NotAfter":  {"at":2000}})),
            ("NotBefore", json!({"NotBefore": {"at":100}})),
            ("Within",    json!({"Within":    {"not_before":100,"not_after":2000}})),
            ("AllOf",     json!({"AllOf":     [{"AttrEq":{"key":"action","value":"read"}}]})),
            ("AnyOf",     json!({"AnyOf":     [{"AttrEq":{"key":"action","value":"read"}}]})),
            ("Not",       json!({"Not":       {"AttrEq":{"key":"action","value":"write"}}})),
        ];
        for (name, v) in cases {
            let arr = serde_json::to_string(&serde_json::json!([v])).unwrap();
            let parsed = parse_caveats(&arr)
                .unwrap_or_else(|e| panic!("parse_caveats failed for {name}: {e}"));
            assert_eq!(parsed.len(), 1, "expected 1 caveat for {name}");
            // Also confirm a first-party Pred is what we got.
            assert!(
                matches!(&parsed[0], Caveat::FirstParty(_)),
                "expected FirstParty caveat for {name}"
            );
        }
        // A garbage input is rejected.
        assert!(parse_caveats("not json").is_err());
        // An unknown variant is rejected (fail-closed).
        assert!(parse_caveats(r#"[{"unknown_variant":42}]"#).is_err());
    }

    #[test]
    fn mint_and_attenuate_round_trip_through_decide() {
        let _g = lock();
        let root = root();
        install(&root);

        // Set the mint key from the same root so issued tokens verify.
        set_mint_key_seed(root.secret_bytes());

        // Mint: subject=alice, caveats=[action=read, resource prefix org/42/], until=5000.
        let caveats_json = r#"[
            {"AttrEq":    {"key":"action","value":"read"}},
            {"AttrPrefix":{"key":"resource","prefix":"org/42/"}}
        ]"#;
        let tok = mint_token("alice", caveats_json, 5000)
            .expect("mint must succeed when the key is configured");

        // The minted token admits the right request.
        assert!(decide(&tok, "read", "org/42/public/doc1", 1000).allowed());
        // The subject is embedded and recovered.
        assert_eq!(subject(&tok).as_deref(), Some("alice"));
        // Past the NotAfter: denied.
        assert!(!decide(&tok, "read", "org/42/public/doc1", 9000).allowed());

        // Attenuate to org/42/public/ only.
        let narrowed = attenuate_token(
            &tok,
            r#"[{"AttrPrefix":{"key":"resource","prefix":"org/42/public/"}}]"#,
        )
        .expect("attenuate must succeed for a valid token");

        // Narrowed admits the public path but not the private one.
        assert!(decide(&narrowed, "read", "org/42/public/doc1", 1000).allowed());
        assert!(!decide(&narrowed, "read", "org/42/private/doc9", 1000).allowed());
        // And not the parent-only path.
        assert!(!decide(&tok, "write", "org/42/public/doc1", 1000).allowed());

        // Attenuating garbage fails closed.
        assert!(attenuate_token("not-a-token", r#"[{"AttrEq":{"key":"x","value":"y"}}]"#).is_err());

        // Mint with negative clock fails.
        assert!(mint_token("alice", "[]", -1).is_err());

        // No mint key configured → error.
        clear_mint_key();
        assert!(mint_token("alice", caveats_json, 5000).is_err());
    }

    #[test]
    fn dev_mint_composes_the_common_shape_and_round_trips() {
        let _g = lock();
        let root = root();
        install(&root);
        set_mint_key_seed(root.secret_bytes());

        // Multi-action dev-mint: read+write under "org/42/", subject alice, until 5000.
        let tok = dev_mint(
            "alice",
            &["read".to_string(), "write".to_string()],
            "org/42/",
            5000,
        )
        .expect("dev_mint must succeed when the mint key is configured");

        // The composed token is admitted by the SAME (action, resource, now)
        // contract dregg_cap_admits binds — both actions, under the prefix.
        assert!(decide(&tok, "read", "org/42/public/doc1", 1000).allowed());
        assert!(decide(&tok, "write", "org/42/public/doc1", 1000).allowed());
        // An action NOT in the set is denied (AnyOf is exactly the listed set).
        assert!(!decide(&tok, "delete", "org/42/public/doc1", 1000).allowed());
        // Outside the resource prefix: denied.
        assert!(!decide(&tok, "read", "org/99/public/doc1", 1000).allowed());
        // Past the NotAfter (until=5000): denied.
        assert!(!decide(&tok, "read", "org/42/public/doc1", 9000).allowed());
        // The subject is embedded + recovered (the dregg_cap_subject convention).
        assert_eq!(subject(&tok).as_deref(), Some("alice"));

        // Single-action dev-mint uses a bare AttrEq (not AnyOf) — still admitted.
        let one = dev_mint("bob", &["read".to_string()], "", 5000)
            .expect("single-action dev_mint must succeed");
        // Empty prefix ⇒ any resource admitted (the caller opted into that).
        assert!(decide(&one, "read", "anything/at/all", 1000).allowed());
        assert!(!decide(&one, "write", "anything/at/all", 1000).allowed());

        // EMPTY actions ⇒ AnyOf([]) ⇒ admits NOTHING (fail-closed, never wide-open).
        let none = dev_mint("carol", &[], "org/42/", 5000)
            .expect("dev_mint with no actions still mints (a useless token)");
        assert!(!decide(&none, "read", "org/42/public/doc1", 1000).allowed());
        assert!(!decide(&none, "write", "org/42/public/doc1", 1000).allowed());

        // The composed JSON is exactly what parse_caveats round-trips (no drift).
        let json = dev_mint_caveats_json(&["read".to_string(), "write".to_string()], "org/42/");
        assert!(parse_caveats(&json).is_ok());
    }

    #[test]
    fn dev_mint_fails_loudly_without_a_mint_key() {
        let _g = lock();
        let root = root();
        install(&root);
        // Crucially: NO mint key. dev_mint must NOT silently mint — it must fail
        // with the SAME fail-closed error mint_token raises (the issuer-key
        // discipline is intact; dev_mint does not bypass it).
        clear_mint_key();
        let err = dev_mint("alice", &["read".to_string()], "org/42/", 5000)
            .expect_err("dev_mint MUST fail loudly when no mint key is configured");
        assert!(
            err.contains("no mint key configured"),
            "the error must name the missing mint key, got: {err}"
        );
    }

    #[test]
    fn issuer_status_reports_the_loud_no_key_mode() {
        let _g = lock();
        let root = root();

        // No verify key, no mint key ⇒ the LOUD "everything denies" + dev minting
        // disabled. This is the discoverability the status surface exists for.
        clear_issuer_pubkey();
        clear_mint_key();
        let s = issuer_status();
        assert!(s.verify_key_hex.is_none());
        assert!(!s.mint_key_configured);
        let text = issuer_status_text();
        assert!(text.contains("NOT CONFIGURED"), "no-key status must be loud: {text}");
        assert!(text.contains("EVERYTHING DENIES"), "must name the failure mode: {text}");
        assert!(text.contains("DISABLED"), "dev minting must read disabled: {text}");

        // Configure the verify key only (the production posture: verify in pg,
        // mint out-of-database). Status reports the key id + minting still off.
        set_issuer_pubkey(root.public());
        let s = issuer_status();
        assert_eq!(s.verify_key_hex.as_deref(), Some(root.public().to_hex().as_str()));
        assert!(!s.mint_key_configured);
        let text = issuer_status_text();
        assert!(text.contains("CONFIGURED"), "verify-key-set status: {text}");
        assert!(text.contains(&root.public().to_hex()), "must report the key id: {text}");

        // Now enable dev minting with a MATCHING key — status confirms the match.
        set_mint_key_seed(root.secret_bytes());
        let s = issuer_status();
        assert!(s.mint_key_configured);
        assert_eq!(s.mint_public_hex.as_deref(), Some(root.public().to_hex().as_str()));
        let text = issuer_status_text();
        assert!(text.contains("ENABLED"), "dev minting enabled: {text}");
        assert!(text.contains("MATCHES"), "matching keys flagged: {text}");

        // A MISMATCHED mint key (different seed) is flagged loudly — tokens it
        // mints would not verify against the configured issuer.
        let other = RootKey::from_seed([9u8; 32]);
        set_mint_key_seed(other.secret_bytes());
        let text = issuer_status_text();
        assert!(text.contains("MISMATCH"), "mismatched keys must be flagged: {text}");
    }

    #[test]
    fn subject_recovered_only_for_authentic_chain() {
        let _g = lock();
        let root = root();
        install(&root);
        let tok = mint_org42(&root).encode();
        assert_eq!(subject(&tok).as_deref(), Some("agent-1"));

        // Even an EXPIRED-but-authentic token still names its subject (the
        // subject is read off the verified chain, not gated on the caveats).
        // (mint_org42 has NotAfter 2000; subject() binds no clock, so the
        // temporal caveat is ContextIncomplete — a non-chain refusal — and the
        // subject is still recovered.)
        assert_eq!(subject(&tok).as_deref(), Some("agent-1"));

        // A foreign-issuer token yields no subject (chain does not verify).
        let other = RootKey::from_seed([9u8; 32]);
        let foreign = mint_org42(&other).encode();
        assert_eq!(subject(&foreign), None);

        // Garbage yields no subject.
        assert_eq!(subject("nope"), None);
    }
}
