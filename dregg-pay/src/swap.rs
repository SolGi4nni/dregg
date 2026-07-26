//! [`JupiterSwap`] — the pile→fuel **swap execution**: convert the treasury's illiquid
//! `$DREGG` pile into USDC fuel over the `$DREGG`→SOL→USDC Jupiter route, **behind an
//! operator-held [`Signer`]** and **authorized by a governance vote**.
//!
//! # Who authorizes, who signs — the two independent gates
//!
//! A swap moves treasury value, so it is gated twice and NEITHER gate is automated:
//!
//! * **The vote authorizes.** A [`SwapAuthorization`] is minted ONLY by a passed
//!   liquidity-event vote ([`crate::governance`]). It is stamped by the operator's
//!   [`GovernanceAuthority`] key (a certification of the tally outcome) and binds the
//!   exact `amount`, `min_out`, and the two mints. [`JupiterSwap::execute`] REFUSES
//!   any authorization it cannot verify against the configured authority public key —
//!   a forged or wrong-authority authorization is [`SwapError::Unauthorized`]. There is
//!   no `execute`-without-authorization path: the value type is required.
//! * **The operator signs.** The on-chain swap transaction is signed by an
//!   operator-held [`Signer`]. `dregg-pay` NEVER holds the key: [`MockSigner`] is the
//!   throwaway test signer (real ed25519, no network); the production path injects the
//!   operator's secured signer (KMS/HSM). [`JupiterSwap::build_unsigned`] builds the
//!   exact bytes the operator signs — for the real venue these are the **Solana message
//!   of a Jupiter v6 swap transaction** — so a real deployment hands the operator an
//!   unsigned transaction and takes the signature back; the key stays with the operator.
//!
//! # The real route+tx construction ([`JupiterVenue`])
//!
//! The swap-execution seam ([`SwapVenue`]) is injected exactly like the pricing oracle's
//! [`HttpGet`](crate::pricing::HttpGet). [`JupiterVenue`] is the real path:
//!
//! 1. **Quote.** `GET {api_base}/quote?inputMint={dregg}&outputMint={usdc}&amount={in}&slippageBps={bps}&swapMode=ExactIn`
//!    — Jupiter finds the best `$DREGG`→SOL→USDC path (the SOL leg is implicit in the
//!    returned `routePlan`). [`parse_jupiter_quote`] parses `outAmount`, `slippageBps`,
//!    and the per-hop `routePlan` (and validates the quote is for the exact mint pair).
//! 2. **Build.** `POST {api_base}/swap` with `{"quoteResponse": <the quote>, "userPublicKey": <operator pubkey>, ...}`
//!    — Jupiter returns a base64 `swapTransaction`. [`JupiterVenue`] base64-decodes it to
//!    the real unsigned versioned-transaction bytes and extracts the exact **Solana
//!    message** the operator signs (past the empty signature slots).
//!
//! The GET/POST transports are the injected [`HttpGet`](crate::pricing::HttpGet) /
//! [`HttpPost`] seams, so the core carries **no `reqwest`/`tokio`** and the whole
//! build path is driven in tests over a `MockJupiter` that returns a canned route — no
//! network, no funds. On a (mock) success the treasury pile
//! ([`Treasury::dregg_balance`]) moves DOWN by `amount` and the fuel tank
//! ([`Treasury::usdc_balance`]) moves UP by the realized USDC (the quoted amount on the
//! mock path), floored by the authorization's `min_out`.
//!
//! # Honest scope — what a live swap still needs
//!
//! The **quote + tx build** are real here and driven end-to-end. A live mainnet swap
//! additionally needs: (1) a real [`HttpGet`](crate::pricing::HttpGet)/[`HttpPost`]
//! bound to `reqwest` (the operator's transport), (2) the operator's secured [`Signer`]
//! (KMS/HSM) over [`UnsignedSwapTx::message`], and (3) broadcast — splicing the operator
//! signature into [`UnsignedSwapTx::tx_bytes`] and `sendTransaction` to the RPC, then
//! reading the *realized* out-amount from the confirmed transaction (the mock path uses
//! the quoted amount as realized). Mainnet is a config flip on ember's go; custody
//! remains the signer.

use base64::{Engine as _, engine::general_purpose::STANDARD as BASE64};
use ed25519_dalek::{Signature, Signer as _, SigningKey, Verifier as _, VerifyingKey};

use crate::pricing::HttpGet;
use crate::treasury::{Treasury, TreasuryStore};

// ─────────────────────────────────────────────────────────────────────────────
// The operator signer seam — dregg-pay NEVER holds a key
// ─────────────────────────────────────────────────────────────────────────────

/// Why a signer backend failed.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum SignerError {
    /// The signing backend (HSM / KMS / local key) failed to produce a signature.
    Backend(String),
}

impl std::fmt::Display for SignerError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            SignerError::Backend(e) => write!(f, "signer backend error: {e}"),
        }
    }
}

impl std::error::Error for SignerError {}

/// An **operator-held** transaction signer. The key lives with the operator (a local
/// secured key, a KMS, an HSM) — `dregg-pay` only ever calls [`Signer::sign`] and reads
/// [`Signer::public_key`]; it holds no key itself. This is the seam that keeps
/// settlement a deliberate operator action, never an automated key-in-code.
pub trait Signer {
    /// The signer's ed25519 public key (32 bytes) — the operator authority whose
    /// signature the venue / chain verifies.
    fn public_key(&self) -> [u8; 32];

    /// Sign `message`, returning a 64-byte ed25519 signature. On the real path this is
    /// the operator's secured backend; in tests [`MockSigner`] signs with a throwaway
    /// key (real crypto, no network).
    fn sign(&self, message: &[u8]) -> Result<[u8; 64], SignerError>;
}

/// A throwaway ed25519 signer for driven tests. NEVER a real operator key — built from
/// a fixed test seed. It performs REAL ed25519 signing so the driven tests exercise the
/// genuine signature path (the same shape a KMS/HSM signer satisfies), with no funds and
/// no network.
pub struct MockSigner {
    key: SigningKey,
}

impl MockSigner {
    /// A mock signer from a throwaway 32-byte seed. Never a real operator key.
    pub fn from_seed(seed: [u8; 32]) -> Self {
        MockSigner {
            key: SigningKey::from_bytes(&seed),
        }
    }
}

impl Signer for MockSigner {
    fn public_key(&self) -> [u8; 32] {
        self.key.verifying_key().to_bytes()
    }

    fn sign(&self, message: &[u8]) -> Result<[u8; 64], SignerError> {
        Ok(self.key.sign(message).to_bytes())
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// The governance authority — certifies a passed vote into a SwapAuthorization
// ─────────────────────────────────────────────────────────────────────────────

/// The operator-held **governance authority**: the key that certifies a passed
/// liquidity-event vote into a [`SwapAuthorization`] the swap executor can verify without
/// re-running the vote. It is operator config (throwaway in tests), never a compiled-in
/// mainnet secret — the same custody law as [`Seed`](crate::config::Seed). The vote is
/// the decision; this key is only the attestation that binds the decision to an exact
/// swap so [`JupiterSwap`] can trust it at a distance.
pub struct GovernanceAuthority {
    key: SigningKey,
}

impl GovernanceAuthority {
    /// A governance authority from a throwaway 32-byte seed (tests) or the operator's
    /// configured certification key (prod). Never hardcoded to a mainnet value.
    pub fn from_seed(seed: [u8; 32]) -> Self {
        GovernanceAuthority {
            key: SigningKey::from_bytes(&seed),
        }
    }

    /// The authority public key — what [`JupiterSwap`] is configured with to verify a
    /// [`SwapAuthorization`].
    pub fn public_key(&self) -> [u8; 32] {
        self.key.verifying_key().to_bytes()
    }

    /// Certify a passed vote into a signed [`SwapAuthorization`]. Called by
    /// [`crate::governance`] ONLY once a real quorum has been reached — this method
    /// does not itself check the vote (that is governance's job); it binds the swap
    /// params so the executor can verify the outcome.
    pub(crate) fn authorize(
        &self,
        amount: u64,
        min_out: u64,
        dregg_mint: [u8; 32],
        usdc_mint: [u8; 32],
        poll_id: [u8; 32],
    ) -> SwapAuthorization {
        let msg = authorization_message(amount, min_out, &dregg_mint, &usdc_mint, &poll_id);
        let signature = self.key.sign(&msg).to_bytes();
        SwapAuthorization {
            amount,
            min_out,
            dregg_mint,
            usdc_mint,
            poll_id,
            signature,
        }
    }
}

/// The canonical bytes a [`SwapAuthorization`] is signed over — binds every field so a
/// signature can never be replayed onto a different amount, floor, mint pair, or poll.
fn authorization_message(
    amount: u64,
    min_out: u64,
    dregg_mint: &[u8; 32],
    usdc_mint: &[u8; 32],
    poll_id: &[u8; 32],
) -> Vec<u8> {
    let mut m = Vec::with_capacity(18 + 8 + 8 + 32 * 3);
    m.extend_from_slice(b"dregg-pay/swap-auth/v1");
    m.extend_from_slice(&amount.to_le_bytes());
    m.extend_from_slice(&min_out.to_le_bytes());
    m.extend_from_slice(dregg_mint);
    m.extend_from_slice(usdc_mint);
    m.extend_from_slice(poll_id);
    m
}

/// A governance-issued **authorization** for exactly one pile→fuel swap. Minted ONLY by
/// [`GovernanceAuthority::authorize`] (i.e. by a passed vote in [`crate::governance`]);
/// its `signature` is verified by [`JupiterSwap::execute`] against the configured
/// authority public key, so a hand-rolled / wrong-authority authorization is refused.
/// The `signature` field is private: no external code can forge one.
#[derive(Clone, Debug)]
pub struct SwapAuthorization {
    /// Atomic `$DREGG` authorized to swap out of the pile.
    pub amount: u64,
    /// The minimum atomic USDC the swap must realize (the slippage floor). A fill below
    /// this fails closed.
    pub min_out: u64,
    /// The `$DREGG` mint this authorization is bound to.
    pub dregg_mint: [u8; 32],
    /// The USDC mint this authorization is bound to.
    pub usdc_mint: [u8; 32],
    /// The liquidity-event poll whose passed vote authorized this swap (provenance).
    pub poll_id: [u8; 32],
    /// The governance authority's ed25519 signature over
    /// [`authorization_message`]. Private — only [`GovernanceAuthority::authorize`]
    /// produces a valid value, so a [`SwapAuthorization`] cannot be forged outside a vote.
    signature: [u8; 64],
}

impl SwapAuthorization {
    /// Verify this authorization against `authority_pk` — the real gate: recompute the
    /// canonical bytes and check the governance signature. A forged or wrong-authority
    /// authorization returns `false`.
    pub fn verify(&self, authority_pk: &[u8; 32]) -> bool {
        let Ok(vk) = VerifyingKey::from_bytes(authority_pk) else {
            return false;
        };
        let Ok(sig) = Signature::from_slice(&self.signature) else {
            return false;
        };
        let msg = authorization_message(
            self.amount,
            self.min_out,
            &self.dregg_mint,
            &self.usdc_mint,
            &self.poll_id,
        );
        vk.verify(&msg, &sig).is_ok()
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// The swap route
// ─────────────────────────────────────────────────────────────────────────────

/// The `$DREGG`→SOL→USDC route a swap realizes. The SOL leg is implicit in the Jupiter
/// route (Jupiter finds the best path through SOL); this records the endpoints and the
/// slippage floor the swap must clear.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SwapRoute {
    /// Atomic `$DREGG` sold into the route (out of the pile).
    pub dregg_in: u64,
    /// The minimum atomic USDC the route must return (the governance slippage floor).
    pub min_usdc_out: u64,
    /// The `$DREGG` mint (input).
    pub dregg_mint: [u8; 32],
    /// The USDC mint (output).
    pub usdc_mint: [u8; 32],
}

/// The canonical bytes a **mock** venue's operator signs — binds the route so an operator
/// signature can't be replayed onto a different swap. The real [`JupiterVenue`] signs the
/// Solana message of the actual Jupiter transaction instead (see [`JupiterVenue`]); this
/// minimal binding is what the fixed-rate [`MockSwapVenue`] custody-tests prove over.
pub fn swap_message(route: &SwapRoute) -> Vec<u8> {
    let mut m = Vec::with_capacity(18 + 8 + 8 + 32 * 2);
    m.extend_from_slice(b"dregg-pay/swap-tx/v1");
    m.extend_from_slice(&route.dregg_in.to_le_bytes());
    m.extend_from_slice(&route.min_usdc_out.to_le_bytes());
    m.extend_from_slice(&route.dregg_mint);
    m.extend_from_slice(&route.usdc_mint);
    m
}

// ─────────────────────────────────────────────────────────────────────────────
// Jupiter v6 quote parsing + the Solana message extraction
// ─────────────────────────────────────────────────────────────────────────────

/// One hop of a Jupiter `routePlan` — e.g. the `$DREGG`→SOL leg then the SOL→USDC leg.
/// Exposed so a caller (and the driven tests) can see the SOL leg the route goes through.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RouteHop {
    /// The AMM label for this hop (e.g. `Orca`, `Raydium`).
    pub label: String,
    /// The input mint of this hop (base58).
    pub input_mint: String,
    /// The output mint of this hop (base58).
    pub output_mint: String,
    /// Atomic input into this hop.
    pub in_amount: u64,
    /// Atomic output of this hop.
    pub out_amount: u64,
    /// The percent of the split routed through this hop.
    pub percent: u8,
}

/// A parsed Jupiter v6 quote: the promised out-amount, the slippage the quote was built
/// at, the per-hop route, and the RAW quote JSON (which the `/swap` POST echoes back).
#[derive(Clone, Debug)]
pub struct JupiterQuote {
    /// The promised atomic USDC out (`outAmount`).
    pub out_amount: u64,
    /// The slippage tolerance the quote was requested/returned with, in basis points.
    pub slippage_bps: u16,
    /// The `$DREGG`→SOL→USDC hops.
    pub hops: Vec<RouteHop>,
    /// The verbatim quote object — passed unchanged into the `/swap` request body.
    pub raw: serde_json::Value,
}

/// Parse a Jupiter v6 `/quote` response, validating it is a quote for exactly the
/// `expected_input`→`expected_output` mint pair (both base58). A quote for a different
/// pair — or with an unparseable amount — is a [`SwapError::Venue`] (fail closed: never
/// build a swap tx off a mis-bound quote).
pub fn parse_jupiter_quote(
    json: &str,
    expected_input: &str,
    expected_output: &str,
) -> Result<JupiterQuote, SwapError> {
    let raw: serde_json::Value = serde_json::from_str(json)
        .map_err(|e| SwapError::Venue(format!("quote JSON parse: {e}")))?;

    let input_mint = raw
        .get("inputMint")
        .and_then(|v| v.as_str())
        .ok_or_else(|| SwapError::Venue("quote missing inputMint".into()))?;
    let output_mint = raw
        .get("outputMint")
        .and_then(|v| v.as_str())
        .ok_or_else(|| SwapError::Venue("quote missing outputMint".into()))?;
    if input_mint != expected_input || output_mint != expected_output {
        return Err(SwapError::Venue(format!(
            "quote mint pair {input_mint}->{output_mint} does not match route {expected_input}->{expected_output}"
        )));
    }

    let out_amount = raw
        .get("outAmount")
        .and_then(parse_amount_field)
        .ok_or_else(|| SwapError::Venue("quote missing/invalid outAmount".into()))?;

    // Jupiter renders slippageBps as a number; default to 0 if absent.
    let slippage_bps = raw.get("slippageBps").and_then(|v| v.as_u64()).unwrap_or(0);
    let slippage_bps = u16::try_from(slippage_bps)
        .map_err(|_| SwapError::Venue("quote slippageBps out of range".into()))?;

    let mut hops = Vec::new();
    if let Some(plan) = raw.get("routePlan").and_then(|v| v.as_array()) {
        for step in plan {
            let info = step
                .get("swapInfo")
                .ok_or_else(|| SwapError::Venue("routePlan step missing swapInfo".into()))?;
            let get_str = |k: &str| -> Result<String, SwapError> {
                info.get(k)
                    .and_then(|v| v.as_str())
                    .map(|s| s.to_string())
                    .ok_or_else(|| SwapError::Venue(format!("routePlan step missing {k}")))
            };
            let get_amt = |k: &str| -> Result<u64, SwapError> {
                info.get(k)
                    .and_then(parse_amount_field)
                    .ok_or_else(|| SwapError::Venue(format!("routePlan step invalid {k}")))
            };
            let percent = step.get("percent").and_then(|v| v.as_u64()).unwrap_or(100);
            hops.push(RouteHop {
                label: get_str("label").unwrap_or_default(),
                input_mint: get_str("inputMint")?,
                output_mint: get_str("outputMint")?,
                in_amount: get_amt("inAmount")?,
                out_amount: get_amt("outAmount")?,
                percent: u8::try_from(percent).unwrap_or(100),
            });
        }
    }

    Ok(JupiterQuote {
        out_amount,
        slippage_bps,
        hops,
        raw,
    })
}

/// Jupiter renders atomic amounts as JSON strings (to survive `u64` past `2^53`), but
/// tolerate a bare number too.
fn parse_amount_field(v: &serde_json::Value) -> Option<u64> {
    match v {
        serde_json::Value::String(s) => s.parse::<u64>().ok(),
        serde_json::Value::Number(n) => n.as_u64(),
        _ => None,
    }
}

/// Decode a Solana `shortvec` (compact-u16) length prefix, returning
/// `(value, bytes_consumed)`. Used to skip past the signatures array of a serialized
/// transaction to find the message the operator actually signs.
fn decode_shortvec_len(bytes: &[u8]) -> Option<(usize, usize)> {
    let mut len: usize = 0;
    let mut size = 0usize;
    for &b in bytes {
        len |= ((b & 0x7f) as usize) << (size * 7);
        size += 1;
        if b & 0x80 == 0 {
            return Some((len, size));
        }
        if size >= 3 {
            return None;
        }
    }
    None
}

/// Extract the exact bytes a Solana signer signs from a serialized (unsigned) transaction:
/// a transaction is `[shortvec sig_count][sig_count × 64-byte signatures][message…]`, and
/// the signature is computed over the `message…` tail. A malformed/short transaction is a
/// [`SwapError::Venue`].
pub fn solana_sign_target(tx_bytes: &[u8]) -> Result<Vec<u8>, SwapError> {
    let (num_sigs, header) = decode_shortvec_len(tx_bytes)
        .ok_or_else(|| SwapError::Venue("transaction: bad signature-count prefix".into()))?;
    let start = header
        .checked_add(num_sigs.checked_mul(64).unwrap_or(usize::MAX))
        .unwrap_or(usize::MAX);
    if start > tx_bytes.len() {
        return Err(SwapError::Venue(
            "transaction shorter than its declared signatures".into(),
        ));
    }
    Ok(tx_bytes[start..].to_vec())
}

// ─────────────────────────────────────────────────────────────────────────────
// The swap-execution seam — the venue trait + the fixed-rate mock + the real Jupiter
// ─────────────────────────────────────────────────────────────────────────────

/// A built (unsigned) swap, the venue's product of quoting + constructing the transaction.
#[derive(Clone, Debug)]
pub struct BuiltSwap {
    /// The route this realizes.
    pub route: SwapRoute,
    /// The full unsigned serialized transaction (base64-decoded from Jupiter on the real
    /// path). The operator splices its signature into this to broadcast.
    pub tx_bytes: Vec<u8>,
    /// The exact bytes the operator signs — the Solana **message** of `tx_bytes` (past the
    /// empty signature slots), or the [`swap_message`] binding on the fixed-rate mock.
    pub sign_target: Vec<u8>,
    /// The atomic USDC the quote promised.
    pub quoted_out: u64,
    /// The slippage (bps) the quote/tx was built at.
    pub slippage_bps: u16,
    /// The `$DREGG`→SOL→USDC hops (empty on the fixed-rate mock).
    pub hops: Vec<RouteHop>,
    /// A tag identifying the venue that built this (`"jupiter-v6"` / `"mock-fixed-rate"`).
    pub venue_tag: String,
}

/// The swap-execution seam. Injected (not baked-in `reqwest`/`tokio`) exactly like the
/// pricing oracle's [`HttpGet`](crate::pricing::HttpGet):
///
/// * [`MockSwapVenue`] fills at a fixed `$DREGG`/USDC rate — driven, no network, no tx.
/// * [`JupiterVenue`] quotes the Jupiter v6 `/quote` API and builds the real `/swap`
///   transaction (driven over a `MockJupiter` in tests).
pub trait SwapVenue {
    /// Quote the atomic USDC a `route.dregg_in` sale would realize (best-effort — the
    /// realized amount is what [`SwapVenue::submit`] returns and the swap floors on).
    fn quote(&self, route: &SwapRoute) -> Result<u64, SwapError>;

    /// Build the unsigned swap transaction for `route`, owned/paid by `operator_pubkey`
    /// (the fee-payer/owner Jupiter builds the tx around). Returns the [`BuiltSwap`] whose
    /// `sign_target` the operator signs.
    fn build(&self, route: &SwapRoute, operator_pubkey: &[u8; 32]) -> Result<BuiltSwap, SwapError>;

    /// Submit the operator-signed swap, returning `(realized_usdc, tx_reference)`. The
    /// `signature` is the operator's signature over [`BuiltSwap::sign_target`]. On the
    /// mock path the realized amount is `quoted_out`; a live venue splices `signature`
    /// into `tx_bytes`, `sendTransaction`s it, and reads realized-out from the confirmed
    /// transaction.
    fn submit(
        &self,
        route: &SwapRoute,
        quoted_out: u64,
        tx_bytes: &[u8],
        signature: &[u8; 64],
    ) -> Result<(u64, String), SwapError>;
}

/// A mock swap venue: fills `$DREGG`→USDC at a fixed rational rate, no network, no real
/// transaction. It realizes `dregg_in * num / den` atomic USDC — e.g. `num = 5, den =
/// 1000` models `$0.005`/`$DREGG` at equal (6,6) decimals. Its `sign_target` is the
/// [`swap_message`] binding (a custody tooth), not a Jupiter transaction; use
/// [`JupiterVenue`] to drive the real route+tx build.
pub struct MockSwapVenue {
    num: u128,
    den: u128,
}

impl MockSwapVenue {
    /// A venue that realizes `dregg_in * num / den` atomic USDC (a fixed rational rate).
    pub fn new(num: u128, den: u128) -> Self {
        MockSwapVenue { num, den }
    }

    fn fill(&self, dregg_in: u64) -> u64 {
        u64::try_from((dregg_in as u128) * self.num / self.den).unwrap_or(u64::MAX)
    }
}

impl SwapVenue for MockSwapVenue {
    fn quote(&self, route: &SwapRoute) -> Result<u64, SwapError> {
        Ok(self.fill(route.dregg_in))
    }

    fn build(
        &self,
        route: &SwapRoute,
        _operator_pubkey: &[u8; 32],
    ) -> Result<BuiltSwap, SwapError> {
        let msg = swap_message(route);
        Ok(BuiltSwap {
            route: route.clone(),
            tx_bytes: msg.clone(),
            sign_target: msg,
            quoted_out: self.fill(route.dregg_in),
            slippage_bps: 0,
            hops: Vec::new(),
            venue_tag: "mock-fixed-rate".into(),
        })
    }

    fn submit(
        &self,
        route: &SwapRoute,
        _quoted_out: u64,
        _tx_bytes: &[u8],
        _signature: &[u8; 64],
    ) -> Result<(u64, String), SwapError> {
        let usdc = self.fill(route.dregg_in);
        Ok((usdc, format!("mock-swap:{}:{usdc}", route.dregg_in)))
    }
}

/// The POST seam for Jupiter's `/swap` endpoint (the GET seam is
/// [`HttpGet`](crate::pricing::HttpGet), reused). A production impl issues a POST with the
/// JSON `body` and returns the response body. Injected exactly like [`HttpGet`], so the
/// pure tx-build core carries no `reqwest`/`tokio` and is driven in tests.
pub trait HttpPost {
    /// POST `body` (a JSON string) to `url`, returning the response body as a string.
    fn post(&self, url: &str, body: &str) -> Result<String, SwapError>;
}

/// The REAL `$DREGG`→SOL→USDC venue over the public Jupiter v6 swap API. Quotes `/quote`
/// over an injected [`HttpGet`](crate::pricing::HttpGet) and builds the `/swap`
/// transaction over an injected [`HttpPost`]; both mints come from the [`SwapRoute`]
/// (i.e. from [`PayConfig`](crate::config::PayConfig)), never hardcoded.
pub struct JupiterVenue<G: HttpGet, P: HttpPost> {
    get: G,
    post: P,
    api_base: String,
    slippage_bps: u16,
}

impl<G: HttpGet, P: HttpPost> JupiterVenue<G, P> {
    /// The public Jupiter v6 swap API base. A public network constant, not a secret and
    /// not a mint.
    pub const DEFAULT_API_BASE: &'static str = "https://quote-api.jup.ag/v6";

    /// Build over the default public Jupiter v6 endpoint with a `slippage_bps` tolerance
    /// (the Jupiter-level slippage requested in the quote; the governance `min_out` is an
    /// independent hard floor enforced by [`JupiterSwap`]).
    pub fn new(get: G, post: P, slippage_bps: u16) -> Self {
        Self::with_api_base(get, post, slippage_bps, Self::DEFAULT_API_BASE.to_string())
    }

    /// Build with an explicit `api_base` (an operator override / a devnet proxy).
    pub fn with_api_base(get: G, post: P, slippage_bps: u16, api_base: String) -> Self {
        JupiterVenue {
            get,
            post,
            api_base,
            slippage_bps,
        }
    }

    /// The exact `/quote` URL this venue would GET for `route` (exposed so tests can
    /// assert it without a network call).
    pub fn quote_url(&self, route: &SwapRoute) -> String {
        format!(
            "{}/quote?inputMint={}&outputMint={}&amount={}&slippageBps={}&swapMode=ExactIn&onlyDirectRoutes=false",
            self.api_base,
            bs58::encode(route.dregg_mint).into_string(),
            bs58::encode(route.usdc_mint).into_string(),
            route.dregg_in,
            self.slippage_bps,
        )
    }

    /// The `/swap` URL this venue POSTs the build request to.
    pub fn swap_url(&self) -> String {
        format!("{}/swap", self.api_base)
    }

    /// GET + parse the Jupiter quote for `route`.
    fn fetch_quote(&self, route: &SwapRoute) -> Result<JupiterQuote, SwapError> {
        let body = self
            .get
            .get(&self.quote_url(route))
            .map_err(SwapError::from)?;
        parse_jupiter_quote(
            &body,
            &bs58::encode(route.dregg_mint).into_string(),
            &bs58::encode(route.usdc_mint).into_string(),
        )
    }

    /// The `/swap` request body binding the quote + the operator as owner/fee-payer.
    fn swap_body(quote: &JupiterQuote, operator_pubkey: &[u8; 32]) -> String {
        serde_json::json!({
            "quoteResponse": quote.raw,
            "userPublicKey": bs58::encode(operator_pubkey).into_string(),
            "wrapAndUnwrapSol": true,
            "dynamicComputeUnitLimit": true,
        })
        .to_string()
    }
}

impl<G: HttpGet, P: HttpPost> SwapVenue for JupiterVenue<G, P> {
    fn quote(&self, route: &SwapRoute) -> Result<u64, SwapError> {
        Ok(self.fetch_quote(route)?.out_amount)
    }

    fn build(&self, route: &SwapRoute, operator_pubkey: &[u8; 32]) -> Result<BuiltSwap, SwapError> {
        let quote = self.fetch_quote(route)?;
        let body = Self::swap_body(&quote, operator_pubkey);
        let resp = self.post.post(&self.swap_url(), &body)?;

        let value: serde_json::Value = serde_json::from_str(&resp)
            .map_err(|e| SwapError::Venue(format!("swap JSON parse: {e}")))?;
        let b64 = value
            .get("swapTransaction")
            .and_then(|v| v.as_str())
            .ok_or_else(|| SwapError::Venue("swap response missing swapTransaction".into()))?;
        let tx_bytes = BASE64
            .decode(b64)
            .map_err(|e| SwapError::Venue(format!("swapTransaction base64: {e}")))?;
        let sign_target = solana_sign_target(&tx_bytes)?;

        Ok(BuiltSwap {
            route: route.clone(),
            tx_bytes,
            sign_target,
            quoted_out: quote.out_amount,
            slippage_bps: quote.slippage_bps,
            hops: quote.hops,
            venue_tag: "jupiter-v6".into(),
        })
    }

    fn submit(
        &self,
        _route: &SwapRoute,
        quoted_out: u64,
        _tx_bytes: &[u8],
        signature: &[u8; 64],
    ) -> Result<(u64, String), SwapError> {
        // Broadcast is the live follow-up: a mainnet submit splices `signature` into
        // `tx_bytes`, `sendTransaction`s the serialized tx to the RPC, confirms it, and
        // reads the *realized* out-amount from the transaction meta. On the driven path we
        // report the quoted amount as realized and the operator signature (base58) as the
        // transaction reference — the on-chain form of a Solana tx signature.
        Ok((quoted_out, bs58::encode(signature).into_string()))
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// The swap executor
// ─────────────────────────────────────────────────────────────────────────────

/// Why a swap was refused.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum SwapError {
    /// The [`SwapAuthorization`] did not verify against the configured governance
    /// authority — a forged / wrong-authority / tampered authorization (the vote gate).
    Unauthorized,
    /// The authorization is for a different mint pair than this swap executor is
    /// configured for (a bound-authorization mismatch).
    MintMismatch,
    /// The pile cannot cover the authorized `amount` — fail closed (need vs have).
    PileShort {
        /// Atomic `$DREGG` the swap needs.
        needed: u64,
        /// Atomic `$DREGG` in the pile.
        available: u64,
    },
    /// The realized (or quoted) USDC was below the authorization's `min_out` — the
    /// slippage floor bit. Fail closed: no treasury move happens.
    SlippageExceeded {
        /// The realized/quoted atomic USDC.
        realized: u64,
        /// The authorized floor.
        min_out: u64,
    },
    /// The operator signer failed.
    Signer(SignerError),
    /// The venue (Jupiter quote/build transport, a parse, or the mock) failed.
    Venue(String),
}

impl std::fmt::Display for SwapError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            SwapError::Unauthorized => {
                write!(
                    f,
                    "swap refused: authorization did not verify (no passed vote)"
                )
            }
            SwapError::MintMismatch => {
                write!(
                    f,
                    "swap refused: authorization bound to a different mint pair"
                )
            }
            SwapError::PileShort { needed, available } => write!(
                f,
                "swap refused: pile short — need {needed} atomic $DREGG, have {available}"
            ),
            SwapError::SlippageExceeded { realized, min_out } => write!(
                f,
                "swap refused: realized {realized} atomic USDC below floor {min_out}"
            ),
            SwapError::Signer(e) => write!(f, "swap refused: {e}"),
            SwapError::Venue(e) => write!(f, "swap venue error: {e}"),
        }
    }
}

impl std::error::Error for SwapError {}

impl From<SignerError> for SwapError {
    fn from(e: SignerError) -> Self {
        SwapError::Signer(e)
    }
}

impl From<crate::pricing::PriceError> for SwapError {
    fn from(e: crate::pricing::PriceError) -> Self {
        // The Jupiter GET seam is the pricing crate's `HttpGet`, whose transport error is
        // `PriceError`; surface it as a venue transport failure.
        SwapError::Venue(e.to_string())
    }
}

/// The REALIZED slippage of a fill, in basis points, as a signed integer.
///
/// `(quoted − realized) · 10000 / quoted`: **positive** means the fill came in WORSE than
/// the quote (the ordinary meaning of slippage), **negative** means better. Computed in
/// `i128` and clamped into `i64`, so no input wraps; a `quoted` of `0` has no basis and
/// reads `0`.
///
/// This exists because a market-price swap ACCEPTS whatever slippage the venue gives — and
/// accepting it is not the same as not measuring it. Every [`SwapOutcome`] carries this
/// beside the realized amount so the receipt says what the acceptance cost.
pub fn realized_slippage_bps(quoted_out: u64, realized_out: u64) -> i64 {
    if quoted_out == 0 {
        return 0;
    }
    let drop = quoted_out as i128 - realized_out as i128;
    let bps = drop * 10_000 / quoted_out as i128;
    bps.clamp(i64::MIN as i128, i64::MAX as i128) as i64
}

/// The result of an executed swap.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SwapOutcome {
    /// Atomic `$DREGG` sold out of the pile.
    pub dregg_in: u64,
    /// Atomic USDC realized into the fuel tank.
    pub usdc_out: u64,
    /// The atomic USDC the venue QUOTED before the fill — the baseline the realized
    /// amount is measured against.
    pub quoted_out: u64,
    /// The REALIZED slippage in basis points ([`realized_slippage_bps`]): positive =
    /// filled worse than quoted, negative = better. A market-price swap accepts whatever
    /// this reads; the receipt records it regardless.
    pub slippage_bps: i64,
    /// The new pile balance (atomic `$DREGG`) after the swap.
    pub pile_after: u64,
    /// The new fuel balance (atomic USDC) after the swap.
    pub fuel_after: u64,
    /// The venue transaction reference (a Jupiter tx signature on the real path; a
    /// synthetic id on the mock path).
    pub tx_reference: String,
}

/// An unsigned swap transaction: the exact bytes the operator signs, the full transaction
/// to splice the signature into, and the realized route. A real deployment hands this to
/// the operator's secured signer and passes the returned signature to
/// [`JupiterSwap::submit_signed`] — `dregg-pay` never holds the key.
#[derive(Clone, Debug)]
pub struct UnsignedSwapTx {
    /// The route the signed transaction realizes.
    pub route: SwapRoute,
    /// The operator public key the transaction was built around (fee-payer/owner). The
    /// signature is verified against this at submit.
    pub operator_pubkey: [u8; 32],
    /// The exact bytes the operator signs (the Solana message on the Jupiter path).
    pub message: Vec<u8>,
    /// The full unsigned serialized transaction (the operator splices its signature in to
    /// broadcast). On the fixed-rate mock this equals `message`.
    pub tx_bytes: Vec<u8>,
    /// The atomic USDC the quote promised (already checked to clear the floor).
    pub quoted_out: u64,
    /// The Jupiter-level slippage (bps) the transaction was built at.
    pub slippage_bps: u16,
    /// The `$DREGG`→SOL→USDC hops (empty on the fixed-rate mock).
    pub hops: Vec<RouteHop>,
}

/// The pile→fuel swap executor over an injected [`SwapVenue`]. Configured with the mint
/// pair (so it can reject a mis-bound authorization) and the governance authority public
/// key (so it can verify the vote gate). Holds NO key.
pub struct JupiterSwap<V: SwapVenue> {
    venue: V,
    dregg_mint: [u8; 32],
    usdc_mint: [u8; 32],
    authority_pk: [u8; 32],
}

impl<V: SwapVenue> JupiterSwap<V> {
    /// Build a swap executor: the venue seam, the mint pair from
    /// [`PayConfig`](crate::config::PayConfig), and the governance authority public key a
    /// [`SwapAuthorization`] must verify against.
    pub fn new(
        venue: V,
        dregg_mint: [u8; 32],
        usdc_mint: [u8; 32],
        authority_pk: [u8; 32],
    ) -> Self {
        JupiterSwap {
            venue,
            dregg_mint,
            usdc_mint,
            authority_pk,
        }
    }

    /// Verify an authorization (the vote gate) and build the UNSIGNED swap transaction —
    /// the exact bytes the operator signs. On the real [`JupiterVenue`] this quotes the
    /// `$DREGG`→SOL→USDC route and constructs the actual Jupiter v6 transaction; a real
    /// deployment hands [`UnsignedSwapTx::message`] to the operator's secured signer and
    /// passes the returned signature to [`JupiterSwap::submit_signed`]. `dregg-pay` never
    /// holds the key.
    ///
    /// Refuses ([`SwapError::Unauthorized`] / [`SwapError::MintMismatch`]) before building
    /// anything if the authorization does not verify — the vote gate comes first — and
    /// refuses ([`SwapError::SlippageExceeded`]) if the quoted out cannot clear the
    /// authorized `min_out`, so the operator is never handed a tx that would blow the floor.
    pub fn build_unsigned(
        &self,
        auth: &SwapAuthorization,
        operator_pubkey: [u8; 32],
    ) -> Result<UnsignedSwapTx, SwapError> {
        self.check_auth(auth)?;
        let route = self.route_for(auth);
        let built = self.venue.build(&route, &operator_pubkey)?;
        if built.quoted_out < auth.min_out {
            return Err(SwapError::SlippageExceeded {
                realized: built.quoted_out,
                min_out: auth.min_out,
            });
        }
        Ok(UnsignedSwapTx {
            route,
            operator_pubkey,
            message: built.sign_target,
            tx_bytes: built.tx_bytes,
            quoted_out: built.quoted_out,
            slippage_bps: built.slippage_bps,
            hops: built.hops,
        })
    }

    /// Submit an operator-signed [`UnsignedSwapTx`] (the external, key-stays-with-operator
    /// flow): re-verify the authorization, verify the operator signature over the exact
    /// bytes handed out, check the pile covers it, submit through the venue, enforce the
    /// slippage floor, and — on success — move the treasury (pile DOWN by `amount`, fuel
    /// UP by the realized USDC). Fails closed with NO treasury move on any refusal.
    pub fn submit_signed<S: TreasuryStore>(
        &self,
        auth: &SwapAuthorization,
        unsigned: &UnsignedSwapTx,
        signature: &[u8; 64],
        treasury: &Treasury<S>,
    ) -> Result<SwapOutcome, SwapError> {
        // Gate 1 (again) — the authorization must still verify.
        self.check_auth(auth)?;

        // Gate 2 — the operator signature must verify over the exact bytes we handed out.
        // This is real ed25519 (the same check the chain performs); a stub/tampered
        // signature is refused before anything moves.
        verify_operator_signature(&unsigned.operator_pubkey, &unsigned.message, signature)?;

        // Fail closed if the pile cannot cover the authorized amount.
        let pile = treasury.dregg_balance();
        if auth.amount > pile {
            return Err(SwapError::PileShort {
                needed: auth.amount,
                available: pile,
            });
        }

        let (usdc_out, tx_reference) = self.venue.submit(
            &unsigned.route,
            unsigned.quoted_out,
            &unsigned.tx_bytes,
            signature,
        )?;

        // The slippage floor bites: a fill below the authorized `min_out` fails closed.
        if usdc_out < auth.min_out {
            return Err(SwapError::SlippageExceeded {
                realized: usdc_out,
                min_out: auth.min_out,
            });
        }

        // On success, realize the swap in the treasury: pile DOWN, fuel UP.
        let pile_after =
            treasury
                .withdraw_dregg(auth.amount)
                .map_err(|_| SwapError::PileShort {
                    needed: auth.amount,
                    available: treasury.dregg_balance(),
                })?;
        let fuel_after = treasury.deposit_usdc(usdc_out);

        Ok(SwapOutcome {
            dregg_in: auth.amount,
            usdc_out,
            quoted_out: unsigned.quoted_out,
            slippage_bps: realized_slippage_bps(unsigned.quoted_out, usdc_out),
            pile_after,
            fuel_after,
            tx_reference,
        })
    }

    /// Execute the authorized swap in-process with an operator [`Signer`] — the
    /// convenience over [`build_unsigned`](JupiterSwap::build_unsigned) +
    /// [`submit_signed`](JupiterSwap::submit_signed): verify the authorization (the vote
    /// gate), check the pile, build the real Jupiter transaction, have the operator sign
    /// it, submit it, enforce the floor, and move the treasury.
    ///
    /// REFUSES without a valid authorization ([`SwapError::Unauthorized`]) — there is no
    /// unauthorized path — and fails closed on a short pile, a blown slippage floor, or a
    /// signer/venue error, with NO treasury move on any refusal.
    pub fn execute<S: TreasuryStore>(
        &self,
        auth: &SwapAuthorization,
        signer: &dyn Signer,
        treasury: &Treasury<S>,
    ) -> Result<SwapOutcome, SwapError> {
        // Gate 1 — THE VOTE.
        self.check_auth(auth)?;

        // Fail closed on a short pile BEFORE any network/build work.
        let pile = treasury.dregg_balance();
        if auth.amount > pile {
            return Err(SwapError::PileShort {
                needed: auth.amount,
                available: pile,
            });
        }

        // Build the real unsigned tx (quote + /swap), refusing if the quote can't clear
        // the floor. Then Gate 2 — the operator signs the exact bytes — and submit.
        let unsigned = self.build_unsigned(auth, signer.public_key())?;
        let signature = signer.sign(&unsigned.message)?;
        self.submit_signed(auth, &unsigned, &signature, treasury)
    }

    /// A best-effort USDC quote for an authorization's amount (does not move funds).
    pub fn quote(&self, auth: &SwapAuthorization) -> Result<u64, SwapError> {
        self.check_auth(auth)?;
        self.venue.quote(&self.route_for(auth))
    }

    fn check_auth(&self, auth: &SwapAuthorization) -> Result<(), SwapError> {
        if !auth.verify(&self.authority_pk) {
            return Err(SwapError::Unauthorized);
        }
        if auth.dregg_mint != self.dregg_mint || auth.usdc_mint != self.usdc_mint {
            return Err(SwapError::MintMismatch);
        }
        Ok(())
    }

    fn route_for(&self, auth: &SwapAuthorization) -> SwapRoute {
        SwapRoute {
            dregg_in: auth.amount,
            min_usdc_out: auth.min_out,
            dregg_mint: self.dregg_mint,
            usdc_mint: self.usdc_mint,
        }
    }
}

/// Verify the operator signature over `message` against `operator_pubkey` — real ed25519,
/// the same check the chain performs. A bad key/signature is a [`SwapError::Signer`].
fn verify_operator_signature(
    operator_pubkey: &[u8; 32],
    message: &[u8],
    signature: &[u8; 64],
) -> Result<(), SwapError> {
    let vk = VerifyingKey::from_bytes(operator_pubkey).map_err(|_| {
        SwapError::Signer(SignerError::Backend("operator public key invalid".into()))
    })?;
    let sig = Signature::from_slice(signature).map_err(|_| {
        SwapError::Signer(SignerError::Backend("operator signature malformed".into()))
    })?;
    vk.verify(message, &sig).map_err(|_| {
        SwapError::Signer(SignerError::Backend(
            "operator signature failed to verify".into(),
        ))
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::pricing::PriceError;
    use crate::treasury::InMemoryTreasuryStore;
    use std::sync::Mutex;

    const DREGG_MINT: [u8; 32] = [0x11u8; 32];
    const USDC_MINT: [u8; 32] = [0x22u8; 32];
    // A recognizable "SOL" mint for the mock route's middle leg (not the real WSOL mint).
    const SOL_MINT: [u8; 32] = [0x33u8; 32];

    fn treasury(pile: u64, fuel: u64) -> Treasury<InMemoryTreasuryStore> {
        let t = Treasury::new(InMemoryTreasuryStore::new(), 6);
        t.deposit_dregg(pile);
        t.deposit_usdc(fuel);
        t
    }

    fn b58(x: [u8; 32]) -> String {
        bs58::encode(x).into_string()
    }

    // ── A MockJupiter: implements the GET (/quote) + POST (/swap) seams with a canned
    //    $DREGG→SOL→USDC route, records what it was called with, and base64-encodes a
    //    canned unsigned transaction so the venue decodes REAL bytes back out. No network.
    struct MockJupiter {
        quote_json: String,
        // The canned unsigned transaction the mock's /swap returns (before base64).
        canned_tx: Vec<u8>,
        last_get_url: Mutex<Option<String>>,
        last_post: Mutex<Option<(String, String)>>,
    }

    impl MockJupiter {
        /// A canned quote: `out_amount` USDC out at `slippage_bps`, split over the two
        /// hops $DREGG→SOL and SOL→USDC. The `mid` amount is the SOL-leg output.
        fn new(out_amount: u64, slippage_bps: u16, dregg_in: u64, mid: u64) -> Self {
            let quote_json = serde_json::json!({
                "inputMint": b58(DREGG_MINT),
                "inAmount": dregg_in.to_string(),
                "outputMint": b58(USDC_MINT),
                "outAmount": out_amount.to_string(),
                "otherAmountThreshold": out_amount.to_string(),
                "swapMode": "ExactIn",
                "slippageBps": slippage_bps,
                "routePlan": [
                    {
                        "swapInfo": {
                            "ammKey": "Amm1111111111111111111111111111111111111111",
                            "label": "Orca",
                            "inputMint": b58(DREGG_MINT),
                            "outputMint": b58(SOL_MINT),
                            "inAmount": dregg_in.to_string(),
                            "outAmount": mid.to_string(),
                            "feeAmount": "0",
                            "feeMint": b58(SOL_MINT),
                        },
                        "percent": 100
                    },
                    {
                        "swapInfo": {
                            "ammKey": "Amm2222222222222222222222222222222222222222",
                            "label": "Raydium",
                            "inputMint": b58(SOL_MINT),
                            "outputMint": b58(USDC_MINT),
                            "inAmount": mid.to_string(),
                            "outAmount": out_amount.to_string(),
                            "feeAmount": "0",
                            "feeMint": b58(USDC_MINT),
                        },
                        "percent": 100
                    }
                ]
            })
            .to_string();

            // A canned unsigned versioned transaction: 1 signature slot (shortvec 0x01 +
            // 64 zero bytes) followed by a recognizable "message" body.
            let mut canned_tx = Vec::new();
            canned_tx.push(0x01u8); // shortvec: one required signature
            canned_tx.extend_from_slice(&[0u8; 64]); // the empty signature slot
            canned_tx.extend_from_slice(b"jupiter-v6-mock-message:DREGG->SOL->USDC");

            MockJupiter {
                quote_json,
                canned_tx,
                last_get_url: Mutex::new(None),
                last_post: Mutex::new(None),
            }
        }

        fn message_body(&self) -> Vec<u8> {
            solana_sign_target(&self.canned_tx).unwrap()
        }
    }

    impl HttpGet for MockJupiter {
        fn get(&self, url: &str) -> Result<String, PriceError> {
            *self.last_get_url.lock().unwrap() = Some(url.to_string());
            Ok(self.quote_json.clone())
        }
    }

    impl HttpPost for MockJupiter {
        fn post(&self, url: &str, body: &str) -> Result<String, SwapError> {
            *self.last_post.lock().unwrap() = Some((url.to_string(), body.to_string()));
            let b64 = BASE64.encode(&self.canned_tx);
            Ok(serde_json::json!({
                "swapTransaction": b64,
                "lastValidBlockHeight": 1234567u64,
            })
            .to_string())
        }
    }

    // ── The fixed-rate MockSwapVenue gate tests (refusals + the mock-signed happy path) ──

    #[test]
    fn authorized_swap_moves_pile_to_fuel_mock_signed() {
        let authority = GovernanceAuthority::from_seed([7u8; 32]);
        let signer = MockSigner::from_seed([8u8; 32]);
        // $0.005/$DREGG at (6,6) decimals: 100_000_000 atomic $DREGG → 500_000 atomic USDC.
        let venue = MockSwapVenue::new(5, 1000);
        let swap = JupiterSwap::new(venue, DREGG_MINT, USDC_MINT, authority.public_key());

        let t = treasury(100_000_000, 0);
        let auth = authority.authorize(100_000_000, 400_000, DREGG_MINT, USDC_MINT, [1u8; 32]);
        let out = swap.execute(&auth, &signer, &t).unwrap();
        assert_eq!(out.dregg_in, 100_000_000);
        assert_eq!(out.usdc_out, 500_000);
        assert_eq!(out.pile_after, 0, "pile drained by the swap");
        assert_eq!(out.fuel_after, 500_000, "fuel filled by the swap");
        assert_eq!(t.dregg_balance(), 0);
        assert_eq!(t.usdc_balance(), 500_000);
    }

    #[test]
    fn realized_slippage_is_measured_in_both_directions() {
        // The pure measurement (positive = filled WORSE than quoted).
        assert_eq!(realized_slippage_bps(1_000_000, 1_000_000), 0, "exact fill");
        assert_eq!(realized_slippage_bps(1_000_000, 990_000), 100, "1% worse");
        assert_eq!(
            realized_slippage_bps(1_000_000, 500_000),
            5_000,
            "50% worse"
        );
        assert_eq!(realized_slippage_bps(1_000_000, 0), 10_000, "total loss");
        assert_eq!(
            realized_slippage_bps(1_000_000, 1_010_000),
            -100,
            "a BETTER fill reads negative, never a silent zero"
        );
        // No basis to measure against, and no panic/wrap at the extremes.
        assert_eq!(realized_slippage_bps(0, 5), 0);
        assert_eq!(realized_slippage_bps(1, u64::MAX), i64::MIN);
        assert_eq!(realized_slippage_bps(u64::MAX, 0), 10_000);
    }

    #[test]
    fn a_market_price_swap_accepts_slippage_and_records_it() {
        // A market-price authorization carries min_out = 0, so the SlippageExceeded
        // branch cannot fire and the swap fills at whatever the venue gives — but the
        // receipt still says exactly what that cost.
        let authority = GovernanceAuthority::from_seed([7u8; 32]);
        let signer = MockSigner::from_seed([8u8; 32]);
        // The venue fills at a tenth of the $0.005 reference rate — a catastrophic 90%
        // haircut a floored authorization would have refused outright.
        let swap = JupiterSwap::new(
            MockSwapVenue::new(5, 10_000),
            DREGG_MINT,
            USDC_MINT,
            authority.public_key(),
        );
        let t = treasury(100_000_000, 0);
        let market = authority.authorize(100_000_000, 0, DREGG_MINT, USDC_MINT, [1u8; 32]);
        let out = swap.execute(&market, &signer, &t).unwrap();
        assert_eq!(out.usdc_out, 50_000, "filled at the terrible market price");
        assert_eq!(out.quoted_out, 50_000, "the quote is on the receipt");
        assert_eq!(out.slippage_bps, 0, "realized == quoted on the mock venue");
        assert_eq!(t.dregg_balance(), 0, "the whole pile went");
        assert_eq!(t.usdc_balance(), 50_000);

        // THE CONTRAST that makes min_out = 0 load-bearing: the SAME venue and amount
        // under a floored authorization is refused and moves nothing.
        let t2 = treasury(100_000_000, 0);
        let floored = authority.authorize(100_000_000, 400_000, DREGG_MINT, USDC_MINT, [2u8; 32]);
        assert_eq!(
            swap.execute(&floored, &signer, &t2),
            Err(SwapError::SlippageExceeded {
                realized: 50_000,
                min_out: 400_000
            }),
        );
        assert_eq!(
            t2.dregg_balance(),
            100_000_000,
            "the floored path moved none"
        );
    }

    #[test]
    fn swap_without_valid_authorization_is_refused() {
        let real = GovernanceAuthority::from_seed([7u8; 32]);
        let attacker = GovernanceAuthority::from_seed([0x99u8; 32]);
        let signer = MockSigner::from_seed([8u8; 32]);
        let swap = JupiterSwap::new(
            MockSwapVenue::new(5, 1000),
            DREGG_MINT,
            USDC_MINT,
            real.public_key(),
        );
        let t = treasury(100_000_000, 0);
        let forged = attacker.authorize(100_000_000, 400_000, DREGG_MINT, USDC_MINT, [1u8; 32]);
        assert_eq!(
            swap.execute(&forged, &signer, &t),
            Err(SwapError::Unauthorized)
        );
        assert_eq!(t.dregg_balance(), 100_000_000);
        assert_eq!(t.usdc_balance(), 0);
    }

    #[test]
    fn tampered_authorization_is_refused() {
        let authority = GovernanceAuthority::from_seed([7u8; 32]);
        let signer = MockSigner::from_seed([8u8; 32]);
        let swap = JupiterSwap::new(
            MockSwapVenue::new(5, 1000),
            DREGG_MINT,
            USDC_MINT,
            authority.public_key(),
        );
        let t = treasury(100_000_000, 0);
        let mut auth = authority.authorize(1_000_000, 4_000, DREGG_MINT, USDC_MINT, [1u8; 32]);
        auth.amount = 100_000_000; // tamper after signing
        assert_eq!(
            swap.execute(&auth, &signer, &t),
            Err(SwapError::Unauthorized)
        );
        assert_eq!(t.dregg_balance(), 100_000_000);
    }

    #[test]
    fn swap_fails_closed_when_pile_short() {
        let authority = GovernanceAuthority::from_seed([7u8; 32]);
        let signer = MockSigner::from_seed([8u8; 32]);
        let swap = JupiterSwap::new(
            MockSwapVenue::new(5, 1000),
            DREGG_MINT,
            USDC_MINT,
            authority.public_key(),
        );
        let t = treasury(10, 0);
        let auth = authority.authorize(100_000_000, 1, DREGG_MINT, USDC_MINT, [1u8; 32]);
        assert_eq!(
            swap.execute(&auth, &signer, &t),
            Err(SwapError::PileShort {
                needed: 100_000_000,
                available: 10
            })
        );
        assert_eq!(t.dregg_balance(), 10, "short pile untouched");
    }

    #[test]
    fn slippage_floor_fails_closed_with_no_move() {
        let authority = GovernanceAuthority::from_seed([7u8; 32]);
        let signer = MockSigner::from_seed([8u8; 32]);
        // Venue realizes only 500_000 but the floor is 600_000 → refused.
        let swap = JupiterSwap::new(
            MockSwapVenue::new(5, 1000),
            DREGG_MINT,
            USDC_MINT,
            authority.public_key(),
        );
        let t = treasury(100_000_000, 0);
        let auth = authority.authorize(100_000_000, 600_000, DREGG_MINT, USDC_MINT, [1u8; 32]);
        assert_eq!(
            swap.execute(&auth, &signer, &t),
            Err(SwapError::SlippageExceeded {
                realized: 500_000,
                min_out: 600_000
            })
        );
        assert_eq!(
            t.dregg_balance(),
            100_000_000,
            "no move on slippage refusal"
        );
        assert_eq!(t.usdc_balance(), 0);
    }

    #[test]
    fn mint_mismatch_is_refused() {
        let authority = GovernanceAuthority::from_seed([7u8; 32]);
        let signer = MockSigner::from_seed([8u8; 32]);
        let swap = JupiterSwap::new(
            MockSwapVenue::new(5, 1000),
            DREGG_MINT,
            USDC_MINT,
            authority.public_key(),
        );
        let t = treasury(100_000_000, 0);
        let auth = authority.authorize(1, 1, [0xAB; 32], USDC_MINT, [1u8; 32]);
        assert_eq!(
            swap.execute(&auth, &signer, &t),
            Err(SwapError::MintMismatch)
        );
    }

    // ── base64 / shortvec / quote-parse units ──

    #[test]
    fn base64_roundtrips_the_transaction_bytes() {
        let bytes = b"jupiter-v6-mock-message:DREGG->SOL->USDC\x00\x01\x02\xff";
        let encoded = BASE64.encode(bytes);
        assert_eq!(BASE64.decode(&encoded).unwrap(), bytes);
    }

    #[test]
    fn solana_sign_target_skips_the_signature_slots() {
        // 2 signature slots then a message.
        let mut tx = vec![0x02u8];
        tx.extend_from_slice(&[0u8; 128]);
        tx.extend_from_slice(b"the-message");
        assert_eq!(solana_sign_target(&tx).unwrap(), b"the-message");
        // A tx shorter than its declared signatures is refused.
        let bad = vec![0x05u8, 0, 0];
        assert!(matches!(solana_sign_target(&bad), Err(SwapError::Venue(_))));
    }

    #[test]
    fn parse_jupiter_quote_rejects_a_mint_mismatched_quote() {
        let mj = MockJupiter::new(500_000, 50, 100_000_000, 123_456);
        // Parsing against the WRONG expected output mint is refused (fail closed).
        let wrong = b58([0xCD; 32]);
        assert!(matches!(
            parse_jupiter_quote(&mj.quote_json, &b58(DREGG_MINT), &wrong),
            Err(SwapError::Venue(_))
        ));
        // The right pair parses, exposing the two-hop $DREGG→SOL→USDC route.
        let q = parse_jupiter_quote(&mj.quote_json, &b58(DREGG_MINT), &b58(USDC_MINT)).unwrap();
        assert_eq!(q.out_amount, 500_000);
        assert_eq!(q.slippage_bps, 50);
        assert_eq!(q.hops.len(), 2);
        assert_eq!(q.hops[0].input_mint, b58(DREGG_MINT));
        assert_eq!(
            q.hops[0].output_mint,
            b58(SOL_MINT),
            "first leg goes to SOL"
        );
        assert_eq!(
            q.hops[1].input_mint,
            b58(SOL_MINT),
            "second leg is from SOL"
        );
        assert_eq!(q.hops[1].output_mint, b58(USDC_MINT));
    }

    // ── The REAL Jupiter build path, driven over MockJupiter ──

    #[test]
    fn jupiter_build_unsigned_constructs_the_real_swap_tx() {
        let authority = GovernanceAuthority::from_seed([7u8; 32]);
        let signer = MockSigner::from_seed([8u8; 32]);
        let mj = MockJupiter::new(500_000, 50, 100_000_000, 123_456);
        let expected_message = mj.message_body();
        let venue = JupiterVenue::new(mj, MockJupiter::new(500_000, 50, 100_000_000, 123_456), 50);
        // NOTE: `venue` owns the GET-mock; the POST-mock is a second identical instance.
        let swap = JupiterSwap::new(venue, DREGG_MINT, USDC_MINT, authority.public_key());

        let auth = authority.authorize(100_000_000, 400_000, DREGG_MINT, USDC_MINT, [1u8; 32]);
        let unsigned = swap.build_unsigned(&auth, signer.public_key()).unwrap();

        // The route + quoted amounts + slippage came from the Jupiter quote.
        assert_eq!(unsigned.route.dregg_in, 100_000_000);
        assert_eq!(unsigned.route.min_usdc_out, 400_000);
        assert_eq!(unsigned.quoted_out, 500_000);
        assert_eq!(unsigned.slippage_bps, 50);
        // The two-hop route goes $DREGG → SOL → USDC.
        assert_eq!(unsigned.hops.len(), 2);
        assert_eq!(unsigned.hops[0].output_mint, b58(SOL_MINT));
        assert_eq!(unsigned.hops[1].input_mint, b58(SOL_MINT));
        // The signed message is the REAL Solana message decoded from the Jupiter tx.
        assert_eq!(unsigned.message, expected_message);
        assert!(
            unsigned.tx_bytes.len() > unsigned.message.len(),
            "tx_bytes carries the signature slots the message excludes"
        );
        // The operator can produce a real ed25519 signature over it.
        let sig = signer.sign(&unsigned.message).unwrap();
        assert!(verify_operator_signature(&signer.public_key(), &unsigned.message, &sig).is_ok());
    }

    #[test]
    fn jupiter_quote_url_and_swap_body_carry_the_route_and_operator() {
        let signer = MockSigner::from_seed([8u8; 32]);
        let route = SwapRoute {
            dregg_in: 100_000_000,
            min_usdc_out: 400_000,
            dregg_mint: DREGG_MINT,
            usdc_mint: USDC_MINT,
        };
        let venue = JupiterVenue::new(
            MockJupiter::new(500_000, 50, 100_000_000, 123_456),
            MockJupiter::new(500_000, 50, 100_000_000, 123_456),
            50,
        );
        // The quote URL binds the exact mint pair, amount, and slippage.
        let url = venue.quote_url(&route);
        assert!(url.contains(&format!("inputMint={}", b58(DREGG_MINT))));
        assert!(url.contains(&format!("outputMint={}", b58(USDC_MINT))));
        assert!(url.contains("amount=100000000"));
        assert!(url.contains("slippageBps=50"));
        assert!(url.contains("swapMode=ExactIn"));

        // Building POSTs a /swap body carrying the operator pubkey + the quoteResponse.
        let built = venue.build(&route, &signer.public_key()).unwrap();
        assert_eq!(built.quoted_out, 500_000);
        assert_eq!(built.venue_tag, "jupiter-v6");
        let (post_url, body) = venue.post.last_post.lock().unwrap().clone().unwrap();
        assert_eq!(post_url, venue.swap_url());
        assert!(body.contains(&bs58::encode(signer.public_key()).into_string()));
        assert!(body.contains("quoteResponse"));
        assert!(body.contains("userPublicKey"));
        // The GET recorded the quote URL too.
        assert_eq!(venue.get.last_get_url.lock().unwrap().clone().unwrap(), url);
    }

    #[test]
    fn jupiter_authorized_swap_signs_the_real_tx_and_moves_treasury() {
        let authority = GovernanceAuthority::from_seed([7u8; 32]);
        let signer = MockSigner::from_seed([8u8; 32]);
        let venue = JupiterVenue::new(
            MockJupiter::new(500_000, 50, 100_000_000, 123_456),
            MockJupiter::new(500_000, 50, 100_000_000, 123_456),
            50,
        );
        let swap = JupiterSwap::new(venue, DREGG_MINT, USDC_MINT, authority.public_key());

        let t = treasury(100_000_000, 0);
        let auth = authority.authorize(100_000_000, 400_000, DREGG_MINT, USDC_MINT, [1u8; 32]);
        let out = swap.execute(&auth, &signer, &t).unwrap();

        // Moved by the QUOTED amount, floored by min_out.
        assert_eq!(out.dregg_in, 100_000_000);
        assert_eq!(out.usdc_out, 500_000);
        assert_eq!(out.pile_after, 0, "pile drained");
        assert_eq!(out.fuel_after, 500_000, "fuel filled by the quoted USDC");
        assert_eq!(t.dregg_balance(), 0);
        assert_eq!(t.usdc_balance(), 500_000);
        // The tx reference is the base58 operator signature (the Solana tx-signature form).
        assert!(!out.tx_reference.is_empty());
    }

    #[test]
    fn jupiter_unauthorized_swap_never_builds_or_signs() {
        // A wrong-authority authorization is refused BEFORE any quote/build/sign.
        let real = GovernanceAuthority::from_seed([7u8; 32]);
        let attacker = GovernanceAuthority::from_seed([0x99u8; 32]);
        let signer = MockSigner::from_seed([8u8; 32]);
        let venue = JupiterVenue::new(
            MockJupiter::new(500_000, 50, 100_000_000, 123_456),
            MockJupiter::new(500_000, 50, 100_000_000, 123_456),
            50,
        );
        let swap = JupiterSwap::new(venue, DREGG_MINT, USDC_MINT, real.public_key());
        let t = treasury(100_000_000, 0);
        let forged = attacker.authorize(100_000_000, 400_000, DREGG_MINT, USDC_MINT, [1u8; 32]);

        // Neither build_unsigned nor execute touches the venue.
        assert_eq!(
            swap.build_unsigned(&forged, signer.public_key())
                .unwrap_err(),
            SwapError::Unauthorized
        );
        assert_eq!(
            swap.execute(&forged, &signer, &t),
            Err(SwapError::Unauthorized)
        );
        assert!(
            swap.venue.get.last_get_url.lock().unwrap().is_none(),
            "the quote endpoint was never hit for an unauthorized swap"
        );
        assert_eq!(t.dregg_balance(), 100_000_000, "nothing moved");
    }

    #[test]
    fn jupiter_slippage_below_floor_refused_before_signing() {
        // The quote returns only 300_000 but the authorized floor is 400_000 → refused at
        // build time, before the operator ever signs; nothing moves.
        let authority = GovernanceAuthority::from_seed([7u8; 32]);
        let signer = MockSigner::from_seed([8u8; 32]);
        let venue = JupiterVenue::new(
            MockJupiter::new(300_000, 50, 100_000_000, 90_000),
            MockJupiter::new(300_000, 50, 100_000_000, 90_000),
            50,
        );
        let swap = JupiterSwap::new(venue, DREGG_MINT, USDC_MINT, authority.public_key());
        let t = treasury(100_000_000, 0);
        let auth = authority.authorize(100_000_000, 400_000, DREGG_MINT, USDC_MINT, [1u8; 32]);

        assert_eq!(
            swap.build_unsigned(&auth, signer.public_key()).unwrap_err(),
            SwapError::SlippageExceeded {
                realized: 300_000,
                min_out: 400_000
            }
        );
        assert_eq!(
            swap.execute(&auth, &signer, &t),
            Err(SwapError::SlippageExceeded {
                realized: 300_000,
                min_out: 400_000
            })
        );
        assert_eq!(t.dregg_balance(), 100_000_000, "no move");
        assert_eq!(t.usdc_balance(), 0);
    }

    #[test]
    fn build_unsigned_binds_the_route_for_the_operator_mock_venue() {
        // The fixed-rate mock venue's build_unsigned still binds the route via swap_message.
        let authority = GovernanceAuthority::from_seed([7u8; 32]);
        let signer = MockSigner::from_seed([8u8; 32]);
        let swap = JupiterSwap::new(
            MockSwapVenue::new(5, 1000),
            DREGG_MINT,
            USDC_MINT,
            authority.public_key(),
        );
        let auth = authority.authorize(100_000_000, 400_000, DREGG_MINT, USDC_MINT, [1u8; 32]);
        let unsigned = swap.build_unsigned(&auth, signer.public_key()).unwrap();
        assert_eq!(unsigned.route.dregg_in, 100_000_000);
        assert_eq!(unsigned.route.min_usdc_out, 400_000);
        assert_eq!(unsigned.message, swap_message(&unsigned.route));
        assert_eq!(unsigned.operator_pubkey, signer.public_key());
    }
}
