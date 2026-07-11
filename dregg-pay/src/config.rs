//! [`PayConfig`] and the shared value types — everything the operator configures,
//! nothing hardcoded.
//!
//! **Safety law.** The mainnet `$DREGG` mint and the treasury address are OPERATOR
//! CONFIG ([`PayConfig::mint`] / [`PayConfig::treasury`]), supplied from the
//! environment in production and from a throwaway test fixture in tests. They are
//! never baked into committed source. [`PayConfig::network`] defaults to
//! [`Network::Devnet`]; flipping to [`Network::Mainnet`] is a deliberate operator
//! action.

use zeroize::Zeroizing;

/// A user of the payment system — the discord user id (a snowflake string) or any
/// stable per-user identifier. The same `UserId` always derives the same deposit
/// address (that determinism is what makes attribution automatic).
#[derive(Clone, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct UserId(pub String);

impl UserId {
    /// Borrow the id as bytes (the input to the HD derivation index).
    pub fn as_bytes(&self) -> &[u8] {
        self.0.as_bytes()
    }
}

impl<S: Into<String>> From<S> for UserId {
    fn from(s: S) -> Self {
        UserId(s.into())
    }
}

impl std::fmt::Display for UserId {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(&self.0)
    }
}

/// A Solana address — a 32-byte ed25519 public key. A [`DepositAddress`] is the
/// public key of a per-user HD-derived keypair; funds sent to it are attributable
/// to exactly one user because the derivation is deterministic and injective by
/// index.
#[derive(Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct DepositAddress(pub [u8; 32]);

impl DepositAddress {
    /// The raw 32-byte pubkey.
    pub fn to_bytes(&self) -> [u8; 32] {
        self.0
    }

    /// The base58 encoding (the canonical on-chain / wallet representation).
    pub fn to_base58(&self) -> String {
        bs58::encode(self.0).into_string()
    }

    /// Parse a base58 Solana address into 32 raw bytes.
    pub fn from_base58(s: &str) -> Result<Self, ConfigError> {
        Ok(DepositAddress(parse_pubkey_base58(s)?))
    }
}

impl std::fmt::Display for DepositAddress {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(&self.to_base58())
    }
}

impl std::fmt::Debug for DepositAddress {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "DepositAddress({})", self.to_base58())
    }
}

/// Which Solana cluster the real watcher/sweeper talk to. Defaults to
/// [`Network::Devnet`]; [`Network::Mainnet`] is an explicit operator flip and the
/// only value that touches real funds.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Network {
    /// Solana devnet — throwaway tokens, safe to drive.
    Devnet,
    /// Solana mainnet-beta — real funds. Operator flip only.
    Mainnet,
}

impl Network {
    /// `true` only for [`Network::Mainnet`] — the guard the operator checks before
    /// allowing a real-funds sweep.
    pub fn is_mainnet(&self) -> bool {
        matches!(self, Network::Mainnet)
    }
}

/// The HD seed — secret custody material. Held in a [`Zeroizing`] buffer so it is
/// wiped from memory on drop. In tests this is a throwaway constant; in production
/// it is loaded from the operator's secret store (env / KMS / HSM). This seed is
/// the custody point of the whole "B" model — whoever holds it can sweep every
/// deposit address.
#[derive(Clone)]
pub struct Seed(Zeroizing<Vec<u8>>);

impl Seed {
    /// Wrap raw seed bytes (BIP-39 512-bit seed, or any high-entropy secret ≥ 16
    /// bytes). SLIP-0010 imposes no fixed length; 32–64 bytes is typical.
    pub fn new(bytes: impl Into<Vec<u8>>) -> Self {
        Seed(Zeroizing::new(bytes.into()))
    }

    /// Borrow the raw seed bytes (only the HD derivation calls this).
    pub fn as_bytes(&self) -> &[u8] {
        &self.0
    }
}

impl std::fmt::Debug for Seed {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        // Never print the seed.
        write!(f, "Seed(<{} bytes redacted>)", self.0.len())
    }
}

/// The canonical SPL Token program id (`TokenkegQfeZyiNwAJbNbGKPFXCWuBvf9Ss623VQ5DA`)
/// — this is a well-known PUBLIC network constant, not a secret and not the
/// mint/treasury. Every real SPL token account is owned by this program; the
/// consensus path binds it before trusting a decoded balance.
pub const SPL_TOKEN_PROGRAM_ID: [u8; 32] = [
    6, 221, 246, 225, 215, 101, 161, 147, 217, 203, 225, 70, 206, 235, 121, 172, 28, 180, 133, 237,
    95, 91, 55, 145, 58, 140, 245, 133, 126, 255, 0, 169,
];

/// Everything the operator configures. Nothing here is hardcoded to a mainnet
/// value in committed source: the mint + treasury are supplied at construction
/// (env in prod, throwaway fixtures in tests).
#[derive(Clone)]
pub struct PayConfig {
    /// The `$DREGG` SPL mint (32-byte pubkey). Operator config. In tests: a mock
    /// mint. In prod: the real mainnet mint from the environment.
    pub mint: [u8; 32],
    /// The treasury address swept deposits are sent to. Operator config.
    pub treasury: DepositAddress,
    /// The HD seed the per-user deposit keys are derived from. Secret custody
    /// material (see [`Seed`]).
    pub seed: Seed,
    /// Atomic `$DREGG` units required for one run credit (`price_per_run`). A
    /// payment of `N` atomic units credits `N / price_per_run` runs.
    pub price_per_run: u64,
    /// The Solana JSON-RPC endpoint the real watcher/sweeper use. Never hit in
    /// tests (the mock path uses no network).
    pub rpc_endpoint: String,
    /// Devnet (default, safe) or mainnet (operator flip, real funds).
    pub network: Network,
    /// The SPL Token program id — defaults to [`SPL_TOKEN_PROGRAM_ID`].
    pub spl_token_program: [u8; 32],
}

impl PayConfig {
    /// A devnet/mock config for driven tests — a THROWAWAY seed and a MOCK mint,
    /// never a real mainnet value. `price_per_run` in atomic `$DREGG` units.
    pub fn devnet_mock(
        seed: impl Into<Vec<u8>>,
        mint: [u8; 32],
        treasury: DepositAddress,
        price_per_run: u64,
    ) -> Self {
        PayConfig {
            mint,
            treasury,
            seed: Seed::new(seed),
            price_per_run,
            rpc_endpoint: "https://api.devnet.solana.com".to_string(),
            network: Network::Devnet,
            spl_token_program: SPL_TOKEN_PROGRAM_ID,
        }
    }

    /// Build a config from the operator environment. Reads:
    /// `DREGG_PAY_MINT` (base58 mint), `DREGG_PAY_TREASURY` (base58 treasury),
    /// `DREGG_PAY_SEED` (hex or base58 seed), `DREGG_PAY_PRICE_PER_RUN` (u64),
    /// `DREGG_PAY_RPC` (RPC url), `DREGG_PAY_NETWORK` (`devnet`|`mainnet`,
    /// default devnet). No mainnet value is ever a compiled-in default — the
    /// mint/treasury/seed MUST be supplied by the operator or this fails closed.
    pub fn from_env() -> Result<Self, ConfigError> {
        let get = |k: &str| std::env::var(k).map_err(|_| ConfigError::MissingEnv(k.to_string()));
        let mint = parse_pubkey_base58(&get("DREGG_PAY_MINT")?)?;
        let treasury = DepositAddress::from_base58(&get("DREGG_PAY_TREASURY")?)?;
        let seed_raw = get("DREGG_PAY_SEED")?;
        let seed_bytes = parse_seed(&seed_raw)?;
        let price_per_run = get("DREGG_PAY_PRICE_PER_RUN")?
            .parse::<u64>()
            .map_err(|_| ConfigError::BadValue("DREGG_PAY_PRICE_PER_RUN".to_string()))?;
        let rpc_endpoint = std::env::var("DREGG_PAY_RPC")
            .unwrap_or_else(|_| "https://api.devnet.solana.com".to_string());
        let network = match std::env::var("DREGG_PAY_NETWORK").as_deref() {
            Ok("mainnet") => Network::Mainnet,
            _ => Network::Devnet,
        };
        Ok(PayConfig {
            mint,
            treasury,
            seed: Seed::new(seed_bytes),
            price_per_run,
            rpc_endpoint,
            network,
            spl_token_program: SPL_TOKEN_PROGRAM_ID,
        })
    }
}

impl std::fmt::Debug for PayConfig {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("PayConfig")
            .field("mint", &bs58::encode(self.mint).into_string())
            .field("treasury", &self.treasury)
            .field("seed", &self.seed)
            .field("price_per_run", &self.price_per_run)
            .field("rpc_endpoint", &self.rpc_endpoint)
            .field("network", &self.network)
            .finish()
    }
}

/// A configuration error (fail closed — a missing/invalid operator value is never
/// silently defaulted to a mainnet constant).
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ConfigError {
    /// A required operator environment variable is absent.
    MissingEnv(String),
    /// A base58 pubkey did not decode to 32 bytes.
    BadPubkey(String),
    /// A seed value did not parse as hex or base58.
    BadSeed(String),
    /// A numeric/config value did not parse.
    BadValue(String),
}

impl std::fmt::Display for ConfigError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            ConfigError::MissingEnv(k) => write!(f, "missing operator env var {k}"),
            ConfigError::BadPubkey(s) => write!(f, "invalid base58 pubkey: {s}"),
            ConfigError::BadSeed(s) => write!(f, "invalid seed value: {s}"),
            ConfigError::BadValue(k) => write!(f, "invalid value for {k}"),
        }
    }
}

impl std::error::Error for ConfigError {}

/// Parse a base58 Solana pubkey into 32 bytes (fail closed on the wrong length).
pub fn parse_pubkey_base58(s: &str) -> Result<[u8; 32], ConfigError> {
    let v = bs58::decode(s.trim())
        .into_vec()
        .map_err(|_| ConfigError::BadPubkey(s.to_string()))?;
    if v.len() != 32 {
        return Err(ConfigError::BadPubkey(s.to_string()));
    }
    let mut out = [0u8; 32];
    out.copy_from_slice(&v);
    Ok(out)
}

/// Parse a seed given as `hex:...`/`0x...` hex or bare base58.
fn parse_seed(s: &str) -> Result<Vec<u8>, ConfigError> {
    let s = s.trim();
    if let Some(hex) = s.strip_prefix("hex:").or_else(|| s.strip_prefix("0x")) {
        return decode_hex(hex).ok_or_else(|| ConfigError::BadSeed("hex".to_string()));
    }
    bs58::decode(s)
        .into_vec()
        .map_err(|_| ConfigError::BadSeed("base58".to_string()))
}

fn decode_hex(s: &str) -> Option<Vec<u8>> {
    if s.len() % 2 != 0 {
        return None;
    }
    (0..s.len())
        .step_by(2)
        .map(|i| u8::from_str_radix(&s[i..i + 2], 16).ok())
        .collect()
}
