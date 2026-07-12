//! REAL external accept-KAT — Ethereum MAINNET beacon `light_client/finality_update`
//! captured from a public beacon node (publicnode.com), fork `fulu` (post-Electra).
//! Genuine chain data, NOT a round-trip: it validates `verify_finality_branch`
//! (post-Electra FINALIZED_ROOT_GINDEX=169, depth 7, subtree index 41), the
//! `BeaconBlockHeader` HTR, the 17-field `ExecutionPayloadHeader` HTR, and
//! `verify_execution_payload` (EXECUTION_PAYLOAD_GINDEX=25, depth 4). The recovered
//! execution state_root MATCHES the WETH proof fixture block — the two chain end-to-end.
//! Regenerate: scratchpad/gen_beacon.py over the finality_update JSON.

// --- attested header (its state_root is what finality_branch is proven against) ---
pub const ATTESTED_SLOT: u64 = 14749306;
pub const ATTESTED_PROPOSER: u64 = 798971;
pub const ATTESTED_PARENT_ROOT: &str =
    "120801437db1a2dbce2b3a044472806d68a3e56df5bb876b6b699953ad7d13ef";
pub const ATTESTED_STATE_ROOT: &str =
    "169384fde580fa8a71df6f31c0e14e056c1e3f3f2dcacf7fb8218a6bcc64d1bf";
pub const ATTESTED_BODY_ROOT: &str =
    "31633f9543b1813a16bdf54382a14a4a040e3bc0be27e75ecfca331fd47fb38a";

// --- finalized beacon header ---
pub const FIN_SLOT: u64 = 14749216;
pub const FIN_PROPOSER: u64 = 797812;
pub const FIN_PARENT_ROOT: &str =
    "9f5cc4f188c21fb76c9f4ba450b368469ccf717e10773adf6747db0f6b988022";
pub const FIN_STATE_ROOT: &str = "5de754cc369692b4e9a6d1990a452b9eef07a16b362de717bf47a1890255a2ed";
pub const FIN_BODY_ROOT: &str = "a42d0e7c4700ffb08b52a003ee65c11f8f7ca87eab9325745fc8727e64608d90";

// --- finalized execution payload header (17 fields, Deneb/Electra/Fulu) ---
pub const EX_PARENT_HASH: &str = "11b448b1b8e05ddfbe3747756fb7741e75b45879811d34966e56bc5ec3b6c01b";
pub const EX_FEE_RECIPIENT: &str = "dadb0d80178819f2319190d340ce9a924f783711";
pub const EX_STATE_ROOT: &str = "5e7354b2096400d76b30ebb80753aec8dd275763fc186480152e7a1f2eeb054d";
pub const EX_RECEIPTS_ROOT: &str =
    "651e41785b1df29be5395fbd312f13209a5119f91a8353e396c2373b168efd71";
pub const EX_LOGS_BLOOM: &str = "ad65506bf9967fff6e4defeea9d2dfa15f5d7d1fd5b956f6ef79f7bd7e57bfbfd89ffecff37af5ab879effc1edced5e4dfb9d77dbf7fafef5f99bff5fefd7dbe76bfbe7bd8fdeaef7bfddde8ffedf6fc52eeb6ff7f7e1fb65bfb7f3be3edf7c7bf7d8e73ff6cb5eb7fd4f9fdadd5cfdffbf749ffd8bef7bf578e5aff381ebeda337dbcda3f3c5ffd7eff566ba72e5fbf6384fdffffdfcfcf7bcc6f75fffed9fad6c6ed77fad67eb3fbf7bbfedd5f37c8efd3fcff04bc44da57ff6a33fede7c7764be5f7f43cffa7a75ffbe27d7fbb30957bf7dda5ffd36b655bff3fadff77edb5fdcb7c7fbf799fb1f79affadfeb1d52ed7fffbbdf3f84d65ffbf976ffebe797";
pub const EX_PREV_RANDAO: &str = "106657a49e27cc42c6cc3366ff813c76fa7e0eb0ef35483be2e4549d9ac0c85e";
pub const EX_BLOCK_NUMBER: u64 = 25512833;
pub const EX_GAS_LIMIT: u64 = 60000000;
pub const EX_GAS_USED: u64 = 52161058;
pub const EX_TIMESTAMP: u64 = 1783814615;
pub const EX_EXTRA_DATA: &str = "4275696c6465724e6574";
/// base_fee_per_gas as SSZ 32-byte LITTLE-ENDIAN uint256 (JSON gives decimal 123660355).
pub const EX_BASE_FEE_LE32: &str =
    "43e85e0700000000000000000000000000000000000000000000000000000000";
pub const EX_BLOCK_HASH: &str = "60105537fc77d9d2a3aaa5304de109bfd975a31943cad560a4e7e34f72464c51";
pub const EX_TRANSACTIONS_ROOT: &str =
    "0d68121074548acea5bcee3c14828d88384ae41948c84151269b769fd0d2acc4";
pub const EX_WITHDRAWALS_ROOT: &str =
    "ecf269eb9e6bc6472efad1657b49be5b7f087b3fc015cbbe3fec6310822b33d5";
pub const EX_BLOB_GAS_USED: u64 = 393216;
pub const EX_EXCESS_BLOB_GAS: u64 = 184985647;

/// finality branch (7 nodes, post-Electra depth 7)
pub const FINALITY_BRANCH: &[&str] = &[
    "7108070000000000000000000000000000000000000000000000000000000000",
    "106b2759d67d19a09efbddd029afef8618ea739a0b7ae2b33826d78c0755b867",
    "750ca07658c35fcd8c92c3487f3fac2a9146399369d12157252255020deb0584",
    "7fddfaa6e8175bc74feb5ac97cf7f3f1c17a2f5c930f92f738d687df7cfd02f4",
    "a360f6fd8d0eb71aa27203cc6b0ca654f74b61336977dd3b7cdaff6deb546872",
    "8ecfbf67c4707509a84de6b249032f3fd7b0d67538dcffe8e53e4a532af78a1a",
    "815c47cbb9ad933d24bdf2db508ff33badfad0094a39e1017af2b6f1fea71799",
];

/// execution branch (4 nodes, depth 4)
pub const EXECUTION_BRANCH: &[&str] = &[
    "3ecfd8cb63b54450410304cfc75b2fc58901b078521b8b8110d3ce968772f306",
    "bad9c658e495b1c9e35f5901a1f4603495195b3f71690de647e65525276b11eb",
    "6dd3b9955d892d92338b19976fd07084bfe88a76c3063482b7f30ee60feb2a58",
    "2ae0602805a8e78d1512723dcecdf13c05d8ea5d905e6f401b1cd102bb60b0fb",
];
