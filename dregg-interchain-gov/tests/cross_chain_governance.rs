//! # The full cross-chain non-custodial governance flow — end to end, all three chains
//!
//! A holder proves $DREGG holdings on **Solana**, an **EVM chain (Base)**, and a
//! **Cosmos chain (cosmoshub-4)** — non-custodially, each through its REAL light-client
//! verifier — binds each holding to ONE dregg voter with the wallet key that controls
//! it (Ed25519 / secp256k1-EIP-191 / secp256k1-Cosmos-sign-doc), and casts a single
//! holding-weighted ballot whose weight is the SUM across chains. Forgeries,
//! wrong-chain pairings, cross-chain binding confusion, double-counts, and stale
//! snapshots are all REFUSED, fail-closed.
//!
//! ## What is real vs fixture, honestly (per lane)
//!
//! - **Solana**: the bridge's `anchored_holding_with_cluster` test-utils fixture — a
//!   locally SYNTHESIZED 2-validator cluster (stake accounts, vote accounts, real
//!   Ed25519-signed TowerSync votes, bank-hash binding, a real PoH tick chain), driven
//!   through the REAL production verifier `prove_holding_consensus_anchored` under the
//!   cluster's own weak-subjectivity anchor. The VERIFICATION is the production code
//!   path; the CLUSTER is a fixture (there is no live Solana RPC in a unit test).
//! - **EVM**: a locally SYNTHESIZED token world (account + storage Merkle-Patricia
//!   tries built with the same pinned `alloy-trie` the verifier uses), opened through
//!   the REAL `verify_erc20_holding_finalized` EIP-1186 verifier. The state root is
//!   wrapped with `FinalizedExecution::new_unchecked` — the loud, greppable stand-in
//!   for a live sync-committee finality update (that BLS path is exercised against
//!   real beacon-chain KATs in eth-lightclient's own tests). ALSO exercised below:
//!   the GENUINE Ethereum mainnet WETH `eth_getProof` fixture through the same join.
//! - **Cosmos**: the GENUINE cosmoshub-4 fixture set — a real mainnet SignedHeader
//!   advance verified against the full 180-validator set (real Ed25519, ≥ 2/3 voting
//!   power) and a real ICS-23 bank-balance proof — flows through the compiled join.
//!   Its holder is a module account (no wallet key exists for it, by construction),
//!   so the BOUND-VOTE Cosmos lane uses fields for a holder we hold the key to,
//!   assembled with the edge crate's own decoder + conventions and honestly labeled
//!   `consensus_proven: true` AS A FIXTURE VERDICT (a bindable real fact would need a
//!   live chain and a funded account; the genuine-proof path is the test above it).

use dregg_bridge::solana_holdings::{
    fixtures as sol_fixtures, prove_holding_consensus_anchored, ProvenHolding,
};
use dregg_governance::holding_weight::{
    binding_message, cosmos_address_of_pubkey, cosmos_binding_prehash, eip191_message_hash,
    evm_address_of_pubkey, evm_binding_message, narrow_ballot_weight, CosmosOwnerBinding,
    EvmOwnerBinding, GrantError, HoldingWeightRegistry, OwnerBinding, VerifiedHoldingBallotBox,
    VoterBinding, WeightedBallotEngine,
};
use dregg_governance::proven_foreign_holding::{ChainId, ProvenForeignHolding};
use dregg_governance::{CastOutcome, DecisionRule, Electorate, OptionId, PollSpec, VoterId};
use dregg_interchain_gov::{
    cosmos_fact_to_governance, cosmos_fields_to_holding, evm_holding_to_governance,
    solana_holding_to_governance, JoinError,
};
use eth_lightclient::evm::{
    erc20_balance_slot_key, verify_erc20_holding, verify_erc20_holding_finalized, AccountClaim,
    Erc20ProofError, HoldingTrust, Uint256,
};
use eth_lightclient::finality::FinalizedExecution;

use ed25519_dalek::{Signer, SigningKey as Ed25519Key};
use k256::ecdsa::signature::hazmat::PrehashSigner;
use k256::ecdsa::{Signature as Secp256k1Signature, SigningKey as Secp256k1Key};

// ─────────────────────────────────────────────────────────────────────────────
// The genuine Ethereum mainnet WETH fixture (shared with eth-lightclient's own
// tests) — a real `eth_getProof` capture at a finalized mainnet block.
// ─────────────────────────────────────────────────────────────────────────────
#[allow(dead_code)]
#[path = "../../eth-lightclient/tests/fixtures/weth.rs"]
mod weth;

fn h32(s: &str) -> [u8; 32] {
    let v = hex::decode(s).expect("hex32");
    let mut a = [0u8; 32];
    a.copy_from_slice(&v);
    a
}
fn h20(s: &str) -> [u8; 20] {
    let v = hex::decode(s).expect("hex20");
    let mut a = [0u8; 20];
    a.copy_from_slice(&v);
    a
}
fn hex_nodes(list: &[&str]) -> Vec<Vec<u8>> {
    list.iter()
        .map(|s| hex::decode(s).expect("hex node"))
        .collect()
}
fn u256(s: &str) -> Uint256 {
    Uint256::from_str_radix(s, 16).expect("u256 hex")
}

/// The same guard `dregg-governance`'s positive-path tests use: the weight VERDICT is the
/// Lean-proven core, and when the linked archive lacks it the grant path fail-closes by design.
///
/// Routed through `demand_lean` (2026-07-27): "skip loudly" was to stderr, which cargo captures
/// and throws away on a passing test, so the three tests below reported `ok` having asserted
/// nothing about a three-chain weighted tally. An absent export is now a failure that names it.
fn lean_verdict_core_or_skip() -> bool {
    dregg_lean_ffi::demand_lean(
        dregg_lean_ffi::holding_grant_weight_core_available(),
        "dregg_holding_grant_weight export (the Lean-proven cross-chain weight verdict core)",
    )
}

// ─────────────────────────────────────────────────────────────────────────────
// Alice's three wallets — one keypair per chain, ONE dregg voter identity.
// ─────────────────────────────────────────────────────────────────────────────

const ALICE_VOTER: VoterId = [0xA1u8; 32];
const BOB_VOTER: VoterId = [0xB0u8; 32];

fn alice_solana_key() -> Ed25519Key {
    Ed25519Key::from_bytes(&[0x51u8; 32])
}
fn alice_evm_key() -> Secp256k1Key {
    Secp256k1Key::from_slice(&[0x52u8; 32]).expect("nonzero scalar")
}
fn alice_cosmos_key() -> Secp256k1Key {
    Secp256k1Key::from_slice(&[0x53u8; 32]).expect("nonzero scalar")
}
fn bob_solana_key() -> Ed25519Key {
    Ed25519Key::from_bytes(&[0x61u8; 32])
}

/// A genuine Ed25519 owner→voter binding (the Solana form).
fn ed25519_bind(owner: &Ed25519Key, voter: VoterId) -> OwnerBinding {
    let owner_pk = owner.verifying_key().to_bytes();
    let sig = owner.sign(&binding_message(&owner_pk, &voter)).to_bytes();
    OwnerBinding { voter, sig }
}

/// A genuine EVM binding: the wallet key really signs (RFC-6979, low-S) the
/// EIP-191 prehash for its own address, packed wallet-style r ‖ s ‖ v.
fn evm_bind(key: &Secp256k1Key, voter: VoterId) -> EvmOwnerBinding {
    let addr = evm_address_of_pubkey(key.verifying_key());
    let prehash = eip191_message_hash(&evm_binding_message(&addr, &voter));
    let (sig, recid) = key.sign_prehash_recoverable(&prehash).expect("signs");
    let mut bytes = [0u8; 65];
    bytes[..64].copy_from_slice(&sig.to_bytes());
    bytes[64] = recid.to_byte() + 27;
    EvmOwnerBinding { voter, sig: bytes }
}

/// A genuine Cosmos binding: sign the dregg Cosmos sign-doc prehash, carry the
/// compressed pubkey (Cosmos signatures ship the pubkey; no recovery id).
fn cosmos_bind(key: &Secp256k1Key, voter: VoterId) -> CosmosOwnerBinding {
    let addr = cosmos_address_of_pubkey(key.verifying_key());
    let prehash = cosmos_binding_prehash(&addr, &voter);
    let sig: Secp256k1Signature = key.sign_prehash(&prehash).expect("signs");
    let mut sig_bytes = [0u8; 64];
    sig_bytes.copy_from_slice(&sig.to_bytes());
    let mut pubkey = [0u8; 33];
    pubkey.copy_from_slice(key.verifying_key().to_encoded_point(true).as_bytes());
    CosmosOwnerBinding {
        voter,
        pubkey,
        sig: sig_bytes,
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// SOLANA lane: a synthesized cluster driven through the REAL anchored verifier.
// ─────────────────────────────────────────────────────────────────────────────

const DREGG_MINT: [u8; 32] = [0xD6u8; 32];
const SPL_TOKEN_PROGRAM: [u8; 32] = [0x06u8; 32];
/// The slot `anchored_holding_with_cluster` proves at (fixed inside the fixture).
const SOLANA_FIXTURE_SLOT: u64 = 7_000;

/// Prove `amount` $DREGG held by `wallet` on the synthesized-but-really-verified
/// Solana cluster. Runs the PRODUCTION `prove_holding_consensus_anchored` — stake
/// provenance derived from bank state under the pinned anchor, ≥ 2/3 authorized-voter
/// tally, bank-hash binding, PoH required.
fn solana_proven_holding(wallet: [u8; 32], token_account: [u8; 32], amount: u64) -> ProvenHolding {
    let (proof, anchor, policy) = sol_fixtures::anchored_holding_with_cluster(
        &DREGG_MINT,
        &SPL_TOKEN_PROGRAM,
        token_account,
        wallet,
        amount,
        &[(11, 700), (12, 300)],
    );
    prove_holding_consensus_anchored(
        &proof,
        &DREGG_MINT,
        &SPL_TOKEN_PROGRAM,
        &anchor,
        true,
        Some(&policy),
    )
    .expect("a genuine holding under the pinned anchor verifies")
}

// ─────────────────────────────────────────────────────────────────────────────
// EVM lane: a synthesized token world opened through the REAL EIP-1186 verifier.
// Same technique as eth-lightclient's own adversarial tests: tries built locally
// with the same pinned alloy-trie HashBuilder the verifier uses.
// ─────────────────────────────────────────────────────────────────────────────

mod evm_world {
    use super::*;
    use alloy_primitives::{keccak256, Bytes, B256};
    use alloy_trie::{proof::ProofRetainer, HashBuilder, Nibbles, TrieAccount};

    /// The (fictional, honestly-labeled) $DREGG ERC-20 contract on the test chain.
    pub const DREGG_TOKEN: [u8; 20] = [0xD7u8; 20];
    pub const BALANCES_SLOT: u64 = 3;
    pub const BLOCK_NUMBER: u64 = 21_000_000;

    /// Build a trie from (raw_key, rlp_value) pairs; return the root and each
    /// requested target's proof node list.
    fn build_trie(
        entries: &[(Vec<u8>, Vec<u8>)],
        targets: &[Vec<u8>],
    ) -> ([u8; 32], Vec<Vec<Vec<u8>>>) {
        let target_nibbles: Vec<Nibbles> = targets
            .iter()
            .map(|k| Nibbles::unpack(keccak256(k)))
            .collect();
        let retainer = ProofRetainer::new(target_nibbles.clone());
        let mut hb = HashBuilder::default().with_proof_retainer(retainer);
        let mut sorted: Vec<(Nibbles, &Vec<u8>)> = entries
            .iter()
            .map(|(k, v)| (Nibbles::unpack(keccak256(k)), v))
            .collect();
        sorted.sort_by(|a, b| a.0.cmp(&b.0));
        for (path, value) in sorted {
            hb.add_leaf(path, value);
        }
        let root: B256 = hb.root();
        let retained: Vec<(Nibbles, Bytes)> = hb.take_proof_nodes().into_nodes_sorted();
        let proofs = target_nibbles
            .iter()
            .map(|t| {
                retained
                    .iter()
                    .filter(|(p, _)| t.starts_with(p))
                    .map(|(_, n)| n.to_vec())
                    .collect::<Vec<_>>()
            })
            .collect();
        (root.0, proofs)
    }

    /// A synthesized world where `holder` has `balance` of DREGG_TOKEN (and a
    /// second unrelated holder pads the trie). Returns everything the verifier
    /// needs: state root, account proof, storage proof, account claim.
    pub struct World {
        pub state_root: [u8; 32],
        pub account_proof: Vec<Vec<u8>>,
        pub storage_proof: Vec<Vec<u8>>,
        pub account: AccountClaim,
    }

    pub fn world_with_balance(holder: [u8; 20], balance: u128) -> World {
        // Storage trie: balances[holder] = balance, plus one unrelated entry.
        let slot_key = erc20_balance_slot_key(&holder, BALANCES_SLOT).to_vec();
        let other_key = erc20_balance_slot_key(&[0x99u8; 20], BALANCES_SLOT).to_vec();
        let (storage_root, storage_proofs) = build_trie(
            &[
                (slot_key.clone(), alloy_rlp::encode(Uint256::from(balance))),
                (other_key, alloy_rlp::encode(Uint256::from(7u8))),
            ],
            &[slot_key],
        );
        // Account trie: the token contract account carrying that storage root.
        let account = AccountClaim {
            nonce: 1,
            balance: Uint256::ZERO,
            storage_hash: storage_root,
            code_hash: [0xCCu8; 32],
        };
        let account_rlp = alloy_rlp::encode(TrieAccount {
            nonce: account.nonce,
            balance: account.balance,
            storage_root: account.storage_hash.into(),
            code_hash: account.code_hash.into(),
        });
        let (state_root, account_proofs) = build_trie(
            &[(DREGG_TOKEN.to_vec(), account_rlp)],
            &[DREGG_TOKEN.to_vec()],
        );
        World {
            state_root,
            account_proof: account_proofs[0].clone(),
            storage_proof: storage_proofs[0].clone(),
            account,
        }
    }

    /// The loud, greppable stand-in for a live sync-committee finality update:
    /// eth-lightclient seals `FinalizedExecution` behind this constructor exactly
    /// so a test-asserted root is visible as such. The BLS finality path itself is
    /// KAT-tested in eth-lightclient's own suite.
    pub fn finalized_at(state_root: [u8; 32]) -> FinalizedExecution {
        FinalizedExecution::new_unchecked(0, [0u8; 32], BLOCK_NUMBER, [0u8; 32], state_root, 0)
    }
}

/// Alice's consensus-proven Base holding: the REAL EIP-1186 verifier over the
/// synthesized world, anchored at the (stand-in) finalized execution root.
fn alice_base_holding(balance: u128) -> eth_lightclient::evm::ProvenErc20Holding {
    let holder = evm_address_of_pubkey(alice_evm_key().verifying_key());
    let w = evm_world::world_with_balance(holder, balance);
    verify_erc20_holding_finalized(
        &evm_world::finalized_at(w.state_root),
        &w.account_proof,
        &w.storage_proof,
        evm_world::DREGG_TOKEN,
        holder,
        evm_world::BALANCES_SLOT,
        &w.account,
        Uint256::from(balance),
    )
    .expect("a genuine proof over the synthesized world verifies")
}

// ─────────────────────────────────────────────────────────────────────────────
// COSMOS lane (genuine mainnet fixtures): loaders mirroring
// cosmos-lightclient/tests/common, pointed at that crate's fixture directory.
// ─────────────────────────────────────────────────────────────────────────────

mod cosmos_fixtures {
    use base64::engine::general_purpose::STANDARD;
    use base64::Engine;
    use core::time::Duration;
    use cosmos_lightclient::{decode_commitment_proof, CosmosMembershipProof, TrustedCosmosState};
    use tendermint::block::signed_header::SignedHeader;
    use tendermint::validator::{Info, Set as ValidatorSet};
    use tendermint::Time;

    const DIR: &str = concat!(
        env!("CARGO_MANIFEST_DIR"),
        "/../cosmos-lightclient/tests/fixtures"
    );

    fn read(name: &str) -> String {
        std::fs::read_to_string(format!("{DIR}/{name}")).expect("cosmos fixture present")
    }

    fn signed_header(name: &str) -> SignedHeader {
        serde_json::from_str(&read(name)).expect("SignedHeader parses")
    }

    pub struct MembershipFixture {
        pub app_hash: Vec<u8>,
        pub proof: CosmosMembershipProof,
        pub key: Vec<u8>,
        pub value: Vec<u8>,
    }

    /// The genuine ICS-23 bank-balance proof (bonded_tokens_pool, uatom) whose
    /// root is committed as the H+1 header's app_hash.
    pub fn bank_balance_fixture() -> MembershipFixture {
        let v: serde_json::Value = serde_json::from_str(&read("bank_balance_proof.json")).unwrap();
        let b64 = |k: &str| STANDARD.decode(v[k].as_str().unwrap()).unwrap();
        let app_hash = hex::decode(v["app_hash_hex"].as_str().unwrap()).unwrap();
        MembershipFixture {
            app_hash,
            proof: CosmosMembershipProof {
                store_key: v["store_key"].as_str().unwrap().as_bytes().to_vec(),
                iavl_proof: decode_commitment_proof(&b64("iavl_proof_b64")).unwrap(),
                store_proof: decode_commitment_proof(&b64("simple_proof_b64")).unwrap(),
            },
            key: b64("iavl_key_b64"),
            value: b64("value_b64"),
        }
    }

    pub fn bank_untrusted_signed_header() -> SignedHeader {
        signed_header("bank_commit_h1.json")
    }

    pub fn bank_validators_h1() -> ValidatorSet {
        let infos: Vec<Info> =
            serde_json::from_str(&read("bank_validators_h1.json")).expect("validators");
        ValidatorSet::without_proposer(infos)
    }

    /// The WEAK-SUBJECTIVITY ANCHOR — `cosmos-lightclient`'s one un-gated constructor (there are
    /// no public fields; every other trusted state comes from `TrustedCosmosState::advance` off a
    /// gate-verified header).
    pub fn bank_trusted_state() -> TrustedCosmosState {
        let th = signed_header("bank_commit_h.json");
        TrustedCosmosState::weak_subjectivity_anchor(
            th.header.chain_id.clone(),
            th.header.time,
            th.header.height,
            bank_validators_h1(),
            th.header.next_validators_hash,
        )
        .expect("fixture anchor is self-consistent")
    }

    pub fn now_after(sh: &SignedHeader) -> Time {
        sh.header.time.checked_add(Duration::from_secs(60)).unwrap()
    }

    pub fn trusting_period() -> Duration {
        Duration::from_secs(14 * 24 * 60 * 60)
    }
}

/// Verify the REAL cosmoshub-4 header advance (full 180-validator set, real
/// Ed25519 ≥ 2/3 voting power) and bind the REAL ICS-23 bank-balance proof — the
/// only way a `ProvenCosmosFact` can exist.
///
/// Since 2026-07-29 this path runs through the VERIFIED Lean gate
/// (`dregg_tm_lc_verify`), so an archive that cannot render the decision makes it REFUSE. The
/// `demand_both` probe is the sanctioned form: under `DREGG_TEST_REQUIRE_LEAN` a missing archive
/// FAILS here rather than turning the whole cross-chain suite into a silent green.
fn real_cosmoshub_fact() -> cosmos_lightclient::ProvenCosmosFact {
    use tendermint_light_client_verifier::types::TrustThreshold;
    assert!(
        cosmos_lightclient::verified_gate::demand_both(),
        "the Cosmos light-client gates must be reachable — this suite's ProvenCosmosFact is minted \
         through them, and without them `verify_cosmos_header` fails closed"
    );
    let ush = cosmos_fixtures::bank_untrusted_signed_header();
    let header = cosmos_lightclient::verify_cosmos_header(
        &cosmos_fixtures::bank_trusted_state(),
        &ush,
        &cosmos_fixtures::bank_validators_h1(),
        None,
        TrustThreshold::TWO_THIRDS,
        cosmos_fixtures::trusting_period(),
        cosmos_fixtures::now_after(&ush),
    )
    .expect("genuine cosmoshub-4 header verifies");
    let f = cosmos_fixtures::bank_balance_fixture();
    assert_eq!(header.app_hash(), f.app_hash.as_slice());
    cosmos_lightclient::prove_cosmos_fact(&header, &f.proof, &f.key, &f.value)
        .expect("genuine bank-balance proof binds a fact")
}

/// The Cosmos BOUND-VOTE fields for a holder we hold the key to. The bank KV is
/// synthesized for Alice's address and driven through the edge crate's REAL
/// `decode_bank_balance_kv` decoder + padding/denom-commitment conventions;
/// `consensus_proven: true` is a FIXTURE VERDICT standing in for a header-verified
/// fact (see the module doc — the genuine header+ICS-23 path is exercised by
/// `real_cosmoshub_fact`, whose module-account holder has no wallet key to bind).
const COSMOS_VOTE_HEIGHT: u64 = 31_992_690;

fn alice_cosmos_fields(amount: u128) -> cosmos_lightclient::ForeignHoldingFields {
    let addr = cosmos_address_of_pubkey(alice_cosmos_key().verifying_key());
    let mut key = vec![0x02u8, 20];
    key.extend_from_slice(&addr);
    key.extend_from_slice(b"udregg");
    let value = amount.to_string();
    let bal = cosmos_lightclient::decode_bank_balance_kv(b"bank", &key, value.as_bytes())
        .expect("a well-formed bank KV decodes");
    assert_eq!(bal.address, addr.to_vec());
    assert_eq!(bal.amount, amount);
    let mut holder = [0u8; 32];
    holder[12..].copy_from_slice(&addr);
    cosmos_lightclient::ForeignHoldingFields {
        chain_tag: cosmos_lightclient::COSMOS_CHAIN_TAG,
        holder,
        asset: cosmos_lightclient::cosmos_denom_asset_id(&bal.denom),
        amount: bal.amount,
        snapshot: COSMOS_VOTE_HEIGHT,
        consensus_proven: true, // FIXTURE verdict — see doc comment above
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// THE FLOW — all three chains through to one tally.
// ─────────────────────────────────────────────────────────────────────────────

#[test]
fn full_cross_chain_flow_three_chains_one_weighted_tally() {
    if !lean_verdict_core_or_skip() {
        return;
    }

    // A poll: "adopt the treasury proposal?" with a pinned snapshot per chain.
    let mut engine = VerifiedHoldingBallotBox::new([0u8; 32]);
    let poll = engine
        .open_weighted_poll(&PollSpec {
            question: "adopt the treasury proposal?".into(),
            options: vec!["no".into(), "yes".into()],
            electorate: Electorate::Open,
            rule: DecisionRule::Plurality { quorum: 1 },
            enact_on_pass: false,
            nonce: 0,
        })
        .expect("the weighted holding poll opens on the verified executor");
    let mut reg = HoldingWeightRegistry::new();
    reg.open_chain_snapshot(poll, ChainId::Solana, SOLANA_FIXTURE_SLOT);
    reg.open_chain_snapshot(poll, ChainId::BASE, evm_world::BLOCK_NUMBER);
    reg.open_chain_snapshot(poll, ChainId::cosmos("cosmoshub-4"), COSMOS_VOTE_HEIGHT);

    // ALICE proves her holdings on all three chains, custody never moving:
    // 2000 $DREGG on Solana (real anchored consensus verifier over the fixture cluster),
    let sol = solana_proven_holding(
        alice_solana_key().verifying_key().to_bytes(),
        [0xAAu8; 32],
        2_000,
    );
    assert!(sol.is_consensus_proven());
    let sol_fact = solana_holding_to_governance(&sol);
    // 1000 $DREGG on Base (real EIP-1186 verifier over the synthesized world),
    let base = alice_base_holding(1_000);
    assert_eq!(base.trust(), HoldingTrust::ConsensusProven);
    let base_fact = evm_holding_to_governance(&base, 8453).expect("the EVM join compiles + holds");
    assert_eq!(base_fact.chain, ChainId::BASE);
    // 500 $DREGG on cosmoshub-4 (edge-decoder-driven fields; fixture verdict).
    let cosmos_fact = cosmos_fields_to_holding(&alice_cosmos_fields(500), "cosmoshub-4")
        .expect("the Cosmos join compiles + holds");

    // She binds each holding to ONE dregg voter with the wallet key that controls
    // it — three signature schemes, one voter, zero custody movement.
    let sol_bind = VoterBinding::Ed25519(ed25519_bind(&alice_solana_key(), ALICE_VOTER));
    let base_bind = VoterBinding::Evm(evm_bind(&alice_evm_key(), ALICE_VOTER));
    let cosmos_bind_ = VoterBinding::Cosmos(cosmos_bind(&alice_cosmos_key(), ALICE_VOTER));

    // Each holding grants weight through the fail-closed path (consensus verdict →
    // binding → positive amount → the Lean-proven weight verdict → per-chain
    // snapshot pin → consume-once nullifier).
    let g_sol = reg
        .grant_foreign_into_poll(poll, &sol_fact, &sol_bind)
        .expect("Solana grant");
    let g_base = reg
        .grant_foreign_into_poll(poll, &base_fact, &base_bind)
        .expect("Base grant");
    let g_cosmos = reg
        .grant_foreign_into_poll(poll, &cosmos_fact, &cosmos_bind_)
        .expect("Cosmos grant");
    assert_eq!(g_sol.weight, 2_000);
    assert_eq!(g_base.weight, 1_000);
    assert_eq!(g_cosmos.weight, 500);
    // Three chains, three distinct nullifiers, one voter.
    assert_eq!(g_sol.voter, ALICE_VOTER);
    assert_eq!(g_base.voter, ALICE_VOTER);
    assert_eq!(g_cosmos.voter, ALICE_VOTER);
    assert_ne!(g_sol.nullifier, g_base.nullifier);
    assert_ne!(g_base.nullifier, g_cosmos.nullifier);

    // ONE ballot carrying the cross-chain sum (the fail-closed u128 → u64 narrowing).
    let alice_weight =
        narrow_ballot_weight(g_sol.weight + g_base.weight + g_cosmos.weight).expect("fits");
    assert_eq!(alice_weight, 3_500);
    assert_eq!(
        engine
            .cast_weighted_ballot(poll, ALICE_VOTER, OptionId(1), alice_weight)
            .expect("poll is open"),
        CastOutcome::Accepted
    );

    // BOB votes the other way with a Solana-only holding (1200), via the
    // grant-and-cast convenience.
    let bob = solana_proven_holding(
        bob_solana_key().verifying_key().to_bytes(),
        [0xBBu8; 32],
        1_200,
    );
    let bob_fact = solana_holding_to_governance(&bob);
    let bob_bind = VoterBinding::Ed25519(ed25519_bind(&bob_solana_key(), BOB_VOTER));
    let outcome = reg
        .foreign_grant_and_cast(&mut engine, poll, OptionId(0), &bob_fact, &bob_bind)
        .expect("Bob's grant-and-cast");
    assert_eq!(outcome, CastOutcome::Accepted);

    // THE CROSS-CHAIN WEIGHTED OUTCOME.
    let tally = engine.tally(poll).expect("tally derives");
    assert_eq!(
        tally.per_option.get(1).copied().unwrap_or(0),
        3_500,
        "Alice's weight is the SUM of her proven holdings across three chains"
    );
    assert_eq!(tally.per_option.get(0).copied().unwrap_or(0), 1_200);
    assert_eq!(
        tally.total, 4_700,
        "the whole board is Alice's 3500 plus Bob's 1200, two voters"
    );

    // Re-presenting ANY of Alice's holdings in the same poll is refused — the
    // per-(poll, chain+holder+asset) nullifier already fired.
    assert_eq!(
        reg.grant_foreign_into_poll(poll, &base_fact, &base_bind),
        Err(GrantError::AlreadyCounted)
    );
    assert_eq!(
        reg.grant_foreign_into_poll(poll, &sol_fact, &sol_bind),
        Err(GrantError::AlreadyCounted)
    );
}

// ─────────────────────────────────────────────────────────────────────────────
// THE GENUINE-MAINNET JOIN — real WETH eth_getProof + real cosmoshub-4 header
// + ICS-23 proof, through the same compiled join the flow above uses.
// ─────────────────────────────────────────────────────────────────────────────

#[test]
fn real_mainnet_fixtures_flow_through_the_compiled_join() {
    // EVM: the genuine mainnet WETH EIP-1186 capture, anchored at its fixture
    // state root (new_unchecked = the loud stand-in for a verified finality
    // update; the proof nodes and tries are real mainnet data).
    let finalized = FinalizedExecution::new_unchecked(
        0,
        [0u8; 32],
        weth::BLOCK_NUMBER,
        [0u8; 32],
        h32(weth::STATE_ROOT),
        0,
    );
    let holding = verify_erc20_holding_finalized(
        &finalized,
        &hex_nodes(weth::ACCOUNT_PROOF),
        &hex_nodes(weth::STORAGE_PROOF),
        h20(weth::TOKEN),
        h20(weth::HOLDER),
        weth::BALANCES_SLOT,
        &AccountClaim {
            nonce: weth::ACCT_NONCE,
            balance: u256(weth::ACCT_BALANCE_HEX),
            storage_hash: h32(weth::ACCT_STORAGE_HASH),
            code_hash: h32(weth::ACCT_CODE_HASH),
        },
        u256(weth::EXPECTED_BALANCE_HEX),
    )
    .expect("the real mainnet WETH proof verifies");
    let fact = evm_holding_to_governance(&holding, 1).expect("the join holds for mainnet data");
    assert_eq!(fact.chain, ChainId::ETHEREUM);
    assert!(fact.consensus_proven);
    assert_eq!(Uint256::from(fact.amount), u256(weth::EXPECTED_BALANCE_HEX));
    assert_eq!(&fact.holder[..12], &[0u8; 12]);
    assert_eq!(&fact.holder[12..], &h20(weth::HOLDER));
    assert_eq!(fact.snapshot, weth::BLOCK_NUMBER);

    // NON-CUSTODIAL AUTHORITY TOOTH: we do NOT hold the real WETH holder's key,
    // so no binding we can mint grants its weight — a stranger's signature is
    // UnboundOwner, fail closed.
    let stranger = evm_bind(&alice_evm_key(), ALICE_VOTER);
    let mut reg = HoldingWeightRegistry::new();
    let poll = dregg_governance::PollId([7u8; 32]);
    reg.open_chain_snapshot(poll, ChainId::ETHEREUM, weth::BLOCK_NUMBER);
    assert_eq!(
        reg.grant_foreign_into_poll(poll, &fact, &stranger),
        Err(GrantError::UnboundOwner),
        "custody AND authority stay with the real holder"
    );

    // COSMOS: the genuine cosmoshub-4 header advance (180 validators, real
    // Ed25519 ≥ 2/3) + the genuine ICS-23 bank-balance proof, through the join.
    let fact = cosmos_fact_to_governance(&real_cosmoshub_fact(), "cosmoshub-4")
        .expect("the join holds for mainnet cosmos data");
    assert_eq!(fact.chain, ChainId::cosmos("cosmoshub-4"));
    assert!(fact.consensus_proven);
    assert_eq!(
        fact.amount, 331_305_561_223_899u128,
        "the real on-chain uatom balance"
    );
    assert_eq!(fact.snapshot, 31_992_690);
    // The holder is the bonded_tokens_pool MODULE account: no wallet key exists,
    // so no binding can wield it — fail closed again.
    let mut reg = HoldingWeightRegistry::new();
    reg.open_chain_snapshot(poll, ChainId::cosmos("cosmoshub-4"), fact.snapshot);
    assert_eq!(
        reg.grant_foreign_into_poll(poll, &fact, &cosmos_bind(&alice_cosmos_key(), ALICE_VOTER)),
        Err(GrantError::UnboundOwner)
    );

    // Pinning the WRONG chain refuses at the edge (the fact is cosmoshub-4's).
    assert!(matches!(
        cosmos_fact_to_governance(&real_cosmoshub_fact(), "osmosis-1"),
        Err(JoinError::CosmosFields(_))
    ));
}

// ─────────────────────────────────────────────────────────────────────────────
// REJECT POLARITY — forgeries and confusions, each refused fail-closed.
// ─────────────────────────────────────────────────────────────────────────────

/// A forged EVM holding: tamper one storage-proof node → the REAL verifier
/// refuses; no holding object ever exists to vote with.
#[test]
fn forged_evm_storage_proof_is_refused() {
    let holder = evm_address_of_pubkey(alice_evm_key().verifying_key());
    let w = evm_world::world_with_balance(holder, 1_000);
    let mut tampered = w.storage_proof.clone();
    let last = tampered.len() - 1;
    tampered[last][5] ^= 0x01;
    let r = verify_erc20_holding_finalized(
        &evm_world::finalized_at(w.state_root),
        &w.account_proof,
        &tampered,
        evm_world::DREGG_TOKEN,
        holder,
        evm_world::BALANCES_SLOT,
        &w.account,
        Uint256::from(1_000u64),
    );
    assert_eq!(r, Err(Erc20ProofError::StorageProofInvalid));
}

/// An inflated claim over honest state: the trie does not commit the bigger
/// balance → refused.
#[test]
fn inflated_evm_balance_claim_is_refused() {
    let holder = evm_address_of_pubkey(alice_evm_key().verifying_key());
    let w = evm_world::world_with_balance(holder, 1_000);
    let r = verify_erc20_holding_finalized(
        &evm_world::finalized_at(w.state_root),
        &w.account_proof,
        &w.storage_proof,
        evm_world::DREGG_TOKEN,
        holder,
        evm_world::BALANCES_SLOT,
        &w.account,
        Uint256::from(1_000_000u64), // the lie
    );
    assert_eq!(r, Err(Erc20ProofError::StorageProofInvalid));
}

/// A structure-only EVM holding (bare caller-asserted root — the RPC-echo rung)
/// converts with `consensus_proven: false` and grants ZERO weight: Nomad law.
#[test]
fn structure_only_evm_holding_grants_zero_weight() {
    let holder = evm_address_of_pubkey(alice_evm_key().verifying_key());
    let w = evm_world::world_with_balance(holder, 1_000);
    let bare = verify_erc20_holding(
        w.state_root, // caller-asserted, NOT a finality-verified root
        &w.account_proof,
        &w.storage_proof,
        evm_world::DREGG_TOKEN,
        holder,
        evm_world::BALANCES_SLOT,
        &w.account,
        Uint256::from(1_000u64),
        evm_world::BLOCK_NUMBER,
    )
    .expect("structure verifies");
    assert_eq!(bare.trust(), HoldingTrust::StructureOnly);
    let fact = evm_holding_to_governance(&bare, 8453).expect("joins, carrying the weak verdict");
    assert!(!fact.consensus_proven);

    let mut reg = HoldingWeightRegistry::new();
    let poll = dregg_governance::PollId([8u8; 32]);
    reg.open_chain_snapshot(poll, ChainId::BASE, evm_world::BLOCK_NUMBER);
    assert_eq!(
        reg.grant_foreign_into_poll(poll, &fact, &evm_bind(&alice_evm_key(), ALICE_VOTER)),
        Err(GrantError::NotConsensusProven),
        "an RPC echo grants ZERO weight, fail closed"
    );
}

/// Cross-chain binding confusion: a genuine binding from the WRONG chain's key
/// (or scheme) never wields a holding — chain-shape dispatch refuses.
#[test]
fn cross_chain_binding_confusion_is_refused() {
    if !lean_verdict_core_or_skip() {
        return;
    }
    let base_fact = evm_holding_to_governance(&alice_base_holding(1_000), 8453).unwrap();
    let cosmos_fact = cosmos_fields_to_holding(&alice_cosmos_fields(500), "cosmoshub-4").unwrap();

    let mut reg = HoldingWeightRegistry::new();
    let poll = dregg_governance::PollId([9u8; 32]);
    reg.open_chain_snapshot(poll, ChainId::BASE, evm_world::BLOCK_NUMBER);
    reg.open_chain_snapshot(poll, ChainId::cosmos("cosmoshub-4"), COSMOS_VOTE_HEIGHT);

    // A Cosmos binding presented for the EVM holding: refused (even though both
    // holders are padded 20-byte shapes — the chain gate + different address
    // derivations both refuse).
    assert_eq!(
        reg.grant_foreign_into_poll(
            poll,
            &base_fact,
            &cosmos_bind(&alice_cosmos_key(), ALICE_VOTER)
        ),
        Err(GrantError::UnboundOwner)
    );
    // An EVM binding presented for the Cosmos holding: refused.
    assert_eq!(
        reg.grant_foreign_into_poll(poll, &cosmos_fact, &evm_bind(&alice_evm_key(), ALICE_VOTER)),
        Err(GrantError::UnboundOwner)
    );
    // A binding minted for one voter, replayed for another: the prehash commits
    // to the voter, so the signature no longer verifies — refused.
    let mut replay = evm_bind(&alice_evm_key(), ALICE_VOTER);
    replay.voter = BOB_VOTER;
    assert_eq!(
        reg.grant_foreign_into_poll(poll, &base_fact, &replay),
        Err(GrantError::UnboundOwner)
    );
    // The genuine pairings, for contrast, clear the binding gate (positive
    // control so the refusals above are meaningful).
    assert!(reg
        .grant_foreign_into_poll(poll, &base_fact, &evm_bind(&alice_evm_key(), ALICE_VOTER))
        .is_ok());
    assert!(reg
        .grant_foreign_into_poll(
            poll,
            &cosmos_fact,
            &cosmos_bind(&alice_cosmos_key(), ALICE_VOTER)
        )
        .is_ok());
}

/// A holding proven at a height other than the poll's per-chain pinned snapshot
/// is refused — the move-the-tokens double-count defence, per chain.
#[test]
fn wrong_snapshot_height_is_refused() {
    if !lean_verdict_core_or_skip() {
        return;
    }
    let base_fact = evm_holding_to_governance(&alice_base_holding(1_000), 8453).unwrap();
    let mut reg = HoldingWeightRegistry::new();
    let poll = dregg_governance::PollId([10u8; 32]);
    // The poll pins a DIFFERENT Base block.
    reg.open_chain_snapshot(poll, ChainId::BASE, evm_world::BLOCK_NUMBER + 1);
    assert_eq!(
        reg.grant_foreign_into_poll(poll, &base_fact, &evm_bind(&alice_evm_key(), ALICE_VOTER)),
        Err(GrantError::WrongSnapshot {
            holding_slot: evm_world::BLOCK_NUMBER,
            poll_snapshot: evm_world::BLOCK_NUMBER + 1
        })
    );
    // And a chain with NO pin refuses outright.
    let unpinned = dregg_governance::PollId([11u8; 32]);
    assert_eq!(
        reg.grant_foreign_into_poll(
            unpinned,
            &base_fact,
            &evm_bind(&alice_evm_key(), ALICE_VOTER)
        ),
        Err(GrantError::NoSnapshot)
    );
}

/// The genuine cosmoshub-4 proof refuses a tampered value — a forged Cosmos
/// balance never even becomes a fact.
#[test]
fn tampered_cosmos_value_never_binds_a_fact() {
    use tendermint_light_client_verifier::types::TrustThreshold;
    let ush = cosmos_fixtures::bank_untrusted_signed_header();
    let header = cosmos_lightclient::verify_cosmos_header(
        &cosmos_fixtures::bank_trusted_state(),
        &ush,
        &cosmos_fixtures::bank_validators_h1(),
        None,
        TrustThreshold::TWO_THIRDS,
        cosmos_fixtures::trusting_period(),
        cosmos_fixtures::now_after(&ush),
    )
    .unwrap();
    let f = cosmos_fixtures::bank_balance_fixture();
    let mut inflated = f.value.clone();
    inflated[0] = b'9';
    assert_eq!(
        cosmos_lightclient::prove_cosmos_fact(&header, &f.proof, &f.key, &inflated),
        Err(cosmos_lightclient::MembershipError::IavlProofInvalid)
    );
}
