//! The **NFT EXPORT leg** — project a dregg-proven achievement OUT to Solana as a
//! 1-of-1 SPL NFT that CARRIES the dregg proof.
//!
//! This is the exact INVERSE of the built import rail (`bridge::solana_holdings`,
//! the non-custodial proof-of-holdings read): instead of proving a Solana balance
//! INTO dregg, it projects a dregg-native, already-proven achievement (a cheevo /
//! run — `dregg-season` hall-of-fame, `loot.rs` fair-drop assets, the no-cheat
//! board) OUT onto a durable external chain as a **1-of-1 SPL NFT** whose metadata
//! memo carries the run/cheevo commitment. The earned-ness travels with the token.
//!
//! # Why an SPL NFT (not dregg-native, not a JPEG)
//!
//! * **EARNED / PROVABLE.** The mint is not a picture; it is a token whose memo
//!   binds a dregg proof (a `commitment` to the run/cheevo). Anyone can read the
//!   memo and re-check the earned-ness against dregg — the token is a portable
//!   receipt, not a collectible.
//! * **NOT dregg-native.** Living on Solana as a plain SPL mint dodges dregg-devnet
//!   churn (a re-genesis does not orphan the asset). It is re-importable when
//!   convenient via the existing `ProvenForeignHolding` + `bridge_mint_against_lock`
//!   rail — a 1-of-1 SPL fits the `(asset, amount ≥ 1)` shape as-is (a named
//!   residual below).
//!
//! # The 1-of-1 shape (a TRUE 1-of-1, enforced by the instruction set)
//!
//! A 1-of-1 is not a convention — it is forced by the built transaction:
//! 1. **`SystemProgram::CreateAccount`** — allocate the new mint account (82 bytes,
//!    owner = SPL Token program), rent-funded by the custody payer. The mint account
//!    is a fresh keypair that must co-sign.
//! 2. **`InitializeMint2`** — `decimals = 0` (indivisible), mint & freeze authority =
//!    the custody key.
//! 3. **`AssociatedTokenAccount::Create`** — the recipient's associated token account
//!    (the canonical off-curve PDA of `[recipient, token_program, mint]`).
//! 4. **`MintTo`** — mint **exactly `1`** unit to the recipient's ATA.
//! 5. **`SetAuthority(MintTokens → None)`** — DROP the mint authority, so no further
//!    supply can EVER be minted. Supply is frozen at 1 forever — the token is
//!    genuinely one-of-one, not merely one-so-far.
//! 6. **`Memo`** — the dregg proof (`dregg-nft/v1|<cheevo>|<bs58(commitment)>`,
//!    valid UTF-8 as the Memo program requires) travels in the transaction.
//!
//! # Custody / signing
//!
//! Signing reuses the sweeper's custody model: the mint authority + fee payer is an
//! HD-derived key ([`crate::hd`]), and the exact bytes signed are recovered by the
//! same [`crate::swap::solana_sign_target`] the swap path uses (the transaction
//! MESSAGE, past the signature slots). Two signers sign that one message: the
//! custody authority and the ephemeral mint account.
//!
//! # Named residuals (honest scope)
//!
//! * **The LIVE RPC [`NftTxSubmitter`]** — assembling a fresh recent-blockhash and
//!   `sendTransaction` to a real Solana RPC. The builder + signer are real here; the
//!   in-test submitter is a mock that re-verifies the signature. This is the SAME
//!   seam the sweeper's `TxSubmitter` names.
//! * **Metaplex metadata / compressed cNFTs** — richer, indexer-friendly metadata
//!   (name/image/attributes) and cheap-at-scale cNFTs are a bigger dependency; the
//!   memo carries the proof today.
//! * **The royalty / marketplace-fee rail** — a cut on a secondary sale routed to
//!   the treasury is a separate leg (no settlement path takes a cut today).
//! * **Re-import** — `ProvenForeignHolding` + `bridge_mint_against_lock` already fit
//!   a 1-of-1 SPL `(asset, amount ≥ 1)`; wiring the mint-back is nearly free.

use ed25519_dalek::{Signer, SigningKey};
use sha2::{Digest, Sha256};

use crate::config::PayConfig;
use crate::hd::HdDeposit;
use crate::swap::solana_sign_target;

// ─────────────────────────────────────────────────────────────────────────────
// Public Solana program-id constants (network constants, not secrets / not mints)
// ─────────────────────────────────────────────────────────────────────────────

/// The System program id (`11111111111111111111111111111111`) — all-zero pubkey.
/// Owns / creates the new mint account via `CreateAccount`.
pub const SYSTEM_PROGRAM_ID: [u8; 32] = [0u8; 32];

/// The Associated Token Account program id
/// (`ATokenGPvbdGVxr1b2hvZbsiqW5xWH25efTNsLJA8knL`). Derives + creates the
/// recipient's canonical token account for the mint.
pub const ATA_PROGRAM_ID: [u8; 32] = [
    140, 151, 37, 143, 78, 36, 137, 241, 187, 61, 16, 41, 20, 142, 13, 131, 11, 90, 19, 153, 218,
    255, 16, 132, 4, 142, 123, 216, 219, 233, 248, 89,
];

/// The SPL Memo v2 program id (`MemoSq4gqABAXKb96qnH8TysNcWxMyWCqXgDLGmfcHr`). The
/// dregg proof rides in a memo instruction to this program. The Memo program
/// validates its data as UTF-8, so the proof is encoded as a UTF-8 string.
pub const MEMO_PROGRAM_ID: [u8; 32] = [
    5, 74, 83, 90, 153, 41, 33, 6, 77, 36, 232, 113, 96, 218, 56, 124, 124, 53, 181, 221, 188, 146,
    187, 129, 228, 31, 168, 64, 65, 5, 68, 141,
];

/// The on-chain byte length of an SPL `Mint` account (`spl_token::state::Mint::LEN`).
pub const SPL_MINT_LEN: u64 = 82;

/// A rent-exempt reserve (lamports) sufficient for an 82-byte SPL mint account on
/// mainnet. A default; the live submitter can recompute from the cluster's rent
/// sysvar. This is a network constant, not a secret.
pub const MINT_RENT_LAMPORTS: u64 = 1_461_600;

// SPL Token instruction discriminants (`spl_token::instruction::TokenInstruction`).
const IX_INITIALIZE_MINT2: u8 = 20;
const IX_MINT_TO: u8 = 7;
const IX_SET_AUTHORITY: u8 = 6;
// SPL Token `AuthorityType::MintTokens`.
const AUTHORITY_TYPE_MINT_TOKENS: u8 = 0;
// System program `CreateAccount` instruction index (u32 LE).
const SYS_IX_CREATE_ACCOUNT: u32 = 0;
// Associated Token Account `Create` instruction discriminant (Borsh enum variant 0).
const ATA_IX_CREATE: u8 = 0;

// ─────────────────────────────────────────────────────────────────────────────
// The dregg proof carried in the NFT
// ─────────────────────────────────────────────────────────────────────────────

/// The dregg proof the exported NFT carries — the portable earned-ness. This is a
/// commitment to the already-dregg-proven run / cheevo (e.g. a receipt / settlement
/// commitment, or the champions-board leaf), plus a human-readable achievement id.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct DreggAchievementProof {
    /// A 32-byte commitment to the run / cheevo the NFT attests (the dregg-native
    /// proof this export is anchored to). MUST be non-zero — an all-zero commitment
    /// is "no proof" and is refused by the builder.
    pub commitment: [u8; 32],
    /// A human-readable achievement id (e.g. `"descent:first-crown"`). MUST be
    /// non-empty.
    pub cheevo_id: String,
}

impl DreggAchievementProof {
    /// The memo bytes carried in the transaction — a UTF-8 string (the Memo program
    /// rejects non-UTF-8):
    /// `dregg-nft/v1|<cheevo_id>|<base58(commitment)>`.
    pub fn memo_bytes(&self) -> Vec<u8> {
        format!(
            "dregg-nft/v1|{}|{}",
            self.cheevo_id,
            bs58::encode(self.commitment).into_string()
        )
        .into_bytes()
    }

    /// Whether this proof is present (non-empty id + non-zero commitment). A missing
    /// proof defeats the whole point of an EARNED NFT and is refused.
    fn is_present(&self) -> bool {
        !self.cheevo_id.is_empty() && self.commitment != [0u8; 32]
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// The mint request + the built product
// ─────────────────────────────────────────────────────────────────────────────

/// A request to export an achievement as a 1-of-1 SPL NFT.
#[derive(Clone, Debug)]
pub struct MintNftRequest {
    /// The recipient wallet (32-byte Solana pubkey) that will OWN the NFT. Its
    /// canonical associated token account receives the single unit. MUST NOT be the
    /// all-zero System program id.
    pub recipient: [u8; 32],
    /// The supply to mint. For a 1-of-1 this MUST be exactly `1`; the builder refuses
    /// anything else (this is what makes it a NON-vacuous 1-of-1 check).
    pub supply: u64,
    /// The dregg proof (the earned-ness) carried in the NFT memo.
    pub proof: DreggAchievementProof,
    /// A recent Solana blockhash. On the live path the submitter supplies a fresh one
    /// from the RPC; in tests a fixed fixture blockhash. The message is signed over
    /// it, so it must be final before signing.
    pub recent_blockhash: [u8; 32],
}

/// Why building / minting a 1-of-1 NFT was refused (fail closed — never emit a
/// malformed or unearned mint).
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum NftMintError {
    /// The recipient is the all-zero System program id (or otherwise not a wallet).
    BadRecipient,
    /// The requested supply is not exactly `1` — a 1-of-1 mints one unit.
    NotOneOfOne {
        /// The rejected requested supply.
        requested: u64,
    },
    /// The dregg proof is missing (empty cheevo id or zero commitment) — an
    /// unearned NFT is refused.
    MissingProof,
    /// The custody authority key does not match the expected mint authority — a
    /// derivation / seed mismatch. Refused (never sign for the wrong authority).
    AuthorityMismatch,
    /// The transaction submitter failed.
    Submit(String),
}

impl std::fmt::Display for NftMintError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            NftMintError::BadRecipient => write!(f, "recipient is not a valid wallet"),
            NftMintError::NotOneOfOne { requested } => {
                write!(f, "a 1-of-1 mints exactly 1 unit, not {requested}")
            }
            NftMintError::MissingProof => {
                write!(
                    f,
                    "the dregg proof (earned-ness) is missing — refusing an unearned NFT"
                )
            }
            NftMintError::AuthorityMismatch => {
                write!(f, "custody authority key does not match the mint authority")
            }
            NftMintError::Submit(e) => write!(f, "NFT mint transaction submit failed: {e}"),
        }
    }
}

impl std::error::Error for NftMintError {}

/// A compiled Solana instruction (program index into the message account keys, the
/// account indices it touches, and its data) — enough to ASSERT the built shape.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CompiledInstruction {
    /// Index into [`BuiltNftMint::account_keys`] of the program this invokes.
    pub program_id_index: u8,
    /// Indices into [`BuiltNftMint::account_keys`] of the accounts it touches.
    pub accounts: Vec<u8>,
    /// The instruction data.
    pub data: Vec<u8>,
}

/// A built + signed 1-of-1 NFT-export transaction.
#[derive(Clone, Debug)]
pub struct BuiltNftMint {
    /// The full signed serialized transaction (`compact(sig_count) ‖ signatures ‖
    /// message`) — what the submitter broadcasts.
    pub tx_bytes: Vec<u8>,
    /// The exact bytes the signers signed — the transaction MESSAGE (past the
    /// signature slots). Equals `solana_sign_target(tx_bytes)`.
    pub message: Vec<u8>,
    /// The new NFT mint account pubkey.
    pub mint: [u8; 32],
    /// The recipient wallet (owner of the NFT).
    pub recipient: [u8; 32],
    /// The recipient's canonical associated token account (the off-curve PDA that
    /// receives the single unit).
    pub recipient_ata: [u8; 32],
    /// The custody authority pubkey (fee payer + mint authority) that signed.
    pub authority: [u8; 32],
    /// The dregg proof memo carried in the transaction.
    pub proof_memo: Vec<u8>,
    /// The message's account key table (ordered: writable-signers, readonly-signers,
    /// writable-nonsigners, readonly-nonsigners).
    pub account_keys: Vec<[u8; 32]>,
    /// The compiled instructions (for shape assertions).
    pub instructions: Vec<CompiledInstruction>,
    /// The number of required signatures (message header byte 0).
    pub num_required_signatures: u8,
}

impl BuiltNftMint {
    /// Verify the custody authority actually signed the message: recover the sign
    /// target from `tx_bytes` and check the first signature against `authority`.
    /// This is the same custody proof the sweeper's driven test performs, over the
    /// real transaction message.
    pub fn authority_signature_verifies(&self) -> bool {
        use ed25519_dalek::{Signature, Verifier, VerifyingKey};
        let Ok(target) = solana_sign_target(&self.tx_bytes) else {
            return false;
        };
        if target != self.message {
            return false;
        }
        // The first signature sits right after the compact signature-count prefix.
        // sig_count fits one byte here (2 signers), so the prefix is one byte.
        let sig0 = &self.tx_bytes[1..1 + 64];
        let Ok(vk) = VerifyingKey::from_bytes(&self.authority) else {
            return false;
        };
        let mut sig_bytes = [0u8; 64];
        sig_bytes.copy_from_slice(sig0);
        vk.verify(&target, &Signature::from_bytes(&sig_bytes))
            .is_ok()
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// The on-wire submit seam (mirrors the sweeper's TxSubmitter)
// ─────────────────────────────────────────────────────────────────────────────

/// The transaction-submit seam for the NFT export — the SAME shape as the sweeper's
/// [`TxSubmitter`](crate::sweeper::TxSubmitter). A production impl `sendTransaction`s
/// the already-signed [`BuiltNftMint::tx_bytes`] to a Solana RPC and returns the
/// signature. Tests supply a mock that re-verifies the signature (no network).
pub trait NftTxSubmitter {
    /// Submit the built + signed NFT mint, returning the transaction signature.
    fn submit(&self, built: &BuiltNftMint) -> Result<String, NftMintError>;
}

// ─────────────────────────────────────────────────────────────────────────────
// ATA (associated token account) PDA derivation
// ─────────────────────────────────────────────────────────────────────────────

/// The canonical associated-token-account address for `(wallet, mint)` under the
/// SPL Token program — `find_program_address([wallet, token_program, mint],
/// ata_program)`. A program-derived address is the first candidate that is OFF the
/// ed25519 curve (no private key exists for it); we search bumps `255 → 0`.
pub fn find_associated_token_address(
    wallet: &[u8; 32],
    token_program: &[u8; 32],
    mint: &[u8; 32],
) -> [u8; 32] {
    for bump in (0u8..=255).rev() {
        let mut h = Sha256::new();
        h.update(wallet);
        h.update(token_program);
        h.update(mint);
        h.update([bump]);
        h.update(ATA_PROGRAM_ID);
        h.update(b"ProgramDerivedAddress");
        let candidate: [u8; 32] = h.finalize().into();
        if is_off_curve(&candidate) {
            return candidate;
        }
    }
    // Astronomically unreachable (a PDA exists for all but a negligible fraction of
    // seeds); a valid off-curve address is found within a few bumps in practice.
    unreachable!("no off-curve ATA address found")
}

/// A 32-byte value is a valid PDA iff it is NOT a point on the ed25519 curve (so no
/// secret key maps to it). Decompression failing ⇒ off the curve ⇒ valid PDA.
fn is_off_curve(bytes: &[u8; 32]) -> bool {
    use curve25519_dalek::edwards::CompressedEdwardsY;
    CompressedEdwardsY::from_slice(bytes)
        .map(|c| c.decompress().is_none())
        .unwrap_or(true)
}

// ─────────────────────────────────────────────────────────────────────────────
// Instruction assembly + message compilation
// ─────────────────────────────────────────────────────────────────────────────

/// One account reference in an instruction, with its privilege flags.
#[derive(Clone)]
struct AccountRef {
    pubkey: [u8; 32],
    is_signer: bool,
    is_writable: bool,
}

/// An (uncompiled) instruction: the program, the accounts it references, its data.
struct Instruction {
    program_id: [u8; 32],
    accounts: Vec<AccountRef>,
    data: Vec<u8>,
}

/// Solana `shortvec` (compact-u16) length prefix.
fn encode_shortvec_len(mut len: usize, out: &mut Vec<u8>) {
    loop {
        let mut byte = (len & 0x7f) as u8;
        len >>= 7;
        if len != 0 {
            byte |= 0x80;
        }
        out.push(byte);
        if len == 0 {
            break;
        }
    }
}

/// Compile the fee-payer + instructions into a legacy Solana message, returning the
/// serialized message bytes, the ordered account-key table, the compiled
/// instructions, and the header's `num_required_signatures`. Mirrors
/// `solana_program::message::Message::new_with_blockhash` account ordering.
fn compile_message(
    fee_payer: &[u8; 32],
    instructions: &[Instruction],
    recent_blockhash: &[u8; 32],
) -> (Vec<u8>, Vec<[u8; 32]>, Vec<CompiledInstruction>, u8) {
    // 1. Gather every account reference in encounter order: fee payer first, then per
    //    instruction its accounts, then the program id (readonly non-signer).
    let mut refs: Vec<AccountRef> = vec![AccountRef {
        pubkey: *fee_payer,
        is_signer: true,
        is_writable: true,
    }];
    for ix in instructions {
        for a in &ix.accounts {
            refs.push(a.clone());
        }
        refs.push(AccountRef {
            pubkey: ix.program_id,
            is_signer: false,
            is_writable: false,
        });
    }

    // 2. Dedup by pubkey, ORing privileges, preserving first-occurrence order.
    let mut merged: Vec<AccountRef> = Vec::new();
    for r in refs {
        if let Some(existing) = merged.iter_mut().find(|m| m.pubkey == r.pubkey) {
            existing.is_signer |= r.is_signer;
            existing.is_writable |= r.is_writable;
        } else {
            merged.push(r);
        }
    }

    // 3. Order into the four privilege classes (stable within each).
    let bucket = |signer: bool, writable: bool| -> Vec<AccountRef> {
        merged
            .iter()
            .filter(|m| m.is_signer == signer && m.is_writable == writable)
            .cloned()
            .collect()
    };
    let writable_signers = bucket(true, true);
    let readonly_signers = bucket(true, false);
    let writable_nonsigners = bucket(false, true);
    let readonly_nonsigners = bucket(false, false);

    let num_required_signatures = (writable_signers.len() + readonly_signers.len()) as u8;
    let num_readonly_signed = readonly_signers.len() as u8;
    let num_readonly_unsigned = readonly_nonsigners.len() as u8;

    let mut ordered: Vec<AccountRef> = Vec::new();
    ordered.extend(writable_signers);
    ordered.extend(readonly_signers);
    ordered.extend(writable_nonsigners);
    ordered.extend(readonly_nonsigners);
    let account_keys: Vec<[u8; 32]> = ordered.iter().map(|r| r.pubkey).collect();

    let index_of =
        |key: &[u8; 32]| -> u8 { account_keys.iter().position(|k| k == key).unwrap() as u8 };

    // 4. Compile the instructions to index form.
    let compiled: Vec<CompiledInstruction> = instructions
        .iter()
        .map(|ix| CompiledInstruction {
            program_id_index: index_of(&ix.program_id),
            accounts: ix.accounts.iter().map(|a| index_of(&a.pubkey)).collect(),
            data: ix.data.clone(),
        })
        .collect();

    // 5. Serialize the message.
    let mut msg = Vec::new();
    msg.push(num_required_signatures);
    msg.push(num_readonly_signed);
    msg.push(num_readonly_unsigned);
    encode_shortvec_len(account_keys.len(), &mut msg);
    for k in &account_keys {
        msg.extend_from_slice(k);
    }
    msg.extend_from_slice(recent_blockhash);
    encode_shortvec_len(compiled.len(), &mut msg);
    for ix in &compiled {
        msg.push(ix.program_id_index);
        encode_shortvec_len(ix.accounts.len(), &mut msg);
        msg.extend_from_slice(&ix.accounts);
        encode_shortvec_len(ix.data.len(), &mut msg);
        msg.extend_from_slice(&ix.data);
    }

    (msg, account_keys, compiled, num_required_signatures)
}

// ─────────────────────────────────────────────────────────────────────────────
// The builder — assemble the 1-of-1 NFT-export transaction
// ─────────────────────────────────────────────────────────────────────────────

/// Build (and sign) the 1-of-1 SPL NFT-export transaction with EXPLICIT keys.
///
/// * `authority` — the custody key: fee payer + rent payer + mint authority + freeze
///   authority. This is the HD-derived custody signer (see [`NftMinter`]).
/// * `mint` — the ephemeral new-mint keypair (co-signs `CreateAccount`).
/// * `mint_lamports` — the rent-exempt reserve funded into the mint account.
///
/// Refuses (fail closed) a bad recipient, a supply ≠ 1, or a missing proof BEFORE
/// building anything.
pub fn build_mint_nft(
    request: &MintNftRequest,
    authority: &SigningKey,
    mint: &SigningKey,
    spl_token_program: &[u8; 32],
    mint_lamports: u64,
) -> Result<BuiltNftMint, NftMintError> {
    // ── Fail-closed validation (non-vacuous: the honest mint passes all three). ──
    if request.recipient == SYSTEM_PROGRAM_ID {
        return Err(NftMintError::BadRecipient);
    }
    if request.supply != 1 {
        return Err(NftMintError::NotOneOfOne {
            requested: request.supply,
        });
    }
    if !request.proof.is_present() {
        return Err(NftMintError::MissingProof);
    }

    let authority_pk = authority.verifying_key().to_bytes();
    let mint_pk = mint.verifying_key().to_bytes();
    let ata = find_associated_token_address(&request.recipient, spl_token_program, &mint_pk);
    let memo = request.proof.memo_bytes();

    // ── 1. SystemProgram::CreateAccount (payer funds the new mint account). ──
    let mut create_data = Vec::with_capacity(4 + 8 + 8 + 32);
    create_data.extend_from_slice(&SYS_IX_CREATE_ACCOUNT.to_le_bytes());
    create_data.extend_from_slice(&mint_lamports.to_le_bytes());
    create_data.extend_from_slice(&SPL_MINT_LEN.to_le_bytes());
    create_data.extend_from_slice(spl_token_program); // owner program of the new account
    let create_account = Instruction {
        program_id: SYSTEM_PROGRAM_ID,
        accounts: vec![
            AccountRef {
                pubkey: authority_pk,
                is_signer: true,
                is_writable: true,
            },
            AccountRef {
                pubkey: mint_pk,
                is_signer: true,
                is_writable: true,
            },
        ],
        data: create_data,
    };

    // ── 2. InitializeMint2: decimals=0, mint & freeze authority = custody. ──
    let mut init_data = Vec::with_capacity(1 + 1 + 32 + 1 + 32);
    init_data.push(IX_INITIALIZE_MINT2);
    init_data.push(0u8); // decimals — indivisible
    init_data.extend_from_slice(&authority_pk); // mint authority
    init_data.push(1u8); // COption::Some(freeze authority)
    init_data.extend_from_slice(&authority_pk); // freeze authority
    let init_mint = Instruction {
        program_id: *spl_token_program,
        accounts: vec![AccountRef {
            pubkey: mint_pk,
            is_signer: false,
            is_writable: true,
        }],
        data: init_data,
    };

    // ── 3. AssociatedTokenAccount::Create the recipient's ATA. ──
    let create_ata = Instruction {
        program_id: ATA_PROGRAM_ID,
        accounts: vec![
            AccountRef {
                pubkey: authority_pk,
                is_signer: true,
                is_writable: true,
            }, // funder
            AccountRef {
                pubkey: ata,
                is_signer: false,
                is_writable: true,
            }, // the ATA
            AccountRef {
                pubkey: request.recipient,
                is_signer: false,
                is_writable: false,
            }, // owner
            AccountRef {
                pubkey: mint_pk,
                is_signer: false,
                is_writable: false,
            }, // mint
            AccountRef {
                pubkey: SYSTEM_PROGRAM_ID,
                is_signer: false,
                is_writable: false,
            },
            AccountRef {
                pubkey: *spl_token_program,
                is_signer: false,
                is_writable: false,
            },
        ],
        data: vec![ATA_IX_CREATE],
    };

    // ── 4. MintTo exactly 1 unit to the recipient's ATA. ──
    let mut mint_to_data = Vec::with_capacity(1 + 8);
    mint_to_data.push(IX_MINT_TO);
    mint_to_data.extend_from_slice(&1u64.to_le_bytes()); // supply == 1
    let mint_to = Instruction {
        program_id: *spl_token_program,
        accounts: vec![
            AccountRef {
                pubkey: mint_pk,
                is_signer: false,
                is_writable: true,
            },
            AccountRef {
                pubkey: ata,
                is_signer: false,
                is_writable: true,
            },
            AccountRef {
                pubkey: authority_pk,
                is_signer: true,
                is_writable: false,
            }, // mint authority
        ],
        data: mint_to_data,
    };

    // ── 5. SetAuthority(MintTokens → None): drop mint authority ⇒ TRUE 1-of-1. ──
    let set_authority = Instruction {
        program_id: *spl_token_program,
        accounts: vec![
            AccountRef {
                pubkey: mint_pk,
                is_signer: false,
                is_writable: true,
            },
            AccountRef {
                pubkey: authority_pk,
                is_signer: true,
                is_writable: false,
            }, // current authority
        ],
        // [6, authority_type=MintTokens(0), COption::None(0)]
        data: vec![IX_SET_AUTHORITY, AUTHORITY_TYPE_MINT_TOKENS, 0u8],
    };

    // ── 6. Memo: the dregg proof rides along. ──
    let memo_ix = Instruction {
        program_id: MEMO_PROGRAM_ID,
        accounts: vec![],
        data: memo.clone(),
    };

    let instructions = vec![
        create_account,
        init_mint,
        create_ata,
        mint_to,
        set_authority,
        memo_ix,
    ];

    // ── Compile + sign (custody authority is the fee payer / first signer). ──
    let (message, account_keys, compiled, num_required_signatures) =
        compile_message(&authority_pk, &instructions, &request.recent_blockhash);

    // The signature order matches the signer account order (writable signers first:
    // fee payer, then the mint). Both signers sign the SAME message bytes.
    let mut tx_bytes = Vec::new();
    encode_shortvec_len(num_required_signatures as usize, &mut tx_bytes);
    for key in account_keys.iter().take(num_required_signatures as usize) {
        let sig = if key == &authority_pk {
            authority.sign(&message)
        } else if key == &mint_pk {
            mint.sign(&message)
        } else {
            // No other signer is expected in this instruction set.
            return Err(NftMintError::Submit(
                "unexpected required signer in compiled message".into(),
            ));
        };
        tx_bytes.extend_from_slice(&sig.to_bytes());
    }
    tx_bytes.extend_from_slice(&message);

    Ok(BuiltNftMint {
        tx_bytes,
        message,
        mint: mint_pk,
        recipient: request.recipient,
        recipient_ata: ata,
        authority: authority_pk,
        proof_memo: memo,
        account_keys,
        instructions: compiled,
        num_required_signatures,
    })
}

// ─────────────────────────────────────────────────────────────────────────────
// NftMinter — the HD-custody convenience wrapper
// ─────────────────────────────────────────────────────────────────────────────

/// The domain-separated HD index for the operator's NFT mint AUTHORITY (fee payer +
/// mint authority) — a stable custody key, the SAME `m/44'/501'/index'` space as
/// deposits, domain-separated by a distinct blake3 tag.
fn nft_authority_index() -> u32 {
    let mut h = blake3::Hasher::new();
    h.update(b"dregg-pay/nft-authority-index/v1");
    let d = h.finalize();
    let b = d.as_bytes();
    u32::from_be_bytes([b[0], b[1], b[2], b[3]]) & 0x7fff_ffff
}

/// The domain-separated HD index for the ephemeral per-NFT MINT keypair, keyed by a
/// caller-chosen `nonce` (unique per NFT). Same HD space, distinct blake3 domain.
fn nft_mint_index(nonce: u64) -> u32 {
    let mut h = blake3::Hasher::new();
    h.update(b"dregg-pay/nft-mint-index/v1");
    h.update(&nonce.to_le_bytes());
    let d = h.finalize();
    let b = d.as_bytes();
    u32::from_be_bytes([b[0], b[1], b[2], b[3]]) & 0x7fff_ffff
}

/// The HD-custody NFT minter: derives the mint authority + each ephemeral mint
/// keypair from the operator [`Seed`](crate::config::Seed), builds the 1-of-1 export
/// transaction, signs it, and submits through an injected [`NftTxSubmitter`] — the
/// SAME custody + seam shape as [`SolanaSweeper`](crate::sweeper::SolanaSweeper).
pub struct NftMinter {
    hd: HdDeposit,
    spl_token_program: [u8; 32],
    mint_lamports: u64,
}

impl NftMinter {
    /// Build from a [`PayConfig`] (uses its seed + SPL Token program id).
    pub fn new(config: &PayConfig) -> Self {
        NftMinter {
            hd: HdDeposit::new(config),
            spl_token_program: config.spl_token_program,
            mint_lamports: MINT_RENT_LAMPORTS,
        }
    }

    /// The custody authority (fee payer + mint authority) pubkey.
    pub fn authority_address(&self) -> [u8; 32] {
        self.hd
            .signing_key_at(nft_authority_index())
            .verifying_key()
            .to_bytes()
    }

    /// The mint pubkey that a given `nonce` will produce (deterministic).
    pub fn mint_address(&self, nonce: u64) -> [u8; 32] {
        self.hd
            .signing_key_at(nft_mint_index(nonce))
            .verifying_key()
            .to_bytes()
    }

    /// Build + sign the 1-of-1 NFT-export transaction for `request`, using the mint
    /// keypair derived at `nonce`. Does NOT submit — for offline inspection.
    pub fn build(
        &self,
        request: &MintNftRequest,
        nonce: u64,
    ) -> Result<BuiltNftMint, NftMintError> {
        let authority = self.hd.signing_key_at(nft_authority_index());
        let mint = self.hd.signing_key_at(nft_mint_index(nonce));
        // Custody check: the derived authority IS the mint authority we expect.
        if authority.verifying_key().to_bytes() != self.authority_address() {
            return Err(NftMintError::AuthorityMismatch);
        }
        build_mint_nft(
            request,
            &authority,
            &mint,
            &self.spl_token_program,
            self.mint_lamports,
        )
    }

    /// Build, sign, and SUBMIT the 1-of-1 NFT export through `submitter`, returning
    /// `(BuiltNftMint, tx_signature)`.
    pub fn mint_and_submit<S: NftTxSubmitter>(
        &self,
        request: &MintNftRequest,
        nonce: u64,
        submitter: &S,
    ) -> Result<(BuiltNftMint, String), NftMintError> {
        let built = self.build(request, nonce)?;
        let signature = submitter.submit(&built)?;
        Ok((built, signature))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::config::{DepositAddress, PayConfig, SPL_TOKEN_PROGRAM_ID};
    use ed25519_dalek::{Signature, Verifier, VerifyingKey};

    fn test_config() -> PayConfig {
        let seed = *b"dregg-pay throwaway nft seed 0000000000000";
        let mint = [9u8; 32];
        PayConfig::devnet_mock(seed, mint, DepositAddress([0xEEu8; 32]), 100)
    }

    fn good_proof() -> DreggAchievementProof {
        DreggAchievementProof {
            commitment: [0x7Au8; 32],
            cheevo_id: "descent:first-crown".into(),
        }
    }

    fn good_request(recipient: [u8; 32]) -> MintNftRequest {
        MintNftRequest {
            recipient,
            supply: 1,
            proof: good_proof(),
            recent_blockhash: [0x33u8; 32],
        }
    }

    // A recipient wallet that is a real ed25519 pubkey (not the zero System id).
    fn recipient() -> [u8; 32] {
        SigningKey::from_bytes(&[0x11u8; 32])
            .verifying_key()
            .to_bytes()
    }

    /// The mock submitter: re-verifies the custody signature over the real sign
    /// target (no funds, no network) — the same custody proof the sweeper's mock
    /// submitter performs.
    struct MockNftSubmitter {
        invoked: std::cell::Cell<bool>,
    }
    impl NftTxSubmitter for MockNftSubmitter {
        fn submit(&self, built: &BuiltNftMint) -> Result<String, NftMintError> {
            self.invoked.set(true);
            if !built.authority_signature_verifies() {
                return Err(NftMintError::Submit("authority signature failed".into()));
            }
            Ok(bs58::encode(&built.tx_bytes[1..1 + 64]).into_string())
        }
    }

    #[test]
    fn program_ids_are_canonical() {
        assert_eq!(
            bs58::encode(ATA_PROGRAM_ID).into_string(),
            "ATokenGPvbdGVxr1b2hvZbsiqW5xWH25efTNsLJA8knL"
        );
        assert_eq!(
            bs58::encode(MEMO_PROGRAM_ID).into_string(),
            "MemoSq4gqABAXKb96qnH8TysNcWxMyWCqXgDLGmfcHr"
        );
        assert_eq!(
            bs58::encode(SYSTEM_PROGRAM_ID).into_string(),
            "11111111111111111111111111111111"
        );
    }

    #[test]
    fn ata_is_off_curve_pda() {
        // The derived ATA must itself be off the curve (a real PDA).
        let mint = [0x42u8; 32];
        let ata = find_associated_token_address(&recipient(), &SPL_TOKEN_PROGRAM_ID, &mint);
        assert!(is_off_curve(&ata), "an ATA must be a valid off-curve PDA");
    }

    #[test]
    fn honest_mint_builds_well_formed_one_of_one() {
        let minter = NftMinter::new(&test_config());
        let rcpt = recipient();
        let built = minter.build(&good_request(rcpt), 1).unwrap();

        // 6 instructions in the 1-of-1 order.
        assert_eq!(built.instructions.len(), 6);
        let keys = &built.account_keys;
        let prog = |i: usize| keys[built.instructions[i].program_id_index as usize];

        // (0) CreateAccount for the mint (System program, 82-byte SPL mint, owner =
        //     token program), payer + mint both signers.
        assert_eq!(prog(0), SYSTEM_PROGRAM_ID);
        let ca = &built.instructions[0];
        assert_eq!(&ca.data[0..4], &SYS_IX_CREATE_ACCOUNT.to_le_bytes());
        let space = u64::from_le_bytes(ca.data[12..20].try_into().unwrap());
        assert_eq!(space, SPL_MINT_LEN);
        assert_eq!(&ca.data[20..52], &SPL_TOKEN_PROGRAM_ID); // new account owned by token program

        // (1) InitializeMint2 with decimals == 0 (indivisible).
        assert_eq!(prog(1), SPL_TOKEN_PROGRAM_ID);
        let im = &built.instructions[1];
        assert_eq!(im.data[0], IX_INITIALIZE_MINT2);
        assert_eq!(im.data[1], 0, "a 1-of-1 mint has 0 decimals");
        assert_eq!(&im.data[2..34], &built.authority); // mint authority
        assert_eq!(im.data[34], 1); // freeze authority present

        // (2) Create the recipient's ATA; owner account is the recipient.
        assert_eq!(prog(2), ATA_PROGRAM_ID);
        let cata = &built.instructions[2];
        assert_eq!(cata.data, vec![ATA_IX_CREATE]);
        let ata_idx = cata.accounts[1] as usize;
        let owner_idx = cata.accounts[2] as usize;
        assert_eq!(keys[ata_idx], built.recipient_ata);
        assert_eq!(keys[owner_idx], rcpt, "the recipient is the target owner");

        // (3) MintTo exactly 1 unit, destination == the recipient's ATA.
        assert_eq!(prog(3), SPL_TOKEN_PROGRAM_ID);
        let mt = &built.instructions[3];
        assert_eq!(mt.data[0], IX_MINT_TO);
        let amount = u64::from_le_bytes(mt.data[1..9].try_into().unwrap());
        assert_eq!(amount, 1, "supply-1: a true 1-of-1");
        assert_eq!(keys[mt.accounts[1] as usize], built.recipient_ata);

        // (4) SetAuthority(MintTokens → None): future minting is disabled forever.
        assert_eq!(prog(4), SPL_TOKEN_PROGRAM_ID);
        let sa = &built.instructions[4];
        assert_eq!(
            sa.data,
            vec![IX_SET_AUTHORITY, AUTHORITY_TYPE_MINT_TOKENS, 0u8],
            "mint authority dropped to None — no future mint"
        );

        // (5) The dregg proof memo rides along (valid UTF-8, carries the commitment).
        assert_eq!(prog(5), MEMO_PROGRAM_ID);
        let memo = &built.instructions[5];
        let memo_str = std::str::from_utf8(&memo.data).unwrap();
        assert!(memo_str.starts_with("dregg-nft/v1|descent:first-crown|"));
        assert!(memo_str.contains(&bs58::encode([0x7Au8; 32]).into_string()));
        assert_eq!(memo.data, built.proof_memo);

        // Two signers (custody authority + ephemeral mint), custody first.
        assert_eq!(built.num_required_signatures, 2);
        assert_eq!(keys[0], built.authority);
        assert_eq!(keys[1], built.mint);
    }

    #[test]
    fn signed_by_correct_hd_custody_key() {
        let minter = NftMinter::new(&test_config());
        let built = minter.build(&good_request(recipient()), 7).unwrap();

        // The sign target recovered from the tx equals the message, and BOTH the
        // custody authority and the mint keypair signed it.
        let target = solana_sign_target(&built.tx_bytes).unwrap();
        assert_eq!(target, built.message);
        assert!(built.authority_signature_verifies());

        // The custody authority is exactly the HD-derived authority key.
        assert_eq!(built.authority, minter.authority_address());
        assert_eq!(built.mint, minter.mint_address(7));

        // Verify the mint's signature (2nd slot) too — a full custody proof.
        let sig1 = &built.tx_bytes[1 + 64..1 + 128];
        let mut sb = [0u8; 64];
        sb.copy_from_slice(sig1);
        let mint_vk = VerifyingKey::from_bytes(&built.mint).unwrap();
        assert!(mint_vk.verify(&target, &Signature::from_bytes(&sb)).is_ok());
    }

    #[test]
    fn driven_against_mock_submitter() {
        let minter = NftMinter::new(&test_config());
        let submitter = MockNftSubmitter {
            invoked: std::cell::Cell::new(false),
        };
        let (built, sig) = minter
            .mint_and_submit(&good_request(recipient()), 3, &submitter)
            .unwrap();
        assert!(submitter.invoked.get(), "the submitter was invoked");
        assert!(!sig.is_empty());
        assert_eq!(built.recipient, recipient());
    }

    #[test]
    fn bad_recipient_is_rejected() {
        let minter = NftMinter::new(&test_config());
        let mut req = good_request(recipient());
        req.recipient = SYSTEM_PROGRAM_ID; // the zero id — not a wallet
        assert_eq!(
            minter.build(&req, 1).unwrap_err(),
            NftMintError::BadRecipient
        );
    }

    #[test]
    fn supply_not_one_is_rejected() {
        let minter = NftMinter::new(&test_config());
        for bad in [0u64, 2, 1000] {
            let mut req = good_request(recipient());
            req.supply = bad;
            assert_eq!(
                minter.build(&req, 1).unwrap_err(),
                NftMintError::NotOneOfOne { requested: bad }
            );
        }
    }

    #[test]
    fn missing_proof_is_rejected() {
        let minter = NftMinter::new(&test_config());
        // Empty cheevo id.
        let mut req = good_request(recipient());
        req.proof.cheevo_id = String::new();
        assert_eq!(
            minter.build(&req, 1).unwrap_err(),
            NftMintError::MissingProof
        );
        // Zero commitment.
        let mut req = good_request(recipient());
        req.proof.commitment = [0u8; 32];
        assert_eq!(
            minter.build(&req, 1).unwrap_err(),
            NftMintError::MissingProof
        );
    }
}
