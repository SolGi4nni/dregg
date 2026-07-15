//! Receipt chain verification for proof-carrying state.
//!
//! A receipt chain is a sequence of [`TurnReceipt`]s linked by hash pointers.
//! Each receipt's `previous_receipt_hash` field contains the hash of the prior
//! receipt in the chain. The chain proves that the agent's state evolved through
//! a sequence of valid, executor-checked turns from genesis.
//!
//! This module provides verification functions that check:
//! - Hash continuity: each receipt points to the previous one
//! - State continuity: each receipt's pre_state_hash matches the prior's post_state_hash
//! - Agent consistency: all receipts in a chain belong to the same agent
//! - Genesis validity: the first receipt has `previous_receipt_hash = None`

use dregg_cell::CellId;
use ed25519_dalek;

use crate::turn::TurnReceipt;

/// Errors that can occur during receipt chain verification.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum VerifyError {
    /// The chain is empty (no receipts to verify).
    EmptyChain,

    /// The first receipt in the chain has a non-None previous_receipt_hash.
    /// The genesis receipt must have `previous_receipt_hash = None`.
    GenesisHasPrevious {
        /// The unexpected previous hash found on the genesis receipt.
        previous_hash: [u8; 32],
    },

    /// A receipt's `previous_receipt_hash` does not match the hash of the
    /// preceding receipt in the chain.
    HashChainBreak {
        /// Index of the receipt with the mismatch (1-indexed into the chain).
        index: usize,
        /// The expected hash (computed from the previous receipt).
        expected: [u8; 32],
        /// The actual `previous_receipt_hash` found on this receipt.
        actual: [u8; 32],
    },

    /// A receipt's `pre_state_hash` does not match the prior receipt's `post_state_hash`.
    /// This means there's a gap in the state transitions.
    StateChainBreak {
        /// Index of the receipt with the mismatch (1-indexed into the chain).
        index: usize,
        /// The expected pre_state_hash (from the prior receipt's post_state_hash).
        expected_pre_state: [u8; 32],
        /// The actual pre_state_hash found.
        actual_pre_state: [u8; 32],
    },

    /// A receipt in the chain belongs to a different agent than the first receipt.
    AgentMismatch {
        /// Index of the mismatched receipt.
        index: usize,
        /// The expected agent (from the first receipt).
        expected_agent: CellId,
        /// The actual agent found.
        actual_agent: CellId,
    },

    /// A receipt's executor signature failed verification against all known
    /// executor public keys.
    ExecutorSignatureInvalid {
        /// Index of the receipt with the invalid signature.
        index: usize,
    },

    /// A receipt carries no `executor_signature` at all, under a verifier
    /// that requires one ([`verify_receipt_chain_strict`]).
    ///
    /// **The adversary this stops:** one who takes a valid, executor-signed
    /// chain and simply *deletes* the signatures. Every structural check —
    /// genesis, hash-linking, state continuity, agent consistency — still
    /// passes, because none of them involve the executor. Distinct from
    /// [`Self::ExecutorSignatureInvalid`] on purpose: a forged signature is
    /// an attacker who tried and failed, an absent one is an attacker
    /// exploiting a verifier that treats absence as permission — and for a
    /// caller, "this peer sent junk" and "this chain was never
    /// countersigned" are different events.
    ExecutorSignatureMissing {
        /// Index of the receipt with no signature.
        index: usize,
    },
}

impl core::fmt::Display for VerifyError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            VerifyError::EmptyChain => write!(f, "receipt chain is empty"),
            VerifyError::GenesisHasPrevious { .. } => {
                write!(f, "genesis receipt has a non-None previous_receipt_hash")
            }
            VerifyError::HashChainBreak { index, .. } => {
                write!(f, "hash chain break at receipt index {index}")
            }
            VerifyError::StateChainBreak { index, .. } => {
                write!(f, "state chain break at receipt index {index}")
            }
            VerifyError::AgentMismatch {
                index,
                expected_agent,
                actual_agent,
            } => {
                write!(
                    f,
                    "agent mismatch at receipt index {index}: expected {expected_agent}, got {actual_agent}"
                )
            }
            VerifyError::ExecutorSignatureInvalid { index } => {
                write!(f, "executor signature invalid at receipt index {index}")
            }
            VerifyError::ExecutorSignatureMissing { index } => {
                write!(
                    f,
                    "receipt index {index} carries no executor signature, and this verifier requires one"
                )
            }
        }
    }
}

impl std::error::Error for VerifyError {}

/// Verify a receipt chain for a single agent.
///
/// Checks:
/// 1. The chain is non-empty.
/// 2. The first receipt has `previous_receipt_hash == None` (genesis).
/// 3. Each subsequent receipt's `previous_receipt_hash` matches the BLAKE3 hash
///    of the previous receipt.
/// 4. Each subsequent receipt's `pre_state_hash` matches the prior receipt's
///    `post_state_hash` (state continuity).
/// 5. All receipts in the chain belong to the same agent.
///
/// This function does NOT verify that the turns themselves were valid (that was the
/// executor's job at commit time). It only verifies the chain structure is intact.
pub fn verify_receipt_chain(receipts: &[TurnReceipt]) -> Result<(), VerifyError> {
    if receipts.is_empty() {
        return Err(VerifyError::EmptyChain);
    }

    // Check genesis receipt.
    let genesis = &receipts[0];
    if let Some(prev_hash) = genesis.previous_receipt_hash {
        return Err(VerifyError::GenesisHasPrevious {
            previous_hash: prev_hash,
        });
    }

    let expected_agent = genesis.agent;

    // Walk the chain.
    for i in 1..receipts.len() {
        let prev = &receipts[i - 1];
        let curr = &receipts[i];

        // Check agent consistency.
        if curr.agent != expected_agent {
            return Err(VerifyError::AgentMismatch {
                index: i,
                expected_agent,
                actual_agent: curr.agent,
            });
        }

        // Check hash chain continuity.
        let expected_hash = prev.receipt_hash();
        match curr.previous_receipt_hash {
            Some(actual_hash) if actual_hash == expected_hash => {}
            Some(actual_hash) => {
                return Err(VerifyError::HashChainBreak {
                    index: i,
                    expected: expected_hash,
                    actual: actual_hash,
                });
            }
            None => {
                return Err(VerifyError::HashChainBreak {
                    index: i,
                    expected: expected_hash,
                    actual: [0u8; 32],
                });
            }
        }

        // Check state continuity.
        if curr.pre_state_hash != prev.post_state_hash {
            return Err(VerifyError::StateChainBreak {
                index: i,
                expected_pre_state: prev.post_state_hash,
                actual_pre_state: curr.pre_state_hash,
            });
        }
    }

    Ok(())
}

/// Verify a receipt chain and return the final state commitment.
///
/// On success, returns the `post_state_hash` of the last receipt in the chain.
/// This is the current state commitment that the chain proves.
pub fn verify_receipt_chain_head(receipts: &[TurnReceipt]) -> Result<[u8; 32], VerifyError> {
    verify_receipt_chain(receipts)?;
    Ok(receipts.last().unwrap().post_state_hash)
}

/// Verify that a single receipt correctly extends a chain ending with `previous`.
///
/// This is the "online" check used when appending to a chain: you already trust
/// the chain up to `previous`, and you want to verify `next` links correctly.
pub fn verify_receipt_extends(
    previous: &TurnReceipt,
    next: &TurnReceipt,
) -> Result<(), VerifyError> {
    // Check agent consistency.
    if next.agent != previous.agent {
        return Err(VerifyError::AgentMismatch {
            index: 1,
            expected_agent: previous.agent,
            actual_agent: next.agent,
        });
    }

    // Check hash chain.
    let expected_hash = previous.receipt_hash();
    match next.previous_receipt_hash {
        Some(actual_hash) if actual_hash == expected_hash => {}
        Some(actual_hash) => {
            return Err(VerifyError::HashChainBreak {
                index: 1,
                expected: expected_hash,
                actual: actual_hash,
            });
        }
        None => {
            return Err(VerifyError::HashChainBreak {
                index: 1,
                expected: expected_hash,
                actual: [0u8; 32],
            });
        }
    }

    // Check state continuity.
    if next.pre_state_hash != previous.post_state_hash {
        return Err(VerifyError::StateChainBreak {
            index: 1,
            expected_pre_state: previous.post_state_hash,
            actual_pre_state: next.pre_state_hash,
        });
    }

    Ok(())
}

/// Verify a receipt chain, requiring a valid executor signature on
/// **every** receipt. **This is the strict variant — the one an exit
/// path wants.**
///
/// In addition to the structural checks performed by
/// [`verify_receipt_chain`], every receipt must carry an
/// `executor_signature` that verifies against at least one of
/// `executor_pubkeys`, over the receipt's
/// [`TurnReceipt::canonical_executor_signed_message`].
///
/// The two failure modes are distinguished, because they are different
/// events:
/// - [`VerifyError::ExecutorSignatureMissing`] — the receipt carries no
///   signature at all. An attacker stripping signatures from an
///   otherwise-valid chain produces exactly this, and
///   [`verify_receipt_chain_with_optional_keys`] **accepts** it.
/// - [`VerifyError::ExecutorSignatureInvalid`] — a signature is present
///   but does not verify against any known executor key (forged, wrong
///   signer, wrong length, or the receipt was tampered with after
///   signing).
///
/// Empty `executor_pubkeys` therefore rejects any signed chain (nothing
/// to verify against) and any unsigned one — a caller with no trusted
/// executor keys has nobody to trust, and this says so rather than
/// waving the chain through.
pub fn verify_receipt_chain_strict(
    receipts: &[TurnReceipt],
    executor_pubkeys: &[[u8; 32]],
) -> Result<(), VerifyError> {
    verify_chain_signatures(
        receipts,
        executor_pubkeys,
        /* require_signature */ true,
    )
}

/// Verify a receipt chain, verifying executor signatures **only on the
/// receipts that happen to carry one**.
///
/// ⚠ **This is the lenient variant, and the leniency is the point of the
/// name.** A receipt with no `executor_signature` is not checked and not
/// rejected: strip every signature from a valid chain and this function
/// still returns `Ok(())`. If `executor_pubkeys` is non-empty, that is
/// almost certainly not what you meant — see
/// [`verify_receipt_chain_strict`], which requires a signature on every
/// receipt and names an absent one
/// ([`VerifyError::ExecutorSignatureMissing`]).
///
/// This exists for callers holding a chain whose receipts are
/// legitimately a mix of signed and unsigned (a local, un-finalized
/// chain an executor has not countersigned yet), which want the
/// structural checks of [`verify_receipt_chain`] plus verification of
/// whatever signatures ARE present. Any caller deciding whether to
/// **trust** a chain from a third party wants the strict one; leniency
/// here means an unsigned receipt is indistinguishable from a signed
/// one.
pub fn verify_receipt_chain_with_optional_keys(
    receipts: &[TurnReceipt],
    executor_pubkeys: &[[u8; 32]],
) -> Result<(), VerifyError> {
    verify_chain_signatures(
        receipts,
        executor_pubkeys,
        /* require_signature */ false,
    )
}

/// Shared body of [`verify_receipt_chain_strict`] and
/// [`verify_receipt_chain_with_optional_keys`] — structural checks, then
/// per-receipt signature verification. `require_signature` is the ONLY
/// difference between the two, so the strict variant cannot drift from
/// the lenient one's signature-checking.
fn verify_chain_signatures(
    receipts: &[TurnReceipt],
    executor_pubkeys: &[[u8; 32]],
    require_signature: bool,
) -> Result<(), VerifyError> {
    // First, verify structural integrity.
    verify_receipt_chain(receipts)?;

    // Then verify executor signatures.
    for (i, receipt) in receipts.iter().enumerate() {
        let Some(ref sig_bytes) = receipt.executor_signature else {
            if require_signature {
                return Err(VerifyError::ExecutorSignatureMissing { index: i });
            }
            continue;
        };
        if sig_bytes.len() != 64 {
            return Err(VerifyError::ExecutorSignatureInvalid { index: i });
        }
        let sig_array: [u8; 64] = sig_bytes[..64].try_into().unwrap();
        // The executor signs the v3 canonical message: a domain string over the FULL
        // `receipt_hash()` (see `TurnReceipt::canonical_executor_signed_message`).
        // Verifiers reproduce that message here.
        let msg = receipt.canonical_executor_signed_message();
        let signature = ed25519_dalek::Signature::from_bytes(&sig_array);

        let mut verified = false;
        for pubkey_bytes in executor_pubkeys {
            if let Ok(vk) = ed25519_dalek::VerifyingKey::from_bytes(pubkey_bytes) {
                if vk.verify_strict(&msg, &signature).is_ok() {
                    verified = true;
                    break;
                }
            }
        }

        if !verified {
            return Err(VerifyError::ExecutorSignatureInvalid { index: i });
        }
    }

    Ok(())
}

/// Verify a receipt's Ed25519 executor signature IN ISOLATION.
///
/// Unlike [`verify_receipt_chain_with_optional_keys`], this performs NO genesis /
/// `previous_receipt_hash` / hash-chain / state-continuity checks. It answers
/// exactly one question: does this receipt carry a genuine executor signature
/// over its canonical executor-signed message that verifies against one of
/// `executor_pubkeys`?
///
/// This is the primitive a point-verifier (e.g. the forge's required-check
/// gate) needs when the receipt is NOT the genesis of a chain — a check turn
/// that is the second (or later) edit on its document carries
/// `previous_receipt_hash = Some(..)`, which [`verify_receipt_chain_with_optional_keys`]
/// (treating element [0] as a chain genesis) hard-rejects. Here we ignore the
/// chain position entirely and only bind the executor's authorship.
///
/// A receipt with no `executor_signature` is rejected with
/// [`VerifyError::ExecutorSignatureInvalid`] (an absent signature is not a
/// pass): callers wanting to distinguish "unsigned" from "wrong signer" should
/// pre-check `receipt.executor_signature.is_none()` themselves.
///
/// The signature is checked over [`TurnReceipt::canonical_executor_signed_message`]
/// — the exact message the executor produces (Stage 9 R-4) and the exact bytes
/// [`verify_receipt_chain_with_optional_keys`] checks; this reproduces that check WITHOUT
/// the chain constraints.
pub fn verify_receipt_signature_with_keys(
    receipt: &TurnReceipt,
    executor_pubkeys: &[[u8; 32]],
) -> Result<(), VerifyError> {
    let Some(ref sig_bytes) = receipt.executor_signature else {
        return Err(VerifyError::ExecutorSignatureInvalid { index: 0 });
    };
    if sig_bytes.len() != 64 {
        return Err(VerifyError::ExecutorSignatureInvalid { index: 0 });
    }
    let sig_array: [u8; 64] = sig_bytes[..64].try_into().unwrap();
    // The executor signs the v3 canonical message: a domain string over the FULL
    // `receipt_hash()` (see `TurnReceipt::canonical_executor_signed_message`).
    // Verifiers reproduce that message here.
    let msg = receipt.canonical_executor_signed_message();
    let signature = ed25519_dalek::Signature::from_bytes(&sig_array);

    for pubkey_bytes in executor_pubkeys {
        if let Ok(vk) = ed25519_dalek::VerifyingKey::from_bytes(pubkey_bytes) {
            if vk.verify_strict(&msg, &signature).is_ok() {
                return Ok(());
            }
        }
    }

    Err(VerifyError::ExecutorSignatureInvalid { index: 0 })
}

/// Sign a receipt with the given Ed25519 signing key.
/// Returns the 64-byte signature over
/// [`TurnReceipt::canonical_executor_signed_message`] (Stage 9 R-4).
pub fn sign_receipt(receipt: &TurnReceipt, signing_key: &[u8; 32]) -> Vec<u8> {
    use ed25519_dalek::Signer;
    let sk = ed25519_dalek::SigningKey::from_bytes(signing_key);
    let msg = receipt.canonical_executor_signed_message();
    let sig = sk.sign(&msg);
    sig.to_bytes().to_vec()
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Helper: create a test receipt with specific state hashes and chain link.
    fn make_receipt(
        agent: CellId,
        pre_state: [u8; 32],
        post_state: [u8; 32],
        previous_receipt_hash: Option<[u8; 32]>,
    ) -> TurnReceipt {
        TurnReceipt {
            turn_hash: [0u8; 32],
            forest_hash: [0u8; 32],
            pre_state_hash: pre_state,
            post_state_hash: post_state,
            timestamp: 1000,
            effects_hash: [0u8; 32],
            computrons_used: 100,
            action_count: 1,
            previous_receipt_hash,
            agent,
            federation_id: [0u8; 32],
            routing_directives: Vec::new(),
            introduction_exports: Vec::new(),
            derivation_records: vec![],
            emitted_events: vec![],
            executor_signature: None,
            finality: Default::default(),
            was_encrypted: false,
            was_burn: false,
            consumed_capabilities: vec![],
        }
    }

    /// Build a valid chain of N receipts for a given agent.
    fn build_valid_chain(agent: CellId, n: usize) -> Vec<TurnReceipt> {
        let mut chain: Vec<TurnReceipt> = Vec::with_capacity(n);
        let mut state = [1u8; 32];

        for i in 0..n {
            let pre_state = state;
            // Advance state deterministically.
            state[0] = (i + 2) as u8;
            let post_state = state;

            let previous_receipt_hash = if i == 0 {
                None
            } else {
                Some(chain[i - 1].receipt_hash())
            };

            chain.push(make_receipt(
                agent,
                pre_state,
                post_state,
                previous_receipt_hash,
            ));
        }

        chain
    }

    #[test]
    fn test_verify_empty_chain() {
        let result = verify_receipt_chain(&[]);
        assert_eq!(result.unwrap_err(), VerifyError::EmptyChain);
    }

    #[test]
    fn test_verify_single_receipt_genesis() {
        let agent = CellId::from_bytes([1u8; 32]);
        let receipt = make_receipt(agent, [1u8; 32], [2u8; 32], None);
        assert!(verify_receipt_chain(&[receipt]).is_ok());
    }

    #[test]
    fn test_verify_single_receipt_non_genesis_fails() {
        let agent = CellId::from_bytes([1u8; 32]);
        let receipt = make_receipt(agent, [1u8; 32], [2u8; 32], Some([99u8; 32]));
        let err = verify_receipt_chain(&[receipt]).unwrap_err();
        assert!(matches!(err, VerifyError::GenesisHasPrevious { .. }));
    }

    #[test]
    fn test_verify_valid_chain_of_three() {
        let agent = CellId::from_bytes([1u8; 32]);
        let chain = build_valid_chain(agent, 3);
        assert!(verify_receipt_chain(&chain).is_ok());
    }

    #[test]
    fn test_verify_valid_chain_of_ten() {
        let agent = CellId::from_bytes([1u8; 32]);
        let chain = build_valid_chain(agent, 10);
        assert!(verify_receipt_chain(&chain).is_ok());
    }

    #[test]
    fn test_verify_hash_chain_break() {
        let agent = CellId::from_bytes([1u8; 32]);
        let mut chain = build_valid_chain(agent, 3);

        // Corrupt the second receipt's previous_receipt_hash.
        chain[1].previous_receipt_hash = Some([0xDE; 32]);

        let err = verify_receipt_chain(&chain).unwrap_err();
        match err {
            VerifyError::HashChainBreak { index, .. } => assert_eq!(index, 1),
            other => panic!("expected HashChainBreak, got {other:?}"),
        }
    }

    #[test]
    fn test_verify_state_chain_break() {
        let agent = CellId::from_bytes([1u8; 32]);
        let mut chain = build_valid_chain(agent, 3);

        // Corrupt the third receipt's pre_state_hash so it doesn't match
        // the second receipt's post_state_hash.
        chain[2].pre_state_hash = [0xFF; 32];
        // Fix the hash chain link to still be valid.
        chain[2].previous_receipt_hash = Some(chain[1].receipt_hash());

        let err = verify_receipt_chain(&chain).unwrap_err();
        match err {
            VerifyError::StateChainBreak { index, .. } => assert_eq!(index, 2),
            other => panic!("expected StateChainBreak, got {other:?}"),
        }
    }

    #[test]
    fn test_verify_agent_mismatch() {
        let agent1 = CellId::from_bytes([1u8; 32]);
        let agent2 = CellId::from_bytes([2u8; 32]);
        let mut chain = build_valid_chain(agent1, 3);

        // Change the agent on the second receipt.
        chain[1].agent = agent2;

        let err = verify_receipt_chain(&chain).unwrap_err();
        match err {
            VerifyError::AgentMismatch {
                index,
                expected_agent,
                actual_agent,
            } => {
                assert_eq!(index, 1);
                assert_eq!(expected_agent, agent1);
                assert_eq!(actual_agent, agent2);
            }
            other => panic!("expected AgentMismatch, got {other:?}"),
        }
    }

    #[test]
    fn test_verify_receipt_chain_head() {
        let agent = CellId::from_bytes([1u8; 32]);
        let chain = build_valid_chain(agent, 5);
        let expected_head = chain.last().unwrap().post_state_hash;
        let result = verify_receipt_chain_head(&chain).unwrap();
        assert_eq!(result, expected_head);
    }

    #[test]
    fn test_verify_receipt_extends_valid() {
        let agent = CellId::from_bytes([1u8; 32]);
        let chain = build_valid_chain(agent, 2);
        assert!(verify_receipt_extends(&chain[0], &chain[1]).is_ok());
    }

    #[test]
    fn test_verify_receipt_extends_wrong_hash() {
        let agent = CellId::from_bytes([1u8; 32]);
        let chain = build_valid_chain(agent, 2);
        let mut bad_next = chain[1].clone();
        bad_next.previous_receipt_hash = Some([0xAA; 32]);
        let err = verify_receipt_extends(&chain[0], &bad_next).unwrap_err();
        assert!(matches!(err, VerifyError::HashChainBreak { .. }));
    }

    #[test]
    fn test_verify_receipt_extends_wrong_agent() {
        let agent1 = CellId::from_bytes([1u8; 32]);
        let agent2 = CellId::from_bytes([2u8; 32]);
        let chain = build_valid_chain(agent1, 2);
        let mut bad_next = chain[1].clone();
        bad_next.agent = agent2;
        let err = verify_receipt_extends(&chain[0], &bad_next).unwrap_err();
        assert!(matches!(err, VerifyError::AgentMismatch { .. }));
    }

    #[test]
    fn test_verify_receipt_extends_wrong_pre_state() {
        let agent = CellId::from_bytes([1u8; 32]);
        let chain = build_valid_chain(agent, 2);
        let mut bad_next = chain[1].clone();
        bad_next.pre_state_hash = [0xCC; 32];
        // Fix the hash link.
        bad_next.previous_receipt_hash = Some(chain[0].receipt_hash());
        let err = verify_receipt_extends(&chain[0], &bad_next).unwrap_err();
        assert!(matches!(err, VerifyError::StateChainBreak { .. }));
    }

    #[test]
    fn test_receipt_hash_determinism() {
        let agent = CellId::from_bytes([1u8; 32]);
        let r1 = make_receipt(agent, [1u8; 32], [2u8; 32], None);
        let r2 = make_receipt(agent, [1u8; 32], [2u8; 32], None);
        assert_eq!(r1.receipt_hash(), r2.receipt_hash());
    }

    /// The executor's signature round-trips through the v3 canonical message
    /// (domain || full `receipt_hash()`) and is rejected under a foreign key.
    #[test]
    fn test_executor_signature_roundtrip_canonical_message() {
        let agent = CellId::from_bytes([1u8; 32]);
        let mut receipt = make_receipt(agent, [1u8; 32], [2u8; 32], None);
        receipt.timestamp = 0xBEEF;
        receipt.turn_hash = [0xAB; 32];

        let signing_seed = [0x42u8; 32];
        let sig_bytes = sign_receipt(&receipt, &signing_seed);
        assert_eq!(sig_bytes.len(), 64);
        receipt.executor_signature = Some(sig_bytes);

        let sk = ed25519_dalek::SigningKey::from_bytes(&signing_seed);
        let pk = sk.verifying_key().to_bytes();

        // Verifies under the correct key.
        verify_receipt_chain_with_optional_keys(&[receipt.clone()], &[pk])
            .expect("canonical-message signature must verify under correct key");

        // Rejected under a foreign key.
        let bogus = [0x99u8; 32];
        let err = verify_receipt_chain_with_optional_keys(&[receipt.clone()], &[bogus])
            .expect_err("foreign key must not verify");
        assert!(matches!(err, VerifyError::ExecutorSignatureInvalid { .. }));

        // If the receipt body fields the canonical message commits to are
        // mutated (e.g. post_state_hash), the signature stops verifying.
        let mut tampered = receipt.clone();
        tampered.post_state_hash = [0xFF; 32];
        let err = verify_receipt_chain_with_optional_keys(&[tampered], &[pk])
            .expect_err("tampered post_state_hash must invalidate executor signature");
        assert!(matches!(err, VerifyError::ExecutorSignatureInvalid { .. }));
    }

    /// Build a valid chain of `n` receipts, every one executor-signed under
    /// `seed`. Returns the chain and the executor's public key.
    fn build_signed_chain(agent: CellId, n: usize, seed: [u8; 32]) -> (Vec<TurnReceipt>, [u8; 32]) {
        let mut chain: Vec<TurnReceipt> = Vec::with_capacity(n);
        let mut state = [1u8; 32];

        for i in 0..n {
            let pre_state = state;
            state[0] = (i + 2) as u8;
            let post_state = state;

            let previous_receipt_hash = if i == 0 {
                None
            } else {
                // Sign BEFORE hashing the predecessor: the signature is part
                // of the receipt, so the link must be taken over the signed
                // form or the chain will not verify structurally.
                Some(chain[i - 1].receipt_hash())
            };

            let mut r = make_receipt(agent, pre_state, post_state, previous_receipt_hash);
            r.timestamp = 1000 + i as i64;
            r.turn_hash = [i as u8; 32];
            r.executor_signature = Some(sign_receipt(&r, &seed));
            chain.push(r);
        }

        let pk = ed25519_dalek::SigningKey::from_bytes(&seed)
            .verifying_key()
            .to_bytes();
        (chain, pk)
    }

    /// **The signature-strip forgery.** Take a valid, fully executor-signed
    /// chain and delete one signature. Every structural check still passes —
    /// genesis, hash-linking, state continuity, agent consistency all hold,
    /// because none of them involve the executor at all. Only a verifier that
    /// requires the signature can tell.
    ///
    /// This is the exact hole `verify_receipt_chain_with_keys` had: named as
    /// though it checked keys, it checked signatures only on the receipts that
    /// had them, so the strip was free.
    #[test]
    fn strict_rejects_a_stripped_signature_that_lenient_accepts() {
        let agent = CellId::from_bytes([1u8; 32]);
        let (chain, pk) = build_signed_chain(agent, 3, [0x42u8; 32]);

        // ── HONEST POLE FIRST. The unmodified chain must verify under BOTH
        // verifiers. Without this the reject below would be indistinguishable
        // from a strict verifier that rejects everything — the canary would be
        // vacuous.
        verify_receipt_chain_strict(&chain, &[pk])
            .expect("honest pole: a fully-signed valid chain must verify STRICT");
        verify_receipt_chain_with_optional_keys(&chain, &[pk])
            .expect("honest pole: a fully-signed valid chain must verify LENIENT");

        // ── THE FORGERY: strip the executor signature off the middle receipt.
        // Nothing else is touched, so the hash links are still exact (the
        // successor's previous_receipt_hash was computed over the signed form —
        // which is what makes this interesting: `receipt_hash` covering the
        // signature would have broken the chain and caught this for free).
        let mut forged = chain.clone();
        forged[1].executor_signature = None;

        // Strict names the adversary at the exact index.
        let err = verify_receipt_chain_strict(&forged, &[pk])
            .expect_err("strict must REJECT a chain with a stripped signature");
        assert!(
            matches!(err, VerifyError::ExecutorSignatureMissing { index: 1 }),
            "strict must reject with ExecutorSignatureMissing at the stripped index, got {err:?}"
        );

        // …and the structural verifier is blind to it, which is WHY strict has
        // to exist: the strip is invisible to every check that is not the
        // signature check.
        verify_receipt_chain(&forged)
            .expect("the strip is structurally invisible — this is the point");

        // The lenient verifier ACCEPTS it. This is its documented behaviour,
        // pinned here so the name and the semantics cannot drift apart again:
        // if someone makes this one strict, this assertion reds and they must
        // come rename it.
        verify_receipt_chain_with_optional_keys(&forged, &[pk]).expect(
            "verify_receipt_chain_with_optional_keys is DOCUMENTED lenient: an absent \
             signature is not checked. If this now rejects, the function is strict and \
             its name must say so.",
        );

        // ── Strip them ALL — the fully-unsigned chain, which is what an
        // attacker who fabricates receipts from nothing produces.
        let mut all_stripped = chain.clone();
        for r in &mut all_stripped {
            r.executor_signature = None;
        }
        let err = verify_receipt_chain_strict(&all_stripped, &[pk])
            .expect_err("strict must reject a wholly unsigned chain");
        assert!(
            matches!(err, VerifyError::ExecutorSignatureMissing { index: 0 }),
            "expected ExecutorSignatureMissing at index 0, got {err:?}"
        );
        verify_receipt_chain_with_optional_keys(&all_stripped, &[pk])
            .expect("lenient accepts a wholly unsigned chain — the fail-open, pinned");
    }

    /// Strict distinguishes its two rejects: an ABSENT signature is
    /// `ExecutorSignatureMissing`, a PRESENT-but-bad one is
    /// `ExecutorSignatureInvalid`. A consumer separating "never countersigned"
    /// from "this peer sent junk" needs the distinction, and an undiscriminating
    /// `Err(_)` would not have it.
    #[test]
    fn strict_distinguishes_missing_from_invalid() {
        let agent = CellId::from_bytes([1u8; 32]);
        let (chain, pk) = build_signed_chain(agent, 2, [0x42u8; 32]);

        // Honest pole first.
        verify_receipt_chain_strict(&chain, &[pk])
            .expect("honest pole: the signed chain verifies strict");

        // A forged signature — present, well-formed length, wrong signer.
        let mut wrong_signer = chain.clone();
        let other_seed = [0x99u8; 32];
        wrong_signer[1].executor_signature = Some(sign_receipt(&wrong_signer[1], &other_seed));
        let err = verify_receipt_chain_strict(&wrong_signer, &[pk])
            .expect_err("a signature from an unknown executor must not verify");
        assert!(
            matches!(err, VerifyError::ExecutorSignatureInvalid { index: 1 }),
            "a wrong-signer signature is Invalid, not Missing, got {err:?}"
        );

        // An absent signature on the very same receipt.
        let mut stripped = chain.clone();
        stripped[1].executor_signature = None;
        let err = verify_receipt_chain_strict(&stripped, &[pk]).expect_err("absent must reject");
        assert!(
            matches!(err, VerifyError::ExecutorSignatureMissing { index: 1 }),
            "an absent signature is Missing, not Invalid, got {err:?}"
        );
    }

    /// A caller with no trusted executor keys trusts nobody, and strict says so
    /// rather than waving the chain through on "no signatures to check".
    #[test]
    fn strict_with_no_trusted_keys_rejects_a_validly_signed_chain() {
        let agent = CellId::from_bytes([1u8; 32]);
        let (chain, pk) = build_signed_chain(agent, 2, [0x42u8; 32]);

        // Honest pole first: with the key, it verifies.
        verify_receipt_chain_strict(&chain, &[pk])
            .expect("honest pole: verifies against the real executor key");

        // Without it, the signature verifies against nothing.
        let err = verify_receipt_chain_strict(&chain, &[])
            .expect_err("no trusted keys ⇒ nothing to verify against ⇒ reject");
        assert!(
            matches!(err, VerifyError::ExecutorSignatureInvalid { index: 0 }),
            "expected ExecutorSignatureInvalid, got {err:?}"
        );
    }

    /// FIX #2: `verify_receipt_signature_with_keys` verifies a correctly-signed
    /// receipt IN ISOLATION — crucially, one whose `previous_receipt_hash` is
    /// `Some(..)` (a NON-genesis receipt, e.g. a reviewer's approval posted
    /// after a comment). `verify_receipt_chain_with_optional_keys` rejects that as
    /// `GenesisHasPrevious`; the isolated signature check must NOT.
    #[test]
    fn test_verify_receipt_signature_non_genesis_isolated() {
        let agent = CellId::from_bytes([1u8; 32]);
        // A receipt that is NOT the first on its chain: previous_receipt_hash is Some.
        let mut receipt = make_receipt(agent, [1u8; 32], [2u8; 32], Some([7u8; 32]));
        receipt.timestamp = 0xC0FFEE;
        receipt.turn_hash = [0xAB; 32];

        let signing_seed = [0x42u8; 32];
        receipt.executor_signature = Some(sign_receipt(&receipt, &signing_seed));
        let pk = ed25519_dalek::SigningKey::from_bytes(&signing_seed)
            .verifying_key()
            .to_bytes();

        // The isolated signature check ACCEPTS the non-genesis receipt.
        verify_receipt_signature_with_keys(&receipt, &[pk])
            .expect("a correctly-signed non-genesis receipt verifies in isolation");

        // The chain check would (wrongly, for a point verifier) reject it as
        // GenesisHasPrevious — the exact false negative FIX #2 removes.
        let chain_err =
            verify_receipt_chain_with_optional_keys(&[receipt.clone()], &[pk]).unwrap_err();
        assert!(matches!(chain_err, VerifyError::GenesisHasPrevious { .. }));
    }

    /// The isolated check's negatives: wrong key, tampered body, unsigned.
    #[test]
    fn test_verify_receipt_signature_negatives() {
        let agent = CellId::from_bytes([1u8; 32]);
        let mut receipt = make_receipt(agent, [1u8; 32], [2u8; 32], Some([7u8; 32]));
        receipt.turn_hash = [0xAB; 32];
        let signing_seed = [0x42u8; 32];
        receipt.executor_signature = Some(sign_receipt(&receipt, &signing_seed));
        let pk = ed25519_dalek::SigningKey::from_bytes(&signing_seed)
            .verifying_key()
            .to_bytes();

        // Untrusted key → refused.
        assert!(matches!(
            verify_receipt_signature_with_keys(&receipt, &[[0x99u8; 32]]).unwrap_err(),
            VerifyError::ExecutorSignatureInvalid { .. }
        ));
        // Empty key set → refused.
        assert!(matches!(
            verify_receipt_signature_with_keys(&receipt, &[]).unwrap_err(),
            VerifyError::ExecutorSignatureInvalid { .. }
        ));
        // Tampered signed field → signature no longer verifies.
        let mut tampered = receipt.clone();
        tampered.post_state_hash = [0xFF; 32];
        assert!(matches!(
            verify_receipt_signature_with_keys(&tampered, &[pk]).unwrap_err(),
            VerifyError::ExecutorSignatureInvalid { .. }
        ));
        // Unsigned → refused (absent signature is not a pass).
        let mut unsigned = receipt.clone();
        unsigned.executor_signature = None;
        assert!(matches!(
            verify_receipt_signature_with_keys(&unsigned, &[pk]).unwrap_err(),
            VerifyError::ExecutorSignatureInvalid { .. }
        ));
    }

    #[test]
    fn test_receipt_hash_includes_previous() {
        let agent = CellId::from_bytes([1u8; 32]);
        let r_none = make_receipt(agent, [1u8; 32], [2u8; 32], None);
        let r_some = make_receipt(agent, [1u8; 32], [2u8; 32], Some([3u8; 32]));
        // Different previous_receipt_hash should produce different receipt hashes.
        assert_ne!(r_none.receipt_hash(), r_some.receipt_hash());
    }
}
