use std::cell::Cell;

use dregg_bridge::{
    AdapterError, ChainAttestation, ConditionalAdapterError, ConditionalInterchainAdapter,
    DialAdapter, ExpectedCredit, InterchainAdapter, LockProofTrust, PortableActionBinding,
    TrustRung,
};
use dregg_cell::CellId;

fn binding(recipient: CellId, destination: [u8; 32]) -> PortableActionBinding {
    PortableActionBinding {
        nullifier: [0x11; 32],
        recipient: recipient.0,
        destination_federation: destination,
        amount: 73,
        proof_bytes: vec![],
    }
}

fn expected(recipient: CellId) -> ExpectedCredit {
    ExpectedCredit {
        nullifier: [0x11; 32],
        recipient,
        amount: 73,
    }
}

#[test]
fn conditional_adapter_refuses_recipient_substitution() {
    let bound_recipient = CellId([0x22; 32]);
    let substituted_recipient = CellId([0x44; 32]);
    let attestation = ChainAttestation {
        binding: binding(bound_recipient, [0x33; 32]),
        dial: LockProofTrust::StructureOnly,
    };
    let adapter =
        ConditionalInterchainAdapter::new(DialAdapter::<LockProofTrust>::new(), [0x33; 32]);

    assert!(matches!(
        adapter.into_mint_request(
            &attestation,
            CellId([0xA1; 32]),
            CellId([0xB1; 32]),
            expected(substituted_recipient),
        ),
        Err(ConditionalAdapterError::RecipientMismatch)
    ));
}

#[test]
fn conditional_adapter_refuses_wrong_and_default_destinations() {
    let recipient = CellId([0x22; 32]);
    let attestation = ChainAttestation {
        binding: binding(recipient, [0x55; 32]),
        dial: LockProofTrust::StructureOnly,
    };

    let wrong = ConditionalInterchainAdapter::new(DialAdapter::<LockProofTrust>::new(), [0x33; 32]);
    assert!(matches!(
        wrong.into_mint_request(
            &attestation,
            CellId([0xA1; 32]),
            CellId([0xB1; 32]),
            expected(recipient),
        ),
        Err(ConditionalAdapterError::WrongDestinationFederation { .. })
    ));

    let default_local =
        ConditionalInterchainAdapter::new(DialAdapter::<LockProofTrust>::new(), [0; 32]);
    assert!(matches!(
        default_local.into_mint_request(
            &attestation,
            CellId([0xA1; 32]),
            CellId([0xB1; 32]),
            expected(recipient),
        ),
        Err(ConditionalAdapterError::EmptyLocalFederation)
    ));
}

#[test]
fn conditional_adapter_refuses_event_splicing_and_zero_nullifier() {
    let recipient = CellId([0x22; 32]);
    let adapter =
        ConditionalInterchainAdapter::new(DialAdapter::<LockProofTrust>::new(), [0x33; 32]);
    let attestation = ChainAttestation {
        binding: binding(recipient, [0x33; 32]),
        dial: LockProofTrust::StructureOnly,
    };

    let mut wrong_nullifier = expected(recipient);
    wrong_nullifier.nullifier = [0x12; 32];
    assert!(matches!(
        adapter.into_mint_request(
            &attestation,
            CellId([0xA1; 32]),
            CellId([0xB1; 32]),
            wrong_nullifier,
        ),
        Err(ConditionalAdapterError::NullifierMismatch)
    ));

    let mut wrong_amount = expected(recipient);
    wrong_amount.amount += 1;
    assert!(matches!(
        adapter.into_mint_request(
            &attestation,
            CellId([0xA1; 32]),
            CellId([0xB1; 32]),
            wrong_amount,
        ),
        Err(ConditionalAdapterError::AmountMismatch)
    ));

    let mut empty = attestation;
    empty.binding.nullifier = [0; 32];
    assert!(matches!(
        adapter.into_mint_request(
            &empty,
            CellId([0xA1; 32]),
            CellId([0xB1; 32]),
            ExpectedCredit {
                nullifier: [0; 32],
                recipient,
                amount: 73,
            },
        ),
        Err(ConditionalAdapterError::Adapter(
            AdapterError::EmptyAttestation
        ))
    ));
}

#[test]
fn exact_statement_constructs_only_checked_values() {
    let recipient = CellId([0x22; 32]);
    let attestation = ChainAttestation {
        binding: binding(recipient, [0x33; 32]),
        dial: LockProofTrust::StructureOnly,
    };
    let adapter =
        ConditionalInterchainAdapter::new(DialAdapter::<LockProofTrust>::new(), [0x33; 32]);

    let request = adapter
        .into_mint_request(
            &attestation,
            CellId([0xA1; 32]),
            CellId([0xB1; 32]),
            expected(recipient),
        )
        .expect("all statement fields agree");
    assert_eq!(request.lock_nullifier.0, [0x11; 32]);
    assert_eq!(request.recipient, recipient);
    assert_eq!(request.amount, 73);
    assert_eq!(
        request.consensus_verified,
        TrustRung::Rpc.reached_consensus()
    );
}

#[derive(Debug)]
struct AlternatingAdapter {
    calls: Cell<usize>,
    first: PortableActionBinding,
    second: PortableActionBinding,
}

impl InterchainAdapter for AlternatingAdapter {
    type Attestation = ();

    fn trust_rung(&self, _: &Self::Attestation) -> TrustRung {
        TrustRung::Rpc
    }

    fn to_action_binding(
        &self,
        _: &Self::Attestation,
    ) -> Result<PortableActionBinding, AdapterError> {
        let call = self.calls.get();
        self.calls.set(call + 1);
        Ok(if call == 0 {
            self.first.clone()
        } else {
            self.second.clone()
        })
    }
}

#[test]
fn binding_is_extracted_once_so_check_and_use_share_one_snapshot() {
    let recipient = CellId([0x22; 32]);
    let inner = AlternatingAdapter {
        calls: Cell::new(0),
        first: binding(recipient, [0x33; 32]),
        second: binding(CellId([0x99; 32]), [0x33; 32]),
    };
    let adapter = ConditionalInterchainAdapter::new(inner, [0x33; 32]);

    let request = adapter
        .into_mint_request(
            &(),
            CellId([0xA1; 32]),
            CellId([0xB1; 32]),
            expected(recipient),
        )
        .expect("the first and only snapshot matches");
    assert_eq!(request.recipient, recipient);
    assert_eq!(
        adapter.inner().calls.get(),
        1,
        "binding must be extracted once"
    );
}
