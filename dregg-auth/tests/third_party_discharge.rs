//! Third-party caveats and the discharge protocol: the macaroon binding
//! discipline (`Dregg2.Authority.MacaroonDischarge`) made executable —
//! missing / unbound / bound-elsewhere / forged / expired discharges are all
//! refused, the honest bound discharge admits.

use dregg_auth::credential::{Caveat, Context, Discharge, GatewayKey, Pred, Refusal, RootKey};

fn payments_caveat(gateway: &GatewayKey) -> Caveat {
    Caveat::ThirdParty {
        gateway: gateway.public().0,
        caveat_id: b"payments-approval-42".to_vec(),
        hint: "payments desk approves this spend".into(),
    }
}

#[test]
fn honest_bound_discharge_admits() {
    // MacaroonDischarge.bound_discharge_verifies.
    let root = RootKey::from_seed([21u8; 32]);
    let gateway = GatewayKey::from_seed([22u8; 32]);
    let cred = root.mint([
        Caveat::FirstParty(Pred::NotAfter { at: 1_000 }),
        payments_caveat(&gateway),
    ]);
    let d = gateway.discharge(b"payments-approval-42".to_vec(), cred.tail(), []);
    let ctx = Context::new().at(500).discharge(d);
    assert_eq!(cred.verify(&root.public(), &ctx), Ok(()));
}

#[test]
fn missing_discharge_is_refused() {
    let root = RootKey::from_seed([21u8; 32]);
    let gateway = GatewayKey::from_seed([22u8; 32]);
    let cred = root.mint([payments_caveat(&gateway)]);
    let refusal = cred
        .verify(&root.public(), &Context::new().at(500))
        .unwrap_err();
    assert!(matches!(refusal, Refusal::MissingDischarge { .. }));
    // The refusal names the caveat id and gateway.
    let msg = refusal.to_string();
    assert!(msg.contains("discharge"), "{msg}");
}

#[test]
fn unbound_discharge_is_refused_even_when_otherwise_perfect() {
    // MacaroonDischarge.unbound_discharge_rejected: fail-closed,
    // unconditionally — even with zero conditions. The honest API cannot even
    // construct an unbound discharge (binding is a required argument), so we
    // assemble the hostile wire form by hand.
    let root = RootKey::from_seed([23u8; 32]);
    let gateway = GatewayKey::from_seed([24u8; 32]);
    let cred = root.mint([payments_caveat(&gateway)]);
    let unbound = Discharge::from_parts(
        b"payments-approval-42".to_vec(),
        vec![],
        None,
        [0u8; 64], // binding is checked BEFORE the signature: rejected regardless
    );
    let ctx = Context::new().at(500).discharge(unbound);
    assert!(matches!(
        cred.verify(&root.public(), &ctx),
        Err(Refusal::UnboundDischarge { .. })
    ));
}

#[test]
fn discharge_bound_to_another_credential_is_refused() {
    // MacaroonDischarge.binding_not_replayable_to_other_root: a discharge
    // issued for a heavily-attenuated credential cannot be replayed against a
    // less-attenuated one (or any other).
    let root = RootKey::from_seed([25u8; 32]);
    let gateway = GatewayKey::from_seed([26u8; 32]);

    let narrow = root
        .mint([payments_caveat(&gateway)])
        .attenuate([Caveat::FirstParty(Pred::NotAfter { at: 10 })]);
    let wide = root.mint([payments_caveat(&gateway)]);

    // The gateway discharges the NARROW credential.
    let d = gateway.discharge(b"payments-approval-42".to_vec(), narrow.tail(), []);

    // Replaying that discharge against the WIDE credential is refused.
    let ctx = Context::new().at(500).discharge(d);
    assert!(matches!(
        wide.verify(&root.public(), &ctx),
        Err(Refusal::DischargeBoundElsewhere { .. })
    ));
}

#[test]
fn discharge_signed_by_the_wrong_gateway_is_refused() {
    let root = RootKey::from_seed([27u8; 32]);
    let gateway = GatewayKey::from_seed([28u8; 32]);
    let impostor = GatewayKey::from_seed([29u8; 32]);
    let cred = root.mint([payments_caveat(&gateway)]);
    // Correct id, correct binding — but the impostor's signature.
    let d = impostor.discharge(b"payments-approval-42".to_vec(), cred.tail(), []);
    let ctx = Context::new().at(500).discharge(d);
    assert!(matches!(
        cred.verify(&root.public(), &ctx),
        Err(Refusal::DischargeBadSignature { .. })
    ));
}

#[test]
fn expired_discharge_condition_is_refused() {
    // The gateway's own first-party conditions (the Lean `fp` list) gate the
    // discharge: an approval that expires is an approval that expires.
    let root = RootKey::from_seed([30u8; 32]);
    let gateway = GatewayKey::from_seed([31u8; 32]);
    let cred = root.mint([payments_caveat(&gateway)]);
    let d = gateway.discharge(
        b"payments-approval-42".to_vec(),
        cred.tail(),
        [Pred::NotAfter { at: 600 }],
    );
    let pk = root.public();
    // Inside the approval window: admitted.
    assert_eq!(
        cred.verify(&pk, &Context::new().at(500).discharge(d.clone())),
        Ok(())
    );
    // After it: refused, naming the discharge's violated terms.
    let refusal = cred
        .verify(&pk, &Context::new().at(700).discharge(d))
        .unwrap_err();
    match &refusal {
        Refusal::DischargeCaveatRefused { requires, .. } => {
            assert!(requires.contains("not after clock 600"), "{requires}");
        }
        other => panic!("expected DischargeCaveatRefused, got {other:?}"),
    }
}

#[test]
fn rebinding_after_attenuation_requires_a_fresh_discharge() {
    // The binding commits the WHOLE chain (the tail hashes the final
    // signature, which signs over its parent): attenuating after the
    // discharge was issued changes the tail, so the old discharge no longer
    // binds — the holder must request a fresh one for the credential as
    // actually presented (MacaroonDischarge.rebinding_changes_replay).
    let root = RootKey::from_seed([32u8; 32]);
    let gateway = GatewayKey::from_seed([33u8; 32]);
    let cred = root.mint([payments_caveat(&gateway)]);
    let d = gateway.discharge(b"payments-approval-42".to_vec(), cred.tail(), []);

    let attenuated = cred.attenuate([Caveat::FirstParty(Pred::NotAfter { at: 900 })]);
    let ctx = Context::new().at(500).discharge(d);
    assert!(matches!(
        attenuated.verify(&root.public(), &ctx),
        Err(Refusal::DischargeBoundElsewhere { .. })
    ));

    // Fresh discharge bound to the attenuated tail: admitted.
    let fresh = gateway.discharge(b"payments-approval-42".to_vec(), attenuated.tail(), []);
    let ctx = Context::new().at(500).discharge(fresh);
    assert_eq!(attenuated.verify(&root.public(), &ctx), Ok(()));
}

#[test]
fn discharge_wire_roundtrip() {
    let root = RootKey::from_seed([34u8; 32]);
    let gateway = GatewayKey::from_seed([35u8; 32]);
    let cred = root.mint([payments_caveat(&gateway)]);
    let d = gateway.discharge(
        b"payments-approval-42".to_vec(),
        cred.tail(),
        [Pred::NotAfter { at: 600 }],
    );
    let encoded = d.encode();
    assert!(encoded.starts_with("dgd1_"));
    let decoded = Discharge::decode(&encoded).unwrap();
    assert_eq!(decoded, d);
    let ctx = Context::new().at(500).discharge(decoded);
    assert_eq!(cred.verify(&root.public(), &ctx), Ok(()));
    // The discharge explains itself.
    let explained = d.explain();
    assert!(explained.contains("not after clock 600"), "{explained}");
    assert!(
        explained.contains("bound to credential tail"),
        "{explained}"
    );
}
