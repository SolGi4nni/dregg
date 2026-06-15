//! Mint / attenuate / verify / refuse cycles for the proven credential core,
//! plus the non-widening refusals (the `attenuate_narrows` discipline made
//! executable) and the wire roundtrip.

use dregg_auth::credential::{
    CREDENTIAL_PREFIX, Caveat, Context, Credential, Pred, PublicKey, Refusal, RootKey, Unbound,
    WireError,
};

fn fp(p: Pred) -> Caveat {
    Caveat::FirstParty(p)
}

fn tool_eq(t: &str) -> Pred {
    Pred::AttrEq {
        key: "tool".into(),
        value: t.into(),
    }
}

#[test]
fn mint_verify_allow() {
    let root = RootKey::from_seed([7u8; 32]);
    let cred = root.mint([fp(tool_eq("read")), fp(Pred::NotAfter { at: 2_000 })]);
    let ctx = Context::new().at(1_000).attr("tool", "read");
    assert_eq!(cred.verify(&root.public(), &ctx), Ok(()));
}

#[test]
fn wrong_attribute_refused_with_terms() {
    let root = RootKey::from_seed([7u8; 32]);
    let cred = root.mint([fp(tool_eq("read"))]);
    let ctx = Context::new().at(1_000).attr("tool", "delete-repo");
    let refusal = cred.verify(&root.public(), &ctx).unwrap_err();
    match &refusal {
        Refusal::CaveatRefused { block, requires } => {
            assert_eq!(*block, 0);
            assert!(requires.contains("`tool` = `read`"), "terms: {requires}");
        }
        other => panic!("expected CaveatRefused, got {other:?}"),
    }
    // The refusal explains itself.
    assert!(refusal.to_string().contains("requires"));
}

#[test]
fn temporal_refusal_after_expiry_and_before_vesting() {
    let root = RootKey::from_seed([1u8; 32]);
    let cred = root.mint([fp(Pred::Within {
        not_before: 100,
        not_after: 200,
    })]);
    let pk = root.public();
    // Inside the window: admitted (withinWindow = meet of after & before).
    assert_eq!(cred.verify(&pk, &Context::new().at(150)), Ok(()));
    // Before vesting and after expiry: refused.
    assert!(matches!(
        cred.verify(&pk, &Context::new().at(50)),
        Err(Refusal::CaveatRefused { .. })
    ));
    assert!(matches!(
        cred.verify(&pk, &Context::new().at(250)),
        Err(Refusal::CaveatRefused { .. })
    ));
}

#[test]
fn missing_clock_is_a_refusal_even_under_not() {
    // Fail-closed: a context with no clock cannot satisfy ANY temporal
    // predicate — and `Not` must not convert that absence into authority.
    let root = RootKey::from_seed([2u8; 32]);
    let cred = root.mint([fp(Pred::Not(Box::new(Pred::NotAfter { at: 100 })))]);
    let refusal = cred.verify(&root.public(), &Context::new()).unwrap_err();
    assert!(matches!(
        refusal,
        Refusal::ContextIncomplete {
            unbound: Unbound::Clock,
            ..
        }
    ));
}

#[test]
fn missing_attribute_is_a_refusal_not_false() {
    let root = RootKey::from_seed([2u8; 32]);
    // Not(tool = read): with `tool` unbound this must refuse, not admit.
    let cred = root.mint([fp(Pred::Not(Box::new(tool_eq("read"))))]);
    let refusal = cred
        .verify(&root.public(), &Context::new().at(1))
        .unwrap_err();
    assert!(matches!(
        refusal,
        Refusal::ContextIncomplete {
            unbound: Unbound::Attr(_),
            ..
        }
    ));
}

#[test]
fn attenuation_narrows_and_parent_still_admits() {
    // attenuate_narrows, executable: anything the child admits, the parent
    // admitted; and there are requests the parent admits that the child
    // refuses.
    let root = RootKey::from_seed([3u8; 32]);
    let parent = root.mint([fp(Pred::AnyOf(vec![tool_eq("read"), tool_eq("pr-create")]))]);
    let pk = root.public();

    let read = Context::new().at(10).attr("tool", "read");
    let pr = Context::new().at(10).attr("tool", "pr-create");
    assert_eq!(parent.verify(&pk, &read), Ok(()));
    assert_eq!(parent.verify(&pk, &pr), Ok(()));

    let child = parent.attenuate([fp(tool_eq("read"))]);
    assert_eq!(child.verify(&pk, &read), Ok(()));
    // The narrowed credential can never regain `pr-create`.
    assert!(matches!(
        child.verify(&pk, &pr),
        Err(Refusal::CaveatRefused { block: 1, .. })
    ));
}

#[test]
fn empty_anyof_refuses_fail_closed() {
    // Pred.evalAny [] = false — the fail-closed disjunction.
    let root = RootKey::from_seed([4u8; 32]);
    let cred = root.mint([fp(Pred::AnyOf(vec![]))]);
    assert!(matches!(
        cred.verify(&root.public(), &Context::new().at(1)),
        Err(Refusal::CaveatRefused { .. })
    ));
    // Pred.evalAll [] = true — the empty meet constrains nothing.
    let cred = root.mint([fp(Pred::AllOf(vec![]))]);
    assert_eq!(cred.verify(&root.public(), &Context::new().at(1)), Ok(()));
}

#[test]
fn trivial_attenuation_is_identity_on_authority() {
    // attenuate_trivial: appending `True` changes the chain, not the verdict.
    let root = RootKey::from_seed([5u8; 32]);
    let cred = root.mint([fp(tool_eq("read"))]);
    let pk = root.public();
    let ctx = Context::new().at(1).attr("tool", "read");
    let attenuated = cred.attenuate([fp(Pred::True)]);
    assert_eq!(attenuated.verify(&pk, &ctx), Ok(()));
}

// ---------------------------------------------------------------------------
// Non-widening: amplification is inexpressible in the API (there is no remove/
// widen method — this is checked by the fact this test file cannot even
// attempt it), and the wire refuses the two ways to forge it.
// ---------------------------------------------------------------------------

#[test]
fn stripping_the_attenuation_block_is_refused() {
    // A recipient of the NARROWED credential tries to widen by re-encoding
    // with the last block dropped. The carried proof key matches the dropped
    // block's key, not the prefix's, so decode refuses — and the recipient
    // never held the prefix's key (that is the possession discipline).
    let root = RootKey::from_seed([6u8; 32]);
    let parent = root.mint([fp(Pred::AnyOf(vec![tool_eq("read"), tool_eq("pr-create")]))]);
    // The parent's chain bytes are visible inside the child's encoding (the
    // blocks are public); capture them before handing the child off.
    let parent_encoded = parent.encode();
    let child = parent.attenuate([fp(tool_eq("read"))]);
    let encoded = child.encode();

    // Splice: decode, then re-encode a credential pretending to be the parent
    // chain. We simulate the attacker by surgically corrupting the wire: the
    // honest API offers no strip, so the attack must go through bytes.
    // Dropping the last block while keeping the only proof key the attacker
    // has (the child's) must be rejected at decode.
    let tampered = {
        // Re-encode the parent's blocks with the CHILD's proof seed: the
        // attacker holds child.proof, not parent.proof.
        // (We rebuild via the public wire form of the parent and the child's
        // seed — i.e. exactly the forgery a byte-splicer would assemble.)
        let parent_bytes = parent_encoded.strip_prefix(CREDENTIAL_PREFIX).unwrap();
        let child_bytes = encoded.strip_prefix(CREDENTIAL_PREFIX).unwrap();
        use base64::Engine;
        let eng = base64::engine::general_purpose::URL_SAFE_NO_PAD;
        let mut p = eng.decode(parent_bytes).unwrap();
        let c = eng.decode(child_bytes).unwrap();
        // postcard layout ends with the 32-byte proof seed: transplant the
        // child's tail seed onto the parent's chain.
        let plen = p.len();
        p[plen - 32..].copy_from_slice(&c[c.len() - 32..]);
        format!("{CREDENTIAL_PREFIX}{}", eng.encode(p))
    };
    let err = Credential::decode(&tampered).unwrap_err();
    assert!(matches!(err, WireError::Malformed(_)), "got {err:?}");
}

#[test]
fn tampered_signature_is_refused() {
    let root = RootKey::from_seed([8u8; 32]);
    let cred = root
        .mint([fp(tool_eq("read"))])
        .attenuate([fp(Pred::NotAfter { at: 99 })]);
    let encoded = cred.encode();
    use base64::Engine;
    let eng = base64::engine::general_purpose::URL_SAFE_NO_PAD;
    let mut bytes = eng
        .decode(encoded.strip_prefix(CREDENTIAL_PREFIX).unwrap())
        .unwrap();
    // Flip a byte in the middle of the chain (a block signature / caveat
    // byte): either the schema breaks or a signature stops verifying. Both
    // are refusals — never a silent wider grant.
    let mid = bytes.len() / 2;
    bytes[mid] ^= 0x40;
    let tampered = format!("{CREDENTIAL_PREFIX}{}", eng.encode(bytes));
    match Credential::decode(&tampered) {
        Err(_) => {} // schema-level refusal
        Ok(c) => {
            let ctx = Context::new().at(1).attr("tool", "read");
            let v = c.verify(&root.public(), &ctx);
            assert!(v.is_err(), "tampered credential must not verify");
        }
    }
}

#[test]
fn wrong_root_key_is_refused() {
    let root = RootKey::from_seed([9u8; 32]);
    let other = RootKey::from_seed([10u8; 32]);
    let cred = root.mint([fp(tool_eq("read"))]);
    let ctx = Context::new().at(1).attr("tool", "read");
    assert!(matches!(
        cred.verify(&other.public(), &ctx),
        Err(Refusal::BadSignature { block: 0 })
    ));
}

// ---------------------------------------------------------------------------
// Wire format.
// ---------------------------------------------------------------------------

#[test]
fn wire_roundtrip_preserves_the_decision() {
    let root = RootKey::from_seed([11u8; 32]);
    let cred = root
        .mint([fp(tool_eq("read")), fp(Pred::NotAfter { at: 500 })])
        .attenuate([fp(Pred::AttrPrefix {
            key: "path".into(),
            prefix: "/docs/".into(),
        })]);
    let encoded = cred.encode();
    assert!(encoded.starts_with(CREDENTIAL_PREFIX));
    // Header-safe: base64url alphabet only after the prefix.
    assert!(
        encoded[CREDENTIAL_PREFIX.len()..]
            .chars()
            .all(|c| c.is_ascii_alphanumeric() || c == '-' || c == '_')
    );

    let decoded = Credential::decode(&encoded).unwrap();
    let pk = root.public();
    let ok = Context::new()
        .at(400)
        .attr("tool", "read")
        .attr("path", "/docs/guide");
    let bad = Context::new()
        .at(400)
        .attr("tool", "read")
        .attr("path", "/secrets");
    assert_eq!(decoded.verify(&pk, &ok), Ok(()));
    assert!(decoded.verify(&pk, &bad).is_err());
    // Tail (the discharge binding target) survives the roundtrip.
    assert_eq!(decoded.tail(), cred.tail());
    // Re-encoding is stable.
    assert_eq!(decoded.encode(), encoded);
}

#[test]
fn unknown_prefix_is_an_error_not_a_fallback() {
    assert!(matches!(
        Credential::decode("dga9_AAAA"),
        Err(WireError::Prefix { .. })
    ));
    assert!(matches!(
        Credential::decode("eb2_AAAA"),
        Err(WireError::Prefix { .. })
    ));
}

#[test]
fn public_key_hex_roundtrip() {
    let root = RootKey::from_seed([12u8; 32]);
    let pk = root.public();
    assert_eq!(PublicKey::from_hex(&pk.to_hex()), Ok(pk));
}

// ---------------------------------------------------------------------------
// Explain.
// ---------------------------------------------------------------------------

#[test]
fn explain_names_every_term_and_the_tail() {
    let root = RootKey::from_seed([13u8; 32]);
    let cred = root
        .mint([
            fp(tool_eq("read")),
            fp(Pred::Within {
                not_before: 100,
                not_after: 200,
            }),
        ])
        .attenuate([fp(Pred::AttrPrefix {
            key: "path".into(),
            prefix: "/docs/".into(),
        })]);
    let explained = cred.explain();
    assert!(explained.contains("block 0 (root grant)"), "{explained}");
    assert!(explained.contains("block 1 (attenuation)"), "{explained}");
    assert!(
        explained.contains("attribute `tool` = `read`"),
        "{explained}"
    );
    assert!(
        explained.contains("within clock window [100, 200]"),
        "{explained}"
    );
    assert!(
        explained.contains("attribute `path` starts with `/docs/`"),
        "{explained}"
    );
    // The faithfulness tag: the full tail hex.
    let tail_hex: String = cred.tail().iter().map(|b| format!("{b:02x}")).collect();
    assert!(
        explained.contains(&format!("[tail {tail_hex}]")),
        "{explained}"
    );
}
