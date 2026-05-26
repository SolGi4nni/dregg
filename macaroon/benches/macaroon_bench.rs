use criterion::{Criterion, black_box, criterion_group, criterion_main};
use dregg_macaroon::{CaveatSet, Macaroon, ThirdPartyCaveat, create_discharge, crypto};

fn bench_create(c: &mut Criterion) {
    let root_key = crypto::random_key();
    c.bench_function("macaroon_create", |b| {
        b.iter(|| {
            black_box(Macaroon::new(
                &root_key,
                b"kid-1".to_vec(),
                "https://dregg.dev".into(),
            ));
        });
    });
}

fn bench_verify_no_caveats(c: &mut Criterion) {
    let root_key = crypto::random_key();
    let mac = Macaroon::new(&root_key, b"kid-1".to_vec(), "https://dregg.dev".into());
    c.bench_function("macaroon_verify_0_caveats", |b| {
        b.iter(|| {
            black_box(mac.verify(&root_key, &[]).unwrap());
        });
    });
}

fn bench_verify_with_caveats(c: &mut Criterion) {
    let root_key = crypto::random_key();
    let mut mac = Macaroon::new(&root_key, b"kid-1".to_vec(), "https://dregg.dev".into());
    for i in 0..5 {
        mac.add_first_party_wire(dregg_macaroon::WireCaveat {
            caveat_type: 1,
            body: vec![i as u8],
        });
    }
    c.bench_function("macaroon_verify_5_caveats", |b| {
        b.iter(|| {
            black_box(mac.verify(&root_key, &[]).unwrap());
        });
    });
}

fn bench_serialize_deserialize(c: &mut Criterion) {
    let root_key = crypto::random_key();
    let mut mac = Macaroon::new(&root_key, b"kid-1".to_vec(), "https://dregg.dev".into());
    mac.add_first_party_wire(dregg_macaroon::WireCaveat {
        caveat_type: 1,
        body: vec![0x42],
    });
    let serialized = mac.serialize().unwrap();

    c.bench_function("macaroon_serialize", |b| {
        b.iter(|| {
            black_box(mac.serialize().unwrap());
        });
    });

    c.bench_function("macaroon_deserialize", |b| {
        b.iter(|| {
            black_box(Macaroon::deserialize(&serialized).unwrap());
        });
    });
}

fn bench_encode_decode(c: &mut Criterion) {
    let root_key = crypto::random_key();
    let mac = Macaroon::new(&root_key, b"kid-1".to_vec(), "https://dregg.dev".into());
    let encoded = mac.encode().unwrap();

    c.bench_function("macaroon_encode", |b| {
        b.iter(|| {
            black_box(mac.encode().unwrap());
        });
    });

    c.bench_function("macaroon_decode", |b| {
        b.iter(|| {
            black_box(Macaroon::decode(&encoded).unwrap());
        });
    });
}

fn bench_third_party_flow(c: &mut Criterion) {
    let root_key = crypto::random_key();
    let shared_key = crypto::random_key();

    c.bench_function("macaroon_3p_full_flow", |b| {
        b.iter(|| {
            let mut mac = Macaroon::new(&root_key, b"kid-1".to_vec(), "https://dregg.dev".into());
            mac.add_third_party("https://auth.dregg.dev", &shared_key, CaveatSet::new())
                .unwrap();

            let tp_caveats = mac.caveats.third_party_caveats();
            let tp = ThirdPartyCaveat::decode_body(&tp_caveats[0].body).unwrap();
            let wire_ticket = ThirdPartyCaveat::decrypt_ticket(&tp.ticket, &shared_key).unwrap();
            let mut dk = [0u8; 32];
            dk.copy_from_slice(&wire_ticket.discharge_key);

            let mut discharge =
                create_discharge(tp.ticket.clone(), &dk, "https://auth.dregg.dev".into(), &[]);
            mac.bind_discharge(&mut discharge);
            black_box(mac.verify(&root_key, &[discharge]).unwrap());
        });
    });
}

fn bench_hmac_chain(c: &mut Criterion) {
    let key = crypto::random_key();
    let messages: Vec<Vec<u8>> = (0..10).map(|i| vec![i; 32]).collect();

    c.bench_function("hmac_chain_10_links", |b| {
        b.iter(|| {
            let mut tail = key;
            for msg in &messages {
                tail = crypto::hmac_sha256(&tail, msg);
            }
            black_box(tail);
        });
    });
}

criterion_group!(
    benches,
    bench_create,
    bench_verify_no_caveats,
    bench_verify_with_caveats,
    bench_serialize_deserialize,
    bench_encode_decode,
    bench_third_party_flow,
    bench_hmac_chain,
);
criterion_main!(benches);
