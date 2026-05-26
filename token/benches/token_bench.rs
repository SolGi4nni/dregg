use criterion::{BenchmarkId, Criterion, black_box, criterion_group, criterion_main};
use dregg_token::{
    Attenuation, AuthRequest, AuthToken, BiscuitToken, MacaroonToken, RevocationFilter, TokenFormat,
};

fn macaroon_root_key() -> [u8; 32] {
    let mut key = [0u8; 32];
    getrandom::fill(&mut key).unwrap();
    key
}

fn bench_macaroon_mint(c: &mut Criterion) {
    let key = macaroon_root_key();
    c.bench_function("token_macaroon_mint", |b| {
        b.iter(|| {
            black_box(MacaroonToken::mint(key, b"kid", "dregg.dev"));
        });
    });
}

fn bench_macaroon_verify(c: &mut Criterion) {
    let key = macaroon_root_key();
    let token = MacaroonToken::mint(key, b"kid", "dregg.dev");
    let request = AuthRequest::default();
    c.bench_function("token_macaroon_verify", |b| {
        b.iter(|| {
            black_box(token.verify(&request).unwrap());
        });
    });
}

fn bench_macaroon_attenuate(c: &mut Criterion) {
    let key = macaroon_root_key();
    let token = MacaroonToken::mint(key, b"kid", "dregg.dev");
    let attenuation = Attenuation {
        apps: vec![("my-app".into(), "r".into())],
        not_after: Some(1700000000),
        ..Default::default()
    };
    c.bench_function("token_macaroon_attenuate", |b| {
        b.iter(|| {
            black_box(token.attenuate(&attenuation).unwrap());
        });
    });
}

fn bench_biscuit_mint(c: &mut Criterion) {
    let keypair = biscuit_auth::KeyPair::new();
    let code = r#"
    app("test-app");
    service("http");
    right("read");
    unrestricted(true);
  "#;
    c.bench_function("token_biscuit_mint", |b| {
        b.iter(|| {
            black_box(BiscuitToken::mint(&keypair, code).unwrap());
        });
    });
}

fn bench_biscuit_verify(c: &mut Criterion) {
    let keypair = biscuit_auth::KeyPair::new();
    let code = r#"
    app("test-app");
    service("http");
    right("read");
    unrestricted(true);
  "#;
    let token = BiscuitToken::mint(&keypair, code).unwrap();
    let request = AuthRequest {
        app_id: Some("test-app".into()),
        action: Some("r".into()),
        ..Default::default()
    };
    c.bench_function("token_biscuit_verify", |b| {
        b.iter(|| {
            black_box(token.verify(&request).unwrap());
        });
    });
}

fn bench_biscuit_attenuate(c: &mut Criterion) {
    let keypair = biscuit_auth::KeyPair::new();
    let code = r#"
    app("test-app");
    service("http");
    right("read");
    unrestricted(true);
  "#;
    let token = BiscuitToken::mint(&keypair, code).unwrap();
    let attenuation = Attenuation {
        apps: vec![("test-app".into(), "r".into())],
        not_after: Some(1700000000),
        ..Default::default()
    };
    c.bench_function("token_biscuit_attenuate", |b| {
        b.iter(|| {
            black_box(token.attenuate(&attenuation).unwrap());
        });
    });
}

fn bench_format_detection(c: &mut Criterion) {
    let key = macaroon_root_key();
    let mac = MacaroonToken::mint(key, b"kid", "loc");
    let encoded = mac.to_encoded().unwrap();
    c.bench_function("token_format_detect", |b| {
        b.iter(|| {
            black_box(TokenFormat::detect(&encoded).unwrap());
        });
    });
}

fn bench_macaroon_encode_decode(c: &mut Criterion) {
    let key = macaroon_root_key();
    let token = MacaroonToken::mint(key, b"kid", "dregg.dev");
    let encoded = token.to_encoded().unwrap();

    c.bench_function("token_macaroon_encode", |b| {
        b.iter(|| {
            black_box(token.to_encoded().unwrap());
        });
    });

    c.bench_function("token_macaroon_decode", |b| {
        b.iter(|| {
            black_box(MacaroonToken::from_encoded(&encoded, key).unwrap());
        });
    });
}

fn bench_attenuation_chain_verify(c: &mut Criterion) {
    let mut group = c.benchmark_group("token_attenuation_chain");

    for &depth in &[1usize, 5, 10, 20] {
        let key = macaroon_root_key();
        let root = MacaroonToken::mint(key, b"kid-1", "dregg.dev");
        let mut token: Box<dyn AuthToken> = Box::new(root);
        for i in 0..depth {
            let att = Attenuation {
                apps: vec![(format!("app-{i}"), "r".into())],
                ..Default::default()
            };
            token = token.attenuate(&att).unwrap();
        }
        let request = AuthRequest::default();

        group.bench_with_input(BenchmarkId::new("verify_depth", depth), &depth, |b, _| {
            b.iter(|| {
                black_box(token.verify(&request).unwrap());
            });
        });
    }

    group.finish();
}

fn bench_revocation_filter(c: &mut Criterion) {
    let mut group = c.benchmark_group("token_revocation_filter");

    for &count in &[1_000usize, 10_000, 100_000] {
        let filter = RevocationFilter::new();
        for i in 0..count {
            filter.revoke(&format!("nonce-{i}"));
        }

        group.bench_with_input(BenchmarkId::new("lookup_present", count), &count, |b, _| {
            b.iter(|| {
                black_box(filter.is_revoked("nonce-500"));
            });
        });

        group.bench_with_input(BenchmarkId::new("lookup_absent", count), &count, |b, _| {
            b.iter(|| {
                black_box(filter.is_revoked("not-revoked-xyz"));
            });
        });
    }

    group.finish();
}

fn bench_token_serialization_size(c: &mut Criterion) {
    let mut group = c.benchmark_group("token_serialization");

    // Macaroon encode/decode with varying caveat counts
    for &num_caveats in &[0usize, 1, 5, 10] {
        let key = macaroon_root_key();
        let root = MacaroonToken::mint(key, b"kid-1", "dregg.dev");
        let mut token: Box<dyn AuthToken> = Box::new(root);
        for i in 0..num_caveats {
            let att = Attenuation {
                apps: vec![(format!("app-{i}"), "rw".into())],
                ..Default::default()
            };
            token = token.attenuate(&att).unwrap();
        }
        let encoded = token.to_encoded().unwrap();
        eprintln!(
            "  [token_size] Macaroon with {} caveats: {} bytes",
            num_caveats,
            encoded.len()
        );

        group.bench_with_input(
            BenchmarkId::new("macaroon_encode", num_caveats),
            &num_caveats,
            |b, _| {
                b.iter(|| black_box(token.to_encoded().unwrap()));
            },
        );
    }

    group.finish();
}

criterion_group!(
    benches,
    bench_macaroon_mint,
    bench_macaroon_verify,
    bench_macaroon_attenuate,
    bench_biscuit_mint,
    bench_biscuit_verify,
    bench_biscuit_attenuate,
    bench_format_detection,
    bench_macaroon_encode_decode,
    bench_attenuation_chain_verify,
    bench_revocation_filter,
    bench_token_serialization_size,
);
criterion_main!(benches);
