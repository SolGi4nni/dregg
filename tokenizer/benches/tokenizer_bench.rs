use criterion::{Criterion, black_box, criterion_group, criterion_main};
use dregg_tokenizer::{SealedSecret, TokenizerKeypair};

fn bench_keypair_generate(c: &mut Criterion) {
    c.bench_function("tokenizer_keypair_generate", |b| {
        b.iter(|| {
            black_box(TokenizerKeypair::generate());
        });
    });
}

fn bench_seal(c: &mut Criterion) {
    let keypair = TokenizerKeypair::generate();
    let plaintext = b"super-secret-access-token-value-here";
    c.bench_function("tokenizer_seal", |b| {
        b.iter(|| {
            black_box(SealedSecret::seal(plaintext, keypair.public_key()).unwrap());
        });
    });
}

fn bench_unseal(c: &mut Criterion) {
    let keypair = TokenizerKeypair::generate();
    let plaintext = b"super-secret-access-token-value-here";
    let sealed = SealedSecret::seal(plaintext, keypair.public_key()).unwrap();
    c.bench_function("tokenizer_unseal", |b| {
        b.iter(|| {
            black_box(keypair.unseal(&sealed).unwrap());
        });
    });
}

fn bench_seal_unseal_roundtrip(c: &mut Criterion) {
    let keypair = TokenizerKeypair::generate();
    let plaintext = b"super-secret-access-token-value-here";
    c.bench_function("tokenizer_seal_unseal_roundtrip", |b| {
        b.iter(|| {
            let sealed = SealedSecret::seal(plaintext, keypair.public_key()).unwrap();
            black_box(keypair.unseal(&sealed).unwrap());
        });
    });
}

fn bench_seal_large_payload(c: &mut Criterion) {
    let keypair = TokenizerKeypair::generate();
    let plaintext = vec![0x42u8; 4096];
    c.bench_function("tokenizer_seal_4kb", |b| {
        b.iter(|| {
            black_box(SealedSecret::seal(&plaintext, keypair.public_key()).unwrap());
        });
    });
}

criterion_group!(
    benches,
    bench_keypair_generate,
    bench_seal,
    bench_unseal,
    bench_seal_unseal_roundtrip,
    bench_seal_large_payload,
);
criterion_main!(benches);
