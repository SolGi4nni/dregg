// Minimal tfhe-rs smoke test: confirm the real library encrypts, adds
// homomorphically, and compares — the three primitives the clearing needs.
use std::time::Instant;
use tfhe::prelude::*;
use tfhe::{generate_keys, set_server_key, ConfigBuilder, FheUint16};

fn main() {
    let config = ConfigBuilder::default().build();
    let (ck, sk) = generate_keys(config);
    set_server_key(sk);

    let a = FheUint16::encrypt(40u16, &ck);
    let b = FheUint16::encrypt(2u16, &ck);

    let t = Instant::now();
    let s = &a + &b;
    let add_ns = t.elapsed();

    let t = Instant::now();
    let ge = a.ge(&b);
    let ge_ns = t.elapsed();

    let sd: u16 = s.decrypt(&ck);
    let ged: bool = ge.decrypt(&ck);
    println!("40+2 = {sd}  (add {add_ns:?})");
    println!("40>=2 = {ged}  (ge {ge_ns:?})");
    assert_eq!(sd, 42);
    assert!(ged);
    println!("SMOKE OK: real tfhe-rs primitives work");
}
