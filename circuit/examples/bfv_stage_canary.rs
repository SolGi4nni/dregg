pub use dregg_circuit::BabyBear;
pub use dregg_circuit::descriptor_ir2;
pub use dregg_circuit::descriptor_ir2_canonical;
pub use dregg_circuit::private_book_bfv_tables;

#[path = "../src/private_book_bfv_exact_public.rs"]
mod private_book_bfv_exact_public;

fn main() {
    let proof = private_book_bfv_exact_public::prove_bfv_q0_n8_exact_public()
        .expect("fixed q0/N8 exact-public KAT must prove");
    private_book_bfv_exact_public::verify_bfv_q0_n8_exact_public(&proof)
        .expect("all three fixed stages must verify");
    assert_eq!(proof.stage_count(), 3);
    println!("q0/N8 exact-public three-stage proof green");
}
