//! **The durability market loop, end-to-end** — the M1 organs wired into one flow.
//!
//! This composes the pieces built for the market into a single coherent path, the way
//! a real durability deal lives and (mis)behaves:
//!
//! 1. **Bonded operators** ([`dregg_storage_templates::bonded_operator`]) — each posts a
//!    bond over the real relay-operator template; the operator's ed25519 verifying key IS
//!    its identity (the `operator_pk` throughout).
//! 2. **Placement** ([`dregg_storage::placement`]) — per-grain, owner-supplied-candidate,
//!    deterministic (by `grain_id`), bond-weighted selection of the operators for a grain.
//! 3. **Durability deal** ([`dregg_storage::durability_deal`]) — the grain's bytes are
//!    Reed-Solomon k-of-n sharded across the selected operators.
//! 4. **Proof-of-retrievability** — a challenge on a shard is answered by the ASSIGNED
//!    operator (signed); an honest operator verifies, an impostor is rejected.
//! 5. **Slash → treasury** ([`crate::relay_dispute::SlashPayout`]) — a faulty operator
//!    (fails its PoR) has its bond seized and split conserving: restitution to the wronged
//!    grain owner + remainder to the treasury.
//!
//! No global consensus, no global directory, no global-owned treasury — per-grain,
//! bilateral, owner-anchored, conserving throughout. This test is the proof the organs
//! compose into a working loop, not just individually.

#[cfg(test)]
mod tests {
    use dregg_storage::durability_deal::{challenge_message, create, shard_layout};
    use dregg_storage::placement::{OperatorCandidate, select_operators};
    use dregg_storage_templates::bonded_operator::open_bonded_operator;
    use ed25519_dalek::{Signer, SigningKey, VerifyingKey};

    use crate::relay_dispute::SlashPayout;

    fn signer(seed: u8) -> SigningKey {
        SigningKey::from_bytes(&[seed; 32])
    }

    #[test]
    fn durability_market_loop_end_to_end() {
        // The grain's durable bytes + the RS parameters => n shards.
        let data = b"the grain's durable state, worth keeping alive across operators";
        let chunk_size = 64usize; // >= data.len() => k=1, n=expansion (small operator set)
        let expansion = 3usize;
        let (_k_data, n) = shard_layout(data.len(), chunk_size, expansion);
        let bond_min = 1_000u64;

        // 1. BONDED OPERATORS: n+2 candidates, identity = ed25519 vk bytes, distinct bonds.
        let signers: Vec<SigningKey> = (1..=(n as u8 + 2)).map(signer).collect();
        let candidates: Vec<OperatorCandidate> = signers
            .iter()
            .enumerate()
            .map(|(i, s)| {
                let pk = s.verifying_key().to_bytes();
                let bond = 10_000 - (i as u64) * 500; // all comfortably above the floor
                // The bonded-operator cell is a real template instance (bond invariant enforced).
                let bonded =
                    open_bonded_operator(bond, bond_min, pk).expect("bond above floor registers");
                assert!(bonded.bond_amount() >= bonded.bond_min());
                OperatorCandidate::new(pk, bonded.bond_amount(), bonded.bond_min(), 0)
            })
            .collect();

        // 2. PLACEMENT: pick n operators for this grain (deterministic, bond-weighted).
        let grain_id = b"grain-market-loop-xyz";
        let placements =
            select_operators(&candidates, grain_id, n).expect("enough eligible operators");
        assert_eq!(placements.len(), n, "one operator selected per shard");
        // Deterministic: the same grain re-selects the same operators.
        let again = select_operators(&candidates, grain_id, n).unwrap();
        assert_eq!(
            placements, again,
            "placement is a pure function of (candidates, grain_id)"
        );

        // 3. DURABILITY DEAL: RS-shard the grain across the selected operators.
        let shard_ops: Vec<VerifyingKey> = placements
            .iter()
            .map(|p| VerifyingKey::from_bytes(&p.operator_id).expect("operator id is a vk"))
            .collect();
        let (deal, chunks) =
            create(data, chunk_size, expansion, &shard_ops).expect("deal places every shard");

        // 4. PoR — HONEST: the assigned operator answers a challenge (signed) and verifies.
        let nonce = 42u64;
        let idx = deal.challenge_index(nonce);
        let assigned_vk = shard_ops[idx];
        let assigned = signers
            .iter()
            .find(|s| s.verifying_key() == assigned_vk)
            .expect("the assigned operator is one of ours");
        let msg = challenge_message(&deal.root, idx, nonce);
        let good = assigned.sign(&msg);
        assert!(
            deal.verify_challenge_authenticated(idx, nonce, &chunks[idx], &good)
                .is_ok(),
            "the assigned operator, holding the shard, passes its PoR"
        );

        // 4b. PoR — FAULT: any other operator cannot answer for this shard.
        let impostor = signers
            .iter()
            .find(|s| s.verifying_key() != assigned_vk)
            .expect("another operator exists");
        let bad = impostor.sign(&challenge_message(&deal.root, idx, nonce));
        assert!(
            deal.verify_challenge_authenticated(idx, nonce, &chunks[idx], &bad)
                .is_err(),
            "an operator that does not hold the shard fails the PoR (fault proven)"
        );

        // 5. SLASH the faulty operator -> restitution + treasury, conserving.
        //    Its bond had `10_000 - i*500`; headroom above the floor is seizable.
        let faulty_bond = candidates
            .iter()
            .find(|c| c.operator_id == impostor.verifying_key().to_bytes())
            .map(|c| c.bond)
            .unwrap();
        let seizable = faulty_bond - bond_min; // never below the floor
        let proven_loss = 300u64; // the grain owner's proven loss (re-provisioning the shard)
        let bounty = 100u64;
        let payout = SlashPayout::split(seizable, proven_loss, bounty);

        assert_eq!(
            payout.restitution + payout.remainder,
            seizable,
            "the seizure is conserved: restitution + remainder == seized (nothing destroyed)"
        );
        assert_eq!(
            payout.restitution,
            (proven_loss + bounty).min(seizable),
            "the wronged grain owner is made whole up to their proven loss + bounty"
        );
        assert!(
            payout.remainder > 0,
            "the remainder routes to the treasury (a public fault-beacon)"
        );

        // The loop closed: a bonded operator was placed, held (or failed to hold) a shard,
        // and a proven durability fault seized its bond into restitution + treasury.
    }
}
