# Codex re-review #3 — the segment-accumulator close + the weak-digest deviation (2026-06-24)

VERDICT: PARTIAL CLOSE. Distinct-endpoint mixed-root forgery genuinely REJECTED (structural). But the digest deviation (base-field fold instead of codex's specified collision-resistant commitment) is a REAL soundness downgrade for same-endpoint/same-count histories — and it's ALGEBRAICALLY broken, not merely 31-bit.

**Verdict: partial close.** The original mixed-root forgery with different genesis/final/count is closed in the K-fold path. The root proof exposes the descriptor-derived segment, and the verifier compares it to the carried claim at [ivc_turn_chain.rs:1757](/Users/ember/dev/breadstuffs/circuit-prove/src/ivc_turn_chain.rs:1757). So if A and B differ in genesis, final, or count, the rejection does not depend on the digest.

But the deviation is a real soundness downgrade for same-genesis, same-final, same-count histories.

**Findings**

1. **High: same-endpoint history binding is only the weak `acc` lane.**  
   Leaf segments expose only `[old, new, 1, H(old,new)]` from PI 42/43 at [ivc_turn_chain.rs:1059](/Users/ember/dev/breadstuffs/circuit-prove/src/ivc_turn_chain.rs:1059). Aggregation exposes only `[first_old, last_new, count, acc]` at [ivc_turn_chain.rs:1632](/Users/ember/dev/breadstuffs/circuit-prove/src/ivc_turn_chain.rs:1632). The verifier does not pin intermediate roots independently; it checks only the folded root segment. The carried binding proof is explicitly ignored at [ivc_turn_chain.rs:1724](/Users/ember/dev/breadstuffs/circuit-prove/src/ivc_turn_chain.rs:1724).

2. **High: the base-field fold has cheap algebraic collisions, not just ~31-bit generic risk.**  
   The fold is `h(a,b)=a*M1+b*M2+a*b*M3` at [ivc_turn_chain.rs:253](/Users/ember/dev/breadstuffs/circuit-prove/src/ivc_turn_chain.rs:253). For a 2-turn chain `G -> x -> F`, the root digest is:
   `D(x)=h(h(G,x), h(x,F))`, a quadratic over BabyBear. Given one middle root `x`, the paired collision root is algebraically computable. Example over the actual constants: `G=0, F=0, x=1` collides with `x'=395800066`, both producing digest `528231422`. There are also degeneracies: `a = -M2/M3 = 924467525` makes `h(a,b)` independent of `b`; `b = -M1/M3 = 526820265` makes it independent of `a`.

3. **Medium: dropping the binding proof is correct for the old bug, but removes the stronger cross-check.**  
   Removing the swappable binding leaf from the soundness path was necessary. But now the only K-fold ordered-history commitment is the weak segment `acc`. The old Poseidon `TurnChainBindingAir` still exists and really constrains its digest at [ivc_turn_chain.rs:613](/Users/ember/dev/breadstuffs/circuit-prove/src/ivc_turn_chain.rs:613), but it is no longer verified in the K-fold verifier.

4. **Medium: the online accumulator is not closed by this fix.**  
   [accumulator.rs:39](/Users/ember/dev/breadstuffs/circuit-prove/src/accumulator.rs:39) explicitly says the online accumulator still uses a separate binding leaf and retains the mixed-root structural weakness. Scope the close to the balanced K-fold path only.

5. **Low/medium: continuity/count constraints are good for the provided leaves, with caveats.**  
   `L.last_new == R.first_old` and count additivity are enforced at [ivc_turn_chain.rs:1625](/Users/ember/dev/breadstuffs/circuit-prove/src/ivc_turn_chain.rs:1625). That prevents gaps, padding injection, and broken reorderings in the provided leaf order. It does not prove membership in an external finalized list, and count is a BabyBear field, so formally it is modulo `p` unless the system bounds `num_turns < p`.

**Bottom line:** distinct-endpoint mixed-root forgery is genuinely rejected. Full ordered-history soundness is not achieved. Same-endpoint/same-count histories rely on a one-felt, algebraically weak digest; if an attacker can realize colliding intermediate roots as valid executions, a proof of A can stand in for B’s middle history. The fix should replace `seg_hash2_*` with an in-circuit collision-resistant multi-felt commitment, and the root claim should carry that wider digest.
203,455
**Verdict: partial close.** The original mixed-root forgery with different genesis/final/count is closed in the K-fold path. The root proof exposes the descriptor-derived segment, and the verifier compares it to the carried claim at [ivc_turn_chain.rs:1757](/Users/ember/dev/breadstuffs/circuit-prove/src/ivc_turn_chain.rs:1757). So if A and B differ in genesis, final, or count, the rejection does not depend on the digest.

But the deviation is a real soundness downgrade for same-genesis, same-final, same-count histories.

**Findings**

1. **High: same-endpoint history binding is only the weak `acc` lane.**  
   Leaf segments expose only `[old, new, 1, H(old,new)]` from PI 42/43 at [ivc_turn_chain.rs:1059](/Users/ember/dev/breadstuffs/circuit-prove/src/ivc_turn_chain.rs:1059). Aggregation exposes only `[first_old, last_new, count, acc]` at [ivc_turn_chain.rs:1632](/Users/ember/dev/breadstuffs/circuit-prove/src/ivc_turn_chain.rs:1632). The verifier does not pin intermediate roots independently; it checks only the folded root segment. The carried binding proof is explicitly ignored at [ivc_turn_chain.rs:1724](/Users/ember/dev/breadstuffs/circuit-prove/src/ivc_turn_chain.rs:1724).

2. **High: the base-field fold has cheap algebraic collisions, not just ~31-bit generic risk.**  
   The fold is `h(a,b)=a*M1+b*M2+a*b*M3` at [ivc_turn_chain.rs:253](/Users/ember/dev/breadstuffs/circuit-prove/src/ivc_turn_chain.rs:253). For a 2-turn chain `G -> x -> F`, the root digest is:
   `D(x)=h(h(G,x), h(x,F))`, a quadratic over BabyBear. Given one middle root `x`, the paired collision root is algebraically computable. Example over the actual constants: `G=0, F=0, x=1` collides with `x'=395800066`, both producing digest `528231422`. There are also degeneracies: `a = -M2/M3 = 924467525` makes `h(a,b)` independent of `b`; `b = -M1/M3 = 526820265` makes it independent of `a`.

3. **Medium: dropping the binding proof is correct for the old bug, but removes the stronger cross-check.**  
   Removing the swappable binding leaf from the soundness path was necessary. But now the only K-fold ordered-history commitment is the weak segment `acc`. The old Poseidon `TurnChainBindingAir` still exists and really constrains its digest at [ivc_turn_chain.rs:613](/Users/ember/dev/breadstuffs/circuit-prove/src/ivc_turn_chain.rs:613), but it is no longer verified in the K-fold verifier.

4. **Medium: the online accumulator is not closed by this fix.**  
   [accumulator.rs:39](/Users/ember/dev/breadstuffs/circuit-prove/src/accumulator.rs:39) explicitly says the online accumulator still uses a separate binding leaf and retains the mixed-root structural weakness. Scope the close to the balanced K-fold path only.

5. **Low/medium: continuity/count constraints are good for the provided leaves, with caveats.**  
   `L.last_new == R.first_old` and count additivity are enforced at [ivc_turn_chain.rs:1625](/Users/ember/dev/breadstuffs/circuit-prove/src/ivc_turn_chain.rs:1625). That prevents gaps, padding injection, and broken reorderings in the provided leaf order. It does not prove membership in an external finalized list, and count is a BabyBear field, so formally it is modulo `p` unless the system bounds `num_turns < p`.
