# `dregg` Holistic DSL: One Language, Three Modes

## Answer: One language, three compilation modes

Not two separate languages. One syntax with three *scopes*:

1. **Constraint scope** (Phase 1-2: per-row expressions) -- `require!`, `mutate!`, `hash!`
2. **Trace scope** (new: layout + topology) -- `layout!`, `transition!`, `for_each!`
3. **Composition scope** (new: proof orchestration) -- `compose!`, `bind!`, `chain!`

The proc macro `#[dregg_circuit]` dispatches on scope markers. The same token stream targets BabyBear STARK (`StarkAir`), Plonky3 (`Air<AB>`), and Kimchi (Poseidon gates) via backend trait selection at compile time.

## Derivation AIR in the DSL

```rust
#[dregg_circuit(backend = "babybear | plonky3 | kimchi")]
mod derivation {
    layout! {
        rule_id: Field,
        body: [BodyAtom; 8],
        head_pred: Field,
        head_terms: [Term; 4],
        derived_hash: Field,
        substitution: [Field; 8],
        eq_checks: [EqCheck; 4],
        memberof_checks: [MemberOfCheck; 4],
        gte_check: RangeCheck<30>,
        lt_check: RangeCheck<30>,
        check_bindings: [TermBinding; 20],
    }

    struct BodyAtom { hash: Field, membership: Binary, root: Field }
    struct Term { is_var: Binary, raw: Field, sel: [Binary; 8] }
    struct EqCheck { active: Binary, term_a: Field, term_b: Field }
    struct RangeCheck<const BITS: usize> { active: Binary, a: Field, b: Field, diff: Field, bits: [Binary; BITS] }
    struct TermBinding { is_var: Binary, raw: Field, sel: [Binary; 8] }

    constraints! {
        for atom in body {
            binary!(atom.membership);
            require!(atom.membership * atom.hash != 0);  // hash nonzero when used
            require!(atom.membership * (atom.root - public[0]) == 0);  // roots match state
        }
        require!(sum(body.*.membership) != 0);  // at least one body

        for term in head_terms {
            binary!(term.is_var);
            for s in term.sel { binary!(s); }
            require!(sum(term.sel) == term.is_var);  // exactly-one selector
            let resolved = term.is_var * dot(term.sel, substitution)
                         + (1 - term.is_var) * term.raw;
            require!(head_terms[term.index].value == resolved);  // substitution correct
        }

        require!(derived_hash == hash!(head_pred, head_terms.*.value));
        require!(derived_hash == public[1]);

        for check in eq_checks {
            binary!(check.active);
            require!(check.active * (check.term_a - check.term_b) == 0);
        }

        range_check!(gte_check);  // expands: binary bits, decomposition, high bit zero
        range_check!(lt_check);
        bind_check_terms!(check_bindings, substitution);
    }

    public_inputs! { state_root, derived_fact_hash, not_after, org_id, budget }
}
```

Width: computed at compile time from `layout!`. The macro counts fields, expands arrays, sums struct widths. For this definition: 371 columns -- matching the hand-written AIR exactly.

## Sovereign Transition in the DSL

```rust
#[dregg_circuit]
mod sovereign_transfer {
    layout! { old_balance: Field, amount: Field, new_balance: Field, direction: Binary }

    constraints! {
        binary!(direction);
        require!(new_balance == old_balance + amount - 2 * direction * amount);
    }

    public_inputs! { old_commitment: [Field; 8], new_commitment: [Field; 8],
                     effects_hash: [Field; 8], cell_id_hash: [Field; 8] }
}
```

## Temporal Predicate (Transition Constraints)

```rust
#[dregg_circuit]
mod temporal_predicate {
    layout! { step: Field, state_root: Field, value: Field, diff: Field,
              bits: [Binary; 30], accumulator: Field }

    constraints! {
        require!(diff == value - public.threshold);
        range_check_inline!(diff, bits);
    }

    transition! {
        require!(next.accumulator == local.accumulator + 1);
        require!(next.step == local.step + 1);
    }

    boundary! {
        first { step == 0; accumulator == 1; state_root == public.initial_root; }
        last  { accumulator == public.num_steps; state_root == public.final_root; }
    }

    public_inputs! { threshold, num_steps, initial_root, final_root }
}
```

## IVC Hash Chain (Multi-row with Poseidon2)

```rust
#[dregg_circuit]
mod ivc_chain {
    layout! { step: Field, old_hash: Field, new_root: Field, new_hash: Field }

    constraints! {
        require!(new_hash == hash!(IVC_DOMAIN_TAG, old_hash, new_root, step));
    }

    boundary! {
        first { step == 1; old_hash == hash!(IVC_DOMAIN_TAG, public.initial_root, 0); }
        last  { step == public.step_count; new_hash == public.accumulated_hash; }
    }

    public_inputs! { initial_root, final_root, step_count, accumulated_hash }
}
```

## Composition (Presentation Proof)

```rust
#[dregg_compose]
mod presentation {
    proofs! {
        fold: ivc_chain,
        derivation: derivation | multi_step_derivation,
        membership: merkle_membership,
    }

    bind! {
        fold.final_root == derivation.public.state_root;
        membership.leaf == issuer_key_hash;
        membership.root == public.federation_root;
        composition_commitment == hash!(
            fold.accumulated_hash,
            derivation.public.derived_fact_hash,
            presentation_tag
        );
    }

    public_inputs! {
        federation_root, request_predicate: [Field; 4], timestamp,
        presentation_tag, revealed_facts_commitment: [Field; 4],
        composition_commitment: [Field; 4], verifier_nonce, verifier_block_height
    }
}
```

## Design Decisions

**Q1: One language or two?** One language. The `layout!`/`constraints!`/`transition!`/`boundary!` blocks are all proc-macro-recognized sections within a single `#[dregg_circuit]` attribute. Composition uses `#[dregg_compose]` -- same parser, different code-gen path.

**Q2: Proc macro or standalone parser?** Proc macro. It generates `impl StarkAir` (for BabyBear), `impl Air<AB>` (for Plonky3), and Kimchi gate sequences. No separate toolchain. The `backend` attribute selects which impls to emit.

**Q3: Relation to `StarkAir` trait?** The macro GENERATES the `StarkAir` impl. `eval_constraints` is synthesized from the `constraints!` + `transition!` blocks. `width()` is computed from `layout!`. `boundary_constraints()` comes from `boundary!`. The generated code is equivalent to hand-written AIR code -- same performance, same constraint degree.

**Q4: Same definition targets BabyBear and Kimchi?** Yes. The `layout!` is backend-agnostic (column counts are universal). Constraints compile to polynomial expressions; the backend chooses field type and gate decomposition. `hash!` dispatches to Poseidon2 (BabyBear) or Mina-Poseidon (Kimchi). `range_check!` dispatches to bit columns (STARK) or Kimchi RangeCheck gates.

**Q5: Plonky3's `Air` trait?** Third target. The macro emits `impl<AB: AirBuilder> Air<AB> for FooAir` alongside `impl StarkAir`. Same constraint expressions, different trait method signatures. The `AB::Expr` abstraction in Plonky3 maps directly to our polynomial constraint AST.

## What the Macro Computes at Compile Time

- Column indices (replacing hand-written `pub mod col { ... }`)
- Trace width (replacing `const DERIVATION_AIR_WIDTH: usize = 371`)
- Constraint count and maximum degree
- Witness generation skeleton (struct with all layout fields)
- Public input indices
- `for` loops unroll to concrete column ranges

## What Stays Outside the DSL

- Witness acquisition (fetching Merkle paths, computing substitutions)
- The IVC builder orchestration logic (when to fold, when to finalize)
- Bridge-layer protocol (SP1 wrapping, EVM verification)
- Runtime policy evaluation (which rules to apply)

The DSL describes WHAT the circuit proves. The runtime decides WHEN and WITH WHAT witness.
