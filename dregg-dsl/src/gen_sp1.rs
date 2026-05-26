/// Code generator: SP1 guest program (RISC-V zkVM).
///
/// Produces a function `{name}_sp1_guest() -> &'static str` that returns Rust source
/// code suitable for compiling as an SP1 guest program. The generated code:
///
/// 1. Reads inputs from the SP1 host via `sp1_zkvm::io::read()`
/// 2. Evaluates the constraint logic (same semantics as `gen_rust.rs`)
/// 3. Commits public outputs via `sp1_zkvm::io::commit()`
///
/// ## Why SP1?
///
/// SP1 proves arbitrary Rust code inside a RISC-V zkVM. This means any
/// `CircuitDescriptor` can be proven without building a custom AIR — the
/// RISC-V execution trace IS the proof. This is ideal for:
///
/// - Complex constraints that don't map cleanly to arithmetic circuits
/// - TurnExecutor verification (the "prove the executor" vision)
/// - Rapid prototyping before writing optimized native AIRs
///
/// ## Trade-offs vs Native AIR
///
/// - **Proof size**: SP1 proofs are larger (~100KB vs ~1KB for STARK)
/// - **Prover time**: 10-100x slower than native AIR for simple constraints
/// - **Flexibility**: Can prove anything Rust can express (no degree limits)
/// - **Development speed**: Zero circuit engineering needed
///
/// ## Generated Code Structure
///
/// ```ignore
/// #![no_main]
/// sp1_zkvm::entrypoint!(main);
///
/// pub fn main() {
///     // Read inputs
///     let param1: u64 = sp1_zkvm::io::read();
///     // ... evaluate constraints ...
///     // Commit outputs
///     sp1_zkvm::io::commit(&result);
/// }
/// ```
///
/// ## Membership Constraints
///
/// For set membership, the SP1 guest simply reads the Merkle proof from
/// the host and verifies it in Rust — no circuit gadgets needed. The
/// zkVM proves the verification was done correctly.
use proc_macro2::TokenStream;
use quote::{format_ident, quote};

use crate::ir::{ConstraintIr, MutateOp, ParamType, RequirementKind, Statement};

pub fn generate_sp1(ir: &ConstraintIr) -> TokenStream {
    let fn_name = format_ident!("{}_sp1_guest", ir.name);
    let guest_code = build_sp1_guest_code(ir);

    quote! {
        /// Returns SP1 guest program source code implementing this constraint.
        ///
        /// Compile this with the SP1 toolchain (`cargo prove build`) to get an
        /// ELF that can be proven by the SP1 prover. The host program should
        /// provide inputs via `sp1_zkvm::io::write()`.
        pub fn #fn_name() -> &'static str {
            #guest_code
        }
    }
}

fn build_sp1_guest_code(ir: &ConstraintIr) -> String {
    let mut lines = Vec::new();

    lines.push("#![no_main]".to_string());
    lines.push("sp1_zkvm::entrypoint!(main);".to_string());
    lines.push(String::new());
    lines.push("pub fn main() {".to_string());

    // Read inputs
    for p in &ir.params {
        let name = p.name.to_string();
        let rust_type: String = match &p.ty {
            ParamType::U64 => "u64".to_string(),
            ParamType::ByteArray32 => "[u8; 32]".to_string(),
            ParamType::ByteMatrix32(n) => format!("[[u8; 32]; {}]", n),
            ParamType::Set => "Vec<u64>".to_string(), // Sets passed as vectors for SP1
            ParamType::UserDefined(path) => path.clone(),
        };

        if p.mutable {
            lines.push(format!(
                "    let mut {}: {} = sp1_zkvm::io::read();",
                name, rust_type
            ));
        } else {
            lines.push(format!(
                "    let {}: {} = sp1_zkvm::io::read();",
                name, rust_type
            ));
        }
    }

    lines.push(String::new());

    // Generate constraint evaluation
    emit_sp1_statements(&ir.statements, &mut lines, 1);

    // Commit outputs
    lines.push(String::new());
    if ir.is_effect {
        // Commit mutated values as public outputs
        for p in &ir.params {
            if p.mutable {
                let name = p.name.to_string();
                lines.push(format!("    sp1_zkvm::io::commit(&{});", name));
            }
        }
    }

    // Commit success flag
    lines.push("    sp1_zkvm::io::commit(&1u8); // success".to_string());
    lines.push("}".to_string());

    lines.join("\n")
}

fn emit_sp1_statements(statements: &[Statement], lines: &mut Vec<String>, indent: usize) {
    let pad = "    ".repeat(indent);

    for stmt in statements {
        match stmt {
            Statement::Require(req) => {
                let check = match &req.kind {
                    RequirementKind::LessEqual { left, right } => {
                        let l = quote::quote!(#left).to_string();
                        let r = quote::quote!(#right).to_string();
                        format!(
                            "assert!({} <= {}, \"constraint violated: {} <= {}\");",
                            l, r, l, r
                        )
                    }
                    RequirementKind::GreaterEqual { left, right } => {
                        let l = quote::quote!(#left).to_string();
                        let r = quote::quote!(#right).to_string();
                        format!(
                            "assert!({} >= {}, \"constraint violated: {} >= {}\");",
                            l, r, l, r
                        )
                    }
                    RequirementKind::Equal { left, right } => {
                        let l = quote::quote!(#left).to_string();
                        let r = quote::quote!(#right).to_string();
                        format!(
                            "assert!({} == {}, \"constraint violated: {} == {}\");",
                            l, r, l, r
                        )
                    }
                    RequirementKind::NotEqual { left, right } => {
                        let l = quote::quote!(#left).to_string();
                        let r = quote::quote!(#right).to_string();
                        format!(
                            "assert!({} != {}, \"constraint violated: {} != {}\");",
                            l, r, l, r
                        )
                    }
                    RequirementKind::Membership { set, element } => {
                        format!(
                            "assert!({}.contains(&{}), \"membership check failed\");",
                            set, element
                        )
                    }
                    RequirementKind::BitRange { value, bits } => {
                        let v = quote::quote!(#value).to_string();
                        format!(
                            "assert!((({}) as u128) < (1u128 << {}), \"bit_range({}) violated\");",
                            v, bits, bits
                        )
                    }
                    RequirementKind::MerkleAtPosition {
                        root,
                        leaf,
                        position,
                        siblings,
                        depth,
                    } => {
                        // Real Merkle inclusion check in the SP1 guest.
                        //
                        // We compute a Poseidon2 hash chain from the leaf up to the
                        // claimed root, branching left/right at each level based on
                        // the bits of `position`. The check `assert!(current == root)`
                        // executes inside the RISC-V zkVM, so the proof attests to
                        // the actual hash computation.
                        //
                        // The hash-pair primitive `dregg_sp1_runtime::poseidon2_hash_pair`
                        // is expected to be provided by the host's SP1 guest crate. It
                        // takes two `[u8; 32]` digests and returns a `[u8; 32]` digest
                        // bit-compatible with the rest of the system's Poseidon2 use.
                        let root_s = quote::quote!(#root).to_string();
                        let leaf_s = quote::quote!(#leaf).to_string();
                        let pos_s = quote::quote!(#position).to_string();
                        let sib_s = quote::quote!(#siblings).to_string();
                        let d = *depth as usize;
                        format!(
                            "{{ let mut __cur: [u8; 32] = {leaf};\n\
                             {pad}    let __pos: u64 = ({pos}) as u64;\n\
                             {pad}    for __i in 0..{depth}usize {{\n\
                             {pad}        let __bit = ((__pos >> __i) & 1) == 1;\n\
                             {pad}        let __sib: [u8; 32] = {sib}[__i];\n\
                             {pad}        __cur = if __bit {{\n\
                             {pad}            dregg_sp1_runtime::poseidon2_hash_pair(&__sib, &__cur)\n\
                             {pad}        }} else {{\n\
                             {pad}            dregg_sp1_runtime::poseidon2_hash_pair(&__cur, &__sib)\n\
                             {pad}        }};\n\
                             {pad}    }}\n\
                             {pad}    assert!(__cur == {root}, \"merkle_at_position: chain != root (depth={depth})\");\n\
                             {pad}}}",
                            leaf = leaf_s,
                            pos = pos_s,
                            sib = sib_s,
                            depth = d,
                            root = root_s,
                            pad = pad,
                        )
                    }
                    RequirementKind::Poseidon2Hash { inputs, output } => {
                        // Real Poseidon2 hash assertion in the SP1 guest.
                        //
                        // Concatenate the input digests into a slice and assert that
                        // `dregg_sp1_runtime::poseidon2_hash_many(&inputs) == output`.
                        // The guest crate is expected to provide this helper; the
                        // assertion executes inside the zkVM so the proof attests
                        // to the actual hash.
                        let out_s = quote::quote!(#output).to_string();
                        let input_refs: Vec<String> = inputs
                            .iter()
                            .map(|e| format!("&{}", quote::quote!(#e)))
                            .collect();
                        let inputs_arr = input_refs.join(", ");
                        let arity = inputs.len();
                        format!(
                            "{{ let __ins: [&[u8; 32]; {arity}] = [{ins}];\n\
                             {pad}    let __h = dregg_sp1_runtime::poseidon2_hash_many(&__ins);\n\
                             {pad}    assert!(__h == {out}, \"poseidon2_hash: hash != claimed output\");\n\
                             {pad}}}",
                            arity = arity,
                            ins = inputs_arr,
                            out = out_s,
                            pad = pad,
                        )
                    }
                };
                lines.push(format!("{}{}", pad, check));
            }
            Statement::Mutate(mutation) => {
                let target = &mutation.target;
                let operand = &mutation.operand;
                let op_str = match mutation.op {
                    MutateOp::SubAssign => format!("{} -= {};", target, operand),
                    MutateOp::AddAssign => format!("{} += {};", target, operand),
                    MutateOp::Assign => format!("{} = {};", target, operand),
                };
                lines.push(format!("{}{}", pad, op_str));
            }
            Statement::Match {
                discriminant, arms, ..
            } => {
                lines.push(format!("{}match {} {{", pad, discriminant));
                for arm in arms {
                    lines.push(format!("{}    {} => {{", pad, arm.pattern_tokens));
                    emit_sp1_statements(&arm.body, lines, indent + 2);
                    lines.push(format!("{}    }}", pad));
                }
                lines.push(format!("{}}}", pad));
            }
        }
    }
}
