//! Canonical verifier recipe for the additive, non-live exact FNSP-v3 relation.
//!
//! Descriptor JSON is a Lean-emission/provenance transport, never protocol identity.  The
//! executable program component is a recoverable fixed-record envelope containing the code-owned
//! relation id/version, canonical typed DescriptorIR-v2 bytes, semantic manifest, and ordered host
//! ABI.  The AIR family and source/build-recipe provenance occupy independent recipe components.

use std::sync::OnceLock;

use dregg_circuit::descriptor_by_name::descriptor_by_name;
use dregg_circuit::descriptor_ir2::{EffectVmDescriptor2, parse_vm_descriptor2};
use dregg_circuit::descriptor_ir2_canonical::{
    canonical_effect_vm_descriptor2_bytes, decode_canonical_effect_vm_descriptor2,
};

/// Lean-emitted descriptor from which the canonical executable relation envelope is generated.
/// The staged compatibility wrapper and the turn verifier both execute this same typed relation.
pub const EXECUTABLE_DESCRIPTOR_JSON: &str = include_str!(
    "../../circuit/staged-descriptors/fnsp-v3/faithful-note-spend-exact-aafi-fns3-rotated-wide-state.json"
);

/// Exact bytes served by the production by-name descriptor table.  Provenance only.
pub const PRODUCTION_DESCRIPTOR_JSON: &str =
    include_str!("../../circuit/descriptors/by-name/faithful-note-spend-exact-v3.json");

pub const PREDICATE_NAME: &str = "faithful-note-spend-v3-plan::exact-aafi-fns3-rotated-wide-state";
pub const PLONKY3_REV: &str = "82cfad73cd734d37a0d51953094f970c531817ec";

pub const RELATION_ID: &str = "dregg.faithful-note-spend-exact";
pub const RELATION_VERSION: u32 = 3;
const RELATION_ENVELOPE_MAGIC: &[u8; 8] = b"FNS3REL\0";
const RELATION_ENVELOPE_VERSION: u32 = 1;
pub const MAX_RELATION_PROGRAM_BYTES: usize = 4 * 1024 * 1024;
const MAX_RELATION_ID_BYTES: usize = 256;
const MAX_CANONICAL_DESCRIPTOR_BYTES: usize = MAX_RELATION_PROGRAM_BYTES - 64 * 1024;
const MAX_SEMANTIC_MANIFEST_BYTES: usize = 16 * 1024;
const MAX_PUBLIC_ABI_SLOTS: usize = 256;
const MAX_PUBLIC_ABI_TEXT_BYTES: usize = 256;
const MIN_ENCODED_ABI_SLOT_BYTES: usize = 8 + 4 + 4 + 8;

/// Human-auditable executable contract layered over the exhaustive typed descriptor encoding.
pub const SEMANTIC_RELATION_MANIFEST: &str = concat!(
    "exact FNSP-v3 note spend; historical note membership; signed nullifier/value/asset binding; ",
    "AAFI append at a proved free index; prior/successor native root8 and u64 counts; ",
    "FNS3 state commitments; rotated before/after outer state commitments"
);

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct PublicAbiSlot {
    pub name: &'static str,
    pub offset: u32,
    pub length_in_felts: u32,
    pub encoding: &'static str,
}

/// Exact ordered 76-lane signed-effect/anchor ABI consumed by the verifier-facing relation.
pub const PUBLIC_ABI: &[PublicAbiSlot] = &[
    PublicAbiSlot {
        name: "historical_height",
        offset: 0,
        length_in_felts: 4,
        encoding: "u64-le-u16x4",
    },
    PublicAbiSlot {
        name: "historical_note_root",
        offset: 4,
        length_in_felts: 8,
        encoding: "babybear-root8",
    },
    PublicAbiSlot {
        name: "nullifier",
        offset: 12,
        length_in_felts: 16,
        encoding: "bytes32-le-u16x16",
    },
    PublicAbiSlot {
        name: "value",
        offset: 28,
        length_in_felts: 4,
        encoding: "u64-le-u16x4",
    },
    PublicAbiSlot {
        name: "asset_type",
        offset: 32,
        length_in_felts: 4,
        encoding: "u64-le-u16x4",
    },
    PublicAbiSlot {
        name: "successor_exact_root",
        offset: 36,
        length_in_felts: 8,
        encoding: "babybear-root8",
    },
    PublicAbiSlot {
        name: "prior_exact_root",
        offset: 44,
        length_in_felts: 8,
        encoding: "babybear-root8",
    },
    PublicAbiSlot {
        name: "pre_count",
        offset: 52,
        length_in_felts: 4,
        encoding: "u64-le-u16x4",
    },
    PublicAbiSlot {
        name: "post_count",
        offset: 56,
        length_in_felts: 4,
        encoding: "u64-le-u16x4",
    },
    PublicAbiSlot {
        name: "before_outer_commit",
        offset: 60,
        length_in_felts: 8,
        encoding: "babybear-digest8",
    },
    PublicAbiSlot {
        name: "after_outer_commit",
        offset: 68,
        length_in_felts: 8,
        encoding: "babybear-digest8",
    },
];

const EXPECTED_TRACE_WIDTH: usize = 3760;
const EXPECTED_PUBLIC_INPUTS: usize = 76;
const EXPECTED_CONSTRAINTS: usize = 1258;

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct DecodedPublicAbiSlot {
    pub name: String,
    pub offset: u32,
    pub length_in_felts: u32,
    pub encoding: String,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct DecodedRelationProgram {
    pub relation_id: String,
    pub relation_version: u32,
    pub descriptor: EffectVmDescriptor2,
    pub semantic_manifest: String,
    pub public_abi: Vec<DecodedPublicAbiSlot>,
}

fn executable_descriptor() -> Result<EffectVmDescriptor2, String> {
    let descriptor = parse_vm_descriptor2(EXECUTABLE_DESCRIPTOR_JSON)?;
    if descriptor.name != PREDICATE_NAME
        || descriptor.trace_width != EXPECTED_TRACE_WIDTH
        || descriptor.public_input_count != EXPECTED_PUBLIC_INPUTS
        || descriptor.constraints.len() != EXPECTED_CONSTRAINTS
    {
        return Err("executable exact FNSP-v3 descriptor shape drifted".to_owned());
    }
    Ok(descriptor)
}

/// CI/provenance validation only.  Raw equality and the by-name table are deliberately absent
/// from every protocol identity function below.
pub fn validate_provenance() -> Result<EffectVmDescriptor2, String> {
    if EXECUTABLE_DESCRIPTOR_JSON.as_bytes() != PRODUCTION_DESCRIPTOR_JSON.as_bytes() {
        return Err("production exact FNSP-v3 descriptor differs from executable emission".into());
    }
    let executable = executable_descriptor()?;
    let production = parse_vm_descriptor2(PRODUCTION_DESCRIPTOR_JSON)?;
    let by_name = descriptor_by_name(PREDICATE_NAME)
        .ok_or_else(|| "production exact FNSP-v3 by-name route is absent".to_owned())?;
    if executable != production || executable != by_name {
        return Err("production/by-name exact FNSP-v3 semantics differ from executable".into());
    }
    Ok(executable)
}

fn push_len_prefixed(out: &mut Vec<u8>, bytes: &[u8]) {
    out.extend_from_slice(&(bytes.len() as u64).to_le_bytes());
    out.extend_from_slice(bytes);
}

fn encode_relation_program_for(
    descriptor: &EffectVmDescriptor2,
    relation_id: &str,
    relation_version: u32,
    manifest: &str,
    abi: &[PublicAbiSlot],
) -> Result<Vec<u8>, String> {
    if relation_id.len() > MAX_RELATION_ID_BYTES {
        return Err("exact FNSP-v3 relation id exceeds envelope bound".to_owned());
    }
    if manifest.len() > MAX_SEMANTIC_MANIFEST_BYTES {
        return Err("exact FNSP-v3 semantic manifest exceeds envelope bound".to_owned());
    }
    if abi.len() > MAX_PUBLIC_ABI_SLOTS {
        return Err("exact FNSP-v3 public ABI exceeds slot bound".to_owned());
    }
    if abi.iter().any(|slot| {
        slot.name.len() > MAX_PUBLIC_ABI_TEXT_BYTES
            || slot.encoding.len() > MAX_PUBLIC_ABI_TEXT_BYTES
    }) {
        return Err("exact FNSP-v3 public ABI text exceeds envelope bound".to_owned());
    }
    let descriptor_bytes = canonical_effect_vm_descriptor2_bytes(descriptor)
        .map_err(|error| format!("canonical DescriptorIR-v2 encoding failed: {error}"))?;
    if descriptor_bytes.len() > MAX_CANONICAL_DESCRIPTOR_BYTES {
        return Err("canonical exact FNSP-v3 descriptor exceeds envelope bound".to_owned());
    }
    let mut out = Vec::with_capacity(descriptor_bytes.len() + manifest.len() + 512);
    out.extend_from_slice(RELATION_ENVELOPE_MAGIC);
    out.extend_from_slice(&RELATION_ENVELOPE_VERSION.to_le_bytes());
    push_len_prefixed(&mut out, relation_id.as_bytes());
    out.extend_from_slice(&relation_version.to_le_bytes());
    push_len_prefixed(&mut out, &descriptor_bytes);
    push_len_prefixed(&mut out, manifest.as_bytes());
    out.extend_from_slice(&(abi.len() as u64).to_le_bytes());
    for slot in abi {
        push_len_prefixed(&mut out, slot.name.as_bytes());
        out.extend_from_slice(&slot.offset.to_le_bytes());
        out.extend_from_slice(&slot.length_in_felts.to_le_bytes());
        push_len_prefixed(&mut out, slot.encoding.as_bytes());
    }
    if out.len() > MAX_RELATION_PROGRAM_BYTES {
        return Err("exact FNSP-v3 relation envelope exceeds total bound".to_owned());
    }
    Ok(out)
}

/// Canonically envelope alternate parsed bytes under the fixed exact-FNSP relation/ABI contract.
/// Primarily useful for proving that equivalent source encodings resolve to one program identity.
pub fn relation_program_bytes_for_descriptor(
    descriptor: &EffectVmDescriptor2,
) -> Result<Vec<u8>, String> {
    encode_relation_program_for(
        descriptor,
        RELATION_ID,
        RELATION_VERSION,
        SEMANTIC_RELATION_MANIFEST,
        PUBLIC_ABI,
    )
}

static RELATION_PROGRAM_BYTES: OnceLock<Vec<u8>> = OnceLock::new();

/// Canonical, recoverable executable relation envelope used as `VkComponents.program_bytes`.
pub fn relation_program_bytes() -> &'static [u8] {
    RELATION_PROGRAM_BYTES
        .get_or_init(|| {
            relation_program_bytes_for_descriptor(
                &executable_descriptor()
                    .expect("code-owned executable exact FNSP-v3 descriptor must remain valid"),
            )
            .expect("code-owned exact FNSP-v3 relation must canonically encode")
        })
        .as_slice()
}

struct Cursor<'a> {
    bytes: &'a [u8],
    offset: usize,
}

impl<'a> Cursor<'a> {
    fn remaining(&self) -> usize {
        self.bytes.len() - self.offset
    }

    fn take(&mut self, length: usize) -> Result<&'a [u8], String> {
        let end = self
            .offset
            .checked_add(length)
            .ok_or_else(|| "relation envelope offset overflow".to_owned())?;
        let bytes = self
            .bytes
            .get(self.offset..end)
            .ok_or_else(|| "truncated relation envelope".to_owned())?;
        self.offset = end;
        Ok(bytes)
    }

    fn u32(&mut self) -> Result<u32, String> {
        Ok(u32::from_le_bytes(
            self.take(4)?.try_into().expect("four bytes"),
        ))
    }

    fn u64(&mut self) -> Result<u64, String> {
        Ok(u64::from_le_bytes(
            self.take(8)?.try_into().expect("eight bytes"),
        ))
    }

    fn len_prefixed_bounded(&mut self, field: &str, maximum: usize) -> Result<&'a [u8], String> {
        let length = usize::try_from(self.u64()?)
            .map_err(|_| "relation envelope length does not fit usize".to_owned())?;
        if length > maximum {
            return Err(format!("relation envelope {field} exceeds bound"));
        }
        self.take(length)
    }

    fn string(&mut self, field: &str, maximum: usize) -> Result<String, String> {
        std::str::from_utf8(self.len_prefixed_bounded(field, maximum)?)
            .map(str::to_owned)
            .map_err(|error| format!("relation envelope {field} is not UTF-8: {error}"))
    }

    fn finish(self) -> Result<(), String> {
        if self.offset == self.bytes.len() {
            Ok(())
        } else {
            Err("trailing bytes after relation envelope".to_owned())
        }
    }
}

/// Decode the complete executable relation recipe.  The nested descriptor decoder is the strict
/// inverse of the generic canonical DescriptorIR-v2 encoder, not a JSON parser.
pub fn decode_relation_program(bytes: &[u8]) -> Result<DecodedRelationProgram, String> {
    if bytes.len() > MAX_RELATION_PROGRAM_BYTES {
        return Err("exact FNSP-v3 relation envelope exceeds total bound".to_owned());
    }
    let mut cursor = Cursor { bytes, offset: 0 };
    if cursor.take(RELATION_ENVELOPE_MAGIC.len())? != RELATION_ENVELOPE_MAGIC {
        return Err("invalid exact FNSP-v3 relation-envelope magic".to_owned());
    }
    let envelope_version = cursor.u32()?;
    if envelope_version != RELATION_ENVELOPE_VERSION {
        return Err(format!(
            "unsupported exact FNSP-v3 relation-envelope version {envelope_version}"
        ));
    }
    let relation_id = cursor.string("relation id", MAX_RELATION_ID_BYTES)?;
    let relation_version = cursor.u32()?;
    let descriptor = decode_canonical_effect_vm_descriptor2(
        cursor.len_prefixed_bounded("canonical descriptor", MAX_CANONICAL_DESCRIPTOR_BYTES)?,
    )
    .map_err(|error| format!("canonical DescriptorIR-v2 decoding failed: {error}"))?;
    let semantic_manifest = cursor.string("semantic manifest", MAX_SEMANTIC_MANIFEST_BYTES)?;
    let abi_count = usize::try_from(cursor.u64()?)
        .map_err(|_| "public ABI count does not fit usize".to_owned())?;
    if abi_count > MAX_PUBLIC_ABI_SLOTS
        || abi_count > cursor.remaining() / MIN_ENCODED_ABI_SLOT_BYTES
    {
        return Err("public ABI count exceeds bounded remaining envelope".to_owned());
    }
    let mut public_abi = Vec::new();
    public_abi
        .try_reserve_exact(abi_count)
        .map_err(|_| "cannot allocate exact FNSP-v3 public ABI".to_owned())?;
    for _ in 0..abi_count {
        public_abi.push(DecodedPublicAbiSlot {
            name: cursor.string("public ABI name", MAX_PUBLIC_ABI_TEXT_BYTES)?,
            offset: cursor.u32()?,
            length_in_felts: cursor.u32()?,
            encoding: cursor.string("public ABI encoding", MAX_PUBLIC_ABI_TEXT_BYTES)?,
        });
    }
    cursor.finish()?;
    Ok(DecodedRelationProgram {
        relation_id,
        relation_version,
        descriptor,
        semantic_manifest,
        public_abi,
    })
}

fn public_abi_matches_exact(decoded: &[DecodedPublicAbiSlot]) -> bool {
    decoded.len() == PUBLIC_ABI.len()
        && decoded.iter().zip(PUBLIC_ABI).all(|(decoded, expected)| {
            decoded.name == expected.name
                && decoded.offset == expected.offset
                && decoded.length_in_felts == expected.length_in_felts
                && decoded.encoding == expected.encoding
        })
}

/// Decode and authenticate the fixed executable envelope contract, returning the exact typed
/// descriptor that proof verification must execute.  This does not consult descriptor JSON.
pub fn decode_exact_relation_program(bytes: &[u8]) -> Result<EffectVmDescriptor2, String> {
    let decoded = decode_relation_program(bytes)?;
    if decoded.relation_id != RELATION_ID
        || decoded.relation_version != RELATION_VERSION
        || decoded.semantic_manifest != SEMANTIC_RELATION_MANIFEST
        || !public_abi_matches_exact(&decoded.public_abi)
    {
        return Err("exact FNSP-v3 executable relation envelope contract differs".to_owned());
    }
    Ok(decoded.descriptor)
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct DescriptorIr2AirShape {
    air_id: &'static str,
    field: &'static str,
    permutation: &'static str,
    descriptor_wire_version: u32,
    trace_width: u32,
    public_inputs: u32,
    constraint_count: u32,
    batch_instance_degree_bits: &'static [u8],
}

const AIR_SHAPE: DescriptorIr2AirShape = DescriptorIr2AirShape {
    air_id: "descriptor-ir2-batch-air-v2",
    field: "BabyBear",
    permutation: "Poseidon2-W16-D4-rate8",
    descriptor_wire_version: 2,
    trace_width: EXPECTED_TRACE_WIDTH as u32,
    public_inputs: EXPECTED_PUBLIC_INPUTS as u32,
    constraint_count: EXPECTED_CONSTRAINTS as u32,
    batch_instance_degree_bits: &[5, 8, 11, 5],
};

const DESCRIPTOR_IR2_AIR_SOURCE: &[u8] = include_bytes!("../../circuit/src/descriptor_ir2.rs");
const LEAN_DESCRIPTOR_AIR_SOURCE: &[u8] =
    include_bytes!("../../circuit/src/lean_descriptor_air.rs");
const AIR_IMPLEMENTATION_SOURCES: &[(&str, &[u8])] = &[
    ("circuit/src/descriptor_ir2.rs", DESCRIPTOR_IR2_AIR_SOURCE),
    (
        "circuit/src/lean_descriptor_air.rs",
        LEAN_DESCRIPTOR_AIR_SOURCE,
    ),
];

fn air_fingerprint_for_parts(
    shape: DescriptorIr2AirShape,
    implementation_sources: &[(&str, &[u8])],
) -> [u8; 32] {
    let mut hasher = blake3::Hasher::new_derive_key("dregg-descriptor-ir2-air-shape-v1");
    hasher.update(&(implementation_sources.len() as u64).to_le_bytes());
    for (path, source) in implementation_sources {
        update_len_prefixed_hash(&mut hasher, path.as_bytes());
        update_len_prefixed_hash(&mut hasher, source);
    }
    for text in [shape.air_id, shape.field, shape.permutation] {
        hasher.update(&(text.len() as u64).to_le_bytes());
        hasher.update(text.as_bytes());
    }
    hasher.update(&shape.descriptor_wire_version.to_le_bytes());
    hasher.update(&shape.trace_width.to_le_bytes());
    hasher.update(&shape.public_inputs.to_le_bytes());
    hasher.update(&shape.constraint_count.to_le_bytes());
    hasher.update(&(shape.batch_instance_degree_bits.len() as u64).to_le_bytes());
    hasher.update(shape.batch_instance_degree_bits);
    *hasher.finalize().as_bytes()
}

fn air_fingerprint_for_shape(shape: DescriptorIr2AirShape) -> [u8; 32] {
    air_fingerprint_for_parts(shape, AIR_IMPLEMENTATION_SOURCES)
}

/// Independent identity of the actual generic DescriptorIR-v2 AIR/interpreter sources plus fixed
/// execution shape.  The particular relation payload lives only in `relation_program_bytes()`.
pub fn air_fingerprint() -> [u8; 32] {
    air_fingerprint_for_shape(AIR_SHAPE)
}

const EXACT_VERIFIER_SOURCE: &[u8] = include_bytes!("faithful_note_spend_exact_v3.rs");
const IDENTITY_ENVELOPE_SOURCE: &[u8] = include_bytes!("faithful_note_spend_exact_v3_identity.rs");
const CANONICAL_DESCRIPTOR_CODEC_SOURCE: &[u8] =
    include_bytes!("../../circuit/src/descriptor_ir2_canonical.rs");
const STARK_ZK_CONFIG_SOURCE: &[u8] = include_bytes!("../../circuit/src/stark_zk.rs");
const DESCRIPTOR_IR2_VERIFIER_SOURCE: &[u8] = include_bytes!("../../circuit/src/descriptor_ir2.rs");
const LEAN_DESCRIPTOR_VERIFIER_SOURCE: &[u8] =
    include_bytes!("../../circuit/src/lean_descriptor_air.rs");
const TURN_STATEMENT_ADAPTER_SOURCE: &[u8] =
    include_bytes!("../../turn/src/faithful_note_spend_exact_v3.rs");
// The exact-v3 verifier wrapper now lives in `dregg-turn-prover` (the crate that
// IS the prover), not behind `dregg-turn`'s `prover` feature. `include_bytes!` is a
// source read, not a cargo dependency, so this does not create a
// circuit-prove -> turn-prover crate edge; it just keeps the fingerprint pointed at
// where the verifier actually is. Moving the file DID change this fingerprint (the
// closure is a hash of the exact bytes) — legitimate, because the verifier source
// genuinely changed, and this recipe is explicitly non-live with no compiled VK or
// wasm artifact claimed.
const TURN_VERIFIER_WRAPPER_SOURCE: &[u8] =
    include_bytes!("../../turn-prover/src/faithful_note_spend_exact_v3_verifier.rs");

const VERIFIER_SOURCE_CLOSURE: &[(&str, &[u8])] = &[
    (
        "circuit-prove/src/faithful_note_spend_exact_v3_identity.rs",
        IDENTITY_ENVELOPE_SOURCE,
    ),
    (
        "circuit/src/descriptor_ir2_canonical.rs",
        CANONICAL_DESCRIPTOR_CODEC_SOURCE,
    ),
    (
        "circuit-prove/src/faithful_note_spend_exact_v3.rs",
        EXACT_VERIFIER_SOURCE,
    ),
    ("circuit/src/stark_zk.rs", STARK_ZK_CONFIG_SOURCE),
    (
        "circuit/src/descriptor_ir2.rs",
        DESCRIPTOR_IR2_VERIFIER_SOURCE,
    ),
    (
        "circuit/src/lean_descriptor_air.rs",
        LEAN_DESCRIPTOR_VERIFIER_SOURCE,
    ),
    (
        "turn/src/faithful_note_spend_exact_v3.rs",
        TURN_STATEMENT_ADAPTER_SOURCE,
    ),
    (
        "turn-prover/src/faithful_note_spend_exact_v3_verifier.rs",
        TURN_VERIFIER_WRAPPER_SOURCE,
    ),
];

fn update_len_prefixed_hash(hasher: &mut blake3::Hasher, bytes: &[u8]) {
    hasher.update(&(bytes.len() as u64).to_le_bytes());
    hasher.update(bytes);
}

fn verifier_source_closure_fingerprint_for(sources: &[(&str, &[u8])]) -> [u8; 32] {
    let mut hasher = blake3::Hasher::new_derive_key("dregg-fnsp-v3-verifier-source-closure-v1");
    hasher.update(&(sources.len() as u64).to_le_bytes());
    for (path, source) in sources {
        update_len_prefixed_hash(&mut hasher, path.as_bytes());
        update_len_prefixed_hash(&mut hasher, source);
    }
    *hasher.finalize().as_bytes()
}

/// Build-recipe/source-closure provenance for the executable-envelope identity/codec, verifier,
/// HidingFRI config, generic DescriptorIR interpreter, and both turn-side host adapters.
/// `SourceHash` does **not** authenticate compiled behavior absent reproducible-build/translation
/// evidence; no compiled VK or wasm exists here.
pub fn verifier_source_closure_fingerprint() -> [u8; 32] {
    verifier_source_closure_fingerprint_for(VERIFIER_SOURCE_CLOSURE)
}

pub fn proving_system_canonical_bytes() -> Vec<u8> {
    let mut bytes = vec![0];
    bytes.extend_from_slice(&(PLONKY3_REV.len() as u64).to_le_bytes());
    bytes.extend_from_slice(PLONKY3_REV.as_bytes());
    bytes
}

#[cfg(test)]
mod tests {
    use super::*;

    const EXECUTABLE_HEADER: &str = concat!(
        "{\"name\":\"faithful-note-spend-v3-plan::exact-aafi-fns3-rotated-wide-state\",",
        "\"ir\":2,\"trace_width\":3760,\"public_input_count\":76,"
    );

    fn whitespace_and_top_level_key_reordered_json() -> String {
        let body = EXECUTABLE_DESCRIPTOR_JSON
            .strip_prefix(EXECUTABLE_HEADER)
            .expect("executable descriptor header remains recognized");
        format!(
            "{{\n  \"public_input_count\" : 76,\n  \"trace_width\" : 3760,\n  \
             \"name\" : \"{PREDICATE_NAME}\",\n  \"ir\" : 2,\n  {body}\n"
        )
    }

    fn decoded_expected_abi() -> Vec<DecodedPublicAbiSlot> {
        PUBLIC_ABI
            .iter()
            .map(|slot| DecodedPublicAbiSlot {
                name: slot.name.to_owned(),
                offset: slot.offset,
                length_in_felts: slot.length_in_felts,
                encoding: slot.encoding.to_owned(),
            })
            .collect()
    }

    #[test]
    fn production_route_is_provenance_identical_to_executed_emission() {
        assert_eq!(
            PRODUCTION_DESCRIPTOR_JSON.as_bytes(),
            EXECUTABLE_DESCRIPTOR_JSON.as_bytes()
        );
        validate_provenance().expect("production provenance validates");
    }

    #[test]
    fn executable_relation_envelope_recovers_exact_descriptor_manifest_and_abi() {
        let executable = executable_descriptor().expect("executable descriptor");
        let decoded = decode_relation_program(relation_program_bytes()).expect("relation decodes");
        assert_eq!(decoded.relation_id, RELATION_ID);
        assert_eq!(decoded.relation_version, RELATION_VERSION);
        assert_eq!(decoded.descriptor, executable);
        assert_eq!(decoded.semantic_manifest, SEMANTIC_RELATION_MANIFEST);
        assert_eq!(decoded.public_abi, decoded_expected_abi());
        assert!(!relation_program_bytes().starts_with(b"{"));
    }

    #[test]
    fn json_whitespace_and_key_order_do_not_change_typed_program_identity() {
        let canonical = executable_descriptor().expect("executable descriptor");
        let alternate = parse_vm_descriptor2(&whitespace_and_top_level_key_reordered_json())
            .expect("equivalent reordered JSON parses");
        assert_eq!(canonical, alternate);
        assert_eq!(
            canonical_effect_vm_descriptor2_bytes(&canonical).expect("canonical encoding"),
            canonical_effect_vm_descriptor2_bytes(&alternate).expect("canonical encoding")
        );
        assert_eq!(
            relation_program_bytes(),
            encode_relation_program_for(
                &alternate,
                RELATION_ID,
                RELATION_VERSION,
                SEMANTIC_RELATION_MANIFEST,
                PUBLIC_ABI,
            )
            .expect("alternate relation encodes")
        );
    }

    #[test]
    fn relation_constraint_abi_and_version_mutations_change_program_bytes() {
        let descriptor = executable_descriptor().expect("executable descriptor");
        let baseline = relation_program_bytes();

        let mut changed_constraint = descriptor.clone();
        changed_constraint
            .constraints
            .pop()
            .expect("nonempty constraints");
        assert_ne!(
            baseline,
            encode_relation_program_for(
                &changed_constraint,
                RELATION_ID,
                RELATION_VERSION,
                SEMANTIC_RELATION_MANIFEST,
                PUBLIC_ABI,
            )
            .expect("changed relation encodes")
        );

        let mut changed_abi = PUBLIC_ABI.to_vec();
        changed_abi[0].length_in_felts += 1;
        let changed_abi_program = encode_relation_program_for(
            &descriptor,
            RELATION_ID,
            RELATION_VERSION,
            SEMANTIC_RELATION_MANIFEST,
            &changed_abi,
        )
        .expect("changed ABI encodes");
        assert_ne!(baseline, changed_abi_program);
        assert!(decode_exact_relation_program(&changed_abi_program).is_err());
        let changed_version_program = encode_relation_program_for(
            &descriptor,
            RELATION_ID,
            RELATION_VERSION + 1,
            SEMANTIC_RELATION_MANIFEST,
            PUBLIC_ABI,
        )
        .expect("changed version encodes");
        assert_ne!(baseline, changed_version_program);
        assert!(decode_exact_relation_program(&changed_version_program).is_err());
    }

    #[test]
    fn air_shape_identity_is_independent_of_relation_payload_and_has_teeth() {
        let baseline = air_fingerprint();
        let mut changed = AIR_SHAPE;
        changed.trace_width += 1;
        assert_ne!(baseline, air_fingerprint_for_shape(changed));
        changed = AIR_SHAPE;
        changed.air_id = "different-descriptor-air";
        assert_ne!(baseline, air_fingerprint_for_shape(changed));

        let mut changed_air_source = DESCRIPTOR_IR2_AIR_SOURCE.to_vec();
        changed_air_source.push(b'\n');
        let changed_sources = [
            (
                "circuit/src/descriptor_ir2.rs",
                changed_air_source.as_slice(),
            ),
            (
                "circuit/src/lean_descriptor_air.rs",
                LEAN_DESCRIPTOR_AIR_SOURCE,
            ),
        ];
        assert_ne!(
            baseline,
            air_fingerprint_for_parts(AIR_SHAPE, &changed_sources)
        );

        let descriptor = executable_descriptor().expect("executable descriptor");
        let mut relation_mutation = descriptor.clone();
        relation_mutation.constraints.pop();
        assert_eq!(baseline, air_fingerprint());
        assert_ne!(
            relation_program_bytes(),
            encode_relation_program_for(
                &relation_mutation,
                RELATION_ID,
                RELATION_VERSION,
                SEMANTIC_RELATION_MANIFEST,
                PUBLIC_ABI,
            )
            .expect("relation mutation encodes")
        );
    }

    #[test]
    fn source_hash_binds_each_actual_source_leg_as_provenance() {
        let baseline = verifier_source_closure_fingerprint();
        assert!(
            STARK_ZK_CONFIG_SOURCE
                .windows(b"ZK_FRI_NUM_QUERIES".len())
                .any(|window| window == b"ZK_FRI_NUM_QUERIES")
        );
        for index in 0..VERIFIER_SOURCE_CLOSURE.len() {
            let mut mutated_source = VERIFIER_SOURCE_CLOSURE[index].1.to_vec();
            mutated_source.push(b'\n');
            let mut mutated_closure = VERIFIER_SOURCE_CLOSURE.to_vec();
            mutated_closure[index].1 = &mutated_source;
            assert_ne!(
                baseline,
                verifier_source_closure_fingerprint_for(&mutated_closure),
                "source leg {} must move SourceHash",
                VERIFIER_SOURCE_CLOSURE[index].0
            );
        }
    }

    #[test]
    fn relation_decoder_refuses_oversize_huge_counts_and_trailing_bytes() {
        assert!(decode_relation_program(&vec![0; MAX_RELATION_PROGRAM_BYTES + 1]).is_err());

        let mut huge_relation_id = relation_program_bytes().to_vec();
        huge_relation_id[12..20].copy_from_slice(&u64::MAX.to_le_bytes());
        assert!(decode_relation_program(&huge_relation_id).is_err());

        let mut huge_abi_count = relation_program_bytes().to_vec();
        let mut offset = RELATION_ENVELOPE_MAGIC.len() + 4;
        let relation_id_len = u64::from_le_bytes(
            huge_abi_count[offset..offset + 8]
                .try_into()
                .expect("relation id length"),
        ) as usize;
        offset += 8 + relation_id_len + 4;
        let descriptor_len = u64::from_le_bytes(
            huge_abi_count[offset..offset + 8]
                .try_into()
                .expect("descriptor length"),
        ) as usize;
        offset += 8 + descriptor_len;
        let manifest_len = u64::from_le_bytes(
            huge_abi_count[offset..offset + 8]
                .try_into()
                .expect("manifest length"),
        ) as usize;
        offset += 8 + manifest_len;
        huge_abi_count[offset..offset + 8].copy_from_slice(&u64::MAX.to_le_bytes());
        assert!(decode_relation_program(&huge_abi_count).is_err());

        let mut trailing = relation_program_bytes().to_vec();
        trailing.push(0);
        assert!(decode_relation_program(&trailing).is_err());
    }
}
