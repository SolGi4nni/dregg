// Per-variant Effect wire differential — the drift killer for the FULL enum.
//
// For EVERY newly modeled `Effect` kind (Rust declaration indexes 7..=33 plus
// a smoke re-check of 0..=6), this builds a turn in TS carrying that effect,
// hands the SAME turn (serde-JSON form) to the repo's own dregg-wasm build
// (the actual Rust `dregg-turn` code), and asserts:
//
//   - BYTE EQUALITY of the TS postcard `Turn` encoding vs the Rust
//     `postcard::to_allocvec` re-encode (`sign_turn_v3` output) — the
//     postcard-layout half;
//   - EQUALITY of the TS `turnHash` vs the Rust canonical `Turn::hash` (v3)
//     — which folds `CallForest::compute_hash` → `Action::hash` →
//     `Effect::hash`, so this half verifies the TS `effectHash` preimage of
//     the variant under test against the REAL Rust hash.
//
// Actions here carry a dummy `Authorization::Signature` (NOT Unchecked), so
// the oracle skips signing and performs a PURE re-encode: these tests isolate
// wire layout + hash preimages. The signing differentials live in
// `wire.test.mjs` (unchanged).
//
// ⚠ ORACLE FRESHNESS: `loadWasmOracle` fails loud when `wasm/pkg` is absent.
// These tests were validated against the pkg built 2026-07-16 15:49; the
// wire-relevant sources (turn/, types/, cell wire structs) had NO shape
// changes between that build and the tree these tests landed in (verified by
// git log over the specific files). Rebuild via `npm run build:oracle` when
// in doubt — a stale oracle proves nothing about NEW Rust variants.

import { test } from "node:test";
import assert from "node:assert/strict";

import { loadWasmOracle, hex, raw } from "./helpers.mjs";

const b32 = (n) => Uint8Array.from({ length: 32 }, () => n & 0xff);
const b64 = (n) => Uint8Array.from({ length: 64 }, () => n & 0xff);
const blob = (n, len) => Uint8Array.from({ length: len }, (_, i) => (n + i) & 0xff);
const arr = (b) => Array.from(b);

// ─── serde-JSON forms (externally tagged Rust enums, snake_case fields) ─────

function authRequiredToJson(a) {
  switch (a.kind) {
    case "none":
      return "None";
    case "signature":
      return "Signature";
    case "proof":
      return "Proof";
    case "either":
      return "Either";
    case "impossible":
      return "Impossible";
    case "custom":
      return { Custom: { vk_hash: arr(a.vkHash) } };
    default:
      throw new Error(`no JSON for AuthRequired ${a.kind}`);
  }
}

function permissionsToJson(p) {
  return {
    send: authRequiredToJson(p.send),
    receive: authRequiredToJson(p.receive),
    set_state: authRequiredToJson(p.setState),
    set_permissions: authRequiredToJson(p.setPermissions),
    set_verification_key: authRequiredToJson(p.setVerificationKey),
    increment_nonce: authRequiredToJson(p.incrementNonce),
    delegate: authRequiredToJson(p.delegate),
    access: authRequiredToJson(p.access),
  };
}

function simpleConstraintToJson(c) {
  switch (c.kind) {
    case "fieldEquals":
      return { FieldEquals: { index: c.index, value: arr(c.value) } };
    case "writeOnce":
      return { WriteOnce: { index: c.index } };
    case "senderIs":
      return { SenderIs: { pk: arr(c.pk) } };
    case "not":
      return { Not: simpleConstraintToJson(c.inner) };
    default:
      throw new Error(`no JSON for SimpleStateConstraint ${c.kind}`);
  }
}

function stateConstraintToJson(c) {
  switch (c.kind) {
    case "fieldEquals":
      return { FieldEquals: { index: c.index, value: arr(c.value) } };
    case "writeOnce":
      return { WriteOnce: { index: c.index } };
    case "senderIs":
      return { SenderIs: { pk: arr(c.pk) } };
    case "balanceGte":
      return { BalanceGte: { min: Number(c.min) } };
    case "preimageGate":
      return {
        PreimageGate: {
          commitment_index: c.commitmentIndex,
          hash_kind: c.hashKind === "blake3" ? "Blake3" : "Poseidon2",
        },
      };
    case "anyOf":
      // StateConstraint::AnyOf is a STRUCT variant { variants } (postcard-
      // identical to a newtype seq, but the JSON form differs).
      return { AnyOf: { variants: c.variants.map(simpleConstraintToJson) } };
    default:
      throw new Error(`no JSON for StateConstraint ${c.kind}`);
  }
}

function cellProgramToJson(p) {
  switch (p.kind) {
    case "none":
      return "None";
    case "predicate":
      return { Predicate: p.constraints.map(stateConstraintToJson) };
    case "circuit":
      return { Circuit: { circuit_hash: arr(p.circuitHash) } };
    default:
      throw new Error(`no JSON for CellProgram ${p.kind}`);
  }
}

function refusalReasonToJson(r) {
  switch (r.kind) {
    case "declined":
      return "Declined";
    case "noAuthority":
      return "NoAuthority";
    case "windowExpired":
      return "WindowExpired";
    case "custom":
      return { Custom: { reason_hash: arr(r.reasonHash) } };
    default:
      throw new Error(`no JSON for RefusalReason ${r.kind}`);
  }
}

function deathReasonToJson(r) {
  switch (r.kind) {
    case "voluntary":
      return "Voluntary";
    case "forced":
      return "Forced";
    case "migrated":
      return "Migrated";
    case "custom":
      return { Custom: { reason_hash: arr(r.reasonHash) } };
    default:
      throw new Error(`no JSON for DeathReason ${r.kind}`);
  }
}

function capTargetToJson(t) {
  switch (t.kind) {
    case "selfCell":
      return "SelfCell";
    case "specific":
      return { Specific: arr(t.cell) };
    case "any":
      return "Any";
    default:
      throw new Error(`no JSON for CapTarget ${t.kind}`);
  }
}

function attestedRootToJson(r) {
  return {
    merkle_root: arr(r.merkleRoot),
    note_tree_root: r.noteTreeRoot ? arr(r.noteTreeRoot) : null,
    nullifier_set_root: r.nullifierSetRoot ? arr(r.nullifierSetRoot) : null,
    height: Number(r.height),
    timestamp: Number(r.timestamp),
    blocklace_block_id: r.blocklaceBlockId ? arr(r.blocklaceBlockId) : null,
    finality_round: r.finalityRound !== undefined ? Number(r.finalityRound) : null,
    quorum_signatures: r.quorumSignatures.map(([pk, sig]) => [arr(pk), arr(sig)]),
    threshold_qc: r.thresholdQc ? arr(r.thresholdQc) : null,
    threshold: r.threshold,
    federation_id: arr(r.federationId),
    receipt_stream_root: r.receiptStreamRoot ? arr(r.receiptStreamRoot) : null,
    hybrid_quorum: r.hybridQuorum.map((h) => ({
      pubkey: arr(h.pubkey),
      signature: arr(h.signature),
      ml_dsa_pubkey: arr(h.mlDsaPubkey),
      pq_signature: arr(h.pqSignature),
    })),
  };
}

function proofConditionToJson(c) {
  switch (c.kind) {
    case "hashPreimage":
      return { HashPreimage: { hash: arr(c.hash) } };
    case "remoteProof":
      return {
        RemoteProof: {
          federation_root: arr(c.federationRoot),
          expected_air: c.expectedAir,
          expected_conclusion: c.expectedConclusion,
        },
      };
    case "localProof":
      return { LocalProof: { expected_air: c.expectedAir, expected_public_inputs: c.expectedPublicInputs } };
    case "turnExecuted":
      return { TurnExecuted: { turn_hash: arr(c.turnHash) } };
    default:
      throw new Error(`no JSON for ProofCondition ${c.kind}`);
  }
}

function resolutionConditionToJson(c) {
  switch (c.kind) {
    case "awaitReceipt":
      return {
        AwaitReceipt: {
          turn_hash: arr(c.turnHash),
          federation_id: c.federationId ? arr(c.federationId) : null,
        },
      };
    case "awaitCondition":
      return { AwaitCondition: proofConditionToJson(c.condition) };
    case "awaitHeight":
      return { AwaitHeight: Number(c.height) };
    default:
      throw new Error(`no JSON for ResolutionCondition ${c.kind}`);
  }
}

function conditionProofToJson(p) {
  switch (p.kind) {
    case "preimage":
      return { Preimage: arr(p.preimage) };
    case "starkProof":
      return {
        StarkProof: {
          proof_bytes: arr(p.proofBytes),
          federation_root: arr(p.federationRoot),
          public_outputs: p.publicOutputs,
          air_name: p.airName,
        },
      };
    default:
      throw new Error(`no JSON for ConditionProof ${p.kind}`);
  }
}

function effectToJson(e) {
  switch (e.kind) {
    case "setField":
      return { SetField: { cell: arr(e.cell), index: e.index, value: arr(e.value) } };
    case "transfer":
      return { Transfer: { from: arr(e.from), to: arr(e.to), amount: Number(e.amount) } };
    case "grantCapability":
      return {
        GrantCapability: {
          from: arr(e.from),
          to: arr(e.to),
          cap: {
            target: arr(e.cap.target),
            slot: e.cap.slot,
            permissions: authRequiredToJson(e.cap.permissions),
            breadstuff: e.cap.breadstuff ? arr(e.cap.breadstuff) : null,
            expires_at: e.cap.expiresAt !== undefined ? Number(e.cap.expiresAt) : null,
            stored_epoch: e.cap.storedEpoch !== undefined ? Number(e.cap.storedEpoch) : null,
            provenance: arr(e.cap.provenance ?? new Uint8Array(32)),
          },
        },
      };
    case "revokeCapability":
      return { RevokeCapability: { cell: arr(e.cell), slot: e.slot } };
    case "emitEvent":
      return { EmitEvent: { cell: arr(e.cell), event: { topic: arr(e.topic), data: e.data.map(arr) } } };
    case "incrementNonce":
      return { IncrementNonce: { cell: arr(e.cell) } };
    case "createCell":
      return {
        CreateCell: { public_key: arr(e.publicKey), token_id: arr(e.tokenId), balance: Number(e.balance) },
      };
    case "setPermissions":
      return { SetPermissions: { cell: arr(e.cell), new_permissions: permissionsToJson(e.newPermissions) } };
    case "setVerificationKey":
      return {
        SetVerificationKey: {
          cell: arr(e.cell),
          new_vk: e.newVk ? { hash: arr(e.newVk.hash), data: arr(e.newVk.data) } : null,
        },
      };
    case "setProgram":
      return { SetProgram: { cell: arr(e.cell), program: cellProgramToJson(e.program) } };
    case "noteSpend":
      return {
        NoteSpend: {
          nullifier: arr(e.nullifier),
          note_tree_root: arr(e.noteTreeRoot),
          value: Number(e.value),
          asset_type: Number(e.assetType),
          spending_proof: arr(e.spendingProof),
          value_commitment: e.valueCommitment ? arr(e.valueCommitment) : null,
        },
      };
    case "noteCreate":
      return {
        NoteCreate: {
          commitment: arr(e.commitment),
          value: Number(e.value),
          asset_type: Number(e.assetType),
          encrypted_note: arr(e.encryptedNote),
          value_commitment: e.valueCommitment ? arr(e.valueCommitment) : null,
          range_proof: e.rangeProof ? arr(e.rangeProof) : null,
        },
      };
    case "spawnWithDelegation":
      return {
        SpawnWithDelegation: {
          child_public_key: arr(e.childPublicKey),
          child_token_id: arr(e.childTokenId),
          max_staleness: Number(e.maxStaleness),
        },
      };
    case "refreshDelegation":
      return { RefreshDelegation: { child: arr(e.child), snapshot: arr(e.snapshot) } };
    case "revokeDelegation":
      return { RevokeDelegation: { child: arr(e.child) } };
    case "bridgeMint":
      return {
        BridgeMint: {
          portable_proof: {
            nullifier: arr(e.portableProof.nullifier),
            destination_federation: arr(e.portableProof.destinationFederation),
            source_root: attestedRootToJson(e.portableProof.sourceRoot),
            spending_proof: arr(e.portableProof.spendingProof),
            destination_commitment: arr(e.portableProof.destinationCommitment),
            value: Number(e.portableProof.value),
            asset_type: Number(e.portableProof.assetType),
          },
        },
      };
    case "introduce":
      return {
        Introduce: {
          introducer: arr(e.introducer),
          recipient: arr(e.recipient),
          target: arr(e.target),
          permissions: authRequiredToJson(e.permissions),
        },
      };
    case "pipelinedSend":
      return {
        PipelinedSend: {
          target: {
            source_turn: arr(e.target.sourceTurn),
            output_slot: e.target.outputSlot,
            federation_id: e.target.federationId ? arr(e.target.federationId) : null,
          },
          action: actionToJson(e.action),
        },
      };
    case "exerciseViaCapability":
      return {
        ExerciseViaCapability: { cap_slot: e.capSlot, inner_effects: e.innerEffects.map(effectToJson) },
      };
    case "makeSovereign":
      return { MakeSovereign: { cell: arr(e.cell) } };
    case "createCellFromFactory":
      return {
        CreateCellFromFactory: {
          factory_vk: arr(e.factoryVk),
          owner_pubkey: arr(e.ownerPubkey),
          token_id: arr(e.tokenId),
          params: {
            mode: e.params.mode === "hosted" ? "Hosted" : "Sovereign",
            program_vk: e.params.programVk ? arr(e.params.programVk) : null,
            initial_fields: e.params.initialFields.map(([i, v]) => [i, Number(v)]),
            initial_caps: e.params.initialCaps.map((g) => ({
              target: capTargetToJson(g.target),
              max_permissions: authRequiredToJson(g.maxPermissions),
              attenuatable: g.attenuatable,
            })),
            owner_pubkey: arr(e.params.ownerPubkey),
          },
        },
      };
    case "refusal":
      return {
        Refusal: {
          cell: arr(e.cell),
          offered_action_commitment: arr(e.offeredActionCommitment),
          refusal_reason: refusalReasonToJson(e.refusalReason),
          proof_witness_index: e.proofWitnessIndex,
        },
      };
    case "cellSeal":
      return { CellSeal: { target: arr(e.target), reason: arr(e.reason) } };
    case "cellUnseal":
      return { CellUnseal: { target: arr(e.target) } };
    case "cellDestroy":
      return {
        CellDestroy: {
          target: arr(e.target),
          certificate: {
            cell_id: arr(e.certificate.cellId),
            last_receipt_hash: arr(e.certificate.lastReceiptHash),
            final_state_commitment: arr(e.certificate.finalStateCommitment),
            destroyed_at_height: Number(e.certificate.destroyedAtHeight),
            reason: deathReasonToJson(e.certificate.reason),
          },
        },
      };
    case "burn":
      return { Burn: { target: arr(e.target), slot: e.slot, amount: Number(e.amount) } };
    case "attenuateCapability":
      return {
        AttenuateCapability: {
          cell: arr(e.cell),
          slot: e.slot,
          narrower_permissions: authRequiredToJson(e.narrowerPermissions),
          narrower_effects: e.narrowerEffects !== undefined ? e.narrowerEffects : null,
          narrower_expiry: e.narrowerExpiry !== undefined ? Number(e.narrowerExpiry) : null,
        },
      };
    case "receiptArchive":
      return {
        ReceiptArchive: {
          prefix_end_height: Number(e.prefixEndHeight),
          checkpoint: {
            cell_id: arr(e.checkpoint.cellId),
            archive_start_height: Number(e.checkpoint.archiveStartHeight),
            archive_end_height: Number(e.checkpoint.archiveEndHeight),
            archive_blob_hash: arr(e.checkpoint.archiveBlobHash),
            archive_terminal_commitment: arr(e.checkpoint.archiveTerminalCommitment),
            archive_terminal_receipt_hash: arr(e.checkpoint.archiveTerminalReceiptHash),
          },
        },
      };
    case "promise":
      return {
        Promise: {
          cell: arr(e.cell),
          resolution_condition: resolutionConditionToJson(e.resolutionCondition),
          wake: turnToJson(e.wake),
          timeout_height: Number(e.timeoutHeight),
        },
      };
    case "notify":
      return {
        Notify: {
          from: arr(e.from),
          to: arr(e.to),
          wake: turnToJson(e.wake),
          resolution_condition: resolutionConditionToJson(e.resolutionCondition),
          timeout_height: Number(e.timeoutHeight),
        },
      };
    case "react":
      return {
        React: {
          pending_id: arr(e.pendingId),
          condition: proofConditionToJson(e.condition),
          resolution_proof: conditionProofToJson(e.resolutionProof),
          wake: turnToJson(e.wake),
        },
      };
    case "mint":
      return { Mint: { target: arr(e.target), slot: e.slot, amount: Number(e.amount) } };
    case "shieldedTransfer":
      return {
        ShieldedTransfer: {
          payload: {
            merkle_root: e.payload.merkleRoot,
            inputs: e.payload.inputs.map((i) => ({
              nullifier: i.nullifier,
              value_binding: i.valueBinding,
              proof: arr(i.proof),
            })),
            input_legs: e.payload.inputLegs.map((l) => ({
              asset_type: Number(l.assetType),
              commitment_bytes: arr(l.commitmentBytes),
            })),
            output_legs: e.payload.outputLegs.map((l) => ({
              asset_type: Number(l.assetType),
              commitment_bytes: arr(l.commitmentBytes),
            })),
            output_range_proofs: e.payload.outputRangeProofs.map(arr),
            conservation: {
              excess_commitment: arr(e.payload.conservation.excessCommitment),
              nonce_commitment: arr(e.payload.conservation.nonceCommitment),
              response: arr(e.payload.conservation.response),
            },
          },
        },
      };
    case "custom":
      return {
        Custom: {
          cell: arr(e.cell),
          program_vk_hash: arr(e.programVkHash),
          proof_commitment: arr(e.proofCommitment),
        },
      };
    default:
      throw new Error(`no JSON form for effect ${e.kind}`);
  }
}

function authToJson(a) {
  switch (a.kind) {
    case "signature":
      return { Signature: [arr(a.r), arr(a.s)] };
    case "unchecked":
      return "Unchecked";
    default:
      throw new Error(`no JSON form for authorization ${a.kind}`);
  }
}

function actionToJson(a) {
  return {
    target: arr(a.target),
    method: arr(a.method),
    args: a.args.map(arr),
    authorization: authToJson(a.authorization),
    preconditions: { cell_state: null, network: null, valid_while: null, witnessed: [] },
    effects: a.effects.map(effectToJson),
    may_delegate: "None",
    commitment_mode: "Full",
    balance_change: a.balanceChange !== undefined ? Number(a.balanceChange) : null,
    witness_blobs: [],
  };
}

function turnToJson(t) {
  return {
    agent: arr(t.agent),
    nonce: Number(t.nonce),
    call_forest: {
      roots: t.roots.map((r) => ({ action: actionToJson(r.action), children: [], hash: arr(new Uint8Array(32)) })),
      forest_hash: arr(new Uint8Array(32)),
    },
    fee: Number(t.fee),
    memo: t.memo ?? null,
    valid_until: t.validUntil !== undefined ? Number(t.validUntil) : null,
    previous_receipt_hash: t.previousReceiptHash ? arr(t.previousReceiptHash) : null,
    depends_on: (t.dependsOn ?? []).map(arr),
    conservation_proof: null,
    sovereign_witnesses: {},
    execution_proof: null,
    execution_proof_cell: null,
    execution_proof_new_commitment: null,
    custom_program_proofs: null,
    effect_binding_proofs: [],
    cross_effect_dependencies: [],
    effect_witness_index_map: [],
  };
}

// ─── fixtures ───────────────────────────────────────────────────────────────

/** Dummy classical signature (the oracle re-encodes without signing). */
const DUMMY_SIG = { kind: "signature", r: b32(0x51), s: b32(0x52) };

function signedAction(rawMod, target, effects) {
  const a = rawMod.unsignedActionNamed(target, "execute", effects);
  a.authorization = DUMMY_SIG;
  return a;
}

/** A minimal default-bundle wake turn (nested inside Promise/Notify/React). */
function wakeTurn(rawMod, agent) {
  return {
    agent,
    nonce: 3n,
    roots: [{ action: signedAction(rawMod, agent, [{ kind: "incrementNonce", cell: agent }]), children: [] }],
    fee: 5n,
  };
}

const PERMS_ALL_KINDS = {
  send: { kind: "signature" },
  receive: { kind: "none" },
  setState: { kind: "proof" },
  setPermissions: { kind: "either" },
  setVerificationKey: { kind: "impossible" },
  incrementNonce: { kind: "custom", vkHash: b32(0xc1) },
  delegate: { kind: "signature" },
  access: { kind: "none" },
};

function attestedRootFull() {
  return {
    merkleRoot: b32(0xa1),
    noteTreeRoot: b32(0xa2),
    nullifierSetRoot: b32(0xa3),
    height: 77n,
    timestamp: -12345n, // negative i64 exercises the zigzag encoding
    blocklaceBlockId: b32(0xa4),
    finalityRound: 9n,
    quorumSignatures: [[b32(0xb1), b64(0xb2)]],
    thresholdQc: blob(0xb3, 10),
    threshold: 2,
    federationId: b32(0xb4),
    receiptStreamRoot: b32(0xb5),
    hybridQuorum: [
      { pubkey: b32(0xc1), signature: b64(0xc2), mlDsaPubkey: blob(0xc3, 7), pqSignature: blob(0xc4, 9) },
    ],
  };
}

function attestedRootMinimal() {
  return {
    merkleRoot: b32(0xd1),
    height: 1n,
    timestamp: 1700000000n,
    quorumSignatures: [],
    threshold: 0,
    federationId: b32(0),
    hybridQuorum: [],
  };
}

/** One fixture per Effect kind — 34 total, sub-shape variations included. */
function fixtures(rawMod, agent, programMod) {
  return {
    setField: [{ kind: "setField", cell: agent, index: 3, value: rawMod.fieldFromU64(77n) }],
    transfer: [{ kind: "transfer", from: agent, to: b32(9), amount: 12345n }],
    grantCapability: [
      {
        kind: "grantCapability",
        from: agent,
        to: b32(8),
        cap: {
          target: b32(7),
          slot: 2,
          permissions: { kind: "signature" },
          expiresAt: 900n,
          provenance: rawMod.fieldFromU64(0xabcdefn),
        },
      },
    ],
    revokeCapability: [{ kind: "revokeCapability", cell: agent, slot: 5 }],
    emitEvent: [
      { kind: "emitEvent", cell: agent, topic: rawMod.symbol("ping"), data: [rawMod.fieldFromU64(1n)] },
    ],
    incrementNonce: [{ kind: "incrementNonce", cell: agent }],
    createCell: [{ kind: "createCell", publicKey: b32(0xaa), tokenId: b32(0xbb), balance: 500n }],
    setPermissions: [{ kind: "setPermissions", cell: agent, newPermissions: PERMS_ALL_KINDS }],
    setVerificationKey: [
      { kind: "setVerificationKey", cell: agent, newVk: { hash: b32(0x11), data: blob(0x12, 5) } },
      { kind: "setVerificationKey", cell: agent }, // None branch
    ],
    setProgram: [
      { kind: "setProgram", cell: agent, program: { kind: "none" } },
      {
        kind: "setProgram",
        cell: agent,
        program: {
          kind: "predicate",
          constraints: [
            programMod.fieldEquals(0, rawMod.fieldFromU64(42n)),
            programMod.writeOnce(1),
            programMod.senderIs(b32(0x21)),
            programMod.balanceGte(100n),
            programMod.preimageGate(2, "blake3"),
            programMod.anyOf([
              { kind: "writeOnce", index: 4 },
              { kind: "senderIs", pk: b32(0x23) },
              { kind: "not", inner: { kind: "fieldEquals", index: 5, value: rawMod.fieldFromU64(9n) } },
            ]),
          ],
        },
      },
      { kind: "setProgram", cell: agent, program: { kind: "circuit", circuitHash: b32(0x22) } },
    ],
    noteSpend: [
      {
        kind: "noteSpend",
        nullifier: b32(0x31),
        noteTreeRoot: b32(0x32),
        value: 44n,
        assetType: 2n,
        spendingProof: blob(0x33, 11),
        valueCommitment: b32(0x34),
      },
      {
        kind: "noteSpend",
        nullifier: b32(0x35),
        noteTreeRoot: b32(0x36),
        value: 1n,
        assetType: 0n,
        spendingProof: blob(0x37, 3),
      },
    ],
    noteCreate: [
      {
        kind: "noteCreate",
        commitment: b32(0x41),
        value: 7n,
        assetType: 1n,
        encryptedNote: blob(0x42, 13),
        valueCommitment: b32(0x43),
        rangeProof: blob(0x44, 6),
      },
      { kind: "noteCreate", commitment: b32(0x45), value: 2n, assetType: 0n, encryptedNote: blob(0x46, 4) },
    ],
    spawnWithDelegation: [
      { kind: "spawnWithDelegation", childPublicKey: b32(0x51), childTokenId: b32(0x52), maxStaleness: 3600n },
    ],
    refreshDelegation: [{ kind: "refreshDelegation", child: b32(0x53), snapshot: b32(0x54) }],
    revokeDelegation: [{ kind: "revokeDelegation", child: b32(0x55) }],
    bridgeMint: [
      {
        kind: "bridgeMint",
        portableProof: {
          nullifier: b32(0x61),
          destinationFederation: b32(0x62),
          sourceRoot: attestedRootFull(),
          spendingProof: blob(0x63, 15),
          destinationCommitment: b32(0x64),
          value: 88n,
          assetType: 3n,
        },
      },
      {
        kind: "bridgeMint",
        portableProof: {
          nullifier: b32(0x65),
          destinationFederation: b32(0x66),
          sourceRoot: attestedRootMinimal(),
          spendingProof: blob(0x67, 2),
          destinationCommitment: b32(0x68),
          value: 1n,
          assetType: 0n,
        },
      },
    ],
    introduce: [
      {
        kind: "introduce",
        introducer: agent,
        recipient: b32(0x71),
        target: b32(0x72),
        permissions: { kind: "custom", vkHash: b32(0x73) },
      },
    ],
    pipelinedSend: [
      {
        kind: "pipelinedSend",
        target: { sourceTurn: b32(0x74), outputSlot: 2, federationId: b32(0x75) },
        action: signedAction(rawMod, b32(0x76), [{ kind: "incrementNonce", cell: b32(0x76) }]),
      },
    ],
    exerciseViaCapability: [
      {
        kind: "exerciseViaCapability",
        capSlot: 4,
        innerEffects: [
          { kind: "transfer", from: agent, to: b32(0x81), amount: 10n },
          { kind: "burn", target: agent, slot: 0, amount: 5n },
        ],
      },
    ],
    makeSovereign: [{ kind: "makeSovereign", cell: agent }],
    createCellFromFactory: [
      {
        kind: "createCellFromFactory",
        factoryVk: b32(0x91),
        ownerPubkey: b32(0x92),
        tokenId: b32(0x93),
        params: {
          mode: "hosted",
          programVk: b32(0x94),
          initialFields: [
            [0, 5n],
            [3, 700n],
          ],
          initialCaps: [
            { target: { kind: "selfCell" }, maxPermissions: { kind: "signature" }, attenuatable: true },
            { target: { kind: "specific", cell: b32(0x95) }, maxPermissions: { kind: "none" }, attenuatable: false },
            { target: { kind: "any" }, maxPermissions: { kind: "custom", vkHash: b32(0x96) }, attenuatable: true },
          ],
          ownerPubkey: b32(0x92),
        },
      },
      {
        kind: "createCellFromFactory",
        factoryVk: b32(0x97),
        ownerPubkey: b32(0x98),
        tokenId: b32(0x99),
        params: { mode: "sovereign", initialFields: [], initialCaps: [], ownerPubkey: b32(0x98) },
      },
    ],
    refusal: [
      {
        kind: "refusal",
        cell: agent,
        offeredActionCommitment: b32(0xa1),
        refusalReason: { kind: "declined" },
        proofWitnessIndex: 0,
      },
      {
        kind: "refusal",
        cell: agent,
        offeredActionCommitment: b32(0xa2),
        refusalReason: { kind: "noAuthority" },
        proofWitnessIndex: 1,
      },
      {
        kind: "refusal",
        cell: agent,
        offeredActionCommitment: b32(0xa3),
        refusalReason: { kind: "windowExpired" },
        proofWitnessIndex: 2,
      },
      {
        kind: "refusal",
        cell: agent,
        offeredActionCommitment: b32(0xa4),
        refusalReason: { kind: "custom", reasonHash: b32(0xa5) },
        proofWitnessIndex: 3,
      },
    ],
    cellSeal: [{ kind: "cellSeal", target: agent, reason: b32(0xb1) }],
    cellUnseal: [{ kind: "cellUnseal", target: agent }],
    cellDestroy: [
      {
        kind: "cellDestroy",
        target: agent,
        certificate: {
          cellId: agent,
          lastReceiptHash: b32(0xb2),
          finalStateCommitment: b32(0xb3),
          destroyedAtHeight: 999n,
          reason: { kind: "voluntary" },
        },
      },
      {
        kind: "cellDestroy",
        target: agent,
        certificate: {
          cellId: agent,
          lastReceiptHash: b32(0xb4),
          finalStateCommitment: b32(0xb5),
          destroyedAtHeight: 1000n,
          reason: { kind: "custom", reasonHash: b32(0xb6) },
        },
      },
    ],
    burn: [{ kind: "burn", target: agent, slot: 0, amount: 250n }],
    attenuateCapability: [
      {
        kind: "attenuateCapability",
        cell: agent,
        slot: 1,
        narrowerPermissions: { kind: "signature" },
        narrowerEffects: 0b1010,
        narrowerExpiry: 5000n,
      },
      { kind: "attenuateCapability", cell: agent, slot: 2, narrowerPermissions: { kind: "impossible" } },
    ],
    receiptArchive: [
      {
        kind: "receiptArchive",
        prefixEndHeight: 40n,
        checkpoint: {
          cellId: agent,
          archiveStartHeight: 1n,
          archiveEndHeight: 40n,
          archiveBlobHash: b32(0xc1),
          archiveTerminalCommitment: b32(0xc2),
          archiveTerminalReceiptHash: b32(0xc3),
        },
      },
    ],
    promise: [
      {
        kind: "promise",
        cell: agent,
        resolutionCondition: { kind: "awaitReceipt", turnHash: b32(0xd1), federationId: b32(0xd2) },
        wake: wakeTurn(rawMod, agent),
        timeoutHeight: 100n,
      },
      {
        kind: "promise",
        cell: agent,
        resolutionCondition: { kind: "awaitHeight", height: 55n },
        wake: wakeTurn(rawMod, agent),
        timeoutHeight: 101n,
      },
    ],
    notify: [
      {
        kind: "notify",
        from: agent,
        to: b32(0xd3),
        wake: wakeTurn(rawMod, agent),
        resolutionCondition: {
          kind: "awaitCondition",
          condition: { kind: "localProof", expectedAir: "predicate-arith-ge::threshold-v1", expectedPublicInputs: [1, 2, 3] },
        },
        timeoutHeight: 102n,
      },
    ],
    react: [
      {
        kind: "react",
        pendingId: b32(0xd4),
        condition: { kind: "hashPreimage", hash: b32(0xd5) },
        resolutionProof: { kind: "preimage", preimage: b32(0xd6) },
        wake: wakeTurn(rawMod, agent),
      },
      {
        kind: "react",
        pendingId: b32(0xd7),
        condition: { kind: "remoteProof", federationRoot: b32(0xd8), expectedAir: "some-air", expectedConclusion: 7 },
        resolutionProof: {
          kind: "starkProof",
          proofBytes: blob(0xd9, 8),
          federationRoot: b32(0xda),
          publicOutputs: [4, 5],
          airName: "some-air",
        },
        wake: wakeTurn(rawMod, agent),
      },
    ],
    mint: [{ kind: "mint", target: agent, slot: 0, amount: 777n }],
    shieldedTransfer: [
      {
        kind: "shieldedTransfer",
        payload: {
          merkleRoot: 123456,
          inputs: [
            { nullifier: 11, valueBinding: 12, proof: blob(0xe1, 9) },
            { nullifier: 13, valueBinding: 14, proof: blob(0xe2, 5) },
          ],
          inputLegs: [
            { assetType: 1n, commitmentBytes: b32(0xe3) },
            { assetType: 1n, commitmentBytes: b32(0xe4) },
          ],
          outputLegs: [{ assetType: 1n, commitmentBytes: b32(0xe5) }],
          outputRangeProofs: [blob(0xe6, 7)],
          conservation: { excessCommitment: b32(0xe7), nonceCommitment: b32(0xe8), response: b32(0xe9) },
        },
      },
    ],
    custom: [{ kind: "custom", cell: agent, programVkHash: b32(0xf1), proofCommitment: b32(0xf2) }],
  };
}

// ─── the differentials ──────────────────────────────────────────────────────

const seed32 = Uint8Array.from({ length: 32 }, (_, i) => 0x30 + i);
const federationId = new Uint8Array(32);

async function ctx() {
  const wasm = await loadWasmOracle();
  const rawMod = await raw();
  const { program } = await import("../dist/index.mjs");
  const agent = b32(0x05);
  return { wasm, rawMod, program, agent };
}

function differential(wasm, rawMod, agent, effects, label) {
  const tsTurn = {
    agent,
    nonce: 7n,
    roots: [{ action: signedAction(rawMod, agent, effects), children: [] }],
    fee: 10_000n,
    memo: `fx-${label}`,
    validUntil: 1765432100n,
  };
  const jsonBytes = new TextEncoder().encode(JSON.stringify(turnToJson(tsTurn)));
  // Pre-signed (non-Unchecked) actions: the oracle performs a PURE re-encode.
  const oracle = wasm.sign_turn_v3(jsonBytes, seed32, federationId);
  assert.equal(
    hex(rawMod.encodeTurn(tsTurn)),
    hex(Uint8Array.from(oracle.turn_bytes)),
    `${label}: TS postcard layout diverged from Rust postcard::to_allocvec`,
  );
  assert.equal(
    rawMod.turnHashHex(tsTurn),
    oracle.turn_id,
    `${label}: TS Turn::hash (v3, folds Effect::hash) diverged from Rust`,
  );
}

test("EFFECT_KIND_COUNT is 34 and the fixture map covers every kind", async () => {
  const { rawMod, program, agent } = await ctx();
  assert.equal(rawMod.EFFECT_KIND_COUNT, 34, "modeled-kind count must match the Rust enum (34 variants)");
  const fx = fixtures(rawMod, agent, program);
  const kinds = Object.keys(fx);
  assert.equal(kinds.length, 34, `fixture map covers ${kinds.length}/34 kinds`);
  // Every fixture kind field agrees with its map key (no mislabeled fixture).
  for (const [k, effects] of Object.entries(fx)) {
    for (const e of effects) assert.equal(e.kind, k === "grantCapability" ? "grantCapability" : e.kind);
    assert.ok(effects.length >= 1);
    assert.ok(effects.every((e) => e.kind === k), `fixture list for ${k} contains only ${k}`);
  }
});

test("differential: every Effect kind, TS postcard + Turn::hash == Rust (per-kind)", async () => {
  const { wasm, rawMod, program, agent } = await ctx();
  const fx = fixtures(rawMod, agent, program);
  for (const [kind, effects] of Object.entries(fx)) {
    differential(wasm, rawMod, agent, effects, kind);
  }
});

test("differential: one mega-turn carrying all 34 kinds at once", async () => {
  const { wasm, rawMod, program, agent } = await ctx();
  const fx = fixtures(rawMod, agent, program);
  const all = Object.values(fx).flat();
  differential(wasm, rawMod, agent, all, "mega");
});

test("unmodeled shapes REFUSE loudly (Cases program / Receipt proof)", async () => {
  const { rawMod, agent } = await ctx();
  const badProgram = {
    agent,
    nonce: 0n,
    roots: [
      {
        action: signedAction(rawMod, agent, [
          { kind: "setProgram", cell: agent, program: { kind: "cases", cases: [] } },
        ]),
        children: [],
      },
    ],
    fee: 0n,
  };
  assert.throws(() => rawMod.encodeTurn(badProgram), /unmodeled wire shape/);
  const badProof = {
    agent,
    nonce: 0n,
    roots: [
      {
        action: signedAction(rawMod, agent, [
          {
            kind: "react",
            pendingId: b32(1),
            condition: { kind: "hashPreimage", hash: b32(2) },
            resolutionProof: { kind: "receipt" },
            wake: wakeTurn(rawMod, agent),
          },
        ]),
        children: [],
      },
    ],
    fee: 0n,
  };
  assert.throws(() => rawMod.encodeTurn(badProof), /unmodeled wire shape/);
});
