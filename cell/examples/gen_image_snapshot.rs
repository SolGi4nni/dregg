//! gen_image_snapshot — emit a LIVE IMAGE of REAL `dregg-cell` cells as a
//! `#![no_std]`-friendly Rust data table, for the seL4 deos-image viewer PD.
//!
//! The deos-image PD is `#![no_std]` on a bare-metal seL4 Microkit target and
//! cannot link `dregg-cell` (std + bulletproofs/curve25519). So we build a REAL
//! `World` of cells here with the REAL crate — real `CellId::derive_raw`, real
//! `CapabilitySet::grant`, real `Permissions`, real signed `balance`, real
//! `fields[16]`, real `VerificationKey`, real lifecycle — compute each cell's
//! REAL `state_commitment()`, and freeze the renderable view into plain consts
//! the viewer `include!`s. The ids and commitments below are NOT invented:
//! they are this crate's output. Regenerate with:
//!
//!   cargo run -p dregg-cell --example gen_image_snapshot \
//!     > sel4/dregg-pd/deos-image/src/image_data.rs
//!
//! (run from the repo root). This is a build-time snapshot — the LIVE in-VM
//! executor mutating these cells as it runs turns is the named next rung
//! (Rung 3, the executor-PD Lean runtime). This viewer walks real frozen cells.

use std::fmt::Write as _;

use dregg_cell::cell::{Cell, CellConfig, CellMode, VerificationKey};
use dregg_cell::permissions::{AuthRequired, Permissions};
use dregg_cell::state::FieldElement;
use dregg_cell::vk_v2::{ProvingSystemId, VerifierFingerprint, VkComponents};
use dregg_types::CellId;

/// Deterministic keypair-ish material for a named cell (so ids are stable and
/// reproducible run-to-run — the same `seed → CellId` shape the firmament's
/// boot scenes use).
fn pk_for(seed: u8) -> [u8; 32] {
    let mut pk = [0u8; 32];
    pk[0] = seed;
    pk[31] = seed.wrapping_mul(7).wrapping_add(3);
    // a little more entropy across the middle so the rendered hex looks real
    pk[7] = seed.wrapping_mul(13);
    pk[15] = seed.wrapping_mul(29).wrapping_add(1);
    pk[23] = seed.wrapping_mul(101);
    pk
}

const GARDEN_TOKEN: [u8; 32] = *b"deos.garden.token.domain.0000000";
const VALUE_TOKEN: [u8; 32] = *b"deos.value.computrons.domain.000";

/// Pack a short ASCII string into a 32-byte field element (left-justified),
/// the way an app stores a small label in a state slot.
fn fe_text(s: &str) -> FieldElement {
    let mut f = [0u8; 32];
    let b = s.as_bytes();
    let n = b.len().min(32);
    f[..n].copy_from_slice(&b[..n]);
    f
}

/// Pack a u64 into a field element, big-endian in the low 8 bytes.
fn fe_u64(v: u64) -> FieldElement {
    let mut f = [0u8; 32];
    f[24..32].copy_from_slice(&v.to_be_bytes());
    f
}

/// A real verification key built from real canonical VK-v2 components.
fn real_vk(program: &str) -> VerificationKey {
    VerificationKey::from_components(&VkComponents {
        program_bytes: program.as_bytes(),
        air_fingerprint: *blake3::hash(format!("air::{program}").as_bytes()).as_bytes(),
        verifier_fingerprint: VerifierFingerprint::SourceHash(
            *blake3::hash(format!("verifier::{program}").as_bytes()).as_bytes(),
        ),
        proving_system_id: ProvingSystemId::Plonky3BabyBearFri { p3_rev: "82cfad73" },
    })
}

/// One renderable cell, with everything the viewer needs to inspect it.
struct ImageCell {
    key: &'static str,   // short nav key (rail label)
    title: &'static str, // human title
    blurb: &'static str, // one-line "what is this" subtitle
    cell: Cell,
    // a couple of human field annotations (slot -> meaning) for legibility
    field_notes: &'static [(usize, &'static str)],
}

fn auth_str(a: &AuthRequired) -> &'static str {
    match a {
        AuthRequired::None => "none",
        AuthRequired::Signature => "signature",
        AuthRequired::Proof => "proof",
        AuthRequired::Either => "either",
        AuthRequired::Impossible => "impossible",
        AuthRequired::Custom { .. } => "custom(vk)",
    }
}

fn mode_str(m: &CellMode) -> &'static str {
    match m {
        CellMode::Sovereign => "SOVEREIGN",
        CellMode::Hosted => "HOSTED",
    }
}

/// Render a lifecycle to a short tag + a longer descriptor.
fn lifecycle_tags(c: &Cell) -> (&'static str, String) {
    use dregg_cell::lifecycle::CellLifecycle::*;
    match &c.lifecycle {
        Live => ("LIVE", "accepts effects; the ordinary running state".into()),
        Sealed { sealed_at, .. } => (
            "SEALED",
            format!("reversible quiescence; sealed at height {sealed_at}"),
        ),
        Destroyed { destroyed_at, .. } => (
            "DESTROYED",
            format!("permanently retired at height {destroyed_at}"),
        ),
        Migrated { .. } => ("MIGRATED", "moved to a successor cell".into()),
        Archived {
            archived_through, ..
        } => (
            "ARCHIVED",
            format!("history checkpointed through height {archived_through}; still live"),
        ),
    }
}

fn hex8(bytes: &[u8]) -> String {
    // first 8 bytes as two 4-byte groups, like the tutorial rendered ids
    let mut s = String::new();
    for (i, b) in bytes.iter().take(16).enumerate() {
        if i > 0 && i % 4 == 0 {
            s.push(' ');
        }
        let _ = write!(s, "{b:02x}");
    }
    s
}

fn hex_full_short(bytes: &[u8]) -> String {
    // a longer 12-byte fingerprint for the drill-in evidence view
    let mut s = String::new();
    for (i, b) in bytes.iter().take(12).enumerate() {
        if i > 0 && i % 4 == 0 {
            s.push(' ');
        }
        let _ = write!(s, "{b:02x}");
    }
    s.push_str(" ..");
    s
}

fn build_image() -> Vec<ImageCell> {
    let mut cells = Vec::new();

    // ── 1. about deos — the welcome woven in as the first inspectable object.
    // A real sovereign cell whose fields hold the houyhnhnm framing text.
    {
        let pk = pk_for(0xA0);
        let mut c = Cell::from_config(
            pk,
            GARDEN_TOKEN,
            CellConfig::sovereign()
                .with_balance(0)
                .with_permissions(Permissions::sovereign_default()),
        );
        c.state.set_field(0, fe_text("welcome to deos"));
        c.state.set_field(1, fe_text("a computer you hold"));
        c.state.set_field(2, fe_text("authority is proof"));
        c.state.set_field(3, fe_text("persistence is default"));
        c.state.set_field(4, fe_text("the keys are yours"));
        // a couple of nonce bumps so it's clearly "been used"
        let _ = c.state.increment_nonce();
        let _ = c.state.increment_nonce();
        cells.push(ImageCell {
            key: "about",
            title: "about deos",
            blurb: "the welcome, as a live object you can inspect",
            cell: c,
            field_notes: &[
                (0, "greeting"),
                (1, "thesis"),
                (2, "law of authority"),
                (3, "law of persistence"),
                (4, "law of sovereignty"),
            ],
        });
    }

    // ── 2. the garden — a sovereign content cell holding the Sacred Motto.
    {
        let pk = pk_for(0x9A);
        let mut c = Cell::from_config(pk, GARDEN_TOKEN, CellConfig::sovereign().with_balance(0));
        c.state.set_field(0, fe_text("I object to doing"));
        c.state.set_field(1, fe_text("things computers"));
        c.state.set_field(2, fe_text("can do."));
        c.state.set_field(3, fe_text("- Guild of Houyhnhnm"));
        c.state.set_field(7, fe_u64(1999)); // the AOL-wonder year
        let _ = c.state.increment_nonce();
        // selectively-disclosable: a private field (commitment only)
        c.state.set_field(10, fe_text("a private leaf"));
        c.state
            .set_field_visibility(10, dregg_cell::state::FieldVisibility::Committed, 0x2a);
        cells.push(ImageCell {
            key: "garden",
            title: "the garden",
            blurb: "a sovereign content cell — transclude its quote",
            cell: c,
            field_notes: &[
                (0, "motto line 1"),
                (1, "motto line 2"),
                (2, "motto line 3"),
                (3, "attribution"),
                (7, "year (u64)"),
                (10, "private (committed)"),
            ],
        });
    }

    // ── 3. the wallet — value-bearing, real signed balance, spend permissions,
    // and caps pointing at the garden + a peer (the web of cells).
    {
        let pk = pk_for(0x01);
        let mut c = Cell::from_config(
            pk,
            VALUE_TOKEN,
            CellConfig::sovereign()
                .with_balance(1_000)
                .with_permissions(Permissions::default_user()),
        );
        // grant real caps to other cells in the image
        let garden_id = CellId::derive_raw(&pk_for(0x9A), &GARDEN_TOKEN);
        let peer_id = CellId::derive_raw(&pk_for(0x42), &VALUE_TOKEN);
        c.capabilities.grant(garden_id, AuthRequired::Either);
        c.capabilities.grant(peer_id, AuthRequired::Signature);
        // a transfer-shaped state: last-recipient + last-amount
        c.state.set_field(0, fe_text("last->peer"));
        c.state.set_field(1, fe_u64(250));
        let _ = c.state.increment_nonce();
        let _ = c.state.increment_nonce();
        let _ = c.state.increment_nonce();
        cells.push(ImageCell {
            key: "wallet",
            title: "your wallet",
            blurb: "value + the c-list — spend caps over the web",
            cell: c,
            field_notes: &[(0, "last recipient"), (1, "last amount")],
        });
    }

    // ── 4. the mint — an ISSUER WELL: a real NEGATIVE balance (−supply), and
    // grant authority. The conservation shadow: Σ balances = 0 across the image.
    {
        let pk = pk_for(0xF0);
        let mut c = Cell::from_config(
            pk,
            VALUE_TOKEN,
            CellConfig::sovereign()
                .with_balance(0)
                .with_permissions(Permissions::sovereign_default()),
        );
        // the well carries −supply for the value minted into the wallet (1000)
        // plus the peer (200): Σ = 0.
        let _ = c.state.well_debit_balance(1_200);
        c.state.set_field(0, fe_text("computrons issuer"));
        c.state.set_field(1, fe_u64(1_200)); // total supply minted
        c.verification_key = Some(real_vk("dregg.mint.v1"));
        let _ = c.state.increment_nonce();
        cells.push(ImageCell {
            key: "mint",
            title: "the mint",
            blurb: "an issuer well: -supply, so the image conserves to zero",
            cell: c,
            field_notes: &[(0, "role"), (1, "supply minted (u64)")],
        });
    }

    // ── 5. the chronicle — a SEALED record cell (lifecycle variety) with a VK
    // (proved state). Shows the EVIDENCE substance richly.
    {
        let pk = pk_for(0xC0);
        let mut c = Cell::from_config(pk, GARDEN_TOKEN, CellConfig::sovereign().with_balance(0));
        // a proof set all 16 fields → proved_state true
        for i in 0..16 {
            c.state.set_field(i, fe_u64((i as u64 + 1) * 111));
        }
        c.state.set_proved_state(true);
        c.verification_key = Some(real_vk("dregg.chronicle.v2"));
        let _ = c.state.increment_nonce();
        let _ = c.state.increment_nonce();
        // seal it (reversible quiescence)
        let reason = *blake3::hash(b"end of the season").as_bytes();
        c.seal(reason, 42_000).expect("seal a live cell");
        cells.push(ImageCell {
            key: "record",
            title: "the chronicle",
            blurb: "a sealed, proof-backed record — read its evidence",
            cell: c,
            field_notes: &[(0, "entry 1"), (1, "entry 2"), (15, "entry 16")],
        });
    }

    // ── 6. a peer — a small value cell, the far end of the wallet's cap. Shows
    // a different lifecycle (Destroyed) so the rail spans the lifecycle space.
    // NOTE: it keeps balance 200 (its final-state balance) so the image still
    // conserves to zero against the mint's -1200; a death certificate binds its
    // final commitment.
    {
        let pk = pk_for(0x42);
        let mut c = Cell::from_config(
            pk,
            VALUE_TOKEN,
            CellConfig::sovereign()
                .with_balance(200)
                .with_permissions(Permissions::default_user()),
        );
        c.state.set_field(0, fe_text("a friend's cell"));
        let _ = c.state.increment_nonce();
        // permanently retire it (the DESTROYED lifecycle) — a death certificate
        // binds its final state-commitment so observers prove "retired", not
        // infer from absence.
        let cert = dregg_cell::lifecycle::DeathCertificate {
            cell_id: c.id(),
            last_receipt_hash: *blake3::hash(b"peer.last.receipt").as_bytes(),
            final_state_commitment: c.state_commitment(),
            destroyed_at_height: 41_700,
            reason: dregg_cell::lifecycle::DeathReason::Voluntary,
        };
        c.destroy(&cert).expect("retire the peer");
        cells.push(ImageCell {
            key: "peer",
            title: "a peer",
            blurb: "the far end of a cap — retired, but provably so",
            cell: c,
            field_notes: &[(0, "label")],
        });
    }

    cells
}

fn emit(cells: &[ImageCell]) {
    // Header.
    println!("// @generated by `cargo run -p dregg-cell --example gen_image_snapshot`.");
    println!("// DO NOT EDIT BY HAND. A frozen LIVE IMAGE of REAL dregg-cell cells:");
    println!("// every id / commitment / cap below is this crate's genuine output");
    println!("// (real CellId::derive_raw, real state_commitment, real CapabilitySet).");
    println!("//");
    println!("// Regenerate from the repo root (and redirect into this file):");
    println!("//   cargo run -p dregg-cell --example gen_image_snapshot \\");
    println!("//     > sel4/dregg-pd/deos-image/src/image_data.rs");
    println!();
    println!("#![allow(dead_code)]");
    println!();
    println!("/// One inspectable substance value: a (label, value) pair, pre-rendered.");
    println!("pub struct Kv {{ pub k: &'static str, pub v: &'static str }}");
    println!();
    println!("/// One capability in a cell's c-list (the AUTHORITY substance), rendered.");
    println!("pub struct CapRow {{");
    println!("    pub target: &'static str, // target cell id (short hex)");
    println!("    pub slot: u32,");
    println!("    pub auth: &'static str,   // AuthRequired");
    println!("    pub note: &'static str,   // human note (which named cell / caveat)");
    println!("}}");
    println!();
    println!("/// One state field (the STATE substance), rendered.");
    println!("pub struct FieldRow {{");
    println!("    pub slot: u32,");
    println!("    pub note: &'static str,   // human meaning, or \"\"");
    println!("    pub kind: &'static str,   // public | committed | disclosable");
    println!("    pub value: &'static str,  // decoded value or commitment hash");
    println!("}}");
    println!();
    println!("/// One cell in the image — everything the viewer inspects.");
    println!("pub struct ImageCell {{");
    println!("    pub key: &'static str,");
    println!("    pub title: &'static str,");
    println!("    pub blurb: &'static str,");
    println!("    pub id_hex: &'static str,      // content-addressed id (short)");
    println!("    pub pk_hex: &'static str,");
    println!("    pub token_hex: &'static str,");
    println!("    pub mode: &'static str,");
    println!("    pub life_tag: &'static str,");
    println!("    pub life_desc: &'static str,");
    println!("    // VALUE substance");
    println!("    pub balance: i64,");
    println!("    pub is_well: bool,");
    println!("    // STATE substance");
    println!("    pub nonce: u64,");
    println!("    pub fields_used: u32,          // how many of the 16 fields are nonzero");
    println!("    pub fields: &'static [FieldRow],");
    println!("    // AUTHORITY substance");
    println!("    pub caps: &'static [CapRow],");
    println!("    pub perms: &'static [Kv],      // the 8 permission gates");
    println!("    // EVIDENCE substance");
    println!("    pub proved_state: bool,");
    println!("    pub vk_hash: &'static str,     // \"none\" if no VK");
    println!("    pub vk_program: &'static str,");
    println!("    pub commitment: &'static str,  // state_commitment() (short hex)");
    println!("}}");
    println!();

    // Named cells (so the wallet's caps can reference "garden"/"peer" by name).
    let name_by_id: std::collections::HashMap<[u8; 32], &'static str> = cells
        .iter()
        .map(|ic| (*ic.cell.id().as_bytes(), ic.title))
        .collect();

    println!("pub const IMAGE: &[ImageCell] = &[");
    for ic in cells {
        let c = &ic.cell;
        let (life_tag, life_desc) = lifecycle_tags(c);
        let is_well = c.state.balance() < 0;
        let fields_used = (0..16)
            .filter(|&i| {
                c.state
                    .get_field(i)
                    .map(|f| f != &[0u8; 32])
                    .unwrap_or(false)
            })
            .count() as u32;

        println!("    ImageCell {{");
        println!("        key: {:?},", ic.key);
        println!("        title: {:?},", ic.title);
        println!("        blurb: {:?},", ic.blurb);
        println!("        id_hex: {:?},", hex8(c.id().as_bytes()));
        println!("        pk_hex: {:?},", hex8(c.public_key()));
        println!("        token_hex: {:?},", hex8(c.token_id()));
        println!("        mode: {:?},", mode_str(&c.mode));
        println!("        life_tag: {life_tag:?},");
        println!("        life_desc: {life_desc:?},");
        println!("        balance: {},", c.state.balance());
        println!("        is_well: {is_well},");
        println!("        nonce: {},", c.state.nonce());
        println!("        fields_used: {fields_used},");

        // fields
        println!("        fields: &[");
        for i in 0..16 {
            let f = c.state.get_field(i).copied().unwrap_or([0u8; 32]);
            if f == [0u8; 32] {
                continue;
            }
            let note = ic
                .field_notes
                .iter()
                .find(|(s, _)| *s == i)
                .map(|(_, n)| *n)
                .unwrap_or("");
            // decode the value: try text, else u64, else hex
            let (kind, value) = match c.state.get_field_public(i) {
                Some(dregg_cell::state::PublicFieldView::Committed(h)) => {
                    ("committed".to_string(), hex_full_short(&h))
                }
                _ => {
                    // public — decode
                    let kind = match c.state.field_visibility[i] {
                        dregg_cell::state::FieldVisibility::Public => "public",
                        dregg_cell::state::FieldVisibility::Committed => "committed",
                        dregg_cell::state::FieldVisibility::SelectivelyDisclosable => "disclosable",
                    };
                    (kind.to_string(), decode_field(&f))
                }
            };
            println!(
                "            FieldRow {{ slot: {i}, note: {note:?}, kind: {kind:?}, value: {value:?} }},"
            );
        }
        println!("        ],");

        // caps
        println!("        caps: &[");
        for cap in c.capabilities.iter() {
            let tgt = cap.target.as_bytes();
            let note = name_by_id
                .get(tgt)
                .map(|n| format!("-> {n}"))
                .unwrap_or_else(|| "-> (external)".into());
            println!(
                "            CapRow {{ target: {:?}, slot: {}, auth: {:?}, note: {:?} }},",
                hex8(tgt),
                cap.slot,
                auth_str(&cap.permissions),
                note
            );
        }
        println!("        ],");

        // perms
        let p = &c.permissions;
        println!("        perms: &[");
        for (k, a) in [
            ("send", &p.send),
            ("receive", &p.receive),
            ("set_state", &p.set_state),
            ("set_permissions", &p.set_permissions),
            ("set_vk", &p.set_verification_key),
            ("increment_nonce", &p.increment_nonce),
            ("delegate", &p.delegate),
            ("access", &p.access),
        ] {
            println!("            Kv {{ k: {:?}, v: {:?} }},", k, auth_str(a));
        }
        println!("        ],");

        // evidence
        println!("        proved_state: {},", c.state.proved_state());
        match &c.verification_key {
            Some(vk) => {
                println!("        vk_hash: {:?},", hex_full_short(&vk.hash));
                let prog = String::from_utf8_lossy(&vk.data).to_string();
                println!("        vk_program: {prog:?},");
            }
            None => {
                println!("        vk_hash: \"none\",");
                println!("        vk_program: \"\",");
            }
        }
        println!(
            "        commitment: {:?},",
            hex_full_short(&c.state_commitment())
        );
        println!("    }},");
    }
    println!("];");

    // A footer fact computed from the real cells: conservation.
    let total: i64 = cells.iter().map(|ic| ic.cell.state.balance()).sum();
    println!();
    println!("/// The real sum of all balances across the image (the conservation");
    println!("/// shadow: issuer wells carry -supply, so a closed image sums to zero).");
    println!("pub const BALANCE_SUM: i64 = {total};");
    println!("/// How many cells are in the image.");
    println!("pub const N_CELLS: usize = {};", cells.len());
}

/// Best-effort decode of a field element for display: text if printable, else
/// the trailing u64, else short hex.
fn decode_field(f: &FieldElement) -> String {
    // text? (leading printable ASCII run, rest zero)
    let text_len = f.iter().take_while(|&&b| b != 0).count();
    if text_len > 0 && f[text_len..].iter().all(|&b| b == 0) {
        if f[..text_len].iter().all(|&b| (0x20..=0x7e).contains(&b)) {
            return format!("\"{}\"", String::from_utf8_lossy(&f[..text_len]));
        }
    }
    // u64 in the low 8 bytes, rest zero?
    if f[..24].iter().all(|&b| b == 0) {
        let mut le = [0u8; 8];
        le.copy_from_slice(&f[24..32]);
        let v = u64::from_be_bytes(le);
        if v != 0 {
            return format!("{v}");
        }
    }
    hex_full_short(f)
}

fn main() {
    let cells = build_image();
    emit(&cells);
}
