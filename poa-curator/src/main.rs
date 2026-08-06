use std::collections::BTreeMap;
use std::env;
use std::fs::{self, File, OpenOptions};
use std::io::{Read, Write};
use std::path::{Path, PathBuf};

#[cfg(unix)]
use std::os::unix::fs::{MetadataExt, OpenOptionsExt};

use dregg_types::{SigningKey, generate_keypair};
use poa_curator::companion::{CompanionManifestV3, SignedCompanionManifestV3};
use poa_curator::{
    ContentEpochEnvelope, CuratorKeyPin, CuratorSigner, DETACHED_SIGNATURE_FILENAME, Poag1Bundle,
};

const USAGE: &str = r#"poa-curator — Path of Angels development content ceremony

usage:
  poa-curator keygen --secret PATH --pin PATH
  poa-curator sign-content --secret PATH --pin PATH --manifest PATH --deployment PATH --epoch N --counter N [--output PATH]
  poa-curator verify-content --pin PATH --manifest PATH --deployment PATH --epoch N --counter N [--signature PATH]
  poa-curator preview-epoch --manifest PATH --deployment PATH [--pin PATH --signature PATH --epoch N --counter N]
  poa-curator sign-companion --secret PATH --pin PATH --manifest PATH --deployment PATH --content-signature PATH --content-epoch N --content-counter N --draft PATH --output PATH
  poa-curator verify-companion --pin PATH --manifest PATH --deployment PATH --content-signature PATH --content-epoch N --content-counter N --input PATH
  poa-curator sign-world-activation --secret PATH --pin PATH --preview PATH --output PATH
  poa-curator verify-world-activation --pin PATH --envelope PATH
  poa-curator signal-replay --bundle PATH
  poa-curator signal-review --bundle PATH
  poa-curator promotion-inbox --bundle PATH --manifest PATH --deployment PATH --pin PATH --signature PATH --epoch N --counter N

`keygen` creates a DEVELOPMENT beta curator key, never a Sentyr identity. It
refuses to overwrite either output and writes the raw 32-byte secret mode 0600.

`preview-epoch` is read-only JSON. With no signature tuple it loudly reports an
unsigned WIP; signature status becomes valid only when all four verification
flags are supplied and verify against the exact bundle and deployment.

`sign-companion` signs one short-lived, exact YouTube/X discovery route only
after the same curator key, POAG1 bytes, content epoch and PoA deployment have
all been verified. It refuses to overwrite its output. `verify-companion`
repeats the complete ceremony without reading a secret key.

`sign-world-activation` signs the `signing_message` of a
POA-WORLD-ACTIVATION-PREVIEW-V1 emitted by `dregg-node
poa-galley-world-preview`. It does NOT trust the preview's printed message: it
re-derives the canonical statement bytes from the preview's structured fields
and refuses if the two disagree, so a curator cannot sign bytes nobody
re-derived. It also refuses a secret that does not derive the pin, a preview
addressed to another curator, and any statement the store would refuse to
install. `verify-world-activation` repeats the check without a secret key.

`signal-replay` is read-only. It checks a caller-supplied sealed wire chain,
reruns every transition through native Lean, and prints one machine-readable
semantic-replay report. It does not authenticate where the wires came from.

`signal-review` reruns the supplied state/carrier through Lean for semantic
inspection only. `promotion-inbox` instead requires `--bundle` to be a
bearer-fetched POA-SIGNAL-NODE-ENVELOPE-V1: the curator checks its exact
SignedTurn, executor receipt, rostered-node signature, durable CommitRecord
digest/projection, and native-Lean replay. The V1 export has no quorum or
threshold/hybrid certificate, external deployment-manifest trust pin,
actor-cell PQ-enrollment proof, or exact signed-catalog mission/config binding,
so this command still refuses canon promotion.
"#;

fn main() {
    if let Err(error) = run(env::args().skip(1).collect()) {
        eprintln!("poa-curator: {error}");
        std::process::exit(2);
    }
}

fn run(arguments: Vec<String>) -> Result<(), String> {
    let Some(command) = arguments.first().map(String::as_str) else {
        return Err(USAGE.into());
    };
    if matches!(command, "help" | "--help" | "-h") {
        print!("{USAGE}");
        return Ok(());
    }
    let flags = parse_flags(&arguments[1..])?;
    match command {
        "keygen" => command_keygen(&flags),
        "sign-content" => command_sign_content(&flags),
        "verify-content" => command_verify_content(&flags),
        "preview-epoch" => command_preview_epoch(&flags),
        "sign-companion" => command_sign_companion(&flags),
        "verify-companion" => command_verify_companion(&flags),
        "sign-world-activation" => command_sign_world_activation(&flags),
        "verify-world-activation" => command_verify_world_activation(&flags),
        "signal-replay" => command_signal_replay(&flags),
        "signal-review" => command_signal_review(&flags),
        "promotion-inbox" => command_promotion_inbox(&flags),
        other => Err(format!("unknown command {other:?}\n\n{USAGE}")),
    }
}

fn command_sign_world_activation(flags: &BTreeMap<String, String>) -> Result<(), String> {
    exact_flags(flags, &["secret", "pin", "preview", "output"], &[])?;
    let secret_path = flag_path(flags, "secret")?;
    let pin_path = flag_path(flags, "pin")?;
    let preview_path = flag_path(flags, "preview")?;
    let output = flag_path(flags, "output")?;

    let secret = load_secret_key(&secret_path)?;
    let pin = CuratorKeyPin::load(&pin_path).map_err(|error| error.to_string())?;
    let pin_key = pin.public_key().map_err(|error| error.to_string())?;
    let preview =
        poa_curator::world_activation::load_preview(&preview_path).map_err(|e| e.to_string())?;
    let signed = poa_curator::world_activation::sign_world_activation(&secret, &pin_key, &preview)
        .map_err(|error| error.to_string())?;
    // Verify the emitted document the way an operator would, before it exists on
    // disk: a envelope this tool cannot check is one the node discovers at install.
    poa_curator::world_activation::verify_world_activation(&pin_key, &signed.envelope)
        .map_err(|error| format!("self-verification failed: {error}"))?;

    let mut bytes = serde_json::to_vec_pretty(&signed.envelope).map_err(|e| e.to_string())?;
    bytes.push(b'\n');
    atomic_write_new(&output, &bytes, 0o644)?;
    println!(
        "signed world activation counter {} ({}): {}",
        signed.envelope.counter,
        signed.envelope.kind,
        output.display()
    );
    println!("  signing_message_sha256 {}", signed.signing_message_sha256);
    Ok(())
}

fn command_verify_world_activation(flags: &BTreeMap<String, String>) -> Result<(), String> {
    exact_flags(flags, &["pin", "envelope"], &[])?;
    let pin_path = flag_path(flags, "pin")?;
    let envelope_path = flag_path(flags, "envelope")?;

    let pin = CuratorKeyPin::load(&pin_path).map_err(|error| error.to_string())?;
    let pin_key = pin.public_key().map_err(|error| error.to_string())?;
    let envelope =
        poa_curator::world_activation::load_envelope(&envelope_path).map_err(|e| e.to_string())?;
    let sha = poa_curator::world_activation::verify_world_activation(&pin_key, &envelope)
        .map_err(|error| error.to_string())?;
    println!(
        "world activation counter {} ({}) verifies against the pin",
        envelope.counter, envelope.kind
    );
    println!("  signing_message_sha256 {sha}");
    Ok(())
}

fn command_sign_companion(flags: &BTreeMap<String, String>) -> Result<(), String> {
    exact_flags(
        flags,
        &[
            "secret",
            "pin",
            "manifest",
            "deployment",
            "content-signature",
            "content-epoch",
            "content-counter",
            "draft",
            "output",
        ],
        &[],
    )?;
    let content_epoch = flag_u64(flags, "content-epoch")?;
    let content_counter = flag_u64(flags, "content-counter")?;
    let pin = CuratorKeyPin::load(flag_path(flags, "pin")?).map_err(|error| error.to_string())?;
    let bundle =
        Poag1Bundle::load(flag_path(flags, "manifest")?).map_err(|error| error.to_string())?;
    let bound = bundle
        .bind_deployment(flag_path(flags, "deployment")?)
        .map_err(|error| error.to_string())?;
    let content = ContentEpochEnvelope::load(flag_path(flags, "content-signature")?)
        .map_err(|error| error.to_string())?;
    let verified = content
        .verify(&bound, &pin, content_epoch, content_counter)
        .map_err(|error| error.to_string())?;
    let secret = load_secret_key(&flag_path(flags, "secret")?)?;
    if secret.public_key() != pin.public_key().map_err(|error| error.to_string())? {
        return Err("secret key does not match the external public pin".into());
    }
    let manifest =
        CompanionManifestV3::load(flag_path(flags, "draft")?).map_err(|error| error.to_string())?;
    let now = unix_now()?;
    let signed = SignedCompanionManifestV3::sign(manifest, &secret, &bound, &verified, now)
        .map_err(|error| error.to_string())?;
    signed
        .verify(&pin, &bound, &verified, now)
        .map_err(|error| format!("self-verification failed: {error}"))?;
    let mut bytes = serde_json::to_vec_pretty(&signed).map_err(|error| error.to_string())?;
    bytes.push(b'\n');
    let output = flag_path(flags, "output")?;
    atomic_write_new(&output, &bytes, 0o644)?;
    println!(
        "signed companion {}:{} sequence {}: {}",
        match &signed.manifest.context {
            poa_curator::companion::CompanionContext::Youtube { .. } => "youtube",
            poa_curator::companion::CompanionContext::X { .. } => "x",
        },
        match &signed.manifest.context {
            poa_curator::companion::CompanionContext::Youtube { video_id, .. } => video_id,
            poa_curator::companion::CompanionContext::X { post_id } => post_id,
        },
        signed.manifest.sequence,
        output.display()
    );
    Ok(())
}

fn command_verify_companion(flags: &BTreeMap<String, String>) -> Result<(), String> {
    exact_flags(
        flags,
        &[
            "pin",
            "manifest",
            "deployment",
            "content-signature",
            "content-epoch",
            "content-counter",
            "input",
        ],
        &[],
    )?;
    let content_epoch = flag_u64(flags, "content-epoch")?;
    let content_counter = flag_u64(flags, "content-counter")?;
    let pin = CuratorKeyPin::load(flag_path(flags, "pin")?).map_err(|error| error.to_string())?;
    let bundle =
        Poag1Bundle::load(flag_path(flags, "manifest")?).map_err(|error| error.to_string())?;
    let bound = bundle
        .bind_deployment(flag_path(flags, "deployment")?)
        .map_err(|error| error.to_string())?;
    let content = ContentEpochEnvelope::load(flag_path(flags, "content-signature")?)
        .map_err(|error| error.to_string())?;
    let verified = content
        .verify(&bound, &pin, content_epoch, content_counter)
        .map_err(|error| error.to_string())?;
    let signed = SignedCompanionManifestV3::load(flag_path(flags, "input")?)
        .map_err(|error| error.to_string())?;
    signed
        .verify(&pin, &bound, &verified, unix_now()?)
        .map_err(|error| error.to_string())?;
    println!(
        "verified companion content epoch {} counter {} sequence {}",
        content_epoch, content_counter, signed.manifest.sequence
    );
    Ok(())
}

fn unix_now() -> Result<u64, String> {
    std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .map(|duration| duration.as_secs())
        .map_err(|error| format!("system clock predates Unix epoch: {error}"))
}

fn command_signal_review(flags: &BTreeMap<String, String>) -> Result<(), String> {
    exact_flags(flags, &["bundle"], &[])?;
    let export =
        poa_curator::signal_replay::export_semantic_review_file(flag_path(flags, "bundle")?)
            .map_err(|error| error.to_string())?;
    println!(
        "{}",
        serde_json::to_string(&export).map_err(|error| error.to_string())?
    );
    Ok(())
}

fn command_promotion_inbox(flags: &BTreeMap<String, String>) -> Result<(), String> {
    exact_flags(
        flags,
        &[
            "bundle",
            "manifest",
            "deployment",
            "pin",
            "signature",
            "epoch",
            "counter",
        ],
        &[],
    )?;
    let authority_path = flag_path(flags, "bundle")?;
    let manifest_path = flag_path(flags, "manifest")?;
    let deployment_path = flag_path(flags, "deployment")?;
    let pin = CuratorKeyPin::load(flag_path(flags, "pin")?).map_err(|error| error.to_string())?;
    let bundle = Poag1Bundle::load(&manifest_path).map_err(|error| error.to_string())?;
    let bound = bundle
        .bind_deployment(&deployment_path)
        .map_err(|error| error.to_string())?;
    let envelope = ContentEpochEnvelope::load(flag_path(flags, "signature")?)
        .map_err(|error| error.to_string())?;
    let epoch = flag_u64(flags, "epoch")?;
    let counter = flag_u64(flags, "counter")?;
    let verified_content = envelope
        .verify(&bound, &pin, epoch, counter)
        .map_err(|error| error.to_string())?;
    let authority = poa_curator::authority_export::verify_authority_export_file(
        &authority_path,
        bound.deployment(),
    )
    .map_err(|error| error.to_string())?;
    let activation_digest = verified_content
        .activation_digest()
        .strip_prefix("sha256:")
        .ok_or_else(|| "verified activation digest is not canonical SHA-256".to_owned())?
        .to_owned();
    if authority.content_root != bundle.content_root()
        || authority.content_epoch != bundle.content_epoch()
        || authority.activation_digest != activation_digest
    {
        return Err(
            "promotion-inbox refused: node envelope names a different signed content epoch".into(),
        );
    }
    let _mission_draft = bundle
        .prepare_mission(authority.mission_id, &[], None)
        .map_err(|error| error.to_string())?;
    refuse_node_envelope_promotion(authority.sequence, epoch, counter)
}

fn refuse_node_envelope_promotion(sequence: u64, epoch: u64, counter: u64) -> Result<(), String> {
    Err(format!(
        "promotion-inbox refused after checking the exact node-attested envelope for authority sequence {}: POA-SIGNAL-NODE-ENVELOPE-V1 does not prove an externally pinned deployment roster, actor-cell PQ enrollment, exact authenticated mission/config equality, or federation finality; those bindings plus a quorum/threshold hybrid certificate over the carrying block, exact receipt, and durable commitment root are required (signed content epoch {epoch}, counter {counter})",
        sequence
    ))
}

#[cfg(test)]
mod node_envelope_promotion_tests {
    use super::*;

    #[test]
    fn otherwise_checked_node_envelope_reaches_explicit_four_gap_hard_refusal() {
        let error = refuse_node_envelope_promotion(3, 7, 4).unwrap_err();
        for missing in [
            "externally pinned deployment roster",
            "actor-cell PQ enrollment",
            "exact authenticated mission/config equality",
            "federation finality",
            "quorum/threshold hybrid certificate",
        ] {
            assert!(error.contains(missing), "missing refusal clause: {missing}");
        }
    }
}

fn command_signal_replay(flags: &BTreeMap<String, String>) -> Result<(), String> {
    exact_flags(flags, &["bundle"], &[])?;
    let report = poa_curator::signal_replay::replay_exact_bundle_file(flag_path(flags, "bundle")?)
        .map_err(|error| error.to_string())?;
    println!(
        "{}",
        serde_json::to_string(&report).map_err(|error| error.to_string())?
    );
    Ok(())
}

fn parse_flags(arguments: &[String]) -> Result<BTreeMap<String, String>, String> {
    if !arguments.len().is_multiple_of(2) {
        return Err("every --flag requires exactly one value".into());
    }
    let mut flags = BTreeMap::new();
    for pair in arguments.chunks_exact(2) {
        let name = pair[0]
            .strip_prefix("--")
            .filter(|name| !name.is_empty())
            .ok_or_else(|| format!("expected --flag, got {:?}", pair[0]))?;
        if flags.insert(name.to_owned(), pair[1].clone()).is_some() {
            return Err(format!("duplicate --{name}"));
        }
    }
    Ok(flags)
}

fn exact_flags(
    flags: &BTreeMap<String, String>,
    required: &[&str],
    optional: &[&str],
) -> Result<(), String> {
    for name in required {
        if !flags.contains_key(*name) {
            return Err(format!("missing --{name}"));
        }
    }
    for name in flags.keys() {
        if !required.contains(&name.as_str()) && !optional.contains(&name.as_str()) {
            return Err(format!("unknown flag --{name}"));
        }
    }
    Ok(())
}

fn flag_path(flags: &BTreeMap<String, String>, name: &str) -> Result<PathBuf, String> {
    flags
        .get(name)
        .map(PathBuf::from)
        .ok_or_else(|| format!("missing --{name}"))
}

fn flag_u64(flags: &BTreeMap<String, String>, name: &str) -> Result<u64, String> {
    flags
        .get(name)
        .ok_or_else(|| format!("missing --{name}"))?
        .parse()
        .map_err(|_| format!("--{name} must be an unsigned 64-bit integer"))
}

fn command_keygen(flags: &BTreeMap<String, String>) -> Result<(), String> {
    exact_flags(flags, &["secret", "pin"], &[])?;
    let secret_path = flag_path(flags, "secret")?;
    let pin_path = flag_path(flags, "pin")?;
    if secret_path == pin_path {
        return Err("--secret and --pin must be different paths".into());
    }
    refuse_existing(&secret_path)?;
    refuse_existing(&pin_path)?;

    let (secret, public) = generate_keypair();
    let pin = CuratorKeyPin::new(&public);
    let mut pin_bytes = serde_json::to_vec_pretty(&pin).map_err(|error| error.to_string())?;
    pin_bytes.push(b'\n');

    atomic_write_new(&secret_path, &secret.to_bytes(), 0o600)?;
    if let Err(error) = atomic_write_new(&pin_path, &pin_bytes, 0o644) {
        let _ = fs::remove_file(&secret_path);
        return Err(error);
    }
    println!(
        "created development curator key and external pin {}",
        pin_path.display()
    );
    Ok(())
}

fn command_sign_content(flags: &BTreeMap<String, String>) -> Result<(), String> {
    exact_flags(
        flags,
        &[
            "secret",
            "pin",
            "manifest",
            "deployment",
            "epoch",
            "counter",
        ],
        &["output"],
    )?;
    let secret_path = flag_path(flags, "secret")?;
    let pin_path = flag_path(flags, "pin")?;
    let manifest_path = flag_path(flags, "manifest")?;
    let deployment_path = flag_path(flags, "deployment")?;
    let epoch = flag_u64(flags, "epoch")?;
    let counter = flag_u64(flags, "counter")?;
    let output = flags.get("output").map(PathBuf::from).unwrap_or_else(|| {
        manifest_path
            .parent()
            .unwrap_or_else(|| Path::new("."))
            .join(DETACHED_SIGNATURE_FILENAME)
    });

    let secret = load_secret_key(&secret_path)?;
    let pin = CuratorKeyPin::load(&pin_path).map_err(|error| error.to_string())?;
    if secret.public_key() != pin.public_key().map_err(|error| error.to_string())? {
        return Err("secret key does not match the external public pin".into());
    }
    let bundle = Poag1Bundle::load(&manifest_path).map_err(|error| error.to_string())?;
    let bound = bundle
        .bind_deployment(&deployment_path)
        .map_err(|error| error.to_string())?;
    let envelope = CuratorSigner::new(&secret)
        .sign_content_epoch(&bound, epoch, counter)
        .map_err(|error| error.to_string())?;
    envelope
        .verify(&bound, &pin, epoch, counter)
        .map_err(|error| format!("self-verification failed: {error}"))?;
    let mut bytes = serde_json::to_vec_pretty(&envelope).map_err(|error| error.to_string())?;
    bytes.push(b'\n');
    atomic_write_new(&output, &bytes, 0o644)?;
    println!(
        "signed content epoch {epoch} counter {counter}: {}",
        output.display()
    );
    Ok(())
}

fn command_verify_content(flags: &BTreeMap<String, String>) -> Result<(), String> {
    exact_flags(
        flags,
        &["pin", "manifest", "deployment", "epoch", "counter"],
        &["signature"],
    )?;
    let pin_path = flag_path(flags, "pin")?;
    let manifest_path = flag_path(flags, "manifest")?;
    let deployment_path = flag_path(flags, "deployment")?;
    let epoch = flag_u64(flags, "epoch")?;
    let counter = flag_u64(flags, "counter")?;
    let signature_path = flags
        .get("signature")
        .map(PathBuf::from)
        .unwrap_or_else(|| {
            manifest_path
                .parent()
                .unwrap_or_else(|| Path::new("."))
                .join(DETACHED_SIGNATURE_FILENAME)
        });
    let pin = CuratorKeyPin::load(pin_path).map_err(|error| error.to_string())?;
    let bundle = Poag1Bundle::load(manifest_path).map_err(|error| error.to_string())?;
    let bound = bundle
        .bind_deployment(deployment_path)
        .map_err(|error| error.to_string())?;
    let envelope = ContentEpochEnvelope::load(signature_path).map_err(|error| error.to_string())?;
    let verified = envelope
        .verify(&bound, &pin, epoch, counter)
        .map_err(|error| error.to_string())?;
    println!(
        "verified content epoch {epoch} counter {counter} activation {}",
        verified.activation_digest()
    );
    Ok(())
}

fn command_preview_epoch(flags: &BTreeMap<String, String>) -> Result<(), String> {
    const VERIFICATION_FLAGS: [&str; 4] = ["pin", "signature", "epoch", "counter"];
    exact_flags(flags, &["manifest", "deployment"], &VERIFICATION_FLAGS)?;
    let supplied_verification_flags = VERIFICATION_FLAGS
        .iter()
        .filter(|name| flags.contains_key(**name))
        .count();
    if supplied_verification_flags != 0 && supplied_verification_flags != VERIFICATION_FLAGS.len() {
        return Err(
            "signature verification requires --pin, --signature, --epoch, and --counter together"
                .into(),
        );
    }

    let bundle =
        Poag1Bundle::load(flag_path(flags, "manifest")?).map_err(|error| error.to_string())?;
    let bound = bundle
        .bind_deployment(flag_path(flags, "deployment")?)
        .map_err(|error| error.to_string())?;
    let preview = if supplied_verification_flags == 0 {
        bound
            .unsigned_epoch_preview()
            .map_err(|error| error.to_string())?
    } else {
        let pin =
            CuratorKeyPin::load(flag_path(flags, "pin")?).map_err(|error| error.to_string())?;
        let envelope = ContentEpochEnvelope::load(flag_path(flags, "signature")?)
            .map_err(|error| error.to_string())?;
        let epoch = flag_u64(flags, "epoch")?;
        let counter = flag_u64(flags, "counter")?;
        let verified = envelope
            .verify(&bound, &pin, epoch, counter)
            .map_err(|error| error.to_string())?;
        verified
            .epoch_preview(&bound)
            .map_err(|error| error.to_string())?
    };
    println!(
        "{}",
        serde_json::to_string_pretty(&preview).map_err(|error| error.to_string())?
    );
    Ok(())
}

fn refuse_existing(path: &Path) -> Result<(), String> {
    match fs::symlink_metadata(path) {
        Ok(_) => Err(format!("refusing to overwrite {}", path.display())),
        Err(error) if error.kind() == std::io::ErrorKind::NotFound => Ok(()),
        Err(error) => Err(format!("cannot inspect {}: {error}", path.display())),
    }
}

fn load_secret_key(path: &Path) -> Result<SigningKey, String> {
    let mut options = OpenOptions::new();
    options.read(true);
    #[cfg(unix)]
    options.custom_flags(libc::O_NOFOLLOW);
    let mut file = options
        .open(path)
        .map_err(|error| format!("cannot open secret key {}: {error}", path.display()))?;
    let metadata = file
        .metadata()
        .map_err(|error| format!("cannot inspect secret key {}: {error}", path.display()))?;
    if !metadata.is_file() || metadata.len() != 32 {
        return Err(format!(
            "secret key {} must be one regular 32-byte file",
            path.display()
        ));
    }
    #[cfg(unix)]
    if metadata.mode() & 0o077 != 0 {
        return Err(format!(
            "secret key {} must not grant group/other permissions",
            path.display()
        ));
    }
    let mut bytes = [0u8; 32];
    file.read_exact(&mut bytes)
        .map_err(|error| format!("cannot read secret key {}: {error}", path.display()))?;
    Ok(SigningKey::from_bytes(&bytes))
}

fn atomic_write_new(path: &Path, bytes: &[u8], mode: u32) -> Result<(), String> {
    refuse_existing(path)?;
    let parent = path
        .parent()
        .filter(|path| !path.as_os_str().is_empty())
        .unwrap_or(Path::new("."));
    if !parent.is_dir() {
        return Err(format!(
            "output directory does not exist: {}",
            parent.display()
        ));
    }
    let file_name = path
        .file_name()
        .and_then(|name| name.to_str())
        .ok_or_else(|| format!("output path has no UTF-8 filename: {}", path.display()))?;
    for attempt in 0..128u32 {
        let temporary = parent.join(format!(".{file_name}.tmp-{}-{attempt}", std::process::id()));
        let mut options = OpenOptions::new();
        options.write(true).create_new(true);
        #[cfg(unix)]
        options.mode(mode);
        let mut file = match options.open(&temporary) {
            Ok(file) => file,
            Err(error) if error.kind() == std::io::ErrorKind::AlreadyExists => continue,
            Err(error) => return Err(format!("cannot create {}: {error}", temporary.display())),
        };
        let result = (|| {
            file.write_all(bytes)
                .map_err(|error| format!("cannot write {}: {error}", temporary.display()))?;
            file.sync_all()
                .map_err(|error| format!("cannot sync {}: {error}", temporary.display()))?;
            fs::hard_link(&temporary, path).map_err(|error| {
                if error.kind() == std::io::ErrorKind::AlreadyExists {
                    format!("refusing to overwrite {}", path.display())
                } else {
                    format!("cannot publish {}: {error}", path.display())
                }
            })?;
            File::open(parent)
                .and_then(|directory| directory.sync_all())
                .map_err(|error| format!("cannot sync {}: {error}", parent.display()))?;
            Ok(())
        })();
        let _ = fs::remove_file(&temporary);
        return result;
    }
    Err(format!(
        "could not allocate a temporary file beside {}",
        path.display()
    ))
}
