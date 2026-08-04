use std::collections::BTreeMap;
use std::env;
use std::fs::{self, File, OpenOptions};
use std::io::{Read, Write};
use std::path::{Path, PathBuf};

#[cfg(unix)]
use std::os::unix::fs::{MetadataExt, OpenOptionsExt};

use dregg_types::{SigningKey, generate_keypair};
use poa_curator::{
    ContentEpochEnvelope, CuratorKeyPin, CuratorSigner, DETACHED_SIGNATURE_FILENAME, Poag1Bundle,
};

const USAGE: &str = r#"poa-curator — Path of Angels development content ceremony

usage:
  poa-curator keygen --secret PATH --pin PATH
  poa-curator sign-content --secret PATH --pin PATH --manifest PATH --deployment PATH --epoch N --counter N [--output PATH]
  poa-curator verify-content --pin PATH --manifest PATH --deployment PATH --epoch N --counter N [--signature PATH]
  poa-curator preview-epoch --manifest PATH --deployment PATH [--pin PATH --signature PATH --epoch N --counter N]
  poa-curator signal-replay --bundle PATH

`keygen` creates a DEVELOPMENT beta curator key, never a Sentyr identity. It
refuses to overwrite either output and writes the raw 32-byte secret mode 0600.

`preview-epoch` is read-only JSON. With no signature tuple it loudly reports an
unsigned WIP; signature status becomes valid only when all four verification
flags are supplied and verify against the exact bundle and deployment.

`signal-replay` is read-only. It verifies an exact exported durable-wire bundle,
reruns every transition through native Lean, and prints one machine-readable
JSON report naming the deterministic final head.
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
        "signal-replay" => command_signal_replay(&flags),
        other => Err(format!("unknown command {other:?}\n\n{USAGE}")),
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
