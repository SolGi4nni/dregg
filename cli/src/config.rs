//! Configuration management for `~/.dregg/config.toml`.

use std::path::PathBuf;

use serde::{Deserialize, Serialize};

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Config {
    #[serde(default = "NodeConfig::default")]
    pub node: NodeConfig,
    #[serde(default = "OutputConfig::default")]
    pub output: OutputConfig,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct NodeConfig {
    #[serde(default = "default_node_url")]
    pub url: String,
    /// Bearer token for the node's protected endpoints (turn submission, cap
    /// ops, etc.). Obtained from `POST /cipherclerk/unlock` (`bearer_token`).
    /// Sent as `Authorization: Bearer <token>`. Optional — public reads
    /// (status, identity, producer, cells) work without it.
    #[serde(default)]
    pub token: Option<String>,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct OutputConfig {
    #[serde(default = "default_format")]
    pub format: String,
}

fn default_node_url() -> String {
    "http://localhost:8420".to_string()
}

fn default_format() -> String {
    "color".to_string()
}

impl Default for NodeConfig {
    fn default() -> Self {
        Self {
            url: default_node_url(),
            token: None,
        }
    }
}

impl Default for OutputConfig {
    fn default() -> Self {
        Self {
            format: default_format(),
        }
    }
}

impl Default for Config {
    fn default() -> Self {
        Self {
            node: NodeConfig::default(),
            output: OutputConfig::default(),
        }
    }
}

/// Returns the default config path. Honors `DREGG_HOME` (→ `$DREGG_HOME/config.toml`)
/// for a hermetic, testable config root — used by the preflight check, CI, and
/// sandboxes so `dregg config init` never mutates the operator's real `~/.dregg`.
/// Falls back to `~/.dregg/config.toml`.
pub fn config_path() -> PathBuf {
    if let Ok(home) = std::env::var("DREGG_HOME") {
        if !home.is_empty() {
            return PathBuf::from(home).join("config.toml");
        }
    }
    let base = dirs::home_dir().unwrap_or_else(|| PathBuf::from("."));
    base.join(".dregg").join("config.toml")
}

impl Config {
    /// Load config from the given path (or default). Missing file => defaults.
    ///
    /// On parse failure (corrupt or hand-edited TOML), logs a warning to stderr
    /// and falls back to safe built-in defaults rather than silently ignoring
    /// the user's settings. This closes a bad-UX gap where `dregg config set`
    /// or manual edits could be lost without any indication.
    pub fn load(path: Option<&str>) -> Self {
        let file_path = match path {
            Some(p) => PathBuf::from(p),
            None => config_path(),
        };

        if !file_path.exists() {
            return Config::default();
        }

        match std::fs::read_to_string(&file_path) {
            Ok(contents) => match toml::from_str(&contents) {
                Ok(cfg) => cfg,
                Err(e) => {
                    eprintln!(
                        "warning: failed to parse config file {}: {}. Using built-in defaults.",
                        file_path.display(),
                        e
                    );
                    Config::default()
                }
            },
            Err(e) => {
                if file_path.exists() {
                    eprintln!(
                        "warning: failed to read config file {}: {}. Using built-in defaults.",
                        file_path.display(),
                        e
                    );
                }
                Config::default()
            }
        }
    }

    /// Write the default config to the given path, creating parent dirs.
    pub fn write_default(path: &PathBuf) -> Result<(), Box<dyn std::error::Error>> {
        if let Some(parent) = path.parent() {
            std::fs::create_dir_all(parent)?;
        }
        let default = Config::default();
        let toml_str = toml::to_string_pretty(&default)?;
        std::fs::write(path, toml_str)?;
        Ok(())
    }

    /// Returns true if output format is JSON.
    pub fn is_json(&self) -> bool {
        self.output.format == "json"
    }
}

/// Set a dotted key in the config file. Creates the file if it doesn't exist.
pub fn set_value(key: &str, value: &str) -> Result<(), Box<dyn std::error::Error>> {
    let path = config_path();
    let mut cfg = Config::load(Some(path.to_str().unwrap_or("")));

    match key {
        "node.url" => cfg.node.url = value.to_string(),
        "node.token" => cfg.node.token = Some(value.to_string()),
        "output.format" => {
            if !["color", "plain", "json"].contains(&value) {
                return Err(format!("Invalid format '{}'. Use: color, plain, json", value).into());
            }
            cfg.output.format = value.to_string();
        }
        _ => {
            // Note: "cclerk.keyfile" was a legacy/dead setting (never loaded or used
            // by any CLI command; all cipherclerk ops proxy through the node). It is
            // no longer accepted to avoid user confusion.
            return Err(format!(
                "Unknown config key '{}'. Valid keys: node.url, node.token, output.format",
                key
            )
            .into());
        }
    }

    if let Some(parent) = path.parent() {
        std::fs::create_dir_all(parent)?;
    }
    let toml_str = toml::to_string_pretty(&cfg)?;
    std::fs::write(&path, toml_str)?;
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    /// The hermetic-root contract that the preflight `cli_config_init` check
    /// (preflight/src/checks/cli.rs) relies on: when `DREGG_HOME` is set,
    /// `config_path()` resolves to `$DREGG_HOME/config.toml` and `config init`
    /// (`Config::write_default` on that path) writes THERE — never into the
    /// operator's real `~/.dregg`. The empty-`DREGG_HOME` case must fall back
    /// to `~/.dregg/config.toml`.
    ///
    /// All `DREGG_HOME` mutation lives in this single test because the env var
    /// is process-global; splitting it would race the other test threads. We
    /// snapshot and restore the variable so the suite leaves no residue.
    #[test]
    fn dregg_home_redirects_config_init_hermetically() {
        let saved = std::env::var_os("DREGG_HOME");
        // SAFETY: edition-2024 marks env mutation `unsafe`; this is the only
        // test touching `DREGG_HOME`, and it restores the prior value below.
        let restore = || unsafe {
            match &saved {
                Some(v) => std::env::set_var("DREGG_HOME", v),
                None => std::env::remove_var("DREGG_HOME"),
            }
        };

        // What the real `~/.dregg/config.toml` resolves to — the path the
        // hermetic redirect must NOT collide with.
        let real_home_cfg = dirs::home_dir()
            .unwrap_or_else(|| PathBuf::from("."))
            .join(".dregg")
            .join("config.toml");

        let tmp = tempfile::tempdir().expect("temp dir");
        let expected = tmp.path().join("config.toml");

        // SAFETY: see above.
        unsafe {
            std::env::set_var("DREGG_HOME", tmp.path());
        }

        // 1. The redirect: config_path() points into the temp root, not ~/.dregg.
        let resolved = config_path();
        assert_eq!(
            resolved, expected,
            "DREGG_HOME must redirect config_path() to $DREGG_HOME/config.toml"
        );
        assert_ne!(
            resolved, real_home_cfg,
            "the hermetic redirect must NOT resolve to the operator's real ~/.dregg/config.toml"
        );

        // 2. `dregg config init` (write_default on that path) lands in the temp
        //    root and produces a config the loader round-trips.
        assert!(
            !expected.exists(),
            "temp config must not pre-exist (tempdir is fresh)"
        );
        Config::write_default(&resolved).expect("write_default into DREGG_HOME");
        assert!(
            expected.exists(),
            "config init must write $DREGG_HOME/config.toml at {}",
            expected.display()
        );
        let loaded = Config::load(Some(resolved.to_str().unwrap()));
        assert_eq!(loaded.node.url, default_node_url());
        assert_eq!(loaded.output.format, default_format());

        // 3. The empty-DREGG_HOME guard: a blank override is ignored, falling
        //    back to ~/.dregg (so an empty env var can't hijack the root).
        // SAFETY: see above.
        unsafe {
            std::env::set_var("DREGG_HOME", "");
        }
        assert_eq!(
            config_path(),
            real_home_cfg,
            "empty DREGG_HOME must fall back to ~/.dregg/config.toml"
        );

        restore();
        // tmp's Drop removes the throwaway root, leaving no on-disk residue.
    }
}
