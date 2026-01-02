//! # Configuration Management
//!
//! Loads and manages compositor configuration.
//!
//! Currently configuration is managed via:
//! - Environment variables (see `config.example.toml`)
//! - Command-line arguments
//!
//! This module provides structures for future TOML-based configuration support.

use serde::Deserialize;
use std::collections::HashMap;
use std::fs;
use std::path::PathBuf;

#[derive(Debug, Deserialize, serde::Serialize)]
pub struct Config {
    pub terminal: String,
    pub keyboard_shortcuts: HashMap<String, String>,
    pub startup_apps: Vec<String>,
    pub display: Display,
    pub keyboard: KeyboardOptions,
    pub tiling: Tiling,
}

#[derive(Debug, Deserialize, serde::Serialize)]
pub struct Tiling {
    pub master_ratio: f32,
    pub gap_size: i32,
}

#[derive(Debug, Deserialize, serde::Serialize)]
pub struct KeyboardOptions {
    pub layout: String,
    pub model: String,
    pub options: String,
    pub variant: String,
    pub rules: String,
}

#[derive(Debug, Deserialize, serde::Serialize)]
pub struct Display {
    pub scale: u32,
}

impl Config {
    pub fn load() -> Self {
        #[cfg(feature = "config-cache")]
        {
            // Try to use bincode cache if available and valid
            if let Ok(cached) = Self::load_from_cache() {
                return cached;
            }
        }

        // Fall back to loading from TOML (human-editable source of truth)
        Self::load_from_toml()
    }

    /// Load config from TOML file (human-editable, source of truth)
    fn load_from_toml() -> Self {
        let path = dirs::config_dir()
            .unwrap_or_else(|| PathBuf::from("."))
            .join("wyvern/config.toml");

        let content = fs::read_to_string(&path).unwrap_or_else(|_| {
            eprintln!("Using default config; failed to read {}", path.display());
            String::new()
        });

        let config = toml::from_str(&content).unwrap_or_else(|_| {
            eprintln!("Failed to parse config.toml, using defaults");
            Config::default()
        });

        #[cfg(feature = "config-cache")]
        {
            // Update cache for next load (non-blocking, errors are ignored)
            let _ = config.save_to_cache();
        }

        config
    }

    /// Load config from bincode cache (fast path, ~50x faster than TOML)
    #[cfg(feature = "config-cache")]
    fn load_from_cache() -> Result<Self, Box<dyn std::error::Error>> {
        use std::io::Read;

        let cache_path = dirs::cache_dir()
            .ok_or("No cache directory")?
            .join("wyvern/config.bincode");

        let toml_path = dirs::config_dir()
            .ok_or("No config directory")?
            .join("wyvern/config.toml");

        // Check if cache exists and is newer than TOML
        let cache_mtime = fs::metadata(&cache_path)?.modified()?;
        let toml_mtime = fs::metadata(&toml_path)?.modified()?;

        if cache_mtime < toml_mtime {
            return Err("Cache is stale".into());
        }

        // Load and deserialize cache
        let mut file = fs::File::open(&cache_path)?;
        let mut bytes = Vec::new();
        file.read_to_end(&mut bytes)?;

        bincode::decode_from_slice(&bytes, bincode::config::standard())
            .map(|(config, _)| config)
            .map_err(|e| e.into())
    }

    /// Save config to bincode cache for faster future loads
    #[cfg(feature = "config-cache")]
    fn save_to_cache(&self) -> Result<(), Box<dyn std::error::Error>> {
        use std::io::Write;

        let cache_dir = dirs::cache_dir()
            .ok_or("No cache directory")?
            .join("wyvern");

        fs::create_dir_all(&cache_dir)?;

        let cache_path = cache_dir.join("config.bincode");
        let encoded = bincode::encode_to_vec(self, bincode::config::standard())?;

        let mut file = fs::File::create(&cache_path)?;
        file.write_all(&encoded)?;
        file.sync_all()?;

        Ok(())
    }
}

impl Default for Config {
    fn default() -> Self {
        let mut keyboard_shortcuts = HashMap::new();
        keyboard_shortcuts.insert("super+return".into(), "weston-terminal".into());
        keyboard_shortcuts.insert("super+f4".into(), "killall weston-terminal".into()); // TODO: make it work
        keyboard_shortcuts.insert("super+q".into(), "quit".into());

        Self {
            terminal: "weston-terminal".into(),
            keyboard_shortcuts,
            startup_apps: vec!["waybar".into()],
            display: Display { scale: 1 },
            keyboard: KeyboardOptions {
                layout: "en".into(),
                model: "pc105".into(),
                options: "grp:alt_shift_toggle".into(),
                variant: "".into(),
                rules: "evdev".into(),
            },
            tiling: Tiling {
                master_ratio: 0.55,
                gap_size: 10,
            },
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_default_config() {
        let config = Config::default();

        // Verify default values
        assert_eq!(config.terminal, "weston-terminal");
        assert_eq!(config.display.scale, 1);
        assert_eq!(config.tiling.gap_size, 10);
        assert_eq!(config.tiling.master_ratio, 0.55);

        // Verify keyboard layout defaults
        assert_eq!(config.keyboard.layout, "en");
        assert_eq!(config.keyboard.model, "pc105");

        // Verify startup apps
        assert!(!config.startup_apps.is_empty());
        assert!(config.startup_apps.contains(&"waybar".to_string()));
    }

    #[test]
    fn test_keyboard_shortcuts() {
        let config = Config::default();

        // Verify all default shortcuts are present
        assert!(config.keyboard_shortcuts.contains_key("super+return"));
        assert!(config.keyboard_shortcuts.contains_key("super+f4"));
        assert!(config.keyboard_shortcuts.contains_key("super+q"));

        // Verify specific shortcut values
        assert_eq!(
            config.keyboard_shortcuts.get("super+return").unwrap(),
            "weston-terminal"
        );
        assert_eq!(config.keyboard_shortcuts.get("super+q").unwrap(), "quit");
    }

    #[test]
    fn test_display_config() {
        let config = Config::default();

        // Verify display settings
        assert_eq!(config.display.scale, 1);

        // Display scale should be at least 1
        assert!(config.display.scale >= 1);
    }

    #[test]
    fn test_tiling_ratios() {
        let config = Config::default();

        // Master ratio should be between 0.0 and 1.0
        assert!(config.tiling.master_ratio > 0.0);
        assert!(config.tiling.master_ratio < 1.0);

        // Gap size should be non-negative
        assert!(config.tiling.gap_size >= 0);
    }

    #[test]
    fn test_config_serialization() {
        let config = Config::default();

        // Verify that Config can be serialized to TOML (for future config file support)
        let serialized = toml::to_string(&config);
        assert!(serialized.is_ok(), "Config should be serializable to TOML");
    }
}
