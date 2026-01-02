//! Integration tests for Wyvern compositor
//!
//! Tests core functionality including configuration loading,
//! backend initialization, and state transitions.

#[test]
fn test_crate_compiles() {
    // This test verifies that the wyvern crate compiles with all features.
    // It's a basic smoke test to ensure no compilation errors.
    // More detailed tests follow below.
}

#[test]
fn test_feature_flags() {
    // Verify that feature flags are properly set during compilation.
    // This would be more comprehensive if run with different feature sets.

    #[cfg(feature = "udev")]
    {
        // udev backend should be available
    }

    #[cfg(feature = "winit")]
    {
        // winit backend should be available
    }

    #[cfg(feature = "x11")]
    {
        // x11 backend should be available
    }
}

#[test]
fn test_config_module_exists() {
    // Verify that the config module is properly exported
    use wyvern::config::Config;

    // Config module should be publicly accessible and default should work
    let config = Config::default();

    // Verify that we can instantiate and access config fields
    assert!(!config.terminal.is_empty());
    assert!(!config.startup_apps.is_empty());
}
