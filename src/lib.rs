#![warn(rust_2018_idioms)]
// If no backend is enabled, a large portion of the codebase is unused.
// So silence this useless warning for the CI.
#![cfg_attr(
    not(any(feature = "winit", feature = "x11", feature = "udev")),
    allow(dead_code, unused_imports)
)]
//! # Wyvern Wayland Compositor
//!
//! Wyvern is a modern, minimal Wayland compositor built on [Smithay](https://smithay.info).
//! It provides multiple backends for different execution environments:
//! - **udev** (default): Full-featured DRM/KMS backend for production use on Wayland/Linux
//! - **winit**: Desktop windowing backend for development and testing
//! - **x11**: X11 server backend for compatibility with legacy X11 environments
//!
//! ## Architecture Overview
//!
//! Wyvern follows a modular event-driven architecture:
//! - [`state`]: Central compositor state machine managing clients, surfaces, and rendering
//! - [`shell`]: Protocol handlers for XDG shell and X11 window management
//! - [`render`]: Abstract rendering interface supporting EGL + OpenGL ES
//! - [`input_handler`]: Keyboard and pointer event processing
//! - [`drawing`]: Layer rendering and element composition
//! - [`focus`]: Window focus and keyboard focus management
//! - [`udev`], [`winit`], [`x11`]: Backend-specific implementations
//!
//! ## Module Organization
//!
//! - **Core modules** (always compiled): [`state`], [`shell`], [`render`], [`drawing`], [`focus`], [`input_handler`]
//! - **Backend modules** (feature-gated): [`udev`], [`winit`], [`x11`]
//! - **Utilities**: [`config`], [`cursor`]
//!
//! ## Building and Running
//!
//! ```bash
//! # Build with all backends
//! cargo build --release
//!
//! # Build with specific backends
//! cargo build --features udev,egl
//! cargo build --features winit,egl
//! cargo build --features x11,egl
//!
//! # Run with backend selection
//! ./target/release/wyvern         # Uses default backend
//! ./target/release/wyvern --udev  # Force udev backend
//! ```
//!
//! ## Configuration
//!
//! See `config.example.toml` for all available environment variables and command-line options.
//! Key variables: `WYVERN_DRM_DEVICE`, `WYVERN_DISABLE_10BIT`, `WYVERN_NO_VULKAN`, `RUST_LOG`
//!
//! ## Safety
//!
//! All unsafe blocks are documented with `// SAFETY:` comments explaining:
//! - The contract being upheld
//! - Why the invariant is guaranteed
//! - What could go wrong if the invariant is violated
//!
//! See [`docs/ARCHITECTURE.md`](../docs/ARCHITECTURE.md) for detailed safety analysis.

pub mod config;
#[cfg(any(feature = "udev", feature = "xwayland"))]
pub mod cursor;
pub mod drawing;
pub mod focus;
pub mod input_handler;
pub mod render;
pub mod shell;
pub mod state;
#[cfg(feature = "udev")]
pub mod udev;
#[cfg(feature = "winit")]
pub mod winit;
#[cfg(feature = "x11")]
pub mod x11;

pub use state::{ClientState, WyvernState};
