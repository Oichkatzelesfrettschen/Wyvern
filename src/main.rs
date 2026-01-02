//! # Wyvern Entry Point
//!
//! The main executable that initializes logging, profiling, and backend selection.
//!
//! ## Startup Sequence
//!
//! 1. Initialize tracing subscriber for structured logging (respects `RUST_LOG` env var)
//! 2. Initialize optional profiling (Tracy, Puffin)
//! 3. Create event channel for communication between event loop and handlers
//! 4. Parse command-line argument to determine backend
//! 5. Launch selected backend (udev, winit, or x11)
//!
//! ## Command-Line Arguments
//!
//! - `wyvern` - Use default backend (udev if available, else winit or x11)
//! - `wyvern --winit` - Force winit backend
//! - `wyvern --tty-udev` - Force udev backend on TTY
//! - `wyvern --x11` - Force X11 backend
//!
//! ## Environment Variables
//!
//! - `RUST_LOG`: Control logging verbosity (trace, debug, info, warn, error)
//! - Backend-specific variables documented in `config.example.toml`
//!
//! See [`wyvern`] crate documentation for architecture overview.

use calloop::channel;
#[cfg(feature = "udev")]
use wyvern::udev;
#[cfg(feature = "winit")]
use wyvern::winit;
#[cfg(feature = "x11")]
use wyvern::x11;

#[cfg(feature = "profile-with-tracy-mem")]
#[global_allocator]
static GLOBAL: profiling::tracy_client::ProfiledAllocator<std::alloc::System> =
    profiling::tracy_client::ProfiledAllocator::new(std::alloc::System, 10);

fn main() {
    if let Ok(env_filter) = tracing_subscriber::EnvFilter::try_from_default_env() {
        tracing_subscriber::fmt()
            .compact()
            .with_env_filter(env_filter)
            .init();
    } else {
        tracing_subscriber::fmt().compact().init();
    }

    #[cfg(feature = "profile-with-tracy")]
    profiling::tracy_client::Client::start();

    profiling::register_thread!("Main Thread");

    #[cfg(feature = "profile-with-puffin")]
    let _server =
        puffin_http::Server::new(&format!("0.0.0.0:{}", puffin_http::DEFAULT_PORT)).unwrap();
    #[cfg(feature = "profile-with-puffin")]
    profiling::puffin::set_scopes_on(true);

    let (event_tx, event_rx) = channel::channel();

    let arg = ::std::env::args().nth(1);
    match arg.as_deref() {
        #[cfg(feature = "winit")]
        Some("--winit") => {
            tracing::info!("Starting Wyvern with winit backend");
            winit::run_winit(event_rx, event_tx.clone());
        }
        #[cfg(feature = "udev")]
        Some("--tty-udev") => {
            tracing::info!("Starting Wyvern on a tty using udev");
            udev::run_udev(event_rx, event_tx.clone());
        }
        #[cfg(feature = "x11")]
        Some("--x11") => {
            tracing::info!("Starting Wyvern with x11 backend");
            x11::run_x11(event_rx, event_tx.clone());
        }
        Some(other) => {
            tracing::error!("Unknown backend: {}", other);
        }
        #[cfg(feature = "udev")]
        None => {
            udev::run_udev(event_rx, event_tx.clone());
        }
        #[cfg(feature = "winit")]
        #[cfg(not(feature = "udev"))]
        None => {
            winit::run_winit(event_rx, event_tx.clone());
        }
        #[cfg(feature = "x11")]
        #[cfg(not(any(feature = "udev", feature = "winit")))]
        None => {
            x11::run_x11(event_rx, event_tx.clone());
        }
        #[cfg(not(any(feature = "udev", feature = "winit", feature = "x11")))]
        None => {
            tracing::error!(
                "No backend enabled. Build with at least one of: --features udev, winit, or x11"
            );
        }
    }
}
