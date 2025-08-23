use wyvern::udev;
use wyvern::winit;
use wyvern::x11;
use calloop::channel;

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
        None => {
            udev::run_udev(event_rx, event_tx.clone());
        }
    }
}
