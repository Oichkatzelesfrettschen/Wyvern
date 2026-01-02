# Wyvern Compositor - Technical Standards & Practices

## Build & Test Commands

### Setup
```bash
# Install toolchain (Nightly 2026-01-01)
rustup update nightly-2026-01-01
rustup override set nightly-2026-01-01

# Install dependencies (Arch Linux example)
sudo pacman -S libwayland libxcb libinput libseat

# Clone and build
git clone https://github.com/Oichkatzelesfrettschen/Wyvern
cd Wyvern
cargo build --release
```

### Daily Development
```bash
# Check for errors
cargo check --all-features

# Run linter (must pass with zero warnings)
cargo clippy --all-targets --all-features -- -D warnings

# Format code
cargo fmt

# Run tests
cargo test --all-features

# Run compositor
cargo run --release -- --winit  # Dev: nested window
cargo run --release -- --udev   # Prod: standalone (needs seatd)
```

### Profiling & Performance
```bash
# Profile with Tracy (visual frame analysis)
TRACY_ENABLE=1 cargo run --features profile-with-tracy -- --winit
# Open http://localhost:8086 in browser

# Generate flamegraph
cargo flamegraph -- --winit

# Benchmark layout algorithm
cargo bench

# Check memory allocations
valgrind --tool=massif ./target/release/wyvern -- --winit
```

## Project Structure

### Modules
- **src/main.rs** - Entry point, backend selector
- **src/state.rs** - WyvernState, window management (50KB)
- **src/input_handler.rs** - Keyboard/pointer routing (58KB)
- **src/udev.rs** - DRM/KMS backend (1.8K LOC)
- **src/winit.rs** - Nested window backend (18KB)
- **src/x11.rs** - X11 backend (19KB)
- **src/render.rs** - Rendering pipeline (7.9KB)
- **src/shell/** - Wayland protocol handlers
  - **shell/mod.rs** - Layer shell, toplevels
  - **shell/xdg.rs** - XDG shell protocol (651 LOC)
  - **shell/grabs.rs** - Window move/resize grabs
  - **shell/ssd.rs** - Server-side decorations
- **src/config.rs** - Config file loading
- **src/focus.rs** - Window focus & cycling

### Dependencies (Key)
- **smithay** v0.7.0 - Wayland compositor framework
- **wayland-server** v0.31.9 - Wire protocol
- **winit** v0.30.12 - Window management
- **parking_lot** v0.12.5 - Fast locks
- **once_cell** v1.21.3 - Lazy statics
- **tracing** v0.1.37 - Structured logging

## Development Practices

### Code Quality
- All compiler warnings must be fixed (-D warnings in CI)
- Clippy warnings treated as errors
- Format code with `cargo fmt`
- Unsafe blocks must have safety comments (// SAFETY: ...)
- Unsafe code in FFI boundaries only (libwayland, libdrm, EGL, GL)

### Safety Standards
- No `unsafe static mut` (use `once_cell` or `AtomicBool`)
- No raw pointer dereferences without SAFETY comments
- Wayland buffer lifecycle checked on drop
- Input event ranges validated (coordinates within screen bounds)

### Testing
- Unit tests in same file as code
- Integration tests in tests/
- Performance regressions caught by criterion benchmarks
- Miri run on unsafe blocks: `cargo miri test`
- Infer run monthly: `infer run -- cargo build`

### Observability
- Structured logging via tracing spans
- Enable with `RUST_LOG=wyvern=debug cargo run ...`
- Frame profiling via Tracy (feature: profile-with-tracy)
- Memory profiling via Valgrind/dhat

## Backends (Features)

### Udev/DRM (Standalone)
- Default for release builds
- Requires: libseat, seatd or logind
- Supports: Multi-GPU, hotplug, TTY switching
- Run: `cargo run --release -- --udev`

### Winit (Development)
- Default for debug builds
- Nests inside host X11/Wayland
- No special requirements
- Run: `cargo run -- --winit`

### X11 (Compatibility)
- Runs as X11 window, hosts XWayland
- Experimental, used for testing
- Run: `cargo run -- --x11`

## Common Issues & Solutions

### "Permission denied" on --udev
**Solution:** Start seatd
```bash
seatd -u "$USER" &
cargo run -- --udev
```

### "XWayland failed to start" on X11 backend
**Solution:** Ensure X11 socket writeable
```bash
chmod 1777 /tmp/.X11-unix
```

### "GLES context creation failed"
**Solution:** Check GPU driver
```bash
glxinfo | grep "OpenGL version"
```

### Slow frame rates (< 30 FPS)
**Solution:** Profile with flamegraph
```bash
cargo flamegraph -- --winit
# Identify hot functions, prioritize bottlenecks
```

## References

- [Smithay Documentation](https://docs.rs/smithay/0.7.0/)
- [Wayland Protocol Spec](https://wayland.freedesktop.org/)
- [XDG Shell Protocol](https://wayland.freedesktop.org/xdg-shell/)
- [Architecture Guide](./docs/ARCHITECTURE.md)
- [Roadmap & Milestones](./TODOS_AND_BRAINSTORMS.md)

---

**Last Updated:** 2026-01-01
**Maintained By:** Eirikr
