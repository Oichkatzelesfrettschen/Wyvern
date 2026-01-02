# Wyvern Architecture Guide

**Last Updated:** 2026-01-01
**Framework:** Smithay v0.7.0
**Language:** Rust (nightly-2026-01-01)

---

## 1. System Overview

Wyvern is a Wayland compositor built on the Smithay framework. It manages the display server lifecycle, handles input events, routes client requests, and coordinates rendering across multiple backends.

### Role in System Architecture

```
┌─────────────────────────────────────────────────────┐
│ Wayland Clients (Applications)                       │
│  - XDG Shell (windows)                              │
│  - Layer Shell (panels, overlays)                   │
│  - XWayland (legacy X11 apps)                       │
└──────────────────┬──────────────────────────────────┘
                   │ Wayland Protocol (local socket)
┌──────────────────▼──────────────────────────────────┐
│ Wyvern Compositor                                    │
│  - Protocol Dispatch (shell/*)                      │
│  - Window Management (state.rs)                     │
│  - Input Routing (input_handler.rs)                 │
│  - Rendering Coordination (render.rs, drawing.rs)   │
└──────────────────┬──────────────────────────────────┘
                   │
        ┌──────────┼──────────┐
        │          │          │
   ┌────▼──┐  ┌───▼────┐ ┌──▼────┐
   │ Udev  │  │ Winit  │ │  X11  │
   │Backend│  │Backend │ │Backend│
   └────┬──┘  └───┬────┘ └──┬────┘
        │         │         │
   ┌────▼─────────▼─────────▼────┐
   │ Hardware / Host Display      │
   │ (DRM/KMS, Wayland, X11)      │
   └─────────────────────────────┘
```

### Key Responsibilities

1. **Protocol Handler** - Wayland wire protocol parsing and client lifecycle
2. **Compositor** - Window layout, tiling, fullscreen/maximize operations
3. **Input Dispatcher** - Keyboard shortcuts, pointer routing, grab management
4. **Renderer** - GPU command submission, damage tracking, frame timing
5. **Backend Abstraction** - GPU driver interface (DRM, Vulkan, GL)

---

## 2. Backend Abstraction Pattern

Wyvern supports three runtime backends through a common trait-based abstraction:

```rust
pub trait Backend: Sized + 'static {
    type Surface: RenderSurface;
    // ... backend-specific implementation
}
```

### Backend Selection

All three backends implement identical protocol handlers (shell/, input_handler.rs) through compile-time feature flags:

| Backend | Feature | Use Case | GUI Environment |
|---------|---------|----------|-----------------|
| **udev** | `udev` | Production standalone compositor | TTY (tty1-tty6) |
| **winit** | `winit` | Development nested compositor | X11 or Wayland (host desktop) |
| **x11** | `x11` | Testing and compatibility | X11 window |

### Backend-Specific Data Structures

Each backend maintains distinct context:

#### UdevData (Production DRM/KMS Backend)
```
UdevData {
  devices: HashMap<DrmDeviceHandle, Rc<Device>>,      // GPU devices (single/multi-GPU)
  session: Session,                                    // libseat session manager
  input_backend: LibinputInputBackend,                // libinput device manager
  current_state: RenderingState,                      // Display configuration
  outputs: Vec<Output>,                               // Physical displays
  allocator: GbmAllocator,                            // Buffer allocation
  renderer: Option<GlesRenderer>,                     // OpenGL ES rendering
}
```

#### WinitData (Development Nested Backend)
```
WinitData {
  event_loop: WinitEventLoop,    // Nested Wayland/X11 event loop
  window: WinitWindow,            // Host window
  renderer: GlesRenderer,         // OpenGL ES rendering context
  buffer_queue: BufferQueue,     // Page flip state
}
```

#### X11Data (X11 Compatibility Backend)
```
X11Data {
  connection: X11Connection,      // X11 protocol socket
  window: X11Window,              // Compositor window (drawable)
  egl_display: EGLDisplay,        // OpenGL ES context
  renderer: GlesRenderer,         // Rendering backend
  xwayland: Option<XWaylandData>, // X11 application support
}
```

### WyvernState Generic Pattern

The central compositor state is parameterized over `BackendData`:

```rust
pub struct WyvernState<BackendData: Backend> {
    // Shared across all backends (62 fields total)
    pub space: Space<Window>,              // Window tree and layout
    pub outputs: Vec<Output>,              // Display configuration
    pub compositor_state: CompositorState,
    pub shell_state: WlrShellState,
    pub xdg_shell_state: XdgShellState,
    // ... protocol state, input state, etc.

    // Backend-specific
    pub backend_data: BackendData,
}
```

This pattern allows:
- **Single Protocol Implementation** - shell/mod.rs, input_handler.rs work identically
- **Backend-Specific Rendering** - Each backend's `render()` call is optimized for its hardware
- **Type Safety** - Compile-time verification that backends implement required traits

---

## 3. Module Layering

Files are organized by abstraction layer:

### Layer 1: Protocol Handlers (shell/)
**Purpose:** Parse Wayland protocol requests, validate state, delegate to compositor

- **shell/mod.rs** (476 lines) - Smithay delegate! macros, protocol state initialization
- **shell/xdg.rs** (651 lines) - XDG Shell (toplevel windows, popups, grabs)
- **shell/grabs.rs** (761 lines) - **CRITICAL** - Move/resize grab state machine
- **shell/x11.rs** (334 lines) - XWayland integration, X11 window mapping
- **shell/xdg.rs** (651 lines) - Keyboard focus, pointer constraints

**Key Exports:**
- `XdgShellState` - Toplevel window management
- `ResizeGrab` - Window resize state machine
- `PointerConstraintsHandler` - Cursor confinement

### Layer 2: Compositor Core (state.rs, input_handler.rs)
**Purpose:** Window management, tiling layout, input routing

- **state.rs** (1272 lines) - WyvernState struct, window operations, tiling layout calculation
  - **Complexity:** High (50KB file with 62-field state struct)
  - **Key Methods:**
    - `new()` - Compositor initialization
    - `recalculate_tiling()` - Master/stack layout with gaps
    - `map_window()` - Add window to layout
    - `unmap_window()` - Remove window from layout

- **input_handler.rs** (1456 lines) - Keyboard/pointer event dispatch
  - **Complexity:** High (58KB file, ~200 branches)
  - **Key Handlers:**
    - `keyboard_handle()` - Hotkey detection, text input
    - `pointer_button()` - Window selection, button grabs
    - `pointer_motion()` - Cursor position updates
    - `pointer_axis()` - Scroll wheel handling

**Key Structures:**
```rust
pub enum Focus {
    Window(Window),
    Fullscreen(FullscreenSurface),
    Layer(LayerSurface),
}

pub struct Tiling {
    master_width: f64,           // Master pane width ratio
    gap_size: i32,               // Pixel gap between windows
    master_windows: usize,       // # windows in master pane
}
```

### Layer 3: Rendering Abstraction (render.rs, drawing.rs)
**Purpose:** Abstract rendering operations, manage damage tracking

- **render.rs** - RenderSurface trait, damage region tracking
- **drawing.rs** (345 lines) - FPS counter, debug overlays, frame composition

**Key Operations:**
- Scene composition (apply damage, render elements)
- FPS ticker (1000 ms sample window)
- PNG screenshot capture (debug feature)

### Layer 4: Backend Implementations (udev.rs, winit.rs, x11.rs)

#### udev.rs (1766 lines) - DRM/KMS Production Backend
**Initialization:** `run_udev()`
```
1. Create libseat session
2. Enumerate DRM devices (GPU discovery)
3. Create GBM allocator
4. Initialize GLES renderer
5. Register for udev hotplug events
6. Create calloop event sources:
   - DRM device events (mode changes, page flips)
   - Input device events (libinput)
   - Custom events (tiling recalculation)
7. Enter event loop
```

**Key Types:**
- `DrmDevice` - Single GPU context (DRM FD, CRTC/plane state)
- `RenderingState` - Output configuration (mode, scale, transform)
- `FrameResult` - Page flip completion tracking

**Multi-GPU Support:** Uses HashMap<DrmDeviceHandle, Device> for concurrent GPU usage

#### winit.rs (505 lines) - Nested Wayland/X11 Backend
**Initialization:** `run_winit()`
```
1. Create WinitEventLoop (connects to host Wayland/X11)
2. Create nested window
3. Initialize GLES renderer
4. Create page flip queue
5. Register window event sources
6. Enter event loop
```

**Key Limitation:** Single window = single output (no multi-monitor in winit mode)

#### x11.rs (512 lines) - X11 Compatibility Backend
**Initialization:** `run_x11()`
```
1. Connect to X11 server
2. Create X11 drawable (compositor window)
3. Initialize EGL/GLES
4. Setup XWayland integration (Optional: feature "xwayland")
5. Register X11 events
6. Enter event loop
```

**Critical Bug (TODO):** Drop order of GlesRenderer vs X11Surface (line 67-68)

---

## 4. Key Data Structures

### Window Tree (space.rs - from Smithay)
```
Space<Window> {
  layers: LayerMap,          // Background/bottom/top/overlay stacking
  mapped_windows: Vec<(Window, Point)>,  // Window positions and order
  // Queries: overlapping windows, focus cycle, output assignment
}
```

### Window Mapping Sequence
```
Client Request (XdgShell::commit)
  ↓ (shell/xdg.rs)
WyvernState::map_window()
  ↓ (state.rs)
space.insert_window()
  ↓
recalculate_tiling()  ← Repositions all windows based on layout
  ↓
Schedule render frame
  ↓ (next frame)
Composite all windows
  ↓
Schedule hardware flip (udev backend) or swap buffers (gl backend)
  ↓
Client sees window on screen
```

### Focus Management
```
pub struct FocusState {
    keyboard_focus: Option<Focus>,
    pointer_focus: Option<PointerFocusTarget>,
    grab: Option<PointerGrab>,
}
```

**Focus Priority:** Exclusive grab > Popup > Toplevel > Layer > None

---

## 5. Event Loop Architecture

Wyvern uses `calloop::EventLoop` (async-free event dispatcher) with these event sources:

### Event Sources by Backend

**Udev Backend:**
- DRM device events (CRTC page flip completion)
- Udev device hotplug events (GPU added/removed)
- libinput input events (keyboard/pointer/touchpad)
- Custom event channel (tiling recalculation signals)

**Winit Backend:**
- Winit window events (mouse, keyboard, window close)
- Custom event channel (tiling recalculation signals)

**X11 Backend:**
- X11 protocol events (window operations, input)
- Custom event channel (tiling recalculation signals)

### Event Loop Flow
```
loop {
    // Wait for events (1000 * 1000 / 60 = ~16.6ms for 60 FPS)
    events = event_loop.dispatch(timeout);

    for event in events {
        match event {
            DrmPageFlip => schedule_next_frame(),
            InputEvent => dispatch_to_focused_surface(),
            ClientRequest => process_protocol_request(),
            CustomEvent::TilingRecalculate => recalculate_tiling(),
        }
    }

    // Render frame if dirty
    if frame_scheduled {
        render_frame();
        submit_to_gpu();
    }
}
```

---

## 6. Protocol Integration Points

### Wayland Protocol Flow

```
Client (XDG Shell Request: map toplevel)
  ↓ (socket)
Wayland Server (smithay-backend)
  ↓
delegate_xdg_shell!(WyvernState<BackendData>)
  ↓ (shell/xdg.rs)
WyvernState::map_window()
  ↓ (state.rs)
space.insert_window() + recalculate_tiling()
  ↓
Next render frame:
  - composite_window(window, offset)
  - submit_frame(damage_region)
  ↓ (client callback)
frame_callback { time = now }  ← Client uses for animation
```

### Protocol Handlers Implemented

| Protocol | Handler | File | Features |
|----------|---------|------|----------|
| wl_compositor | CompositorHandler | shell/mod.rs | Buffer attachment, surface damage |
| xdg-shell | XdgShellHandler | shell/xdg.rs | Toplevels, popups, resizing, fullscreen |
| wlr-layer-shell | WlrLayerShellHandler | shell/mod.rs | Panels, overlays, exclusive zones |
| wl_pointer | PointerHandler | input_handler.rs | Motion, button, axis (scroll) |
| wl_keyboard | KeyboardHandler | input_handler.rs | Key press, key repeat, modifiers |
| xwayland | XWaylandHandler | shell/x11.rs | X11 window bridge (optional feature) |

---

## 7. Rendering Pipeline

### Frame Composition (udev backend example)

```
1. Fetch damage region (areas that changed)
   damage = space.damage_since_last_frame()

2. Clear damage areas
   renderer.clear(damage, color::BLACK)

3. Composite windows in order
   for window in space.windows_in_z_order() {
       element = RenderElement::from_window(window)
       renderer.render_element(element, damage)
   }

4. Composite debug overlays (if debug feature)
   if cfg!(debug) {
       fps_ticker.render_frame(renderer)
   }

5. Submit to GPU
   surface.queue_buffer(renderer.finish())
   surface.swap_buffers()  // or schedule_page_flip()

6. Wait for page flip (vsync)
   event_loop.wait_for(DrmPageFlip)

7. Schedule next frame
   callback = next_frame_callback()
```

### Damage Tracking (Optimization)
- Only re-render areas that changed (not full screen each frame)
- Reduces GPU load by 50-70% in static scenes
- Uses `Region` abstraction (union of dirty rectangles)

### Rendering State Machine
```
Idle → ScheduleFrame → Rendering → Submitted → WaitingForFlip → Idle
                                     ↓
                              (on flip complete)
                              frame_callback event
```

---

## 8. Safety & Unsafe Code Audit

All unsafe blocks are FFI-related (GPU driver calls require raw pointers):

| File | Line | Operation | Safety Invariant |
|------|------|-----------|------------------|
| x11.rs | 134 | EGLDisplay::new(device) | Device outlives display |
| x11.rs | 202 | GlesRenderer::new(context) | Context valid for lifetime |
| state.rs | 728 | display.get_mut().dispatch_clients() | No concurrent mutation |
| udev.rs | 829 | EGLDisplay::new(gbm) | GBM device outlives display |

**Safety Model:** Single-threaded event loop prevents concurrent access; all mutable state accessed via `&mut self`.

---

## 9. Adding a New Backend

To implement a new backend (e.g., VNC, RDP, nested Wayland):

1. **Implement `Backend` trait** (state.rs)
   ```rust
   pub trait Backend: Sized + 'static {
       type Surface: RenderSurface;
       fn render_frame(&self) -> Result<(), RenderError>;
       fn recalculate_layout(&mut self, state: &WyvernState<Self>);
   }
   ```

2. **Create backend module** (new file: src/your_backend.rs)
   ```rust
   pub struct YourBackendData { /* ... */ }

   impl Backend for YourBackendData {
       // Implement trait methods
   }

   pub fn run_your_backend(
       event_rx_main: calloop::channel::Channel<CustomEvent>,
       event_tx_for_state: calloop::channel::Sender<CustomEvent>,
   ) {
       // 1. Initialize event loop
       // 2. Create display server
       // 3. Initialize backend data
       // 4. Register event sources
       // 5. Enter loop
   }
   ```

3. **Add feature flag** (Cargo.toml)
   ```toml
   [features]
   your_backend = ["smithay/backend_x", ...]
   ```

4. **Wire up main.rs**
   ```rust
   #[cfg(feature = "your_backend")]
   fn run_your_backend(...) { ... }
   ```

5. **Add protocol handlers** (inherit from state.rs, no changes needed)

---

## 10. Common Architectural Patterns

### 1. "Startup Apps" Hack (input_handler.rs:70-85)
**Why:** XWayland initialization was unconditional, wasting resources
**Current:** AtomicBool gate (spawn apps only once)
**Phase 1 Plan:** Socket activation (lazy XWayland)

### 2. CCN Monolith (state.rs:1272 lines, CCN=62)
**Why:** Window management logic intermixed with rendering, input, protocol handling
**Symptom:** Hard to trace, easy to introduce bugs
**Phase 2 Plan:** Extract to state/layout.rs, state/focus.rs modules

### 3. Winit Nesting Trap (winit.rs:1 output limit)
**Why:** Smithay's winit backend doesn't support multi-monitor nesting
**Impact:** Useless for production; good for testing only
**Phase 1 Plan:** Document limitation, maybe add SDL3 backend

### 4. Drop Order Bug (x11.rs:67-68)
**Why:** GlesRenderer drops before X11Surface; causes MakeCurrent to fail
**Risk:** Intermittent crashes when exiting
**Phase 0 Fix:** Reorder struct fields or use ManuallyDrop

---

## 11. References

- [Smithay Documentation](https://docs.rs/smithay/0.7.0/)
- [Wayland Protocol Spec](https://wayland.freedesktop.org/)
- [XDG Shell Specification](https://wayland.freedesktop.org/xdg-shell/)
- [DRM/KMS Linux Kernel Docs](https://dri.freedesktop.org/)
- [calloop Event Loop](https://docs.rs/calloop/)

---

**End of Architecture Document**
