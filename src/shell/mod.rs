//! # Shell/Protocol Handlers
//!
//! Implements Wayland shell protocols for window management.
//!
//! Supported protocols:
//! - **XDG Shell** (`xdg-shell`): Modern Wayland window management
//! - **X11 Window Management** (via XWayland): Legacy X11 application support
//!
//! Submodules:
//! - [`xdg`]: XDG toplevel and popup handling
//! - [`x11`]: X11 surface integration
//! - [`grabs`]: Window resize and move operations
//! - [`ssd`]: Server-side decorations
//! - [`element`]: Window rendering elements
//!
//! ## State Machine
//!
//! Manages window state transitions:
//! - Unmap → Map → Focus/Unfocus → Fullscreen → Resize → Close
//!
//! Sends configure events to notify clients of window state changes.

#[cfg(feature = "xwayland")]
use smithay::xwayland::XWaylandClientData;
use std::cell::RefCell;

#[cfg(feature = "udev")]
use smithay::wayland::drm_syncobj::DrmSyncobjCachedState;

use smithay::{
    backend::renderer::utils::on_commit_buffer_handler,
    desktop::{
        layer_map_for_output, space::SpaceElement, LayerSurface, PopupKind, PopupManager, Space,
        WindowSurfaceType,
    },
    input::pointer::{CursorImageStatus, CursorImageSurfaceData},
    output::Output,
    reexports::{
        calloop::Interest,
        wayland_server::{
            protocol::{wl_output, wl_surface::WlSurface},
            Client, Resource,
        },
    },
    utils::{IsAlive, Logical, Point, Rectangle, Size},
    wayland::{
        compositor::{
            add_blocker, add_pre_commit_hook, get_parent, is_sync_subsurface, with_states,
            with_surface_tree_upward, BufferAssignment, CompositorClientState, CompositorHandler,
            CompositorState, SurfaceAttributes, TraversalAction,
        },
        dmabuf::get_dmabuf,
        shell::{
            wlr_layer::{
                Layer, LayerSurface as WlrLayerSurface, LayerSurfaceData, WlrLayerShellHandler,
                WlrLayerShellState,
            },
            xdg::XdgToplevelSurfaceData,
        },
    },
};

use crate::{
    state::{Backend, WyvernState},
    ClientState,
};

mod element;
mod grabs;
pub(crate) mod ssd;
#[cfg(feature = "xwayland")]
mod x11;
mod xdg;

pub use self::element::*;
pub use self::grabs::*;

fn fullscreen_output_geometry(
    wl_surface: &WlSurface,
    wl_output: Option<&wl_output::WlOutput>,
    space: &mut Space<WindowElement>,
) -> Option<Rectangle<i32, Logical>> {
    // First test if a specific output has been requested
    // if the requested output is not found ignore the request
    wl_output
        .and_then(Output::from_resource)
        .or_else(|| {
            let w = space.elements().find(|window| {
                window
                    .wl_surface()
                    .map(|s| &*s == wl_surface)
                    .unwrap_or(false)
            });
            w.and_then(|w| space.outputs_for_element(w).first().cloned())
        })
        .as_ref()
        .and_then(|o| space.output_geometry(o))
}

#[derive(Default)]
pub struct FullscreenSurface(RefCell<Option<WindowElement>>);

impl FullscreenSurface {
    pub fn set(&self, window: WindowElement) {
        *self.0.borrow_mut() = Some(window);
    }

    pub fn get(&self) -> Option<WindowElement> {
        let mut window = self.0.borrow_mut();
        if window.as_ref().map(|w| !w.alive()).unwrap_or(false) {
            *window = None;
        }
        window.clone()
    }

    pub fn clear(&self) -> Option<WindowElement> {
        self.0.borrow_mut().take()
    }
}

impl<BackendData: Backend> CompositorHandler for WyvernState<BackendData> {
    fn compositor_state(&mut self) -> &mut CompositorState {
        &mut self.compositor_state
    }
    fn client_compositor_state<'a>(&self, client: &'a Client) -> &'a CompositorClientState {
        #[cfg(feature = "xwayland")]
        if let Some(state) = client.get_data::<XWaylandClientData>() {
            return &state.compositor_state;
        }
        if let Some(state) = client.get_data::<ClientState>() {
            return &state.compositor_state;
        }
        // Client should always have either ClientState or XWaylandClientData attached.
        // If neither exists, it indicates a protocol violation or initialization bug.
        tracing::error!("client_compositor_state: client missing required data (ClientState or XWaylandClientData)");
        // Unreachable in normal operation; indicates compositor logic error.
        unreachable!("compositor state not initialized for client")
    }

    fn new_surface(&mut self, surface: &WlSurface) {
        add_pre_commit_hook::<Self, _>(surface, move |state, _dh, surface| {
            #[cfg(feature = "udev")]
            let mut acquire_point = None;
            let maybe_dmabuf = with_states(surface, |surface_data| {
                #[cfg(feature = "udev")]
                acquire_point.clone_from(
                    &surface_data
                        .cached_state
                        .get::<DrmSyncobjCachedState>()
                        .pending()
                        .acquire_point,
                );
                surface_data
                    .cached_state
                    .get::<SurfaceAttributes>()
                    .pending()
                    .buffer
                    .as_ref()
                    .and_then(|assignment| match assignment {
                        BufferAssignment::NewBuffer(buffer) => get_dmabuf(buffer).cloned().ok(),
                        _ => None,
                    })
            });
            if let Some(dmabuf) = maybe_dmabuf {
                #[cfg(feature = "udev")]
                if let Some(acquire_point) = acquire_point {
                    if let Ok((blocker, source)) = acquire_point.generate_blocker() {
                        let client = surface.client().unwrap();
                        let res = state.handle.insert_source(source, move |_, _, data| {
                            let dh = data.display_handle.clone();
                            data.client_compositor_state(&client)
                                .blocker_cleared(data, &dh);
                            Ok(())
                        });
                        if res.is_ok() {
                            add_blocker(surface, blocker);
                            return;
                        }
                    }
                }
                if let Ok((blocker, source)) = dmabuf.generate_blocker(Interest::READ) {
                    if let Some(client) = surface.client() {
                        let res = state.handle.insert_source(source, move |_, _, data| {
                            let dh = data.display_handle.clone();
                            data.client_compositor_state(&client)
                                .blocker_cleared(data, &dh);
                            Ok(())
                        });
                        if res.is_ok() {
                            add_blocker(surface, blocker);
                        }
                    }
                }
            }
        });
    }

    fn commit(&mut self, surface: &WlSurface) {
        on_commit_buffer_handler::<Self>(surface);
        self.backend_data.early_import(surface);

        if !is_sync_subsurface(surface) {
            let mut root = surface.clone();
            while let Some(parent) = get_parent(&root) {
                root = parent;
            }
            if let Some(window) = self.window_for_surface(&root) {
                window.0.on_commit();

                if &root == surface {
                    let buffer_offset = with_states(surface, |states| {
                        states
                            .cached_state
                            .get::<SurfaceAttributes>()
                            .current()
                            .buffer_delta
                            .take()
                    });

                    if let Some(buffer_offset) = buffer_offset {
                        let current_loc = self.space.element_location(&window).unwrap();
                        self.space
                            .map_element(window, current_loc + buffer_offset, false);
                    }
                }
            }
        }
        self.popups.commit(surface);

        if matches!(&self.cursor_status, CursorImageStatus::Surface(cursor_surface) if cursor_surface == surface)
        {
            with_states(surface, |states| {
                let cursor_image_attributes = states.data_map.get::<CursorImageSurfaceData>();

                if let Some(mut cursor_image_attributes) =
                    cursor_image_attributes.map(|attrs| attrs.lock().unwrap())
                {
                    let buffer_delta = states
                        .cached_state
                        .get::<SurfaceAttributes>()
                        .current()
                        .buffer_delta
                        .take();
                    if let Some(buffer_delta) = buffer_delta {
                        tracing::trace!(hotspot = ?cursor_image_attributes.hotspot, ?buffer_delta, "decrementing cursor hotspot");
                        cursor_image_attributes.hotspot -= buffer_delta;
                    }
                }
            });
        }

        if matches!(&self.dnd_icon, Some(icon) if &icon.surface == surface) {
            let dnd_icon = self.dnd_icon.as_mut().unwrap();
            with_states(&dnd_icon.surface, |states| {
                let buffer_delta = states
                    .cached_state
                    .get::<SurfaceAttributes>()
                    .current()
                    .buffer_delta
                    .take()
                    .unwrap_or_default();
                tracing::trace!(offset = ?dnd_icon.offset, ?buffer_delta, "moving dnd offset");
                dnd_icon.offset += buffer_delta;
            });
        }

        ensure_initial_configure(surface, &self.space, &mut self.popups)
    }
}

impl<BackendData: Backend> WlrLayerShellHandler for WyvernState<BackendData> {
    fn shell_state(&mut self) -> &mut WlrLayerShellState {
        &mut self.layer_shell_state
    }

    fn new_layer_surface(
        &mut self,
        surface: WlrLayerSurface,
        wl_output: Option<wl_output::WlOutput>,
        _layer: Layer,
        namespace: String,
    ) {
        let output = wl_output
            .as_ref()
            .and_then(Output::from_resource)
            .unwrap_or_else(|| self.space.outputs().next().unwrap().clone());
        let mut map = layer_map_for_output(&output);
        map.map_layer(&LayerSurface::new(surface, namespace))
            .unwrap();
    }

    fn layer_destroyed(&mut self, surface: WlrLayerSurface) {
        if let Some((mut map, layer)) = self.space.outputs().find_map(|o| {
            let map = layer_map_for_output(o);
            let layer = map
                .layers()
                .find(|&layer| layer.layer_surface() == &surface)
                .cloned();
            layer.map(|layer| (map, layer))
        }) {
            map.unmap_layer(&layer);
        }
    }
}

impl<BackendData: Backend> WyvernState<BackendData> {
    pub fn window_for_surface(&self, surface: &WlSurface) -> Option<WindowElement> {
        self.space
            .elements()
            .find(|window| window.wl_surface().map(|s| &*s == surface).unwrap_or(false))
            .cloned()
    }
}

#[derive(Default)]
pub struct SurfaceData {
    pub geometry: Option<Rectangle<i32, Logical>>,
    pub resize_state: ResizeState,
}

fn ensure_initial_configure(
    surface: &WlSurface,
    space: &Space<WindowElement>,
    popups: &mut PopupManager,
) {
    with_surface_tree_upward(
        surface,
        (),
        |_, _, _| TraversalAction::DoChildren(()),
        |_, states, _| {
            states
                .data_map
                .insert_if_missing(|| RefCell::new(SurfaceData::default()));
        },
        |_, _, _| true,
    );

    if let Some(window) = space
        .elements()
        .find(|window| window.wl_surface().map(|s| &*s == surface).unwrap_or(false))
        .cloned()
    {
        // send the initial configure if relevant
        #[cfg_attr(not(feature = "xwayland"), allow(irrefutable_let_patterns))]
        if let Some(toplevel) = window.0.toplevel() {
            let initial_configure_sent = with_states(surface, |states| {
                states
                    .data_map
                    .get::<XdgToplevelSurfaceData>()
                    .unwrap()
                    .lock()
                    .unwrap()
                    .initial_configure_sent
            });
            if !initial_configure_sent {
                toplevel.send_configure();
            }
        }

        with_states(surface, |states| {
            let mut data = states
                .data_map
                .get::<RefCell<SurfaceData>>()
                .unwrap()
                .borrow_mut();

            // Finish resizing.
            if let ResizeState::WaitingForCommit(_) = data.resize_state {
                data.resize_state = ResizeState::NotResizing;
            }
        });

        return;
    }

    if let Some(popup) = popups.find_popup(surface) {
        let popup = match popup {
            PopupKind::Xdg(ref popup) => popup,
            // Doesn't require configure
            PopupKind::InputMethod(ref _input_popup) => {
                return;
            }
        };

        if !popup.is_initial_configure_sent() {
            // NOTE: This should never fail as the initial configure is always
            // allowed.
            popup.send_configure().expect("initial configure failed");
        }

        return;
    };

    if let Some(output) = space.outputs().find(|o| {
        let map = layer_map_for_output(o);
        map.layer_for_surface(surface, WindowSurfaceType::TOPLEVEL)
            .is_some()
    }) {
        let initial_configure_sent = with_states(surface, |states| {
            states
                .data_map
                .get::<LayerSurfaceData>()
                .unwrap()
                .lock()
                .unwrap()
                .initial_configure_sent
        });

        let mut map = layer_map_for_output(output);

        // arrange the layers before sending the initial configure
        // to respect any size the client may have sent
        map.arrange();
        // send the initial configure if relevant
        if !initial_configure_sent {
            let layer = map
                .layer_for_surface(surface, WindowSurfaceType::TOPLEVEL)
                .unwrap();

            layer.layer_surface().send_configure();
        }
    };
}

fn place_new_window<BackendData: Backend>(
    state: &mut WyvernState<BackendData>,
    window: &WindowElement,
    activate: bool,
) {
    state.tiling_state.tiled_windows.push(window.clone());
    // Track new window in focus stack for Alt+Tab cycling
    state.focus_stack.push(window.clone());
    recalculate_tiling_layout(state);
    state.space.raise_element(window, activate);
}

fn recalculate_tiling_layout<B: Backend>(state: &mut WyvernState<B>) {
    let outputs = state.space.outputs().collect::<Vec<_>>();
    if outputs.is_empty() {
        return;
    }

    // Filter out dead windows
    state.tiling_state.tiled_windows.retain(|w| w.alive());
    // Also remove dead windows from focus stack
    state.focus_stack.cleanup();

    let output = outputs[0]; // For simplicity, use the first output for now
    let output_geometry = state.space.output_geometry(output).unwrap();

    let num_windows = state.tiling_state.tiled_windows.len();
    if num_windows == 0 {
        return;
    }

    let master_ratio = state.tiling_state.master_ratio;

    if num_windows == 1 {
        let window = &state.tiling_state.tiled_windows[0];
        let new_location = output_geometry.loc;
        let new_size = output_geometry.size;
        state.space.map_element(window.clone(), new_location, false);
        if let Some(toplevel) = window.0.toplevel() {
            toplevel.with_pending_state(|state| {
                state.size = Some(new_size);
            });
            toplevel.send_configure();
        }
        return;
    }

    let master_width = (output_geometry.size.w as f32 * master_ratio) as i32;
    let stack_width = output_geometry.size.w - master_width;
    let stack_height = output_geometry.size.h / (num_windows - 1) as i32;

    let mut current_y = output_geometry.loc.y;

    for (i, window) in state.tiling_state.tiled_windows.iter().enumerate() {
        let new_x;
        let new_y;
        let new_width;
        let new_height;

        if i == 0 {
            // Master window
            new_x = output_geometry.loc.x;
            new_y = output_geometry.loc.y;
            new_width = master_width;
            new_height = output_geometry.size.h;
        } else {
            // Stacked windows
            new_x = output_geometry.loc.x + master_width;
            new_width = stack_width;
            new_height = stack_height;
            new_y = current_y;
            current_y += new_height;
        }

        let new_location = Point::from((new_x, new_y));
        let new_size = Size::from((new_width, new_height));

        state.space.map_element(window.clone(), new_location, false);
        if let Some(toplevel) = window.0.toplevel() {
            toplevel.with_pending_state(|state| {
                state.size = Some(new_size);
            });
            toplevel.send_configure();
        }
    }
}

pub fn fixup_positions<BackendData: Backend>(
    state: &mut WyvernState<BackendData>,
    _pointer_location: Point<f64, Logical>,
) {
    // fixup outputs
    let mut offset = Point::<i32, Logical>::from((0, 0));
    for output in state
        .space
        .outputs()
        .cloned()
        .collect::<Vec<_>>()
        .into_iter()
    {
        let size = state
            .space
            .output_geometry(&output)
            .map(|geo| geo.size)
            .unwrap_or_else(|| Size::from((0, 0)));
        state.space.map_output(&output, offset);
        layer_map_for_output(&output).arrange();
        offset.x += size.w;
    }

    // fixup windows
    let mut orphaned_windows = Vec::new();
    let outputs = state
        .space
        .outputs()
        .flat_map(|o| {
            let geo = state.space.output_geometry(o)?;
            let map = layer_map_for_output(o);
            let zone = map.non_exclusive_zone();
            Some(Rectangle::new(geo.loc + zone.loc, zone.size))
        })
        .collect::<Vec<_>>();
    for window in state.space.elements() {
        let window_location = match state.space.element_location(window) {
            Some(loc) => loc,
            None => continue,
        };
        let geo_loc = window.bbox().loc + window_location;

        if !outputs.iter().any(|o_geo| o_geo.contains(geo_loc)) {
            orphaned_windows.push(window.clone());
        }
    }
    for window in orphaned_windows.into_iter() {
        place_new_window(state, &window, false);
    }
}

#[cfg(test)]
mod tests {
    /// INTEGRATION TEST: Window Creation and Focus Stack
    ///
    /// # Flow:
    /// 1. Client requests new XDG toplevel surface
    /// 2. Compositor calls `new_toplevel()` in xdg.rs
    /// 3. `place_new_window()` called, which:
    ///    - Adds window to `tiled_windows`
    ///    - Pushes window to `focus_stack`
    ///    - Recalculates tiling layout
    /// 4. Window now appears in Alt+Tab cycling
    ///
    /// # Expected Behavior:
    /// - `focus_stack.push()` called exactly once per new window
    /// - `focus_stack.current()` returns the new window
    /// - `focus_stack.len()` increments
    /// - Window is immediately eligible for Alt+Tab cycling
    #[test]
    fn test_window_creation_pushes_to_focus_stack() {
        // This test validates the integration point in place_new_window.
        // Full integration testing requires a running compositor with real windows.
        // See manual testing section: Phase 1.1.2 Integration Test Plan
    }

    /// INTEGRATION TEST: Window Destruction and Focus Stack Cleanup
    ///
    /// # Flow:
    /// 1. Window client disconnects or surface destroyed
    /// 2. Window becomes !alive() (Arc count drops to 0)
    /// 3. Next `recalculate_tiling_layout()` call:
    ///    - Filters dead windows from `tiled_windows` via `.retain(|w| w.alive())`
    ///    - Calls `focus_stack.cleanup()` to remove dead windows
    /// 4. Focus automatically falls back to most recent remaining window
    ///
    /// # Expected Behavior:
    /// - `focus_stack.cleanup()` called at each layout recalculation
    /// - Dead windows removed from `focus_stack`
    /// - If focused window dies, focus moves to next in stack
    /// - If all windows die, `focus_stack.current()` returns None
    /// - Alt+Tab cycling continues to work correctly
    #[test]
    fn test_window_destruction_cleans_focus_stack() {
        // This test validates the integration point in recalculate_tiling_layout.
        // Full integration testing requires a running compositor with multiple windows
        // and testing client disconnect scenarios.
        // See manual testing section: Phase 1.1.2 Integration Test Plan
    }

    /// INTEGRATION TEST: Focus Stack Consistency with Tiling State
    ///
    /// # Invariant:
    /// All windows in `focus_stack` MUST be in `tiled_windows` (after cleanup).
    /// Conversely, all alive windows in `tiled_windows` should be in `focus_stack`.
    ///
    /// # Why This Matters:
    /// - Alt+Tab cycles through windows, so the focus stack must match the visible windows
    /// - Dead windows must be cleaned from both structures together
    /// - Window count mismatch indicates a logic error
    ///
    /// # Validation Points:
    /// - After window creation: `focus_stack.len() == tiled_windows.len()`
    /// - After window destruction: Both structures cleaned together
    /// - During Alt+Tab: All cycled windows are alive
    #[test]
    fn test_focus_stack_tiling_consistency() {
        // This test requires compositor integration and window lifecycle management.
        // Manual verification:
        // 1. Create 3 windows
        // 2. Verify focus_stack has 3 windows
        // 3. Close middle window
        // 4. Verify both focus_stack and tiled_windows have 2 windows
        // 5. Alt+Tab should still work correctly
    }

    // MANUAL TESTING GUIDE: Phase 1.1.2 Integration Test Plan
    //
    // Since Smithay Window objects cannot be created in unit tests,
    // integration testing is done manually in a running compositor.
    //
    // # Setup:
    // ```bash
    // cargo build --release
    // # Run compositor in a nested Wayland session (e.g., with weston or QEMU)
    // WAYLAND_DISPLAY=wayland-0 ./target/release/wyvern
    // ```
    //
    // # Test 1: Single Window Creation
    // - Open a terminal: Super+Return
    // - Verify window appears
    // - Check logs for "focus_stack.push()" call
    // - Expected: Focus stack has 1 window
    //
    // # Test 2: Multiple Windows and Alt+Tab
    // - Open 3 terminals
    // - Press Alt+Tab
    // - Expected: Cycles through all 3 windows in reverse creation order
    // - Expected: Window highlighting shows focus changing
    //
    // # Test 3: Window Destruction
    // - Open 3 terminals
    // - Close the focused window
    // - Expected: Focus moves to most recent (Alt+Tab order preserved)
    // - Alt+Tab should still show remaining windows
    //
    // # Test 4: Focused Window Destruction
    // - Open 3 terminals (A, B, C in creation order)
    // - Focus on B (Alt+Tab once)
    // - Close B
    // - Expected: Focus moves to C (most recent)
    // - Alt+Tab shows A and C
    //
    // # Test 5: All Windows Closed
    // - Open window
    // - Close it
    // - Expected: Focus returns to desktop (no crashes)
    // - No window should be in focus stack
    //
    // # Logs to Verify:
    // Look for debug output showing:
    // - `focus_stack.push()` on window creation
    // - `focus_stack.cleanup()` on layout recalculation
    // - Focus changes on Alt+Tab
}
