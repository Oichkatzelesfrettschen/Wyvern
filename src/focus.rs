//! # Focus Management
//!
//! Keyboard and pointer focus tracking for windows and surfaces.
//!
//! Manages:
//! - Keyboard focus (which window receives keyboard input)
//! - Pointer focus (which window receives mouse input)
//! - Focus cycl ing and navigation between windows
//! - XWayland window focus integration
//!
//! Focus state changes trigger protocol updates (e.g., `wl_keyboard::enter`/`leave`)
//! to notify clients of focus changes.

use std::borrow::Cow;

#[cfg(feature = "xwayland")]
use smithay::xwayland::X11Surface;
pub use smithay::{
    backend::input::KeyState,
    desktop::{LayerSurface, PopupKind},
    input::{
        keyboard::{KeyboardTarget, KeysymHandle, ModifiersState},
        pointer::{AxisFrame, ButtonEvent, MotionEvent, PointerTarget, RelativeMotionEvent},
        Seat,
    },
    reexports::wayland_server::{backend::ObjectId, protocol::wl_surface::WlSurface, Resource},
    utils::{IsAlive, Serial},
    wayland::seat::WaylandFocus,
};
use smithay::{
    desktop::{Window, WindowSurface},
    input::{
        pointer::{
            GestureHoldBeginEvent, GestureHoldEndEvent, GesturePinchBeginEvent,
            GesturePinchEndEvent, GesturePinchUpdateEvent, GestureSwipeBeginEvent,
            GestureSwipeEndEvent, GestureSwipeUpdateEvent,
        },
        touch::TouchTarget,
    },
};

use crate::{
    shell::{WindowElement, SSD},
    state::{Backend, WyvernState},
};

#[derive(Debug, Clone, PartialEq)]
#[allow(clippy::large_enum_variant)]
pub enum KeyboardFocusTarget {
    Window(Window),
    LayerSurface(LayerSurface),
    Popup(PopupKind),
}

impl IsAlive for KeyboardFocusTarget {
    #[inline]
    fn alive(&self) -> bool {
        match self {
            KeyboardFocusTarget::Window(w) => w.alive(),
            KeyboardFocusTarget::LayerSurface(l) => l.alive(),
            KeyboardFocusTarget::Popup(p) => p.alive(),
        }
    }
}

#[derive(Debug, Clone, PartialEq)]
pub enum PointerFocusTarget {
    WlSurface(WlSurface),
    #[cfg(feature = "xwayland")]
    X11Surface(X11Surface),
    SSD(SSD),
}

impl IsAlive for PointerFocusTarget {
    #[inline]
    fn alive(&self) -> bool {
        match self {
            PointerFocusTarget::WlSurface(w) => w.alive(),
            #[cfg(feature = "xwayland")]
            PointerFocusTarget::X11Surface(w) => w.alive(),
            PointerFocusTarget::SSD(x) => x.alive(),
        }
    }
}

impl From<PointerFocusTarget> for WlSurface {
    #[inline]
    fn from(target: PointerFocusTarget) -> Self {
        target.wl_surface().unwrap().into_owned()
    }
}

impl<BackendData: Backend> PointerTarget<WyvernState<BackendData>> for PointerFocusTarget {
    fn enter(
        &self,
        seat: &Seat<WyvernState<BackendData>>,
        data: &mut WyvernState<BackendData>,
        event: &MotionEvent,
    ) {
        match self {
            PointerFocusTarget::WlSurface(w) => PointerTarget::enter(w, seat, data, event),
            #[cfg(feature = "xwayland")]
            PointerFocusTarget::X11Surface(w) => PointerTarget::enter(w, seat, data, event),
            PointerFocusTarget::SSD(w) => PointerTarget::enter(w, seat, data, event),
        }
    }
    fn motion(
        &self,
        seat: &Seat<WyvernState<BackendData>>,
        data: &mut WyvernState<BackendData>,
        event: &MotionEvent,
    ) {
        match self {
            PointerFocusTarget::WlSurface(w) => PointerTarget::motion(w, seat, data, event),
            #[cfg(feature = "xwayland")]
            PointerFocusTarget::X11Surface(w) => PointerTarget::motion(w, seat, data, event),
            PointerFocusTarget::SSD(w) => PointerTarget::motion(w, seat, data, event),
        }
    }
    fn relative_motion(
        &self,
        seat: &Seat<WyvernState<BackendData>>,
        data: &mut WyvernState<BackendData>,
        event: &RelativeMotionEvent,
    ) {
        match self {
            PointerFocusTarget::WlSurface(w) => {
                PointerTarget::relative_motion(w, seat, data, event)
            }
            #[cfg(feature = "xwayland")]
            PointerFocusTarget::X11Surface(w) => {
                PointerTarget::relative_motion(w, seat, data, event)
            }
            PointerFocusTarget::SSD(w) => PointerTarget::relative_motion(w, seat, data, event),
        }
    }
    fn button(
        &self,
        seat: &Seat<WyvernState<BackendData>>,
        data: &mut WyvernState<BackendData>,
        event: &ButtonEvent,
    ) {
        match self {
            PointerFocusTarget::WlSurface(w) => PointerTarget::button(w, seat, data, event),
            #[cfg(feature = "xwayland")]
            PointerFocusTarget::X11Surface(w) => PointerTarget::button(w, seat, data, event),
            PointerFocusTarget::SSD(w) => PointerTarget::button(w, seat, data, event),
        }
    }
    fn axis(
        &self,
        seat: &Seat<WyvernState<BackendData>>,
        data: &mut WyvernState<BackendData>,
        frame: AxisFrame,
    ) {
        match self {
            PointerFocusTarget::WlSurface(w) => PointerTarget::axis(w, seat, data, frame),
            #[cfg(feature = "xwayland")]
            PointerFocusTarget::X11Surface(w) => PointerTarget::axis(w, seat, data, frame),
            PointerFocusTarget::SSD(w) => PointerTarget::axis(w, seat, data, frame),
        }
    }
    fn frame(&self, seat: &Seat<WyvernState<BackendData>>, data: &mut WyvernState<BackendData>) {
        match self {
            PointerFocusTarget::WlSurface(w) => PointerTarget::frame(w, seat, data),
            #[cfg(feature = "xwayland")]
            PointerFocusTarget::X11Surface(w) => PointerTarget::frame(w, seat, data),
            PointerFocusTarget::SSD(w) => PointerTarget::frame(w, seat, data),
        }
    }
    fn leave(
        &self,
        seat: &Seat<WyvernState<BackendData>>,
        data: &mut WyvernState<BackendData>,
        serial: Serial,
        time: u32,
    ) {
        match self {
            PointerFocusTarget::WlSurface(w) => PointerTarget::leave(w, seat, data, serial, time),
            #[cfg(feature = "xwayland")]
            PointerFocusTarget::X11Surface(w) => PointerTarget::leave(w, seat, data, serial, time),
            PointerFocusTarget::SSD(w) => PointerTarget::leave(w, seat, data, serial, time),
        }
    }
    fn gesture_swipe_begin(
        &self,
        seat: &Seat<WyvernState<BackendData>>,
        data: &mut WyvernState<BackendData>,
        event: &GestureSwipeBeginEvent,
    ) {
        match self {
            PointerFocusTarget::WlSurface(w) => {
                PointerTarget::gesture_swipe_begin(w, seat, data, event)
            }
            #[cfg(feature = "xwayland")]
            PointerFocusTarget::X11Surface(w) => {
                PointerTarget::gesture_swipe_begin(w, seat, data, event)
            }
            PointerFocusTarget::SSD(w) => PointerTarget::gesture_swipe_begin(w, seat, data, event),
        }
    }
    fn gesture_swipe_update(
        &self,
        seat: &Seat<WyvernState<BackendData>>,
        data: &mut WyvernState<BackendData>,
        event: &GestureSwipeUpdateEvent,
    ) {
        match self {
            PointerFocusTarget::WlSurface(w) => {
                PointerTarget::gesture_swipe_update(w, seat, data, event)
            }
            #[cfg(feature = "xwayland")]
            PointerFocusTarget::X11Surface(w) => {
                PointerTarget::gesture_swipe_update(w, seat, data, event)
            }
            PointerFocusTarget::SSD(w) => PointerTarget::gesture_swipe_update(w, seat, data, event),
        }
    }
    fn gesture_swipe_end(
        &self,
        seat: &Seat<WyvernState<BackendData>>,
        data: &mut WyvernState<BackendData>,
        event: &GestureSwipeEndEvent,
    ) {
        match self {
            PointerFocusTarget::WlSurface(w) => {
                PointerTarget::gesture_swipe_end(w, seat, data, event)
            }
            #[cfg(feature = "xwayland")]
            PointerFocusTarget::X11Surface(w) => {
                PointerTarget::gesture_swipe_end(w, seat, data, event)
            }
            PointerFocusTarget::SSD(w) => PointerTarget::gesture_swipe_end(w, seat, data, event),
        }
    }
    fn gesture_pinch_begin(
        &self,
        seat: &Seat<WyvernState<BackendData>>,
        data: &mut WyvernState<BackendData>,
        event: &GesturePinchBeginEvent,
    ) {
        match self {
            PointerFocusTarget::WlSurface(w) => {
                PointerTarget::gesture_pinch_begin(w, seat, data, event)
            }
            #[cfg(feature = "xwayland")]
            PointerFocusTarget::X11Surface(w) => {
                PointerTarget::gesture_pinch_begin(w, seat, data, event)
            }
            PointerFocusTarget::SSD(w) => PointerTarget::gesture_pinch_begin(w, seat, data, event),
        }
    }
    fn gesture_pinch_update(
        &self,
        seat: &Seat<WyvernState<BackendData>>,
        data: &mut WyvernState<BackendData>,
        event: &GesturePinchUpdateEvent,
    ) {
        match self {
            PointerFocusTarget::WlSurface(w) => {
                PointerTarget::gesture_pinch_update(w, seat, data, event)
            }
            #[cfg(feature = "xwayland")]
            PointerFocusTarget::X11Surface(w) => {
                PointerTarget::gesture_pinch_update(w, seat, data, event)
            }
            PointerFocusTarget::SSD(w) => PointerTarget::gesture_pinch_update(w, seat, data, event),
        }
    }
    fn gesture_pinch_end(
        &self,
        seat: &Seat<WyvernState<BackendData>>,
        data: &mut WyvernState<BackendData>,
        event: &GesturePinchEndEvent,
    ) {
        match self {
            PointerFocusTarget::WlSurface(w) => {
                PointerTarget::gesture_pinch_end(w, seat, data, event)
            }
            #[cfg(feature = "xwayland")]
            PointerFocusTarget::X11Surface(w) => {
                PointerTarget::gesture_pinch_end(w, seat, data, event)
            }
            PointerFocusTarget::SSD(w) => PointerTarget::gesture_pinch_end(w, seat, data, event),
        }
    }
    fn gesture_hold_begin(
        &self,
        seat: &Seat<WyvernState<BackendData>>,
        data: &mut WyvernState<BackendData>,
        event: &GestureHoldBeginEvent,
    ) {
        match self {
            PointerFocusTarget::WlSurface(w) => {
                PointerTarget::gesture_hold_begin(w, seat, data, event)
            }
            #[cfg(feature = "xwayland")]
            PointerFocusTarget::X11Surface(w) => {
                PointerTarget::gesture_hold_begin(w, seat, data, event)
            }
            PointerFocusTarget::SSD(w) => PointerTarget::gesture_hold_begin(w, seat, data, event),
        }
    }
    fn gesture_hold_end(
        &self,
        seat: &Seat<WyvernState<BackendData>>,
        data: &mut WyvernState<BackendData>,
        event: &GestureHoldEndEvent,
    ) {
        match self {
            PointerFocusTarget::WlSurface(w) => {
                PointerTarget::gesture_hold_end(w, seat, data, event)
            }
            #[cfg(feature = "xwayland")]
            PointerFocusTarget::X11Surface(w) => {
                PointerTarget::gesture_hold_end(w, seat, data, event)
            }
            PointerFocusTarget::SSD(w) => PointerTarget::gesture_hold_end(w, seat, data, event),
        }
    }
}

impl<BackendData: Backend> KeyboardTarget<WyvernState<BackendData>> for KeyboardFocusTarget {
    fn enter(
        &self,
        seat: &Seat<WyvernState<BackendData>>,
        data: &mut WyvernState<BackendData>,
        keys: Vec<KeysymHandle<'_>>,
        serial: Serial,
    ) {
        match self {
            KeyboardFocusTarget::Window(w) => match w.underlying_surface() {
                WindowSurface::Wayland(w) => {
                    KeyboardTarget::enter(w.wl_surface(), seat, data, keys, serial)
                }
                #[cfg(feature = "xwayland")]
                WindowSurface::X11(s) => KeyboardTarget::enter(s, seat, data, keys, serial),
            },
            KeyboardFocusTarget::LayerSurface(l) => {
                KeyboardTarget::enter(l.wl_surface(), seat, data, keys, serial)
            }
            KeyboardFocusTarget::Popup(p) => {
                KeyboardTarget::enter(p.wl_surface(), seat, data, keys, serial)
            }
        }
    }
    fn leave(
        &self,
        seat: &Seat<WyvernState<BackendData>>,
        data: &mut WyvernState<BackendData>,
        serial: Serial,
    ) {
        match self {
            KeyboardFocusTarget::Window(w) => match w.underlying_surface() {
                WindowSurface::Wayland(w) => {
                    KeyboardTarget::leave(w.wl_surface(), seat, data, serial)
                }
                #[cfg(feature = "xwayland")]
                WindowSurface::X11(s) => KeyboardTarget::leave(s, seat, data, serial),
            },
            KeyboardFocusTarget::LayerSurface(l) => {
                KeyboardTarget::leave(l.wl_surface(), seat, data, serial)
            }
            KeyboardFocusTarget::Popup(p) => {
                KeyboardTarget::leave(p.wl_surface(), seat, data, serial)
            }
        }
    }
    fn key(
        &self,
        seat: &Seat<WyvernState<BackendData>>,
        data: &mut WyvernState<BackendData>,
        key: KeysymHandle<'_>,
        state: KeyState,
        serial: Serial,
        time: u32,
    ) {
        match self {
            KeyboardFocusTarget::Window(w) => match w.underlying_surface() {
                WindowSurface::Wayland(w) => {
                    KeyboardTarget::key(w.wl_surface(), seat, data, key, state, serial, time)
                }
                #[cfg(feature = "xwayland")]
                WindowSurface::X11(s) => {
                    KeyboardTarget::key(s, seat, data, key, state, serial, time)
                }
            },
            KeyboardFocusTarget::LayerSurface(l) => {
                KeyboardTarget::key(l.wl_surface(), seat, data, key, state, serial, time)
            }
            KeyboardFocusTarget::Popup(p) => {
                KeyboardTarget::key(p.wl_surface(), seat, data, key, state, serial, time)
            }
        }
    }
    fn modifiers(
        &self,
        seat: &Seat<WyvernState<BackendData>>,
        data: &mut WyvernState<BackendData>,
        modifiers: ModifiersState,
        serial: Serial,
    ) {
        match self {
            KeyboardFocusTarget::Window(w) => match w.underlying_surface() {
                WindowSurface::Wayland(w) => {
                    KeyboardTarget::modifiers(w.wl_surface(), seat, data, modifiers, serial)
                }
                #[cfg(feature = "xwayland")]
                WindowSurface::X11(s) => {
                    KeyboardTarget::modifiers(s, seat, data, modifiers, serial)
                }
            },
            KeyboardFocusTarget::LayerSurface(l) => {
                KeyboardTarget::modifiers(l.wl_surface(), seat, data, modifiers, serial)
            }
            KeyboardFocusTarget::Popup(p) => {
                KeyboardTarget::modifiers(p.wl_surface(), seat, data, modifiers, serial)
            }
        }
    }
}

impl<BackendData: Backend> TouchTarget<WyvernState<BackendData>> for PointerFocusTarget {
    fn down(
        &self,
        seat: &Seat<WyvernState<BackendData>>,
        data: &mut WyvernState<BackendData>,
        event: &smithay::input::touch::DownEvent,
        seq: Serial,
    ) {
        match self {
            PointerFocusTarget::WlSurface(w) => TouchTarget::down(w, seat, data, event, seq),
            #[cfg(feature = "xwayland")]
            PointerFocusTarget::X11Surface(w) => TouchTarget::down(w, seat, data, event, seq),
            PointerFocusTarget::SSD(w) => TouchTarget::down(w, seat, data, event, seq),
        }
    }

    fn up(
        &self,
        seat: &Seat<WyvernState<BackendData>>,
        data: &mut WyvernState<BackendData>,
        event: &smithay::input::touch::UpEvent,
        seq: Serial,
    ) {
        match self {
            PointerFocusTarget::WlSurface(w) => TouchTarget::up(w, seat, data, event, seq),
            #[cfg(feature = "xwayland")]
            PointerFocusTarget::X11Surface(w) => TouchTarget::up(w, seat, data, event, seq),
            PointerFocusTarget::SSD(w) => TouchTarget::up(w, seat, data, event, seq),
        }
    }

    fn motion(
        &self,
        seat: &Seat<WyvernState<BackendData>>,
        data: &mut WyvernState<BackendData>,
        event: &smithay::input::touch::MotionEvent,
        seq: Serial,
    ) {
        match self {
            PointerFocusTarget::WlSurface(w) => TouchTarget::motion(w, seat, data, event, seq),
            #[cfg(feature = "xwayland")]
            PointerFocusTarget::X11Surface(w) => TouchTarget::motion(w, seat, data, event, seq),
            PointerFocusTarget::SSD(w) => TouchTarget::motion(w, seat, data, event, seq),
        }
    }

    fn frame(
        &self,
        seat: &Seat<WyvernState<BackendData>>,
        data: &mut WyvernState<BackendData>,
        seq: Serial,
    ) {
        match self {
            PointerFocusTarget::WlSurface(w) => TouchTarget::frame(w, seat, data, seq),
            #[cfg(feature = "xwayland")]
            PointerFocusTarget::X11Surface(w) => TouchTarget::frame(w, seat, data, seq),
            PointerFocusTarget::SSD(w) => TouchTarget::frame(w, seat, data, seq),
        }
    }

    fn cancel(
        &self,
        seat: &Seat<WyvernState<BackendData>>,
        data: &mut WyvernState<BackendData>,
        seq: Serial,
    ) {
        match self {
            PointerFocusTarget::WlSurface(w) => TouchTarget::cancel(w, seat, data, seq),
            #[cfg(feature = "xwayland")]
            PointerFocusTarget::X11Surface(w) => TouchTarget::cancel(w, seat, data, seq),
            PointerFocusTarget::SSD(w) => TouchTarget::cancel(w, seat, data, seq),
        }
    }

    fn shape(
        &self,
        seat: &Seat<WyvernState<BackendData>>,
        data: &mut WyvernState<BackendData>,
        event: &smithay::input::touch::ShapeEvent,
        seq: Serial,
    ) {
        match self {
            PointerFocusTarget::WlSurface(w) => TouchTarget::shape(w, seat, data, event, seq),
            #[cfg(feature = "xwayland")]
            PointerFocusTarget::X11Surface(w) => TouchTarget::shape(w, seat, data, event, seq),
            PointerFocusTarget::SSD(w) => TouchTarget::shape(w, seat, data, event, seq),
        }
    }

    fn orientation(
        &self,
        seat: &Seat<WyvernState<BackendData>>,
        data: &mut WyvernState<BackendData>,
        event: &smithay::input::touch::OrientationEvent,
        seq: Serial,
    ) {
        match self {
            PointerFocusTarget::WlSurface(w) => TouchTarget::orientation(w, seat, data, event, seq),
            #[cfg(feature = "xwayland")]
            PointerFocusTarget::X11Surface(w) => {
                TouchTarget::orientation(w, seat, data, event, seq)
            }
            PointerFocusTarget::SSD(w) => TouchTarget::orientation(w, seat, data, event, seq),
        }
    }
}

impl WaylandFocus for PointerFocusTarget {
    #[inline]
    fn wl_surface(&self) -> Option<Cow<'_, WlSurface>> {
        match self {
            PointerFocusTarget::WlSurface(w) => w.wl_surface(),
            #[cfg(feature = "xwayland")]
            PointerFocusTarget::X11Surface(w) => w.wl_surface().map(Cow::Owned),
            PointerFocusTarget::SSD(_) => None,
        }
    }
    #[inline]
    fn same_client_as(&self, object_id: &ObjectId) -> bool {
        match self {
            PointerFocusTarget::WlSurface(w) => w.same_client_as(object_id),
            #[cfg(feature = "xwayland")]
            PointerFocusTarget::X11Surface(w) => w.same_client_as(object_id),
            PointerFocusTarget::SSD(w) => w
                .wl_surface()
                .map(|surface| surface.same_client_as(object_id))
                .unwrap_or(false),
        }
    }
}

impl WaylandFocus for KeyboardFocusTarget {
    #[inline]
    fn wl_surface(&self) -> Option<Cow<'_, WlSurface>> {
        match self {
            KeyboardFocusTarget::Window(w) => w.wl_surface(),
            KeyboardFocusTarget::LayerSurface(l) => Some(Cow::Borrowed(l.wl_surface())),
            KeyboardFocusTarget::Popup(p) => Some(Cow::Borrowed(p.wl_surface())),
        }
    }
}

impl From<WlSurface> for PointerFocusTarget {
    #[inline]
    fn from(value: WlSurface) -> Self {
        PointerFocusTarget::WlSurface(value)
    }
}

impl From<&WlSurface> for PointerFocusTarget {
    #[inline]
    fn from(value: &WlSurface) -> Self {
        PointerFocusTarget::from(value.clone())
    }
}

impl From<PopupKind> for PointerFocusTarget {
    #[inline]
    fn from(value: PopupKind) -> Self {
        PointerFocusTarget::from(value.wl_surface())
    }
}

#[cfg(feature = "xwayland")]
impl From<X11Surface> for PointerFocusTarget {
    #[inline]
    fn from(value: X11Surface) -> Self {
        PointerFocusTarget::X11Surface(value)
    }
}

#[cfg(feature = "xwayland")]
impl From<&X11Surface> for PointerFocusTarget {
    #[inline]
    fn from(value: &X11Surface) -> Self {
        PointerFocusTarget::from(value.clone())
    }
}

impl From<WindowElement> for KeyboardFocusTarget {
    #[inline]
    fn from(w: WindowElement) -> Self {
        KeyboardFocusTarget::Window(w.0.clone())
    }
}

impl From<LayerSurface> for KeyboardFocusTarget {
    #[inline]
    fn from(l: LayerSurface) -> Self {
        KeyboardFocusTarget::LayerSurface(l)
    }
}

impl From<PopupKind> for KeyboardFocusTarget {
    #[inline]
    fn from(p: PopupKind) -> Self {
        KeyboardFocusTarget::Popup(p)
    }
}

impl From<KeyboardFocusTarget> for PointerFocusTarget {
    #[inline]
    fn from(value: KeyboardFocusTarget) -> Self {
        match value {
            KeyboardFocusTarget::Window(w) => match w.underlying_surface() {
                WindowSurface::Wayland(w) => PointerFocusTarget::from(w.wl_surface()),
                #[cfg(feature = "xwayland")]
                WindowSurface::X11(s) => PointerFocusTarget::from(s),
            },
            KeyboardFocusTarget::LayerSurface(surface) => {
                PointerFocusTarget::from(surface.wl_surface())
            }
            KeyboardFocusTarget::Popup(popup) => PointerFocusTarget::from(popup.wl_surface()),
        }
    }
}

/// Focus stack for tracking window Z-order and enabling Alt+Tab cycling.
///
/// Maintains an ordered list of windows from least to most recent:
/// `[oldest, ..., previous, current_focus]`
///
/// When a window is created, it's pushed to the top.
/// When a window is destroyed, it's removed from the stack.
/// When Alt+Tab is pressed, cycling moves backward through the stack (oldest direction).
///
/// # Example
///
/// ```ignore
/// let mut stack = FocusStack::new();
/// stack.push(window1.clone());
/// stack.push(window2.clone());
/// stack.push(window3.clone());
///
/// // Currently focused on window3
/// assert_eq!(stack.current(), Some(&window3));
///
/// // Alt+Tab cycles backward to window2
/// stack.cycle_backward();
/// assert_eq!(stack.current(), Some(&window2));
/// ```
#[derive(Debug, Clone)]
pub struct FocusStack {
    /// Windows in focus order: [oldest, ..., most_recent]
    windows: Vec<WindowElement>,
    /// Index of currently focused window in `windows` vec
    /// invariant: current_index < windows.len() or windows is empty
    current_index: Option<usize>,
}

impl FocusStack {
    /// Create an empty focus stack.
    pub fn new() -> Self {
        FocusStack {
            windows: Vec::new(),
            current_index: None,
        }
    }

    /// Push a window to the top of the stack.
    ///
    /// If the window already exists in the stack, it's moved to the top.
    /// Automatically cleans up dead windows before pushing.
    pub fn push(&mut self, window: WindowElement) {
        // Clean up dead windows
        self.cleanup();

        // Remove if already present
        if let Some(pos) = self.windows.iter().position(|w| w == &window) {
            self.windows.remove(pos);
        }

        // Push to top
        self.windows.push(window);
        self.current_index = Some(self.windows.len() - 1);
    }

    /// Get the currently focused window (top of stack).
    pub fn current(&self) -> Option<&WindowElement> {
        self.current_index.and_then(|idx| self.windows.get(idx))
    }

    /// Remove a specific window from the stack.
    ///
    /// If the removed window was focused, focus automatically moves to the next
    /// most recent window in the stack.
    pub fn remove(&mut self, window: &WindowElement) {
        if let Some(pos) = self.windows.iter().position(|w| w == window) {
            self.windows.remove(pos);

            // Adjust current_index after removal
            match self.current_index {
                None => {}
                Some(idx) if idx == pos => {
                    // Removed window was focused
                    // Set focus to the most recent remaining window
                    if !self.windows.is_empty() {
                        self.current_index = Some(self.windows.len() - 1);
                    } else {
                        self.current_index = None;
                    }
                }
                Some(idx) if idx > pos => {
                    // Removed window was before focused window, adjust index
                    self.current_index = Some(idx - 1);
                }
                _ => {
                    // Removed window was after focused window, index unchanged
                }
            }
        }
    }

    /// Cycle focus to the next window (Alt+Shift+Tab behavior).
    ///
    /// Moves focus forward through the stack (toward most recent).
    /// Wraps around from oldest to most recent.
    pub fn cycle_forward(&mut self) {
        // Clean up dead windows first
        self.cleanup();

        if self.windows.is_empty() {
            return;
        }

        match self.current_index {
            None => {
                // No current focus, focus the most recent
                self.current_index = Some(self.windows.len() - 1);
            }
            Some(idx) => {
                // Move to next (older) window
                if idx == 0 {
                    // Wrap to most recent
                    self.current_index = Some(self.windows.len() - 1);
                } else {
                    self.current_index = Some(idx - 1);
                }
            }
        }
    }

    /// Cycle focus to the previous window (Alt+Tab behavior).
    ///
    /// Moves focus backward through the stack (toward least recent).
    /// Wraps around from most recent to oldest.
    pub fn cycle_backward(&mut self) {
        // Clean up dead windows first
        self.cleanup();

        if self.windows.is_empty() {
            return;
        }

        match self.current_index {
            None => {
                // No current focus, focus the most recent
                self.current_index = Some(self.windows.len() - 1);
            }
            Some(idx) => {
                // Move to previous (more recent) window
                if idx == self.windows.len() - 1 {
                    // Wrap to oldest
                    self.current_index = Some(0);
                } else {
                    self.current_index = Some(idx + 1);
                }
            }
        }
    }

    /// Set focus to a specific window without cycling.
    ///
    /// If the window is not in the stack, does nothing.
    pub fn set_focus(&mut self, window: WindowElement) {
        if let Some(idx) = self.windows.iter().position(|w| w == &window) {
            self.current_index = Some(idx);
        }
    }

    /// Get all windows in focus order (oldest to most recent).
    pub fn windows(&self) -> &[WindowElement] {
        &self.windows
    }

    /// Get the count of windows in the stack.
    pub fn len(&self) -> usize {
        self.windows.len()
    }

    /// Check if the stack is empty.
    pub fn is_empty(&self) -> bool {
        self.windows.is_empty()
    }

    /// Remove all dead windows from the stack.
    ///
    /// Called automatically by most operations, but can be called explicitly
    /// to ensure consistency after windows have been closed.
    pub fn cleanup(&mut self) {
        // Remove dead windows
        self.windows.retain(|w| w.alive());

        // Ensure current_index is still valid
        if let Some(idx) = self.current_index {
            if idx >= self.windows.len() {
                // Current index is now out of bounds, reset to last window
                if !self.windows.is_empty() {
                    self.current_index = Some(self.windows.len() - 1);
                } else {
                    self.current_index = None;
                }
            }
        }
    }
}

impl Default for FocusStack {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_focus_stack_new() {
        let stack = FocusStack::new();
        assert!(stack.is_empty());
        assert_eq!(stack.len(), 0);
        assert_eq!(stack.current(), None);
    }

    #[test]
    fn test_focus_stack_default() {
        let stack = FocusStack::default();
        assert!(stack.is_empty());
        assert_eq!(stack.len(), 0);
    }

    #[test]
    fn test_cycle_backward_empty() {
        let mut stack = FocusStack::new();
        // Should not panic on empty stack
        stack.cycle_backward();
        assert!(stack.is_empty());
    }

    #[test]
    fn test_cycle_forward_empty() {
        let mut stack = FocusStack::new();
        // Should not panic on empty stack
        stack.cycle_forward();
        assert!(stack.is_empty());
    }

    #[test]
    fn test_focus_stack_new_is_empty() {
        let stack = FocusStack::new();
        assert_eq!(stack.len(), 0);
        assert!(stack.is_empty());
    }

    #[test]
    fn test_focus_stack_cleanup_idempotent() {
        let mut stack = FocusStack::new();
        stack.cleanup();
        stack.cleanup(); // Should not panic
        assert!(stack.is_empty());
    }

    #[test]
    fn test_focus_stack_is_clone() {
        let stack1 = FocusStack::new();
        let stack2 = stack1.clone();
        assert_eq!(stack1.len(), stack2.len());
        assert!(stack2.is_empty());
    }
}
