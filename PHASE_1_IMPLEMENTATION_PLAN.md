# Phase 1 Implementation Plan: Core Compositor Features (v0.3.0)

**Status**: Phase 1.1 COMPLETE ✅ | Phase 1.2.1 COMPLETE ✅ | Phase 1.2.2-1.5 PENDING
**Timeline**: 4-6 weeks total (2 weeks elapsed)
**Goal**: Implement fundamental window management and input handling
**Last Updated**: 2026-01-02
**Phase 1.1 Commits**: 034c97e (FocusStack + lifecycle), 7fa9f6a (Alt+Tab)
**Phase 1.2.1 Commit**: 1f8805c (KeyRepeatState + tests)

---

## Phase 1 Overview

This phase implements the core compositor features that users interact with daily:
- Focus management (keyboard + pointer focus, Alt+Tab cycling)
- Enhanced keyboard input (repeat, IME integration points)
- Enhanced pointer input (motion, buttons, constraints)
- Basic window tiling (master-stack layout with configurable ratio)
- Window resize/move refinement (size hints, visual feedback)

**Success Criteria**:
- Focus cycling works reliably (Alt+Tab between windows)
- Keyboard input is stable (keys don't get "stuck", repeat works)
- Pointer input is responsive (no jumps, buttons work correctly)
- Tiling automatically arranges windows
- Windows can be resized with visual feedback

---

## Phase 1.1: Focus Management System

**Why**: Windows need to know which has keyboard/pointer focus. Users expect Alt+Tab to switch between windows.

### Current State (Phase 0)

**Existing in `src/focus.rs`**:
- `KeyboardFocusTarget` enum (Window, LayerSurface, Popup)
- `PointerFocusTarget` enum (WlSurface, X11Surface, SSD)
- Full trait implementations for focus event routing

**Existing in `src/state.rs`**:
- `seat: Seat<WyvernState>` (Smithay's focus tracking)
- `pointer: PointerHandle<WyvernState>` (pointer position tracking)
- `focus_changed(&mut self, seat: &Seat, target: Option<&KeyboardFocusTarget>)` (notification method)

**Existing in `src/input_handler.rs`**:
- Keyboard event delegation to focused window
- Pointer event delegation to focused surface

### What Needs to be Built

#### 1.1.1 Focus Stack (Window Z-Order for Alt+Tab)

**File**: `src/focus.rs` (enhance)

```rust
/// Focus stack for Alt+Tab cycling.
/// Ordered from least to most recent: [oldest, ..., current, most_recent]
/// Example: [xterm, firefox, vscode] means vscode is focused
pub struct FocusStack {
    windows: Vec<WindowElement>,
    current_index: usize, // Index into windows vec
}

impl FocusStack {
    /// Create an empty focus stack
    pub fn new() -> Self;

    /// Push window to top of stack (or move to top if already present)
    pub fn push(&mut self, window: WindowElement);

    /// Remove window from stack (e.g., when closed)
    pub fn remove(&self, window: &WindowElement);

    /// Get currently focused window (last element)
    pub fn current(&self) -> Option<&WindowElement>;

    /// Cycle focus to next window (Alt+Tab behavior)
    /// Returns the new focused window
    pub fn cycle_forward(&mut self) -> Option<WindowElement>;

    /// Cycle focus to previous window (Alt+Shift+Tab behavior)
    pub fn cycle_backward(&mut self) -> Option<WindowElement>;

    /// Set focus to specific window without cycling
    pub fn set_focus(&mut self, window: WindowElement);

    /// Get all windows in stack order (for debugging/testing)
    pub fn windows(&self) -> &[WindowElement];
}
```

**Integration Point**: Add to `WyvernState`:
```rust
pub struct WyvernState<BackendData> {
    // ... existing fields ...
    pub focus_stack: FocusStack,
}
```

**Tests Needed**:
- Push/remove maintains correct order
- Cycle forward/backward work in circular manner
- Current always returns most recent window
- Removing current window updates correctly

#### 1.1.2 Focus Change Implementation

**File**: `src/shell/mod.rs` (modify window creation/destruction)

When a window is created:
```rust
pub fn add_window(&mut self, space: &mut Space<WindowElement>, window: WindowElement) {
    // ... existing window setup code ...
    self.wyvern_state.focus_stack.push(window.clone());
    self.set_keyboard_focus(seat, window);
}
```

When a window is destroyed:
```rust
pub fn remove_window(&mut self, window: &WindowElement) {
    // ... existing cleanup code ...
    self.wyvern_state.focus_stack.remove(window);

    // If this was the focused window, set focus to next in stack
    if let Some(next_window) = self.wyvern_state.focus_stack.current() {
        self.set_keyboard_focus(seat, next_window.into());
    }
}
```

#### 1.1.3 Alt+Tab Cycling Handler

**File**: `src/input_handler.rs` (add key binding handler)

```rust
/// Keyboard shortcut handler for focus cycling
pub fn handle_key_binding(
    state: &mut WyvernState<BackendData>,
    keysym: Keysym,
    modifiers: ModifiersState,
) -> bool {
    // Super+Tab = Alt+Tab simulation (since Alt might be reserved)
    if keysym == keysym::XKB_KEY_Tab && modifiers.alt {
        if modifiers.shift {
            state.focus_stack.cycle_backward();
        } else {
            state.focus_stack.cycle_forward();
        }
        // Update seat focus to new window
        if let Some(window) = state.focus_stack.current() {
            state.seat.keyboard.set_focus(
                state.display_handle,
                Some(KeyboardFocusTarget::Window(window.0.clone())),
                SERIAL_COUNTER.next_serial(),
            );
        }
        return true; // Key was handled
    }
    false // Key not handled
}
```

**Testing Strategy**:
```rust
#[test]
fn test_focus_cycling() {
    let mut state = create_test_state();

    // Create 3 windows
    let win1 = create_test_window();
    let win2 = create_test_window();
    let win3 = create_test_window();

    // Add to focus stack
    state.focus_stack.push(win1.clone());
    state.focus_stack.push(win2.clone());
    state.focus_stack.push(win3.clone());

    // Should be focused on win3
    assert_eq!(state.focus_stack.current(), Some(&win3));

    // Cycle backward should go to win2
    state.focus_stack.cycle_backward();
    assert_eq!(state.focus_stack.current(), Some(&win2));

    // Cycle backward again should go to win1
    state.focus_stack.cycle_backward();
    assert_eq!(state.focus_stack.current(), Some(&win1));

    // Cycle backward again should wrap to win3
    state.focus_stack.cycle_backward();
    assert_eq!(state.focus_stack.current(), Some(&win3));
}
```

---

## Phase 1.2: Keyboard Input Handler Enhancements

**Why**: Users need reliable keyboard input with proper repeat when keys are held.

### Current State

**Existing in `src/input_handler.rs`**:
- `KeyboardState { focus: Option<KeyboardFocusTarget>, ... }`
- Keyboard event delegation to focused window
- Keysym filtering (suppressed_keys)

### What Needs to be Built

#### 1.2.1 Key Repeat Handling - COMPLETE ✅

**Commit**: 1f8805c

**File**: `src/input_handler.rs` (lines 1538-1757)

**Implementation**:
```rust
pub struct KeyRepeatState {
    /// Map of keycode -> (press_time, last_repeat_time)
    held_keys: HashMap<u32, (Instant, Option<Instant>)>,
    /// Delay in ms before repeat starts (default: 600)
    repeat_delay: u32,
    /// Time in ms between repeats (default: 40ms = 25 repeats/sec)
    repeat_interval: u32,
}

impl KeyRepeatState {
    pub fn new() -> Self;
    pub fn with_timing(delay_ms: u32, interval_ms: u32) -> Self;
    pub fn on_key_pressed(&mut self, keycode: u32) -> bool;
    pub fn on_key_released(&mut self, keycode: u32) -> bool;
    pub fn get_keys_to_repeat(&mut self) -> Vec<u32>;
    pub fn has_held_keys(&self) -> bool;
    pub fn held_key_count(&self) -> usize;
    pub fn clear(&mut self);
}
```

**Integration**: Added to `WyvernState` (src/state.rs:213)
```rust
pub struct WyvernState<BackendData> {
    // ... existing fields ...
    pub key_repeat_state: input_handler::KeyRepeatState,
}
```

Initialization in WyvernState creation (src/state.rs:898):
```rust
key_repeat_state: input_handler::KeyRepeatState::new(),
```

**Testing**: 9 comprehensive unit tests (all passing)
- `test_key_repeat_state_new` - Default initialization
- `test_key_repeat_state_default` - Default trait impl
- `test_key_pressed_first_key` - Single key tracking
- `test_key_pressed_multiple_keys` - Multiple simultaneous keys
- `test_key_released` - Key release with remaining keys
- `test_repeat_initial_delay` - Initial delay timing validation
- `test_repeat_interval` - Repeat interval timing validation
- `test_clear` - State cleanup
- `test_clone` - Clone implementation

**Quality Metrics**:
- ✓ 24/24 tests passing (15 existing + 9 new)
- ✓ 0 compiler warnings
- ✓ Code formatting compliant
- ✓ Build time: < 10s

**Architecture Notes**:
- Uses `std::time::Instant` for platform-independent timing
- Decoupled from event loop (no direct Smithay dependencies)
- Ready for Phase 1.2.2 integration with event loop timer system
- Supports multiple simultaneous held keys (e.g., Shift+A)

#### 1.2.2 IME Integration Points

**File**: `src/input_handler.rs` (add IME support structure)

```rust
/// Input Method Editor integration
/// Currently just defines the structure for future IME support
pub struct IMEState {
    /// Active input method context
    context: Option<InputMethodContext>,
    /// Preedit text being composed
    preedit: String,
}

impl IMEState {
    pub fn new() -> Self;

    /// Handle key event - return true if IME handled it
    pub fn handle_key(&mut self, keysym: Keysym, state: KeyState) -> bool;

    /// Get preedit text for rendering
    pub fn preedit_text(&self) -> &str;

    /// Commit the current preedit to actual text
    pub fn commit(&mut self) -> String;
}
```

**Note**: Full IME support deferred to Phase 3. Phase 1 establishes the integration points.

#### 1.2.3 Special Key Handling

**File**: `src/input_handler.rs` (enhance key binding handler)

```rust
pub fn handle_key_binding(
    state: &mut WyvernState<BackendData>,
    keysym: Keysym,
    modifiers: ModifiersState,
) -> bool {
    match (keysym, modifiers) {
        // Super+Return = Open terminal
        (keysym::XKB_KEY_Return, modifiers) if modifiers.logo => {
            spawn_terminal(&state.config);
            true
        }
        // Super+Q = Quit
        (keysym::XKB_KEY_q, modifiers) if modifiers.logo => {
            state.running.store(false, Ordering::SeqCst);
            true
        }
        // Alt+Tab = Focus cycling
        (keysym::XKB_KEY_Tab, modifiers) if modifiers.alt => {
            if modifiers.shift {
                state.focus_stack.cycle_backward();
            } else {
                state.focus_stack.cycle_forward();
            }
            true
        }
        _ => false,
    }
}
```

---

## Phase 1.3: Pointer Input Handler Enhancements

**Why**: Mouse/trackpad interaction must be smooth and responsive.

### What Needs to be Built

#### 1.3.1 Cursor Motion Tracking

**File**: `src/input_handler.rs` (enhance pointer state)

```rust
pub struct PointerState {
    /// Current cursor location in logical coordinates
    location: Point<f64, Logical>,

    /// Which surface/element has pointer focus
    focus: Option<PointerFocusTarget>,

    /// Previous location (for motion events)
    previous_location: Point<f64, Logical>,

    /// Whether pointer is currently pressed
    buttons: BitFlags<PointerButton>,
}

impl PointerState {
    pub fn update_location(&mut self, new_location: Point<f64, Logical>);
    pub fn current_location(&self) -> Point<f64, Logical>;
    pub fn is_button_pressed(&self, button: PointerButton) -> bool;
}
```

#### 1.3.2 Double-Click Detection

```rust
pub struct DoubleClickDetector {
    last_click: Option<(PointerButton, Instant)>,
    threshold_ms: u32, // typically 300ms
}

impl DoubleClickDetector {
    pub fn handle_click(&mut self, button: PointerButton, time: Instant) -> ClickType;
}

pub enum ClickType {
    Single,
    Double,
}
```

#### 1.3.3 Pointer Constraint Support (Fullscreen Games)

```rust
/// Tracks whether pointer should be confined to a region
pub struct PointerConstraint {
    /// Region to confine pointer to (None = no constraint)
    region: Option<Rectangle<i32, Logical>>,

    /// Whether cursor should be hidden when constrained
    hide_cursor: bool,
}

impl PointerConstraint {
    pub fn confine_to_region(&mut self, region: Rectangle<i32, Logical>);
    pub fn release(&mut self);
    pub fn clamp_position(&self, pos: Point<f64, Logical>) -> Point<f64, Logical>;
}
```

**Testing**:
```rust
#[test]
fn test_pointer_constraint() {
    let region = Rectangle::from_loc_and_size((100, 100), (300, 300));
    let mut constraint = PointerConstraint::new();
    constraint.confine_to_region(region.clone());

    // Position outside region should be clamped
    let pos = Point::from((400.0, 400.0));
    let clamped = constraint.clamp_position(pos);
    assert!(region.contains(clamped.to_i32()));
}
```

---

## Phase 1.4: Basic Window Tiling

**Why**: Modern compositor users expect organized window layouts.

### Architecture

#### 1.4.1 Tiling Layout Algorithm

**File**: `src/shell/layout.rs` (new)

```rust
/// Tiling layout modes
pub enum LayoutMode {
    /// Master-stack: Master window (50%+) on left, others stacked on right
    MasterStack { master_ratio: f32 },

    /// Monocle: Single window fullscreen
    Monocle,

    /// Floating: Manual window placement (no automatic tiling)
    Floating,
}

/// Master-stack layout algorithm
pub struct MasterStackLayout {
    master_ratio: f32,
    gap_size: i32,
}

impl MasterStackLayout {
    pub fn arrange(
        &self,
        windows: &[WindowElement],
        output_geo: Rectangle<i32, Logical>,
    ) -> Vec<(WindowElement, Rectangle<i32, Logical>)> {
        // Algorithm:
        // 1. If no windows, return empty
        // 2. If 1 window, fullscreen (minus gaps)
        // 3. If 2+ windows:
        //    - Master area: left side, master_ratio fraction of width
        //    - Stack area: right side, (1 - master_ratio) fraction of width
        //    - Divide stack area equally among remaining windows
        //    - Apply gap_size between all tiles

        // Example with 3 windows, master_ratio=0.55:
        // ┌─────────────────────────┐
        // │       Master            │ Stack 1
        // │      (55% width)        ├─────────────┐
        // │                         │             │
        // ├─────────────────────────┤ Stack 2     │
        // │       Master            ├─────────────┤
        // │                         │             │
        // └─────────────────────────┘─────────────┘
    }
}

impl MasterStackLayout {
    pub fn new(master_ratio: f32, gap_size: i32) -> Self;
}
```

**Detailed Implementation**:

```rust
impl MasterStackLayout {
    pub fn arrange(
        &self,
        windows: &[WindowElement],
        output_geo: Rectangle<i32, Logical>,
    ) -> Vec<(WindowElement, Rectangle<i32, Logical>)> {
        if windows.is_empty() {
            return vec![];
        }

        let gap = self.gap_size as f64;
        let output_width = (output_geo.size.w as f64 - gap) / (output_geo.size.w as f64);
        let output_height = (output_geo.size.h as f64 - gap) / (output_geo.size.h as f64);

        if windows.len() == 1 {
            // Single window: fullscreen with gaps
            let width = output_geo.size.w - 2 * self.gap_size;
            let height = output_geo.size.h - 2 * self.gap_size;
            let geo = Rectangle::from_loc_and_size(
                (output_geo.loc.x + self.gap_size, output_geo.loc.y + self.gap_size),
                (width, height),
            );
            return vec![(windows[0].clone(), geo)];
        }

        let mut result = vec![];

        // Master window takes left side
        let master_width = ((output_geo.size.w - self.gap_size) as f64 * self.master_ratio) as i32;
        let master_geo = Rectangle::from_loc_and_size(
            (output_geo.loc.x + self.gap_size, output_geo.loc.y + self.gap_size),
            (master_width - self.gap_size, output_geo.size.h - 2 * self.gap_size),
        );
        result.push((windows[0].clone(), master_geo));

        // Stack windows on right
        let stack_x = output_geo.loc.x + master_width + self.gap_size;
        let stack_width = output_geo.size.w - master_width - 2 * self.gap_size;
        let stack_height = (output_geo.size.h - 2 * self.gap_size) / (windows.len() - 1) as i32;

        for (i, window) in windows.iter().enumerate().skip(1) {
            let stack_y = output_geo.loc.y + self.gap_size
                + (i - 1) as i32 * (stack_height + self.gap_size);
            let geo = Rectangle::from_loc_and_size((stack_x, stack_y), (stack_width, stack_height));
            result.push((window.clone(), geo));
        }

        result
    }
}
```

**Testing**:
```rust
#[test]
fn test_master_stack_layout() {
    let layout = MasterStackLayout::new(0.55, 10);
    let windows = vec![window1, window2, window3];
    let output_geo = Rectangle::from_loc_and_size((0, 0), (1920, 1080));

    let result = layout.arrange(&windows, output_geo);

    assert_eq!(result.len(), 3);

    // Master should be on left (55% of width)
    let (master_win, master_geo) = &result[0];
    assert_eq!(master_geo.loc.x, 10); // gap
    assert_eq!(master_geo.size.w, (1920 - 10) * 55 / 100); // ~1045

    // Stack windows should divide right side
    let (stack1_win, stack1_geo) = &result[1];
    assert_eq!(stack1_geo.loc.x, master_geo.loc.x + master_geo.size.w + 10);
    assert!(stack1_geo.size.h > 0);
    assert!(stack1_geo.size.h < output_geo.size.h / 2);
}
```

#### 1.4.2 Tiling Integration into State

**File**: `src/state.rs` (enhance TilingState)

Current (Phase 0):
```rust
#[derive(Debug, Default)]
pub struct TilingState {
    pub tiled_windows: Vec<WindowElement>,
    pub master_ratio: f32,
    pub gap_size: i32,
}
```

Enhance for Phase 1:
```rust
#[derive(Debug)]
pub struct TilingState {
    pub tiled_windows: Vec<WindowElement>,
    pub master_ratio: f32,
    pub gap_size: i32,
    pub layout_mode: LayoutMode,
    pub floating_windows: HashSet<WindowId>, // Windows in floating mode
    layout: MasterStackLayout,
}

impl TilingState {
    /// Apply tiling layout to all tiled windows
    /// Should be called:
    /// - When a new window is added
    /// - When a window is removed
    /// - When output size changes
    /// - When master_ratio is changed
    pub fn apply_layout(&self, space: &mut Space<WindowElement>, output_geo: Rectangle<i32, Logical>);

    /// Mark a window as floating (exempt from tiling)
    pub fn set_floating(&mut self, window: &WindowElement, floating: bool);

    /// Adjust master ratio and re-layout
    pub fn set_master_ratio(&mut self, ratio: f32);

    /// Adjust gap size and re-layout
    pub fn set_gap_size(&mut self, size: i32);
}
```

**Applying Layout in Event Loop**:

```rust
// In main event loop, after window changes:
if space_dirty {
    let output_geo = output.geometry();
    state.tiling_state.apply_layout(&mut state.space, output_geo);
    space_dirty = false;
}
```

#### 1.4.3 Monocle Layout (Fullscreen Mode)

```rust
pub struct MonocleLayout;

impl MonocleLayout {
    pub fn arrange(
        &self,
        windows: &[WindowElement],
        output_geo: Rectangle<i32, Logical>,
    ) -> Vec<(WindowElement, Rectangle<i32, Logical>)> {
        if windows.is_empty() {
            return vec![];
        }

        // Only the first window is visible, fullscreen
        let focused = &windows[0];
        let geo = output_geo;

        vec![(focused.clone(), geo)]
    }
}
```

#### 1.4.4 Per-Window Floating Mode

```rust
pub fn toggle_floating(state: &mut WyvernState, window: &WindowElement) {
    if state.tiling_state.floating_windows.contains(&window.id()) {
        state.tiling_state.floating_windows.remove(&window.id());
    } else {
        state.tiling_state.floating_windows.insert(window.id());
    }

    // Re-apply layout
    let output_geo = state.get_output_geometry();
    state.tiling_state.apply_layout(&mut state.space, output_geo);
}
```

---

## Phase 1.5: Window Resize/Move Operations (Refinement)

**Status**: `src/shell/grabs.rs` exists, needs enhancement

### What to Enhance

#### 1.5.1 Size Hints Respect

**File**: `src/shell/grabs.rs`

When resizing a window, respect client-provided hints:
```rust
pub fn apply_resize_constraints(
    &self,
    new_size: Size<i32, Logical>,
    window: &WindowElement,
) -> Size<i32, Logical> {
    let hints = window.0.surface_size_limits(); // Get from xdg_toplevel

    Size {
        w: new_size.w.max(hints.min.w).min(hints.max.w),
        h: new_size.h.max(hints.min.h).min(hints.max.h),
    }
}
```

#### 1.5.2 Visual Resize Feedback

During active resize grab, draw a semi-transparent rectangle showing final size:
```rust
pub fn render_resize_feedback(
    renderer: &mut R,
    resize_geo: Rectangle<i32, Physical>,
    location: Point<i32, Physical>,
) {
    // Draw semi-transparent rectangle at new size
    // Updates on each mouse motion
}
```

#### 1.5.3 Keyboard-Based Resize

Support Alt+arrow keys to resize without mouse:
```rust
if keysym == keysym::XKB_KEY_Left && modifiers.alt {
    if state.is_resizing {
        state.current_resize_size.w -= 20;
    }
}
```

---

## Implementation Sequence

**Recommended order** to build incrementally and test as you go:

1. ✅ Phase 1.1.1: FocusStack data structure + unit tests
2. ✅ Phase 1.1.2: Focus change on window create/destroy
3. ✅ Phase 1.1.3: Alt+Tab cycling handler + integration tests
4. ✅ Phase 1.2.1: Key repeat state + tests
5. ✅ Phase 1.2.2: IME integration points (structure only)
6. ✅ Phase 1.2.3: Special key binding handler
7. ✅ Phase 1.3.1: Pointer motion tracking
8. ✅ Phase 1.3.2: Double-click detection
9. ✅ Phase 1.3.3: Pointer constraint support
10. ✅ Phase 1.4.1: Master-stack layout algorithm + tests
11. ✅ Phase 1.4.2: Tiling integration into WyvernState
12. ✅ Phase 1.4.3: Monocle layout + floating mode
13. ✅ Phase 1.5.1-5.3: Resize/move refinement

---

## Quality Gates for Phase 1 Completion

- ✅ All 5 subsystems functional (focus, keyboard, pointer, tiling, resize)
- ✅ Comprehensive unit tests (target 80%+ coverage)
- ✅ Integration tests for focus cycling, tiling geometry
- ✅ No new panic! calls introduced
- ✅ Clippy: 0 warnings
- ✅ Cargo fmt: 100% compliant
- ✅ Documentation: All new code documented
- ✅ Manual testing: Windows tile correctly, focus cycles, keyboard/mouse work

---

## Git Workflow for Phase 1

Suggested commit structure:
```
feat: focus management system (FocusStack + Alt+Tab)
feat: keyboard repeat handling
feat: key binding handlers (Super+Return, Super+Q, etc.)
feat: pointer input enhancements (motion, double-click, constraint)
feat: master-stack tiling layout
feat: monocle layout and floating windows
feat: window resize/move refinement
feat: Phase 1 integration tests (80%+ coverage)
```

Each commit should be independently testable.

---

## Success Metrics (v0.3.0 Release)

| Metric | Target |
|--------|--------|
| Windows auto-tiling | Yes |
| Alt+Tab focusing | Works reliably |
| Keyboard repeat | Smooth, no stuck keys |
| Mouse interaction | Responsive |
| Test coverage | ≥80% |
| Code warnings | 0 |
| Documentation | Complete |

---

**Next Action**: Begin Phase 1.1.1 (FocusStack implementation)
