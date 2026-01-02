# Wyvern Implementation Roadmap: Complete Phase 1.2-5 Plans

**Document Purpose**: Exhaustive implementation guide for Phase 1.2 through Phase 5
**Target Version**: v1.0.0 (Phase 5 complete)
**Last Updated**: 2026-01-02
**Status**: Phase 1.1 COMPLETE, Detailed plans for 1.2-5 below

---

## Table of Contents

1. [Phase 1.2: Keyboard Input Enhancements](#phase-12-keyboard-input-enhancements)
2. [Phase 1.3: Pointer Input Enhancements](#phase-13-pointer-input-enhancements)
3. [Phase 1.4: Basic Window Tiling](#phase-14-basic-window-tiling)
4. [Phase 1.5: Window Resize/Move Refinement](#phase-15-window-resizemove-refinement)
5. [Phase 2: Advanced Rendering](#phase-2-advanced-rendering)
6. [Phase 3: Protocol & Interoperability](#phase-3-protocol--interoperability)
7. [Phase 4: Advanced Features & Optimization](#phase-4-advanced-features--optimization)
8. [Phase 5: Production Deployment & Polish](#phase-5-production-deployment--polish)

---

## Phase 1.2: Keyboard Input Enhancements

**Target Release**: v0.3.0 (with Phase 1.1)
**Timeline**: 1-2 weeks
**Status**: PARTIAL (1.2.1 COMPLETE ✅)

### Goals

- Keyboard repeat handling (hold key, auto-repeat after delay)
- IME (Input Method Editor) integration points
- Special key handling (Super key combinations)
- Keyboard layout switching support
- Reliable key event routing

### 1.2.1: Keyboard Repeat Handling - COMPLETE ✅

**Commit**: 1f8805c

**Why**: Users expect keys to repeat when held. Without this, holding 'a' types only one 'a'.

**Implementation** (Session 2):

**File**: `src/input_handler.rs` (lines 1538-1757)

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

**Integration** (WyvernState - Session 2):
- Added field: `pub key_repeat_state: input_handler::KeyRepeatState,` (src/state.rs:213)
- Initialized: `key_repeat_state: input_handler::KeyRepeatState::new(),` (src/state.rs:898)
- Ready for Phase 1.2.2 integration with event loop timer

**Testing** (Session 2 - 9 tests, 100% pass):
- ✓ test_key_repeat_state_new - Default initialization
- ✓ test_key_repeat_state_default - Default trait
- ✓ test_key_pressed_first_key - Single key tracking
- ✓ test_key_pressed_multiple_keys - Multiple simultaneous keys
- ✓ test_key_released - Key release with remaining keys
- ✓ test_repeat_initial_delay - Initial delay timing (with sleep)
- ✓ test_repeat_interval - Repeat interval timing (with sleep)
- ✓ test_clear - State cleanup
- ✓ test_clone - Clone trait implementation

**Phase 1.2.2 Integration** (Next):
1. Add `CustomEvent::KeyRepeat { keycode }` to event dispatcher
2. Register timer in event loop: `event_loop.handle().insert_source(Timer::..., ...)`
3. Periodic callback: calls `key_repeat_state.get_keys_to_repeat()`
4. For each returned keycode: send synthetic keyboard event to focused window

---

### 1.2.2: IME Integration Points

**Why**: Support for Input Method Editors (CJK languages, special characters).

**Implementation**:

**File**: `src/input_handler.rs` + `src/input_method.rs` (new)

The Wayland text-input protocol defines IME interaction:

```rust
// Skeleton for IME integration
pub struct InputMethodState {
    /// Currently active IME context (if any)
    active_context: Option<InputMethodContext>,
    /// Preedit string (composition in progress)
    preedit: String,
    /// Cursor position in preedit
    preedit_cursor: usize,
}

impl InputMethodState {
    /// Called when text input is activated (window gets focus)
    pub fn activate(&mut self, surface: &WlSurface) {
        // Request IME context for this surface
    }

    /// Handle preedit update from IME
    pub fn on_preedit(&mut self, text: String, cursor_pos: usize) {
        self.preedit = text;
        self.preedit_cursor = cursor_pos;
        // Notify focused surface of preedit
    }

    /// Handle commit from IME
    pub fn on_commit(&mut self, text: String) {
        // Send committed text to focused surface
        // Clear preedit
        self.preedit.clear();
    }
}
```

**Integration Points**:
1. Initialize IME seat in `WyvernState::new()`
2. Activate IME on focus change
3. Route IME events to focused window
4. Render preedit text (if needed for visual feedback)

**Testing**:
- IME activation on window focus
- Preedit rendering (composition display)
- Commit handling (final text insertion)
- Multiple IMEs (switching between input methods)

---

### 1.2.3: Special Key Handling

**Why**: Super key (Windows key) combos and special modifiers.

**Implementation**:

Extend `process_keyboard_shortcut()` in `src/input_handler.rs`:

```rust
fn process_keyboard_shortcut(modifiers: ModifiersState, keysym: Keysym) -> Option<KeyAction> {
    // Existing Alt+Tab handling...

    // Super key combinations (already partially implemented)
    if modifiers.logo && (xkb::KEY_1..=xkb::KEY_9).contains(&raw) {
        return Some(KeyAction::Screen((raw - xkb::KEY_1) as usize));
    }

    // Super+Return opens terminal (already implemented)
    // Super+Shift+X combinations for advanced operations

    if modifiers.logo && modifiers.shift {
        match keysym {
            Keysym::M => Some(KeyAction::ScaleDown),
            Keysym::P => Some(KeyAction::ScaleUp),
            Keysym::W => Some(KeyAction::TogglePreview),
            Keysym::D => Some(KeyAction::ToggleDecorations),
            Keysym::T => Some(KeyAction::ToggleTint),
            Keysym::R => Some(KeyAction::RotateOutput),
            Keysym::Return => Some(KeyAction::Run(cfg.terminal)),
            // NEW: Phase 1.2 additions:
            Keysym::C => Some(KeyAction::CycleTilingLayout),  // Toggle master-stack/monocle
            Keysym::H => Some(KeyAction::DecreaseMasterRatio),  // Resize master area
            Keysym::L => Some(KeyAction::IncreaseMasterRatio),  // Resize master area
            _ => None,
        }
    }

    None
}
```

**New KeyActions**:
```rust
enum KeyAction {
    // ... existing variants ...
    CycleTilingLayout,          // Switch between layouts
    DecreaseMasterRatio,        // Make master window smaller
    IncreaseMasterRatio,        // Make master window larger
}
```

**Testing**:
- Super+Shift+C cycles through layouts
- Super+Shift+H/L adjust master window size
- Verify modifier combinations work correctly
- No conflicts with client shortcuts

---

### 1.2.4: Keyboard Layout Switching

**Why**: Support multiple keyboard layouts (QWERTY, DVORAK, Colemak, etc.).

**Implementation**:

**File**: `src/config.rs` + `src/input_handler.rs`

```rust
// In src/config.rs
#[derive(Debug, Deserialize, Serialize)]
pub struct KeyboardOptions {
    pub layout: String,      // "en", "fr", "de", "ja", etc.
    pub model: String,       // "pc105", "macbook", etc.
    pub variant: String,     // "dvorak", "colemak", etc.
    pub options: String,     // "grp:alt_shift_toggle", etc.
    pub rules: String,       // "evdev", etc.
}

// In WyvernState
pub struct KeyboardState {
    pub current_layout: String,
    pub available_layouts: Vec<String>,
}

impl WyvernState {
    pub fn switch_keyboard_layout(&mut self, layout: &str) -> Result<()> {
        // Notify Smithay keyboard handler
        let keyboard = self.seat.get_keyboard().unwrap();

        // Update XKB keymap with new layout
        keyboard.set_keymap(layout);

        self.keyboard_state.current_layout = layout.to_string();
        Ok(())
    }

    pub fn cycle_keyboard_layout(&mut self) {
        let current_idx = self.keyboard_state.available_layouts
            .iter()
            .position(|l| l == &self.keyboard_state.current_layout)
            .unwrap_or(0);

        let next_idx = (current_idx + 1) % self.keyboard_state.available_layouts.len();
        let next_layout = self.keyboard_state.available_layouts[next_idx].clone();
        let _ = self.switch_keyboard_layout(&next_layout);
    }
}
```

**Config Example**:
```toml
[keyboard]
layout = "en"
variant = "dvorak"
model = "pc105"
options = "grp:alt_shift_toggle,caps:escape"  # Toggle layout with Alt+Shift
rules = "evdev"
available_layouts = ["en", "fr", "de"]
```

**Testing**:
- Load different keyboard layouts
- Verify key mapping changes
- Alt+Shift toggles between layouts
- Super+Space cycles layouts

---

### 1.2.5: Key Event Routing Validation

**Why**: Ensure keys always reach the right window, with proper event sequencing.

**Implementation**:

In `keyboard_key_to_action()` (src/input_handler.rs):

```rust
fn keyboard_key_to_action<B: InputBackend>(&mut self, evt: B::KeyboardKeyEvent) -> KeyAction {
    let keycode = evt.key_code();
    let state = evt.state();

    // 1. Check layer shells (TopLevel/Overlay with KeyboardInteractivity::Exclusive)
    //    These should intercept keys before windows get them

    // 2. Check keyboard shortcuts inhibitor
    //    If active surface has inhibited shortcuts, don't process compositor shortcuts

    // 3. Route to focused window
    //    Keyboard::input() handles this automatically via Smithay

    // 4. Check for compositor shortcuts (Alt+Tab, etc.)
    //    Only if not inhibited

    // 5. Log key events for debugging
    debug!(?keycode, ?state, "key event routed to window");
}
```

**Testing**:
- Layer shell keys don't leak to windows
- Keyboard shortcut inhibitor works
- Alt+Tab doesn't interfere with Ctrl+Tab (browser tabs)
- Arrow keys work in text editors
- Global shortcuts and window shortcuts don't conflict

---

### 1.2.6: Testing Strategy for Phase 1.2

**Unit Tests**:
- KeyRepeatState state machine
- Layout switching logic
- Keysym to KeyAction mapping

**Integration Tests**:
- Key repeat timing accuracy
- Multiple keyboards connected
- Layout switching during typing
- IME activation on focus change

**Manual Testing Scenarios**:
1. Hold key, verify repeat rate matches config
2. Type in different keyboard layouts
3. Use IME to compose characters
4. Super+Shift+C cycles through layouts
5. Alt+Shift toggles between en/fr

---

## Phase 1.3: Pointer Input Enhancements

**Target Release**: v0.3.0 (with Phase 1)
**Timeline**: 1-2 weeks
**Status**: PLANNED

### Goals

- Cursor motion tracking (accurate position)
- Button click detection and routing (left/middle/right)
- Double-click detection (for applications)
- Cursor image synchronization (match application hints)
- Pointer constraints (for games/3D apps)

### 1.3.1: Cursor Motion Tracking

**Why**: Accurate mouse position is fundamental to all pointer operations.

**Implementation**:

**File**: `src/input_handler.rs` (enhance pointer handler)

Smithay already provides cursor position via `PointerHandle`. We need to:

1. **Track current position**:
```rust
pub struct PointerState {
    /// Current cursor position in compositor space
    pub location: Point<f64, Logical>,
    /// Previous frame position (for delta calculation)
    pub last_location: Point<f64, Logical>,
    /// Velocity (pixels per millisecond)
    pub velocity: Vector<f64, Logical>,
}

impl PointerState {
    pub fn on_motion(&mut self, pos: Point<f64, Logical>) {
        self.last_location = self.location;
        self.location = pos;

        // Calculate velocity for smooth tracking
        let delta = pos - self.last_location;
        self.velocity = delta / 16.0;  // Assuming 60 FPS
    }
}
```

2. **Find window under cursor**:
```rust
fn find_window_under_cursor(&self, location: Point<f64, Logical>)
    -> Option<(WindowElement, Point<f64, Logical>)>
{
    self.space
        .element_under(location)
        .map(|(elem, loc)| (elem, loc))
}
```

3. **Update Wayland cursor**:
```rust
// In pointer motion handler
let surface = find_window_under_cursor(location);
self.pointer.motion(self, location, serial, time);
```

**Testing**:
- Cursor position accurate within 1 pixel
- No jumps or stuttering
- Works across multiple outputs
- Smooth motion at 60 FPS

---

### 1.3.2: Button Event Routing

**Why**: Click detection determines which window gets input.

**Implementation**:

**File**: `src/input_handler.rs` (pointer button handler)

```rust
impl<BackendData: Backend> WyvernState<BackendData> {
    fn on_pointer_button(&mut self, btn: PointerButtonEvent) {
        let button = btn.button();
        let state = btn.state();  // Pressed or Released
        let serial = SCOUNTER.next_serial();
        let time = btn.time_msec();

        // Find window under cursor
        let location = self.pointer.current_location();
        if let Some((window, _)) = self.space.element_under(location) {
            // Get surface under cursor within the window
            if let Some((_surface, location)) = window.surface_under(
                location - self.space.element_location(&window).unwrap().to_f64(),
                WindowSurfaceType::ALL,
            ) {
                // Send button event to surface
                let button_event = ButtonEvent {
                    button,
                    state,
                    serial,
                    time,
                };
                self.pointer.button(self, button_event);
            }
        }
    }
}
```

**Button Mapping**:
- Left (272): Select, drag, interactive elements
- Middle (273): Paste, pan (in some apps)
- Right (274): Context menu
- Side buttons (275, 276): Back/Forward in browsers

**Testing**:
- Left click selects correct window
- Drag operations work (window move/resize)
- Right-click shows context menu
- Middle-click paste works in X11 apps
- Click on decorations (close/minimize buttons)

---

### 1.3.3: Double-Click Detection

**Why**: Applications need to distinguish single vs. double clicks.

**Implementation**:

```rust
pub struct ClickState {
    /// Time of last click (ms)
    last_click_time: u32,
    /// Position of last click
    last_click_position: Point<f64, Logical>,
    /// Double-click timeout (ms)
    double_click_timeout: u32,
    /// Double-click distance threshold (pixels)
    double_click_distance: f64,
}

impl ClickState {
    pub fn on_button(&mut self, button: u32, time: u32, location: Point<f64, Logical>)
        -> ClickType
    {
        let delta_time = time - self.last_click_time;
        let delta_distance = location.distance(self.last_click_position);

        if delta_time < self.double_click_timeout
            && delta_distance < self.double_click_distance
        {
            ClickType::Double
        } else {
            self.last_click_time = time;
            self.last_click_position = location;
            ClickType::Single
        }
    }
}
```

**Config**:
```toml
[pointer]
double_click_timeout = 300      # ms
double_click_distance = 5.0     # pixels
```

**Testing**:
- Double-click in text editor selects word
- Double-click title bar maximizes window
- Triple-click selects paragraph
- Slow double-clicks treated as separate single clicks

---

### 1.3.4: Cursor Image Synchronization

**Why**: Cursor should change shape (arrow, text, hand, etc.) based on context.

**Implementation**:

```rust
pub struct CursorState {
    /// Current cursor shape
    current_shape: CursorShape,
    /// Surface providing cursor image (if any)
    cursor_surface: Option<WlSurface>,
    /// Hotspot (offset from top-left)
    hotspot: Point<i32, Logical>,
}

enum CursorShape {
    Default,      // Arrow
    Text,         // I-beam
    Hand,         // Pointer/hand
    Busy,         // Wait spinner
    Move,         // Four-way arrows
    Resize(Edge), // Edge-specific resize cursor
}

impl WyvernState {
    fn update_cursor(&mut self, location: Point<f64, Logical>) {
        if let Some((window, _)) = self.space.element_under(location) {
            // Ask window for cursor image
            if let Some(surface) = window.wl_surface() {
                // Check if window has set custom cursor
                if let Some(cursor_data) = get_cursor_data(&surface) {
                    self.cursor_state.cursor_surface = Some(cursor_data.surface);
                    self.cursor_state.hotspot = cursor_data.hotspot;
                }
            }
        }
    }
}
```

**Testing**:
- Arrow cursor on desktop
- Text (I-beam) cursor in text editor
- Hand cursor over links
- Resize cursors at window edges
- Wait cursor during long operations

---

### 1.3.5: Pointer Constraints (Fullscreen Games)

**Why**: Games and 3D apps need to constrain cursor to window.

**Implementation**:

Uses Wayland pointer-constraints protocol:

```rust
pub struct PointerConstraints {
    /// Active constraint (if any)
    active: Option<PointerConstraint>,
}

impl PointerConstraints {
    pub fn on_constraint_created(&mut self, constraint: PointerConstraint) {
        // Set constraint region
        self.active = Some(constraint);
    }

    pub fn on_pointer_motion(&mut self, new_location: Point<f64, Logical>)
        -> Point<f64, Logical>
    {
        if let Some(constraint) = &self.active {
            // Check if position is within constraint region
            if !constraint.region.contains(new_location) {
                // Clamp or warp pointer back
                return constraint.region.clamp(new_location);
            }
        }
        new_location
    }
}
```

**Constraint Types**:
- Confined: Cursor stays within region (can't leave window)
- Locked: Cursor position is hidden, only motion delta available

**Testing**:
- FPS games with locked cursor
- 3D modeling with confined cursor
- Cursor reappears on Alt+Tab
- Motion events still work while constrained

---

### 1.3.6: Testing Strategy for Phase 1.3

**Unit Tests**:
- ClickState double-click detection
- PointerConstraints region clamping

**Integration Tests**:
- Cursor motion tracking accuracy
- Button event routing to correct window
- Double-click detection timing

**Manual Testing**:
1. Move cursor, watch for smooth motion
2. Click windows and verify focus changes
3. Double-click title bar to maximize
4. Run fullscreen game with locked cursor
5. Middle-click to paste in terminal

---

## Phase 1.4: Basic Window Tiling

**Target Release**: v0.3.0 (with Phase 1)
**Timeline**: 2-3 weeks
**Status**: PLANNED

### Goals

- Master-stack tiling layout (primary + secondary areas)
- Monocle layout (fullscreen mode)
- Floating window mode
- Window arrangement and resizing
- Configurable master ratio and gaps

### 1.4.1: Master-Stack Layout

**Why**: Users need automatic window arrangement for productivity.

**Implementation**:

**File**: `src/shell/mod.rs` (enhance `recalculate_tiling_layout`)

```rust
pub enum LayoutMode {
    MasterStack,  // Primary window (50%), secondary stack (50%)
    Monocle,      // All windows fullscreen
    Floating,     // Windows float freely
}

pub struct TilingState {
    pub tiled_windows: Vec<WindowElement>,
    pub layout_mode: LayoutMode,
    pub master_ratio: f32,  // 0.0..1.0, default 0.5
    pub gap_size: i32,      // pixels between windows
}

impl TilingState {
    pub fn arrange_windows(&mut self, space: &mut Space<WindowElement>, output_geo: Rectangle) {
        match self.layout_mode {
            LayoutMode::MasterStack => self.arrange_master_stack(space, output_geo),
            LayoutMode::Monocle => self.arrange_monocle(space, output_geo),
            LayoutMode::Floating => {} // No arrangement needed
        }
    }

    fn arrange_master_stack(&self, space: &mut Space<WindowElement>, output_geo: Rectangle) {
        if self.tiled_windows.is_empty() {
            return;
        }

        let gap = self.gap_size;
        let master_width = (output_geo.size.w as f32 * self.master_ratio) as i32;
        let stack_width = output_geo.size.w - master_width;

        // Master window (first in list)
        let master = &self.tiled_windows[0];
        let master_geo = Rectangle::from_loc_and_size(
            output_geo.loc,
            (master_width - gap, output_geo.size.h),
        );
        space.map_element(master.clone(), master_geo.loc, false);
        master.set_geometry(master_geo);

        // Stack windows (remaining)
        let stack_height = output_geo.size.h / (self.tiled_windows.len() - 1) as i32;
        for (i, window) in self.tiled_windows[1..].iter().enumerate() {
            let stack_geo = Rectangle::from_loc_and_size(
                Point::from((output_geo.loc.x + master_width + gap,
                             output_geo.loc.y + i as i32 * stack_height)),
                (stack_width - gap, stack_height - gap),
            );
            space.map_element(window.clone(), stack_geo.loc, false);
            window.set_geometry(stack_geo);
        }
    }

    fn arrange_monocle(&self, space: &mut Space<WindowElement>, output_geo: Rectangle) {
        for window in &self.tiled_windows {
            space.map_element(window.clone(), output_geo.loc, false);
            window.set_geometry(output_geo);
        }
    }
}
```

**Config**:
```toml
[tiling]
layout_mode = "master-stack"  # or "monocle", "floating"
master_ratio = 0.55           # Master window is 55% of width
gap_size = 10                 # 10px between windows
```

**Testing**:
- Windows tile correctly across output
- Master ratio adjustment works
- Gaps are consistent
- Layout change preserves window content

---

### 1.4.2: Layout Cycling

**Why**: Users switch between layouts with keyboard shortcuts.

**Implementation**:

```rust
impl TilingState {
    pub fn cycle_layout(&mut self) {
        self.layout_mode = match self.layout_mode {
            LayoutMode::MasterStack => LayoutMode::Monocle,
            LayoutMode::Monocle => LayoutMode::Floating,
            LayoutMode::Floating => LayoutMode::MasterStack,
        };
    }
}

// In input_handler.rs
KeyAction::CycleTilingLayout => {
    self.tiling_state.cycle_layout();
    let _ = self.event_tx.send(CustomEvent::TilingRecalculate);
}
```

**Keyboard Binding**: Super+Shift+C cycles layouts

**Testing**:
- Cycle through all 3 layouts
- Windows re-arrange correctly
- Floating windows don't snap to grid

---

### 1.4.3: Master Ratio Adjustment

**Why**: Users customize the master/stack split dynamically.

**Implementation**:

```rust
impl TilingState {
    pub fn increase_master_ratio(&mut self) {
        self.master_ratio = (self.master_ratio + 0.05).min(0.9);
    }

    pub fn decrease_master_ratio(&mut self) {
        self.master_ratio = (self.master_ratio - 0.05).max(0.1);
    }
}

// In input_handler.rs
KeyAction::IncreaseMasterRatio => {
    self.tiling_state.increase_master_ratio();
    let _ = self.event_tx.send(CustomEvent::TilingRecalculate);
}

KeyAction::DecreaseMasterRatio => {
    self.tiling_state.decrease_master_ratio();
    let _ = self.event_tx.send(CustomEvent::TilingRecalculate);
}
```

**Keyboard Bindings**:
- Super+Shift+L: Increase master window
- Super+Shift+H: Decrease master window

**Testing**:
- Ratio adjusts in 5% increments
- Windows resize smoothly
- Ratio persists across layout changes
- No windows smaller than minimum

---

### 1.4.4: Window Movement Between Positions

**Why**: Users reorder windows in the layout.

**Implementation**:

```rust
impl TilingState {
    /// Move window to master position (promoting from stack)
    pub fn promote_to_master(&mut self, window: &WindowElement) {
        if let Some(pos) = self.tiled_windows.iter().position(|w| w == window) {
            if pos != 0 {
                self.tiled_windows.remove(pos);
                self.tiled_windows.insert(0, window.clone());
            }
        }
    }

    /// Move window forward in stack
    pub fn move_forward(&mut self, window: &WindowElement) {
        if let Some(pos) = self.tiled_windows.iter().position(|w| w == window) {
            if pos > 0 {
                self.tiled_windows.swap(pos, pos - 1);
            }
        }
    }

    /// Move window backward in stack
    pub fn move_backward(&mut self, window: &WindowElement) {
        if let Some(pos) = self.tiled_windows.iter().position(|w| w == window) {
            if pos < self.tiled_windows.len() - 1 {
                self.tiled_windows.swap(pos, pos + 1);
            }
        }
    }
}
```

**Keyboard Bindings**:
- Super+Return: Promote focused window to master
- Super+J: Move window down in stack
- Super+K: Move window up in stack

**Testing**:
- Promote window from stack to master
- Reorder windows in stack
- Verify window content preserved

---

### 1.4.5: Floating Mode

**Why**: Some windows (dialogs, floating panels) shouldn't tile.

**Implementation**:

```rust
pub struct WindowState {
    pub element: WindowElement,
    pub is_floating: bool,
    pub floating_geometry: Option<Rectangle<i32, Logical>>,
}

impl TilingState {
    pub fn toggle_floating(&mut self, window: &WindowElement) {
        if let Some(state) = self.window_states.iter_mut().find(|s| &s.element == window) {
            state.is_floating = !state.is_floating;
        }
    }

    pub fn arrange_windows_with_floating(&self, space: &mut Space<WindowElement>, output_geo: Rectangle) {
        let tiled: Vec<_> = self.window_states.iter()
            .filter(|s| !s.is_floating)
            .map(|s| s.element.clone())
            .collect();

        // Arrange tiled windows
        // Floating windows keep their last position
    }
}
```

**Keyboard Binding**: Super+Shift+Space toggles floating for focused window

**Testing**:
- Toggle floating mode
- Floating windows stay in place
- Can't tile floating windows
- Float dialogs by default

---

### 1.4.6: Testing Strategy for Phase 1.4

**Unit Tests**:
- TilingState window arrangement logic
- Ratio adjustment bounds
- Window promotion/demotion

**Integration Tests**:
- Windows tile correctly on output
- Layout cycling preserves window content
- Master ratio adjustment

**Manual Testing**:
1. Create 3 windows, verify master-stack layout
2. Super+Shift+C cycle to monocle (all fullscreen)
3. Super+Shift+L increase master window size
4. Super+Return promote window to master
5. Super+Shift+Space toggle floating

---

## Phase 1.5: Window Resize/Move Refinement

**Target Release**: v0.3.0 (with Phase 1)
**Timeline**: 1-2 weeks
**Status**: PLANNED

### Goals

- Size hints respecting (min/max window dimensions)
- Visual feedback during resize (outline/preview)
- Keyboard-based resize (Alt+arrow keys)
- Smooth animations during resize
- Proper configure event sequencing

### 1.5.1: Size Hints Support

**Why**: Applications specify min/max/preferred window sizes.

**Implementation**:

```rust
/// Window size constraints from XDG or X11
pub struct SizeHints {
    pub min_size: Option<Size<i32, Logical>>,
    pub max_size: Option<Size<i32, Logical>>,
    pub preferred_size: Option<Size<i32, Logical>>,
    pub size_increments: Option<Size<i32, Logical>>,
}

impl WindowElement {
    pub fn get_size_hints(&self) -> SizeHints {
        // Extract from XDG toplevel state
        if let Some(toplevel) = self.0.toplevel() {
            toplevel.with_pending_state(|state| {
                SizeHints {
                    min_size: state.min_size,
                    max_size: state.max_size,
                    preferred_size: state.size,
                    size_increments: None, // From X11 hints
                }
            })
        } else {
            SizeHints::default()
        }
    }

    pub fn clamp_size(&self, mut size: Size<i32, Logical>) -> Size<i32, Logical> {
        let hints = self.get_size_hints();
        if let Some(min) = hints.min_size {
            size.w = size.w.max(min.w);
            size.h = size.h.max(min.h);
        }
        if let Some(max) = hints.max_size {
            size.w = size.w.min(max.w);
            size.h = size.h.min(max.h);
        }
        size
    }
}
```

**Testing**:
- Resize terminal to minimum size
- Maximize window respects max_size
- Drag corner doesn't violate constraints
- Size increments honored (e.g., terminal columns)

---

### 1.5.2: Visual Feedback During Resize

**Why**: Users see what size the window will be before releasing.

**Implementation**:

In resize grab handler (`src/shell/grabs.rs`):

```rust
pub struct ResizeData {
    pub initial_window_location: Point<i32, Logical>,
    pub initial_window_size: Size<i32, Logical>,
    pub edges: ResizeEdge,
    pub target_size: Size<i32, Logical>,  // NEW: Target size during drag
}

impl PointerResizeSurfaceGrab {
    fn update_target_size(&mut self, pointer_pos: Point<f64, Logical>) {
        let delta = pointer_pos - self.start_data.location.to_f64();

        let mut target_size = self.data.initial_window_size.clone();

        if self.data.edges.contains(ResizeEdge::LEFT) {
            target_size.w = (target_size.w as f64 - delta.x) as i32;
        }
        if self.data.edges.contains(ResizeEdge::RIGHT) {
            target_size.w = (target_size.w as f64 + delta.x) as i32;
        }
        if self.data.edges.contains(ResizeEdge::TOP) {
            target_size.h = (target_size.h as f64 - delta.y) as i32;
        }
        if self.data.edges.contains(ResizeEdge::BOTTOM) {
            target_size.h = (target_size.h as f64 + delta.y) as i32;
        }

        // Clamp to size hints
        self.data.target_size = self.window.clamp_size(target_size);

        // Send configure with target size (visual feedback)
        if let Some(toplevel) = self.window.0.toplevel() {
            toplevel.with_pending_state(|state| {
                state.size = Some(self.data.target_size);
            });
            toplevel.send_pending_configure();
        }
    }
}
```

**Rendering**: When resizing, window shows target size in real-time

**Testing**:
- Drag corner shows size changing
- Size hints enforced visually
- No jitter or flicker during drag
- Release applies final size

---

### 1.5.3: Keyboard-Based Resize

**Why**: Users resize without mouse (accessibility, tiling).

**Implementation**:

```rust
impl WyvernState {
    pub fn resize_focused_window(&mut self, direction: ResizeDirection, amount: i32) {
        if let Some(window) = self.focus_stack.current() {
            let current_geo = self.space.element_location(&window);
            let current_size = window.geometry().size;

            let mut new_size = current_size;
            match direction {
                ResizeDirection::Up => new_size.h -= amount,
                ResizeDirection::Down => new_size.h += amount,
                ResizeDirection::Left => new_size.w -= amount,
                ResizeDirection::Right => new_size.w += amount,
            }

            // Clamp to size hints
            new_size = window.clamp_size(new_size);

            // Update window
            if let Some(toplevel) = window.0.toplevel() {
                toplevel.with_pending_state(|state| {
                    state.size = Some(new_size);
                });
                toplevel.send_pending_configure();
            }
        }
    }
}

// In input_handler.rs
KeyAction::ResizeWindow(direction, amount) => {
    self.resize_focused_window(direction, amount);
}
```

**Keyboard Bindings**:
- Super+Alt+J/K/L/I: Resize down/up/right/left
- Hold for continuous resize

**Testing**:
- Resize window without mouse
- Respect size hints
- Works in floating mode
- No crashes on minimum size

---

### 1.5.4: Smooth Animations

**Why**: Visual polish - resize/move should animate smoothly.

**Implementation**:

```rust
pub struct AnimationState {
    /// Active animations
    active: Vec<WindowAnimation>,
}

pub enum WindowAnimation {
    Resize {
        window: WindowElement,
        start_size: Size<i32, Logical>,
        target_size: Size<i32, Logical>,
        start_time: Instant,
        duration_ms: u32,
    },
    Move {
        window: WindowElement,
        start_location: Point<i32, Logical>,
        target_location: Point<i32, Logical>,
        start_time: Instant,
        duration_ms: u32,
    },
}

impl AnimationState {
    pub fn update(&mut self, space: &mut Space<WindowElement>, now: Instant) {
        for animation in &self.active {
            match animation {
                WindowAnimation::Resize { window, start_size, target_size, start_time, duration_ms } => {
                    let elapsed = now.duration_since(*start_time).as_millis() as u32;
                    let progress = (elapsed as f32 / *duration_ms as f32).min(1.0);

                    // Easing function (linear for now, can use easeInOut)
                    let current_size = Size::from((
                        (start_size.w as f32 + (target_size.w - start_size.w) as f32 * progress) as i32,
                        (start_size.h as f32 + (target_size.h - start_size.h) as f32 * progress) as i32,
                    ));

                    if let Some(toplevel) = window.0.toplevel() {
                        toplevel.with_pending_state(|state| {
                            state.size = Some(current_size);
                        });
                        toplevel.send_pending_configure();
                    }
                }
                // Similar for Move animation
                _ => {}
            }
        }

        // Remove completed animations
        self.active.retain(|anim| {
            // Check if duration elapsed
            true
        });
    }
}
```

**Config**:
```toml
[animation]
resize_duration_ms = 200
move_duration_ms = 150
easing = "ease-in-out"  # or "linear"
```

**Testing**:
- Resize animates smoothly
- No frame drops during animation
- Animation duration matches config
- Can interrupt animation with new action

---

### 1.5.5: Configure Event Sequencing

**Why**: Ensure clients receive configure events in correct order.

**Implementation**:

Smithay's `toplevel.send_configure()` handles sequencing automatically. We just need to:

1. Update pending state
2. Send configure once
3. Wait for ack, then apply

```rust
impl WindowElement {
    pub fn update_and_send_configure(&self, new_size: Size<i32, Logical>) {
        if let Some(toplevel) = self.0.toplevel() {
            // Set pending state
            toplevel.with_pending_state(|state| {
                state.size = Some(new_size);
            });

            // Send configure (will get ack'd by client)
            toplevel.send_pending_configure();

            // Client will send commit with new size
            // Window will be mapped to new size automatically
        }
    }
}
```

**Testing**:
- Windows don't flicker on resize
- Clients process configure events correctly
- No "stuck" window states

---

### 1.5.6: Testing Strategy for Phase 1.5

**Unit Tests**:
- Size hints clamping
- Animation progress calculation

**Integration Tests**:
- Resize with mouse drag
- Keyboard-based resize
- Size hint enforcement

**Manual Testing**:
1. Drag window corner, watch for smooth resize
2. Super+Alt+J to resize with keyboard
3. Resize terminal, verify column/row counts correct
4. Maximize respects max_size hint
5. Resize animation looks smooth

---

## Phase 2: Advanced Rendering

**Target Release**: v0.4.0
**Timeline**: 5-7 weeks
**Status**: PLANNED (starts after Phase 1)

### Goals

- Damage tracking optimization (only render changed areas)
- Basic animations (transitions, fade effects)
- Server-side decorations polish
- Layer shell support (panels, notifications)
- Cursor improvements

### 2.1: Damage Tracking Optimization

Implement per-window damage tracking to reduce GPU work.

### 2.2: Basic Animations

Window open/close transitions, focus change animations.

### 2.3: Server-Side Decorations Polish

Theme system, color schemes, hover effects.

### 2.4: Layer Shell Support

Exclusive zones, layer ordering, auto-hide panels.

### 2.5: Cursor Improvements

Theme hot-loading, DPI scaling, animated cursors.

---

## Phase 3: Protocol & Interoperability

**Target Release**: v0.5.0
**Timeline**: 6-8 weeks
**Status**: PLANNED (starts after Phase 2)

### Goals

- XWayland improvements (X11 window integration)
- Additional shell protocols
- Data & clipboard management
- Input method protocol support

---

## Phase 4: Advanced Features & Optimization

**Target Release**: v0.6.0
**Timeline**: 6-8 weeks
**Status**: PLANNED (starts after Phase 3)

### Goals

- Multi-monitor support
- Workspace management
- Session management & lock screen
- Performance optimization
- Error handling & logging

---

## Phase 5: Production Deployment & Polish

**Target Release**: v1.0.0
**Timeline**: 8-10 weeks
**Status**: PLANNED (final phase)

### Goals

- Comprehensive testing suite
- Complete documentation
- Distribution packages
- Platform-specific features
- Production readiness

---

## Summary: Implementation Sequence

```
Phase 1 (Weeks 1-6): Core Foundations
├─ 1.1 Focus Management (COMPLETE)
│  ├─ 1.1.1 FocusStack data structure ✅
│  ├─ 1.1.2 Window lifecycle hooks ✅
│  └─ 1.1.3 Alt+Tab key binding ✅
├─ 1.2 Keyboard Input Enhancements (→ start next session)
├─ 1.3 Pointer Input Enhancements
├─ 1.4 Basic Window Tiling
└─ 1.5 Window Resize/Move Refinement

Phase 2 (Weeks 7-13): Advanced Rendering
├─ 2.1 Damage Tracking
├─ 2.2 Animations
├─ 2.3 SSD Polish
├─ 2.4 Layer Shell
└─ 2.5 Cursor Improvements

Phase 3 (Weeks 14-21): Protocols
Phase 4 (Weeks 22-29): Advanced Features
Phase 5 (Weeks 30-39): Production Release
```

---

## Development Checklist Template

For each phase/subsection:
- [ ] Research & architecture design
- [ ] Core implementation
- [ ] Unit tests
- [ ] Integration tests
- [ ] Manual testing scenarios
- [ ] Documentation & comments
- [ ] Formatting (cargo fmt)
- [ ] Linting (clippy)
- [ ] All tests passing (100%)
- [ ] Compilation (0 errors, 0 warnings)
- [ ] Commit with comprehensive message

---

## Next Session: Phase 1.2 Kickoff

When resuming in the next session:

1. Review Phase 1.1 completion summary
2. Read Phase 1.2 implementation details above
3. Start with 1.2.1 (Key repeat handling)
4. Follow the same rigorous testing/documentation pattern
5. Commit regularly with clear messages
6. Update this roadmap as you complete each subsection

---

**Questions or clarifications needed?** Refer to:
- `PHASE_ROADMAP.md` - High-level overview
- `PHASE_1_IMPLEMENTATION_PLAN.md` - Detailed Phase 1 design
- `docs/ARCHITECTURE.md` - System architecture
- Source code comments - Implementation details
