# Wyvern Phase Roadmap v0.2.0+

**Document Purpose:** Clear, actionable phase-by-phase implementation plan for Wyvern v0.2.0 through v1.0
**Last Updated:** 2026-01-01
**Current Release:** v0.2.0 (Phase 0 Complete)
**Next Release Target:** v0.3.0 (Phase 1 Complete)

---

## Executive Summary

Wyvern has completed **Phase 0: Production Foundations**. The compositor now has:
- ✅ Security patches and stability fixes
- ✅ Comprehensive documentation and test suite
- ✅ Optional performance optimization (config caching)

**Phases 1-5** establish a complete, production-grade Wayland compositor with:
- Core compositor features (focus, tiling, input)
- Advanced rendering and visual effects
- Full protocol support and interoperability
- Performance optimization and testing
- Production deployment readiness

---

## Phase 0: Production Foundations ✅ COMPLETE
**Status:** ✅ DELIVERED (v0.2.0)
**Duration:** Concentrated deep-dive effort
**Key Deliverables:**
- Security patches (RUSTSEC-2025-0055)
- Eliminated 7 panic! calls
- Fixed memory safety issues
- Comprehensive documentation (340+ lines)
- Test suite (8 tests, 100% pass)
- Optional performance caching

---

## Phase 1: Core Compositor Features
**Status:** 📋 PLANNED
**Target Release:** v0.3.0
**Timeline:** 4-6 weeks
**Goal:** Implement fundamental window management and input handling

### 1.1 Focus Management System
**Why:** Windows need to know which has keyboard/pointer focus
**What to build:**
- Keyboard focus tracking (track which window gets keyboard input)
- Pointer focus tracking (track which window is under cursor)
- Focus cycling logic (Alt+Tab window switching)
- Focus change notifications to clients (wl_keyboard::enter/leave)
- XWayland focus integration

**Key Files:** `src/focus.rs`, `src/shell/*.rs`
**Tests needed:**
- Focus cycling between windows
- Focus persistence across minimize/maximize
- XWayland focus synchronization

### 1.2 Keyboard Input Handler Enhancements
**Why:** Users need reliable keyboard input with proper repeat
**What to build:**
- Keyboard repeat handling (hold key, auto-repeat after delay)
- IME (Input Method Editor) integration points
- Key event routing to focused window
- Special key handling (Super key, Alt key combos)
- Keyboard layout switching support

**Key Files:** `src/input_handler.rs`
**Tests needed:**
- Key repeat timing accuracy
- Key modifiers (Shift, Ctrl, Alt, Super) work correctly
- Layout switching doesn't break key events

### 1.3 Pointer Input Handler Enhancements
**Why:** Mouse/trackpad interaction must be smooth and responsive
**What to build:**
- Cursor motion tracking
- Button event routing (left, middle, right clicks)
- Double-click detection
- Cursor image synchronization
- Pointer constraint support (fullscreen games)
- Touchpad gesture support (if available)

**Key Files:** `src/input_handler.rs`, `src/cursor.rs`
**Tests needed:**
- Cursor position accuracy
- Button click routing to correct window
- Double-click timing validation

### 1.4 Basic Window Tiling
**Why:** Modern compositor users expect organized window layouts
**What to build:**
- Master-stack tiling layout (Dwm/i3 style)
  - Master window area (often 50% of screen)
  - Secondary stack area (remaining 50%)
  - Configurable master ratio adjustment
- Basic tile switching (mod+arrow to move between tiles)
- Window gap configuration
- Monocle layout (fullscreen mode)
- Floating window mode per window

**Key Files:** `src/shell/element.rs`, `src/state.rs`
**Config options:**
- `master_ratio`: 0.5 (50/50 split)
- `gap_size`: 10px (window borders)
- `layout_mode`: "master-stack" | "monocle" | "floating"

**Tests needed:**
- Windows tile correctly across resizes
- Master ratio adjustment works
- Gap sizing is consistent

### 1.5 Window Resize/Move Operations (Refinement)
**Why:** Users need to resize and reposition windows
**Status:** Partially implemented (grabs.rs exists)
**What to enhance:**
- Add size hints respect (min_width, min_height, etc.)
- Improve resize feedback visual indicators
- Add keyboard-based resize (hold Alt, arrow keys)
- Smooth animations during resize
- Proper configure event sequencing

**Key Files:** `src/shell/grabs.rs`

---

## Phase 2: Advanced Rendering
**Status:** 📋 PLANNED
**Target Release:** v0.4.0
**Timeline:** 5-7 weeks
**Goal:** Add visual polish and rendering optimizations

### 2.1 Damage Tracking Optimization
**Why:** Reduce GPU/CPU work by only rendering changed areas
**What to build:**
- Per-window damage tracking
- Damage union for compositor layers
- Efficient damage composition
- Direct scanout path optimization
- Output damage synchronization with atomic commits

**Performance Target:** 60 FPS on moderate GPU at 1440p

### 2.2 Basic Animations
**Why:** Smooth transitions improve user experience
**What to build:**
- Window open/close transitions (fade, slide)
- Focus change animations
- Workspace switch animations (optional)
- Damage-aware animation rendering
- Animation timing configuration

**Key Files:** New `src/animation.rs`
**Config options:**
- `animation_duration_ms`: 200-500ms
- `animation_easing`: "linear" | "easeInOut"

### 2.3 Server-Side Decorations Polish
**Why:** Consistent window decorations across all clients
**What to build:**
- Theme system for decorations
- Color scheme support (light/dark)
- Hover effects on decoration buttons
- Right-click menu support
- Decoration option negotiation with clients

**Key Files:** `src/shell/ssd.rs`

### 2.4 Layer Shell Support
**Why:** Panels, taskbars, notifications need proper layering
**What to build:**
- Exclusive zones (panels reserve screen space)
- Layer ordering (background, bottom, top, overlay)
- Auto-hide panel support
- Notification positioning
- Anchor point support (top, bottom, left, right edges)

**Key Files:** `src/shell/mod.rs` (expand xdg support)

### 2.5 Cursor Improvements
**Why:** Cursor should match theme and application hints
**What to build:**
- Cursor theme hot-loading
- Cursor size per output DPI
- Animated cursor support
- HiDPI cursor rendering
- Application-specific cursor shapes

**Key Files:** `src/cursor.rs`

---

## Phase 3: Protocol & Interoperability
**Status:** 📋 PLANNED
**Target Release:** v0.5.0
**Timeline:** 6-8 weeks
**Goal:** Support additional Wayland protocols for ecosystem compatibility

### 3.1 XWayland Improvements
**Why:** Support legacy X11 applications seamlessly
**What to build:**
- Proper ICCCM window hints support
- EWMH extended window manager hints
- X11 window type handling (dialog, menu, tooltip, etc.)
- Drag-and-drop (XDND protocol) support
- Copy/paste via selection atoms
- Minimize/maximize/fullscreen via X11 requests

**Key Files:** `src/shell/x11.rs`

### 3.2 Additional Shell Protocols
**Why:** Support different window types and application needs
**What to build:**
- wlr-layer-shell (panels, notifications)
- wlr-output-management (display configuration)
- wlr-virtual-pointer (remote input)
- wlr-screencopy (screenshot/recording)
- xdg-activation (app focus requests)

**Key Files:** New protocol handler modules

### 3.3 Data & Clipboard Management
**Why:** Copy/paste between applications is essential
**What to build:**
- Wayland data-device protocol
- Selection clipboard management
- Drag-and-drop data transfer
- MIME type negotiation
- Clipboard history (optional)

### 3.4 Input Method Protocol
**Why:** Support IME for CJK and other input methods
**What to build:**
- Input method context creation
- Text input protocol v1/v3 support
- Preedit text rendering integration
- Commit string handling

---

## Phase 4: Advanced Features & Optimization
**Status:** 📋 PLANNED
**Target Release:** v0.6.0
**Timeline:** 6-8 weeks
**Goal:** Production-grade features and performance

### 4.1 Multi-Monitor Support
**Why:** Most users have multiple displays
**What to build:**
- Monitor hotplug detection
- Per-output configuration
- Cursor movement across monitors
- Window focusing across monitors
- Workspace assignment per monitor (optional)
- Output configuration via wlr-output-management

**Testing:** Multi-monitor test suite with virtual outputs

### 4.2 Workspace Management
**Why:** Organize windows across virtual workspaces
**What to build:**
- Multiple virtual workspaces (typically 5-10)
- Window workspace assignment
- Workspace switching (mod+number)
- Window move between workspaces
- Workspace visualization (indicators, preview)
- Persist workspace layout to config

### 4.3 Session Management & Lock Screen
**Why:** Secure sessions and screen locking
**What to build:**
- Session lifecycle management
- Lock screen support (ext-session-lock protocol)
- Lock screen keyboard/mouse handling
- Session restore on unlock
- Idle detection and auto-lock

### 4.4 Performance Optimization
**Why:** Wyvern should run smoothly on modest hardware
**Optimization Targets:**
- Frame time < 16ms (60 FPS target)
- Memory footprint < 50MB baseline
- Startup time < 2s
- Config load time < 100ms (achieved via bincode cache)

**Key Areas:**
- Damage tracking refinement
- Render batching optimization
- Memory pooling for allocations
- Lazy loading of features
- Profiling-guided optimization (use puffin/tracy)

### 4.5 Error Handling & Logging
**Why:** Production systems need excellent observability
**What to build:**
- Structured logging everywhere (tracing crate)
- Log level configuration per module
- Trace profiling support (puffin/tracy)
- Performance metrics collection
- Crash reporting infrastructure

---

## Phase 5: Production Deployment & Polish
**Status:** 📋 PLANNED
**Target Release:** v1.0.0
**Timeline:** 8-10 weeks
**Goal:** Release-grade stability and documentation

### 5.1 Comprehensive Testing
**Why:** Users deserve reliable software
**What to build:**
- Unit test suite (config, state machine, rendering)
- Integration tests (backend initialization, protocol handling)
- System tests (multi-window, multi-monitor scenarios)
- Stress tests (1000+ windows, rapid focus changes)
- Regression test suite (automated CI/CD)
- Performance benchmarks (track FPS, memory, latency)

**Target Coverage:** ≥80% code coverage

### 5.2 Documentation Completion
**Why:** Users and developers need clear guidance
**What to create:**
- User manual (installation, configuration, usage)
- Developer guide (architecture deep-dive, contribution guide)
- API documentation (rustdoc)
- Troubleshooting guide (common issues, solutions)
- Architecture decision records (ADRs)
- Security policy and vulnerability disclosure process

### 5.3 Build & Distribution
**Why:** Users need easy installation
**What to provide:**
- Packaged releases (Linux distros)
- Binary releases for major platforms
- Docker image for containerized deployment
- Installation scripts and dependency management
- Build reproducibility verification
- Security signing of releases

### 5.4 Platform-Specific Features
**Why:** Optimize for different hardware/configurations
**What to build:**
- GPU-specific optimizations (NVIDIA, AMD, Intel)
- Wayland-specific features per platform
- Input device support (tablets, trackpads, keyboards)
- Audio integration (if needed)
- Power management (sleep, idle handling)

### 5.5 Future-Proofing
**Why:** Wyvern should remain maintainable
**What to establish:**
- Semantic versioning and release process
- Backward compatibility policy
- Deprecation policy for old protocols
- Security update cadence
- Feature addition criteria
- Community contribution guidelines

---

## Success Criteria by Phase

| Phase | Metric | Target |
|-------|--------|--------|
| **Phase 0** | Security patches | 100% ✅ |
| **Phase 0** | Documentation completeness | 100% ✅ |
| **Phase 0** | Test pass rate | 100% ✅ |
| **Phase 1** | Focus system working | Yes |
| **Phase 1** | Basic tiling functional | Yes |
| **Phase 1** | Keyboard input stable | Yes |
| **Phase 2** | 60 FPS rendering | Yes |
| **Phase 2** | Visual polish complete | Yes |
| **Phase 3** | XWayland integration | Yes |
| **Phase 3** | Multi-protocol support | Yes |
| **Phase 4** | Multi-monitor working | Yes |
| **Phase 4** | Workspace management | Yes |
| **Phase 5** | Code coverage | ≥80% |
| **Phase 5** | Documentation complete | Yes |
| **Phase 5** | v1.0 release ready | Yes |

---

## Dependencies & Prerequisites

### Phase 1 Prerequisites (from Phase 0)
- ✅ Security patches applied
- ✅ Error handling strategy established
- ✅ Testing framework in place
- ✅ Module documentation complete

### Phase 2 Prerequisites (Phase 1 complete)
- ✅ Focus system working
- ✅ Input handling stable
- ✅ Tiling foundation solid

### Phase 3 Prerequisites (Phase 2 complete)
- ✅ Rendering stable at 60 FPS
- ✅ Visual polish complete
- ✅ Animation system working

### Phase 4 Prerequisites (Phase 3 complete)
- ✅ XWayland stable
- ✅ Multiple protocols working
- ✅ Clipboard/selection working

### Phase 5 Prerequisites (Phase 4 complete)
- ✅ All features implemented
- ✅ Performance targets met
- ✅ No critical bugs remaining

---

## Risk Mitigation

| Risk | Impact | Mitigation |
|------|--------|-----------|
| Smithay API changes | Medium | Pin Smithay version, monitor for breaking changes |
| GPU driver issues | Medium | Fallback to software renderer (Pixman) |
| XWayland complexity | High | Dedicated testing, upstream coordination |
| Performance targets | Medium | Early profiling, optimization phases |
| Community contributions | Low | Clear CONTRIBUTING.md, code review process |

---

## Development Workflow

### For Each Phase:
1. **Planning** (1-2 days): Review requirements, identify risks
2. **Implementation** (3-5 weeks): Code, test, iterate
3. **Testing** (1 week): Unit, integration, system tests
4. **Documentation** (3-5 days): Code docs, user guide, changelog
5. **Release** (1-2 days): Tag, publish, announce

### Code Quality Gates:
- ✅ All tests pass
- ✅ Cargo fmt compliance
- ✅ Clippy zero warnings
- ✅ Documentation updated
- ✅ CHANGELOG.md updated
- ✅ Commit messages follow conventional commits

---

## Quick Reference: What Gets Built When

```
Phase 0: ✅ DONE - Foundations (v0.2.0)
├─ Security patches
├─ Documentation
├─ Test suite
└─ Performance optimization

Phase 1: Focus & Tiling (v0.3.0)
├─ Focus management
├─ Keyboard input
├─ Pointer input
├─ Basic tiling
└─ Resize/move refinement

Phase 2: Rendering & Polish (v0.4.0)
├─ Damage tracking
├─ Animations
├─ SSD polish
├─ Layer shell
└─ Cursor improvements

Phase 3: Protocols (v0.5.0)
├─ XWayland improvements
├─ Shell protocols
├─ Data/clipboard
└─ Input methods

Phase 4: Advanced Features (v0.6.0)
├─ Multi-monitor
├─ Workspaces
├─ Session management
├─ Performance optimization
└─ Observability

Phase 5: Production Release (v1.0.0)
├─ Comprehensive testing
├─ Documentation
├─ Distribution
├─ Platform optimization
└─ Community readiness
```

---

## Questions? See Also:
- `TODOS_AND_BRAINSTORMS.md` - Detailed analysis and deep-dives
- `docs/ARCHITECTURE.md` - System architecture overview
- `config.example.toml` - Configuration reference
- Source files with module-level `//!` documentation

---

**Next Step:** Begin Phase 1 planning and implementation planning (focus management, keyboard input, pointer input, tiling architecture)
