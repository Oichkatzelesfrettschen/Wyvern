# Wyvern Modernization & Refactor Roadmap

**Document Version:** 1.0
**Last Updated:** 2025-12-31
**Project State:** Functional hybrid compositor with dynamic tiling, keyboard settings, multi-backend support

---

## Executive Summary

Wyvern is a **hybrid Wayland compositor** supporting three backends (udev/DRM, winit, X11) with dynamic tiling and keyboard configuration. The codebase is well-structured but requires modernization across three vectors:

1. **Dependency Updates** - Pin toolchain, update key crates to 2026 ecosystem versions
2. **Backend Architecture** - Improve session management (libseat), optimize XWayland lifecycle
3. **Rendering & Diagnostics** - Stabilize GL as default, enhance tracing/logging, deprecate Vulkan complexity

This document evolves iteratively; sections are marked with task status and confidence levels.

---

## Part 1: Design Critique & Current State Analysis

### 1.1 Framework Layer (Smithay v0.7.0)

**Status:** EXCELLENT CHOICE
**Confidence:** 100%
**Assessment:**

Smithay is the de-facto Rust standard for building Wayland compositors. It correctly abstracts:
- Wire protocol boilerplate (Wayland/Wayland Protocols)
- Event loop integration (calloop)
- XDG shell, layer shell, and data device protocols

**Current Implementation Strengths:**
- Modular architecture (lib.rs exposes state, rendering, input as separate modules)
- Conditional feature compilation (udev, winit, x11, xwayland all togglable)
- Proper tracing integration already in place (main.rs uses tracing_subscriber)
- Support for multiple rendering backends (GL, Vulkan, Pixman)

**Current Gaps & Critique:**

| Issue | Impact | Priority |
|-------|--------|----------|
| winit as default backend | Dev convenience, but insufficient for production | HIGH |
| No explicit libseat integration visible | Missing privilege-dropping on standalone | HIGH |
| XWayland may spawn unconditionally | Resource waste if X11 clients are rare | MEDIUM |
| Vulkan support adds complexity | Brittleness vs. stability tradeoff | MEDIUM |
| No async/await pervasive | calloop-based sync, OK but opportunity cost | LOW |

### 1.2 Backend Analysis

#### Udev/DRM Backend (Recommended for Standalone)

**Status:** PARTIALLY IMPLEMENTED
**Confidence:** 75%

**What we know:**
- udev.rs (63KB) suggests full DRM/KMS implementation
- Device management via libseat implies session handling
- Environment variables (WYVERN_DRM_DEVICE, SMITHAY_USE_LEGACY) show device flexibility

**Recommended Actions:**
1. **Verify libseat usage** - Confirm privilege dropping works for non-root seatd
2. **Test TTY switching** - Ensure SIGCONT/SIGSTOP handling is solid
3. **Document device enumeration** - What happens on multi-GPU systems?

#### Winit Backend (Development/Nested)

**Status:** FUNCTIONAL
**Confidence:** 85%

winit.rs (18KB) provides nested execution for development. This is excellent for testing without rebooting.

**Improvement Point:**
- Ensure proper fullscreen negotiation with host compositor
- Verify dpi-awareness for HiDPI nested sessions

#### X11 Backend (Compatibility)

**Status:** MODERN & CORRECT
**Confidence:** 90%

Using x11rb (pure Rust) instead of xcb is the right call. x11.rs (19KB) handles both client role (running as X11 window) and server role (hosting XWayland).

**Recommended Actions:**
1. Verify XWayland lazy loading (only spawn on first X11 client)
2. Ensure proper ICCCM/EWMH compliance for window hints

### 1.3 Rendering Stack

**Status:** AMBITIOUS, NEEDS FOCUS
**Confidence:** 65%

**Current Setup:**
- Default: OpenGL (renderer_gl feature)
- Optional: Vulkan (renderer_vulkan feature)
- Fallback: Pixman software renderer

**Critique:**

Vulkan support for a 2D compositor introduces:
- Complex synchronization (image layout transitions, semaphores)
- Fragmented driver support (especially on Intel legacy iGPUs)
- Minimal performance gain (2D rendering ≠ compute-bound workload)

**Recommendation:**
Mark Vulkan as **experimental/optional**. Default to OpenGL (GLES3) for:
- Driver compatibility (works on Intel, AMD, NVIDIA, ARM)
- Simpler synchronization (fence, single layout per pass)
- Sufficient performance (120+ FPS on modern hardware)

**Action Items:**
1. **Stabilize GL rendering** - Ensure all tests pass with renderer_gl only
2. **Document Vulkan path** - Note limitations and when to use
3. **Benchmark** - Measure FPS on GL vs. Vulkan on diverse hardware

### 1.4 Profiling & Diagnostics

**Status:** GOOD FOUNDATION, INCOMPLETE
**Confidence:** 80%

**Current Strengths:**
- tracing_subscriber with EnvFilter (main.rs line 12)
- tracy profiler support (feature: profile-with-tracy, global allocator)
- puffin_http for frame-time analysis (feature: profile-with-puffin)
- profiling crate for thread annotation

**Gaps:**
1. No structured logging for client lifecycle (map, unmap, focus, damage)
2. Missing performance counters (e.g., frame count, buffer upload time)
3. No documentation on how to use RUST_LOG=smithay=debug in practice

**Improvement Path:**
- Add client state change logging (trace level)
- Log render cycle duration and buffer upload statistics
- Document profiling setup in project CLAUDE.md

### 1.5 Code Organization

**Status:** WELL-STRUCTURED
**Confidence:** 90%

Current module layout:
```
src/
├── main.rs          # Entry point, backend dispatch
├── lib.rs           # Module exports
├── state.rs         # WyvernState, core compositor logic (50KB)
├── input_handler.rs # Keyboard/pointer input (58KB)
├── focus.rs         # Window focus, cycling (22KB)
├── udev.rs          # DRM/KMS backend (63KB)
├── winit.rs         # Nested window backend (18KB)
├── x11.rs           # X11 backend (19KB)
├── render.rs        # Rendering pipeline (7.9KB)
├── drawing.rs       # Drawing primitives (8KB)
├── config.rs        # Configuration loading (2.2KB)
├── cursor.rs        # Cursor management (2.8KB)
└── shell/           # Protocol handlers (likely)
```

**Assessment:**
- **Strengths:** Backends isolated, state centralized, clear separation of concerns
- **Weakness:** state.rs is 50KB; consider extracting window layout logic into state/layout.rs

---

## Part 2: Rust Toolchain & Dependency Modernization

### 2.1 Pinned Rust Toolchain

**Status:** TODO
**Priority:** HIGH

As of 2026-01-01, Rust Nightly continues to evolve. Lock to ensure reproducible builds:

**File: rust-toolchain.toml**
```toml
[toolchain]
channel = "nightly-2026-01-01"
components = ["rust-src", "rust-analyzer", "llvm-tools-preview"]
targets = ["x86_64-unknown-linux-gnu"]
```

**Action Item:** Create rust-toolchain.toml and commit it.

### 2.2 Dependency Audit & Updates

**Status:** IN PROGRESS
**Confidence:** 85%

#### Critical Updates (Must Do)

| Crate | Current | Target | Reason |
|-------|---------|--------|--------|
| smithay | 0.7.0 | 0.7.0+ | Check for bug fixes in 0.7.x series |
| x11rb | 0.13.0 | 0.13.2+ | Protocol definition fixes, recommended upstream |
| winit | ??? | 0.30.12+ | Wayland backend fixes, must be 0.30.x |
| wayland-protocols | 0.32.8 | 0.33.0+ | Protocols evolve; keep fresh |
| calloop | 0.14.3 | 0.14.3 | Stable; no change needed |

**Action Items:**
1. Run `cargo update` and compare semver constraints
2. Test with newer winit (0.30.x)
3. Test wayland-protocols 0.33+ if available
4. Run full test suite after updates

#### Optional Ecosystem Additions (Roadmap)

These are NOT required for v1.0, but should be evaluated for v1.1+:

| Crate | Purpose | Rationale |
|-------|---------|-----------|
| wayland-client | Client libraries for compositor integration | Enable Wyvern to act as a Wayland client in nested mode |
| smithay-clipboard | Clipboard protocol helpers | Implement copy/paste correctly without manual wire handling |
| seatd (via libseat bindings) | Privilege separation | Already in use; document and test |
| env_logger or fern | Structured logging | Complement tracing with rotating logs (OPTIONAL) |

**Action Items:**
1. Audit current smithay_clipboard usage (if any)
2. Verify libseat Rust bindings are in place
3. Document why seatd is (or isn't) used in main.rs

---

## Part 3: Modernization Roadmap (Phased Approach)

### Phase 0: Baseline & Verification (Week 1)

**Goal:** Establish reproducible build and understand current functionality.

**Tasks:**

- [ ] Create rust-toolchain.toml (nightly-2026-01-01)
- [ ] Run `cargo build --all-features` and document any warnings
- [ ] Run `cargo test` and ensure pass rate > 95%
- [ ] Create CLAUDE.md (project-specific) with build/test commands
- [ ] Document current keyboard shortcuts and tiling behavior

**Acceptance Criteria:**
- [ ] Builds reproducibly with pinned toolchain
- [ ] All tests pass (or documented as expected failures)
- [ ] README.md lists prerequisites accurately
- [ ] Existing features (dynamic tiling, keyboard settings) documented

### Phase 1: Dependency Modernization & Stabilization (Week 2-3)

**Goal:** Update to 2026 ecosystem, stabilize GL rendering, confirm session handling.

**Tasks:**

- [ ] Bump smithay to latest 0.7.x
- [ ] Bump x11rb to 0.13.2+
- [ ] Evaluate & update winit to 0.30.12+
- [ ] Test all three backends (udev, winit, x11) after updates
- [ ] Disable/document Vulkan as experimental
- [ ] Verify libseat privilege dropping (non-root seatd)
- [ ] Confirm XWayland lazy loading

**Acceptance Criteria:**
- [ ] All features compile without warnings
- [ ] Udev backend works on test hardware without root (seatd)
- [ ] Winit backend nests correctly
- [ ] X11 backend hosts XWayland on demand
- [ ] benchmark: GL rendering > 60 FPS on modern GPU

### Phase 2: Logging, Tracing & Diagnostics (Week 4-5)

**Goal:** Instrument code for observability; enable debugging without source changes.

**Tasks:**

- [ ] Add trace! logs for client lifecycle (map, unmap, focus, damage)
- [ ] Add performance counters (frame time, buffer uploads)
- [ ] Document RUST_LOG usage for development
- [ ] Add optional metrics export (e.g., Prometheus format)
- [ ] Create diagnostics guide in project CLAUDE.md

**Acceptance Criteria:**
- [ ] `RUST_LOG=wyvern=trace cargo run -- --winit` shows detailed logs
- [ ] Frame timing visible in tracy/puffin output
- [ ] New contributor can diagnose hang/crash with logs
- [ ] Zero impact on release performance

### Phase 3: Code Organization & Refactoring (Week 6-7)

**Goal:** Extract large modules; clarify responsibilities.

**Tasks:**

- [ ] Extract layout logic from state.rs into state/layout.rs
- [ ] Extract shell protocol handling into shell/ subdirectory
- [ ] Review input_handler.rs (58KB) for extraction opportunity
- [ ] Add module-level documentation (//! sections)
- [ ] Ensure all public types have doc comments

**Acceptance Criteria:**
- [ ] No module > 40KB (excluding state.rs if necessary)
- [ ] All public APIs documented
- [ ] build warnings remain zero
- [ ] Tests continue to pass

### Phase 4: Protocol & Spec Compliance (Week 8-10)

**Goal:** Ensure Wayland protocols are correctly implemented; document deviations.

**Tasks:**

- [ ] Audit XDG shell implementation (window focus, resize, move)
- [ ] Verify layer shell for panels/notifications
- [ ] Check data device protocol (copy/paste)
- [ ] Implement missing protocols (e.g., ext-session-lock for screensaver)
- [ ] Document any intentional deviations from spec

**Acceptance Criteria:**
- [ ] XDG shell tests pass (smithay::desktop tests)
- [ ] Can resize/move windows without crashes
- [ ] Layer-shell clients (panels) render correctly
- [ ] Data device (copy/paste) works end-to-end

### Phase 5: Feature Expansion (Week 11+)

**Goal:** Add missing desktop environment features.

**Suggested Enhancements:**

1. **Configuration**
   - [ ] Support ~/.config/wyvern/wyvern.toml for tiling rules
   - [ ] Dynamic workspace switching
   - [ ] Per-workspace layout (some workspaces tile, others float)

2. **Clipboard**
   - [ ] Implement smithay-clipboard helpers
   - [ ] Support primary selection
   - [ ] Support clipboard history (optional)

3. **Input Methods**
   - [ ] IBus/Fcitx5 support for non-Latin input
   - [ ] Compose key handling

4. **Rendering**
   - [ ] Decorations (window frames) via client-side protocols
   - [ ] Blur/shadow effects (Wayland blur protocol)

5. **Output & Hotplug**
   - [ ] Graceful display hotplug (disconnect/reconnect monitors)
   - [ ] Per-output scaling and refresh rate

---

## Part 4: Detailed Technical Decisions

### 4.1 Rendering: GL vs. Vulkan Resolution

**Current Status:** Both enabled, undefined default
**Decision Needed:** Stabilize GL; mark Vulkan experimental

**Analysis:**

**OpenGL (GLES3) Pros:**
- Wide driver support (Intel, AMD, NVIDIA, ARM, etc.)
- Simpler synchronization model (fence + single layout)
- Sufficient for 2D (150+ FPS easy on modern GPU)
- Well-understood debugging (apitrace, frame profilers)

**Vulkan Pros:**
- Explicit synchronization (more control)
- Lower CPU overhead on integrated GPU

**Vulkan Cons:**
- Fragmented driver support (Intel 5th-gen+ only, some AMD gaps)
- Complex image layout transitions, pipeline barriers
- Minimal real-world benefit for 2D compositing
- Harder to debug (few tools compared to OpenGL)

**Recommendation:**

1. **Default:** Use `renderer_gl` (already in features)
2. **Optional:** Keep `renderer_vulkan` in Cargo.toml but mark in docs as experimental
3. **Guidance:** Document when to use Vulkan (e.g., "Vulkan is experimental. Use GL for stability. Vulkan is recommended only if you encounter GPU utilization issues on GL and have Vulkan 1.2+ hardware.")
4. **Testing:** Require GL tests to pass in CI; Vulkan tests optional

**File Changes Needed:**
- README.md: Add section "Rendering Backends" explaining choice
- src/render.rs: Add comment explaining GL default
- Cargo.toml: Uncomment/document renderer_vulkan as optional

### 4.2 Session Management: libseat & TTY Handling

**Current Status:** Partially documented (libseat in dependencies), unclear usage

**Decision Needed:** Clarify libseat integration; ensure non-root support

**What We Know:**
- README.md mentions libseat requirement
- WYVERN_DRM_DEVICE env variable suggests manual device selection
- udev.rs (63KB) implies full device management

**Recommended Actions:**

1. **Verify libseat integration** in udev.rs:
   - Does Wyvern use libseat or direct logind/seatd?
   - What happens when run as non-root without seatd?
   - Document privilege dropping in code comments

2. **Document seatd setup** in README.md:
   ```markdown
   ### Running without root

   Wyvern can run as a regular user via seatd:

   ```bash
   seatd -u "$USER" &
   cargo run -- --tty-udev
   ```
   ```

3. **Add session lifecycle logging** (Phase 2):
   - Log when TTY is acquired/released
   - Log device permissions changes
   - Trace SIGCONT/SIGSTOP handling

### 4.3 XWayland: Lazy Loading & Lifecycle

**Current Status:** Unknown if lazy-loaded
**Decision Needed:** Confirm lazy loading; document startup behavior

**Context:**

XWayland is a bridge allowing X11 applications to run on Wayland. It's heavyweight (~5MB resident, 10+ threads). Many modern compositors lazy-load it (start only when first X11 client connects).

**Recommended Actions:**

1. **Audit x11.rs for XWayland startup:**
   - Is XWayland spawned unconditionally?
   - Or spawned on first X11 client request?
   - Document in code comments

2. **If not lazy-loaded, implement:**
   ```rust
   // Pseudocode: spawn XWayland only when needed
   if should_start_xwayland {
       xwayland = spawn_xwayland(...);
       register_with_compositor();
   }
   ```

3. **Add diagnostics:**
   - Log when XWayland is started
   - Log first X11 client connection
   - Measure startup latency

---

## Part 5: Testing & Validation Strategy

### 5.1 Regression Testing

**Goal:** Ensure updates don't break existing functionality.

**Current Tests:** cargo test (assumed in codebase)

**Recommended Additions:**

1. **Backend integration tests:**
   - Test each backend can start/stop cleanly
   - Test focus switching works
   - Test keyboard input routing

2. **Protocol compliance tests:**
   - XDG shell client behavior
   - Layer shell panel rendering
   - Data device copy/paste

3. **Performance regression tests:**
   - Frame time benchmark (should not increase)
   - Startup time (should not increase)
   - Memory usage (should not exceed baseline)

**Action Items:**
- [ ] Document existing test coverage (Phase 0)
- [ ] Identify missing integration test categories (Phase 1)
- [ ] Implement 3-5 critical regression tests (Phase 2)

### 5.2 Hardware Testing Matrix

**Goal:** Ensure stability across diverse hardware.

**Minimal Matrix for v1.0:**

| Hardware | GPU | Driver | Status |
|----------|-----|--------|--------|
| Desktop (x86_64) | NVIDIA GTX 1060 | nvidia 550+ | REQUIRED |
| Laptop (x86_64) | Intel 5th-gen UHD | i965 | REQUIRED |
| Laptop (x86_64) | AMD Ryzen 5 integrated | AMDGPU | REQUIRED |
| Raspberry Pi 4 | VideoCore VI | vc4 | OPTIONAL |

**Action Items:**
- [ ] Test on at least desktop + laptop configurations
- [ ] Document any driver-specific issues in README

---

## Part 6: Documentation Requirements

### 6.1 Project CLAUDE.md (To Create)

**File:** ./CLAUDE.md (project-specific)

**Contents (sketch):**

```markdown
# Wyvern Compositor - Technical Standards

## Build & Test

- **Toolchain:** nightly-2026-01-01 (see rust-toolchain.toml)
- **Build:** `cargo build --all-features`
- **Test:** `cargo test --all-features`
- **Lint:** `cargo clippy --all-targets --all-features -- -D warnings`

## Backends

- **udev (default):** DRM/KMS on TTY. Requires libseat (seatd or logind).
- **winit:** Nested in X11/Wayland. Dev-friendly.
- **x11:** Runs as X11 client; hosts XWayland.

## Key Modules

- **state.rs:** WyvernState, core compositor logic
- **input_handler.rs:** Keyboard/pointer routing
- **udev.rs / winit.rs / x11.rs:** Backend implementations
- **render.rs:** Rendering pipeline (GL default)
- **shell/:** Wayland protocol handlers

## Standards

- **Logging:** tracing (RUST_LOG=wyvern=trace for debug)
- **Profiling:** tracy (feature: profile-with-tracy)
- **Rendering:** OpenGL GLES3 (Vulkan experimental)
- **Session:** libseat for privilege separation

## Common Issues

- **Won't run without root:** Ensure seatd is running or logind is available
- **Vulkan crashes:** Use GL (WYVERN_NO_VULKAN=1)
- **Nested in Wayland:** Use --x11 backend instead of --winit
```

### 6.2 Architecture Documentation

**File:** ./docs/ARCHITECTURE.md

**Contents (sketch):**

```markdown
# Wyvern Architecture

## High-Level Flow

1. main.rs dispatcher selects backend (udev/winit/x11)
2. Backend initializes smithay State + event loop
3. input_handler.rs routes keyboard/pointer events
4. state.rs manages window layout, focus, damage
5. render.rs submits frame to GPU via smithay

## Backend Abstraction

All backends implement a common pattern:
- Initialize smithay State
- Create event channel (calloop)
- Run event loop (calloop + signal handling)

## Window Layout

WyvernState::windows manages:
- Toplevel surfaces (app windows)
- Layer surfaces (panels, notifications)
- Popups (menus, tooltips)

Layout policy: Dynamic tiling (see focus.rs)

## Rendering Pipeline

1. Collect damaged regions
2. Render each surface
3. Composite layers (background, windows, toplevels, overlays)
4. Submit frame
```

---

## Part 7: Risk Assessment & Mitigation

### 7.1 Risks & Mitigations

| Risk | Impact | Mitigation |
|------|--------|-----------|
| Dependency upgrade breaks smithay integration | HIGH | Test Phase 1 thoroughly on all backends |
| Vulkan instability on some GPUs | MEDIUM | Document Vulkan as experimental; default to GL |
| XWayland startup delays user | LOW | Implement lazy loading (Phase 3) |
| Large modules hard to navigate | LOW | Refactor Phase 3 (extract layout, shell) |
| No performance baseline | MEDIUM | Establish FPS/memory/startup metrics (Phase 2) |

### 7.2 Rollback Strategy

All phases preserve a working state:
- Phase 0: Baseline established; trivial to roll back
- Phase 1: Dependency updates; can revert with `git revert`
- Phase 2: New diagnostics; purely additive, safe to revert
- Phase 3: Refactoring; large risk; test thoroughly before merge

---

## Part 8: Success Criteria & Completion Definition

### Phase 0 Complete When:
- [ ] rust-toolchain.toml committed
- [ ] CLAUDE.md (project-specific) written
- [ ] All existing tests pass
- [ ] README accurate and tested

### Phase 1 Complete When:
- [ ] Deps updated; all features compile
- [ ] All backends tested on real hardware
- [ ] No compiler warnings
- [ ] Performance baseline measured (GL: 60+ FPS)

### Phase 2 Complete When:
- [ ] All trace! logs added to client lifecycle
- [ ] RUST_LOG=trace works and shows expected output
- [ ] Frame timing metrics visible
- [ ] Zero performance regression

### Phase 3 Complete When:
- [ ] No module > 40KB (except state.rs if necessary)
- [ ] All public APIs documented
- [ ] Architecture.md accurate
- [ ] Tests still pass after refactoring

### Full Modernization (Phases 0-4) Complete When:
- [ ] All success criteria above met
- [ ] specs reviewed and deviations documented
- [ ] Performance benchmarks show stability
- [ ] Documentation reflects current code

---

## Part 9: Future Enhancements (Post-Phase 5)

Once modernization is complete, consider:

1. **Performance Tuning**
   - Profile with tracy on diverse hardware
   - Optimize buffer upload paths
   - Consider wgpu abstraction for GL/Vulkan portability

2. **Advanced Features**
   - Multi-workspace support
   - Gesture input (touchpad, touchscreen)
   - Screenshot/screen recording (portal integration)

3. **Developer Experience**
   - Debug UI (overlay showing focus/damage regions)
   - Client debugging protocol
   - Performance profiler integration

4. **Ecosystem Integration**
   - systemd user service for auto-start
   - XDG desktop file
   - Distribution packaging (AUR, Fedora, Debian)

---

## Part 10: Comprehensive Code Analysis Infrastructure

**Status:** NEW SECTION (based on Code-Analysis-Tooling analysis)
**Version:** 1.1 Enhancement
**Date Added:** 2025-12-31

This section synthesizes a 5-layer code analysis pyramid specifically tailored to Wyvern's modernization needs.

### 10.1 The 5-Layer Analysis Pyramid for Wyvern

A complete code analysis infrastructure ensures quality, correctness, and security through layered verification:

```
┌──────────────────────────────────────────────────────────────────┐
│ LAYER 5: FORMAL VERIFICATION (Correctness Proofs)              │
│ Tools: TLA+ (dynamic tiling algorithm), Coq (theorems)         │
│ Purpose: Prove absence of deadlock/race conditions             │
│ Cost: High (human time), Low (once proven)                     │
│ Timeline: Hours/Days (per specification)                       │
│ Application to Wyvern:                                         │
│  - Verify dynamic tiling window layout algorithm               │
│  - Prove focus cycling never deadlocks                         │
│  - Prove seat/input routing correctness                        │
└──────────────────────────────────────────────────────────────────┘

┌──────────────────────────────────────────────────────────────────┐
│ LAYER 4: ABSTRACT INTERPRETATION (Memory Safety)               │
│ Tools: Facebook Infer (separation logic), z3, KLEE (symbolic)  │
│ Purpose: Detect memory leaks, null dereferences, use-after-free│
│ Cost: Moderate (CPU), Scalable (Facebook uses at 1M+ LOC)      │
│ Timeline: Minutes per analysis                                 │
│ Application to Wyvern:                                         │
│  - Detect memory leaks in Smithay FFI boundaries               │
│  - Verify Wayland buffer lifecycle (allocation/deallocation)  │
│  - Check resource cleanup on surface destruction               │
│  - Race condition detection in input handling                  │
└──────────────────────────────────────────────────────────────────┘

┌──────────────────────────────────────────────────────────────────┐
│ LAYER 3: SEMANTIC CODE PATTERNS (Vulnerability Detection)      │
│ Tools: Semgrep (cross-language), Coccinelle (C transformation) │
│ Purpose: Find known vulnerability patterns at scale             │
│ Cost: Low (CPU), Fast, User-configurable                       │
│ Timeline: Seconds (50-150 rules)                               │
│ Application to Wyvern:                                         │
│  - OWASP Top 10 patterns (SQL injection NA, XSS in wayland)   │
│  - CWE Top 25 (buffer overflow, integer overflow, etc.)       │
│  - Custom patterns: unsafe Wayland protocol handling           │
│  - Taint tracking: untrusted client data flow analysis         │
└──────────────────────────────────────────────────────────────────┘

┌──────────────────────────────────────────────────────────────────┐
│ LAYER 2: CODE QUALITY METRICS (Technical Debt Tracking)        │
│ Tools: SonarQube (aggregation), Clippy (Rust linter)          │
│ Purpose: Track complexity, coverage, maintainability over time │
│ Cost: Low (mostly storage), Strategic visibility               │
│ Timeline: 1-2 minutes per scan                                 │
│ Application to Wyvern:                                         │
│  - Complexity of state.rs (50KB), input_handler.rs (58KB)      │
│  - Code duplication across backend implementations             │
│  - Test coverage for each module (target: 80%+)                │
│  - Technical debt trend analysis (historical tracking)         │
│  - Bug density (bugs per KLOC)                                 │
└──────────────────────────────────────────────────────────────────┘

┌──────────────────────────────────────────────────────────────────┐
│ LAYER 1: LINTING & TYPE CHECKING (Fast Feedback)              │
│ Tools: clippy (Rust), shellcheck (shell), cargo check          │
│ Purpose: Catch obvious errors (syntax, undeclared vars, etc.)  │
│ Cost: Very Low, Fast, High noise (false positives)             │
│ Timeline: Fast (< 1 second per invocation)                    │
│ Application to Wyvern:                                         │
│  - Clippy warnings as errors (-D warnings in CI)               │
│  - Cargo fmt enforcement (formatting consistency)              │
│  - Type checking via cargo check (fast feedback loop)          │
│  - Deny deprecated APIs in Smithay usage                       │
└──────────────────────────────────────────────────────────────────┘
```

### 10.2 Specific Tools & Integration Plan for Wyvern

#### Layer 5: TLA+ for Dynamic Tiling Algorithm Verification

**Status:** RECOMMENDED (New)
**Priority:** MEDIUM (Phase 5+, after stabilization)

**Why TLA+ for Wyvern?**

The dynamic tiling algorithm is the heart of Wyvern. A bug in tiling can:
- Cause windows to disappear or overlap unintentionally
- Create visual deadlocks (infinite loops in layout calculation)
- Cause focus cycling to fail or hang

**Application Strategy:**

```tla
---- FILE: Tiling.tla ----
MODULE Tiling
EXTENDS Naturals, Sequences

VARIABLE
  windows,          \* Set of active windows
  layout,           \* Current layout (split tree)
  focusedWindow,    \* Currently focused window
  focusedWorkspace  \* Current workspace

---- Initial State: Single window
Init == /\ windows = {w1}
        /\ layout = w1
        /\ focusedWindow = w1
        /\ focusedWorkspace = "ws1"

---- Next: Add/remove windows, cycle focus, change layout
Next == \/ AddWindow
        \/ RemoveWindow
        \/ CycleFocus
        \/ SplitHorizontal
        \/ SplitVertical

---- Invariant: Focus is always on an existing window
FocusInvariant == focusedWindow \in windows

---- Liveness: Focus cycling always terminates
FocusCyclingTerminates == <>[](\A w \in windows : CanReachViaFocus(w))

Spec == Init /\ [][Next]_<<windows, layout, focusedWindow>>

THEOREM Spec => []FocusInvariant  \* Prove: focus never orphaned
THEOREM Spec => FocusCyclingsTerminates  \* Prove: cycle terminates
```

**Verification Process:**
```bash
# 1. Write TLA+ specification of tiling algorithm
vim Wyvern_Tiling.tla

# 2. Run TLC model checker
tlc Wyvern_Tiling.tla -depth 1000 -workers 4

# 3. If errors found, fix spec or algorithm
# 4. Iterate until: Diameter OK, Invariants hold, Liveness proven
```

**Integration Points:**
- Model checking runs in CI (after Phase 4)
- If tiling algorithm changes, spec updated before implementation
- Spec becomes living documentation of tiling guarantees

#### Layer 4: Facebook Infer for Memory Safety Analysis

**Status:** RECOMMENDED (Phase 2, after dependency updates)
**Priority:** HIGH (critical for FFI boundaries)
**Installation:** `sudo pacman -U ~/pkgbuilds/infer-static/infer-static-1.1.0-1-x86_64.pkg.tar.zst`

**Why Infer for Wyvern?**

Wyvern has FFI boundaries:
- Smithay (Rust) ↔ Wayland C protocol
- Smithay ↔ DRM/KMS C libraries (libdrm, libgbm)
- Smithay ↔ XWayland (X11 C client protocol)

Infer detects:
- Memory leaks (unclosed file handles, allocated buffers)
- Use-after-free (accessing freed Wayland surfaces)
- Null dereferences (uninitialized protocol state)
- Race conditions (concurrent surface access)

**Application Strategy:**

```bash
# 1. Analyze entire Wyvern project
infer run -- cargo build --release 2>&1 | tee infer-build.log

# 2. Review findings
cat infer-out/report.txt | grep -E "ERROR|WARNING"
firefox infer-out/report.html

# 3. For each finding:
#    - False positive? Document why (--infer-ignore-exceptions)
#    - Real leak? Fix in code
#    - Design issue? Update CLAUDE.md with pattern

# 4. Integrate into CI/CD (see section 10.4)
```

**Expected Findings & Handling:**

| Finding Type | Expected | Example | Action |
|-------|----------|---------|--------|
| Memory Leak | 2-5 | Wayland buffer not deallocated on error path | FIX |
| Use-After-Free | 0-1 | Surface accessed after protocol destruction | FIX |
| Null Dereference | 1-3 | Uninitialized input_handler state | FIX |
| Race Condition | 0-2 | Concurrent focus changes | FIX/DOCUMENT |
| Resource Leak | 3-5 | File descriptor from DRM device | FIX |

**Integration Workflow:**

```bash
# Phase 2: Run once to establish baseline
infer run -- cargo build
BASELINE=$(wc -l < infer-out/report.txt)
# Store baseline in CI/CD config

# Ongoing: Block merges if new findings > baseline
infer run -- cargo build
CURRENT=$(wc -l < infer-out/report.txt)
if [ "$CURRENT" -gt "$BASELINE" ]; then
  echo "❌ NEW MEMORY SAFETY ISSUES DETECTED"
  exit 1
fi
```

#### Layer 3: Semgrep for Security & Pattern Detection

**Status:** RECOMMENDED (Phase 2, immediate installation)
**Priority:** MEDIUM (security baseline)
**Installation:** `yay -S semgrep`

**Why Semgrep for Wyvern?**

Wyvern processes untrusted client data:
- Wayland protocol messages from clients
- X11 window hints and properties
- Input events (keyboard/pointer coordinates)

Semgrep can detect:
- Malformed protocol handling (incomplete validation)
- Integer overflows (screen coordinates, buffer sizes)
- Buffer overflows (string handling)
- Logic errors (taint tracking for client data)

**Custom Ruleset for Wyvern:**

```yaml
---- FILE: .semgrep.yml ----
rules:
  - id: untrusted_wayland_buffer_size
    pattern-either:
      - pattern: |
          buffer_size = client_message.width * client_message.height
          # Must validate: width/height < MAX_RESOLUTION
      - pattern: malloc(untrusted_size)
    message: Buffer allocation from untrusted client data without bounds check
    severity: WARNING
    languages: [rust]

  - id: invalid_focus_transition
    pattern: |
      focus_window(client_provided_id)
      # Without verifying client_provided_id is valid window
    message: Potential focus hijack; validate window ownership
    severity: ERROR
    languages: [rust]

  - id: missing_wayland_protocol_validation
    pattern: |
      match wayland_message {
        XDG_SHELL_REQUEST => { /* handler */ }
        // Missing default case for unknown requests
      }
    message: Incomplete protocol state machine; add exhaustive match
    severity: WARNING
    languages: [rust]
```

**Integration:**

```bash
# Run before each commit
semgrep --config=.semgrep.yml --error src/

# Run in CI with public rulesets
semgrep --config=p/owasp-top-ten --config=p/security-audit src/

# Custom org ruleset (if using Semgrep Cloud)
semgrep --config=p/<org-slug>/wyvern-compositor src/
```

#### Layer 2: SonarQube for Quality Tracking

**Status:** RECOMMENDED (Phase 2-3)
**Priority:** MEDIUM (long-term visibility)
**Installation:** `sudo pacman -U ~/pkgbuilds/sonarqube-server/sonarqube-server-10.6-2-x86_64.pkg.tar.zst`

**Why SonarQube for Wyvern?**

Tracks:
- Code complexity (cyclomatic, cognitive)
- Test coverage (% of lines executed)
- Duplicate code blocks
- Technical debt estimate (in person-days)
- Bug density trends over time

**Setup:**

```bash
# 1. Install and start
sonarqube-setup
systemctl --user start sonarqube-server

# 2. Generate token
# Navigate to http://localhost:9000 → Administration → Security → User Tokens

# 3. Create sonar-project.properties
cat > sonar-project.properties << 'EOF'
sonar.projectKey=wyvern
sonar.projectName=Wyvern Compositor
sonar.projectVersion=$(git describe --tags)
sonar.sources=src
sonar.tests=tests
sonar.exclusions=**/generated/**,**/migrations/**
sonar.coverage.exclusions=**/test/**,**/benches/**

# Rust-specific settings
sonar.rust.clippy.reportPath=clippy-report.json
sonar.rust.coverage.reportPath=coverage.xml
EOF

# 4. Run scanner
sonar-scanner -Dsonar.login=squ_XXXXX

# 5. View dashboard
firefox http://localhost:9000/dashboard?id=wyvern
```

**Metrics to Track:**

| Metric | Target | Current | Action |
|--------|--------|---------|--------|
| Test Coverage | 80%+ | TBD | Increase in Phase 4 |
| Complexity (state.rs) | < 15 | TBD | Refactor large functions |
| Duplicates | < 3% | TBD | Extract common patterns |
| Tech Debt | < 5 days | TBD | Schedule refactoring |
| Bugs Found | Decreasing trend | Baseline phase 2 | Monitor over time |

#### Layer 1: Clippy + Cargo for Fast Feedback

**Status:** IN USE (already integrated)
**Priority:** HIGH (first-line defense)

**Current Setup:**
- `cargo clippy --all-targets --all-features -- -D warnings` ✅ Already in use (lib.rs line 1)
- `cargo fmt` for formatting consistency ✅
- `cargo test` for unit tests ✅

**Enhancements Needed:**

```bash
# 1. Add to CI/CD (see section 10.4)
cargo clippy --all-targets --all-features -- -D warnings

# 2. Add deny crate for supply chain security
cat > deny.toml << 'EOF'
[advisories]
db-path = "~/.cargo/advisory-db"
vulnerability = "deny"
unmaintained = "warn"
unsound = "warn"

[licenses]
allow = [
  "MIT",
  "Apache-2.0",
  "Apache-2.0 OR MIT",
]
EOF

# 3. Run deny before merge
cargo deny check

# 4. Add SARIF output for CI/CD integration
cargo clippy --message-format=json > clippy-report.json
```

### 10.3 CI/CD Pipeline Integration

**Status:** RECOMMENDED (Phase 2-3)
**File to Create:** `.github/workflows/code-analysis.yml` (GitHub Actions)

```yaml
name: Code Analysis Pipeline

on: [push, pull_request]

jobs:
  # Layer 1: Fast Feedback (1 min)
  lint:
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v3
      - uses: dtolnay/rust-toolchain@stable
      - run: cargo clippy --all-targets --all-features -- -D warnings
      - run: cargo fmt --check
      - run: cargo deny check

  # Layer 3: Security Patterns (30 sec)
  semgrep:
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v3
      - uses: returntocorp/semgrep-action@v1
        with:
          config: |
            p/owasp-top-ten
            p/security-audit
            .semgrep.yml

  # Layer 4: Memory Safety (5 min) - Rust only, build on Linux
  infer:
    runs-on: ubuntu-latest
    if: contains(github.event.head_commit.message, '[infer]') || github.event_name == 'push'
    steps:
      - uses: actions/checkout@v3
      - uses: dtolnay/rust-toolchain@stable
      - run: cargo install infer || apt-get install -y infer
      - run: infer run -- cargo build --all-features
      - uses: actions/upload-artifact@v3
        with:
          name: infer-report
          path: infer-out/report.html

  # Layer 2: Quality Aggregation (2 min)
  sonarqube:
    runs-on: ubuntu-latest
    if: github.event_name == 'push' && github.ref == 'refs/heads/main'
    steps:
      - uses: actions/checkout@v3
      - run: cargo clippy --message-format=json > clippy.json || true
      - run: cargo tarpaulin --out Xml --output-dir coverage
      - uses: SonarSource/sonarqube-scan-action@v2
        env:
          SONAR_HOST_URL: https://sonarqube.example.com
          SONAR_LOGIN: ${{ secrets.SONAR_TOKEN }}

  # Test Suite
  test:
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v3
      - uses: dtolnay/rust-toolchain@stable
      - run: cargo test --all-features
      - run: cargo tarpaulin --out Xml
      - uses: codecov/codecov-action@v3

  # Layer 5: Formal Verification (Manual, on demand)
  # Note: TLA+ requires GUI/manual verification; can't easily CI
  # Recommendation: Run locally, commit .tla specs to repo
  # CD could verify .tla specs parse: tlc -check <spec>
```

### 10.4 Measurement & Quality Gates

**Status:** RECOMMENDED (Phase 3)
**Purpose:** Define success criteria, block low-quality merges

**Quality Gate Definition:**

```yaml
# File: sonar-quality-gate.yml (SonarQube configuration)

# 1. CORRECTNESS
- metric: reliability_rating
  condition: A  # A=0 bugs, B=1-5, C=6-10, D=11-20, E=21+

- metric: security_rating
  condition: A  # No security vulnerabilities

- metric: coverage
  condition: '>80'  # At least 80% coverage

# 2. MAINTAINABILITY
- metric: sqale_rating
  condition: A  # Technical debt ratio < 5%

- metric: cognitive_complexity
  condition: '<10'  # Avg cyclomatic complexity per function

- metric: duplicated_lines
  condition: '<3'  # Less than 3% duplication

# 3. CUSTOM FOR WYVERN
- metric: file_complexity  # state.rs shouldn't exceed 40KB
  condition: '<2000 lines'  # Max file size

# Block merge if ANY gate fails
allow_failures: false
```

**Measurement Dashboard (Track Monthly):**

```
Week 1:  Phase 0 - Baseline metrics established
  ├─ Code Complexity: state.rs = 42 (HIGH), input_handler.rs = 38
  ├─ Coverage: 45% (LOW, target 80%)
  ├─ Tech Debt: 12 days (MEDIUM, target < 5 days)
  └─ Bugs Found: 0 (baseline for Infer)

Week 4:  Phase 1 Complete
  ├─ Deps updated: smithay 0.7.0 → 0.7.2, x11rb 0.13.0 → 0.13.2
  ├─ Coverage: 52% (improving)
  ├─ Tech Debt: 10 days (improving)
  └─ Bugs Found: 3 memory issues (Infer), all fixed

Week 8:  Phase 2 Complete
  ├─ Tracing added to client lifecycle
  ├─ Coverage: 68% (near target)
  ├─ Tech Debt: 6 days (on track)
  └─ Semgrep: 152 OWASP rules checked, 0 failures
```

### 10.5 Security & Correctness Verification Strategy

**Status:** NEW (comprehensive security focus)
**Priority:** HIGH (compositor handles untrusted input)

**Threat Model for Wyvern:**

1. **Malicious Wayland Client**
   - Send oversized buffers (DOS)
   - Provide invalid window coordinates (crash)
   - Request invalid operations (deadlock)

2. **X11 Application via XWayland**
   - Send malformed X11 protocol messages
   - Request forbidden operations (bypass restrictions)

3. **Local Privilege Escalation**
   - Exploit DRM device access
   - Exploit session management bugs

**Verification Approach:**

```bash
# 1. Fuzzing (detect crashes)
cargo fuzz target=wayland_message_parser -- -max_len=10000

# 2. Protocol Validation (automated)
semgrep --config=.semgrep.yml --error src/shell/ src/state.rs

# 3. Formal Verification (prove correctness)
# For critical paths (focus cycling, window closing):
tlc Wyvern_Focus_Protocol.tla -depth 500

# 4. Memory Safety (static + runtime)
infer run -- cargo build
cargo miri test  # Runtime verification on unsafe blocks
```

### 10.6 Performance Analysis & Profiling Integration

**Status:** RECOMMENDED (Phase 2-3, profiling setup)
**Tools:** perf, flamegraph, tracy (already in codebase)

**Measurement Framework:**

```bash
# Baseline Metrics (Phase 0)
perf stat -e cycles,instructions,cache-misses cargo run -- --winit < test_events.log
# Output: ~2B cycles, 5B instructions, 50M cache-misses per frame

# Profiling (Phase 2)
flamegraph --bin wyvern -- --winit < test_events.log
# Output: Identify hot functions (> 10% CPU time)
# Expected: render() > input_handler() > focus.rs

# Tracy Integration (already enabled via feature: profile-with-tracy)
TRACY_ENABLE=1 cargo run --features profile-with-tracy -- --winit
# Open http://localhost:8086 in browser (Tracy UI)
# Monitor: Frame time, GPU stall, memory allocations

# Regression Detection
# Commit baseline measurements to repo
# CI checks if new measurements exceed +10% threshold
```

---

## Appendix: Referenced Files & Links

### Key Source Files
- **src/main.rs** - Entry point, backend dispatcher
- **src/state.rs** - Core WyvernState, window management (50KB)
- **src/input_handler.rs** - Keyboard/pointer routing (58KB)
- **src/udev.rs** - DRM/KMS backend (63KB)
- **src/winit.rs** - Nested window backend (18KB)
- **src/x11.rs** - X11 backend (19KB)
- **src/render.rs** - Rendering pipeline (7.9KB)

### External References
- [Smithay Documentation](https://docs.rs/smithay)
- [Wayland Protocol Spec](https://wayland.freedesktop.org/)
- [XDG Shell Protocol](https://wayland.freedesktop.org/xdg-shell/)
- [Libseat Documentation](https://git.sr.ht/~kennylevinsen/seatd)

---

## Document Maintenance

This document is a living record. Update it:
- **After completing a phase:** Tick checkboxes, note date
- **When design decisions change:** Update rationale with new date
- **When new risks emerge:** Add to risk table with mitigation
- **Monthly:** Review "Future Enhancements" and resurface if priorities shift

**Last Updated:** 2025-12-31
**Next Review:** 2026-01-28 (Phase 0 completion target)
