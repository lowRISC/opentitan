# Implementation Plan: Refactoring `opentitanlib` Monolith

This document outlines the plan to refactor the large Rust crate `//sw/host/opentitanlib` into smaller, logical crates, maintain backward compatibility via a super-crate, and feature-gate hardware transports.

## Goal
1.  **Modularization**: Break down `opentitanlib` into smaller crates with clear responsibilities.
2.  **Cycle Resolution**: Resolve existing circular dependencies (e.g., between `transport`, `bootstrap`, `app`, and `io`).
3.  **Feature Gating**: Allow compiling `opentitanlib` with a subset of hardware transports (e.g., to reduce dependencies and binary size).
4.  **Backward Compatibility**: Keep `opentitanlib` as a "super-crate" that re-exports all public items from the sub-crates, ensuring no breakage for existing tools and tests.
5.  **Testability**: Ensure tests can be run and pass at each step.

---

## Current Architecture & Dependency Analysis

The monolithic `opentitanlib` crate currently has the following internal structure:
-   `util`: Low-level utilities (file, status, presentation, vmem, etc.).
-   `crypto`: Cryptographic helpers.
-   `io`: Hardware Abstraction Layer (HAL) interfaces (`GpioPin`, `Uart`, `Spi`, `I2c`, `JtagChain`, etc.) and command-line parameters (`UartParams`, `SpiParams`, etc.).
-   `transport`: Core `Transport` traits, capabilities, and concrete implementations (`ftdi`, `hyperdebug`, `chip_whisperer`, etc.).
-   `chip` / `dif`: Chip register definitions and interface wrappers.
-   `debug`: Debugging utilities (DMI, OpenOCD interface).
-   `bootstrap` / `rescue` / `spiflash` / `otp` / `ownership` / `tpm`: Protocol implementations.
-   `app`: Top-level application context, config file parsing, and `TransportWrapper`.
-   `backend`: Factory to instantiate concrete transports based on CLI options.
-   `test_utils`: Helpers for system-level testing.

### Identified Cycles (Circular Dependencies)

1.  **`io` <-> `app` (via `Params::create`)**
    -   `io/uart.rs` defines `UartParams` which has a `create` method taking `&TransportWrapper` (defined in `app`).
    -   Similarly, `SpiParams`, `I2cParams`, and `JtagParams` in `io` have `create` methods taking `&TransportWrapper`.
    -   `app` naturally depends on `io` because `TransportWrapper` exposes and wraps `io` traits.

2.  **`transport` <-> `bootstrap` (via `ProxyOps::bootstrap`)**
    -   `transport` core defines `ProxyOps` trait (used by proxy client transport).
    -   `ProxyOps::bootstrap` takes `&BootstrapOptions` (defined in `bootstrap`).
    -   `bootstrap` depends on `transport` core (for `Capability`, `ProgressIndicator`, etc.) and `app` (`TransportWrapper`).

3.  **`debug` -> `test_utils` -> `backend` -> `debug`**
    -   `debug/dmi.rs` uses `test_utils::poll::poll_until`.
    -   `test_utils/init.rs` uses `backend::create` to initialize target under test.
    -   `backend` depends on all transports, some of which might use `debug` (though currently transports seem clean, but this is a potential issue).
    -   Specifically, `debug/openocd.rs` uses `dif/lc_ctrl` and `io/jtag`.

---

## Target Architecture (DAG)

We propose splitting the monolith into the following sub-crates, forming a clean Directed Acyclic Graph (DAG):

```mermaid
graph TD
    core[opentitanlib_core]
    chip[opentitanlib_chip]
    debug[opentitanlib_debug]
    app[opentitanlib_app]
    transports[opentitanlib_transports]
    protocols[opentitanlib_protocols]
    backend[opentitanlib_backend]
    test_utils[opentitanlib_test_utils]
    super[opentitanlib super-crate]
    
    chip --> core
    debug --> chip
    debug --> core
    app --> debug
    app --> core
    
    transports --> core
    
    protocols --> app
    protocols --> core
    
    backend --> transports
    backend --> app
    backend --> core
    
    test_utils --> backend
    test_utils --> protocols
    
    super --> backend
    super --> test_utils
    super --> protocols
    super --> app
    super --> debug
    super --> chip
    super --> core
```

### Crate Responsibilities

1.  **`opentitanlib_core`**:
    *   `util/**` (excluding `test_utils` candidates, move `poll_until` here).
    *   `crypto/**`.
    *   `io/**` (Interfaces only: `GpioPin`, `Uart`, `Spi`, etc.).
    *   `io/capabilities.rs` (Moved from `transport/mod.rs`).
    *   `io/errors.rs` (Moved from `transport/errors.rs`).
    *   `io/bootstrap_types.rs` (Data structures: `BootstrapOptions`, `BootstrapProtocol`).
    *   `transport/mod.rs` (Core `Transport` and `ProxyOps` traits only).
2.  **`opentitanlib_chip`**:
    *   `chip/**`.
    *   `dif/**`.
3.  **`opentitanlib_debug`**:
    *   `debug/**` (DMI, OpenOCD, ELF debugger).
4.  **`opentitanlib_app`**:
    *   `app/**` (`TransportWrapper`, Config parsing).
    *   `app/params.rs` (New: implementation of `create` methods for `Params` structs).
5.  **`opentitanlib_transports`**:
    *   `transport/ftdi/**`, `transport/hyperdebug/**`, etc. (Concrete implementations).
    *   Feature gates will be defined here to conditionally compile individual transports.
6.  **`opentitanlib_protocols`**:
    *   `bootstrap/**`, `rescue/**`, `spiflash/**`, `otp/**`, `ownership/**`, `tpm/**`.
7.  **`opentitanlib_backend`**:
    *   `backend/**` (Instantiates concrete transports, maps names to implementations).
8.  **`opentitanlib_test_utils`**:
    *   `test_utils/**` (excluding `poll_until` which moves to `core`).
9.  **`opentitanlib` (Super-crate)**:
    *   No local logic. Re-exports all public items from the sub-crates to maintain 100% backward compatibility.

---

## Detailed Refactoring Steps

### Phase 1: Cycle Resolution (In-Place)
Perform all refactorings within the current monolithic crate to ensure it compiles and passes tests at each step.

#### Step 1.1: Move `poll_until` to `util`
-   Create [src/util/poll.rs](file:///usr/local/google/home/cfrantz/opentitan/ottool/sw/host/opentitanlib/src/util/poll.rs) and move `poll_until` from [src/test_utils/poll.rs](file:///usr/local/google/home/cfrantz/opentitan/ottool/sw/host/opentitanlib/src/test_utils/poll.rs) to it.
-   Update `src/debug/dmi.rs` to import from `crate::util::poll::poll_until`.
-   Update `test_utils` submodules to import from `crate::util::poll::poll_until`.
-   *Verification*: `blaze test //sw/host/opentitanlib:opentitanlib_test`

#### Step 1.2: Move `Capability` and `Capabilities` to `io`
-   Create [src/io/capabilities.rs](file:///usr/local/google/home/cfrantz/opentitan/ottool/sw/host/opentitanlib/src/io/capabilities.rs).
-   Move `Capability`, `Capabilities`, and `NeededCapabilities` from [src/transport/mod.rs](file:///usr/local/google/home/cfrantz/opentitan/ottool/sw/host/opentitanlib/src/transport/mod.rs) to it.
-   Re-export them in `src/io/mod.rs`.
-   Re-export them in `src/transport/mod.rs` (for backward compatibility).
-   Update internal imports to use `crate::io::capabilities::Capability` (or `crate::io::Capability`).
-   *Verification*: `blaze test //sw/host/opentitanlib:opentitanlib_test`

#### Step 1.3: Move `TransportError` and `TransportInterfaceType` to `io`
-   Create [src/io/errors.rs](file:///usr/local/google/home/cfrantz/opentitan/ottool/sw/host/opentitanlib/src/io/errors.rs).
-   Move contents of [src/transport/errors.rs](file:///usr/local/google/home/cfrantz/opentitan/ottool/sw/host/opentitanlib/src/transport/errors.rs) to it.
-   Update it to import `Capability` from `crate::io::capabilities::Capability`.
-   Delete `src/transport/errors.rs`.
-   Re-export `TransportError` and `TransportInterfaceType` in `src/io/mod.rs`.
-   Re-export them in `src/transport/mod.rs` (for backward compatibility).
-   Update imports in `src/io/*.rs` and other files to use local errors (or `crate::io::TransportError`).
-   *Verification*: `blaze test //sw/host/opentitanlib:opentitanlib_test`

#### Step 1.4: Move `BootstrapOptions` and `BootstrapProtocol` to `io`
-   Create [src/io/bootstrap_types.rs](file:///usr/local/google/home/cfrantz/opentitan/ottool/sw/host/opentitanlib/src/io/bootstrap_types.rs).
-   Move `BootstrapOptions` and `BootstrapProtocol` from [src/bootstrap/mod.rs](file:///usr/local/google/home/cfrantz/opentitan/ottool/sw/host/opentitanlib/src/bootstrap/mod.rs) to it.
-   Re-export them in `src/io/mod.rs`.
-   Re-export them in `src/bootstrap/mod.rs` (for backward compatibility).
-   Update `ProxyOps` in `src/transport/mod.rs` to import `BootstrapOptions` from `crate::io`.
-   *Verification*: `blaze test //sw/host/opentitanlib:opentitanlib_test`

#### Step 1.5: Refactor `Params` instantiation to `TransportWrapper`
-   Remove `create` methods from:
    -   `UartParams` in [src/io/uart.rs](file:///usr/local/google/home/cfrantz/opentitan/ottool/sw/host/opentitanlib/src/io/uart.rs)
    -   `SpiParams` in [src/io/spi.rs](file:///usr/local/google/home/cfrantz/opentitan/ottool/sw/host/opentitanlib/src/io/spi.rs)
    -   `I2cParams` in [src/io/i2c.rs](file:///usr/local/google/home/cfrantz/opentitan/ottool/sw/host/opentitanlib/src/io/i2c.rs)
    -   `JtagParams` in [src/io/jtag.rs](file:///usr/local/google/home/cfrantz/opentitan/ottool/sw/host/opentitanlib/src/io/jtag.rs)
-   Remove `use crate::app::TransportWrapper;` from these files.
-   In [src/app/mod.rs](file:///usr/local/google/home/cfrantz/opentitan/ottool/sw/host/opentitanlib/src/app/mod.rs), implement these methods on `TransportWrapper`:
    ```rust
    impl TransportWrapper {
        pub fn create_uart(&self, params: &UartParams) -> Result<Rc<dyn Uart>> { ... }
        pub fn create_spi(&self, params: &SpiParams, default_instance: &str) -> Result<Rc<dyn Target>> { ... }
        pub fn create_i2c(&self, params: &I2cParams, default_instance: &str) -> Result<Rc<dyn Bus>> { ... }
        pub fn create_jtag<'t>(&'t self, params: &JtagParams) -> Result<Box<dyn JtagChain + 't>> { ... }
    }
    ```
-   Update callers:
    -   `src/bootstrap/primitive.rs`: `container.spi_params.create(transport, "BOOTSTRAP")?` -> `transport.create_spi(&container.spi_params, "BOOTSTRAP")?`
    -   `src/bootstrap/eeprom.rs`: same.
    -   `src/bootstrap/legacy.rs`: same.
    -   `src/bootstrap/legacy_rescue.rs`: `container.uart_params.create(transport)?` -> `transport.create_uart(&container.uart_params)?`
    -   `src/test_utils/init.rs`: `self.bootstrap.options.uart_params.create(&transport)?` -> `transport.create_uart(&self.bootstrap.options.uart_params)?`
-   *Verification*: `blaze test //sw/host/opentitanlib:opentitanlib_test` and `blaze build //sw/host/opentitantool`.

At this point, `src/io` should have **ZERO** internal dependencies on `src/app` or `src/transport`!

---

### Phase 2: Define Sub-Crates (In-Place)
Before moving files, we can define separate `rust_library` targets in `sw/host/opentitanlib/BUILD` to ensure boundaries are correct and dependencies are properly declared.

We will define:
1.  `opentitanlib_core` (sources under `src/{util, crypto, io}`, and core parts of `src/transport/mod.rs`)
2.  `opentitanlib_chip` (sources under `src/{chip, dif}`)
3.  `opentitanlib_debug` (sources under `src/debug`)
4.  `opentitanlib_app` (sources under `src/app`)
5.  `opentitanlib_transports` (sources under `src/transport/{ftdi, hyperdebug, ...}`)
6.  `opentitanlib_protocols` (sources under `src/{bootstrap, rescue, ...}`)
7.  `opentitanlib_backend` (sources under `src/backend`)
8.  `opentitanlib_test_utils` (sources under `src/test_utils`)

#### Step 2.1: Adjust `src/transport/mod.rs` for core vs transports
-   `src/transport/mod.rs` currently defines core traits AND registers submodules for concrete transports.
-   To split them, we should keep the core traits in `opentitanlib_core`, but move concrete submodule declarations (e.g. `pub mod ftdi;`) to a separate file that will be part of `opentitanlib_transports`.
-   Actually, in Rust, a crate can only extend its own modules.
-   If `opentitanlib_transports` is a separate crate, it will have its own `lib.rs` which can define:
    ```rust
    pub mod ftdi;
    pub mod hyperdebug;
    // ...
    ```
    And these will be accessed as `opentitanlib_transports::ftdi::...` instead of `opentitanlib::transport::ftdi::...`.
-   To maintain backward compatibility in `opentitanlib` (super-crate), we can re-export them:
    ```rust
    // In sw/host/opentitanlib/src/lib.rs (super-crate)
    pub mod transport {
        pub use opentitanlib_core::transport::*; // Core traits
        pub use opentitanlib_transports::ftdi; // Concrete transport
        pub use opentitanlib_transports::hyperdebug;
        // ...
    }
    ```
    This is beautiful because it preserves the exact same import paths for users!

#### Step 2.2: Define Bazel targets and compile them
-   Update `sw/host/opentitanlib/BUILD` to define the sub-libraries.
-   We will need to change `crate::` imports inside the sub-crates to use the correct external crate names (e.g., in `src/app/mod.rs`, change `use crate::io::...` to `use opentitanlib_core::io::...`).
-   This will be done systematically:
    -   `core` can use `crate::` for `util`, `crypto`, `io`, `transport` (core).
    -   `chip` must use `opentitanlib_core::` for core imports.
    -   `debug` must use `opentitanlib_core::` and `opentitanlib_chip::`.
    -   `app` must use `opentitanlib_core::`, `opentitanlib_chip::`, `opentitanlib_debug::`.
    -   `transports` must use `opentitanlib_core::` (concrete transports only depend on core).
    -   `protocols` must use `opentitanlib_core::`, `opentitanlib_app::`.
    -   `backend` must use `opentitanlib_core::`, `opentitanlib_app::`, `opentitanlib_transports::`.
    -   `test_utils` must use `opentitanlib_core::`, `opentitanlib_app::`, `opentitanlib_protocols::`, `opentitanlib_backend::`.
-   *Verification*: Build each sub-library individually.

---

### Phase 3: File Organization (Optional but Recommended)
Move the files into separate subdirectories to reflect the crate boundaries.

-   `sw/host/opentitanlib/core/src/...`
-   `sw/host/opentitanlib/chip/src/...`
-   `sw/host/opentitanlib/debug/src/...`
-   `sw/host/opentitanlib/app/src/...`
-   `sw/host/opentitanlib/transports/src/...`
-   `sw/host/opentitanlib/protocols/src/...`
-   `sw/host/opentitanlib/backend/src/...`
-   `sw/host/opentitanlib/test_utils/src/...`
-   Update `BUILD` files to point to the new paths.

---

### Phase 4: Feature Gating Transports
Implement Cargo features to allow conditional compilation of hardware transports.

-   In `opentitanlib_transports` crate (or `opentitanlib_backend` which is the factory):
    -   Define features in `BUILD` (using `crate_features`) and Rust code:
        -   `ftdi`
        -   `hyperdebug`
        -   `chip_whisperer`
        -   `verilator`
        -   `qemu`
        -   `proxy`
    -   In `opentitanlib_transports/src/lib.rs`:
        ```rust
        #[cfg(feature = "ftdi")]
        pub mod ftdi;
        #[cfg(feature = "hyperdebug")]
        pub mod hyperdebug;
        // ...
        ```
    -   In `opentitanlib_backend/src/mod.rs` (the factory):
        -   Feature-gate the imports and match arms:
            ```rust
            #[cfg(feature = "ftdi")]
            use opentitanlib_transports::ftdi;
            
            pub fn create(args: &BackendOpts) -> Result<TransportWrapper> {
                // ...
                let (backend, default_conf) = match env.get_interface() {
                    // ...
                    #[cfg(feature = "ftdi")]
                    "ftdi" => (
                        ftdi::create::<Ft4232hq>(args)?,
                        Some(Path::new("/__builtin__/opentitan_ftdi_voyager.json")),
                    ),
                    // ...
                    _ => return Err(Error::UnknownInterface(interface.to_string()).into()),
                };
                // ...
            }
            ```
-   In the super-crate `opentitanlib`:
    -   Propagate these features:
        ```toml
        [features]
        default = ["ftdi", "hyperdebug", "chip_whisperer", "verilator", "qemu", "proxy"]
        ftdi = ["opentitanlib_transports/ftdi", "opentitanlib_backend/ftdi"]
        # ...
        ```
        (Or equivalent Bazel configuration).

---

## Testing & Verification Plan

At each step, we must ensure that the codebase remains buildable and all tests pass.

### Unit Tests
Run unit tests of `opentitanlib`:
```bash
blaze test //sw/host/opentitanlib:opentitanlib_test
```
When split, we will have separate tests:
```bash
blaze test //sw/host/opentitanlib/core:core_test
blaze test //sw/host/opentitanlib/app:app_test
# ...
```

### Integration Tests
Verify that external tools (like `opentitantool`) still compile and run correctly:
```bash
blaze build //sw/host/opentitantool
```
Run `opentitantool` tests:
```bash
blaze test //sw/host/opentitantool:opentitantool_test
```
Run system end-to-end tests (which use `test_utils` extensively):
```bash
blaze test //sw/host/tests/chip/gpio:gpio_intr
blaze test //sw/host/tests/chip/flash_ctrl:flash_ctrl
# (and other tests listed in dependency analysis)
```
