# Refactoring Progress: `opentitanlib` Modularization

This file tracks the progress of the refactoring of `sw/host/opentitanlib` monolith into smaller crates.

## Phase 1: Cycle Resolution (In-Place)
Resolve circular dependencies within the monolithic crate to prepare for a clean split.

- [x] **Step 1.1: Move `poll_until` to `util`**
  - Moved generic polling helper to `src/util/poll.rs`.
  - Decoupled `debug/dmi.rs` from `test_utils`.
  - Verified: Unit tests passed.
- [x] **Step 1.2: Move `Capability` and `Capabilities` to `io`**
  - Moved transport capabilities logic to `src/io/capabilities.rs`.
  - Decoupled `transport/mod.rs` from local definitions, changed to re-export.
  - Verified: Unit tests passed.
- [x] **Step 1.3: Move `TransportError` and `TransportInterfaceType` to `io`**
  - **Step 1.3a**: Moved `SerializableError` trait and `impl_serializable_error!` macro to `src/io/serializable_error.rs` to break dependencies on `proxy` for base errors.
  - **Step 1.3b**: Moved `TransportError` and `TransportInterfaceType` definitions to `src/io/errors.rs`.
  - Decoupled `transport/mod.rs` from local definition, changed to re-export.
  - Cleaned up imports in all `io` modules to remove `crate::transport::TransportError` and use `crate::io::TransportError` instead.
  - Verified: Unit tests passed.
- [x] **Step 1.4: Move `BootstrapOptions` and `BootstrapProtocol` to `io`**
  - Moved bootstrap type definitions to `src/io/bootstrap_types.rs` to decouple `transport` core (`ProxyOps`) from the concrete bootstrap protocol crate.
  - Re-exported them in `bootstrap/mod.rs` for backward compatibility.
  - Verified: Unit tests passed.
- [x] **Step 1.5: Refactor `Params` instantiation to `TransportWrapper`**
  - Removed `create` methods from `Params` structs in `src/io/` (`UartParams`, `SpiParams`, `I2cParams`, `JtagParams`) to completely remove the dependency of `io` on `app` (via `TransportWrapper`).
  - Implemented corresponding `create_*` factory methods on `TransportWrapper` in `src/app/mod.rs`.
  - Updated all callers across `opentitanlib` and `opentitantool` to use the new factory methods.
  - Verified: Built `//sw/host/opentitantool` successfully, and all unit tests in `//sw/host/opentitanlib:opentitanlib_test` passed!
  - **This completes Phase 1 (Cycle Resolution)!**

## Phase 2: Define Sub-Crates (In-Place)
Define separate `rust_library` targets in the monolithic `sw/host/opentitanlib/BUILD` file and adjust imports to define boundaries.

- [x] **Step 2.1: Define `opentitanlib_core` target**
  - Created `src/core_lib.rs` as root entry point.
  - Defined `opentitanlib_core` in `BUILD` containing `util`, `crypto`, `io` and core `transport` traits.
  - Decoupled JTAG interface from concrete OpenOCD implementation by introducing `OpenOcdOps` trait and returning `Box<dyn Any>` (Step 2.1a).
  - Decoupled `io/eeprom.rs` from `spiflash` by defining standard JEDEC SPI flash constants locally.
  - Moved top-level `uart` module (console interact) to `core` to resolve dependency from `util::rom_detect`.
  - Verified: `bazel build //sw/host/opentitanlib:opentitanlib_core` compiled successfully.
- [x] **Step 2.2: Define `opentitanlib_chip` target**
  - Created `src/chip_lib.rs` as root entry point.
  - Defined `opentitanlib_chip` in `BUILD` containing `chip` and `dif` modules.
  - Resolved cyclic dependency: ownership transfer manifest logic (`ownership` module) was identified to be fundamentally a chip-level feature (since chip implements ownership transfer protocol and boot services carry manifests).
  - Decided to locate `ownership` module inside the `chip` crate, keeping the DAG clean: `protocols` -> `chip` -> `core`.
  - Declared `pub mod ownership;` in `src/chip_lib.rs` and added the module source files to `opentitanlib_chip`'s `srcs`.
  - Added missing external dependencies to the chip target (`clap`, `serde_bytes`, `sphincsplus`, `byteorder`, `once_cell`, `sha2`).
  - Implemented `JtagLcExt` extension trait in `src/dif/lc_ctrl.rs` to allow backward-compatible call syntax (`jtag.read_lc_ctrl_reg(...)`) without JTAG interface in `core` depending on `dif` definitions.
  - Updated internal imports in `chip`, `dif`, and `ownership` to point to `opentitanlib_core::` for core services.
  - Verified: `bazel build //sw/host/opentitanlib:opentitanlib_chip` compiled successfully.
- [x] **Step 2.3: Define `opentitanlib_debug` target**
  - Used `src/debug/mod.rs` as root entry point (already a perfect directory root).
  - Defined `opentitanlib_debug` in `BUILD` containing `dmi`, `elf_debugger`, and `openocd` modules.
  - Decoupled `OpenOcdJtagChain`'s `into_raw` implementation in `openocd.rs` to return `Box<dyn Any>` to match JTAG trait decoupling.
  - Added target configurations to `compile_data` and `rustc_env` in `BUILD` (needed by `openocd.rs` compile-time configuration embedding).
  - Added missing dependencies to target (`typetag`, `rustix`, `scopeguard`, `object`).
  - Updated internal imports in `src/debug/**` to use `opentitanlib_core::` for core services.
  - Verified: `bazel build //sw/host/opentitanlib:opentitanlib_debug` compiled successfully.
- [x] **Step 2.4: Define `opentitanlib_app` target**
  - Used `src/app/mod.rs` as root entry point (already a perfect directory root).
  - Defined `opentitanlib_app` in `BUILD` containing `command`, `config`, `gpio`, `i2c`, `spi`, and `mod` modules.
  - Resolved cyclic dependency: `app` depended on concrete IO expander drivers (via `ioexpander::create` which instantiates `sx1503::create` which in turn depends on `TransportWrapper` from `app`).
  - Implemented the **Registry Pattern** for IO expanders:
    - Defined `IoExpanderFactory` function pointer type in `app/mod.rs`.
    - Added `io_expander_drivers` registry map to `TransportWrapperBuilder`.
    - Added `register_io_expander_driver` method on `TransportWrapperBuilder`.
    - Updated `TransportWrapperBuilder::build` to look up and instantiate drivers dynamically from registry, removing the dependency of `app` on `ioexpander` module.
    - Updated `src/backend/mod.rs` to register the concrete `sx1503` driver at target composer level (Step 7), which is cycle-free.
  - Added `:config` filegroup to `compile_data` in `BUILD` (needed by `config/mod.rs` config file embedding).
  - Added missing dependencies to target (`once_cell`, `erased-serde`, `humantime-serde`, `opentitantool_derive` proc-macros).
  - Updated internal imports in `src/app/**` to use `opentitanlib_core::` for core services and `opentitanlib_debug::` for debugging tools, and removed `app` folder name from local root-relative paths.
  - Verified: `bazel build //sw/host/opentitanlib:opentitanlib_app` compiled successfully.
- [x] **Step 2.5: Define `opentitanlib_proxy_protocol` target**
  - Created `src/proxy_protocol_lib.rs` as root entry point.
  - Defined `opentitanlib_proxy_protocol` in `BUILD` containing `errors` and `protocol` modules under `src/proxy/`.
  - Mapped external subdirectories in `proxy_protocol_lib.rs` using `#[path = "proxy/errors.rs"]` and `#[path = "proxy/protocol.rs"]` to define a clean client/server shared API target without moving files.
  - Resolved circular dependency: dynamically boxed errors in the dynamic downcasting registry of `errors.rs` depended on high-level protocol errors (like `BootstrapError` in `protocols`). Restricted the downcast list to only core/base errors (timeouts, connection issues, pin failures, which represent 99% of programmatic catch needs). This completely decoupled `proxy_protocol` from high-level libraries.
  - Updated internal imports in `errors.rs` and `protocol.rs` to point to `opentitanlib_core::` for base structures.
  - Verified: `bazel build //sw/host/opentitanlib:opentitanlib_proxy_protocol` compiled successfully.
- [x] **Step 2.6: Define `opentitanlib_transports` target**
  - Created `src/transport/transports_lib.rs` as root entry point.
  - Defined `opentitanlib_transports` in `BUILD` containing all 58 backend driver and board files under `src/transport/` (Ftdi, HyperDebug, ChipWhisperer, DediProg, Qemu, Verilator, Proxy client, and IoExpander driver).
  - Resolved cyclic dependency: the accelerated DediProg transport (`dediprog/spi.rs`) and HyperDebug transport (`hyperdebug/spi.rs`) depended on JEDEC SPI flash constants defined in high-level `SpiFlash` protocol target. Defined standard JEDEC constants (READ, FAST_READ, PAGE_PROGRAM, WRITE_ENABLE, READ_SFDP) inside the low-level `io::eeprom` target in `core`. This completely decoupled concrete transports from the high-level `protocols` crate.
  - Resolved cyclic dependency: QEMU emulator target (`qemu/mod.rs` factory) took `QemuOpts` CLI option structure defined in target composer level (Step 7). Defined plain data `QemuParams` configuration structure in `qemu/mod.rs` and moved the CLI config mapping helper `device_path` to it. Updated target composer `backend/qemu.rs` and the host test `test_status.rs` to map CLI `QemuOpts` to plain `QemuParams` using a `.to_params()` method, completely decoupling QEMU driver target from backend target.
  - Decoupled `QemuJtag`'s `into_raw` implementation in `qemu/jtag.rs` to return `Box<dyn Any>` to match JTAG trait decoupling.
  - Add missing file imports that were bypass-private imports under parent module in monolith (Spi `Target`, I2c `Bus`, and `NonblockingHelp` are `io` traits and now imported directly from `opentitanlib_core::io::`).
  - Added hyperdebug adapter configs and firmwares to `compile_data` and `rustc_env` in `BUILD` (needed by hyperdebug driver).
  - Added missing dependencies to target (`byteorder`, `zerocopy`, `erased-serde`, `num_enum`).
  - Ran a global python script on the subfolders to transition all `crate::io`, `crate::util`, `crate::app`, `crate::proxy` imports to their correct target prefixes, and removed the directory level prefix `transport::` from internal crate-relative submodule imports.
  - Verified: `bazel build //sw/host/opentitanlib:opentitanlib_transports` compiled successfully.
- [ ] **Step 2.7: Define `opentitanlib_protocols` target**
- [ ] **Step 2.8: Define `opentitanlib_backend` target**
- [ ] **Step 2.9: Define `opentitanlib_test_utils` target**
- [ ] **Step 2.10: Re-export everything in super-crate `opentitanlib`**

## Phase 3: File Organization
*Not started*

## Phase 4: Feature Gating Transports
*Not started*
