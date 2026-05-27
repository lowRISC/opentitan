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
- [ ] **Step 2.5: Define `opentitanlib_transports` target**
- [ ] **Step 2.6: Define `opentitanlib_protocols` target**
- [ ] **Step 2.7: Define `opentitanlib_backend` target**
- [ ] **Step 2.8: Define `opentitanlib_test_utils` target**
- [ ] **Step 2.9: Re-export everything in super-crate `opentitanlib`**

## Phase 3: File Organization
*Not started*

## Phase 4: Feature Gating Transports
*Not started*
