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
*Not started*

## Phase 3: File Organization
*Not started*

## Phase 4: Feature Gating Transports
*Not started*
