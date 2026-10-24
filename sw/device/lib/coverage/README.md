# OpenTitan Code Coverage

OpenTitan's test coverage system provides comprehensive line coverage
measurement for all device-side software components, including C code, RISC-V
assembly, and OTBN application code. Measuring code coverage is a critical
metric for assessing the thoroughness of a test suite and is a requirement for
achieving high-assurance security certifications.

The system is optimized for resource-constrained environments and supports
execution across multiple platforms, ranging from host-side unit tests to
full-system emulation and hardware. It provides visibility into which parts of
the device-side firmware—including the ROM, ROM\_EXT, and owner-stage code—are
exercised by functional and end-to-end tests.

## Tiered Coverage Strategy

To cover the diverse range of software on OpenTitan, the system employs three
distinct mechanisms:

-   **Clang Source-based Coverage:** Used for all C/C++ code. It utilizes LLVM's
    source-based instrumentation with a custom, lightweight on-device runtime to
    minimize RAM and Flash overhead.
-   **Ibex ASM Coverage:** A custom framework for handwritten RISC-V assembly.
    It includes an automated instrumentation tool and macros for manual marking,
    with support for preserving coverage data across SRAM scrambling events.
-   **OTBN Coverage:** Application coverage for the OpenTitan Big Number (OTBN)
    accelerator, integrated directly into the OTBN simulator (`otbnsim`).

## Component Directory

If you are a developer looking for a practical guide on how to run tests and
analyze coverage reports, start here:

-   **[Code Coverage User Guide](../../../../doc/getting_started/coverage.md):**
    Practical manual for running tests and analyzing reports.

For more in-depth technical documentation on specific parts of the system, see:

-   **[On-Device Clang Coverage](./doc/clang.md):** Source-based instrumentation
    details, runtime library, and wire format.
-   **[Ibex ASM Coverage](../../../../util/coverage/asm/README.md):** Details of
    the assembly instrumentation framework.
-   **[OTBN Coverage](./doc/otbn.md):** Simulation-based coverage for the OTBN
    accelerator.
-   **[ROM Coverage](../../silicon_creator/rom/doc/coverage.md):** Flash ROM
    mechanism and boot-stage integration.
-   **[ROM\_EXT Coverage](../../silicon_creator/rom_ext/doc/coverage.md):**
    Integration guide for second-stage boot and ROM\_EXT E2E tests.
-   **[CI Testing](../../../../util/coverage/doc/ci.md):** Distributed
    collection, aggregation pipeline, and smoke tests.
-   **[Coverage Viewer](../../../../util/coverage/viewer/README.md):**
    Interactive report viewer features, data schema, and filtering.

## Platform Support Matrix

The coverage system supports several primary types of tests across different
execution environments:

Test Type                    | Execution Platform | Coverage Mechanism
:--------------------------- | :----------------- | :-----------------
**Host-side C/C++ Unittest** | Host PC            | LLVM Source-based (Standard Runtime)
**Ibex C Functest**          | FPGA / QEMU        | OTTF Coverage Runtime
**Ibex ASM Functest**        | FPGA / QEMU        | Ibex ASM Instrumentation
**ROM E2E Test**             | FPGA / QEMU        | UART Runtime + Flash ROM
**ROM\_EXT E2E Test**        | FPGA / QEMU        | UART Runtime
**Provisioning E2E Test**    | FPGA               | Custom Runtimes
**OTBN ASM Simtest**         | OTBN Simulator     | Program Counter Tracking

Coverage profiles for device-side tests are compressed on-device and transmitted
to the host via UART or console anchors, where they are reconstructed into
standard LLVM `profraw` and LCOV formats.

## Bazel Coverage Overview

Bazel's `coverage` subcommand is designed to collect code coverage data for test
targets, generating a combined LCOV report in
`bazel-out/_coverage/_coverage_report.dat`.

While this works out-of-the-box for host-side unit tests, the process involves
several automated steps:

1.  **Building:** The `--collect_code_coverage` flag activates the toolchain's
    coverage feature, and instrumented object files are collected.
2.  **Testing:** Bazel's `collect_coverage.sh` wrapper runs the test, ensuring
    the `LLVM_PROFILE_FILE` environment variable is set. The instrumented code
    dumps raw profiling data (`.profraw`) to this path.
3.  **Collection:** Bazel invokes a `_collect_cc_coverage` tool (defined in the
    test rule) to convert the `.profraw` data into the LCOV `.dat` format.
4.  **Merging:** All LCOV reports from a single test invocation are merged into
    a single `coverage.dat`.
5.  **Final Aggregation:** Bazel aggregates all `coverage.dat` reports from all
    tests into the final comprehensive `_coverage_report.dat`.

OpenTitan's custom tests (Functional, E2E, and OTBN) leverage this standard flow
by providing their own implementations of the capture and conversion tools.

## Bazel Integration & Build System

The OpenTitan build system uses Bazel to manage the complexities of
cross-compiling instrumented firmware. Coverage is enabled globally using the
`--config=ot_coverage` flag, which activates several build-time features.

### Coverage Build Indicators

To support special adjustments for coverage builds, the system provides several
indicators for detecting the coverage mode. These indicators follow Bazel
conventions and are used across C/C++, Rust, and linker scripts.

#### `coverage_enabled`

This flag is set when running `bazel coverage --config=ot_coverage`, regardless
of whether the specific target is instrumented.

-   **Linker:** `DEFINED(_ot_coverage_enabled)`
-   **C/C++:** `#ifdef OT_COVERAGE_ENABLED`
-   **Rust:** `#[cfg(feature = "ot_coverage_enabled")]`
-   **Bazel Select:** `//rules/coverage:enabled`
-   **Bazel Rule:** `ctx.var.get('ot_coverage_enabled', 'false') == 'true'`

#### `coverage_instrumented`

This flag is set only when the target is actually being instrumented with LLVM
coverage profiling.

-   **Linker:** `DEFINED(_ot_coverage_instrumented)`
-   **C/C++:** `#ifdef OT_COVERAGE_INSTRUMENTED`
-   **Bazel Select:** `//rules/coverage:instrumented`
-   **Bazel Rule:** `ctx.coverage_instrumented()`

### Transitions and Instrumentation Control

Not all targets should be instrumented for coverage. For example, host-side
tools, the `test_rom`, and the coverage runtime itself must remain
uninstrumented to avoid recursion or excessive resource usage.

Disabling instrumentation only affects the `coverage_instrumented` indicators;
the `coverage_enabled` indicators remain active.

Bazel **Transitions** are used to manage this:

-   **Host Transition:** Automatically disables `collect_code_coverage` for all
    host-side dependencies.
-   **Per-Target Control:** The `opentitan_binary` and `opentitan_test` rules
    provide a `collect_code_coverage` attribute:
    -   `0`: Force disable instrumentation for the target and all its
        dependencies.
    -   `1`: Force enable instrumentation.
    -   `-1`: Inherit from the parent configuration.
-   **Local Disablement:** Using `features = ["-coverage"]` in a `cc_library`.
    This disables instrumentation for that specific library but does not affect
    its dependencies.

## Flash Memory Layout

Instrumenting firmware for coverage significantly increases its size (typically
by **1.5x to 2x**) due to profiling counters and metadata. To accommodate this,
the memory layout is adjusted when building in coverage mode.

### ROM\_EXT Layout Adjustments

To accommodate the larger instrumented binary, the build system expands the
ROM\_EXT slot size (typically to 128K) when building in coverage mode. This
shift occurs within the allocated flash slots (e.g., Flash Slot A).

Mode                  | ROM\_EXT Size | Tests Space
:-------------------- | :------------ | :----------
**Normal**            | 64K           | 448K
**ROM\_EXT Coverage** | 128K          | 384K / 320K

### ROM Coverage Layout Adjustments

Measuring ROM coverage requires more significant changes to the overall flash
map. Due to the impact of this layout change, these adjustments are only applied
to tests annotated with the `rom_coverage` Bazel tag.

-   **Flash ROM Slot:** The instrumented ROM is stored at the end of the eFlash.
-   **Minimal Loader:** The mask ROM slot is occupied by a minimal **Flash ROM
    Loader** that jumps to the Flash ROM.
-   **Shifted Application Slots:** Application slots (Owner/OTTF) are shifted to
    accommodate the larger ROM\_EXT and the Flash ROM.

Mode             | ROM Slot       | Flash Slot A   | Flash Slot B          | End of Flash
:--------------- | :------------- | :------------- | :-------------------- | :-----------
**Normal**       | Mask ROM (32K) | RomExt + Tests | RomExt + Tests (512K) | N/A
**Rom Coverage** | Loader (32K)   | RomExt + Tests | RomExt + Tests (448K) | Flash ROM (64K)

### Assemble Address Variables

To manage these variations, OpenTitan introduces the `slot_spec` attribute in
the execution environment configuration. This allows the build system to define
different layouts for normal and coverage builds using Bazel `select`
statements:

```py
EARLGREY_SLOTS_NORMAL = {
    "rom_ext_size": "0x10000",
    "owner_slot_a": "0x10000",
    # ...
}
EARLGREY_SLOTS_COVERAGE = {
    "rom_ext_size": "0x20000",
    "owner_slot_a": "0x20000",
    # ...
}
EARLGREY_SLOTS = select({
    "//rules/coverage:enabled": EARLGREY_SLOTS_COVERAGE,
    "//conditions:default": EARLGREY_SLOTS_NORMAL,
})
```

These variables are used in two primary ways:

1.  **Binary Assembly:** The build system uses these variables as placeholders
    in the firmware assembly specification to place binaries at the correct
    offsets.

    ```py
    # Example assembly spec
    assemble = "{rom_ext}@{rom_ext_slot_a} {firmware}@{owner_slot_a}"
    ```

2.  **Linker and C Symbols:** Every key in the `slot_spec` is automatically
    exposed as a linker symbol (prefixed with `_`, e.g., `_rom_ext_size`).
    Firmware and linker scripts can reference these symbols to adapt to the
    current layout:

    ```ld
    /* Example linker script usage */
    _ottf_start_address = ORIGIN(eflash) + _rom_ext_size;
    ```
