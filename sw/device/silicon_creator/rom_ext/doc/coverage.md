# ROM\_EXT Coverage

Measuring code coverage for the ROM\_EXT involves standard on-device
instrumentation and utilizes the UART-based reporting mechanism.

## Coverage Reporting

The ROM\_EXT uses the **UART runtime** for coverage collection. Coverage data is
automatically reported to the UART stream under the following conditions:

1.  **Stage Transition:** Just before jumping to the next boot stage (e.g.,
    Owner stage).
2.  **Shutdown/Reset:** Immediately before the device performs a reset or enters
    a shutdown state.

### Testing with ROM\_EXT Coverage

When running tests that include the ROM\_EXT (e.g., using the `rom_ext`
execution environment), coverage is handled automatically. The instrumented
ROM\_EXT will automatically emit its coverage profile to the UART stream, and
the `opentitanlib` console will capture and demux the data into the test
artifacts.

No special action or test-code modification is required to enable coverage for
the ROM\_EXT; if the test executes the ROM\_EXT code, the coverage will be
captured.

### Practical Considerations for Tests

To ensure that reported coverage data is reliably captured and processed by the
host-side tools, developers should keep the following in mind:

-   **E2E Test Log Reading:** For end-to-end tests, ensure that the test runner
    reads enough UART logs after the firmware execution completes. This allows
    time for the full coverage profile to be transmitted and detected by the
    `opentitanlib` console.
-   **Rescue Tests:** In rescue mode, the coverage report is typically triggered
    during the reboot sequence. For rescue-specific tests, sending the **reboot
    command** is necessary to initiate the transfer of the coverage profile to
    the host.

## Flash Memory Layout

The instrumented ROM\_EXT is significantly larger than the standard production
version. To accommodate this, the coverage build employs an expanded flash
memory layout where the ROM\_EXT slot is increased (typically to 128K).

For detailed information on the adjusted flash memory map and how it is managed
via the `slot_spec` attribute, see the
**[Flash Memory Layout](../../../lib/coverage/README.md#flash-memory-layout)**
section in the Test Coverage Overview.

## Transport Initialization

The ROM\_EXT is divided into immutable and mutable sections, which handle
coverage transport initialization differently:

-   **Immutable Section:** This section relies on the **coverage transport
    (UART)** already initialized by the ROM. Because the immutable section
    cannot access architecture-specific libraries to initialize UART, it assumes
    the transport is ready for reporting coverage data.
-   **Mutable Section:** This section **re-initializes** the coverage transport
    upon boot, ensuring it has full control over the reporting mechanism for its
    execution.

## Invalidation and Handoff

To prevent coverage data from being corrupted or incorrectly attributed across
boot stages, the `coverage_invalidate()` function is called before every stage
transition (e.g., ROM to ROM\_EXT).

This ensures that the `coverage_status` flag is cleared, and any subsequent
stage must explicitly call `coverage_init()` to re-enable measurement for its
own execution.

## Technical Details

For more in-depth information on the underlying coverage mechanisms used by the
ROM\_EXT, refer to the following documents:

-   **[On-Device Clang Coverage](../../../lib/coverage/doc/clang.md):** Details
    of the C/C++ instrumentation and runtime library.
-   **[Ibex ASM Coverage](../../../../../util/coverage/asm/README.md):** Details
    of the assembly instrumentation framework used in assembly files such as
    `rom_ext_start.S`.
