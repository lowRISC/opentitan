# ROM Coverage

Measuring code coverage for the Mask ROM is primarily constrained by the fixed
size of the ROM slot (32K). OpenTitan addresses this by using a "Flash ROM"
mechanism for coverage builds.

## Coverage Reporting

To measure ROM coverage, test targets must be annotated with the `rom_coverage`
Bazel tag. When coverage is enabled, ROM coverage-enabled tests will
automatically switch from using the standard Mask ROM to using the
coverage-instrumented Flash ROM and its corresponding Loader.

To indicate that the ROM is instrumented for coverage, it prints an **`InsROM:`
banner** instead of the standard `ROM:` banner during early boot (useful for
human debugging).

The Instrumented Flash ROM reports its collected coverage data through the
**UART stream**. This data is handled automatically by the **OpenTitan console**
on the host. The console monitors the UART stream for the coverage anchors and
demuxes the profile data for verification and storage, ensuring that the ROM
coverage is captured without interference from standard boot logs.

## Flash ROM and Loader

Since the instrumented Mask ROM exceeds the 32K limit of the dedicated ROM slot,
it is relocated to the end of the eFlash (the **Flash ROM**). A minimal **Flash
ROM Loader** is then placed in the Mask ROM slot to initialize the system and
jump to the Flash ROM.

### Flash ROM Settings

The specific binaries for the Flash ROM and its Loader are configured in the
execution environment (e.g., `fpga_cw310`, `sim_qemu`). The build system
switches these binaries based on the `rom_coverage` tag.

```python
fpga_cw340(
    # ...
    rom = "//sw/device/silicon_creator/rom:mask_rom",
    flash_rom = "//sw/device/silicon_creator/rom:flash_rom_image",
    flash_rom_loader = "//sw/device/lib/testing/test_rom:flash_rom_loader",
)
```

-   In standard builds, the `rom` field is used.
-   In coverage builds for targets with the `rom_coverage` tag, the build system
    switches to the `flash_rom` and `flash_rom_loader`.

### Flash ROM

The **Flash ROM** is a variant of the Mask ROM that is stored at the end of the
internal eFlash (the "Flash ROM Slot"). It is updated via bootstrap and provides
sufficient space to accommodate the instrumentation overhead required for
coverage measurement. The Flash ROM image can be cleared using the
`clear-flash-rom` command in `opentitantool`.

### Flash ROM Loader

The **Flash ROM Loader** is a variant of the standard `test_rom` that acts as a
minimal bootstrap and trampoline. Its primary responsibility is to detect the
presence of a Flash ROM and jump to it as early as possible in the boot
sequence.

## Pre-configuration Requirements

Because the Flash ROM executes from eFlash instead of the standard ROM region,
the Loader must pre-configure the hardware to allow a seamless transition:

-   **ePMP Setup:** The Loader unlocks the ePMP (Enhanced Physical Memory
    Protection) to allow read-write-execute access to the entire address space.
-   **Flash Controller Configuration:**
    -   **Memory Protection:** The Flash ROM region (MP Region 7) is configured
        to allow execution.
    -   **Scrambling & ECC:** Scrambling and Error Correction Code (ECC) are
        disabled for the Flash ROM region regardless of the Flash configuration.
-   **SRAM Initialization:** The Main SRAM is initialized and scrambled before
    the jump to ensure the Flash ROM has a clean execution environment.
-   **Vector Table:** The `mtvec` register is redirected to the vector table
    located within the Flash ROM image.

## Existence Detection

The Loader determines whether to jump to the Flash ROM by checking for a unique
**Version Magic** number within the `build_info` struct, which is located at the
end of the Flash ROM image.

The system uses the `kBuildInfoVersion1` magic value. If this magic is detected,
the Loader performs a jump to the Flash ROM entry point. If the magic is missing
(e.g., after a bitstream clear or flash erase), the Loader falls back to the
standard Test ROM execution path.

## Clearing and Updating the Flash ROM

Since the Flash ROM is stored in the eFlash, the bootstrap mechanism within the
Flash ROM itself is configured to skip clearing the Flash ROM slot to avoid
breaking itself.

To return the system to the **Flash ROM Loader**, the Flash ROM detection magic
must be cleared. This can be done by using the `clear-flash-rom` command in
`opentitantool` to invalidate the magic value. After the slot has been cleared,
the Loader can then be used to bootstrap a fresh Flash ROM image.
