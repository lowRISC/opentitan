# On-Device Clang Coverage

OpenTitan uses LLVM's source-based code coverage for C and C++ code. To support
on-device measurement on memory-constrained hardware, the system replaces the
standard, resource-heavy LLVM `compiler-rt` with a lightweight, optimized
on-device runtime.

The on-device coverage system workflow consists of four primary stages:

1.  **Instrumentation:** The compiler inserts profiling counters and emits
    mapping metadata.
2.  **Execution:** The firmware initializes counters and records execution hits
    in RAM.
3.  **Reporting:** The on-device runtime compresses and transmits the counter
    data via UART or OTTF console.
4.  **Reconstruction:** Host-side tools capture the stream, correlate it with
    ELF metadata using the Build ID, and generate standard LLVM coverage
    reports.

## Instrumentation and Compiler Features

Instrumentation for C/C++ code is managed through Bazel's standard coverage
mechanisms and OpenTitan's hermetic toolchain.

### Enabling Instrumentation

When running with `bazel coverage --config=ot_coverage`, the
`--collect_code_coverage` flag is automatically set. This signals Bazel to
request the `coverage` feature from the C++ toolchain.

In OpenTitan's hermetic toolchain, requesting this feature triggers the
insertion of necessary Clang flags, such as `-fprofile-instr-generate` and
`-fcoverage-mapping`. These flags instruct the compiler to insert profiling
counters into the generated code and emit the corresponding mapping metadata
sections.

### Overriding and Disablement

Instrumentation can be selectively disabled for specific targets to save
resources or avoid recursion:

-   **Bazel Transitions:** The OpenTitan transition on `opentitan_binary` allows
    forcing `collect_code_coverage = 0` for a target and all its transitive
    dependencies.
-   **Feature Overrides:** A target can explicitly opt-out of instrumentation by
    including `features = ["-coverage"]` in its definition. This prevents the
    toolchain from adding the coverage-related compiler flags for that specific
    library.

## Coverage Runtime Library

The runtime library (`sw/device/lib/coverage`) provides a lightweight API for
managing coverage collection on-device. It is designed to be modular, allowing
different transport layers (UART or OTTF) to be plugged in depending on the test
environment.

### API Library and No-op implementation

The core API (`//sw/device/lib/coverage:api`) provides the C interface for
firmware. When the coverage build is disabled, the API header defines these
functions as empty macros to ensure all calls are removed by the preprocessor.

The API library also includes a **weak, no-op implementation** of the coverage
functions. This ensures that common libraries (like `shutdown` or `rstmgr`) that
call the coverage API can still be linked in unit tests or other environments
where custom reporting is not required.

### Runtime Variants and Bazel Aliasing

To minimize the risk of accidentally pulling coverage code into production
firmware, the library target is aliased to different variants based on Bazel
configuration:

-   **`coverage:instrumented`:** The full implementation used for reporting
    coverage data via UART or OTTF.
-   **`coverage:enabled`:** A minimal "skip" runtime that only reports a
    `COVERAGE PROFILE SKIP` anchor. This is used when coverage is enabled
    globally but a specific binary (like the `test_rom`) is not instrumented.
-   **`default`:** Aliased to an empty target (`//sw/device:nothing`), ensuring
    zero impact on production binaries.

The **OTTF runtime** is automatically included by the on-device test framework
libraries, while the **UART runtime** must be manually added to the dependencies
of boot-stage binaries like the `ROM_EXT`.

### API and Lifecycle

-   **`coverage_init()`:** Initializes the `__llvm_prf_cnts` region in RAM to
    `0xFF` (uncovered). It also sets the `coverage_status` flag to the current
    Build ID, marking the counters as valid for reporting.
-   **`coverage_report()`:** Compresses the counter data and transmits the
    profile over the configured transport.
-   **`coverage_invalidate()`:** Clears the `coverage_status` flag. This must be
    called before transitioning to a subsequent boot stage to prevent stale
    coverage data from being reported later.

### Linker Script Integration

The coverage system provides several linker script fragments to manage memory:

-   **`bss.ld`:** Defines the RAM region for counters (`__llvm_prf_cnts`).
-   **`rodata.ld`:** Defines sections for the Build ID metadata.
-   **`info.ld`:** Defines non-loaded `INFO` sections used by host-side tools to
    extract coverage mapping. This is automatically included in the global
    OpenTitan info sections.

These fragments ensure that when coverage is disabled, the resulting sections
have zero length and do not consume space in the final binary.

### Build ID Tracking

To ensure that reported counters are correlated with the correct version of the
firmware, the runtime utilizes the GNU Build ID. The `coverage_status` is
initialized to `build_id | 1`. This value is checked before reporting to confirm
that the counters in RAM match the currently executing binary.

## Compiler Optimizations

Standard LLVM coverage profiling can significantly inflate both the binary size
and the RAM usage of a firmware image. OpenTitan mitigates this through two
primary compiler-level adjustments:

### Uint8 Bool Counters

By default, LLVM uses 64-bit execution counters for each basic block. To save
RAM, the OpenTitan toolchain is configured to use **single-byte boolean
counters**. Each counter is a `uint8_t` that is initialized to `0xFF`
(uncovered) and set to `0x00` (covered) upon execution. This reduction from 8
bytes to 1 byte per counter allows instrumentation of much larger codebases
within the limited SRAM available on OpenTitan.

### Counter Section Initialization

The `__llvm_prf_cnts` section, which contains these counters, is normally
emitted as `PROGBITS` in the ELF file, increasing the size of the binary stored
in Flash. To save Flash space, the OpenTitan build system drops this section
from the final `.bin` file.

Instead, the section is zero-length in the flash image, and the **Coverage
Runtime Library** is responsible for initializing the RAM region with `0xFF` at
startup.

## Compression and Wire Format

To minimize transmission time and log flooding, coverage profiles are compressed
using a custom Run-Length Encoding (RLE) algorithm with bit-packing.

### RLE and Bit-Packing

The `coverage_compress()` function in `printer.c` processes the counter stream:

-   **Bit-Packing:** If a sequence of counters alternates rapidly (span < 8),
    consecutive 8 counters are packed into a single byte. The **first counter**
    in the sequence is placed at the **least significant bit (LSB)**, and the
    eighth counter at the most significant bit (MSB).
    -   `0x00` (covered) becomes bit `1`.
    -   `0xFF` (uncovered) becomes bit `0`.
-   **RLE Encoding:** For spans of identical counters (or short spans that
    cannot be bit-packed), a tag-and-length format is used. The length is
    encoded as a **var-int** following the tag byte (`0x00` or `0xFF`):

Span Length (x)       | Encoding               | Length | Example (Tag `0xFF`)
:-------------------- | :--------------------- | :----- | :-------------------
`0 <= x <= 0xFD`      | `[tag][size_le8]`      | 2B     | `FF 05` (5 x `0xFF`)
`0xFE <= x <= 0xFFFF` | `[tag][FE][size_le16]` | 4B     | `FF FE 00 01` (256 x `0xFF`)
`0x10000 <= x`        | `[tag][FF][size_le24]` | 5B     | `FF FF 00 00 01` (65536 x `0xFF`)

### Wire Format

The profile is transmitted as a hex-encoded stream of magic bytes, the 20-byte
Build ID, the compressed counters, and a CRC32 checksum. The stream is
encapsulated by standardized anchors that allow host-side tools to identify the
data type and status:

-   **`== COVERAGE PROFILE START ==` / `== COVERAGE PROFILE END ==`**:
    Encapsulate a valid, compressed coverage profile.
-   **`== COVERAGE PROFILE SKIP ==`**: Indicates that while the overall build is
    in coverage mode, this specific binary has instrumentation disabled. No
    profile data follows this anchor.
-   **`== COVERAGE PROFILE INVALID ==`**: Indicates that a reporting attempt was
    made but the data was marked invalid (e.g., after a call to
    `coverage_invalidate()`).

A typical valid report follows this structure:

```
== COVERAGE PROFILE START ==
[Magic Bytes: \x81OTCove\xff]
[20-byte Build ID]
[Compressed Counter Stream]
[4-byte CRC32]
== COVERAGE PROFILE END ==
```

## Host-Side Processing

### Build ID-based Correlation

Since the on-device runtime only reports raw counters to save bandwidth, the
host must be able to correlate these counters with the correct ELF metadata to
reconstruct the profile.

The system utilizes the **GNU Build ID** (a unique SHA-1 hash) for this purpose:

1.  Every instrumented binary includes a unique Build ID in its `rodata`
    segment.
2.  The on-device runtime captures this Build ID and prepends it to the
    transmitted coverage report.
3.  The host-side `collect_cc_coverage` tool uses the Build ID from the report
    to find the matching ELF file in the build artifacts, allowing it to extract
    the necessary LLVM coverage metadata to reconstruct a valid report.

### Data Capture (opentitanlib)

The `opentitanlib` console (accessible via `opentitantool console`) monitors the
UART/OTTF stream for the coverage start anchor. Upon detection, it demuxes the
hex-encoded coverage data from the regular log stream, redirecting it to an
internal buffer for verification. This ensures that large coverage profiles do
not flood the console logs and are reliably captured for subsequent processing.

Once the end anchor is reached, the captured data is saved to a file with the
`.xprofraw` extension. The save path is determined by the `LLVM_PROFILE_FILE`
environment variable, which is automatically set by Bazel when running in
coverage mode.

### Profile Reconstruction (collect\_cc\_coverage)

The `collect_cc_coverage` tool (implemented in Rust) transforms the raw device
dump into a standard LCOV file.

1.  **ELF Correlation:** It extracts the Build ID from the raw dump and searches
    for a matching ELF binary within the test's **`runfiles`**. OpenTitan's
    custom Bazel rules automatically propagate these binaries to ensure they are
    available during the coverage collection phase.
2.  **Metadata Extraction:** Once the matching ELF is found, the tool extracts
    the static LLVM coverage metadata sections (`__llvm_prf_data` and
    `__llvm_prf_names`).
3.  **Profile Generation:** It decompresses the device-side counters and
    combines them with the extracted metadata to produce a standard `profraw`
    file.
4.  **LCOV Conversion:** It invokes `llvm-profdata` and `llvm-cov export` to
    transform the `profraw` data into the standard LCOV (`.dat`) format.

The resulting LCOV data is then merged by Bazel's coverage infrastructure to
produce a single `coverage.dat` file for the test target. This merging is
essential for tests that report multiple coverage profiles during a single
execution (e.g., across multiple boot stages).

## Known Limitations

-   **Branch Elimination:** Branches that depend on unsatisfied compile-time
    constants are often optimized out by the compiler and removed from the final
    firmware. However, these branches remain in the LLVM coverage mapping
    metadata and will be reported as "uncovered" in the final report, even if
    the code path is technically unreachable in that specific build.
-   **Inaccuracy around Reset Points:** Clang's instrumentation assumes that
    basic-block control flow continues linearly or through standard branch
    instructions. When a device reset occurs (e.g., during `shutdown_finalize`
    in `shutdown.c`), the execution environment is destroyed and re-initialized,
    breaking this assumption. This can lead to inaccurate or missing coverage
    data for the code immediately surrounding the reset point.
