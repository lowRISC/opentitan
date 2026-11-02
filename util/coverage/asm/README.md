# Ibex ASM Coverage Guide

OpenTitan provides a custom framework for measuring code coverage in handwritten
RISC-V assembly files. This enables the generation of detailed coverage reports
for assembly code, similar to those produced for C/C++ code.

## Overview

The Ibex ASM coverage system consists of several integrated components:

-   **Assembly API:** A set of RISC-V macros (defined in `api_asm.h`) for
    interacting with the coverage runtime and incrementing counters in SRAM.
-   **Instrumentation Tool:** A basic block analysis and counter insertion
    framework managed via the `run_instrument.sh` wrapper script, which
    automatically processes all registered assembly files in the repository.
-   **Bazel Rule:** The `asm_library_with_coverage` rule, which manages the
    instrumentation process and injects LLVM-compatible coverage metadata into
    the final binary.

## User Guide

### 1. Enabling Coverage in Assembly Files

To measure coverage for an assembly file, you must include the coverage API and
specify the counter placement.

#### 1.1. Import the coverage API

Include the coverage header at the top of your assembly file:

```assembly
#include "sw/device/lib/coverage/api_asm.h"
```

#### 1.2. Specify the counter placement

Add the following section pragma to your assembly file to define where counters
are stored:

```assembly
// PRAGMA_COVERAGE: section(<section_name>)
```

Available sections:

*   `__llvm_prf_cnts`: For standard assembly code running after SRAM scrambling.
*   `__llvm_prf_cnts_head`: Reserved for early-boot code that runs before SRAM
    scrambling. Only 64 counters are available in this section, as they must be
    manually preserved in registers.

#### 1.3. Define the Bazel Library

In your `BUILD` file, use the `asm_library_with_coverage` rule instead of
`cc_library`.

```bazel
load("//rules/coverage:asm.bzl", "asm_library_with_coverage")

asm_library_with_coverage(
    name = "my_assembly_lib",
    srcs = ["my_assembly_file.S"],
    deps = [
        "//sw/device/lib/coverage:api_asm",
    ],
)
```

The `asm_library_with_coverage` rule registers the assembly files for
instrumentation and wraps them as a `cc_library`.

Note that the `srcs` attribute MUST only contain assembly files.

All other attributes are passed through to the underlying `cc_library`. When
coverage mode is disabled, this rule behaves identically to `cc_library`.

### 2. Instrumentation

The tool supports both automatic and manual instrumentation.

#### 2.1. Automatic Instrumentation (Recommended)

Automatic instrumentation is activated using pragmas in the assembly source:

```assembly
// PRAGMA_COVERAGE: autogen start
... assembly code ...
// PRAGMA_COVERAGE: autogen stop
```

If the `stop` pragma is omitted, autogeneration remains active from the `start`
pragma until the end of the file.

To apply the instrumentation markers, run the following command:

```bash
./util/coverage/asm/run_instrument.sh --apply
```

The tool has several modes:

*   `--apply`: Refreshes all markers and saves changes in place.
*   `--check`: Linting mode for CI to verify markers are up-to-date.
*   `--dryrun`: Displays results of basic block analysis without modifying
    files.
*   `--clear`: Removes all existing auto-generated markers.

#### 2.2. Manual Instrumentation

While automatic instrumentation is convenient, manual markers may be required in
certain scenarios:

-   **Register Constraints:** The automatic instrumentation macro
    (`COVERAGE_ASM_AUTOGEN_MARK`) always clobbers the **`t6` register**. If `t6`
    is unavailable or must be preserved (e.g., in an Interrupt Service Routine
    handler), you must use a manual marker to specify an alternative temporary
    register.
-   **Placement Restrictions:** In sensitive code regions, such as those
    performing **SRAM scrambling** or early-boot memory initialization, autogen
    markers might be placed at inappropriate locations. Manual markers allow for
    precise control over exactly where the counter is incremented.

Use the `COVERAGE_ASM_MANUAL_MARK(kTemp, kIndex)` macro for precise control:

-   `kTemp`: A temporary register that will be clobbered.
-   `kIndex`: A unique integer; the instrumentation tool will automatically
    reassign sequential indices when run.

### 3. Running Tests and Generating Reports

Once the setup steps are complete, you can generate a coverage report using the
`bazel coverage` command. For example:

```bash
./bazelisk.sh coverage --config=ot_coverage \
  //sw/device/tests:crt_test_fpga_cw340_test_rom

genhtml -o /tmp/$USER/coverage --ignore-errors inconsistent \
  bazel-out/_coverage/_coverage_report.dat

# ...
# Processing file sw/device/lib/crt/crt.S
#   lines=51 hit=51 functions=2 hit=2
# ...
```

The reports will include the assembly source files with line-by-line coverage
data.

--------------------------------------------------------------------------------

## Implementation Details

### Assembly Syntax Restrictions

To ensure reliable parsing, instrumented assembly must follow these conventions:

-   **One statement per line:** Each line must contain exactly one instruction,
    label, or directive.
-   **Function Encapsulation:** Code should be within functions marked with
    `.type name, @function` and terminated with a `.size` annotation.
-   **Labels:** Branch targets should be on their own line.

### Automated Instrumentation Flow

The project provides the `util/coverage/asm/run_instrument.sh` script to manage
automated instrumentation. This script discovers all assembly sources belonging
to `asm_library_with_coverage` targets and processes them with the
`instrument.py` tool.

Registering your assembly file for coverage tracking is as simple as adding it
to an `asm_library_with_coverage` rule.

### Automated Instrumentation Logic

The `util/coverage/asm/instrument.py` tool performs basic block analysis to
optimize counter placement:

-   **Block Splitting:** Code is split into blocks at every label (entry point)
    and after every branch or trap instruction (exit point).
-   **Marker Insertion:** If a block does not have a manual marker and autogen
    is enabled, the tool inserts an autogen marker.
-   **Connectivity Analysis:** Blocks are assigned `up` and `down` attributes to
    track fall-through and entry connectivity.
-   **Counter Propagation:** If two blocks are connected, the tool propagates
    the counter ID. This allows covering blocks where adding a marker is
    infeasible by leveraging markers from adjacent blocks.

### Counter Preservation across SRAM Scrambling

During early boot, OpenTitan scrambles Main SRAM, which is destructive to
existing data. To preserve coverage data, the `api_asm.h` library provides
macros to backup and restore the "head" counters:

-   `COVERAGE_ASM_BACKUP_COUNTERS(kReg0, kReg1)`: Copies the first 64 counters
    into registers.
-   `COVERAGE_ASM_RESTORE_COUNTERS(kReg0, kReg1)`: Restores them back to SRAM
    after scrambling is complete.

### Bazel Integration

The `asm_library_with_coverage` rule integrates assembly coverage into the Clang
pipeline by:

1.  **Metadata Injection:** Running the `generate_mapping.py` tool to append
    LLVM-compatible coverage metadata (`__llvm_covmap`, `__llvm_covfun`) and
    profiling data (`__llvm_prf_data`, `__llvm_prf_names`) directly to the
    assembly sources as assembly directives.
2.  **Counter Allocation:** Defining the counter array (`.L__asm_profc`) within
    the specified coverage counter section.
3.  **Compilation:** Passing the processed assembly files to `cc_library` to be
    compiled into the final library.

## Known Limitations

-   **Vector Table Support:** The RISC-V vector table is not supported for
    instrumentation. Because the vector table has a fixed architectural layout
    and size, adding instrumentation macros would displace the handlers and
    break the table structure.
