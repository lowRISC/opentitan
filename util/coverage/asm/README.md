# RISC-V Assembly Coverage Guide

This document outlines the usage of the RISC-V assembly coverage tool.

## Overview

The RISC-V assembly coverage tool allows users to add LLVM-compatible coverage
mapping and profiling data to hand-written assembly files. This enables the
generation of detailed coverage reports for assembly code, similar to those
produced for C/C++ code.

The tool provides two main functionalities:

### 1. Auto-Instrumentation

```shell
./util/coverage/asm/run_instrument.sh
```

This tool automatically injects coverage `MARK` macros into assembly source
files at basic block boundaries. This tool needs to be run after the assembly
file is modified to ensure the generated counter is up-to-date.

### 2. Coverage Report Integration
The `asm_library_with_coverage` Bazel rule is designed to automatically inject
the LLVM coverage mapping and profiling data, integrating them for the LLVM
coverage reporting tools.

This allows Bazel to automatically generate coverage data for assembly code
when building with coverage mode enabled.


## Getting Started

### 1. Enable Instrumentation and Coverage Report

#### 1.1. Import the coverage API.
The coverage API needs to be included in the assembly file to use the coverage marking functions.

```assembly
#include "sw/device/lib/coverage/api_asm.h"
```

#### 1.2. Specify the counter placement
Add the following section pragma in your assembly file.

```assembly
// PRAGMA_COVERAGE: section(<section_name>)
```

The section could be chosen from the following two options:

*   `__llvm_prf_cnts`: For assembly code running after SRAM scramble.
*   `__llvm_prf_cnts_head`: Reserved for assembly code that runs before SRAM scramble. This section is designed for counters that must survive across SRAM scramble, by backing up in registers. There are only 64 counters available in this section.

#### 1.3. Create asm library.
In your `BUILD` file, define an `asm_library_with_coverage` target,
specifying your assembly source files.

```bazel
load("//rules/coverage:asm.bzl", "asm_library_with_coverage")

asm_library_with_coverage(
    name = "my_assembly_lib",
    srcs = ["my_assembly_file.S"],
    deps = [
        "//sw/device/lib/coverage:api_asm",
        # Add other necessary dependencies
    ],
)
```

This rule registers the assembly files for instrumentation, integrating them
into Bazel's coverage system by preprocessing the source files in `srcs` and
then wrapping them as a `cc_library`.

The `asm_library_with_coverage` rule has the same attributes as `cc_library`,
but its `srcs` attribute MUST only contain assembly files.

When coverage mode is disabled, the preprocessing step is skipped, so this rule
behaves identically to `cc_library`.

#### 1.4. Example:
Example from `sw/device/lib/crt/crt.S`:

```assembly
#include "sw/device/lib/coverage/api_asm.h"

// PRAGMA_COVERAGE: section(__llvm_prf_cnts_head)
// PRAGMA_COVERAGE: autogen start

.section .crt, "ax", @progbits
crt_section_clear:
...
```

### 2. Automatic Instrumentation

Automatic instrumentation is off by default. To activate it, place the
`autogen start` pragma at the desired insertion point for generated markers.

```assembly
// PRAGMA_COVERAGE: autogen start
```

The autogeneration feature can be deactivated using the `stop` pragma.
If the `stop` pragma is omitted, autogeneration will remain active after
the `start` pragma until the end of the file.

```assembly
// PRAGMA_COVERAGE: autogen stop
```

#### 2.1. Run the Instrumentation Tool

```bash
./util/coverage/asm/run_instrument.sh \
  (--apply | --check | --dryrun | --clear)
```

The instrumentation tool has four modes:

*   `--apply`: This mode refreshes all the auto-generated markers and saves the changes in place.
*   `--check`: This is a linting mode for CI that shows the diff that would be applied to the files, indicating which lines need to be updated.
*   `--dryrun`: This mode processes the files without modifying them. It displays the results of the basic block analysis, allowing users to review the code before they are applied.
*   `--clear`: This mode removes all existing auto-generated markers.

By default, the tool operates on all source files associated with the `asm_library_with_coverage` instances. You can also target specific files using the `--files` flag.

### 3. Manual Instrumentation

For precise control or when automatic instrumentation is not sufficient,
you can manually add coverage `MARK` calls to your assembly files.

Use `COVERAGE_ASM_MANUAL_MARK(kTemp, kIndex)` to mark a basic block as
executed.

*   `kTemp`: A temporary register that will be clobbered.
*   `kIndex`: An arbitrary integer; the autogeneration tool will automatically reassign a unique, sequential index.

#### 3.1. Refresh Autogen Markers

The instrumentation tool (see Section 2.1) should be executed to update counter indices.

It skips inserting generated markers into basic blocks that have been manually instrumented.

The tool provides a visual representation of the counter assignments, which you can use for verification.

### 4. Test with Coverage

Once the setup steps are complete, you can generate a coverage report using the `bazel coverage` command.

For example:

```shell
./bazelisk.sh coverage --config=ot_coverage \
  //sw/device/tests:crt_test_fpga_cw340_test_rom

genhtml -o /tmp/$USER/coverage --ignore-errors inconsistent \
  bazel-out/_coverage/_coverage_report.dat

# ...
# Processing file sw/device/lib/crt/crt.S
#   lines=51 hit=51 functions=2 hit=2
# ...
```
