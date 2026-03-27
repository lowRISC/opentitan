# OTBN Coverage

Coverage for the OpenTitan Big Number (OTBN) accelerator is measured through the
OTBN simulator (`otbnsim`). Unlike C or RISC-V assembly, which require
instrumentation of the code itself, OTBN coverage is non-invasive and is
collected during simulation.

## Program Counter Tracking

When a test executes OTBN application code, the simulator tracks every
instruction executed by the processor.

The `ExecutionStats` class within the simulator maintains a **coverage map**
indexed by the program counter (PC). Every time an instruction at a specific PC
is executed, the corresponding counter in the map is incremented.

## OTBN Source Mapping

To produce a human-readable coverage report, the simulator must correlate
executed PCs with the original assembly source lines.

This is achieved using **DWARF debug information** produced by the OTBN
assembler. The simulator's `ExecutionStatAnalyzer` reads the ELF binary of the
OTBN application and iterates through the DWARF line programs to build a mapping
between instruction addresses and `(file, line_number)` pairs.

## LCOV Report Integration

If the `COVERAGE_OUTPUT_FILE` environment variable is set (which is done
automatically by the `bazel coverage` command), the simulator will dump the
collected coverage data in the standard LCOV format upon completion.

Because this data is in the standard LCOV format, it can be seamlessly merged
with coverage reports from C and RISC-V assembly code using host-side tooling,
providing a unified view of the entire test's coverage.

## Known Limitations

-   **Label Coverage:** Unlike Ibex assembly coverage, OTBN labels are typically
    marked as "skipped" in the report. This is because OTBN coverage relies on
    line-number mappings from the program counter (PC) stored in the DWARF debug
    information, which only covers executable instructions and not the preceding
    labels.
-   **Function Coverage:** Function-level coverage is not available for OTBN
    code. Because OTBN assembly typically does not use function-typed labels
    (e.g., `.type name, @function`), the simulator cannot reliably distinguish
    function entry points from normal jump labels, preventing the calculation of
    per-function execution metrics.
-   **IMEM and DMEM Address Overlap:** Both OTBN instruction memory (IMEM) and
    data memory (DMEM) start at address `0`. This can lead to cases where source
    lines containing instructions that are placed in DMEM (e.g., in a `.data` or
    `.bss` section) are incorrectly reported as covered if the corresponding
    address in IMEM is executed. In practice, it is atypical to place executable
    instructions in OTBN data sections, so this overlap has minimal impact on
    report accuracy.
