---
title: "Signoff Checklist"
---

This document explains the recommended checklist items to review when transitioning from one [Development Stage]({{<relref "/doc/project/development_stages.md" >}}) to another, for design, verification, and [software device interface function (DIF)]({{< relref "doc/rm/device_interface_functions.md" >}}) stages.
It is expected that the items in each stage (D1, V1, S1, etc) are completed.

## D1

For a transition from D0 to D1, the following items are expected be completed.

### SPEC_COMPLETE

Specification mostly (90%) complete, all features are defined.
Specification is submitted into the repo as a markdown document.
It is acceptable to make changes for further clarification or more details after the D1 stage.

### CSR_DEFINED

The CSRs required to implement the primary programming model are defined.
The Hjson file defining the CSRs is checked into the repository.
It is acceptable to add or modify registers during the D2 stage in order to complete implementation.

### CLKRST_CONNECTED

Clock(s)/Reset(s) connected to all sub-modules.

### IP_TOP

Unit `.sv` exists, meet comportability requirements.

### IP_INSTANTIABLE

Unit is able to be instantiated and bound in top level RTL.
The design must compile and elaborate cleanly without errors.
The unit must not break top level functionality such as propagating X through TL-UL interface, continuously asserting the interrupts, or creating undesired TL-UL transactions.

### PHYSICAL_MACROS_DEFINED_80

All expected memories identified, representative macros instantiated.
All other physical elements (analog components, pads, etc) are identified and represented with a behavioral model.
It is acceptable to make changes to these physical macros after the D1 stage as long as they do not have a large impact on the expected resulting area (roughly "80% accurate").

### FUNC_IMPLEMENTED

Mainline functional path is implemented to allow for a basic functionality test by verification.
("Feature complete" is the target for D2 status.)

### ASSERT_KNOWN_ADDED

All the outputs of the IP have `ASSERT_KNOWN` assertions.

### LINT_SETUP

Lint run setup, compiles and runs. It is acceptable to have lint errors and
warnings at this stage.

## D2

### NEW_FEATURES

Any new features added since D1 are documented, reviewed with DV/SW/FPGA.
The GitHub Issue, Pull Request, or RFC where the feature was discussed should be linked in the `Notes` section.

### BLOCK_DIAGRAM

Block diagrams updated.

### DOC_INTERFACE

Documented non-registered block interfaces.

### MISSING_FUNC

Documented the missing functionalities.

### FEATURE_FROZEN

Feature requests for this IP version are frozen at this time.

### FEATURE_COMPLETE

All features specified have been completed.

### AREA_CHECK

Area check completed either on FPGA or on Design Compiler.

### PORT_FROZEN

100% ports. Port is frozen.

### ARCHITECTURE_FROZEN

100% architectural states exists (RAMs, CSRs, etc)

### REVIEW_TODO

Review and sign off TODOs.

### STYLE_X

Conforming to [style guide regarding X usage](https://github.com/lowRISC/style-guides/blob/master/VerilogCodingStyle.md#dont-cares-xs).

### LINT_PASS

Lint passes. Waiver reviewed.

### CDC_SETUP

CDC run set up. No must fix errors, waiver file created.

### FPGA_TIMING

FPGA synthesis timing meet (Fmax-10%) target or better

### CDC_SYNCMACRO

CDC Sync flops use behavioral synchronization macros(`prim_flop_2sync`) not
2flops.

### SEC_CM_IMPLEMENTED

Any appropriate security counter-measures documented and implemented.
For redundantly encoded FSMs, [the sparse-fsm-encode.py script](https://github.com/lowRISC/opentitan/blob/master/util/design/sparse-fsm-encode.py) must be used to generate the encoding.

### SEC_NON_RESET_FLOPS

A review of sensitive security-critical storage flops was completed.
Where appropriate, non-reset flops are used to store secure material.

### SEC_SHADOW_REGS

Shadow registers are implemented for all appropriate storage of critical control functions.

### SEC_RND_CNST

Compile-time random netlist constants (such as LFSR seeds or scrambling constants) are exposed to topgen via the `randtype` parameter mechanism in the comportable IP Hjson file.
Default random seeds and permutations for LFSRs can be generated with [the gen-lfsr-seed.py script](https://github.com/lowRISC/opentitan/blob/master/util/design/gen-lfsr-seed.py).
See also the related [GitHub issue #2229](https://github.com/lowRISC/opentitan/issues/2229).

## D3

### NEW_FEATURES_D3

Any approved new features since D2 documented, and reviewed with DV/SW/FPGA

### TODO_COMPLETE

Resolve all TODOs.

### LINT_COMPLETE

Lint clean. Lint waiver file reviewed and signed off by tech steering committe.

### CDC_COMPLETE

CDC clean. CDC waiver file reviewed and signed off by tech sterring committe.

### REVIEW_RTL

Hold Design Review: Hold a RTL sanity check review by an independent designer.

### REVIEW_DELETED_FF

Hold Design Review: Sign off deleted flops list (one last time).

### REVIEW_SW_CSR

Review Design Change with SW: Review CSRs

### REVIEW_SW_FATAL_ERR

Review Design Change with SW: Review Fatal Errors

### REVIEW_SW_CHANGE

Review Design Change with SW: Review other SW visible changes

### REVIEW_SW_ERRATA

Review Design Change with SW: Review known "Won't Fix" bugs and "Errata".

## V1

For a transition from V0 to V1, the following items are expected be completed.
Prefix "SIM" is applicable for simulation-based DV approach only, while "FPV" is for FPV approach only.

### DV_DOC_DRAFT_COMPLETED

- DV document drafted, indicating the overall DV strategy, intent and the testbench environment details with diagrams, details on TB, UVCs, checkers, scoreboard, interfaces, assertions, coverage objects (if applicable).
- Details may be missing since most items are not expected to be fully developed at this stage.

### DV_PLAN_COMPLETED

A fully completed DV plan written in Hjson, indicating the list of planned tests with descriptions indicating the goal of the test and optionally details on stimulus and the checking procedure.
A fully completed functional coverage plan written in Hjson, indicating the list of functional coverage points and coverage crosses with a description of what feature is covered by this coverpoint.

### TB_TOP_CREATED

- Top level testbench with DUT instantiated and following interfaces hooked up (as applicable): TileLink, clocks and resets, interrupts and major DUT interfaces.
- All interfaces may not be hooked up at this point. Inputs for which interfaces have not yet been created may be tied off to 0.

### PRELIMINARY_ASSERTION_CHECKS_ADDED

- All available interface assertion monitors hooked up (example: tlul_assert).

### SIM_TB_ENV_CREATED

- UVM environment created with major interface agents and UVCs connected and instantiated.
- TLM connections made from UVC monitors to the scoreboard.

### SIM_RAL_MODEL_GEN_AUTOMATED

RAL model is generated by using [regtool]({{< relref "/util/reggen/README.md" >}}) and instantiated in UVM environment.

### CSR_CHECK_GEN_AUTOMATED

CSR check is generated by using [regtool]({{< relref "/util/reggen/README.md" >}}) and bound in the TB environment.

### TB_GEN_AUTOMATED

Full testbench automation completed if applicable. This may be required for verifying multiple flavors of parameterized DUT designs.

### SIM_SANITY_TEST_PASSING

- Sanity test exercising a basic functionality of a major DUT datapath passing.
- What functionality to test and to what level may be governed by higher level (example: chip) integration requirements. These are to be captured when the DV plan is reviewed with the key stakeholders.

### SIM_CSR_MEM_TEST_SUITE_PASSING

CSR test suite added for ALL interfaces that have access to system memory map (JTAG, TL, etc.):
- HW reset test (test all resets)
- CSR read/write
- Bit Bash
- Aliasing

Memory test suite added for ALL interfaces that have access to system memory map (JTAG, TL, etc.) if the DUT has memories:
- Mem walk

Ensure all these tests verify back-2back access with zero delays, along with partial reads and partial writes.

### FPV_MAIN_ASSERTIONS_PROVEN

- Each input and each output of the module is part of at least one assertion.
- Assertions for main functional path are implemented and proven.

### SIM_ALT_TOOL_SETUP

Verify that the sanity test passes cleanly (with no warnings) with one additional tool apart from the primary tool selected for signoff.

### SIM_SANITY_REGRESSION_SETUP

Sanity regression set up for code health. A small suite of tests identified for running the sanity regression on. If the testbench has more than one compile-time configuration, then a sanity test for each configuration should be ideally selected.

### SIM_NIGHTLY_REGRESSION_SETUP

Nightly regression for running all tests with multiple random seeds (iterations) setup. Selecting the number of iterations for running each test is subjective - it depends on the failure rate and available compute resources. For starters, it is recommended to set iterations to 100 for each test. It may be trimmed down if the compute load is too high. As such, the goal should be to have the nightly regression finish overnight so that the results are available next morning for triage.

### FPV_REGRESSION_SETUP

Set up FPV regression by adding the module to `hw/formal/fpv_all` script.

### SIM_COVERAGE_MODEL_ADDED

- Structural coverage collection model checked in. This specifies what hierarchies and what types of coverage to collect. For example, pre-verified sub-mudules (including some `prim` components pre-verified thoroughly with FPV) can be black-boxed and only IO toggle coverage can be setup for those sub-modules for coverage collection.
- Functional coverage shell object created - this may not contain coverpoints or covergroups yet, but it is primed for use in post-V2 test development.

### PRE_VERIFIED_SUB_MODULES_V1

Sub-modules that are pre-verified with their own testbenches have already reached V1 or higher stage.

### TB_LINT_SETUP

[VeribleLint](https://google.github.io/verible/verilog_lint.html) for the testbench is [setup]({{< relref "hw/lint/doc/README.md" >}}) to run in nightly regression, with appropriate waivers.
* For DV testbench, an entry is expected to be added at `hw/<top-level-design>/lint/<top-level-design>_dv_lint_cfgs.hjson`
* For FPV testbench, an entry is expected to be added at `hw/<top-level-design>/lint/<top-level-design>_fpv_lint_cfgs.hjson`

### DESIGN_SPEC_REVIEWED

RTL (uArch) specification reviewed and signed off.

### DV_PLAN_REVIEWED

DV document & DV plan reviewed with key stakeholders - designer, design lead, DV lead, architects, higher level (chip) design and DV leads.

### STD_TEST_CATEGORIES_PLANNED

Following categories of post-V1 tests focused at in the DV plan review (as applicable):
- Security/error
- Power
- Performance
- Debug
- Stress

### V2_CHECKLIST_SCOPED

Reviewed V2 checklist to understand scope and estimate effort.

## V2

For a transition from V1 to V2, the following items are expected be completed.
Prefix "SIM" is applicable for simulation-based DV approach only, while "FPV" is for FPV approach only.

### DESIGN_DELTAS_CAPTURED_V2

It is possible for the design to have undergone some changes since the DV document and DV plan was reviewed prior to V1 stage. Please ensure that those deltas have been captured adequately in the DV document and the DV plan documents.

### DV_DOC_COMPLETED

DV document is fully completed in terms of content.

### FUNCTIONAL_COVERAGE_PLAN_IMPLEMENTED

All coverage points have been written and implemented

### ALL_INTERFACES_EXERCISED

- For simulation based DV, all interfaces including sidebands have been connected and exercised.
- For the FPV approach, all interfaces including sidebands are asserted.

### ALL_ASSERTION_CHECKS_ADDED

All planned assertions have been written and enabled.

### SIM_TB_ENV_COMPLETED

UVM environment fully developed with end-2-end checks in scoreboard enabled.

### SIM_ALL_TESTS_PASSING

All tests in the DV plan written and passing with at least one random seed.

### FPV_ALL_ASSERTIONS_WRITTEN

- All assertions are implemented and above 90% proven.
- Each output of the module contains at least one forward and one backward assertion check.
- FPV module converges within reasonable runtime.

### FPV_ALL_ASSUMPTIONS_REVIEWED

All assumptions are implemented and reviewed.

### SIM_FW_SIMULATED

For chip-level, verified pieces of FW code (DIFs) in simulaton.

### SIM_NIGHTLY_REGRESSION_V2

Nightly regression with multiple random seeds passing: 90%

### SIM_CODE_COVERAGE_V2

Code coverage requirements: line, toggle, fsm (state & transition), branch, assertion: 90%

### SIM_FUNCTIONAL_COVERAGE_V2

Functional coverage requirements: coverpoints: 100%, crosses: 75%

### FPV_CODE_COVERAGE_V2

Code coverage requirements: branch, statement, functional: 90%

### FPV_COI_COVERAGE_V2

COI coverage requirements: 75%

### TB_LINT_PASS

Lint for the testbench passes. Waiver reviewed.

### NO_HIGH_PRIORITY_ISSUES_PENDING

Ensure that all high priority (tagged P0 and P1) design bugs have been addressed and closed. If the bugs were found elsewhere, ensure that they are reproduced deterministically in DV (through additional tests or by tweaking existing tests as needed) and the fixes are adequately verified.

### ALL_LOW_PRIORITY_ISSUES_ROOT_CAUSED

Ensure that all low priority (tagged P2 and P3) design bugs habe been root-caused. They may be deferred to post D2V2 for closure.

### PRE_VERIFIED_SUB_MODULES_V2

Sub-modules that are pre-verified with their own testbenches have already reached V2 or higher stage.

### V3_CHECKLIST_SCOPED

Reviewed V3 checklist to understand scope and estimate effort.

## V3

For a transition from V2 to V3, the following items are expected be completed.
Prefix "SIM" is applicable for simulation-based DV approach only, while "FPV" is for FPV approach only.

### DESIGN_DELTAS_CAPTURED_V3

It is possible for the design to undergo changes even at this stage (when it is expected to be mature). Please ensure that those new deltas have been captured adequately in the DV document and the DV plan documents.

### ALL_TODOS_RESOLVED

Ensure that the complete testbench code is free from TODOs.

### X_PROP_ANALYSIS_COMPLETED

X Propagation Analysis complete

### FPV_ASSERTIONS_PROVEN_AT_V3

- Assertion proven requirement: 100% of properties proven
- No undetermined or unreachable properties

### SIM_NIGHTLY_REGRESSION_AT_V3

Nightly regression with multiple random seeds passing: 100% (with 1 week minimum soak time)

### SIM_CODE_COVERAGE_AT_100

Code coverage requirements: line, toggle, fsm (state & transition), branch, assertion: 100%

### SIM_FUNCTIONAL_COVERAGE_AT_100

Functional coverage requirements: coverpoints: 100%, crosses: 100%

### FPV_CODE_COVERAGE_AT_100

Code coverage requirements: branch, statement, functional: 100%

### FPV_COI_COVERAGE_AT_100

COI coverage requirements: 100%

### NO_ISSUES_PENDING

Ensure that all design bugs have been addressed and closed.

### NO_TOOL_WARNINGS_THROWN

Clean up all compile-time and run-time warnings thrown by the simulator.

### TB_LINT_COMPLETE

Lint for the testbench is clean. Lint waiver file reviewed and signed off by tech steering committe.

### PRE_VERIFIED_SUB_MODULES_V3

Sub-modules that are pre-verified with their own testbenches have already reached V3 stage.

## S1

For a transition from S0 to S1, the following items are expected be completed.

### DIF_EXISTS

`dif_<ip>.h` and, optionally, `dif_<ip>.c` exist in `sw/device/lib/dif`.

### DIF_USED_IN_TREE

All existing in-tree code which uses the device, uses the device via the DIF.
There is no remaining driver code that directly uses the device outside of DIF code.

### DIF_TEST_UNIT

Software unit tests exist for the DIF in `sw/device/tests/dif` named `dif_<ip>_unittest.cc`.

### DIF_TEST_SMOKE

Smoke tests exist for the DIF in `sw/device/tests/dif` named `dif_<ip>_smoketest.c`.

This should perform a basic test of the main datapath of the hardware module by the embedded core, via the DIF, and should be able to be run on all OpenTitan platforms (including FPGA, simulation, and DV).
This test will be shared with DV.

Smoke tests are for diagnosing major issues in both software and hardware, and with this in mind, they should execute quickly.
Initially we expect this kind of test to be written by hardware designers for debugging issues during module development.
This happens long before a DIF is implemented, so there are no requirements on how these should work, though we suggest they are placed in `sw/device/tests/<ip>/<ip>.c` as this has been the convention until now.
Later, when a DIF is written, the DIF author is responsible for updating this test to use the DIF, and for moving this test into the aforementioned location.

## S2

For a transition from S1 to S2, the following items are expected be completed.

### DIF_FEATURES

DIF has functions to cover all specified hardware functionality.

### DIF_HW_USAGE_REVIEWED

The DIF's usage of its respective IP device has been reviewed by the device's hardware designer.

### DIF_HW_FEATURE_COMPLETE

The DIF's respective device IP is at least stage D2.

### DIF_HW_PARAMS

DIF uses automatically generated HW parameters and register definitions.

### DIF_DOC_HW

HW IP Programmer's guide references specific DIF APIs that can be used for operations.

### DIF_CODE_STYLE

DIF follows the DIF-specific guidelines in [`sw/device/lib/dif/README.md`]({{< relref "sw/device/lib/dif/README.md" >}}) and the OpenTitan C style guidelines.

### DIF_DV_TESTS

Chip-level DV testing for the IP using DIFs has been started.

### DIF_USED_TOCK

DIF has initial interface for use from Tock.

## S3

For a transition from S2 to S3, the following items are expected be completed.

### DIF_HW_DESIGN_COMPLETE

The DIF's respective device IP is at least stage D3.

### DIF_HW_VERIFICATION_COMPLETE

The DIF's respective device IP is at least stage V3.

### DIF_REVIEW_C_STABLE

Fully re-review C interface and implementation, with a view to the interface not changing in future.

### DIF_TEST_UNIT_COMPLETE

Unit tests cover (at least):

- Device Initialisation
- All Device FIFOs (including when empty, full, and adding data)
- All Device Registers
- All DIF Functions
- All DIF return codes

### DIF_TODO_COMPLETE

Ensure all DIF TODOs are complete.

### DIF_REVIEW_TOCK_STABLE

Fully re-review Tock interface, with a view to the interface not changing in future.
