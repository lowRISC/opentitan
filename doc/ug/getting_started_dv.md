---
title: "Getting Started with an OpenTitan Design Verification"
---

This document aims to enable a contributor to get started with a design verification (DV) effort within the OpenTitan project.
While most of the focus is on development of a testbench from scratch, it should also be useful to understand how to contribute to an existing effort.
Please refer to the [DV methodology]({{< relref "dv_methodology.md" >}}) document for information on how design verification is done in OpenTitan.

## Stages of DV

The life stages of a design / DV effort within the OpenTitan are described in the [Hardware Development Stages]({{< relref "doc/project/hw_stages.md" >}}) document.
It separates the life of DV into three broad stages: Initial Work, Under Test and Testing Complete.
This document attempts to give guidance on how to get going with the first stage and have a smooth transition into the Under Test stage.
They are not hard and fast rules but methods we have seen work well in the project.
DV indeed cannot begin until the design has transitioned from Specification to the Development stage first.
The design specification, once available, is used as a starting point.

## Getting Started

The very first thing to do in any DV effort is to [document the plan]({{< relref "dv_methodology.md#documentation" >}}) detailing the overall effort.
This is done in conjunction with developing the initial testbench.
It is recommended to use the [uvmdvgen]({{< relref "util/uvmdvgen/README.md" >}}) tool, which serves both needs.

The `uvmdvgen` tool provides the ability to generate the outputs in a specific directory.
This should be set to the root of the DUT directory where the `rtl` directory exists.
When the tool is run, it creates a `dv` directory, along with `data` and `doc` directories.
The `dv` directory is where the complete testbench along with the collaterals to build and run tests can be found.
It puts the documentation sources in `doc` and `data` directories respectively (which also exist alongside the `rtl` directory).
It is recommended to grep for 'TODO' at this stage in all of these generated files to make some of the required fixes right way.
One of these for example, is to create appropriate interfaces for the DUT-specific IOs and have them connected in the testbench (`dv/tb/tb.sv`).

## Documentation and Initial Review

The skeleton [DV plan]({{< relref "dv_methodology.md#dv-plan" >}}) and the [Hjson testplan]({{< relref "dv_methodology.md#testplan" >}}) should be addressed first.
The DV plan documentation is not expected to be completed in full detail at this point.
However, it is expected to list all the verification components needed and depict the planned testbench as a block diagram.
Under the 'design verification' directory in the OpenTitan team drive, some sample testbench block diagrams are available in the `.svg` format, which can be used as a template.
The Hjson testplan on the other hand, is required to be completed.
Please refer to the [testplanner tool]({{< relref "util/testplanner/README.md" >}}) documentation for additional details on how to write the Hjson testplan.
Once done, these documents are to be reviewed with the designer(s) and other project members for completeness and clarity.

## UVM RAL Model

Before running any test, the [UVM RAL model]({{< relref "dv_methodology.md#uvm-register-abstraction-layer-ral-model" >}}) needs to exist (if the design contains CSRs).
The [DV simulation flow]({{< relref "hw/dv/tools/README.md" >}}) has been updated to generate the RAL model automatically at the start of the simulation.
As such, nothing extra needs to be done.
A hook for generating it is already provided in the generated `dv/Makefile`.
It can be created manually by simply navigating to the `dv` directory and invoking the command:
```console
$ cd path-to-dv
$ make ral
```

The generated file is placed in the simulation build scratch area instead of being checked in.

## Supported Simulators

The use of advanced verification constructs such as SystemVerilog classes (on which UVM is based on) requires commercial simulators.
The [DV simulation flow]({{< relref "hw/dv/tools/README.md" >}}) fully supports Synopsys VCS.
There is support for Cadence Xcelium as well, which is being slowly ramped up.

## Building and Running Tests

The `uvmdvgen` tool provides an empty shell sequence at `dv/env/seq_lib/<ip>_sanity_vseq.sv` for developing the sanity test.
The sanity test can be run as-is by invoking `make`, as a "hello world" step to bring the DUT out of reset.
```console
$ cd path-to-dv
$ make [SIMULATOR=xcelium] [WAVES=1]
```

The generated initial testbench is not expected to compile and elaborate successfully right away.
There may be additional fixes required, which can be hopefully be identified easily.
Once the testbench compiles and elaborates without any errors or warnings, the sanity sequence can be developed further to access a major datapath and test the basic functionality of the DUT.

VCS is used as the default simulator.
It can be switched to Xcelium by setting `SIMULATOR=xcelium` on the command line.
The `WAVES=1` switch will cause an `fsdb` dump to be created from the test.
The Synopsys Verdi tool can be invoked (separately) to debug the waves.
Please refer to the [DV simulation flow]({{< relref "hw/dv/tools/README.md" >}}) for additional details.

The `uvmdvgen` script also provides a CSR suite of tests which can be run right out of the box.
The most basic CSR power-on-reset check test can be run by invoking:
```console
$ cd path-to-dv
$ make TEST_NAME=<dut>_csr_hw_reset [WAVES=1]
```
Please refer to [CSR utilities]({{< relref "hw/dv/sv/csr_utils/README" >}}) for more information on how to add exclusions for the CSR tests.

## Full DV

Running the sanity and CSR suite of tests while making progress toward reaching the [V1 stage]({{< relref "doc/project/hw_stages#hardware-verification-stages" >}}) should provide a good reference in terms of how to develop tests as outlined in the testplan and running and debugging them.
Please refer to the [checklist]({{< relref "doc/project/checklist" >}}) to understand the key requirements for progressing through the subsequent verification stages and final signoff.

The [UART DV](https://github.com/lowRISC/opentitan/tree/master/hw/ip/uart/dv) area can be used as a canonical example for making progress.
If it is not clear on how to proceed, feel free to file an issue requesting assistance.
