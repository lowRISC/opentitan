---
title: "Design Verification Setup"
aliases:
    - /doc/ug/getting_started_dv
---

_Before following this guide, make sure you've followed the [dependency installation and software build instructions]({{< relref "getting_started" >}})._

This document aims to enable a contributor to get started with a design verification (DV) effort within the OpenTitan project.
While most of the focus is on development of a testbench from scratch, it should also be useful to understand how to contribute to an existing effort.
Please refer to the [DV methodology]({{< relref "doc/ug/dv_methodology" >}}) document for information on how design verification is done in OpenTitan.

## Stages of DV

The life stages of a design / DV effort within the OpenTitan are described in the [Hardware Development Stages]({{< relref "doc/project/development_stages.md" >}}) document.
It separates the life of DV into three broad stages: Initial Work, Under Test and Testing Complete.
This document attempts to give guidance on how to get going with the first stage and have a smooth transition into the Under Test stage.
They are not hard and fast rules but methods we have seen work well in the project.
DV indeed cannot begin until the design has transitioned from Specification to the Development stage first.
The design specification, once available, is used as a starting point.

## Getting Started

The very first thing to do in any DV effort is to [document the plan]({{< relref "doc/ug/dv_methodology#documentation" >}}) detailing the overall effort.
This is done in conjunction with developing the initial testbench.
It is recommended to use the [uvmdvgen]({{< relref "util/uvmdvgen/doc" >}}) tool, which serves both needs.

The `uvmdvgen` tool provides the ability to generate the outputs in a specific directory.
This should be set to the root of the DUT directory where the `rtl` directory exists.
When the tool is run, it creates a `dv` directory, along with `data` and `doc` directories.
The `dv` directory is where the complete testbench along with the collaterals to build and run tests can be found.
It puts the documentation sources in `doc` and `data` directories respectively (which also exist alongside the `rtl` directory).
It is recommended to grep for 'TODO' at this stage in all of these generated files to make some of the required fixes right way.
One of these for example, is to create appropriate interfaces for the DUT-specific IOs and have them connected in the testbench (`dv/tb/tb.sv`).

## Documentation and Initial Review

The skeleton [DV document]({{< relref "doc/ug/dv_methodology#dv-document" >}}) and the [Hjson testplan]({{< relref "doc/ug/dv_methodology#testplan" >}}) should be addressed first.
The DV documentation is not expected to be completed in full detail at this point.
However, it is expected to list all the verification components needed and depict the planned testbench as a block diagram.
Under the 'design verification' directory in the OpenTitan team drive, some sample testbench block diagrams are available in the `.svg` format, which can be used as a template.
The Hjson testplan, on the other hand, is required to be completed.
Please refer to the [testplanner tool]({{< relref "util/dvsim/doc/testplanner" >}}) documentation for additional details on how to write the Hjson testplan.
Once done, these documents are to be reviewed with the designer(s) and other project members for completeness and clarity.

## UVM RAL Model

Before running any test, the [UVM RAL model]({{< relref "doc/ug/dv_methodology#uvm-register-abstraction-layer-ral-model" >}}) needs to exist (if the design contains CSRs).
The [DV simulation flow]({{< relref "hw/dv/tools/doc" >}}) has been updated to generate the RAL model automatically at the start of the simulation.
As such, nothing extra needs to be done.
It can be created manually by invoking [`regtool`]({{< relref "util/reggen/doc" >}}):
```console
$ util/regtool.py -s -t /path-to-dv /path-to-module/data/<dut>.hjson
```

The generated file is placed in the simulation build scratch area instead of being checked in.

## Supported Simulators

The use of advanced verification constructs such as SystemVerilog classes (on which UVM is based on) requires commercial simulators.
The [DV simulation flow]({{< relref "hw/dv/tools/doc" >}}) fully supports Synopsys VCS.
There is support for Cadence Xcelium as well, which is being slowly ramped up.

## Building and Running Tests

The `uvmdvgen` tool provides an empty shell sequence at `dv/env/seq_lib/<dut>_sanity_vseq.sv` for developing the sanity test.
The sanity test can be run as-is by invoking `dvsim.py`, as a "hello world" step to bring the DUT out of reset.
```console
$ util/dvsim/dvsim.py path/to/<dut>_sim_cfg.hjson -i <dut>_sanity [--waves <format>] [--tool xcelium]
```

The generated initial testbench is not expected to compile and elaborate successfully right away.
There may be additional fixes required, which can hopefully be identified easily.
Once the testbench compiles and elaborates without any errors or warnings, the sanity sequence can be developed further to access a major datapath and test the basic functionality of the DUT.

VCS is used as the default simulator. It can be switched to Xcelium by setting `--tool xcelium` on the command line.

To dump waves from the simulation, pass the `--waves <format>` argument to `dvsim.py`.
If you are using Verdi for waveform viewing, then '--waves fsdb' is probably the best option. For use with other viewers, '--waves shm' is probably the best choice for Xcelium, and '--waves vpd' with vcs.

Please refer to the [DV simulation flow]({{< relref "hw/dv/tools/doc" >}}) for additional details.

The `uvmdvgen` script also enables the user to run the full suite of CSR tests, if the DUT does have CSRs in it.
The most basic CSR power-on-reset check test can be run by invoking:
```console
$ util/dvsim/dvsim.py path/to/<dut>_sim_cfg.hjson -i <dut>_csr_hw_reset [--waves <format>] [--tool xcelium]
```
Please refer to [CSR utilities]({{< relref "hw/dv/sv/csr_utils/doc" >}}) for more information on how to add exclusions for the CSR tests.

## Full DV

Running the sanity and CSR suite of tests while making progress toward reaching the [V1 stage]({{< relref "doc/project/development_stages#hardware-verification-stages" >}}) should provide a good reference in terms of how to develop tests as outlined in the testplan and running and debugging them.
Please refer to the [checklist]({{< relref "doc/project/checklist" >}}) to understand the key requirements for progressing through the subsequent verification stages and final signoff.

The [UART DV](https://github.com/lowRISC/opentitan/tree/master/hw/ip/uart/dv) area can be used as a canonical example for making progress.
If it is not clear on how to proceed, feel free to file an issue requesting assistance.

## Reproduce a DV failure that CI reported

Follow these steps to reproduce the failure

1. Make sure the version of VCS is the same as the [one](https://github.com/lowRISC/opentitan-private-ci/blob/master/jobs.yml#L5) running in CI.

2. CI runs against an auto-generated merge commit, which effectively is generated by merging the pull request (PR) into the master branch.
This "merge" branch is updated automatically by GitHub whenever the PR branch is pushed, or when the PR is closed and re-open.
Retrieve this exact branch by running the following (assuming "upstream" is the name of your lowRISC/opentitan repository).
```console
$ git fetch upstream pull/<PR_number>/merge
$ git checkout -b <temp_branch> FETCH_HEAD
```

3. This is the command that CI runs for the smoke regression.
```console
$ util/dvsim/dvsim.py hw/top_earlgrey/dv/top_earlgrey_sim_cfgs.hjson -i smoke --fixed-seed=1
```
Since the CI runs tests with pseudo-random behaviour driven from 'seed' numbers, to be confident of reproducing the failure we must supply the exact seed that CI used.

Assume there is a failure in the `uart_smoke` test. To reproduce this with the DV simulation environment we use the following command, remembering to replace '<seed>' with the seed number, and to choose an appropriate waveform '<format>':


```console
$ util/dvsim/dvsim.py hw/ip/uart/dv/uart_sim_cfg.hjson -i uart_smoke --fixed-seed=<seed> [--waves <format>]
```

It is recommended to use '--waves fsdb' if you are using Verdi, or '--waves vpd' if you are using vcs but a different waveform viewer. With Xcelium ('--tool xcelium') but not Verdi, then '--waves shm' is the preferred format.

For maximal portability, the standard 'vcd' format is supported by all simulators and waveform viewers, but please be forewarned that vcd files can become extremely large and are generally best avoided.
