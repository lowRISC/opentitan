---
title: "Earlgrey Chip DV document"
---

## Goals
* **DV**
  * Verify `top_earlgrey` features by running dynamic simulations with a SV/UVM based testbench.
  * Verify the integration of all pre-verified IPs instantiated in the chip.
  * Verify the integration and the internal design of non-pre-verified IPs instantiated in the chip.
  * Verify system level scenarios for correctness of our design assumptions and behavior.
  * Verify the full chip configuration and memory address space by running the automated tests.
  * Stress test the XBAR structures in the chip.
* **FPV**
  * Verify the connectivity of signals (that are excluded from functional DV above) from point A to point B.
  * Secure verification
    * Check for leakage of secure data into unsecure locations / paths and vice-versa using the Cadence SPV tool.

## Current status
* [Design & verification stage]({{< relref "hw" >}})
  * [HW development stages]({{< relref "doc/project/development_stages.md" >}})
* [Simulation results](https://reports.opentitan.org/hw/top_earlgrey/dv/latest/results.html)

## Design features
For detailed information on `top_earlgrey` design features, please see the [Earl Grey Top Level Specification]({{< relref "hw/top_earlgrey/doc" >}}).

## Testbench architecture
The `top_earlgrey` chip level testbench has been constructed based on the [CIP testbench architecture]({{< relref "hw/dv/sv/cip_lib/doc" >}}).

### Block diagram
TBD

### Top level testbench
Top level testbench is located at `hw/ip/top_earlgrey/dv/tb/tb.sv`.
It instantiates the `top_earlgrey` DUT module `hw/top_earlgrey/rtl/top_earlgrey_asic.sv`.
In addition, it instantiates the following interfaces, connects them to the DUT and sets their handle into `uvm_config_db`:
* [Clock and reset interface]({{< relref "hw/dv/sv/common_ifs" >}})
  * Main clock as well as USB clock
* [TileLink host interface]({{< relref "hw/dv/sv/tl_agent/README.md" >}})
  * This is connected to the CPU's data port.
* [JTAG interface]()
* SPI interface
* UART interface
* SW logger inteface (for boot_rom as well as the test SW)
* SW test status monitor
* Backdoor memory interfaces (for ROM, SRAM and the flask banks)
* Individual control pins:
  * Bootstrap
  * JTAG/SPI switch
  * SRST_N

### Common DV utility components
The following utilities provide generic helper tasks and functions to perform activities that are common across the project:
* [dv_utils_pkg]({{< relref "hw/dv/sv/dv_utils/README.md" >}})
* [csr_utils_pkg]({{< relref "hw/dv/sv/csr_utils/README.md" >}})

### Global types & methods
All common types and methods defined at the package level can be found in the `chip_env_pkg`.
Some of them in use are:
```systemverilog
[list a few parameters, types & methods; no need to mention all]
```

### TL_agent
The full chip testbench instantiates (already handled in CIP base env) the [tl_agent]({{< relref "hw/dv/sv/tl_agent/README.md" >}}) which provides the ability to drive and independently monitor random traffic via TL host interface into CHIP device.

###  UART Agent
[Describe here or add link to its README]

###  SPI Agent
[Describe here or add link to its README]

###  JTAG Agent
[Describe here or add link to its README]

###  I2C Agent
[Describe here or add link to its README]

###  USB20 Agent
[Describe here or add link to its README]

### UVM RAL Model
The CHIP RAL model is created with the [`ralgen`]({{< relref "hw/dv/tools/ralgen/README.md" >}}) FuseSoC generator script automatically when the simulation is at the build stage.

It can be created manually (separately) by running `make` in the the `hw/` area.

### Reference models

### Testbench configurations

#### Stub CPU mode

#### Bare-metal SW test mode

#### XBAR integration mode

### Stimulus strategy
#### Test sequences
All test sequences reside in `hw/ip/chip/dv/env/seq_lib`.
The `chip_base_vseq` virtual sequence is extended from `cip_base_vseq` and serves as a starting point.
All test sequences are extended from `chip_base_vseq`.
It provides commonly used handles, variables, functions and tasks that the test sequences can simple use / call.
Some of the most commonly used tasks / functions are as follows:
* task 1:
* task 2:

#### Functional coverage
To ensure high quality constrained random stimulus, it is necessary to develop a functional coverage model.
The following covergroups have been developed to prove that the test intent has been adequately met:
* cg1:
* cg2:

### Self-checking strategy
#### Scoreboard
The `chip_scoreboard` is primarily used for end to end checking.
It creates the following analysis ports to retrieve the data monitored by corresponding interface agents:
* analysis port1:
* analysis port2:
<!-- explain inputs monitored, flow of data and outputs checked -->

#### Assertions
* TLUL assertions: The `tb/chip_bind.sv` binds the `tlul_assert` [assertions]({{< relref "hw/ip/tlul/doc/TlulProtocolChecker.md" >}}) to the IP to ensure TileLink interface protocol compliance.
* Unknown checks on DUT outputs: The RTL has assertions to ensure all outputs are initialized to known values after coming out of reset.
* assert prop 1:
* assert prop 2:

## Building and running tests
DV simulations for `top_earlgrey` are run with the [`dvsim`]() tool.
Please take a look at the link for detailed information on the usage, capabilities, features and known issues.
The basic UART transmit and receive test can be run with the following command:
```console
$ ./util/dvsim/dvsim.py hw/top_earlgrey/dv/chip_sim_cfg.hjson -i chip_uart_tx_rx
```
For a list of available tests  to run, please see the 'Tests' column in the [DV plan]({{< relref "#dv_plan" >}}) below.

## Regressions

### Sanity

### SW access

### Nightly

## DV plan
{{< incGenFromIpDesc "../../data/chip_testplan.hjson" "testplan" >}}
