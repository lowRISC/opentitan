---
title: "FLASH_CTRL DV Plan"
---

## Goals
* **DV**
  * Verify all FLASH_CTRL IP features by running dynamic simulations with a SV/UVM based testbench
  * Develop and run all tests based on the [testplan](#testplan) below towards closing code and functional coverage on the IP and all of its sub-modules
* **FPV**
  * Verify TileLink device protocol compliance with an SVA based testbench

## Current status
* [Design & verification stage]({{< relref "hw" >}})
  * [HW development stages]({{< relref "doc/project/development_stages" >}})
* [Simulation results](https://reports.opentitan.org/hw/ip/flash_ctrl/dv/latest/results.html)

## Design features
For detailed information on FLASH_CTRL design features, please see the [FLASH_CTRL HWIP technical specification]({{< relref "hw/ip/flash_ctrl/doc" >}}).
The design under test is a wrapper that instantiates the flash protocol controller, the flash phy controller and the TLUL SRAM adapter.
This wrapper is currently maintained as a part of the DV testbench tentatively - its reorganization is under review.

## Testbench architecture
FLASH_CTRL testbench has been constructed based on the [CIP testbench architecture]({{< relref "hw/dv/sv/cip_lib/doc" >}}).

### Block diagram
![Block diagram](tb.svg)

### Top level testbench
Top level testbench is located at `hw/ip/flash_ctrl/dv/tb/tb.sv`. It instantiates the FLASH_CTRL DUT module `hw/ip/flash_ctrl/rtl/flash_ctrl.sv`.
In addition, it instantiates the following interfaces, connects them to the DUT and sets their handle into `uvm_config_db`:
* [Clock and reset interface]({{< relref "hw/dv/sv/common_ifs" >}})
* [TileLink host interface for the flash controller]({{< relref "hw/dv/sv/tl_agent/README.md" >}})
* [TileLink host interface for the eflash]({{< relref "hw/dv/sv/tl_agent/README.md" >}})
* Interrupts ([`pins_if`]({{< relref "hw/dv/sv/common_ifs" >}})
* Alerts ([`pins_if`]({{< relref "hw/dv/sv/common_ifs" >}})

### Common DV utility components
The following utilities provide generic helper tasks and functions to perform activities that are common across the project:
* [dv_utils_pkg]({{< relref "hw/dv/sv/dv_utils/README.md" >}})
* [csr_utils_pkg]({{< relref "hw/dv/sv/csr_utils/README.md" >}})

### Global types & methods
All common types and methods defined at the package level can be found in
`flash_ctrl_env_pkg`. Some of them in use are:
```systemverilog
[list a few parameters, types & methods; no need to mention all]
```
### TL_agent
FLASH_CTRL testbench instantiates (already handled in CIP base env) [tl_agent]({{< relref "hw/dv/sv/tl_agent/README.md" >}})
which provides the ability to drive and independently monitor random traffic via
TL host interface into FLASH_CTRL device.

### UVM RAL Model
The FLASH_CTRL RAL model is created with the [`ralgen`]({{< relref "hw/dv/tools/ralgen/README.md" >}}) FuseSoC generator script automatically when the simulation is at the build stage.

It can be created manually (separately) by running `make` in the the `hw/` area.

### Stimulus strategy
#### Test sequences
All test sequences reside in `hw/ip/flash_ctrl/dv/env/seq_lib`.
The `flash_ctrl_base_vseq` virtual sequence is extended from `cip_base_vseq` and serves as a starting point.
All test sequences are extended from `flash_ctrl_base_vseq`.
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
The `flash_ctrl_scoreboard` is primarily used for end to end checking.
It creates the following analysis ports to retrieve the data monitored by corresponding interface agents:
* analysis port1:
* analysis port2:
<!-- explain inputs monitored, flow of data and outputs checked -->

#### Assertions
* TLUL assertions: The `tb/flash_ctrl_bind.sv` binds the `tlul_assert` [assertions]({{< relref "hw/ip/tlul/doc/TlulProtocolChecker.md" >}}) to the IP to ensure TileLink interface protocol compliance.
* Unknown checks on DUT outputs: The RTL has assertions to ensure all outputs are initialized to known values after coming out of reset.
* assert prop 1:
* assert prop 2:

## Building and running tests
We are using our in-house developed [regression tool]({{< relref "hw/dv/tools/README.md" >}}) for building and running our tests and regressions.
Please take a look at the link for detailed information on the usage, capabilities, features and known issues.
Here's how to run a basic sanity test:
```console
$ cd hw/ip/flash_ctrl/dv
$ make TEST_NAME=flash_ctrl_sanity
```

## Testplan
{{</* testplan "hw/ip/flash_ctrl/data/flash_ctrl_testplan.hjson" */>}}
