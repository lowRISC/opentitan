---
title: "USBDEV DV document"
---

## Goals
* **DV**
  * Verify all USBDEV IP features by running dynamic simulations with a SV/UVM based testbench.
  * Develop and run all tests based on the [DV plan](#dv-plan) below towards closing code and functional coverage on the IP and all of its sub-modules.
    * Note that code and functional coverage goals are TBD due to pending evaluation of where / how to source a USB20 UVM VIP.
    * The decision is trending towards hooking up a cocotb (Python) based open source USB20 compliance test suite with this UVM environment.
* **FPV**
  * Verify TileLink device protocol compliance with an SVA based testbench.

## Current status
* [Design & verification stage]({{< relref "hw" >}})
  * [HW development stages]({{< relref "doc/project/development_stages" >}})
* [Simulation results](https://reports.opentitan.org/hw/ip/usbdev/dv/latest/results.html)

## Design features
For detailed information on USBDEV design features, please see the [USBDEV HWIP technical specification]({{< relref "hw/ip/usbdev/doc" >}}).

## Testbench architecture
USBDEV testbench has been constructed based on the [CIP testbench architecture]({{< relref "hw/dv/sv/cip_lib/doc" >}}).

### Block diagram
![Block diagram](tb.svg)

### Top level testbench
Top level testbench is located at `hw/ip/usbdev/dv/tb/tb.sv`.
It instantiates the USBDEV DUT module `hw/ip/usbdev/rtl/usbdev.sv`.
In addition, it instantiates the following interfaces, connects them to the DUT and sets their handle into `uvm_config_db`:
* [Clock and reset interface for the TL and USB domains]({{< relref "hw/dv/sv/common_ifs" >}})
* [TileLink host interface]({{< relref "hw/dv/sv/tl_agent/README.md" >}})
* USBDEV IOs
* Interrupts ([`pins_if`]({{< relref "hw/dv/sv/common_ifs" >}})

### Common DV utility components
The following utilities provide generic helper tasks and functions to perform activities that are common across the project:
* [dv_utils_pkg]({{< relref "hw/dv/sv/dv_utils/README.md" >}})
* [csr_utils_pkg]({{< relref "hw/dv/sv/csr_utils/README.md" >}})

### Compile-time configurations
None for now.

### Global types & methods
All common types and methods defined at the package level can be found in `usbdev_env_pkg`.
Some of them in use are:
```systemverilog
[list a few parameters, types & methods; no need to mention all]
```

### TL_agent
USBDEV testbench instantiates (already handled in CIP base env) [tl_agent]({{< relref "hw/dv/sv/tl_agent/README.md" >}}) which provides the ability to drive and independently monitor random traffic via TL host interface into USBDEV device.

###  USB20 Agent
The [usb20_agent]({{< relref "hw/dv/sv/usb20_agent/README.md" >}}) is currently a skeleton implementation.
It does not offer any functionality yet.

### UVM RAL Model
The USBDEV RAL model is created with the [`ralgen`]({{< relref "hw/dv/tools/ralgen/README.md" >}}) FuseSoC generator script automatically when the simulation is at the build stage.

It can be created manually by invoking [`regtool`]({{< relref "util/reggen/README.md" >}}):

### Reference models
There are no reference models in use currently.

### Stimulus strategy
#### Test sequences
All test sequences reside in `hw/ip/usbdev/dv/env/seq_lib`.
The `usbdev_base_vseq` virtual sequence is extended from `cip_base_vseq` and serves as a starting point.
All test sequences are extended from `usbdev_base_vseq`.
It provides commonly used handles, variables, functions and tasks that the test sequences can simple use / call.
Some of the most commonly used tasks / functions are as follows:
* `usbdev_init()`: Do basic USB device initialization.

#### Functional coverage
To ensure high quality constrained random stimulus, it is necessary to develop a functional coverage model.
The following covergroups have been developed to prove that the test intent has been adequately met:
* TBD

### Self-checking strategy
#### Scoreboard
The `usbdev_scoreboard` is primarily used for end to end checking.
It creates the following analysis ports to retrieve the data monitored by corresponding interface agents:
* TBD

#### Assertions
* TLUL assertions: The `tb/usbdev_bind.sv` binds the `tlul_assert` [assertions]({{< relref "hw/ip/tlul/doc/TlulProtocolChecker.md" >}}) to the IP to ensure TileLink interface protocol compliance.
* Unknown checks on DUT outputs: The RTL has assertions to ensure all outputs are initialized to known values after coming out of reset.
* TBD

## Building and running tests
We are using our in-house developed [regression tool]({{< relref "hw/dv/tools/README.md" >}}) for building and running our tests and regressions.
Please take a look at the link for detailed information on the usage, capabilities, features and known issues.
Here's how to run a smoke test:
```console
$ $REPO_TOP/util/dvsim/dvsim.py $REPO_TOP/hw/ip/usbdev/dv/usbdev_sim_cfg.hjson -i usbdev_smoke
```

## DV plan
{{< incGenFromIpDesc "../../data/usbdev_testplan.hjson" "testplan" >}}
