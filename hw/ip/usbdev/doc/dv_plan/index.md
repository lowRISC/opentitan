---
title: "USBDEV DV Plan"
---

## Goals
* **DV**
  * Verify all USBDEV IP features by running dynamic simulations with a SV/UVM based testbench.
  * Develop and run all tests based on the [testplan](#testplan) below towards closing code and functional coverage on the IP and all of its sub-modules.
    * Note that code and functional coverage goals are TBD due to pending evaluation of where / how to source a USB20 UVM VIP.
    * The decision is trending towards hooking up a cocotb (Python) based open source USB20 compliance test suite with this UVM environment.
* **FPV**
  * Verify TileLink device protocol compliance with an SVA based testbench.

## Current status
* [Design & verification stage]({{< relref "doc/project/hw_dashboard" >}})
  * [HW development stages]({{< relref "doc/project/hw_stages" >}})
* DV regression results dashboard (link TBD)

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
The USBDEV RAL model is created with the `hw/dv/tools/gen_ral_pkg.py` wrapper script at the start of the simulation automatically and is placed in the build area, along with a corresponding `fusesoc` core file.
The wrapper script invokes the [regtool.py]({{< relref "util/reggen/README.md" >}}) script from within to generate the RAL model.

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
Here's how to run a basic sanity test:
```console
$ cd hw/ip/usbdev/dv
$ make TEST_NAME=usbdev_sanity
```

## Testplan
{{< testplan "hw/ip/usbdev/data/usbdev_testplan.hjson" >}}
