---
title: "I2C DV Plan"
---

## Goals
* **DV**
  * Verify all I2C IP features by running dynamic simulations with a SV/UVM based testbench
  * Develop and run all tests based on the [testplan](#testplan) below towards closing code and functional coverage on the IP and all of its sub-modules
* **FPV**
  * Verify TileLink device protocol compliance with an SVA based testbench

## Current status
* [Design & verification stage]({{< relref "doc/project/hw_dashboard" >}})
  * [HW development stages]({{< relref "doc/project/hw_stages.md" >}})
* DV regression results dashboard (link TBD)

## Design features
For detailed information on I2C design features, please see the
[I2C design specification]({{< relref "hw/ip/i2c/doc" >}}).

## Testbench architecture
I2C testbench has been constructed based on the
[CIP testbench architecture]({{< relref "hw/dv/sv/cip_lib/doc" >}}).

### Block diagram
![Block diagram](tb.svg)

### Top level testbench
Top level testbench is located at `hw/ip/i2c/dv/tb/tb.sv`. It instantiates the I2C DUT module `hw/ip/i2c/rtl/i2c.sv`.
In addition, it instantiates the following interfaces, connects them to the DUT and sets their handle into `uvm_config_db`:
* [Clock and reset interface]({{< relref "hw/dv/sv/common_ifs" >}})
* [TileLink host interface]({{< relref "hw/dv/sv/tl_agent/README.md" >}})
* I2C IOs
* Interrupts ([`pins_if`]({{< relref "hw/dv/sv/common_ifs" >}}))

### Common DV utility components
The following utilities provide generic helper tasks and functions to perform activities that are common across the project:
* [common_ifs]({{< relref "hw/dv/sv/common_ifs" >}})
* [dv_utils_pkg]({{< relref "hw/dv/sv/dv_utils/README.md" >}})
* [csr_utils_pkg]({{< relref "hw/dv/sv/csr_utils/README.md" >}})

### Global types & methods
All common types and methods defined at the package level can be found in
`i2c_env_pkg`. Some of them in use are:
```systemverilog
parameter uint I2C_FMT_FIFO_DEPTH = 32;
parameter uint I2C_RX_FIFO_DEPTH  = 32;
parameter uint I2C_ADDR_MAP_SIZE  = 128;
```

### TL_agent
I2C instantiates (already handled in CIP base env) [tl_agent]({{< relref "hw/dv/sv/tl_agent/README.md" >}})
which provides the ability to drive and independently monitor random traffic via
TL host interface into I2C device.

### I2C agent
[describe or provide link to I2C agent documentation]

### UVM RAL Model
The I2C RAL model is created with the `hw/dv/tools/gen_ral_pkg.py` wrapper script at the start of the simulation automatically and is placed in the build area, along with a corresponding `fusesoc` core file.
The wrapper script invokes the [regtool.py]({{< relref "util/reggen/README.md" >}}) script from within to generate the RAL model.

It can be created manually by running `make ral` command from the `dv` area.

### Stimulus strategy
#### Test sequences
All test sequences reside in `hw/ip/i2c/dv/env/seq_lib`.
The `i2c_base_vseq` virtual sequence is extended from `cip_base_vseq` and serves as a starting point.
All test sequences are extended from `i2c_base_vseq`.
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
The `i2c_scoreboard` is primarily used for end to end checking.
It creates the following analysis ports to retrieve the data monitored by corresponding interface agents:
* analysis port1:
* analysis port2:

#### Assertions
* TLUL assertions: The `tb/i2c_bind.sv` binds the `tlul_assert` [assertions]({{< relref "hw/ip/tlul/doc/TlulProtocolChecker.md" >}}) to the IP to ensure TileLink interface protocol compliance.
* Unknown checks on DUT outputs: The RTL has assertions to ensure all outputs are initialized to known values after coming out of reset.
* assertion 1
* assertion 2

## Building and running tests
We are using our in-house developed [regression tool]({{< relref "hw/dv/tools/README.md" >}}) for building and running our tests and regressions.
Please take a look at the link for detailed information on the usage, capabilities, features and known issues.
Here's how to run a basic sanity test:
```console
$ cd hw/ip/foo/dv
$ make TEST_NAME=i2c_sanity
```

## Testplan
{{< testplan "hw/ip/i2c/data/i2c_testplan.hjson" >}}
