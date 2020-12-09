---
title: "I2C DV document"
---

## Goals
* **DV**
  * Verify all I2C IP features by running dynamic simulations with a SV/UVM based testbench
  * Develop and run all tests based on the [DV plan](#dv-plan) below towards closing code and functional coverage on the IP and all of its sub-modules
* **FPV**
  * Verify TileLink device protocol compliance with an SVA based testbench

## Current status
* [Design & verification stage]({{< relref "hw" >}})
  * [HW development stages]({{< relref "doc/project/development_stages.md" >}})
* [Simulation results](https://reports.opentitan.org/hw/ip/i2c/dv/latest/results.html)

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
```

### TL_agent
I2C instantiates (already handled in CIP base env) [tl_agent]({{< relref "hw/dv/sv/tl_agent/README.md" >}})
which provides the ability to drive and independently monitor random traffic via
TL host interface into I2C device.

### I2C agent
I2C agent is configured to work device mode and implemented as [reactive agent](https://www.verilab.com/files/mastering_reactive_slaves.pdf)

### UVM RAL Model
The I2C RAL model is created with the [`ralgen`]({{< relref "hw/dv/tools/ralgen/README.md" >}}) FuseSoC generator script automatically when the simulation is at the build stage.

It can be created manually by invoking [`regtool`]({{< relref "util/reggen/README.md" >}}):

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
Here's how to run a smoke test:
```console
$ $REPO_TOP/util/dvsim/dvsim.py $REPO_TOP/hw/ip/i2c/dv/i2c_sim_cfg.hjson -i i2c_smoke
```

## DV plan
{{< testplan "hw/ip/i2c/data/i2c_testplan.hjson" >}}
