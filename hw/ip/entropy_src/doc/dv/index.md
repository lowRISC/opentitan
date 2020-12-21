---
title: "ENTROPY_SRC DV document"
---

## Goals
* **DV**
  * Verify all ENTROPY_SRC IP features by running dynamic simulations with a SV/UVM based testbench
  * Develop and run all tests based on the [DV plan](#dv-plan) below towards closing code and functional coverage on the IP and all of its sub-modules
* **FPV**
  * Verify TileLink device protocol compliance with an SVA based testbench

## Current status
* [Design & verification stage]({{< relref "hw" >}})
  * [HW development stages]({{< relref "doc/project/development_stages" >}})
* [Simulation results](https://reports.opentitan.org/hw/ip/entropy_src/dv/latest/results.html)

## Design features
For detailed information on ENTROPY_SRC design features, please see the [ENTROPY_SRC HWIP technical specification]({{< relref "hw/ip/entropy_src/doc" >}}).

## Testbench architecture
ENTROPY_SRC testbench has been constructed based on the [CIP testbench architecture]({{< relref "hw/dv/sv/cip_lib/doc" >}}).

### Block diagram
![Block diagram](entropy_src_tb.svg)

### Top level testbench
Top level testbench is located at `hw/ip/entropy_src/dv/tb/tb.sv`. It instantiates the ENTROPY_SRC DUT module `hw/ip/entropy_src/rtl/entropy_src.sv`.
In addition, it instantiates the following interfaces, connects them to the DUT and sets their handle into `uvm_config_db`:
* [Clock and reset interface]({{< relref "hw/dv/sv/common_ifs" >}})
* [TileLink host interface]({{< relref "hw/dv/sv/tl_agent/README.md" >}})
* ENTROPY_SRC IOs
* Interrupts ([`pins_if`]({{< relref "hw/dv/sv/common_ifs" >}})
* Alerts ([`pins_if`]({{< relref "hw/dv/sv/common_ifs" >}})
* Devmode ([`pins_if`]({{< relref "hw/dv/sv/common_ifs" >}})

### Common DV utility components
The following utilities provide generic helper tasks and functions to perform activities that are common across the project:
* [common_ifs]({{< relref "hw/dv/sv/common_ifs" >}})
* [dv_utils_pkg]({{< relref "hw/dv/sv/dv_utils/README.md" >}})
* [csr_utils_pkg]({{< relref "hw/dv/sv/csr_utils/README.md" >}})

<!--### Compile-time configurations
TODO-->

### Global types & methods
All common types and methods defined at the package level can be found in
`entropy_src_env_pkg`. Some of them in use are:
<!--TODO-->
```systemverilog
```

### TL_agent
ENTROPY_SRC testbench instantiates (already handled in CIP base env) [tl_agent]({{< relref "hw/dv/sv/tl_agent/README.md" >}})
which provides the ability to drive and independently monitor random traffic via
TL host interface into ENTROPY_SRC device.

###  Rng_agent
Entropy_src testbench instantiates this PUSH_pull_agent({{< relref "hw/dv/sv/push_pull_agent/README.md" >}}) which models the rng source.

###  Csrng_agent
Entropy_src testbench instantiates this push_PULL_agent({{< relref "hw/dv/sv/push_pull_agent/README.md" >}}) which models the csrng module.

### UVM RAL Model
The ENTROPY_SRC RAL model is created with the [`ralgen`]({{< relref "hw/dv/tools/ralgen/README.md" >}}) FuseSoC generator script automatically when the simulation is at the build stage.

It can be created manually (separately) by running `make` in the `hw/` area.

### Stimulus strategy
#### Test sequences
All test sequences reside in `hw/ip/entropy_src/dv/env/seq_lib`.
The `entropy_src_base_vseq` virtual sequence is extended from `cip_base_vseq` and serves as a starting point.
All test sequences are extended from `entropy_src_base_vseq`.
It provides commonly used handles, variables, functions and tasks that the test sequences can simple use / call.
Some of the most commonly used tasks / functions are as follows:
* entropy_src_init:     Initialize the ENTROPY_SRC module from the randomized environment variables in the config.

#### Functional coverage
To ensure high quality constrained random stimulus, it is necessary to develop a functional coverage model.
The following covergroups have been developed to prove that the test intent has been adequately met:
* common covergroup for interrupts `hw/dv/sv/cip_lib/cip_base_env_cov.sv`: Cover interrupt value, interrupt enable, intr_test, interrupt pin

### Self-checking strategy
#### Scoreboard
The `entropy_src_scoreboard` is primarily used for end to end checking.
It creates the following analysis ports to retrieve the data monitored by corresponding interface agents:
* tl_a_chan_fifo, tl_d_chan_fifo:  These 2 fifos provide transaction items at the end of Tilelink address channel and data channel respectively
* rng_fifo, csrng_fifo:   The rng_fifo provides transaction items from the predictor and the csrng_fifo provide actual post-entropy_src transaction items to compare

#### Assertions
* TLUL assertions: The `tb/entropy_src_bind.sv` binds the `tlul_assert` [assertions]({{< relref "hw/ip/tlul/doc/TlulProtocolChecker.md" >}}) to the IP to ensure TileLink interface protocol compliance.
* Unknown checks on DUT outputs: The RTL has assertions to ensure all outputs are initialized to known values after coming out of reset.

## Building and running tests
We are using our in-house developed [regression tool]({{< relref "hw/dv/tools/README.md" >}}) for building and running our tests and regressions.
Please take a look at the link for detailed information on the usage, capabilities, features and known issues.
Here's how to run a smoke test:
```console
$ cd hw/ip/entropy_src/dv
$ make TEST_NAME=entropy_src_smoke
```

## DV plan
{{< testplan "hw/ip/entropy_src/data/entropy_src_testplan.hjson" >}}
