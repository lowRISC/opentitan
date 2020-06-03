---
title: "PATTGEN DV Plan"
---

<!-- Copy this file to hw/ip/pattgen/doc/pattgen_dv_plan.md and make changes as needed.
For convenience 'pattgen' in the document can be searched and replaced easily with the
desired IP (with case sensitivity!). Also, use the testbench block diagram
located at OpenTitan team drive / 'design verification'
as a starting point and modify it to reflect your pattgen testbench and save it
to hw/ip/pattgen/doc/tb.svg. It should get linked and rendered under the block
diagram section below. Please update / modify / remove sections below as
applicable. Once done, remove this comment before making a PR. -->

## Goals
* **DV**
  * Verify all PATTGEN IP features by running dynamic simulations with a SV/UVM based testbench
  * Develop and run all tests based on the [testplan](#testplan) below towards closing code and functional coverage on the IP and all of its sub-modules
* **FPV**
  * Verify TileLink device protocol compliance with an SVA based testbench

## Current status
* [Design & verification stage]({{< relref "doc/project/hw_dashboard" >}})
  * [HW development stages]({{< relref "doc/project/hw_stages" >}})
* [Simulation results](https://reports.opentitan.org/hw/ip/pattgen/dv/latest/results.html)

## Design features
For detailed information on PATTGEN design features, please see the [PATTGEN HWIP technical specification]({{< relref "hw/ip/pattgen/doc" >}}).

## Testbench architecture
PATTGEN testbench has been constructed based on the [CIP testbench architecture]({{< relref "hw/dv/sv/cip_lib/doc" >}}).

### Block diagram
![Block diagram](tb.svg)

### Top level testbench
Top level testbench is located at `hw/ip/pattgen/dv/tb/tb.sv`. It instantiates the PATTGEN DUT module `hw/ip/pattgen/rtl/pattgen.sv`.
In addition, it instantiates the following interfaces, connects them to the DUT and sets their handle into `uvm_config_db`:
* [Clock and reset interface]({{< relref "hw/dv/sv/common_ifs" >}})
* [TileLink host interface]({{< relref "hw/dv/sv/tl_agent/README.md" >}})
* PATTGEN IOs
* Interrupts ([`pins_if`]({{< relref "hw/dv/sv/common_ifs" >}})
* Alerts ([`pins_if`]({{< relref "hw/dv/sv/common_ifs" >}})
* Devmode ([`pins_if`]({{< relref "hw/dv/sv/common_ifs" >}})

### Common DV utility components
The following utilities provide generic helper tasks and functions to perform activities that are common across the project:
* [dv_utils_pkg]({{< relref "hw/dv/sv/dv_utils/README.md" >}})
* [csr_utils_pkg]({{< relref "hw/dv/sv/csr_utils/README.md" >}})

### Compile-time configurations
[list compile time configurations, if any and what are they used for]

### Global types & methods
All common types and methods defined at the package level can be found in
`pattgen_env_pkg`. Some of them in use are:
```systemverilog
[list a few parameters, types & methods; no need to mention all]
```


### UVC/agent 1
[Describe here or add link to its README]

### UVC/agent 2
[Describe here or add link to its README]


### Reference models
[Describe reference models in use if applicable, example: SHA256/HMAC]

### Stimulus strategy
#### Test sequences
All test sequences reside in `hw/ip/pattgen/dv/env/seq_lib`.
The `pattgen_base_vseq` virtual sequence is extended from `cip_base_vseq` and serves as a starting point.
All test sequences are extended from `pattgen_base_vseq`.
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
The `pattgen_scoreboard` is primarily used for end to end checking.
It creates the following analysis ports to retrieve the data monitored by corresponding interface agents:
* analysis port1:
* analysis port2:
<!-- explain inputs monitored, flow of data and outputs checked -->

#### Assertions
* TLUL assertions: The `tb/pattgen_bind.sv` binds the `tlul_assert` [assertions]({{< relref "hw/ip/tlul/doc/TlulProtocolChecker.md" >}}) to the IP to ensure TileLink interface protocol compliance.
* Unknown checks on DUT outputs: The RTL has assertions to ensure all outputs are initialized to known values after coming out of reset.
* assert prop 1:
* assert prop 2:

## Building and running tests
We are using our in-house developed [regression tool]({{< relref "hw/dv/tools/README.md" >}}) for building and running our tests and regressions.
Please take a look at the link for detailed information on the usage, capabilities, features and known issues.
Here's how to run a basic sanity test:
```console
$ cd hw/ip/pattgen/dv
$ make TEST_NAME=pattgen_sanity
```

## Testplan
<!-- TODO: uncomment the line below after adding the testplan -->
{{</* testplan "hw/ip/pattgen/data/pattgen_testplan.hjson" */>}}
