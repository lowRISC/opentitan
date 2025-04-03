# AC_RANGE_CHECK DV document

## Goals
* **DV**
  * Verify all AC_RANGE_CHECK IP features by running dynamic simulations with a SV/UVM based testbench
  * Develop and run all tests based on the [testplan](#testplan) below towards closing code and functional coverage on the IP and all of its sub-modules
* **FPV**
  * Verify TileLink device protocol compliance with an SVA based testbench

## Current status
* [Design & verification stage](../../../../README.md)
  * [HW development stages](../../../../../doc/project_governance/development_stages.md)
* [Simulation results](https://reports.opentitan.org/hw/top_darjeeling/ip_autogen/ac_range_check/dv/latest/report.html)

## Design features
For detailed information on `ac_range_check` design features, please see the [`ac_range_check` HWIP technical specification](../README.md).

## Testbench architecture
The `ac_range_check` UVM DV testbench has been constructed based on the [CIP testbench architecture](../../../../dv/sv/cip_lib/README.md).

### Block diagram
![Block diagram](./doc/tb.svg)
Note: this diagram is editable from [this address](https://docs.google.com/drawings/d/1mZR9z-vssPHhJmbmX_ZZXELSP20vFc28m5TPbK4eVvE/edit?usp=sharing).

### Top level testbench
Top level testbench is located at `hw/top_darjeeling/ip_autogen/ac_range_check/dv/tb/tb.sv`.
It instantiates the `ac_range_check` DUT module `hw/ip/ac_range_check/rtl/ac_range_check.sv`.
In addition, the testbench instantiates the following interfaces, connects them to the DUT and sets their handle into `uvm_config_db`:
* [Clock and reset interface](../../../../dv/sv/common_ifs/README.md)
* [Reset shadowed interface](../../../../dv/sv/common_ifs/README.md)  // TODO add something in this doc about this interface.
* [TileLink host interface for the CSRs](../../../../dv/sv/tl_agent/README.md)
* [TileLink host interface for the Unfiltered CTN accesses](../../../../dv/sv/tl_agent/README.md)
* [TileLink device interface for the Filtered CTN accesses](../../../../dv/sv/tl_agent/README.md)
* Interrupts ([`pins_if`](../../../../dv/sv/common_ifs/README.md))
* Alerts ([`alert_esc_if`](../../../../dv/sv/alert_esc_agent/README.md))


### Common DV utility components
The following utilities provide generic helper tasks and functions to perform activities that are common across the project:
* [dv_utils_pkg](../../../../dv/sv/dv_utils/README.md)
* [csr_utils_pkg](../../../../dv/sv/csr_utils/README.md)

### Compile-time configurations
[list compile time configurations, if any and what are they used for]

### Global types & methods
All common types and methods defined at the package level can be found in `ac_range_check_env_pkg`.
Some of them in use are:
```systemverilog
[list a few parameters, types & methods; no need to mention all]
```

### TL_agent
* `ac_range_check` UVM environment instantiates a (already handled in CIP base env) [tl_agent](../../../../dv/sv/tl_agent/README.md) which provides the ability to drive and independently monitor random traffic via TL host interface into `ac_range_check` device, to access to the CSRs (Control/Status Registers).
* Host interface to the Unfiltered CTN accesses.
* Device interface to the Filtered CTN accesses.

The `tl_agent` monitor supplies partial TileLink request packets as well as completed TileLink response packets over the TLM analysis port for further processing within the `ac_range_check` scoreboard.

### Alert_agent
`ac_range_check` testbench instantiates (already handled in CIP base env) [alert_agents](../../../../dv/sv/alert_esc_agent/README.md):
[list alert names].
The alert_agents provide the ability to drive and independently monitor alert handshakes via alert interfaces in AC_RANGE_CHECK device.

### UVM RAL Model
The `ac_range_check` RAL model is created with the [`ralgen`](../../../../dv/tools/ralgen/README.md) FuseSoC generator script automatically when the simulation is at the build stage.

It can be created manually by invoking [`regtool`](../../../../../util/reggen/doc/setup_and_use.md):

#### Sequence cfg
An efficient way to develop test sequences is by providing some random variables that are used to configure the DUT / drive stimulus.
The random variables are constrained using weights and knobs that can be controlled.
These weights and knobs take on a "default" value that will result in the widest exploration of the design state space, when the test sequence is randomized and run as-is.
To steer the randomization towards a particular distribution or to achieve interesting combinations of the random variables, the test sequence can be extended to create a specialized variant.
In this extended sequence, nothing would need to be done, other than setting those weights and knobs appropriately.
This helps increase the likelihood of hitting the design corners that would otherwise be difficult to achieve, while maximizing reuse.

This object aims to provide such run-time controls.

#### Env cfg
The `ac_range_check_env_cfg`, environment configuration object provides access to the following elements:
* Build-time controls to configure the UVM environment composition during the `build_phase`
* Downstream agent configuration objects for ease of lookup from any environment component
  * This includes the `tl_agent_cfg` objects for both TL interfaces
* All virtual interfaces that connect to the DUT listed above (retrieved from the `uvm_config_db`)
* Sequence configuration object described above

All environment components contain a handle to an instance of this class (that was created in the test class via the parent `dv_base_test`).
By housing all of the above, all pertinent information is more easily shared with all environment components.

### Stimulus strategy
#### Test sequences
All test sequences reside in `hw/top_darjeeling/ip_autogen/ac_range_check/dv/env/seq_lib`.
The `ac_range_check_base_vseq` virtual sequence is extended from `cip_base_vseq` and serves as a starting point.
All test sequences are extended from `ac_range_check_base_vseq`.
It provides commonly used handles, variables, functions and tasks that the test sequences can simple use / call.
Some of the most commonly used tasks / functions are as follows: From `hw/top_darjeeling/ip_autogen/ac_range_check/dv/env/seq/ac_range_check_base_vseq.sv`,
* task 1:
* task 2:

#### Functional coverage
To ensure high quality constrained random stimulus, it is necessary to develop a functional coverage model.
The following covergroups have been developed to prove that the test intent has been adequately met:
* cg1:
* cg2:

### Self-checking strategy
#### Scoreboard
It creates the following analysis ports to retrieve the data monitored by corresponding interface agents:
* analysis port1:
* analysis port2:
<!-- explain inputs monitored, flow of data and outputs checked -->

#### Assertions
* TLUL assertions: The `hw/top_darjeeling/ip_autogen/ac_range_check/dv/sva/ac_range_check_bind.sv` binds the `tlul_assert` [assertions](../../../../ip/tlul/doc/TlulProtocolChecker.md) to the IP to ensure TileLink interface protocol compliance.
* Unknown checks on DUT outputs: The RTL has assertions to ensure all outputs are initialized to known values after coming out of reset.
* assert prop 1:
* assert prop 2:

## Building and running tests
We are using our in-house developed [regression tool](../../../../../util/dvsim/README.md) for building and running our tests and regressions.
Please take a look at the link for detailed information on the usage, capabilities, features and known issues.
Here's how to run a smoke test:
```console
$ cd $REPO_TOP
$ ./util/dvsim/dvsim.py hw/top_darjeeling/ip_autogen/ac_range_check/dv/ac_range_check_sim_cfg.hjson -i ac_range_check_smoke
```

## Testplan
[Testplan](../data/ac_range_check_testplan.hjson)
