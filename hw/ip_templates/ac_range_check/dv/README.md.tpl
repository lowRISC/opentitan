# AC_RANGE_CHECK DV document

${"##"} Goals
* **DV**
  * Verify all AC_RANGE_CHECK IP features by running dynamic simulations with a SV/UVM based testbench
  * Develop and run all tests based on the [testplan](#testplan) below towards closing code and functional coverage on the IP and all of its sub-modules
* **FPV**
  * Verify TileLink device protocol compliance with an SVA based testbench

${"##"} Current status
* [Design & verification stage](../../../../README.md)
  * [HW development stages](../../../../../doc/project_governance/development_stages.md)
* [Simulation results](https://reports.opentitan.org/hw/top_${topname}/ip_autogen/ac_range_check/dv/latest/report.html)

${"##"} Design features
For detailed information on `ac_range_check` design features, please see the [`ac_range_check` HWIP technical specification](../README.md).

${"##"} Testbench architecture
The `ac_range_check` UVM DV testbench has been constructed based on the [CIP testbench architecture](../../../../dv/sv/cip_lib/README.md).

${"###"} Block diagram
![Block diagram](./doc/tb.svg)
Note: this diagram is editable from [this address](https://docs.google.com/drawings/d/1-0r4V6H8RwLeiAa3ng73vcDZdCbeeuFDYPZcX-QXRYo/edit?usp=sharing).

${"###"} Top level testbench
Top level testbench is located at `hw/top_${topname}/ip_autogen/${module_instance_name}/dv/tb/tb.sv`.
It instantiates the `${module_instance_name}` DUT module `hw/top_${topname}/ip_autogen/${module_instance_name}/rtl/${module_instance_name}.sv`.
In addition, the testbench instantiates the following interfaces, connects them to the DUT and sets their handle into `uvm_config_db`:
* [Clock and reset interface](../../../../dv/sv/common_ifs/README.md)
* [Reset shadowed interface](../../../../dv/sv/common_ifs/README.md)  // TODO add something in this doc about this interface.
* [TileLink host interface for the CSRs](../../../../dv/sv/tl_agent/README.md)
* [TileLink host interface for the Unfiltered CTN accesses](../../../../dv/sv/tl_agent/README.md)
* [TileLink device interface for the Filtered CTN accesses](../../../../dv/sv/tl_agent/README.md)
* Interrupts ([`pins_if`](../../../../dv/sv/common_ifs/README.md))
* Alerts ([`alert_esc_if`](../../../../dv/sv/alert_esc_agent/README.md))
* Miscellaneaous IP specific signals without an attached UVM agent `misc_if`


${"###"} Common DV utility components
The following utilities provide generic helper tasks and functions to perform activities that are common across the project:
* [dv_utils_pkg](../../../../dv/sv/dv_utils/README.md)
* [csr_utils_pkg](../../../../dv/sv/csr_utils/README.md)

${"###"} Global types & methods
All common types and methods defined at the package level can be found in `${module_instance_name}_env_pkg`.
Some of them in use are:
```systemverilog
  // Parameters
  parameter uint   NUM_ALERTS                 = 2;
  parameter string LIST_OF_ALERTS[NUM_ALERTS] = {"recov_ctrl_update_err", "fatal_fault"};
  parameter uint   NUM_RANGES                 = ${num_ranges};
  parameter uint   NUM_ROLES                  = ${2**nr_role_bits};
  parameter uint   ROLE_WIDTH                 = ${nr_role_bits};

  // Retrieve the index of the CSR based on its name
  function automatic int get_csr_idx(string csr_ral_name, string csr_name);
```

${"###"} TL_agent
* `ac_range_check` UVM environment instantiates a (already handled in CIP base env) [tl_agent](../../../../dv/sv/tl_agent/README.md) which provides the ability to drive and independently monitor random traffic via TL host interface into `ac_range_check` device, to access to the CSRs (Control/Status Registers).
* Host interface to the Unfiltered CTN accesses.
* Device interface to the Filtered CTN accesses.

The `tl_agent` monitor supplies partial TileLink request packets as well as completed TileLink response packets over the TLM analysis port for further processing within the `ac_range_check` scoreboard.

${"###"} Alert_agent
`ac_range_check` testbench instantiates (already handled in CIP base env) [alert_agents](../../../../dv/sv/alert_esc_agent/README.md):
[list alert names].
The alert_agents provide the ability to drive and independently monitor alert handshakes via alert interfaces in AC_RANGE_CHECK device.

${"###"} UVM RAL Model
The `ac_range_check` RAL model is created with the [`ralgen`](../../../../dv/tools/ralgen/README.md) FuseSoC generator script automatically when the simulation is at the build stage.

It can be created manually by invoking [`regtool`](../../../../../util/reggen/doc/setup_and_use.md):

${"####"} Sequence cfg
An efficient way to develop test sequences is by providing some random variables that are used to configure the DUT / drive stimulus.
The random variables are constrained using weights and knobs that can be controlled.
These weights and knobs take on a "default" value that will result in the widest exploration of the design state space, when the test sequence is randomized and run as-is.
To steer the randomization towards a particular distribution or to achieve interesting combinations of the random variables, the test sequence can be extended to create a specialized variant.
In this extended sequence, nothing would need to be done, other than setting those weights and knobs appropriately.
This helps increase the likelihood of hitting the design corners that would otherwise be difficult to achieve, while maximizing reuse.

This object aims to provide such run-time controls.

${"####"} Env cfg
The `${module_instance_name}_env_cfg`, environment configuration object provides access to the following elements:
* Build-time controls to configure the UVM environment composition during the `build_phase`
* Downstream agent configuration objects for ease of lookup from any environment component
  * This includes the `tl_agent_cfg` objects for both TL interfaces
* All virtual interfaces that connect to the DUT listed above (retrieved from the `uvm_config_db`)
* Sequence configuration object described above

All environment components contain a handle to an instance of this class (that was created in the test class via the parent `dv_base_test`).
By housing all of the above, all pertinent information is more easily shared with all environment components.

${"###"} Stimulus strategy
${"####"} Test sequences
All test sequences reside in `hw/top_${topname}/ip_autogen/ac_range_check/dv/env/seq_lib`.
The `${module_instance_name}_base_vseq` virtual sequence is extended from `cip_base_vseq` and serves as a starting point.
All test sequences are extended from `${module_instance_name}_base_vseq`.
It provides commonly used handles, variables, functions and tasks that the test sequences can simple use / call.
Some of the most commonly used tasks / functions are as follows: From `hw/top_${topname}/ip_autogen/${module_instance_name}/dv/env/seq/${module_instance_name}_base_vseq.sv`,
* `ac_range_check_init`       : initialize ac_range_check settings including configurations and interrupt
* `cfg_range_base`            : configure the range_base registers according to what is defined dut_cfg
* `cfg_range_limit`           : configure the range_limit registers according to what is defined dut_cfg
* `cfg_range_attr`            : configure the range_attr registers according to what is defined dut_cfg
* `range_racl_policy`         : configure the range_racl_policy_shadowed registers according to what is defined dut_cfg
* `send_single_tl_unfilt_tr`  : send one random transaction on the TL Unfiltered interface
* `tl_filt_device_auto_resp`  : auto-respond to incoming TL accesses on the Filtered host interface

${"####"} Functional coverage
To ensure high quality constrained random stimulus, it is necessary to develop a functional coverage model.
The following covergroups have been developed to prove that the test intent has been adequately met:
* `attr_perm_cg`      : evaluates attribute permissions coverage for all the indexes, access types and access permit (minus a bunch of illegal_bins)
* `racl_cg`           : evaluates RACL checks coverage for all the indexes, roles and access types
* `range_cg`          : observes that each index is enabled or disabled
* `addr_match_cg`     : ensures that address matches are observed on all range indexes
* `all_index_miss_cg` : it can occur when a TLUL transaction being checked by ac_range will miss all configured indexes and be denied
* `bypass_cg`         : ensures that IP bypass has been exercised
* `range_lock_cg`     : evaluates range lock coverage for all the indexes and for all ranges (enabled or not)

${"###"} Self-checking strategy
${"####"} Scoreboard
It creates the following analysis ports to retrieve the data monitored by corresponding interface agents:
* tl_a_chan_fifo        : TileLink A channel for CSR accesses
* tl_d_chan_fifo        : TileLink D channel for CSR accesses
* tl_unfilt_d_chan_fifo : TileLink D channel for the Unfiltered interface
* tl_filt_a_chan_fifo   : TileLink A channel for the Filtered interface

${"####"} Assertions
* TLUL assertions: The `hw/top_${topname}/ip_autogen/${module_instance_name}/dv/sva/${module_instance_name}_bind.sv` binds the `tlul_assert` [assertions](../../../../ip/tlul/doc/TlulProtocolChecker.md) to the IP to ensure TileLink interface protocol compliance.
* Unknown checks on DUT outputs: The RTL has assertions to ensure all outputs are initialized to known values after coming out of reset.

${"##"} Building and running tests
The [dvsim](https://github.com/lowRISC/dvsim) tool is used for building and running our tests and regressions.
Please take a look at the link for detailed information on the usage, capabilities, features and known issues.
Here's how to run a smoke test:
```console
$ cd $REPO_TOP
$ dvsim hw/top_${topname}/ip_autogen/${module_instance_name}/dv/ac_range_check_sim_cfg.hjson -i ac_range_check_smoke
```

${"##"} Testplan
[Testplan](../data/ac_range_check_testplan.hjson)
