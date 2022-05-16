---
title: "CLKMGR DV document"
---

## Goals
* **DV**
  * Verify all CLKMGR IP features by running dynamic simulations with a SV/UVM based testbench.
  * Develop and run all tests based on the [testplan](#testplan) below towards closing code and functional coverage on the IP and all of its sub-modules.
* **FPV**
  * Verify TileLink device protocol compliance with an SVA based testbench.
  * Verify clock gating assertions.

## Current status
* [Design & verification stage]({{< relref "hw" >}})
  * [HW development stages]({{< relref "doc/project/development_stages" >}})
* [Simulation results](https://reports.opentitan.org/hw/ip/clkmgr/dv/latest/results.html)

## Design features
The detailed information on CLKMGR design features is at [CLKMGR HWIP technical specification]({{< relref "hw/ip/clkmgr/doc" >}}).

## Testbench architecture
CLKMGR testbench has been constructed based on the [CIP testbench architecture]({{< relref "hw/dv/sv/cip_lib/doc" >}}).

### Block diagram
![Block diagram](tb.svg)

### Top level testbench
Top level testbench is located at `hw/ip/clkmgr/dv/tb.sv`.
It instantiates the CLKMGR DUT module `hw/top_earlgrey/ip/clkmgr/rtl/autogen/clkmgr.sv`.
In addition, it instantiates the following interfaces, connects them to the DUT and sets their handle into `uvm_config_db`:

* [Clock and reset interface]({{< relref "hw/dv/sv/common_ifs" >}})
* [TileLink host interface]({{< relref "hw/dv/sv/tl_agent/README.md" >}})
* CLKMGR IOs: `hw/ip/clkmgr/dv/env/clkmgr_if.sv`

The Devmode ([`pins_if`]({{< relref "hw/dv/sv/common_ifs" >}})) interface should be connected once the RTL adds support for it.

### Common DV utility components
The following utilities provide generic helper tasks and functions to perform activities that are common across the project:

* [dv_utils_pkg]({{< relref "hw/dv/sv/dv_utils/README.md" >}})
* [csr_utils_pkg]({{< relref "hw/dv/sv/csr_utils/README.md" >}})

### Global types & methods
All common types and methods defined at the package level can be found in
`clkmgr_env_pkg`. Some of them in use are:

```systemverilog
  localparam int NUM_PERI = 4;
  localparam int NUM_TRANS = 5;
  localparam int NUM_ALERTS = 2;

  typedef logic [NUM_PERI-1:0] peri_enables_t;
  typedef logic [NUM_TRANS-1:0] hintables_t;

  typedef virtual clkmgr_if clkmgr_vif;
  typedef virtual clk_rst_if clk_rst_vif;
  typedef enum int {PeriDiv4, PeriDiv2, PeriIo, PeriUsb} peri_e;
  typedef enum int {TransAes, TransHmac, TransKmac, TransOtbnIoDiv4, TransOtbnMain} trans_e;
```

### TL_agent
CLKMGR testbench instantiates (already handled in CIP base env) [tl_agent]({{< relref "hw/dv/sv/tl_agent/README.md" >}}) which provides the ability to drive and independently monitor random traffic via TL host interface into CLKMGR device.

### UVM RAL Model
The CLKMGR RAL model is created with the [`ralgen`]({{< relref "hw/dv/tools/ralgen/README.md" >}}) FuseSoC generator script automatically when the simulation is at the build stage.

It can be created manually by invoking [`regtool`]({{< relref "util/reggen/README.md" >}}):

### Stimulus strategy
This module is rather simple: the stimulus is just the external pins and the CSR updates.
There are a couple stages for synchronization of the CSR updates for clock gating controls, but scanmode is used asynchronously.
These go to the clock gating latches.
The external pins controlling the external clock selection need no synchronization.
The tests randomize the inputs and issue CSR updates affecting the specific functions being tested.

#### Test sequences
All test sequences reside in `hw/ip/clkmgr/dv/env/seq_lib`.
The `clkmgr_base_vseq` virtual sequence is extended from `cip_base_vseq` and serves as a starting point.
All test sequences are extended from `clkmgr_base_vseq`.
It provides commonly used handles, variables, functions and tasks that the test sequences can use or call.
Some of the most commonly used tasks / functions are as follows:
* `clkmgr_init`: Sets the frequencies of the various clocks.
* `control_ip_clocks`: Turns on or off the input clocks based on the various clock enable and status ports to and from the `pwrmgr` IP.

The sequence `clkmgr_peri_vseq` randomizes the stimuli that drive the four peripheral clocks.
These clocks are mutually independent so they are tested in parallel.
They depend on the `clk_enables` CSR, which has a dedicated enable for each peripheral clock, the pwrmgr's `<clk>_ip_clk_en` which has a dedicated bit controlling `io`, `main`, and `usb` clocks, and `scanmode_i` which is used asynchronously and also controls all.
The sequence runs a number of iterations, each randomizing all the above.

The sequence `clkmgr_trans_vseq` randomizes the stimuli that drive the five transactional unit clocks.
These are also mutually independent so they are tested in parallel.
They depend on the `clk_hints` CSR, which has a separate bit for each, `<clk>_ip_clk_en` and `scanmode_i` as in the peripheral clocks.
They also depend on the `idle_i` input, which also has a separate bit for each unit.
Any unit's `idle_i` bit is clear when the unit is currently busy, and prevents its clock to be turned off until it becomes idle.

The sequence `clkmgr_extclk_vseq` randomizes the stimuli that drive the external clock selection.
The selection is controlled by software if the `extclk_ctrl.sel` CSR is `prim_mubi_pkg::MuBi4True`, provided the `lc_hw_debug_en_i` input is also set to `lc_ctrl_pkg::On`.
Alternatively, the external clock is selected by the life cycle controller if the `lc_ctrl_byp_req_i` input is `lc_ctrl_pkg::On`.
When the external clock is selected and `scanmode_i` is not set to `prim_mubi_pkg::MuBi4True`, the clock dividers for the clk_io_div2 and clk_io_div4 output clocks are stepped down:
* If `lc_ctrl_byp_req_i` is on, or
* If `extclk_ctrl.hi_speed_sel` CSR is `prim_mubi_pkg::MuBi4True`, when the selection is enabled by software.

The sequence `clkmgr_frequency_vseq` randomly programs the frequency measurement for each clock so its measurement is either okay, slow, or fast.
It checks the recoverable alerts trigger as expected when a measurement is not okay.

#### Functional coverage
To ensure high quality constrained random stimulus, it is necessary to develop a functional coverage model.
The following covergroups have been developed to prove that the test intent has been adequately met:

* Covergroups for inputs to each software gated peripheral clock.
  These are wrapped in class `clkmgr_peri_cg_wrap` and instantiated in `clkmgr_env_cov`.
* Covergroups for inputs to each transactional gated unit clock.
  These are wrapped in class `clkmgr_trans_cg_wrap` and instantiated in `clkmgr_env_cov`.
* Covergroups for the outcome of each clock measurement.
  These are wrapped in class `freq_measure_cg_wrap` and instantiated in `clkmgr_env_cov`.
* Covergroup for the external clock selection logic: `extclk_cg` in `clkmgr_env_cov`.

See more detailed description at `hw/ip/clkmgr/data/clkmgr_testplan.hjson`.

### Self-checking strategy

Most of the checking is done using SVA for input to output, or CSR update to output behavior.
Some of the CLKMGR outputs are gated clocks, which are controlled by both synchronous logic and asynchronous enables.
These asynchronous enables become synchronous because of the SVA semantics.
This is fine since the assertions allow some cycles for the expected behavior to occur.

#### Scoreboard
The `clkmgr_scoreboard` combines CSR updates and signals from the clkmgr vif to instrument some checks and coverage collection.
The CSR updates are determined using the TLUL analysis port.

The output clocks can be separated into two groups: peripheral ip clocks and transactional unit clocks.
Please refer to the [Test sequences section](#test-sequences) above.
The clock gating logic is pretty similar across units in each group.
For each peripheral and transactional clock the scoreboard samples their coverage based on clocking blocks instantiated in `clkmgr_if`.

The external clock control signals with the AST are checked in the scoreboard itself.
This involves checking that
* Transitions in the `lc_clk_byp_req` input are followed by corresponding transitions in the `io_clk_byp_req` output.
  * Transitions in the `all_clk_byp_req` output correspond to the `extclk_ctrl` CSR and the `lc_hw_debug_en` input.

The `jitter_en_o` output is checked to match the `jitter_enable` CSR.

#### Assertions
* Pwrmgr enable-status assertions: Interface `clkmgr_pwrmgr_sva_if` contains concurrent SVA that checks that edges of the various ip_clk_en are followed by corresponding edges of their clk_status.
  The clocks checked are `main`, `io`, and `usb`.
* Gated clock assertions: Interface `clkmgr_gated_clock_sva_if` contains concurrent SVA that checks each gated clock is either running or stopped based on their control logic.
  There is one assertion for each of the four peripheral clock and five hintable clocks.
* Clock divider assertions: Interface `clkmgr_div_sva_if` contains concurrent SVA that checks the `io_div2` and `io_div4` clocks are running at nominal frequency, or are divided by two each in response to the `extclk` logic.
* TLUL assertions: `clkmgr_bind.sv` binds the `tlul_assert` [assertions]({{< relref "hw/ip/tlul/doc/TlulProtocolChecker.md" >}}) to the IP to ensure TileLink interface protocol compliance.
* Unknown checks on DUT outputs: The RTL has assertions to ensure all outputs are initialized to known values after coming out of reset.

## Building and running tests
We are using our in-house developed [regression tool]({{< relref "hw/dv/tools/README.md" >}}) for building and running our tests and regressions.
Please take a look at the link for detailed information on the usage, capabilities, features and known issues.
Here's how to run a smoke test:

```console
$ $REPO_TOP/util/dvsim/dvsim.py $REPO_TOP/hw/ip/clkmgr/dv/clkmgr_sim_cfg.hjson -i clkmgr_smoke
```

## Testplan
{{< incGenFromIpDesc "../../data/clkmgr_testplan.hjson" "testplan" >}}
