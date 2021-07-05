---
title: "CLKMGR DV document"
---

## Goals
* **DV**
  * Verify all CLKMGR IP features by running dynamic simulations with a SV/UVM based testbench.
  * Develop and run all tests based on the [DV plan](#dv-plan) below towards closing code and functional coverage on the IP and all of its sub-modules.
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

Notice the following interfaces should be connected once the RTL adds support for them:

* Alerts ([`alert_esc_if`]({{< relref "hw/dv/sv/alert_esc_agent/README.md" >}}))
* Devmode ([`pins_if`]({{< relref "hw/dv/sv/common_ifs" >}}))

### Common DV utility components
The following utilities provide generic helper tasks and functions to perform activities that are common across the project:

* [dv_utils_pkg]({{< relref "hw/dv/sv/dv_utils/README.md" >}})
* [csr_utils_pkg]({{< relref "hw/dv/sv/csr_utils/README.md" >}})

### Global types & methods
All common types and methods defined at the package level can be found in
`clkmgr_env_pkg`. Some of them in use are:

```systemverilog
  typedef virtual clkmgr_if clkmgr_vif;
  typedef virtual clk_rst_if clk_rst_vif;
  typedef enum int {PeriDiv4, PeriDiv2, PeriIo, PeriUsb} peri_e;
  typedef enum int {TransAes, TransHmac, TransKmac, TransOtbn} trans_e;
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
* `update_idle`: Updates the `idle` input.

The sequence `clkmgr_peri_vseq` randomizes the stimuli that drive the four peripheral clocks.
These clocks are mutually independent so they are tested in parallel.
They depend on the `clk_enables` CSR, which has a dedicated enable for each peripheral clock, the pwrmgr's `ip_clk_en` which controls all, and `scanmode_i` which is used asynchronously and also controls all.
The sequence runs a number of iterations, each randomizing all the above.

The sequence `clkmgr_trans_vseq` randomizes the stimuli that drive the four transactional unit clocks.
These are also mutually independent so they are tested in parallel.
They depend on the `clk_hints` CSR, which has a separate bit for each, `ip_clk_en` and `scanmode_i` as in the peripheral clocks.
They also depend on the `idle_i` input, which also has a separate bit for each unit.
Any unit's `idle_i` bit is clear when the unit is currently busy, and prevents its clock to be turned off until it becomes idle.

The sequence `clkmgr_extclk_vseq` randomizes the stimuli that drive the external clock selection.
The selection is controlled by the `extclk_sel` CSR being `lc_ctrl_pkg::On`, provided the `lc_dft_en_i` input is also set to `lc_ctrl_pkg::On`.
Alternatively, the external clock is also selected if the `lc_ctrl_byp_req_i` is `lc_ctrl_pkg::On`.
When the external clock is selected the clock dividers for the clk_io_div2 and clk_io_div4 output clocks are stepped down, unless `scanmode_i` is set to `lc_ctrl_pkg::On`.

The sequence `clkmgr_jitter_vseq` sets the `jitter` CSR that drives the `jitter_en_o` output to the AST block.
The sequence writes the CSR and checks that the `jitter_en_o` output tracks it.

#### Functional coverage
To ensure high quality constrained random stimulus, it is necessary to develop a functional coverage model.
The following covergroups have been developed to prove that the test intent has been adequately met:

* Covergroups for inputs to the peripherals clock gating.
  These are wrapped in class `clkmgr_peri_cg_wrap` and instantiated in `clkmgr_env_cov`.
* Covergroups for inputs to the transactional units clock gating.
  These are wrapped in class `clkmgr_trans_cg_wrap` and instantiated in `clkmgr_env_cov`.

See more detailed description at `hw/ip/clkmgr/data/clkmgr_testplan.hjson`.

### Self-checking strategy
Most of the CLKMGR outputs are gated clocks, which are controlled by both synchronous logic and asynchronous enables.
If it were not for the asynchronous enables it would be possible to check them with SVA assertions.
The reason asynchronous enables don't work for SVA is because the latter uses sampled values at clock edges.
It may be possible to consider the asynchronous enable as an additional clock, and deal with multiple clock assertions.
However, it seems simpler to just check the clocks in the scoreboard, using regular SV constructs.

#### Scoreboard
The `clkmgr_scoreboard` combines CSR updates and signals from the the clkmgr vif to check the activity of the gated clocks.

The output clocks can be separated into two groups: peripheral ip clocks and transactional unit clocks.
Please refer to the [Test sequences section](#test-sequences) above.
The clock gating logic is pretty similar across units in each group.

To get the right timing for the gated clocks the scoreboard follows these rules:
CSR updates need one extra flop stage using the non-gated version of the clock they control.
The `pwrmgr.ip_clk_en` input needs to be staged like the CSRs.
Transactional unit `idle` bits are in the same clock domain as their controlled clocks so need no extra stages.
The asynchronous `scanmode_i` input needs no stages.
All synchronous signals the scoreboard needs from clkmgr_if are transferred via clocking blocks triggered by the corresponding unit's powerup clock.

In pseudo code the prediction for the clock gate of unit `peri` becomes

```verilog
unit_enable = staged(clk_enables[peri] && ip_clk_en) || is_on(scanmode_i)
```

The transactional units have an additional bit in `idle` that prevents disabling their clock unless this bit is on.
In pseudo code the prediction for the clock gate of unit `trans` becomes

```verilog
unit_enable  = staged(clk_hints[trans] && ip_clk_en) || !idle[trans] || is_on(scanmode_i)
```

The CSR updates are determined using the TLUL analysis port.

#### Assertions
* TLUL assertions: The `tb/clkmgr_bind.sv` binds the `tlul_assert` [assertions]({{< relref "hw/ip/tlul/doc/TlulProtocolChecker.md" >}}) to the IP to ensure TileLink interface protocol compliance.

* Unknown checks on DUT outputs: The RTL has assertions to ensure all outputs are initialized to known values after coming out of reset.

## Building and running tests
We are using our in-house developed [regression tool]({{< relref "hw/dv/tools/README.md" >}}) for building and running our tests and regressions.
Please take a look at the link for detailed information on the usage, capabilities, features and known issues.
Here's how to run a smoke test:

```console
$ $REPO_TOP/util/dvsim/dvsim.py $REPO_TOP/hw/ip/clkmgr/dv/clkmgr_sim_cfg.hjson -i clkmgr_smoke
```

## DV plan
{{< incGenFromIpDesc "../../data/clkmgr_testplan.hjson" "testplan" >}}
