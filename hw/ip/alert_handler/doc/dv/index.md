---
title: "ALERT_HANDLER DV document"
---

## Goals
* **DV**
  * Verify all ALERT_HANDLER IP features by running dynamic simulations with a SV/UVM based testbench
  * Develop and run all tests based on the [DV plan](#dv-plan) below towards closing code and functional coverage on the IP and all of its sub-modules
* **FPV**
  * Verify TileLink device protocol compliance with an SVA based testbench
  * Verify transmitter and receiver pairs for alert and escalator
  * Partially verify ping_timer

## Current status
* [Design & verification stage]({{< relref "hw" >}})
  * [HW development stages]({{< relref "doc/project/development_stages" >}})
* [Simulation results](https://reports.opentitan.org/hw/ip/alert_handler/dv/latest/results.html)

## Design features
For detailed information on ALERT_HANDLER design features, please see the [ALERT_HANDLER HWIP technical specification]({{< relref ".." >}}).

## Testbench architecture
ALERT_HANDLER testbench has been constructed based on the [CIP testbench architecture]({{< relref "hw/dv/sv/cip_lib/doc" >}}).

### Block diagram
![Block diagram](tb.svg)

### Top level testbench
Top level testbench is located at `hw/ip/alert_handler/dv/tb/tb.sv`. It instantiates the ALERT_HANDLER DUT module `hw/ip/alert_handler/rtl/alert_handler.sv`.
In addition, it instantiates the following interfaces, connects them to the DUT and sets their handle into `uvm_config_db`:
* [Clock and reset interface]({{< relref "hw/dv/sv/common_ifs" >}})
* [TileLink host interface]({{< relref "hw/dv/sv/tl_agent/README.md" >}})
* ALERT_HANDLER IOs
* Interrupts ([`pins_if`]({{< relref "hw/dv/sv/common_ifs" >}}))
* Devmode ([`pins_if`]({{< relref "hw/dv/sv/common_ifs" >}}))

The alert_handler testbench environment can be reused in chip level testing.

### Common DV utility components
The following utilities provide generic helper tasks and functions to perform activities that are common across the project:
* [dv_utils_pkg]({{< relref "hw/dv/sv/dv_utils/README.md" >}})
* [csr_utils_pkg]({{< relref "hw/dv/sv/csr_utils/README.md" >}})

### Global types & methods
All common types and methods defined at the package level can be found in
`alert_handler_env_pkg`. Some of them in use are:
```systemverilog
  parameter uint NUM_MAX_ESC_SEV = 8;
```

### TL_agent
ALERT_HANDLER testbench instantiates (already handled in CIP base env) [tl_agent]({{< relref "hw/dv/sv/tl_agent/README.md" >}})
which provides the ability to drive and independently monitor random traffic via
TL host interface into ALERT_HANDLER device.

### ALERT_HANDLER Agent
[ALERT_HANDLER agent]:link WIP is used to drive and monitor transmitter and
receiver pairs for the alerts and escalators.

### UVM RAL Model
The ALERT_HANDLER RAL model is created with the [`ralgen`]({{< relref "hw/dv/tools/ralgen/README.md" >}}) `fusesoc` generator script automatically when the simulation is at the build stage.

It can be created manually by invoking [`regtool`]({{< relref "util/reggen/README.md" >}}):

### Stimulus strategy
#### Test sequences
All test sequences reside in `hw/ip/alert_handler/dv/env/seq_lib`.
The `alert_handler_base_vseq` virtual sequence is extended from `cip_base_vseq` and serves as a starting point.
All test sequences are extended from `alert_handler_base_vseq`.
It provides commonly used handles, variables, functions and tasks that the test sequences can simple use / call.
Some of the most commonly used tasks / functions are as follows:
* drive_alert:     Drive alert_tx signal pairs through `alert_esc_if` interface
* read_ecs_status: Readout registers that reflect escalation status, including `classa/b/c/d_accum_cnt`, `classa/b/c/d_esc_cnt`, and `classa/b/c/d_state`

#### Functional coverage
To ensure high quality constrained random stimulus, it is necessary to develop a functional coverage model.
The following covergroups have been developed to prove that the test intent has been adequately met:
* accum_cnt_cg:      Cover number of alerts triggered under the same class
* esc_sig_length_cg: Cover signal length of each escalation pairs

### Self-checking strategy
#### Scoreboard
The `alert_handler_scoreboard` is primarily used for end to end checking.
It creates the following analysis ports to retrieve the data monitored by corresponding interface agents:
* tl_a_chan_fifo: tl address channel
* tl_d_chan_fifo: tl data channel
* alert_fifo:     An array of `alert_fifo` that connects to corresponding alert_monitors
* esc_fifo:       An array of `esc_fifo` that connects to corresponding esc_monitors

Alert_handler scoreboard monitors all valid CSR registers, alert handshakes, and escalation handshakes.
To ensure certain alert, interrupt, or escalation signals are triggered at the expected time, the alert_handler scoreboard implemented a few counters:
* intr_cnter_per_class[NUM_ALERT_HANDLER_CLASSES]: Count number of clock cycles that the interrupt bit stays high.
  If the stored number is larger than the `timeout_cyc` registers, the corresponding escalation is expected to be triggered
* accum_cnter_per_class[NUM_ALERT_HANDLER_CLASSES]: Count number of alerts triggered under the same class.
  If the stored number is larger than the `accum_threshold` registers, the corresponding escalation is expected to be triggered
* esc_cnter_per_signal[NUM_ESC_SIGNALS]: Count number of clock cycles that each escalation signal stays high.
  Compare the counter against `phase_cyc` registers

The alert_handler scoreboard is parameterized to support different number of classes, alert pairs, and escalation pairs.

#### Assertions
* TLUL assertions: The `tb/alert_handler_bind.sv` binds the `tlul_assert` [assertions]({{< relref "hw/ip/tlul/doc/TlulProtocolChecker.md" >}}) to the IP to ensure TileLink interface protocol compliance.
* Unknown checks on DUT outputs: The RTL has assertions to ensure all outputs are initialized to known values after coming out of reset.

## Building and running tests
We are using our in-house developed [regression tool]({{< relref "hw/dv/tools/README.md" >}}) for building and running our tests and regressions.
Please take a look at the link for detailed information on the usage, capabilities, features and known issues.
Here's how to run a smoke test:
```console
$ $REPO_TOP/util/dvsim/dvsim.py $REPO_TOP/hw/$CHIP/ip/alert_handler/dv/alert_handler_sim_cfg.hjson -i alert_handler_smoke
```
In this run command, $CHIP can be top_earlgrey, etc.

## DV plan
{{< incGenFromIpDesc "../../data/alert_handler_testplan.hjson" "testplan" >}}
