---
title: "AON Timer DV Document"
---

## Goals
* **DV**
  * Verify the always-on timer (*AON Timer*) by running dynamic simulations with a SV/UVM based testbench
  * Develop and run all tests based on the [DV plan](#dv-plan) below towards closing code and functional coverage on the IP and all of its sub-modules
* **FPV**
  * Verify TileLink device protocol compliance with an SVA based testbench

## Current status
* [Design & verification stage]({{< relref "hw" >}})
  * [HW development stages]({{< relref "doc/project/development_stages" >}})
* [Simulation results](https://reports.opentitan.org/hw/ip/aon_timer/dv/latest/results.html)

## Design features

The AON timer is documented in the [AON Timer HWIP technical specification]({{< relref ".." >}}).

## Testbench architecture

The testbench is based on the [CIP testbench architecture]({{< relref "hw/dv/sv/cip_lib/doc" >}}).

### Block diagram
![Block diagram](tb.svg)

### Top-level testbench

The block's testbench is located at `hw/ip/aon_timer/dv/tb/tb.sv`.
It instantiates the `aon_timer` DUT module, defined at `hw/ip/aon_timer/rtl/aon_timer.sv`.

In addition, it instantiates the following interfaces, connects them to the DUT and registers their handles in `uvm_config_db`:
* A [clock and reset interface]({{< relref "hw/dv/sv/common_ifs" >}}) for the fast clock
* A [clock and reset interface]({{< relref "hw/dv/sv/common_ifs" >}}) for the AON clock
* A [TileLink host interface]({{< relref "hw/dv/sv/tl_agent/README.md" >}})
  The AON timer exposes a TL device.
  Here, the testbench is acting as the host CPU; in the OpenTitan SoC, this will be the Ibex core.
* Two interrupts (wakeup timer; watchdog bark) in the fast clock domain
* Two interrupts (wakeup timer; watchdog bite) in the AON clock domain
* The sleep mode input
* The core interface (see below).

The interrupts and sleep mode input are modelled with the basic [`pins_if`]({{< relref "hw/dv/sv/common_ifs#pins_if" >}}) interface.

The AON timer uses three clock domains (`async`, `clk_i` and `clk_aon_i`), with synchronisation logic between them.
The following diagram shows the different inputs and outputs for the module and in which clock domain each resides.

![Design timing domains](domains.svg)

To model this accurately without having to precisely model the timing of the synchronisation logic, the testbench is split into two pieces.
The first piece has a precise model of the AON timer core and checks that the DUT respects it.
The second piece has an approximate timing model and checks forwarding between the async, fast and slow clock domains.
These pieces are connected through a bound-in interface, which observes signals on the `aon_timer_core` instance.
This *core interface* is bound into the design as `u_core_if` and is used to passively monitor the signals coming in and out of the AON Timer Core block in this diagram.

### TileLink agent

In order to communicate through the register interface, the testbench uses the [tl_agent]({{< relref "hw/dv/sv/tl_agent/README.md" >}}) that is instantiated in the CIP base environment.
This is also used by generic test sequences to exercise the register interface.

### UVM RAL Model
The `aon_timer` RAL model is created with the [`ralgen`]({{< relref "hw/dv/tools/ralgen/README.md" >}}) FuseSoC generator script automatically when the simulation is at the build stage.

It can be created manually by invoking [`regtool`]({{< relref "util/reggen/README.md" >}}).
Running
```
util/regtool.py -s -t . hw/ip/aon_timer/data/aon_timer.hjson
```
will generate `aon_timer_ral_pkg.core` and `aon_timer_ral_pkg.sv` in the current directory.

### Stimulus strategy

We want to see timers expire without waiting too long, but we also want to check the counter for large values.
To get this right, we normally set up tests as follows:

- Pick a threshold value
- Pick a start count slightly below the threshold value

Occasionally, we'll pick a start count above the threshold value, to make sure nothing triggers when it shouldn't.
To ensure that we check wrap-around behaviour and see toggles on counter bits, we are careful to pick threshold values more often if they are near zero, the maximum value, or powers of two.

Since the two timers are essentially independent, we use two test sequences, driving them separately.

#### Test sequences

The test sequences can be found in `hw/ip/aon_timer/dv/env/seq_lib`.
The basic test virtual sequence configures the block in a valid initial state, but doesn't enable either timer.
This is used as a base class for automated tests like the CSR tests.

<div class="bd-callout bd-callout-warning">

**TODO**: Describe other test sequences here.

</div>

#### Functional coverage

<div class="bd-callout bd-callout-warning">

**TODO**: Functional coverage points are not yet defined.

</div>

### Self-checking strategy
#### Scoreboard

As described earlier in this document, the self-checking strategy is in two parts.
The first part of the strategy is to track the domain crossing logic and check that values propagate across unmodified and reasonably quickly.
This does not include precise modelling for the CDC timing.

The second part of the self-checking logic looks at only the *core interface*.
This is an interface of type `aon_timer_core_if`, that is bound into the `aon_timer_core` module.
Here, there is a single clock domain (the AON clock) and easily predictable behaviour.
The scoreboard contains an exact model of how the signals exposed by this interface will behave.

Putting the two parts of the scoreboard together gives a full checker for the block.
An incoming configuration write will be tracked (with slightly flexible timing) through the CDC logic by the first part of the scoreboard.
Once it takes effect in the core, the second part of the scoreboard will check that things behave correctly.
Finally, outputs (in the form of configuration register updates or interrupts) will be tracked by the first part of the scoreboard as they go back through the CDC logic and, eventually, make it out to the top-level.

#### Assertions

TLUL protocol assertions are checked by binding the [TL-UL protocol checker]({{< relref "hw/ip/tlul/doc/TlulProtocolChecker.md" >}}) into the design.

Outputs are also checked for `'X` values by assertions in the design RTL.

## Building and running tests

Tests can be run with [`dvsim.py`]({{< relref "hw/dv/tools/README.md" >}}).
The link gives details of the tool's features and command line arguments.
To run a basic smoke test, go to the top of the repository and run:
```console
$ util/dvsim/dvsim.py hw/ip/aon_timer/dv/aon_timer_sim_cfg.hjson -i aon_timer_smoke
```

## DV plan
{{< incGenFromIpDesc "../../data/aon_timer_testplan.hjson" "testplan" >}}
