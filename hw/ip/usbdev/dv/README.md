# USBDEV DV document

## Goals
* **DV**
  * Verify all USBDEV IP features by running dynamic simulations with a SV/UVM based testbench.
  * Develop and run all tests based on the [testplan](#testplan) below towards closing code and functional coverage on the IP and all of its sub-modules.
    * Note that code and functional coverage goals are TBD due to pending evaluation of where / how to source a USB20 UVM VIP.
    * The decision is trending towards hooking up a cocotb (Python) based open source USB20 compliance test suite with this UVM environment.
* **FPV**
  * Verify TileLink device protocol compliance with an SVA based testbench.

## Current status
* [Design & verification stage](../../../README.md)
  * [HW development stages](../../../../doc/project_governance/development_stages.md)
* [Simulation results](https://reports.opentitan.org/hw/ip/usbdev/dv/latest/report.html)

## Design features
For detailed information on USBDEV design features, please see the [USBDEV HWIP technical specification](../README.md).

## Testbench architecture
The USBDEV testbench is based on the [CIP testbench architecture](../../../dv/sv/cip_lib/README.md).

### Top level testbench
The top-level testbench is located at `hw/ip/usbdev/dv/tb/tb.sv`.
It instantiates the USBDEV DUT module `hw/ip/usbdev/rtl/usbdev.sv`.

USBDEV has the following interfaces, which the testbench instantiates and connects and registers with `uvm_config_db`:
- [Clock and reset interfaces](../../../dv/sv/common_ifs/README.md) for the USB and AON clock domains.
- A [TileLink interface](../../../dv/sv/tl_agent/README.md).
  USBDEV is a TL-UL device, which expects to communicate with a TL-UL host.
  In the OpenTitan SoC, this will be the Ibex core.
- A `usb20_block_if` representing the actual USB interface.
  This is using a class that has been developed in parallel with `usb20_if`.
  Eventually, they will hopefully be merged again.
- An [alert interface](../../../dv/sv/alert_esc_agent/README.md)
- Interrupts, modelled with the basic [`pins_if`](../../../dv/sv/common_ifs/README.md) interface.

### Agents
USBDEV has dedicated agents for two interfaces.

- The dedicated [usb20_agent](../../../dv/sv/usb20_agent/README.md), which has its own documentation.
  This handles the USB interface itself.

- The generic [tl_agent](../../../dv/sv/tl_agent/README.md) inherited from CIP base environment.
  This handles TileLink traffic (accessing both CSRs and packet buffers)

### Reference models
The only reference model for USBDEV is a RAL model for CSR reads and writes.
For this, there is a dedicated RAL model, which is created by [`ralgen`](../../../dv/tools/ralgen/README.md) as part of the build flow.

### Stimulus strategy
#### Test sequences
All test sequences reside in `hw/ip/usbdev/dv/env/seq_lib`.
The `usbdev_base_vseq` virtual sequence is extended from `cip_base_vseq` and serves as a starting point.
All test sequences are extended from `usbdev_base_vseq`.
It provides commonly used handles, variables, functions and tasks that the test sequences can simply use / call.

USBDEV virtual sequences normally also run a `usbdev_init` task at the start of the simulation.
This does basic USB device initialization and is only disabled for `usbdev_common_vseq` (which tests CSR behaviour and doesn't need to enable USB itself).

#### Functional coverage

Covergroups for functional coverage (as collected by `usbdev_env_cov`) are listed in the testplan at `hw/ip/usbdev/data/usbdev_testplan.hjson`.

### Self-checking strategy
#### Scoreboard
The `usbdev_scoreboard` is currently in skeleton form and doesn't really contain any checks.
TODO: Extend the scoreboard far enough that there's something to document, then document it here.

#### Assertions
* TLUL assertions: The `tb/usbdev_bind.sv` binds the `tlul_assert` [assertions](../../tlul/doc/TlulProtocolChecker.md) to the IP to ensure TileLink interface protocol compliance.
* Unknown checks on DUT outputs: The RTL has assertions to ensure all outputs are initialized to known values after coming out of reset.

## Building and running tests
We are using our in-house developed [regression tool](../../../../util/dvsim/README.md) for building and running our tests and regressions.
Please take a look at the link for detailed information on the usage, capabilities, features and known issues.
Here's how to run a smoke test:
```console
$ $REPO_TOP/util/dvsim/dvsim.py $REPO_TOP/hw/ip/usbdev/dv/usbdev_sim_cfg.hjson -i usbdev_smoke
```

## Testplan
[Testplan](../data/usbdev_testplan.hjson)
