# RRAM_CTRL DV document

## Goals
* **DV**
  * Verify all RRAM_CTRL IP features by running dynamic simulations with a SV/UVM based testbench
  * Develop and run all tests based on the [testplan](#testplan) below towards closing code and functional coverage on the IP and all of its sub-modules
* **FPV**
  * Verify TileLink device protocol compliance with an SVA based testbench

## Current status
* [Design & verification stage](../../../../README.md)
  * [HW development stages](../../../../doc/project_governance/development_stages.md)
* [Simulation results](https://reports.opentitan.org/hw/ip/rram_ctrl/dv/latest/report.html)

## Design features
For detailed information on `rram_ctrl` design features, please see the [`rram_ctrl` HWIP technical specification](../README.md).

## Testbench architecture
The `rram_ctrl` UVM DV testbench has been constructed based on the [CIP testbench architecture](../../../dv/sv/cip_lib/README.md).

### Block diagram
![Block diagram](../doc/dv/tb.svg)

### Top level testbench
Top level testbench is located at `hw/ip/rram_ctrl/dv/tb.sv`.
It instantiates the `rram_ctrl` DUT module `hw/ip/rram_ctrl/rtl/rram_ctrl.sv`.
In addition, the testbench instantiates the following interfaces, connects them to the DUT and sets their handle into `uvm_config_db`:
* [Clock and reset interface](../../../dv/sv/common_ifs/README.md), one for the core clock domain and one for the OTP clock domain
* [TileLink host interface for the core CSRs](../../../dv/sv/tl_agent/README.md)
* [TileLink host interface for the host registers](../../../dv/sv/tl_agent/README.md) (the RRAM data array, `tl_host`)
* [TileLink host interface for the prim registers](../../../dv/sv/tl_agent/README.md) (the RRAM macro's `tl_prim` interface)
* Alerts ([`alert_esc_if`](../../../dv/sv/alert_esc_agent/README.md))
* `rram_ctrl_otp_key_if`: the `otp_ctrl` scrambling-key request/response handshake, modeled reactively by `otp_model()` in `rram_ctrl_base_vseq.sv` rather than driven by a dedicated agent

The DUT's other input-only signals (life cycle qualifiers, the RMA handshake) are not yet exercised by any test and are tied to fixed values directly in `tb.sv`.

### Common DV utility components
The following utilities provide generic helper tasks and functions to perform activities that are common across the project:
* [dv_utils_pkg](../../../dv/sv/dv_utils/README.md)
* [csr_utils_pkg](../../../dv/sv/csr_utils/README.md)

### Compile-time configurations
`rram_ctrl_env_pkg` mirrors two of the DUT's RTL parameters so `tb.sv` can use them to elaborate the DUT instance: `WrFifoDepth`/`RdFifoDepth` (write/read FIFO depths). `OTP_CLK_FREQ_MHZ` configures the OTP clock generator before the environment even exists, so it lives here too rather than in `rram_ctrl_env_cfg`.

### Global types & methods
All common types and methods defined at the package level can be found in `rram_ctrl_env_pkg`.
Some of them in use are:
```systemverilog
typedef enum int {
  WrEmpty, WrLvl, RdFull, RdLvl, OpDone, CorrErr, NumRramCtrlIntr
} rram_ctrl_intr_e;  // bit positions in intr_state/intr_enable/intr_test

typedef enum bit [1:0] {
  AddrRead, AddrWrite, DataRead, DataWrite
} tl_phase_e;  // TL transaction phase, used by the scoreboard

parameter string LIST_OF_ALERTS[NUM_ALERTS] = {
  "recov_err", "fatal_std_err", "fatal_err", "fatal_macro_err", "recov_macro_err"
};
```

### TL_agents
`rram_ctrl` UVM environment instantiates three (already handled in CIP base env) [tl_agent](../../../dv/sv/tl_agent/README.md) instances, which provide the ability to drive and independently monitor random traffic:
* one on the core interface, to access the core CSRs (Control/Status Registers)
* one on the host interface, to access the RRAM data array
* one on the prim interface, to access the RRAM macro's registers

The `tl_agent` monitors supply partial TileLink request packets as well as completed TileLink response packets over the TLM analysis port for further processing within the `rram_ctrl` scoreboard.

### Alert_agent
`rram_ctrl` testbench instantiates (already handled in CIP base env) [alert_agents](../../../dv/sv/alert_esc_agent/README.md):
`recov_err`, `fatal_std_err`, `fatal_err`, `fatal_macro_err`, `recov_macro_err`.
The alert_agents provide the ability to drive and independently monitor alert handshakes via alert interfaces in RRAM_CTRL device.

### UVM RAL Model
The `rram_ctrl` RAL model is created with the [`ralgen`](../../../dv/tools/ralgen/README.md) FuseSoC generator script automatically when the simulation is at the build stage.

It can be created manually by invoking [`regtool`](../../../../util/reggen/doc/setup_and_use.md):
```console
$ util/regtool.py -s hw/ip/rram_ctrl/data/rram_ctrl.hjson
```

#### Sequence cfg
An efficient way to develop test sequences is by providing some random variables that are used to configure the DUT / drive stimulus.
The random variables are constrained using weights and knobs that can be controlled.
These weights and knobs take on a "default" value that will result in the widest exploration of the design state space, when the test sequence is randomized and run as-is.
To steer the randomization towards a particular distribution or to achieve interesting combinations of the random variables, the test sequence can be extended to create a specialized variant.
In this extended sequence, nothing would need to be done, other than setting those weights and knobs appropriately.
This helps increase the likelihood of hitting the design corners that would otherwise be difficult to achieve, while maximizing reuse.

This object aims to provide such run-time controls. `rram_ctrl` does not currently define one; `rram_ctrl_base_vseq` relies on `cip_base_vseq`'s knobs directly.

#### Env cfg
The `rram_ctrl_env_cfg`, environment configuration object provides access to the following elements:
* Build-time controls to configure the UVM environment composition during the `build_phase`
* Downstream agent configuration objects for ease of lookup from any environment component
  * This includes the `tl_agent_cfg` objects for both TL interfaces
* All virtual interfaces that connect to the DUT listed above (retrieved from the `uvm_config_db`)
* A sequence configuration object, once one is added (see above)

All environment components contain a handle to an instance of this class (that was created in the test class via the parent `dv_base_test`).
By housing all of the above, all pertinent information is more easily shared with all environment components.

### Stimulus strategy
#### Test sequences
All test sequences reside in `hw/ip/rram_ctrl/dv/env/seq_lib`.
The `rram_ctrl_base_vseq` virtual sequence is extended from `cip_base_vseq` and serves as a starting point.
All test sequences are extended from `rram_ctrl_base_vseq`.
It provides commonly used handles, variables, functions and tasks that the test sequences can simple use / call.
Some of the most commonly used tasks / functions are as follows, from `hw/ip/rram_ctrl/dv/env/seq_lib/rram_ctrl_base_vseq.sv`:
* `dut_init()`: resets the DUT and calls `rram_ctrl_init()`
* `rram_ctrl_init()`: brings the controller out of reset — polls the phy's own init, then triggers and polls the controller's INIT sequence (lc key derivation etc), without which the arbiter never grants software/host access
* `apply_reset()` / `apply_resets_concurrently()`: reset both the core and OTP clock domains together, since each clock generator blocks on its own domain's reset
* `otp_model()`: a reactive task, started from `pre_start()`, that answers the DUT's addr/data OTP key requests over `rram_ctrl_otp_key_if`

#### Functional coverage
To ensure high quality constrained random stimulus, it is necessary to develop a functional coverage model.
No covergroups have been developed yet; `rram_ctrl_env_cov` is currently an empty stub extending `cip_base_env_cov`.

### Self-checking strategy
#### Scoreboard
`rram_ctrl_scoreboard` extends `cip_base_scoreboard`, which wires up an analysis port per TL agent (core, host, prim) automatically. Each transaction is dispatched through the overridden `process_tl_access()`, which routes core-CSR accesses to `process_tl_core_access()` and prim accesses to `process_tl_prim_access()` for checking against the register/memory model.

#### Assertions
* TLUL assertions: The `hw/ip/rram_ctrl/dv/sva/rram_ctrl_bind.sv` binds the `tlul_assert` [assertions](../../../ip/tlul/doc/TlulProtocolChecker.md) to the IP to ensure TileLink interface protocol compliance.
* Unknown checks on DUT outputs: The RTL has assertions to ensure all outputs are initialized to known values after coming out of reset.
* No block-specific assertion properties have been added yet.

## Building and running tests
The [dvsim](https://github.com/lowRISC/dvsim) tool is used for building and running our tests and regressions.
Please take a look at the link for detailed information on the usage, capabilities, features and known issues.
Here's how to run a smoke test:
```console
$ cd $REPO_TOP
$ dvsim hw/ip/rram_ctrl/dv/rram_ctrl_sim_cfg.hjson -i rram_ctrl_smoke
```

## Testplan
[Testplan](../data/rram_ctrl_testplan.hjson)
