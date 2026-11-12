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
* Alerts ([`alert_esc_if`](../../../dv/sv/alert_agent/README.md))
* `rram_ctrl_otp_key_if`: the `otp_ctrl` scrambling-key request/response handshake, driven by `rram_ctrl_otp_key_driver` (see [OTP key driver](#otp-key-driver) below)
* `rram_ctrl_otp_macro_if`: the `otp_ctrl` macro interface in the OTP clock domain, through which `otp_ctrl` stores OTP data in the RRAM.
  Its `send()` task issues one command and waits for the response.
* `rram_ctrl_misc_io_if`: the life cycle qualifiers, the RMA handshake, the key manager seeds and the power manager indication.
  All DUT inputs on it are driven to known values from time zero.

It also creates the backdoor utilities of `hw/ip/rram_ctrl/dv/bkdr` for the data array, the info array and the OTP region of the data array, and sets them into `uvm_config_db`.
Unlike in the chip testbench, the data array utility covers the OTP pages too, so that tests can check the OTP integrity page.

### Common DV utility components
The following utilities provide generic helper tasks and functions to perform activities that are common across the project:
* [dv_utils_pkg](../../../dv/sv/dv_utils/README.md)
* [csr_utils_pkg](../../../dv/sv/csr_utils/README.md)

### Compile-time configurations
`tb.sv` locally defines `WrFifoDepth`/`RdFifoDepth`, mirroring two of the DUT's RTL parameters, to elaborate the DUT instance.
It passes both to the environment via `uvm_config_db`, and `rram_ctrl_env_cfg` picks them up into `m_wr_fifo_depth`/`m_rd_fifo_depth` in `build_phase`.
`rram_ctrl_env_pkg`'s `OTP_CLK_FREQ_MHZ` configures the OTP clock generator before the environment even exists, so it stays a package parameter rather than going through the same path.

### Global types & methods
All common types and methods defined at the package level can be found in `rram_ctrl_env_pkg`.
Some of them in use are:
```systemverilog
typedef enum int {
  WrEmpty, WrLvl, RdFull, RdLvl, OpDone, Corr1Err, Corr2Err, NumRramCtrlIntr
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
`rram_ctrl` testbench instantiates (already handled in CIP base env) [alert_agents](../../../dv/sv/alert_agent/README.md):
`recov_err`, `fatal_std_err`, `fatal_err`, `fatal_macro_err`, `recov_macro_err`.
The alert_agents provide the ability to drive and independently monitor alert handshakes via alert interfaces in RRAM_CTRL device.

### OTP key driver
`rram_ctrl_otp_key_if` (see above) has two independent DUT key-request lines, address and data scrambling, that never fire at the same time.
`rram_ctrl_env` instantiates two `rram_ctrl_otp_key_driver` instances (one per line, both bound to the same interface).
Each driver randomizes its own `key`/`rand_key` pair once in `build_phase` and answers every request on its line with that same pair for the life of the test, matching real OTP key-derivation semantics (the derived key doesn't change without a full re-provisioning).
Address and data key material are independent, since each driver randomizes separately.
`rram_ctrl_env` copies both keys into `rram_ctrl_env_cfg`, which needs them to scramble and descramble data through the backdoor.
The key stays in place after the ack, since the DUT only samples it once the ack has crossed into its own clock domain.

The req/ack handshake is driven through `vif.host_cb`, a clocking block synced to `vif.clk` (the DUT's `clk_otp_i`), rather than raw signal reads/writes.
The DUT's `u_addr_sync_reqack`/`u_data_sync_reqack` (`prim_sync_reqack`) assert every `clk_otp_i` cycle that ack is never high while req is low, which constrains how req is sampled and how ack's deassertion is timed:

- **Sampling req**: done via `vif.host_cb.req`. The clocking block's default input skew samples
  it in the Preponed region, just before the clock edge, avoiding the race a raw
  `@(posedge vif.clk)` read would have with the DUT's own same-edge `always_ff` update.
- **Asserting ack**: delayed by a randomized `ack_delay_cycles` (`[0:5]`, re-randomized per
  request) after req is seen. A real otp_ctrl's response latency isn't fixed and the DUT must
  tolerate any value here. Only the deassertion is constrained, not the assertion.
- **Deasserting ack**: exactly one `vif.clk` cycle after asserting it, unconditionally (no
  polling req). `prim_sync_reqack`'s DST-side FSM latches the handshake
  (`dst_req_o & dst_ack_i`) the cycle after ack becomes visible, then flips its
  externally-visible req low the cycle after that, via NRZ toggle encoding that's decoupled
  from how long the real SRC-side round trip takes, so req is guaranteed already low one
  cycle after this wait. This deassertion is a write (`ack <= 0`), not a read, so it doesn't
  race the DUT's same-edge update the way sampling req does: NBA guarantees the DUT's read of
  ack for the handshake-latching edge sees the pre-write value regardless of process order.

`run_phase` races handling requests against `wait (!vif.rst_n)` (`reset_kill`) via `fork`/`join_any`/`disable fork`.
On reset, this kills any in-flight request handling, redrives all outputs to idle, and restarts.

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

This object aims to provide such run-time controls.
`rram_ctrl` does not currently define one.
Instead, `rram_ctrl_env_cfg` holds a few knobs that `rram_ctrl_base_test` reads from plusargs:
* `scr_en_pct`, `reg_en_pct`, `wr_en_pct`, `rd_en_pct`, `ecc_en_pct`: the probability in percent that a randomly configured region or page gets the corresponding property enabled
* `skip_init_data_array`, `skip_init_info_array`: skip zeroing the arrays through the backdoor during initialization
* `skip_lc_init`: skip starting the controller's initialization, so that a test can do it itself

#### Env cfg
The `rram_ctrl_env_cfg`, environment configuration object provides access to the following elements:
* Build-time controls to configure the UVM environment composition during the `build_phase`
* Downstream agent configuration objects for ease of lookup from any environment component
  * This includes the `tl_agent_cfg` objects for both TL interfaces
* All virtual interfaces that connect to the DUT listed above (retrieved from the `uvm_config_db`)
* A sequence configuration object, once one is added (see above)
* The backdoor utilities, together with `rram_bkdr_word_read()`/`rram_bkdr_word_write()`/`rram_bkdr_mem_read()`/`rram_bkdr_mem_write()`, which add or remove the address infection and scrambling the controller applies, and `otp_bkdr_read()`, which also checks the OTP integrity
* `mp_model`, the memory protection model (see [Scoreboard](#scoreboard) below)

All environment components contain a handle to an instance of this class (that was created in the test class via the parent `dv_base_test`).
By housing all of the above, all pertinent information is more easily shared with all environment components.

### Stimulus strategy
#### Test sequences
All test sequences reside in `hw/ip/rram_ctrl/dv/env/seq_lib`.
The `rram_ctrl_base_vseq` virtual sequence is extended from `cip_base_vseq` and serves as a starting point.
All test sequences are extended from `rram_ctrl_base_vseq`.
It provides commonly used handles, variables, functions and tasks that the test sequences can simple use / call.
Some of the most commonly used tasks / functions are as follows, from `hw/ip/rram_ctrl/dv/env/seq_lib/rram_ctrl_base_vseq.sv`:
* `dut_init()`: resets the DUT, calls `rram_ctrl_init()` and sends the OTP Init command
* `rram_ctrl_init()`: polls the phy's own init, zeroes the arrays through the backdoor, then triggers and polls the controller's INIT sequence (lc key derivation etc), without which the arbiter never grants software/host access
* `update_default_region_cfg()`, `update_mp_region()`, `update_info_page_cfg()`: configure memory protection
* `rram_ctrl_write()`, `rram_ctrl_read()`, `rram_ctrl_rewrite()`: run an operation on the controller interface and check the data against the backdoor contents and the memory protection model
* `rram_host_read()`: reads a word through the host interface
* `otp_read()`, `otp_write()`, `otp_zeroize()`: run a command on the OTP macro interface and check the result against the backdoor contents
* `rma_req()`: requests RMA entry and waits for its acknowledgement
* `apply_reset()` / `apply_resets_concurrently()`: reset both the core and OTP clock domains together, since each clock generator blocks on its own domain's reset

#### Functional coverage
To ensure high quality constrained random stimulus, it is necessary to develop a functional coverage model.
No covergroups have been developed yet.
`rram_ctrl_env_cov` is currently an empty stub extending `cip_base_env_cov`.

### Self-checking strategy
#### Scoreboard
`rram_ctrl_scoreboard` extends `cip_base_scoreboard`, which wires up an analysis port per TL agent (core, host, prim) automatically.
Each transaction is dispatched through the overridden `process_tl_access()`, which routes core-CSR accesses to `process_tl_core_access()` and prim accesses to `process_tl_prim_access()` for checking against the register/memory model.

`process_tl_core_access()` itself only dispatches by address kind, to `on_reg_access()` or `on_mem_access()`.
An unmapped address is handled inline instead of through a third handler, since it should be unreachable (see below).
Register prediction (including regwen-gating) is automatic: `rram_ctrl_scoreboard` owns a `uvm_reg_predictor` on the core TL interface, using a `tl_reg_adapter` instance configured the same way as `cip_base_env`'s own (private) frontdoor adapter.
`rram_ctrl_env` connects the core TL monitor to it, since only the env has access to the TL agents.
`on_reg_access()` itself is a no-op today: the read-value check happens on the predictor's side instead, via `ral.default_map.set_check_on_read(1)` (set in `configure_csr_check_exclusions()`, called from `connect_phase`).
This matters because `uvm_reg_predictor::write()` compares the observed read data against the mirror *before* `do_predict()` overwrites it with that same data.
A check in `on_reg_access()` would run too late to be meaningful, since by the time `process_tl_access()` gets to it, prediction has already forced the mirror to match.
`configure_csr_check_exclusions()` also walks every register/field and calls `set_compare(UVM_NO_CHECK)` wherever a `CsrExclCheck`-family exclusion applies in the register spec (e.g. `PHY_STATUS.init_done`, which changes value due to hardware initialization independent of software writes, so the RAL mirror can never predict it.
`rram_ctrl_base_vseq::rram_ctrl_init()` polls exactly this field during DUT bring-up, in every test).
Those excluded fields get no check at all right now.
`on_reg_access()` is where a targeted, hand-rolled check for them would go.
`rram_ctrl_reg_predictor_filter` sits between the TL monitor and the predictor, dropping `d_error`'d items before `uvm_reg_predictor::write()` ever sees them.
This has to happen upstream of the predictor: `uvm_reg_predictor::write()` calls `do_predict()` unconditionally and never checks the bus item's status.
Without the filter, error-injection traffic (e.g. from `run_tl_errors_vseq`) mispredicts rejected writes as successful, and an errored read (`d_data` is undefined per TileLink on `d_error=1`) can corrupt even read-only fields via `UVM_PREDICT_READ`, which overwrites the mirror unconditionally regardless of access policy.
`on_mem_access()` covers the core regfile's `wr_fifo`/`rd_fifo` windows and is currently an empty stub (real FIFO-occupancy tracking is future work).
An unmapped address should be unreachable: `cip_base_scoreboard`'s own `predict_tl_err()` already predicts and checks `d_error` for unmapped addresses generically, before `process_tl_access()` is even called, so `process_tl_core_access()` just flags it with a `uvm_error` inline rather than dispatching to a dedicated handler.

The scoreboard also predicts memory protection errors on the host interface.
`rram_ctrl_mp_model` holds the effective configuration of every page for software and host requests, mirroring `rram_ctrl_region_cfg.sv` and `rram_ctrl_mp.sv`.
This covers the OTP exclusion, the emulated info page windows and subregions, the memory protection regions, the default region and the info pages, including their life cycle gating.
It is derived from the mirrored values of the core RAL model.
Whenever `on_reg_access()` sees a write to a register that affects the data pages, it flags the model as stale, and the model recomputes the pages on its next lookup.
`is_tl_mem_access_allowed()` uses the model to add an error for host reads of pages without read permission.
Once a test requests RMA entry, host accesses are no longer checked, since the DUT then denies all accesses from a point in time the model cannot predict.
The test sequences use the same model to compute the expected data of controller operations.

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
