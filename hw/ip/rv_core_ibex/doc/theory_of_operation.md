# Theory of Operation

## Simple Address Translation

The wrapper supports a simple address translation scheme.
The goal of the scheme is to provide hardware support for A/B software copies.

Each copy of the software is stored at a different location.
Depending upon which execution slot is active, a different copy is used.
This creates an issue because each copy of software has different addresses and thus must be linked differently.
Ideally, software should be able to assume one address all the time, and the hardware should remap to the appropriate physical location.

The translation scheme is based on NAPOT (natural alignment to power of two).
Software picks a matching region and also a remap address.
When an incoming transaction matches the selected power-of-2 region, it is redirected to the new address.
If a transaction does not match, then it is directly passed through.

This allows software to place the executable code at a virtual address in the system and re-map that to the appropriate physical block.

There are separate translations controls for instruction and data.
Each control contains two programmable regions (2 for instruction and 2 for data).
If a transaction matches multiple regions, the lowest indexed region has priority.

For details on how to program the related registers, please see [`IBUS_ADDR_MATCHING_0`](../data/rv_core_ibex.hjson#ibus_addr_matching_0) and [`IBUS_REMAP_ADDR_0`](../data/rv_core_ibex.hjson#ibus_remap_addr_0).

### Translation and Instruction Caching

The simple address translation scheme used in this design is not aware of the processor context, specifically, any instruction caching done in the core.
This means if the address translation scheme were to change, instructions that are already cached may not reflect the updated address setting.

In order to correctly utilize simple address translation along with instruction caching, it is recommended that after the address is updated a `FENCE.I` instruction is issued.
The `FENCE.I` instruction forces the instruction cache to flush, and this aligns the core to the new address setting.

## Random Number Generation

The wrapper has a connection to the [Entropy Distribution Network (EDN)](../../edn/README.md) with a register based interface.
The [`RND_DATA`](../data/rv_core_ibex.hjson#rnd_data) register provides 32-bits directly from the EDN.
[`RND_STATUS.RND_DATA_VALID`](../data/rv_core_ibex.hjson#rnd_status) indicates if the data in [`RND_DATA`](../data/rv_core_ibex.hjson#rnd_data) is valid or not.
A polling style interface is used to get new random data.
Any read to [`RND_DATA`](../data/rv_core_ibex.hjson#rnd_data) when it is valid invalidates the data and triggers an EDN request for new data.
Software should poll [`RND_STATUS.RND_DATA_VALID`](../data/rv_core_ibex.hjson#rnd_status) until it is valid and then read from [`RND_DATA`](../data/rv_core_ibex.hjson#rnd_data) to get the new random data.
Either the data is valid or a request for new data is pending.
It is not possible to have a state where there is no valid data without new data being requested.

Upon reset [`RND_DATA`](../data/rv_core_ibex.hjson#rnd_data) is invalid.
A request is made to the EDN immediately out of reset, this will not be answered until the EDN is enabled.
Software should take care not to enable the EDN until the entropy complex configuration is as desired.
When the entropy complex configuration is changed reading [`RND_DATA`](../data/rv_core_ibex.hjson#rnd_data) when it is valid will suffice to flush any old random data to trigger a new request under the new configuration.
If a EDN request is pending when the entropy complex configuration is changed ([`RND_STATUS.RND_DATA_VALID`](../data/rv_core_ibex.hjson#rnd_status) is clear), it is advisable to wait until it is complete and then flush out the data to ensure the fresh value was produced under the new configuration.

## Crash Dump Collection

In general, when the CPU encounters an error, it is software's responsibility to collect error status and supply it for debug.

However, there are situations where it may not be possible for software to collect any error logging.
These situations include but are not limited to:
* A hung transaction that causes watchdog to expire.
* A double fault that causes the processor to stop execution.
* An alert escalation that directly resets the system without any software intervention.

Under these situations, the software has no hints as to where the error occurred.
To mitigate this issue, Ibex provides crash dump information that can be directly captured in the `rstmgr` for last resort debug after the reset event.

The Ibex crash dump state contains 5 words of debug data:
* word 0: The last exception address (`mtval`)
* word 1: The last exception PC (`mepc`)
* word 2: The last data access address
* word 3: The next PC
* word 4: The current PC

The crash dump information transmitted to the `rstmgr` contains 7 words of debug data and a 1-bit valid indication:
* words 0-4: The current crash dump state
* word 5: The previous exception address (`mtval`)
* word 6: The previous exception PC (`mepc`)
* MSB: Previous state valid indication.

Under normal circumstances, only the current crash dump state is valid.
When the CPU encounters a double fault, the current crash dump is moved to previous, and the new crash dump is shown in current.

This allows the software to see both fault locations and debug accordingly.

In terms of how the crash state information can be used, the following are a few examples.

### Hung Transaction

Assuming the system has a watchdog counter setup, when a CPU transaction hangs the bus (accessing a device whose clock is not turned on or is under reset), the PC and bus access freeze in place until the watchdog resets the system.
Upon reset release, software can check the last PC and data access address to get an idea of what transaction might have caused the bus to hang.

### Double Exception

If the software has some kind of error and encounters two exceptions in a row, the previous exception PC and address show the location of the first exception, while the current exception address and PC show the location of the most recent exception.


## Fetch Enable

Ibex has a top-level fetch enable input (``fetch_enable_i``), which uses the same multi-bit encoding used by the lifecycle controller.
When Ibex fetch is disabled it will cease to execute, but will complete instructions currently in the pipeline.
Ibex fetch is enabled when all of the following conditions are met:
  - The lifecycle controller has enabled it
  - The power manager has enabled it
  - A ``fatal_hw_err`` alert hasn't been raised

### Local Escalation Path

When the ``fatal_hw_err`` alert is raised Ibex fetch is disabled and will remain disabled until ``rv_core_ibex`` is reset.

## Hardware Interfaces

### Signals

* [Interface Tables](../data/rv_core_ibex.hjson#interfaces)

All ports and parameters of Ibex are exposed through this wrapper module, except for the instruction and data memory interfaces (signals starting with `instr_` and `data_`).
Refer to the [Ibex documentation](https://ibex-core.readthedocs.io/en/latest/02_user/integration.html) for a detailed description of these signals and parameters.

The instruction and data memory ports are exposed as TL-UL ports.
The table below lists other signals and the TL-UL ports.

Signal               | Direction        | Type                                   | Description
---------------------|------------------|----------------------------------------|---------------
`rst_cpu_n_o`        | `output`         | `logic`                                | Outgoing indication to reset manager that the process has reset.
`ram_cfg_i`          | `input`          | `prim_ram_1p_pkg::ram_1p_cfg_t`        | Incoming memory configuration that is technology dependent.
`hart_id_i`          | `input`          | `logic [31:0]`                         | Static Hard ID input signal.
`boot_addr_i`        | `input`          | `logic [31:0]`                         | Static boot address input signal.
`fpga_info_i`        | `input`          | `logic [31:0]`                         | Fpga info input signal, coming from a Xilinx USR_ACCESSE2 primitive for example.
`irq_software_i`     | `input`          | `logic`                                | Software interrupt input.
`irq_timer_i`        | `input`          | `logic`                                | Timer interrupt input.
`irq_external_i`     | `input`          | `logic`                                | External interrupt input.
`debug_req_i`        | `input`          | `logic`                                | Debug request from the debug module.
`corei_tl_h_o`       | `output`         | `tlul_pkg::tl_h2d_t`                   | Outgoing instruction tlul request.
`corei_tl_h_i`       | `input`          | `tlul_pkg::tl_d2h_t`                   | Incoming instruction tlul response.
`cored_tl_h_o`       | `output`         | `tlul_pkg::tl_h2d_t`                   | Outgoing data tlul request.
`cored_tl_h_i`       | `input`          | `tlul_pkg::tl_d2h_t`                   | Incoming data tlul response.
`cfg_tl_d_i`         | `output`         | `tlul_pkg::tl_h2d_t`                   | Outgoing data tlul request for peripheral registers.
`cfg_tl_d_o`         | `input`          | `tlul_pkg::tl_d2h_t`                   | Incoming data tlul response for peripheral registers.
`alert_rx_i`         | `input`          | `prim_alert_pkg::alert_rx_t`           | Incoming alert response / ping.
`alert_tx_o`         | `output`         | `prim_alert_pkg::alert_tx_t`           | Outgoing alert request.
`esc_tx_i`           | `input`          | `prim_esc_pkg::esc_tx_t`               | Incoming escalation request / ping.
`esc_rx_o`           | `output`         | `prim_esc_pkg::esc_rx_t`               | Outgoing escalation response.
`nmi_wdog_i`         | `input`          | `logic`                                | Incoming watchdog NMI bark.
`crash_dump_o`       | `output`         | `ibex_pkg::crash_dump_t`               | Outgoing crash dump information to rstmgr.
`cfg_tl_d_i`         | `input`          | `tlul_pkg::tl_h2d_t`                   | Incoming configuration bus request.
`cfg_tl_d_o `        | `output`         | `tlul_pkg::tl_d2h_t`                   | Outgoing configuration bus response.
`lc_cpu_en_i`        | `input`          | `lc_ctrl_pkg::lc_tx_t`                 | CPU enable signal from life cycle controller.
`pwrmgr_cpu_en_i`    | `input`          | `lc_ctrl_pkg::lc_tx_t`                 | CPU enable signal from power manager.
`pwrmgr_o`           | `output`         | `pwrmgr_pkg::pwr_cpu_t`                | Low-power CPU status to power manager.
`edn_i`              | `input`          | `edn_pkg::edn_rsp_t`                   | Incoming entropy response from entropy distribution network.
`edn_o`              | `output`         | `edn_pkg::edn_req_t`                   | Outgoing entropy request to entropy distribution network.
`icache_otp_key_i`   | `input`          | `otp_ctrl_pkg::sram_otp_key_rsp_t`     | Incoming scrambling key response from OTP to icache.
`icache_otp_key_o`   | `output`         | `otp_ctrl_pkg::sram_otp_key_req_t`     | Outgoing scrambling key request from icache to OTP.


The `PipeLine` parameter can be used to configure the bus adapter pipelining.

* Setting `PipeLine` to `0` disables pipelining, which gives minimal latency between the bus and the core, at the cost of a combinatorial path into the core.
* Setting `PipeLine` to `1` introduces a pipelining FIFO between the core instruction/data interfaces and the bus.
  This setting increases the memory access latency, but improves timing.
