# Hardware Interfaces

## Signals

<!-- BEGIN CMDGEN util/regtool.py --interfaces ./hw/ip/rv_core_ibex/data/rv_core_ibex.hjson -->
Referring to the [Comportable guideline for peripheral device functionality](https://opentitan.org/book/doc/contributing/hw/comportability), the module **`rv_core_ibex`** has the following hardware interfaces defined
- Primary Clock: **`clk_i`**
- Other Clocks: **`clk_edn_i`**, **`clk_esc_i`**, **`clk_otp_i`**
- Bus Device Interfaces (TL-UL): **`cfg_tl_d`**
- Bus Host Interfaces (TL-UL): **`corei_tl_h`**, **`cored_tl_h`**
- Peripheral Pins for Chip IO: *none*
- Interrupts: *none*

## [Inter-Module Signals](https://opentitan.org/book/doc/contributing/hw/comportability/index.html#inter-signal-handling)

| Port Name      | Package::Struct                  | Type    | Act   |   Width | Description   |
|:---------------|:---------------------------------|:--------|:------|--------:|:--------------|
| rst_cpu_n      | logic                            | uni     | req   |       1 |               |
| ram_cfg        | prim_ram_1p_pkg::ram_1p_cfg      | uni     | rcv   |       1 |               |
| hart_id        | logic                            | uni     | rcv   |      32 |               |
| boot_addr      | logic                            | uni     | rcv   |      32 |               |
| irq_software   | logic                            | uni     | rcv   |       1 |               |
| irq_timer      | logic                            | uni     | rcv   |       1 |               |
| irq_external   | logic                            | uni     | rcv   |       1 |               |
| esc_tx         | prim_esc_pkg::esc_tx             | uni     | rcv   |       1 |               |
| esc_rx         | prim_esc_pkg::esc_rx             | uni     | req   |       1 |               |
| debug_req      | logic                            | uni     | rcv   |       1 |               |
| crash_dump     | rv_core_ibex_pkg::cpu_crash_dump | uni     | req   |       1 |               |
| lc_cpu_en      | lc_ctrl_pkg::lc_tx               | uni     | rcv   |       1 |               |
| pwrmgr_cpu_en  | lc_ctrl_pkg::lc_tx               | uni     | rcv   |       1 |               |
| pwrmgr         | pwrmgr_pkg::pwr_cpu              | uni     | req   |       1 |               |
| nmi_wdog       | logic                            | uni     | rcv   |       1 |               |
| edn            | edn_pkg::edn                     | req_rsp | req   |       1 |               |
| icache_otp_key | otp_ctrl_pkg::sram_otp_key       | req_rsp | req   |       1 |               |
| fpga_info      | logic                            | uni     | rcv   |      32 |               |
| corei_tl_h     | tlul_pkg::tl                     | req_rsp | req   |       1 |               |
| cored_tl_h     | tlul_pkg::tl                     | req_rsp | req   |       1 |               |
| cfg_tl_d       | tlul_pkg::tl                     | req_rsp | rsp   |       1 |               |

## Security Alerts

| Alert Name   | Description                                                                                                                                                                          |
|:-------------|:-------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------|
| fatal_sw_err | Software triggered alert for fatal faults                                                                                                                                            |
| recov_sw_err | Software triggered Alert for recoverable faults                                                                                                                                      |
| fatal_hw_err | Triggered when - Ibex raises `alert_major_internal_o` - Ibex raises `alert_major_bus_o` - A double fault is seen (Ibex raises `double_fault_seen_o`) - A bus integrity error is seen |
| recov_hw_err | Triggered when Ibex raises `alert_minor_o`                                                                                                                                           |

## Security Countermeasures

| Countermeasure ID                           | Description                                                                                                                                                                                      |
|:--------------------------------------------|:-------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------|
| RV_CORE_IBEX.BUS.INTEGRITY                  | End-to-end bus integrity scheme.                                                                                                                                                                 |
| RV_CORE_IBEX.SCRAMBLE.KEY.SIDELOAD          | The scrambling key for the icache is sideloaded from OTP and thus unreadable by SW.                                                                                                              |
| RV_CORE_IBEX.CORE.DATA_REG_SW.SCA           | Data independent timing.                                                                                                                                                                         |
| RV_CORE_IBEX.PC.CTRL_FLOW.CONSISTENCY       | Correct PC increment check.                                                                                                                                                                      |
| RV_CORE_IBEX.CTRL_FLOW.UNPREDICTABLE        | Randomized dummy instruction insertion.                                                                                                                                                          |
| RV_CORE_IBEX.DATA_REG_SW.INTEGRITY          | Register file integrity checking. Note that whilst the core itself is duplicated (see LOGIC.SHADOW) the register file is not. Protection is provided by an ECC.                                  |
| RV_CORE_IBEX.DATA_REG_SW.GLITCH_DETECT      | This countermeasure augments DATA_REG_SW.INTEGRITY and checks for spurious write-enable signals on the register file by monitoring the one-hot0 property of the individual write-enable strobes. |
| RV_CORE_IBEX.LOGIC.SHADOW                   | Shadow core run in lockstep to crosscheck CPU behaviour. This provides broad protection for all assets with the Ibex core.                                                                       |
| RV_CORE_IBEX.FETCH.CTRL.LC_GATED            | Fetch enable so core execution can be halted.                                                                                                                                                    |
| RV_CORE_IBEX.EXCEPTION.CTRL_FLOW.LOCAL_ESC  | A mechanism to detect and act on double faults. Local escalation shuts down the core when a double fault is seen.                                                                                |
| RV_CORE_IBEX.EXCEPTION.CTRL_FLOW.GLOBAL_ESC | A mechanism to detect and act on double faults. Global escalation sends a fatal alert when a double fault is seen.                                                                               |
| RV_CORE_IBEX.ICACHE.MEM.SCRAMBLE            | ICache memory scrambling.                                                                                                                                                                        |
| RV_CORE_IBEX.ICACHE.MEM.INTEGRITY           | ICache memory integrity checking.                                                                                                                                                                |


<!-- END CMDGEN -->

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
