# Hardware Interfaces

## Signals

<!-- BEGIN CMDGEN util/regtool.py --interfaces ./hw/top_${topname}/ip_autogen/${module_instance_name}/data/${module_instance_name}.hjson -->
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
`pwrmgr_o`           | `output`         | `pwrmgr_pkg::cpu_pwrmgr_t`             | Low-power CPU status to power manager.
`edn_i`              | `input`          | `edn_pkg::edn_rsp_t`                   | Incoming entropy response from entropy distribution network.
`edn_o`              | `output`         | `edn_pkg::edn_req_t`                   | Outgoing entropy request to entropy distribution network.
`icache_otp_key_i`   | `input`          | `otp_ctrl_pkg::sram_otp_key_rsp_t`     | Incoming scrambling key response from OTP to icache.
`icache_otp_key_o`   | `output`         | `otp_ctrl_pkg::sram_otp_key_req_t`     | Outgoing scrambling key request from icache to OTP.


The `PipeLine` parameter can be used to configure the bus adapter pipelining.

* Setting `PipeLine` to `0` disables pipelining, which gives minimal latency between the bus and the core, at the cost of a combinatorial path into the core.
* Setting `PipeLine` to `1` introduces a pipelining FIFO between the core instruction/data interfaces and the bus.
  This setting increases the memory access latency, but improves timing.
