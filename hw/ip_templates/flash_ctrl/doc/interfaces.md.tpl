# Interfaces

<!-- BEGIN CMDGEN util/regtool.py --interfaces ./hw/top_${topname}/ip_autogen/flash_ctrl/data/flash_ctrl.hjson -->
<!-- END CMDGEN -->

${"##"} Signals

In addition to the interrupts and bus signals, the tables below lists the flash controller functional I/Os.

Signal                     | Direction      | Description
------------------------   |-----------     |---------------
`lc_creator_seed_sw_rw_en` | `input`        | Indication from `lc_ctrl` that software is allowed to read/write creator seed.
`lc_owner_seed_sw_rw_en`   | `input`        | Indication from `lc_ctrl` that software is allowed to read/write owner seed.
`lc_seed_hw_rd_en`         | `input`        | Indication from `lc_ctrl` that hardware is allowed to read creator / owner seeds.
`lc_iso_part_sw_rd_en`     | `input`        | Indication from `lc_ctrl` that software is allowed to read the isolated partition.
`lc_iso_part_sw_wr_en`     | `input`        | Indication from `lc_ctrl` that software is allowed to write the isolated partition.
`lc_escalate_en`           | `input`        | Escalation indication from `lc_ctrl`.
`lc_nvm_debug_en`          | `input`        | Indication from lc_ctrl that non-volatile memory debug is allowed.
`core_tl`                  | `input/output` | TL-UL interface used to access `flash_ctrl` registers for activating program / erase and reads to information partitions/
`prim_tl`                  | `input/output` | TL-UL interface used to access the vendor flash memory proprietary registers.
`mem_tl`                   | `input/output` | TL-UL interface used by host to access the vendor flash memory directly.
`OTP`                      | `input/output` | Interface used to request scrambling keys from `otp_ctrl`.
`rma_req`                  | `input`        | rma entry request from `lc_ctrl`.
`rma_ack`                  | `output`       | rma entry acknowlegement to `lc_ctrl`.
`rma_seed`                 | `input`        | rma entry seed.
`pwrmgr`                   | `output`       | Idle indication to `pwrmgr`.
`keymgr`                   | `output`       | Secret seed bus to `keymgr`.

In addition to the functional IOs, there are a set of signals that are directly connected to vendor flash module.

Signal                     | Direction      | Description
------------------------   |-----------     |---------------
`scan_en`                  | `input`        | scan enable
`scanmode`                 | `input`        | scan mode
`scan_rst_n`               | `input`        | scan reset
`flash_bist_enable`        | `input`        | enable flash built-in-self-test
`flash_power_down_h`       | `input`        | flash power down indication, note this is NOT a core level signal
`flash_power_ready_h`      | `input`        | flash power ready indication, note this is NOT a core level signal
`flash_test_mode_a`        | `input/output` | flash test mode io, note this is NOT a core level signal
`flash_test_voltage_h`     | `input/output` | flash test voltage, note this is NOT a core level signal
`flash_alert`              | `output`       | flash alert outputs directly to AST
