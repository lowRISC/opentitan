// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class chip_sw_rom_e2e_jtag_inject_vseq extends chip_sw_base_vseq;
  `uvm_object_utils(chip_sw_rom_e2e_jtag_inject_vseq)
  `uvm_object_new

  virtual task pre_start();
    cfg.chip_vif.tap_straps_if.drive(JtagTapRvDm);
    super.pre_start();
  endtask

  virtual task body();
    lc_ctrl_state_pkg::lc_state_e lc_state = cfg.mem_bkdr_util_h[Otp].otp_read_lc_partition_state();
    super.body();
    // Wait for complete power up.
    `DV_WAIT(cfg.chip_vif.permgr_fast_pwr_state_active)

    // Enable UART0 to fetch console messages.
    `uvm_info(`gfn, "Configuring and connecting UART0", UVM_LOW)
    cfg.m_uart_agent_cfgs[0].set_parity(1'b0, 1'b0);
    cfg.m_uart_agent_cfgs[0].set_baud_rate(cfg.uart_baud_rate);
    cfg.m_uart_agent_cfgs[0].en_tx_monitor = 1;
    cfg.chip_vif.enable_uart(0, 1);

    cfg.sw_test_status_vif.can_pass_only_in_test = 0;
    #5ms;
    override_test_status_and_finish(0);
  endtask

endclass
