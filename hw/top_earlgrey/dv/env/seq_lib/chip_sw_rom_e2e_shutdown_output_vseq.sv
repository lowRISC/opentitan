// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class chip_sw_rom_e2e_shutdown_output_vseq extends
  chip_sw_rom_e2e_base_vseq;
  `uvm_object_utils(chip_sw_rom_e2e_shutdown_output_vseq)
  `uvm_object_new

  virtual task body();
    super.body();

    foreach (lc_state_2_rom_lcv[lc_state]) begin
      `uvm_info(`gfn, $sformatf("Backdoor overwriting the lifecycle state and applying POR ..."),
        UVM_LOW)
      cfg.mem_bkdr_util_h[Otp].otp_write_lc_partition_state(lc_state);
      apply_reset();

      // Wait for retention SRAM initialization to be done before hooking up the UART agent to
      // prevent X's propagating as a result of multiple drivers on pins IOC3 and IOC4 (due to DFT
      // strap sampling in TestUnlocked* and RMA lifecycle states). Once the retention SRAM is
      // initialized, we have made it to `rom_main()`.
      `DV_WAIT(cfg.chip_vif.sram_ret_init_done == 1)
      connect_rom_uart_agent();

      check_uart_output_msg($sformatf("%0s\x0d\n", ROM_BANNER));
      check_uart_output_msg(
        $sformatf("BFV:%0s\x0d\nLCV:%0s\x0d", ROM_BFV_BAD_IDENTIFIER,
          lc_state_2_rom_lcv[lc_state]));

      disconnect_rom_uart_agent();
    end

    rom_e2e_test_boot_fault_success();
  endtask

endclass : chip_sw_rom_e2e_shutdown_output_vseq
