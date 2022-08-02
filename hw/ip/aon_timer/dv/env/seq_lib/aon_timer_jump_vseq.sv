// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// jump test vseq
class aon_timer_jump_vseq extends aon_timer_base_vseq;
  `uvm_object_utils(aon_timer_jump_vseq)

  // Randomize Bark/Bite and Wake-up thresholds for the counter
  rand bit [31:0] wkup_count;
  rand bit [31:0] wdog_count;

  rand bit [31:0] wkup_thold;
  rand bit [31:0] wdog_bark_thold;
  rand bit [31:0] wdog_bite_thold;

  constraint count_vals_c {
    wkup_count inside {[wkup_thold-10:wkup_thold+10]};
    wdog_count inside {[wdog_bark_thold-10:wdog_bark_thold+10]};
  }
  `uvm_object_new


  task body();

    aon_timer_init();
    jump_configure();
    wait_for_interrupt();
    aon_timer_shutdown();

  endtask : body

  // setup basic aon_timer features
  task aon_timer_init();

    `uvm_info(`gfn, "Initializating AON Timer. Writing 0 to WKUP_COUNT and WDOG_COUNT", UVM_LOW)
    // Register Write
    csr_utils_pkg::csr_wr(ral.wkup_count, 32'h0000_0000);
    csr_utils_pkg::csr_wr(ral.wdog_count, 32'h0000_0000);

    `uvm_info(`gfn, "Randomizing AON Timer thresholds", UVM_HIGH)

    `uvm_info(`gfn, $sformatf("Writing 0x%0h to wkup_thold", wkup_thold), UVM_HIGH)
    csr_utils_pkg::csr_wr(ral.wkup_thold, wkup_thold);

    `uvm_info(`gfn, $sformatf("Writing 0x%0h to wdog_bark_thold", wdog_bark_thold), UVM_HIGH)
    csr_utils_pkg::csr_wr(ral.wdog_bark_thold, wdog_bark_thold);

    `uvm_info(`gfn, $sformatf("Writing 0x%0h to wdog_bite_thold", wdog_bite_thold), UVM_HIGH)
    csr_utils_pkg::csr_wr(ral.wdog_bite_thold, wdog_bite_thold);

    cfg.lc_escalate_en_vif.drive(0);

    `uvm_info(`gfn, $sformatf("Writing 0x%0h to WDOG_REGWEN", wdog_regwen), UVM_HIGH)
    csr_utils_pkg::csr_wr(ral.wdog_regwen, wdog_regwen);

  endtask

  task jump_configure();

    // Write random value to the COUNT registers
    csr_utils_pkg::csr_wr(ral.wkup_count, wkup_count);
    `uvm_info(`gfn,
              $sformatf("\n\t Writing random COUNT value of %d to WKUP", wkup_count),
              UVM_HIGH)

    csr_utils_pkg::csr_wr(ral.wdog_count, wdog_count);
    `uvm_info(`gfn,
              $sformatf("\n\t Writing random COUNT value of %d to WDOG", wdog_count),
              UVM_HIGH)

    cfg.aon_clk_rst_vif.wait_clks(1);

    `uvm_info(`gfn, "Enabling AON Timer. Writing 1 to WKUP_CTRL and WDOG_CTRL", UVM_HIGH)
    csr_utils_pkg::csr_wr(ral.wdog_ctrl.enable, 1'b1);
    csr_utils_pkg::csr_wr(ral.wkup_ctrl.enable, 1'b1);

    `uvm_info(`gfn, "\n\t Waiting for AON Timer to finish (interrupt)", UVM_HIGH)
  endtask : jump_configure

endclass : aon_timer_jump_vseq
