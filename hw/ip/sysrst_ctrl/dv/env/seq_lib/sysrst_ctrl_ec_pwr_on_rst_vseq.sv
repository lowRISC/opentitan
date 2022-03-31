// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// This sequence will verify the ec and power on reset sequence.
// It will explicitly release the reset by disabling the override
// function and stretching the ec reset to the value configured in
// ec_rst_ctl register
class sysrst_ctrl_ec_pwr_on_rst_vseq extends sysrst_ctrl_base_vseq;
  `uvm_object_utils(sysrst_ctrl_ec_pwr_on_rst_vseq)

  `uvm_object_new

   rand uint16_t set_ec_rst_timer;

   constraint set_ec_rst_timer_c {
    set_ec_rst_timer dist {
      [10:100] :/ 95,
      [101:$]   :/ 5
    };
    }

   task body();
    uint16_t get_ec_rst_timer;

    `uvm_info(`gfn, "Starting the body from ec_pwr_on_rst_vseq", UVM_LOW)

    // Explicitly release the EC reset
    // Disable the override function
    ral.pin_out_ctl.ec_rst_l.set(0);
    csr_update(ral.pin_out_ctl);

    // Configure the EC_RST_CTL register to stretch the EC rst
    csr_wr(ral.ec_rst_ctl, set_ec_rst_timer);

    // Get the ec_rst timer value
    csr_rd(ral.ec_rst_ctl, get_ec_rst_timer);

    // check ec_rst_l asserts for ec_rst_timer cycles after reset
    monitor_ec_rst_low(get_ec_rst_timer);

    repeat ($urandom_range(2, 4)) begin
      cfg.clk_aon_rst_vif.wait_clks(10);

      // remains high
      `DV_CHECK_EQ(cfg.vif.ec_rst_l_out, 1);

      fork
        begin
          driver_ec_rst_l_in($urandom_range(1, get_ec_rst_timer * 2));
        end
        begin
          monitor_ec_rst_low(get_ec_rst_timer);
        end
      join
    end

    cfg.clk_aon_rst_vif.wait_clks(20);
   endtask : body

endclass : sysrst_ctrl_ec_pwr_on_rst_vseq
