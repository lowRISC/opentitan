// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// class : gpio_rand_intr_trigger_vseq
// This gpio random test sequence performs following in each of multiple iterations:
//  (i) programs random values to a set of selected registers out of following:
//      INTR_ENABLE
//      INTR_CTRL_EN_LVL_LOW
//      INTR_CTRL_EN_LVL_HIGH
//      INTR_CTRL_EN_FALLING
//      INTR_CTRL_EN_RISING
// (ii) performs following two in operations in parallel:
//     - drive random value on gpio_i input
//     - perform periodic read and random clearing of INTR_STATE register
class gpio_rand_intr_trigger_vseq extends gpio_base_vseq;

  constraint num_trans_c {
    num_trans inside {[20:200]};
  }

  `uvm_object_utils(gpio_rand_intr_trigger_vseq)
  `uvm_object_new

  task body();
    `uvm_info(`gfn, $sformatf("num_trans = %0d", num_trans), UVM_HIGH)
    for (uint tr_num = 0; tr_num < num_trans; tr_num++) begin
      string msg_id = {`gfn, $sformatf(" Transaction-%0d", tr_num)};

      `DV_CHECK_MEMBER_RANDOMIZE_FATAL(delay)
      cfg.clk_rst_vif.wait_clks(delay);
      `uvm_info(msg_id, $sformatf("delay = %0d", delay), UVM_HIGH)

      // Step-1 Program interrupt registers
      pgm_intr_regs();

      // Step-2 Do the following operations in parallel:
      //   (i) toggle gpio_i input at random intervals
      //  (ii) inject random read on gpio "intr_state" register
      begin
        uint rd_period;
        uint cnt_gpio_tgl;
        bit gpio_tgl_cycle_done;
        `DV_CHECK_STD_RANDOMIZE_WITH_FATAL(cnt_gpio_tgl, cnt_gpio_tgl inside {[5:20]};)
        `DV_CHECK_STD_RANDOMIZE_WITH_FATAL(rd_period, rd_period inside {[2:20]};)
        fork
          begin : gpio_in_data_drive
            for (uint iter = 0; iter < cnt_gpio_tgl; iter++) begin
              bit [TL_DW-1:0] gpio_i;
              bit [TL_DW-1:0] data_in;
              `DV_CHECK_STD_RANDOMIZE_WITH_FATAL(gpio_i)
              cfg.gpio_vif.drive(gpio_i);
              cfg.clk_rst_vif.wait_clks(1);
              // read data_in register
              csr_rd(.ptr(ral.data_in), .value(data_in));
            end
            gpio_tgl_cycle_done = 1'b1;
          end
          begin : periodic_intr_state_rd_check
            do begin
              bit [TL_DW-1:0] intr_state;
              cfg.clk_rst_vif.wait_clks(rd_period);
              // read intr_state register
              csr_rd(.ptr(ral.intr_state), .value(intr_state));
              // Randomly clear random set of interrupt state register bits
              if ($urandom_range(0, 1)) begin
                `DV_CHECK_RANDOMIZE_FATAL(ral.intr_state)
                csr_update(ral.intr_state);
              end
            end
            while (gpio_tgl_cycle_done != 1'b1);
          end
        join
      end

      `uvm_info(msg_id, "End of Transaction", UVM_HIGH)

    end // end for

  endtask : body

endclass : gpio_rand_intr_trigger_vseq
