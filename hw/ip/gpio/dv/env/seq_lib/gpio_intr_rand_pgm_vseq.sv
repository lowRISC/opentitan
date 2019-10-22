// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// class : gpio_intr_rand_pgm_vseq
// This gpio random test sequence performs random no. of iteration such that
// each iteration will do either of the following operations:
// (i) drives random gpio input data values while gpio outputs are disabled
// (ii) programs random values to a set of selected registers out of following:
//      INTR_ENABLE
//      INTR_STATE
//      INTR_CTRL_EN_LVL_LOW
//      INTR_CTRL_EN_LVL_HIGH
//      INTR_CTRL_EN_FALLING
//      INTR_CTRL_EN_RISING
class gpio_intr_rand_pgm_vseq extends gpio_base_vseq;

  `uvm_object_utils(gpio_intr_rand_pgm_vseq)
  `uvm_object_new

  task body();
    `uvm_info(`gfn, $sformatf("num_trans = %0d", num_trans), UVM_HIGH)
    for (uint tr_num = 0; tr_num < num_trans; tr_num++) begin
      string msg_id = {`gfn, $sformatf(" Transaction-%0d", tr_num)};

      `DV_CHECK_MEMBER_RANDOMIZE_FATAL(delay)
      cfg.clk_rst_vif.wait_clks(delay);

      randcase
        // drive new gpio data in
        1: begin
          // gpio input to drive
          bit [NUM_GPIOS-1:0] gpio_i;
          bit [NUM_GPIOS-1:0] data_in;
          `DV_CHECK_STD_RANDOMIZE_FATAL(gpio_i)
          `uvm_info(msg_id, "drive random value on gpio_i", UVM_HIGH)
          // drive gpio_vif after setting all output enables to 0's
          drive_gpio_in(gpio_i);
          cfg.clk_rst_vif.wait_clks(1);
          // read data_in register
          csr_rd(.ptr(ral.data_in), .value(data_in));
        end
        // write random value(s) to gpio interrupt register(s)
        1: begin
          `uvm_info(msg_id, "program interrupt register(s) to random value(s)", UVM_HIGH)

          if ($urandom_range(0, 1)) begin
            `DV_CHECK_RANDOMIZE_FATAL(ral.intr_enable)
            csr_update(ral.intr_enable);
          end

          if ($urandom_range(0, 1)) begin
            `DV_CHECK_RANDOMIZE_FATAL(ral.intr_ctrl_en_falling)
            csr_update(ral.intr_ctrl_en_falling);
          end

          if ($urandom_range(0, 1)) begin
            `DV_CHECK_RANDOMIZE_FATAL(ral.intr_ctrl_en_rising)
            csr_update(ral.intr_ctrl_en_rising);
          end

          if ($urandom_range(0, 1)) begin
            `DV_CHECK_RANDOMIZE_FATAL(ral.intr_ctrl_en_lvllow)
            csr_update(ral.intr_ctrl_en_lvllow);
          end

          if ($urandom_range(0, 1)) begin
            `DV_CHECK_RANDOMIZE_FATAL(ral.intr_ctrl_en_lvlhigh)
            csr_update(ral.intr_ctrl_en_lvlhigh);
          end

          if ($urandom_range(0, 1)) begin
            `DV_CHECK_RANDOMIZE_FATAL(ral.intr_state)
            csr_update(ral.intr_state);
          end
        end
      endcase
      // Read interrupt state register value
      begin
        bit [TL_DW-1:0] reg_rd_data;
        `DV_CHECK_MEMBER_RANDOMIZE_FATAL(delay)
        cfg.clk_rst_vif.wait_clks(delay);
        // read intr_state register
        csr_rd(.ptr(ral.intr_state), .value(reg_rd_data));
      end
      `uvm_info(msg_id, "End of Transaction", UVM_HIGH)

    end // end for

  endtask : body

endclass : gpio_intr_rand_pgm_vseq
