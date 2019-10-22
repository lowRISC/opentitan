// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// class : gpio_random_long_reg_writes_reg_reads_vseq
// This gpio random test sequence performs random no. of iteration such that
// each iteration will do either of the following operations:
//   (i) drives random gpio input data values
//  (ii) writes any of gpio registers except for CTRL_EN_INPUT_FILTER register
// (iii) reads any of gpio registers
class gpio_random_long_reg_writes_reg_reads_vseq extends gpio_base_vseq;

  `uvm_object_utils(gpio_random_long_reg_writes_reg_reads_vseq)
  `uvm_object_new

  task body();
    // gpio pins_if pins_o value to drive
    bit [NUM_GPIOS-1:0] gpio_i;
    // gpio pins_if pins_oe value to drive
    bit [NUM_GPIOS-1:0] gpio_i_oen;
    `uvm_info(`gfn, $sformatf("num_trans = %0d", num_trans), UVM_HIGH)

    // Wait for minimum 1 clock cycle initially to avoid reading of data_in
    // immediately as the first iteration after reset, while data_in prediction
    // is still being processed
    cfg.clk_rst_vif.wait_clks(1);

    for (uint tr_num = 0; tr_num < num_trans; tr_num++) begin
      string msg_id = {`gfn, $sformatf(" Transaction-%0d", tr_num)};
      uint num_reg_op;
      `DV_CHECK_MEMBER_RANDOMIZE_FATAL(delay)
      `DV_CHECK_STD_RANDOMIZE_WITH_FATAL(num_reg_op, num_reg_op inside {[25:50]};)

      cfg.clk_rst_vif.wait_clks(delay);
      randcase
        // drive new gpio data in
        1: begin
          `DV_CHECK_STD_RANDOMIZE_FATAL(gpio_i)
          `uvm_info(msg_id, $sformatf("drive random value 0x%0h on gpio_i", gpio_i), UVM_HIGH)

          // drive gpio_vif after setting all output enables to 0's
          drive_gpio_in(gpio_i);
          // Wait for one clock cycle for us to read data_in reg reliably
          cfg.clk_rst_vif.wait_clks(1);
        end
        // long reg write
        1: begin
          undrive_gpio_in();
          repeat (num_reg_op) gpio_reg_wr();
        end
        // long reg read
        1: begin
          repeat (num_reg_op) gpio_reg_rd();
        end
      endcase

    end // end for

  endtask : body

  // Task: gpio_reg_wr
  task gpio_reg_wr();
    bit [NUM_GPIOS-1:0] csr_wr_value;
    `DV_CHECK_STD_RANDOMIZE_FATAL(csr_wr_value)

    randcase
      1: begin
        // Writing to DATA_IN reg
        csr_wr(.csr(ral.data_in), .value(csr_wr_value));
      end
      1: begin
        csr_wr(.csr(ral.direct_out), .value(csr_wr_value));
      end
      1: begin
        csr_wr(.csr(ral.masked_out_lower), .value(csr_wr_value));
      end
      1: begin
        csr_wr(.csr(ral.masked_out_upper), .value(csr_wr_value));
      end
      1: begin
        undrive_gpio_in();
        csr_wr(.csr(ral.direct_oe), .value(csr_wr_value));
      end
      1: begin
        csr_wr(.csr(ral.masked_oe_lower), .value(csr_wr_value));
      end
      1: begin
        csr_wr(.csr(ral.masked_oe_upper), .value(csr_wr_value));
      end
      1: begin
        csr_wr(.csr(ral.intr_enable), .value(csr_wr_value));
      end
      1: begin
        csr_wr(.csr(ral.intr_test), .value(csr_wr_value));
        `uvm_info(`gfn, "Writing to intr_test", UVM_NONE)
      end
      1: begin
        csr_wr(.csr(ral.intr_state), .value(csr_wr_value));
      end
      1: begin
        csr_wr(.csr(ral.intr_ctrl_en_falling), .value(csr_wr_value));
      end
      1: begin
        csr_wr(.csr(ral.intr_ctrl_en_rising), .value(csr_wr_value));
      end
      1: begin
        csr_wr(.csr(ral.intr_ctrl_en_lvllow), .value(csr_wr_value));
      end
      1: begin
        csr_wr(.csr(ral.intr_ctrl_en_lvlhigh), .value(csr_wr_value));
      end
    endcase
  endtask : gpio_reg_wr

  // Task: gpio_reg_rd
  task gpio_reg_rd();
    bit [TL_DW-1:0] csr_rd_value;
    randcase
      5: begin
        csr_rd(.ptr(ral.data_in), .value(csr_rd_value));
        `uvm_info(`gfn, "Reading data_in", UVM_HIGH)
      end
      1: begin
        csr_rd(.ptr(ral.direct_out), .value(csr_rd_value));
        `uvm_info(`gfn, "Reading direct_out", UVM_HIGH)
      end
      1: begin
        csr_rd(.ptr(ral.masked_out_lower), .value(csr_rd_value));
        `uvm_info(`gfn, "Reading masked_out_lower", UVM_HIGH)
      end
      1: begin
        csr_rd(.ptr(ral.masked_out_upper), .value(csr_rd_value));
        `uvm_info(`gfn, "Reading masked_out_upper", UVM_HIGH)
      end
      1: begin
        csr_rd(.ptr(ral.direct_oe), .value(csr_rd_value));
        `uvm_info(`gfn, "Reading direct_oe", UVM_HIGH)
      end
      1: begin
        csr_rd(.ptr(ral.masked_oe_lower), .value(csr_rd_value));
        `uvm_info(`gfn, "Reading masked_oe_lower", UVM_HIGH)
      end
      1: begin
        csr_rd(.ptr(ral.masked_oe_upper), .value(csr_rd_value));
        `uvm_info(`gfn, "Reading masked_oe_upper", UVM_HIGH)
      end
      1: begin
        csr_rd(.ptr(ral.intr_enable), .value(csr_rd_value));
        `uvm_info(`gfn, "Reading intr_enable", UVM_HIGH)
      end
      1: begin
        csr_rd(.ptr(ral.intr_test), .value(csr_rd_value));
        `uvm_info(`gfn, "Reading intr_test", UVM_NONE)
      end
      5: begin
        csr_rd(.ptr(ral.intr_state), .value(csr_rd_value));
        `uvm_info(`gfn, "Reading intr_state", UVM_HIGH)
      end
      1: begin
        csr_rd(.ptr(ral.intr_ctrl_en_falling), .value(csr_rd_value));
        `uvm_info(`gfn, "Reading intr_ctrl_en_falling", UVM_HIGH)
      end
      1: begin
        csr_rd(.ptr(ral.intr_ctrl_en_rising), .value(csr_rd_value));
        `uvm_info(`gfn, "Reading intr_ctrl_en_rising", UVM_HIGH)
      end
      1: begin
        csr_rd(.ptr(ral.intr_ctrl_en_lvllow), .value(csr_rd_value));
        `uvm_info(`gfn, "Reading intr_ctrl_en_lvllow", UVM_HIGH)
      end
      1: begin
        csr_rd(.ptr(ral.intr_ctrl_en_lvlhigh), .value(csr_rd_value));
        `uvm_info(`gfn, "Reading intr_ctrl_en_lvlhigh", UVM_HIGH)
      end
      1: begin
        csr_rd(.ptr(ral.ctrl_en_input_filter), .value(csr_rd_value));
        `uvm_info(`gfn, "Reading ctrl_en_input_filter", UVM_HIGH)
      end
    endcase
  endtask : gpio_reg_rd

endclass : gpio_random_long_reg_writes_reg_reads_vseq
