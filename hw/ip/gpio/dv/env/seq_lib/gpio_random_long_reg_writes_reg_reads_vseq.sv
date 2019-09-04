// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// class : gpio_random_long_reg_writes_reg_reads_vseq
// This gpio random test sequence performs random no. of iteration such that
// each iteration will do either of the following operations:
//   (i) drives random gpio input data values such that none of the gpios become
//       unknown value
//  (ii) writes any of gpio registers except for CTRL_EN_INPUT_FILTER and
//       INTR_TEST registers
// (iii) reads any of gpio registers except for CTRL_EN_INPUT_FILTER and
//       INTR_TEST registers
class gpio_random_long_reg_writes_reg_reads_vseq extends gpio_base_vseq;

  // predicted value of DATA_OUT rtl implementation register
  bit [NUM_GPIOS-1:0] data_out;
  // predicted updated value of DATA_OE rtl implementation register
  bit [NUM_GPIOS-1:0] data_oe;

  constraint num_trans_c {
    num_trans inside {[20:200]};
  }

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

      `DV_CHECK_MEMBER_RANDOMIZE_FATAL(delay)
      cfg.clk_rst_vif.wait_clks(delay);

      randcase
        // drive new gpio data in
        1: begin
          `DV_CHECK_STD_RANDOMIZE_FATAL(gpio_i)
          `DV_CHECK_STD_RANDOMIZE_FATAL(gpio_i_oen)
          `uvm_info(msg_id, $sformatf("drive random value 0x%0h on gpio_i", gpio_i), UVM_HIGH)
          `uvm_info(msg_id, $sformatf("drive random value 0x%0h on gpio_i_oen", gpio_i_oen), UVM_HIGH)

          // drive gpio_vif after setting all output enables to 0's
          cfg.gpio_vif.pins_oe = gpio_i_oen;
          cfg.gpio_vif.pins_o = gpio_i;
          // Wait for one clock cycle for us to read data_in reg reliably
          cfg.clk_rst_vif.wait_clks(1);
        end
        // long reg write
        1: begin
          uint no_of_reg_wr;
          `DV_CHECK_STD_RANDOMIZE_WITH_FATAL(no_of_reg_wr, no_of_reg_wr inside {[10:50]};)
          `uvm_info(msg_id, $sformatf("performing long write with %0d transactions",
                                      no_of_reg_wr), UVM_HIGH)
          repeat (no_of_reg_wr) begin
            gpio_reg_wr(.gpio_if_pins_o_val(gpio_i), .gpio_if_pins_oe_val(gpio_i_oen));
          end
        end
        // long reg read
        1: begin
          uint no_of_reg_rd;
          `DV_CHECK_STD_RANDOMIZE_WITH_FATAL(no_of_reg_rd, no_of_reg_rd inside {[10:50]};)
          `uvm_info(msg_id, $sformatf("performing long read with %0d transactions",
                                      no_of_reg_rd), UVM_HIGH)
          repeat (no_of_reg_rd) gpio_reg_rd();
        end
      endcase

      `uvm_info(msg_id, "End of Transaction", UVM_HIGH)

    end // end for

  endtask : body

  // Task: gpio_reg_wr
  task gpio_reg_wr(bit [NUM_GPIOS-1:0] gpio_if_pins_o_val,
                   bit [NUM_GPIOS-1:0] gpio_if_pins_oe_val);
    bit [TL_DW-1:0] csr_wr_value;

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
      end
      1: begin
        csr_rd(.ptr(ral.direct_out), .value(csr_rd_value));
      end
      1: begin
        csr_rd(.ptr(ral.masked_out_lower), .value(csr_rd_value));
      end
      1: begin
        csr_rd(.ptr(ral.masked_out_upper), .value(csr_rd_value));
      end
      1: begin
        csr_rd(.ptr(ral.direct_oe), .value(csr_rd_value));
      end
      1: begin
        csr_rd(.ptr(ral.masked_oe_lower), .value(csr_rd_value));
      end
      1: begin
        csr_rd(.ptr(ral.masked_oe_upper), .value(csr_rd_value));
      end
      1: begin
        csr_rd(.ptr(ral.intr_enable), .value(csr_rd_value));
      end
      5: begin
        csr_rd(.ptr(ral.intr_state), .value(csr_rd_value));
      end
      1: begin
        csr_rd(.ptr(ral.intr_ctrl_en_falling), .value(csr_rd_value));
      end
      1: begin
        csr_rd(.ptr(ral.intr_ctrl_en_rising), .value(csr_rd_value));
      end
      1: begin
        csr_rd(.ptr(ral.intr_ctrl_en_lvllow), .value(csr_rd_value));
      end
      1: begin
        csr_rd(.ptr(ral.intr_ctrl_en_lvlhigh), .value(csr_rd_value));
      end
    endcase
  endtask : gpio_reg_rd

endclass : gpio_random_long_reg_writes_reg_reads_vseq
