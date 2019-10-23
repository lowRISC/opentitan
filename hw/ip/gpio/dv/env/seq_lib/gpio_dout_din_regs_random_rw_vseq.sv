// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// class : gpio_dout_din_regs_random_rw_vseq
// This gpio random test sequence does any of the following:
// (i) drives random gpio input data values while gpio outputs are disabled
// (ii) programs random values of gpio direct output data, gpio direct output enable
//      gpio masked outputs and gpio masked output enables.
class gpio_dout_din_regs_random_rw_vseq extends gpio_base_vseq;

  `uvm_object_utils(gpio_dout_din_regs_random_rw_vseq)
  `uvm_object_new

  task body();
    `uvm_info(`gfn, $sformatf("num_trans = %0d", num_trans), UVM_HIGH)
    for (uint tr_num = 0; tr_num < num_trans; tr_num++) begin
      // Stores either of following:
      // 1. Write Data to be written to register
      // 2. Register Read Data
      logic [TL_DW-1:0] csr_val;

      `DV_CHECK_RANDOMIZE_FATAL(this)
      // Insert some random delay
      cfg.clk_rst_vif.wait_clks(delay);

      randcase
        // drive new gpio data in
        1: begin
          // gpio input to drive
          bit [NUM_GPIOS-1:0] gpio_i;
          bit [TL_DW-1:0] data_in;
          `uvm_info(`gfn, $sformatf("Transaction-%0d: drive random value to gpio_i", tr_num),
                    UVM_HIGH)
          `DV_CHECK_STD_RANDOMIZE_FATAL(gpio_i)
          // drive gpio_vif after setting all output enables to 0's
          drive_gpio_in(gpio_i);
          cfg.clk_rst_vif.wait_clks(1);
          // read data_in register
          csr_rd(.ptr(ral.data_in), .value(data_in));
        end
        // write new value to any one of gpio data registers
        1: begin
          `uvm_info(`gfn, $sformatf("Transaction-%0d: program a random gpio register", tr_num),
                    UVM_HIGH)
          // First, stop driving gpio_i
          undrive_gpio_in();
          // Randomize csr value
          `DV_CHECK_STD_RANDOMIZE_FATAL(csr_val)

          randcase
            1: begin
              // Add single clock cycle delay to avoid update and predict at
              // the same time due to weak pull-up after undrive_gpio_in()
              cfg.clk_rst_vif.wait_clks(1);
              // DATA_IN register is RO, but writing random value to it
              // should have no impact on gpio functionality
              csr_wr(.csr(ral.data_in), .value(csr_val));
            end
            1: csr_wr(.csr(ral.direct_out      ), .value(csr_val));
            1: csr_wr(.csr(ral.direct_oe       ), .value(csr_val));
            1: csr_wr(.csr(ral.masked_out_lower), .value(csr_val));
            1: csr_wr(.csr(ral.masked_oe_lower ), .value(csr_val));
            1: csr_wr(.csr(ral.masked_out_upper), .value(csr_val));
            1: csr_wr(.csr(ral.masked_oe_upper ), .value(csr_val));
          endcase
        end
        // read any one of the gpio data registers
        1: begin
          `uvm_info(`gfn, $sformatf("Transaction-%0d: read random register)", tr_num), UVM_HIGH)
          randcase
            1: csr_rd(.ptr(ral.data_in         ), .value(csr_val));
            1: csr_rd(.ptr(ral.direct_out      ), .value(csr_val));
            1: csr_rd(.ptr(ral.direct_oe       ), .value(csr_val));
            1: csr_rd(.ptr(ral.masked_out_lower), .value(csr_val));
            1: csr_rd(.ptr(ral.masked_oe_lower ), .value(csr_val));
            1: csr_rd(.ptr(ral.masked_out_upper), .value(csr_val));
            1: csr_rd(.ptr(ral.masked_oe_upper ), .value(csr_val));
          endcase
          `uvm_info(`gfn, $sformatf("reg read data = 0x%0h [%0b]", csr_val, csr_val), UVM_HIGH)
        end
      endcase
      `uvm_info(`gfn, $sformatf("End of Transaction-%0d", tr_num), UVM_HIGH)

    end // end for

  endtask : body

endclass : gpio_dout_din_regs_random_rw_vseq
