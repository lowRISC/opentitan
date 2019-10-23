// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// class : gpio_random_dout_din_vseq
// This gpio random test sequence does any of the following:
// (i) drives random gpio input data values while gpio outputs are disabled
// (ii) programs random values of one or more registers out of following:
//      gpio direct output data
//      gpio direct output enable
//      gpio masked output data lower
//      gpio masked output data upper
//      gpio masked output enable lower
//      gpio masked output enable upper
class gpio_random_dout_din_vseq extends gpio_base_vseq;

  `uvm_object_utils(gpio_random_dout_din_vseq)
  `uvm_object_new

  virtual task dut_init(string reset_kind = "HARD");
    // Continue using randomized value by default, unless plusarg
    // no_pullup_pulldown is passed to have no pullup/pulldown
    set_gpio_pulls(.pu(cfg.pullup_en), .pd(cfg.pulldown_en));
    super.dut_init(reset_kind);
  endtask: dut_init

  task body();
    `uvm_info(`gfn, $sformatf("num_trans = %0d", num_trans), UVM_HIGH)
    for (uint tr_num = 0; tr_num < num_trans; tr_num++) begin

      `DV_CHECK_RANDOMIZE_FATAL(this)
      cfg.clk_rst_vif.wait_clks(delay);

      randcase
        // drive new gpio data in
        1: begin
          // gpio input to drive
          bit [NUM_GPIOS-1:0] gpio_i;
          bit [NUM_GPIOS-1:0] data_in;
          `uvm_info(`gfn, $sformatf("Transaction-%0d: drive random value to gpio_i", tr_num),
                    UVM_HIGH)
          `DV_CHECK_STD_RANDOMIZE_FATAL(gpio_i)
          // drive gpio_vif after setting all output enables to 0's
          drive_gpio_in(gpio_i);
          cfg.clk_rst_vif.wait_clks(1);
          // read data_in register
          csr_rd(.ptr(ral.data_in), .value(data_in));
        end
        // write new value(s) to gpio out related register(s)
        1: begin
          `uvm_info(`gfn, $sformatf("Transaction-%0d: program register(s) to random value(s)",
                                    tr_num), UVM_HIGH)
          // First, stop driving gpio_i
          undrive_gpio_in();

          if ($urandom_range(0, 1)) begin
            `DV_CHECK_RANDOMIZE_FATAL(ral.direct_out)
            csr_update(ral.direct_out);
          end

          if ($urandom_range(0, 1)) begin
            `DV_CHECK_RANDOMIZE_FATAL(ral.direct_oe)
            csr_update(ral.direct_oe);
          end

          if ($urandom_range(0, 1)) begin
            `DV_CHECK_RANDOMIZE_FATAL(ral.masked_out_lower)
            csr_update(ral.masked_out_lower);
          end

          if ($urandom_range(0, 1)) begin
            `DV_CHECK_RANDOMIZE_FATAL(ral.masked_oe_lower)
            csr_update(ral.masked_oe_lower);
          end

          if ($urandom_range(0, 1)) begin
            `DV_CHECK_RANDOMIZE_FATAL(ral.masked_out_upper)
            csr_update(ral.masked_out_upper);
          end

          if ($urandom_range(0, 1)) begin
            `DV_CHECK_RANDOMIZE_FATAL(ral.masked_oe_upper)
            csr_update(ral.masked_oe_upper);
          end
        end
      endcase
      `uvm_info(`gfn, $sformatf("End of Transaction-%0d", tr_num), UVM_HIGH)

    end // end for

  endtask : body

endclass : gpio_random_dout_din_vseq
