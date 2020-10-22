// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// class : gpio_full_random_vseq
// This gpio random test sequence performs random no. of iteration such that
// each iteration will do either of the following operations:
//   (i) drives random gpio input data values such that none of the gpios become
//       unknown value
//  (ii) writes any of gpio registers
// (iii) reads any of gpio registers
class gpio_full_random_vseq extends gpio_random_long_reg_writes_reg_reads_vseq;

  // predicted value of DATA_OUT rtl implementation register
  bit [NUM_GPIOS-1:0] data_out;
  // predicted updated value of DATA_OE rtl implementation register
  bit [NUM_GPIOS-1:0] data_oe;
  // Previous value of gpio pins
  bit [NUM_GPIOS-1:0] prev_gpio_val;

  `uvm_object_utils(gpio_full_random_vseq)
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
    // Initialize prev_gpio_val
    prev_gpio_val = (cfg.pullup_en) ? '1 : '0;

    for (uint tr_num = 0; tr_num < num_trans; tr_num++) begin
      string msg_id = {`gfn, $sformatf(" Transaction-%0d", tr_num)};

      `uvm_info(msg_id, "Start of Transaction", UVM_HIGH)
      `DV_CHECK_MEMBER_RANDOMIZE_FATAL(delay)
      cfg.clk_rst_vif.wait_clks(delay);

      randcase
        // drive new gpio data in
        1: begin
          `uvm_info(msg_id, $sformatf("Latest data_out = 0x%0h [%0b]", data_out, data_out),
                    UVM_HIGH)
          `uvm_info(msg_id, $sformatf("Latest data_oe = 0x%0h [%0b]", data_oe, data_oe),
                    UVM_HIGH)
          // Set all 1's in gpio_i_oen first up
          gpio_i_oen = '1;
          `DV_CHECK_STD_RANDOMIZE_FATAL(gpio_i)
          `uvm_info(msg_id, $sformatf("drive random value 0x%0h on gpio_i", gpio_i), UVM_HIGH)

          foreach(gpio_i[pin]) begin
            if (data_oe[pin]) begin
              if (gpio_i[pin] != data_out[pin]) begin
                data_oe[pin] = 1'b0;
              end
              else begin
                bit gpio_i_oe_pin;
                `DV_CHECK_STD_RANDOMIZE_FATAL(gpio_i_oe_pin)
                gpio_i_oen[pin] = gpio_i_oe_pin;
              end
            end
          end
          // Update data_oe reg value
          ral.direct_oe.set(data_oe);
          csr_update(ral.direct_oe);
          // drive gpio_vif after setting all output enables to 0's
          cfg.gpio_vif.pins_oe = gpio_i_oen;
          cfg.gpio_vif.pins_o = gpio_i;
          wait_for_filter_cyles();
          prev_gpio_val = cfg.gpio_vif.sample();
          `uvm_info(`gfn, $sformatf("prev_gpio_val updated to %0h", prev_gpio_val), UVM_HIGH)
        end
        1: begin
          pgm_out_oe_regs(.gpio_if_pins_o_val(gpio_i), .gpio_if_pins_oe_val(gpio_i_oen));
        end
        1: pgm_intr_regs();
        1: pgm_misc_reg();
        1: gpio_reg_rd();
        1: begin
          `DV_CHECK_MEMBER_RANDOMIZE_FATAL(delay)
          cfg.clk_rst_vif.wait_clks(delay);
          csr_utils_pkg::wait_no_outstanding_access();
          dut_init("HARD");
          data_out = '0;
          data_oe  = '0;
        end
      endcase

      `uvm_info(msg_id, "End of Transaction", UVM_HIGH)

    end // end for

  endtask : body

  // Task: pgm_out_oe_regs
  // This task is for programming one or more of *out* and *oe* GPIO registers
  // As some of the GPIO pins are already configured and driven as inputs, we need
  // to make sure that DATA_OUT and DATA_OE combination is programmed such that:
  // - Output driven on pin is same as as GPIO input value, or
  // - Outpurt enable on pin is 0
  // By doing either of above two options, we make sure that none of the GPIO pins
  // become unknowns due to multiple drivers with conflicting values.
  task pgm_out_oe_regs(bit [NUM_GPIOS-1:0] gpio_if_pins_o_val,
                       bit [NUM_GPIOS-1:0] gpio_if_pins_oe_val);
    bit [TL_DW-1:0] csr_wr_value;
    `DV_CHECK_STD_RANDOMIZE_FATAL(csr_wr_value)

    // write to direct_out reg
    if ($urandom_range(0, 1)) begin
      // Avoid 'x' due to different values driven from data_out
      // and gpio_if_pins_o_val sides
      for (uint pin = 0; pin < NUM_GPIOS; pin++) begin
        if (data_oe[pin] == 1'b1 && gpio_if_pins_oe_val[pin] == 1'b1) begin
          csr_wr_value[pin] = gpio_if_pins_o_val[pin];
        end
      end
      csr_wr(.csr(ral.direct_out), .value(csr_wr_value));
      // Update value of data_out
      data_out = csr_wr_value;
      `uvm_info(`gfn, $sformatf("data_out updated to value %0h", data_out), UVM_HIGH)
      // Check if there is update on gpio pins due to register update
      gpio_pins_update_check();
    end

    // write to masked_out_lower reg
    if ($urandom_range(0, 1)) begin
      bit [(NUM_GPIOS/2)-1:0] mask, data;
      {mask, data} = csr_wr_value;
      for (uint pin = 0; pin < ral.masked_out_lower.mask.get_n_bits(); pin++) begin
        if ((data_oe[pin] == 1'b1) && (gpio_if_pins_oe_val[pin] == 1'b1) &&
            (mask[pin] == 1'b1 && (data[pin] != gpio_if_pins_o_val[pin]))) begin
          randcase
            1: data[pin] = gpio_if_pins_o_val[pin];
            1: mask[pin] = 1'b0;
          endcase
        end
      end
      // updated csr_wr_value
      csr_wr_value = {mask, data};
      csr_wr(.csr(ral.masked_out_lower), .value(csr_wr_value));
      // Update data_out value
      for (uint pin = 0; pin < ral.masked_out_lower.mask.get_n_bits(); pin++) begin
        if (mask[pin] == 1'b1) begin
          data_out[pin] = data[pin];
        end
      end
      `uvm_info(`gfn, $sformatf("data_out updated to value %0h", data_out), UVM_HIGH)
      // Check if there is update on gpio pins due to register update
      gpio_pins_update_check();
    end

    // write to masked_out_upper reg
    if ($urandom_range(0, 1)) begin
      bit [(NUM_GPIOS/2)-1:0] mask, data;
      {mask, data} = csr_wr_value;
      for (uint pin = 0; pin < ral.masked_out_upper.mask.get_n_bits(); pin++) begin
        if ((data_oe[(NUM_GPIOS/2) + pin] == 1'b1) &&
            (gpio_if_pins_oe_val[(NUM_GPIOS/2) + pin] == 1'b1) &&
            (mask[pin] == 1'b1 &&
             (data[pin] != gpio_if_pins_o_val[(NUM_GPIOS/2) + pin]))) begin
          randcase
            1: data[pin] = gpio_if_pins_o_val[(NUM_GPIOS/2) + pin];
            1: mask[pin] = 1'b0;
          endcase
        end
      end
      // updated csr_wr_value
      csr_wr_value = {mask, data};
      csr_wr(.csr(ral.masked_out_upper), .value(csr_wr_value));
      // Update value of data_out
      for (uint pin = 0; pin < ral.masked_out_upper.mask.get_n_bits(); pin++) begin
        if (mask[pin] == 1'b1) begin
          data_out[(NUM_GPIOS / 2) + pin] = data[pin];
        end
      end
      `uvm_info(`gfn, $sformatf("data_out updated to value %0h", data_out), UVM_HIGH)
      // Check if there is update on gpio pins due to register update
      gpio_pins_update_check();
    end

    // write to direct_oe reg
    if ($urandom_range(0, 1)) begin
      for (uint pin = 0; pin < NUM_GPIOS; pin++) begin
        if ((csr_wr_value[pin] == 1'b1 && gpio_if_pins_oe_val[pin] == 1'b1) &&
            (data_out[pin] != gpio_if_pins_o_val[pin])) begin
          csr_wr_value[pin] = 1'b0;
        end
      end
      csr_wr(.csr(ral.direct_oe), .value(csr_wr_value));
      // Update data_oe value
      data_oe = csr_wr_value;
      `uvm_info(`gfn, $sformatf("data_oe updated to value %0h", data_oe), UVM_HIGH)
      // Check if there is update on gpio pins due to register update
      gpio_pins_update_check();
    end

    // write to masked_oe_lower reg
    if ($urandom_range(0, 1)) begin
      bit [(NUM_GPIOS/2)-1:0] mask, data;
      {mask, data} = csr_wr_value;
      for (uint pin = 0; pin < ral.masked_oe_lower.mask.get_n_bits(); pin++) begin
        if (mask[pin] == 1'b1 && data[pin] == 1'b1 && gpio_if_pins_oe_val[pin] == 1'b1 &&
            (data_out[pin] != gpio_if_pins_o_val[pin])) begin
          randcase
            1: mask[pin] = 1'b0;
            1: data[pin] = 1'b0;
          endcase
        end
      end
      // updated csr_wr_value
      csr_wr_value = {mask, data};
      csr_wr(.csr(ral.masked_oe_lower), .value(csr_wr_value));
      // Update data_oe value
      for (uint pin = 0; pin < ral.masked_oe_lower.mask.get_n_bits(); pin++) begin
        if (mask[pin] == 1'b1) begin
          data_oe[pin] = data[pin];
        end
      end
      `uvm_info(`gfn, $sformatf("data_oe updated to value %0h", data_oe), UVM_HIGH)
      // Check if there is update on gpio pins due to register update
      gpio_pins_update_check();
    end

    // write to masked_oe_upper
    if ($urandom_range(0, 1)) begin
      bit [(NUM_GPIOS/2)-1:0] mask, data;
      {mask, data} = csr_wr_value;
      for (uint pin = 0; pin < ral.masked_oe_upper.mask.get_n_bits(); pin++) begin
        if (mask[pin] == 1'b1 && data[pin] == 1'b1 &&
            gpio_if_pins_oe_val[(TL_DW/2) + pin] == 1'b1 &&
            (data_out[(TL_DW/2) + pin] != gpio_if_pins_o_val[(TL_DW/2) + pin])) begin
          randcase
            1: mask[pin] = 1'b0;
            1: data[pin] = 1'b0;
          endcase
        end
      end
      // updated csr_wr_value
      csr_wr_value = {mask, data};
      csr_wr(.csr(ral.masked_oe_upper), .value(csr_wr_value));
      // Update data_oe value
      for (uint pin = 0; pin < ral.masked_oe_upper.mask.get_n_bits(); pin++) begin
        if (mask[pin] == 1'b1) begin
          data_oe[(NUM_GPIOS / 2) + pin] = data[pin];
        end
      end
      `uvm_info(`gfn, $sformatf("data_oe updated to value %0h", data_oe), UVM_HIGH)
      // Check if there is update on gpio pins due to register update
      gpio_pins_update_check();
    end
  endtask : pgm_out_oe_regs

  task pgm_intr_regs();
    super.pgm_intr_regs();
    if ($urandom_range(0, 1)) begin
      `DV_CHECK_RANDOMIZE_FATAL(ral.intr_test)
      `uvm_info(`gfn, "Writing to intr_test", UVM_NONE)
      csr_update(.csr(ral.intr_test));
    end
    if ($urandom_range(0, 1)) begin
      `DV_CHECK_RANDOMIZE_FATAL(ral.intr_state)
      csr_update(.csr(ral.intr_state));
    end
  endtask : pgm_intr_regs

  task pgm_misc_reg();
    randcase
      1: begin
        `DV_CHECK_RANDOMIZE_FATAL(ral.data_in)
        csr_update(.csr(ral.data_in));
      end
      1 : begin
        `DV_CHECK_RANDOMIZE_FATAL(ral.ctrl_en_input_filter)
        wait_for_filter_cyles();
        csr_update(.csr(ral.ctrl_en_input_filter));
        wait_for_filter_cyles();
      end
    endcase
  endtask : pgm_misc_reg

  // Function: gpio_pins_update_check
  task gpio_pins_update_check();
    if (cfg.gpio_vif.sample() != prev_gpio_val) begin
      // Wait until GPIO pins are stable
      wait_for_filter_cyles();
      // Update prev_gpio_val
      prev_gpio_val = cfg.gpio_vif.sample();
    end
  endtask : gpio_pins_update_check

  // Task: wait_for_filter_cyles
  task wait_for_filter_cyles;
    // Wait for (FILTER_CYCLES + 1) clock cycles to make sure we can
    // reliably read updated value of data_in even with filter enabled
    cfg.clk_rst_vif.wait_clks(FILTER_CYCLES + 1);
  endtask : wait_for_filter_cyles

endclass : gpio_full_random_vseq
