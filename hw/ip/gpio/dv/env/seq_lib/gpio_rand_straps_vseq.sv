// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// class : gpio_rand_straps_vseq
// This gpio random test sequence performs following in each of multiple iterations:
// - Drives gpio_i input with random values
// - Set the expected strap_data_in based on the condition if is the first triggered strap_en or not
// - Updates the RAL model with the expected strap_data_in and strap_data_in_valid
// - Trigger the strap_en with one clock cycles
// - Read the registers hw_straps_data_in and hw_straps_data_in_valid
// - Check the expected behavior in the scoreboard and also on csr checks
class gpio_rand_straps_vseq extends gpio_base_vseq;

  `uvm_object_utils(gpio_rand_straps_vseq)

  // gpio input to drive
  rand bit [NUM_GPIOS-1:0] gpio_i;
  // gpio output to program in register
  rand bit [NUM_GPIOS-1:0] gpio_o;
  // gpio output enable to program in register
  rand bit [NUM_GPIOS-1:0] gpio_oe;
  // Flag to indicate that the first trigger straps happened
  bit straps_triggered;
  // Read straps_data_in
  bit [NUM_GPIOS-1:0] rd_hw_straps_data_in;
  // Read straps_data_in valid
  bit                 rd_hw_straps_data_in_valid;
  // Expected strap data_in
  bit [NUM_GPIOS-1:0] exp_strap_data_in;

  constraint num_trans_c {
    num_trans inside {[20:200]};
  }

  function new(string name = "gpio_rand_straps_vseq");
    super.new(name);
  endfunction

  task body();
    `uvm_info(`gfn, $sformatf("num_trans = %0d", num_trans), UVM_HIGH)

    for (uint tr_num = 0; tr_num < num_trans; tr_num++) begin
      string msg_id = {`gfn, $sformatf(" Transaction-%0d", tr_num)};
      `DV_CHECK_MEMBER_RANDOMIZE_FATAL(delay)
      `DV_CHECK_MEMBER_RANDOMIZE_FATAL(gpio_i)
      `DV_CHECK_MEMBER_RANDOMIZE_FATAL(gpio_o)
      `DV_CHECK_MEMBER_RANDOMIZE_FATAL(gpio_oe)

      cfg.clk_rst_vif.wait_clks(delay);
      `uvm_info(msg_id, $sformatf("delay = %0d", delay), UVM_HIGH)
      // Step-1 Drive the gpio_i
      drive_gpio_in(gpio_i);

      // If is not the first strap triggered, it should be the gpio_i input (that is the first one after reset),
      // for the following interations keep the same value as the first strap already happened.
      // No more updates in gpio_i should be taken
      // into consideration for the strap_data_in register.
      if(straps_triggered) begin
        exp_strap_data_in = rd_hw_straps_data_in;
      end else begin
        exp_strap_data_in = gpio_i;
      end

      // Wait at least one clock cycle
      `DV_CHECK_MEMBER_RANDOMIZE_WITH_FATAL(delay, delay >= 1;)

      // Step-2 Trigger the snapshot of gpio_i to be stored in the straps registers
      cfg.straps_vif_inst.strap_en = 1;
      cfg.clk_rst_vif.wait_clks(1);
      cfg.straps_vif_inst.strap_en = 0;
      straps_triggered = 'b1;

      // Step-3 Read the HW_STRAPS_DATA_IN register
      // Reading straps data_in will trigger a check inside scoreboard

      // Wait at least one clock cycle
      `DV_CHECK_MEMBER_RANDOMIZE_WITH_FATAL(delay, delay >= 1;)

      // Step-4 Read the hw_straps_data_in and check the expected value in the scoreboard
      csr_rd(.ptr(ral.hw_straps_data_in), .value(rd_hw_straps_data_in));
      // Read the hw_straps_data_in_valid and check the expected value in the scoreboard
      csr_rd(.ptr(ral.hw_straps_data_in_valid), .value(rd_hw_straps_data_in_valid));

      // Stop driving gpio_i
      undrive_gpio_in();

      // Step-5 Read to make sure that if does not affect the straps registers after undrive the gpio_in
      csr_rd(.ptr(ral.hw_straps_data_in), .value(rd_hw_straps_data_in));
      csr_rd(.ptr(ral.hw_straps_data_in_valid), .value(rd_hw_straps_data_in_valid));

      // Additional verification
      // Drive the gpio_o to make sure that has no impact on straps registers.
      // test gpio outputs
      cfg.gpio_vif.drive_en('0);

      ral.direct_out.set(gpio_o);
      ral.direct_oe.set(gpio_oe);
      csr_update(.csr(ral.direct_out));
      csr_update(.csr(ral.direct_oe));

      `DV_CHECK_MEMBER_RANDOMIZE_WITH_FATAL(delay, delay >= 1;)

      // Step-6 Drive again the strap_en
      cfg.straps_vif_inst.strap_en = 1;
      cfg.clk_rst_vif.wait_clks(1);
      cfg.straps_vif_inst.strap_en = 0;

      `DV_CHECK_MEMBER_RANDOMIZE_WITH_FATAL(delay, delay >= 1;)

      // Step-7 Read to make sure that if does not affect the straps registers after drive the gpio_o
      csr_rd(.ptr(ral.hw_straps_data_in), .value(rd_hw_straps_data_in));
      csr_rd(.ptr(ral.hw_straps_data_in_valid), .value(rd_hw_straps_data_in_valid));

      `uvm_info(msg_id, "End of Transaction", UVM_HIGH)

    end // end for

  endtask : body

endclass : gpio_rand_straps_vseq
