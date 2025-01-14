// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Verify the straps data/valid ouput expected values based on the strap_en and gpio_in inputs:
//    - Drive gpio_in input with random values.
//    - Set the strap_en high for at least one clock cycle.
//    - Read the registers hw_straps_data_in and hw_straps_data_in_valid.
//    - The data read and sampled_straps_o will be checked in the scoreboard.
//    - Drive the gpio_out to make sure that has no impact on straps registers.
//    - Read to make sure that if does not affect the straps registers after drive the gpio_out.
//    - Apply reset and make sure the strap registers are clean.
//    - Read straps registers after reset.
//    - Iterate again the same flow, with new random values.
class gpio_rand_straps_vseq extends gpio_base_vseq;

  `uvm_object_utils(gpio_rand_straps_vseq)

  // gpio input to drive
  rand bit [NUM_GPIOS-1:0] gpio_in;
  // gpio output to program in register
  rand bit [NUM_GPIOS-1:0] gpio_out;
  // gpio output enable to program in register
  rand bit [NUM_GPIOS-1:0] gpio_oe;

  // Read straps_data_in
  bit [NUM_GPIOS-1:0] rd_hw_straps_data_in;
  // Read straps_data_in valid
  bit                 rd_hw_straps_data_in_valid;

  constraint num_trans_c {
    num_trans inside {[20:200]};
  }

  function new(string name = "gpio_rand_straps_vseq");
    super.new(name);
  endfunction

  task test_straps_gpio_in();

    // Drive the gpio_in
    drive_gpio_in(gpio_in);

    // Wait at least one clock cycle to drive the strap_en
    // Required because is required one clock cycle to update the gpio_in regsisters.
    `DV_CHECK_MEMBER_RANDOMIZE_WITH_FATAL(delay, delay >= 1;)
    cfg.clk_rst_vif.wait_clks(delay);

    // Trigger the snapshot of gpio_in to be stored in the straps registers
    cfg.straps_vif_inst.port_out.strap_en = 1;
    cfg.clk_rst_vif.wait_clks(1);

    // Wait at least two clock cycles to avoid race condition with the predict value updated
    // in the scoreboard
    `DV_CHECK_MEMBER_RANDOMIZE_WITH_FATAL(delay, delay >= 1;)
    cfg.clk_rst_vif.wait_clks(delay);

    // Read the hw_straps_data_in and check the expected value in the scoreboard
    csr_rd(.ptr(ral.hw_straps_data_in), .value(rd_hw_straps_data_in));
    // Read the hw_straps_data_in_valid and check the expected value in the scoreboard
    csr_rd(.ptr(ral.hw_straps_data_in_valid), .value(rd_hw_straps_data_in_valid));

    // Random wait
    `DV_CHECK_MEMBER_RANDOMIZE_WITH_FATAL(delay, delay >= 0;)
    cfg.clk_rst_vif.wait_clks(delay);

    // Stop driving gpio_in
    undrive_gpio_in();

    // Random wait
    `DV_CHECK_MEMBER_RANDOMIZE_WITH_FATAL(delay, delay >= 0;)
    cfg.clk_rst_vif.wait_clks(delay);

    // Read to make sure that if does not affect the straps registers after undrive the gpio_in
    csr_rd(.ptr(ral.hw_straps_data_in), .value(rd_hw_straps_data_in));
    csr_rd(.ptr(ral.hw_straps_data_in_valid), .value(rd_hw_straps_data_in_valid));

  endtask : test_straps_gpio_in

  task test_straps_gpio_out();

    // Additional verification
    // Drive the gpio_out to make sure that has no impact on straps registers.
    // then read the gpio strap registers again
    cfg.gpio_vif.drive_en('0);

    ral.direct_out.set(gpio_out);
    ral.direct_oe.set(gpio_oe);
    csr_update(.csr(ral.direct_out));
    csr_update(.csr(ral.direct_oe));

    // Random wait
    `DV_CHECK_MEMBER_RANDOMIZE_WITH_FATAL(delay, delay >= 0;)
    cfg.clk_rst_vif.wait_clks(delay);

    // Read to make sure that if does not affect the straps registers after drive the gpio_out
    csr_rd(.ptr(ral.hw_straps_data_in), .value(rd_hw_straps_data_in));
    csr_rd(.ptr(ral.hw_straps_data_in_valid), .value(rd_hw_straps_data_in_valid));

  endtask : test_straps_gpio_out

  task check_transaction(string txn_desc, bit is_first);
    string msg_id = {`gfn, txn_desc};

    `DV_CHECK_MEMBER_RANDOMIZE_FATAL(gpio_in)
    `DV_CHECK_MEMBER_RANDOMIZE_FATAL(gpio_out)
    `DV_CHECK_MEMBER_RANDOMIZE_FATAL(gpio_oe)

    // User case to test the straps output, with gpio_in data randomised
    test_straps_gpio_in();

    // User case to test the straps output/registers, with gpio_out data randomised
    // The gpio_out should not affect the straps output/registers.
    //test_straps_gpio_out();

    // Random wait
    `DV_CHECK_MEMBER_RANDOMIZE_WITH_FATAL(delay, delay >= 1;)
    cfg.clk_rst_vif.wait_clks(delay);

    // Disable the straps.
    cfg.straps_vif_inst.port_out.strap_en = 0;
    // Apply reset and make sure the strap registers are clean
    apply_reset();

    // Random wait
    `DV_CHECK_MEMBER_RANDOMIZE_WITH_FATAL(delay, delay >= 2;)
    cfg.clk_rst_vif.wait_clks(delay);

    // Read the straps registers after reset
    csr_rd(.ptr(ral.hw_straps_data_in), .value(rd_hw_straps_data_in));
    csr_rd(.ptr(ral.hw_straps_data_in_valid), .value(rd_hw_straps_data_in_valid));

  endtask : check_transaction

  task body();
    `uvm_info(`gfn, $sformatf("num_trans = %0d", num_trans), UVM_HIGH)

    for (uint tr_num = 0; tr_num < num_trans; tr_num++) begin
      string msg_id = {`gfn, $sformatf(" Transaction-%0d", tr_num)};
      `DV_CHECK_MEMBER_RANDOMIZE_FATAL(delay)

      cfg.clk_rst_vif.wait_clks(delay);
      `uvm_info(msg_id, $sformatf("delay = %0d", delay), UVM_HIGH)

      check_transaction(msg_id, tr_num == 0);

      `uvm_info(msg_id, "End of Transaction", UVM_HIGH)

    end // end for

  endtask : body

endclass : gpio_rand_straps_vseq
