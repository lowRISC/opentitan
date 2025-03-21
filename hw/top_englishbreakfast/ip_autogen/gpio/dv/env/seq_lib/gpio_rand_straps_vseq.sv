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
//    - Random apply reset and make sure the strap registers are clean,
//    using the stress_all wrap tests with random reset vseq.
class gpio_rand_straps_vseq extends gpio_base_vseq;

  `uvm_object_utils(gpio_rand_straps_vseq)

  // gpio input to drive
  rand bit [NUM_GPIOS-1:0] gpio_in;
  // gpio output to program in register
  rand bit [NUM_GPIOS-1:0] gpio_out;
  // gpio output enable to program in register
  rand bit [NUM_GPIOS-1:0] gpio_oe;

  function new(string name = "gpio_rand_straps_vseq");
    super.new(name);
  endfunction

  // Read hw_straps_data_in and hw_straps_data_in_valid and
  // check they match the expected value in
  // the scoreboard
  task csr_strap_read();
    uvm_status_e status_data_in;
    uvm_status_e status_data_in_valid;

    `uvm_info(`gfn, $sformatf("Reading the data_in status = %0d", status_data_in), UVM_HIGH)
    ral.hw_straps_data_in.mirror(.status(status_data_in), .check(UVM_CHECK), .prior(100));
    cfg.clk_rst_vif.wait_clks_or_rst(1);
    `uvm_info(`gfn, $sformatf("Reading the data valid status = %0d",
                              status_data_in_valid), UVM_HIGH)
    ral.hw_straps_data_in_valid.mirror(.status(status_data_in_valid),
                                       .check(UVM_CHECK),
                                       .prior(100));
    // Check for errors if is not under reset.
    if (!cfg.clk_rst_vif.rst_n) begin
      `uvm_info(`gfn, $sformatf("Reading ignored because is under reset"), UVM_LOW)
    end else begin
      `DV_CHECK_EQ(status_data_in, UVM_IS_OK)
      `DV_CHECK_EQ(status_data_in_valid, UVM_IS_OK)
    end
  endtask : csr_strap_read

  task test_straps_gpio_in();

    // Drive the gpio_in
    drive_gpio_in(gpio_in);
    cfg.clk_rst_vif.wait_clks_or_rst(1);

    // Random wait to drive the strap_en
    short_wait(0);

    // Trigger the snapshot of gpio_in to be stored in the straps registers
    cfg.straps_vif_inst.tb_port.strap_en = 1;
    // Wait at least one clock cycle to update the strap register values.
    cfg.clk_rst_vif.wait_clks_or_rst(2);
    // Read the hw_straps_data_in registers and check the expected value in the scoreboard
    csr_strap_read();
    cfg.clk_rst_vif.wait_clks_or_rst(1);
    // Random wait
    short_wait(0);
    // Stop driving gpio_in to make sure that, this is not affecting the strap_en registers
    // so it will keep the same values were stored before.
    undrive_gpio_in();
    cfg.clk_rst_vif.wait_clks_or_rst(1);
    // Random wait
    short_wait(1);
    // Read to make sure that if does not affect the straps registers after undrive the gpio_in
    csr_strap_read();
    cfg.clk_rst_vif.wait_clks_or_rst(1);
  endtask : test_straps_gpio_in

  task test_straps_gpio_out();
    // Drive the gpio_out to make sure that has no impact on straps registers.
    // then read the gpio strap registers again
    cfg.gpio_vif.drive_en('0);
    csr_wr(ral.direct_out, gpio_out);
    cfg.clk_rst_vif.wait_clks_or_rst(1);
    csr_wr(ral.direct_oe, gpio_oe);
    cfg.clk_rst_vif.wait_clks_or_rst(2);
    // Read to make sure that if does not affect the straps registers after drive the gpio_out
    csr_strap_read();
    cfg.clk_rst_vif.wait_clks_or_rst(1);
  endtask : test_straps_gpio_out

  // This task start the strap en test. First it will test the strap enable
  // with the driven gpio_i. On a second step drive the gpio_out and check the strap
  // registers based on that. And finally applies a second reset and check if the strap registers
  // are reseted.
  task start_test();

    `DV_CHECK_MEMBER_RANDOMIZE_FATAL(gpio_in)
    `DV_CHECK_MEMBER_RANDOMIZE_FATAL(gpio_out)
    `DV_CHECK_MEMBER_RANDOMIZE_FATAL(gpio_oe)

    // User case to test the straps output, with gpio_in data randomised
    test_straps_gpio_in();
    // User case to test the straps output/registers, with gpio_out data randomised
    // The gpio_out should not affect the straps output/registers.
    test_straps_gpio_out();
  endtask : start_test

  task body();
    `uvm_info(`gfn, "Starting the test", UVM_HIGH)
    // test is executed into the stress_all virtual sequence.
    start_test();
    `uvm_info(`gfn, "End of the test", UVM_HIGH)
  endtask : body

endclass : gpio_rand_straps_vseq
