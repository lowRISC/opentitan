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

  // Read hw_straps_data_in and hw_straps_data_in_valid
  // in a shuffle order and
  // check they match the expected value in
  // the scoreboard
  task csr_strap_read();
    uvm_reg regs[$] = '{ral.hw_straps_data_in, ral.hw_straps_data_in_valid};
    regs.shuffle();
    foreach(regs[i]) begin
      uvm_status_e status;
      regs[i].mirror(.status(status), .check(UVM_CHECK), .prior(100));
      if(status != UVM_IS_OK && !cfg.under_reset) begin
        `uvm_error(`gfn, $sformatf("Error reading %s", regs[i].get_full_name()))
      end
    end
  endtask : csr_strap_read

  // Drive the strap_en_i input signal using the strap_en_seq sequence
  task set_strap_en(bit strap_en);

    string strap_seqr = "strap_sequencer";
    strap_sequencer seqr;
    gpio_strap_en_vseq strap_en_seq;

    // Instantiate the strap_en sequence
    strap_en_seq = gpio_strap_en_vseq::type_id::create("strap_en_seq");

    if(!$cast(seqr, p_sequencer.get_sequencer(strap_seqr))) begin
      `uvm_fatal(`gfn, "cast error getting the strap sequencer")
    end

    // Start the strap_en_seq sequence with the desired value.
    if (seqr != null) begin
      `uvm_info(`gfn, $sformatf("Driving strap_en = %0d", strap_en), UVM_HIGH)
      strap_en_seq.strap_en = strap_en;
      strap_en_seq.start(seqr);
    end
  endtask : set_strap_en

  task test_straps_gpio_in();

    drive_gpio_in(gpio_in);
    cfg.clk_rst_vif.wait_clks_or_rst(1);

    // Random wait to drive the strap_en
    short_wait(0);
    if (!cfg.clk_rst_vif.rst_n) return;

    // Trigger the snapshot of gpio_in to be stored in the straps registers
    set_strap_en('b1);
    if (!cfg.clk_rst_vif.rst_n) return;
    // Wait at least one clock cycle to update the strap register values.
    cfg.clk_rst_vif.wait_clks_or_rst(4);
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
      `uvm_info(`gfn, "Start of Test", UVM_HIGH)
      start_test();
      `uvm_info(`gfn, "End of Test", UVM_HIGH)
  endtask : body

endclass : gpio_rand_straps_vseq
