// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Verify the straps data/valid ouput expected values based on the strap_en and ${module_instance_name}_in inputs:
//    - Drive ${module_instance_name}_in input with random values.
//    - Set the strap_en high for at least one clock cycle.
//    - Read the registers hw_straps_data_in and hw_straps_data_in_valid.
//    - The data read and sampled_straps_o will be checked in the scoreboard.
//    - Drive the ${module_instance_name}_out to make sure that has no impact on straps registers.
//    - Read to make sure that if does not affect the straps registers after drive the ${module_instance_name}_out.
//    - Apply reset and make sure the strap registers are clean.
//    - Read straps registers after reset.
//    - Iterate again the same flow, with new random values.
class ${module_instance_name}_rand_straps_vseq extends ${module_instance_name}_base_vseq;

  `uvm_object_utils(${module_instance_name}_rand_straps_vseq)

  // ${module_instance_name} input to drive
  rand bit [NUM_GPIOS-1:0] ${module_instance_name}_in;
  // ${module_instance_name} output to program in register
  rand bit [NUM_GPIOS-1:0] ${module_instance_name}_out;
  // ${module_instance_name} output enable to program in register
  rand bit [NUM_GPIOS-1:0] ${module_instance_name}_oe;

  function new(string name = "${module_instance_name}_rand_straps_vseq");
    super.new(name);
  endfunction

  // Read hw_straps_data_in and hw_straps_data_in_valid and
  // check they match the expected value in
  // the scoreboard
  task csr_strap_read();
    fork
      begin
        uvm_status_e status;
        ral.hw_straps_data_in.mirror(.status(status), .check(UVM_CHECK), .prior(100));
        cfg.clk_rst_vif.wait_clks_or_rst(1);
        `DV_CHECK_EQ(status, UVM_IS_OK)
        `uvm_info(`gfn, $sformatf("Read the data_in status = %0d", status), UVM_HIGH)
      end
      begin
        uvm_status_e status;
        ral.hw_straps_data_in_valid.mirror(.status(status), .check(UVM_CHECK), .prior(100));
        cfg.clk_rst_vif.wait_clks_or_rst(1);
        `DV_CHECK_EQ(status, UVM_IS_OK)
        `uvm_info(`gfn, $sformatf("Read the data valid status = %0d", status), UVM_HIGH)
      end
    join
  endtask : csr_strap_read

  // Drive the strap_en_i input signal using the strap_en_seq sequence
  task set_strap_en(bit strap_en);

    string strap_seqr = "strap_sequencer";
    strap_sequencer seqr;
    ${module_instance_name}_strap_en_vseq strap_en_seq;

    // Instantiate the strap_en sequence
    strap_en_seq = ${module_instance_name}_strap_en_vseq::type_id::create("strap_en_seq");

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

  task test_straps_${module_instance_name}_in();

    // Drive the ${module_instance_name}_in
    `uvm_info(`gfn, "Drive data_in", UVM_HIGH)
    drive_${module_instance_name}_in(${module_instance_name}_in);
    `uvm_info(`gfn, "Driven data_in", UVM_HIGH)

    // Wait at least one clock cycle to drive the strap_en
    // Required because is required one clock cycle to update the ${module_instance_name}_in regsisters.
    `DV_CHECK_MEMBER_RANDOMIZE_WITH_FATAL(delay, delay >= 0;)
    cfg.clk_rst_vif.wait_clks_or_rst(delay);

    `uvm_info(`gfn, "Trigger strap_en", UVM_HIGH)
    // Trigger the snapshot of ${module_instance_name}_in to be stored in the straps registers
    //cfg.straps_vif_inst.tb_port.strap_en = 1;

    set_strap_en('b1);

    `uvm_info(`gfn, "Triggered strap_en", UVM_HIGH)

    // Wait at least one clock cycle to update the strap register values.
    cfg.clk_rst_vif.wait_clks_or_rst(1);

    // Wait some clock cycles to avoid race condition between the prediction value updated
    // in the scoreboard happening together with the csr read transaction.
    `DV_CHECK_MEMBER_RANDOMIZE_WITH_FATAL(delay, delay >= 4;)
    cfg.clk_rst_vif.wait_clks_or_rst(delay);

    // Read the hw_straps_data_in and check the expected value in the scoreboard
    cfg.clk_rst_vif.wait_clks_or_rst(2);
    // Skip if a reset is ongoing...
    if (!cfg.clk_rst_vif.rst_n) begin
      cfg.clk_rst_vif.wait_clks_or_rst(2);
    end
    csr_strap_read();
    cfg.clk_rst_vif.wait_clks_or_rst(1);
    // Skip if a reset is ongoing...
    if (!cfg.clk_rst_vif.rst_n) return;
    // Random wait
    //short_wait(0);

    // Stop driving ${module_instance_name}_in to make sure that, this is not affecting the strap_en registers
    // so it will keep the same values were stored before.
    //undrive_${module_instance_name}_in();
    //cfg.clk_rst_vif.wait_clks_or_rst(1);
    // Skip if a reset is ongoing...
    //if (!cfg.clk_rst_vif.rst_n) return;
    // Random wait
    //short_wait(0);

    //cfg.clk_rst_vif.wait_clks_or_rst(1);
    // Read again to make sure that if does not affect the straps registers after undrive the ${module_instance_name}_in
    //csr_strap_read();
    // Skip if a reset is ongoing...
    //if (!cfg.clk_rst_vif.rst_n) return;
    //cfg.clk_rst_vif.wait_clks_or_rst(1);
  endtask : test_straps_${module_instance_name}_in

  task test_straps_${module_instance_name}_out();

    // Additional verification
    // Drive the ${module_instance_name}_out to make sure that has no impact on straps registers.
    // then read the ${module_instance_name} strap registers again
    cfg.${module_instance_name}_vif.drive_en('0);
    cfg.clk_rst_vif.wait_clks_or_rst(1);
    csr_wr(ral.direct_out, ${module_instance_name}_out);
    cfg.clk_rst_vif.wait_clks_or_rst(1);
    // Skip if a reset is ongoing...
    if (!cfg.clk_rst_vif.rst_n) return;
    csr_wr(ral.direct_oe, ${module_instance_name}_oe);
    cfg.clk_rst_vif.wait_clks_or_rst(1);
    // Skip if a reset is ongoing...
    if (!cfg.clk_rst_vif.rst_n) return;

    // Random wait
    short_wait(0);

    // Read to make sure that if does not affect the straps registers after drive the ${module_instance_name}_out
    csr_strap_read();
    cfg.clk_rst_vif.wait_clks_or_rst(1);
    // Skip if a reset is ongoing...
    if (!cfg.clk_rst_vif.rst_n) return;

  endtask : test_straps_${module_instance_name}_out

  task start_test();

    `DV_CHECK_MEMBER_RANDOMIZE_FATAL(${module_instance_name}_in)
    `DV_CHECK_MEMBER_RANDOMIZE_FATAL(${module_instance_name}_out)
    `DV_CHECK_MEMBER_RANDOMIZE_FATAL(${module_instance_name}_oe)

    // User case to test the strap outputs, with ${module_instance_name}_in data randomised
    `uvm_info(`gfn, "Start test_straps data_in", UVM_HIGH)
    cfg.clk_rst_vif.wait_clks_or_rst(1);
    if (!cfg.clk_rst_vif.rst_n) return;
    test_straps_${module_instance_name}_in();

    // User case to test the strap outputs, with ${module_instance_name}_out data randomised
    // The ${module_instance_name}_out should not affect the straps output/registers.
    //if (!cfg.clk_rst_vif.rst_n) return;
    //test_straps_${module_instance_name}_out();
    //if (!cfg.clk_rst_vif.rst_n) return;

    // Random wait
    //short_wait(0);

    //cfg.clk_rst_vif.wait_clks_or_rst(1);
    //if (!cfg.clk_rst_vif.rst_n) return;
    // Disable the strap_en
    //set_strap_en('b0);
    //cfg.clk_rst_vif.wait_clks_or_rst(1);
    //if (!cfg.clk_rst_vif.rst_n) return;

    // Set zero to the strap_en input.
    //cfg.straps_vif_inst.tb_port.strap_en = 0;

    // Apply reset and make sure the strap registers are clean
    //  apply_reset();

    //cfg.clk_rst_vif.wait_clks_or_rst(1);
    // Skip if a reset is ongoing...
    //if (!cfg.clk_rst_vif.rst_n) return;

    // Random wait, at least one clock cycle to avoid race condition
    // between the reset and read transactions.
    //short_wait(1);

    //cfg.clk_rst_vif.wait_clks_or_rst(1);
    // Skip if a reset is ongoing...
    //if (!cfg.clk_rst_vif.rst_n) return;

    //csr_strap_read();

    //cfg.clk_rst_vif.wait_clks_or_rst(1);
    // Skip if a reset is ongoing...
    //if (!cfg.clk_rst_vif.rst_n) return;

  endtask : start_test

  task body();
      cfg.clk_rst_vif.wait_clks_or_rst(1);
      if (!cfg.clk_rst_vif.rst_n) return;
      // Random wait
      short_wait(0);
      `uvm_info(`gfn, "Start of Test", UVM_HIGH)
      start_test();
      `uvm_info(`gfn, "End of Test", UVM_HIGH)
  endtask : body

endclass : ${module_instance_name}_rand_straps_vseq