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
        ral.hw_straps_data_in.mirror(status, UVM_CHECK);
        `DV_CHECK_EQ(status, UVM_IS_OK)
        `uvm_info(`gfn, $sformatf("Read the data_in status = %0d", status), UVM_HIGH)
      end
      begin
        uvm_status_e status;
        ral.hw_straps_data_in_valid.mirror(status, UVM_CHECK);
        `DV_CHECK_EQ(status, UVM_IS_OK)
        `uvm_info(`gfn, $sformatf("Read the data valid status = %0d", status), UVM_HIGH)
      end
    join
  endtask : csr_strap_read

  task test_straps_${module_instance_name}_in();
    // Drive the ${module_instance_name}_in
    drive_${module_instance_name}_in(${module_instance_name}_in);

    // Random wait to drive the strap_en
    // The strap feature should work from zero clock cycles
    // after driving the ${module_instance_name}_i inputs into the interface.
    short_wait(0);

    // Trigger the snapshot of ${module_instance_name}_in to be stored in the straps registers
    cfg.straps_vif_inst.tb_port.strap_en = 1;
    // Wait at least one clock cycle to update the strap register values.
    short_wait(1);

    // Read the hw_straps_data_in registers and check the expected value in the scoreboard
    csr_strap_read();

    // Random wait
    short_wait(0);

    // Stop driving ${module_instance_name}_in to make sure that, this is not affecting the strap_en registers
    // so it will keep the same values were stored before.
    undrive_${module_instance_name}_in();

    // Random wait
    short_wait(0);

    // Read to make sure that if does not affect the straps registers after undrive the ${module_instance_name}_in
    csr_strap_read();

  endtask : test_straps_${module_instance_name}_in

  task test_straps_${module_instance_name}_out();

    // Additional verification
    // Drive the ${module_instance_name}_out to make sure that has no impact on straps registers.
    // then read the ${module_instance_name} strap registers again
    cfg.${module_instance_name}_vif.drive_en('0);
    csr_wr(ral.direct_out, ${module_instance_name}_out);
    csr_wr(ral.direct_oe, ${module_instance_name}_oe);

    // Random wait
    short_wait(0);

    // Read to make sure that if does not affect the straps registers after drive the ${module_instance_name}_out
    csr_strap_read();

  endtask : test_straps_${module_instance_name}_out

  // This task start the strap en test. First it will test the strap enable
  // with the driven ${module_instance_name}_i. On a second step drive the ${module_instance_name}_out and check the strap
  // registers based on that. And finally applies a second reset and check if the strap registers
  // are reseted.
  task start_test();

    `DV_CHECK_MEMBER_RANDOMIZE_FATAL(${module_instance_name}_in)
    `DV_CHECK_MEMBER_RANDOMIZE_FATAL(${module_instance_name}_out)
    `DV_CHECK_MEMBER_RANDOMIZE_FATAL(${module_instance_name}_oe)

    // User case to test the strap outputs, with ${module_instance_name}_in data randomised
    test_straps_${module_instance_name}_in();

    // User case to test the strap outputs, with ${module_instance_name}_out data randomised
    // The ${module_instance_name}_out should not affect the straps output/registers.
    test_straps_${module_instance_name}_out();

    // Random wait
    short_wait(0);

    // Set zero to the strap_en input.
    cfg.straps_vif_inst.tb_port.strap_en = 0;
    // Apply reset and make sure the strap registers are clean
    apply_reset();

    // Random wait
    // At least one clock cycle required to take the updated register values.
    short_wait(1);

    // Read the straps registers after reset
    csr_strap_read();

  endtask : start_test

  task body();
    `uvm_info(`gfn, "Starting the test", UVM_HIGH)
    // Just a minimum one clock cycle wait between more than one iteration if this
    // test is executed into the stress_all virtual sequence.
    short_wait(1);
    start_test();
    `uvm_info(`gfn, "End of the test", UVM_HIGH)
  endtask : body

endclass : ${module_instance_name}_rand_straps_vseq