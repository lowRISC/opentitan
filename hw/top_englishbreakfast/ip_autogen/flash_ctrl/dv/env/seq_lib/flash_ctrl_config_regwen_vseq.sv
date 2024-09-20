// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Designated sequence to test "RO" type regwen
// The sequence does write and read back check for flash_ctrl.control register.
// Then it launches long operation.
// While operation is on going, try write random data but register value should not be changed.
// Finally, release flash_ctrl.ctrl_regwen and does write and readback check
// with a random data.
// This test does not include any flash data transaction.
class flash_ctrl_config_regwen_vseq extends flash_ctrl_otf_base_vseq;
  `uvm_object_utils(flash_ctrl_config_regwen_vseq)
  `uvm_object_new

  rand bit[31:0] ctrl_data;

  // Make rsvd field '0'
  constraint ctrl_data_c {
    ctrl_data[3:1] == 0;
    ctrl_data[15:11] == 0;
    ctrl_data[31:28] == 0;
  }

  task body();
    uvm_reg_data_t exp_data, dumb_data;

    // Randomized program of control register can trigger
    // unintended or illegal transactions.
    // Since the purpose of this test is to check regwen function,
    // turn off scoreboard to avoid spurious transaction error.
    // Also cover csr read, write check in this sequence.
    cfg.scb_h.skip_read_check = 1;
    cfg.scb_check = 0;
    // Write and read back control register
    `DV_CHECK_MEMBER_RANDOMIZE_FATAL(ctrl_data)
    // Capture for expected data after regwen force '0'
    // set op_start to 0 to avoid spurious error
    ctrl_data[0] = 0;
    exp_data = ctrl_data;
    `uvm_info(`gfn, $sformatf("TEST: exp_data: %x", exp_data), UVM_MEDIUM)
    write_readback_ctrl(.wr_data(exp_data), .exp_data(exp_data));

    // Launch long operation
    flash_program_data_c.constraint_mode(0);

    // Added to avoid contradiction and to follow the constraint ctrl_num_c in
    // flash_ctrl_otf_base_vseq line 95 (at 5/6/2024):
    // if (rand_op.partition == FlashPartData) ctrl_num == ctrl_data_num;
    ctrl_num = ctrl_data_num;
    `DV_CHECK_MEMBER_RANDOMIZE_WITH_FATAL(
        rand_op,
        rand_op.op == FlashOpProgram;
        rand_op.partition == FlashPartData;)
    rand_op.addr[8:0] = 0;
    rand_op.num_words = 16;
    flash_ctrl_start_op(rand_op);
    csr_rd(.ptr(ral.control), .value(exp_data));

    `uvm_info(`gfn, $sformatf("TEST after op start: exp_data: %x", exp_data), UVM_MEDIUM)
    repeat (5) begin
      // Read back value should not be change
      // because regwen is '0'
      dumb_data = $urandom();
      write_readback_ctrl(.wr_data(dumb_data), .exp_data(exp_data));
      cfg.clk_rst_vif.wait_clks($urandom_range(0,10));
    end
    flash_program_data = '{};
    for (int i = 0; i < 16; i++) begin
      flash_program_data.push_back($urandom());
    end
    flash_ctrl_write(flash_program_data, 1);
    wait_flash_op_done(.timeout_ns(cfg.seq_cfg.prog_timeout_ns));

    rand_op_c.constraint_mode(0);
    `DV_CHECK_MEMBER_RANDOMIZE_FATAL(ctrl_data)
    ctrl_data[0] = 0;
    write_readback_ctrl(.wr_data(ctrl_data), .exp_data(ctrl_data));

  endtask // body

  task write_readback_ctrl(uvm_reg_data_t wr_data,
                           uvm_reg_data_t exp_data);
    csr_wr(.ptr(ral.control), .value(wr_data));
    csr_rd_check(.ptr(ral.control), .compare_value(exp_data));
  endtask // write_readback_ctrl

endclass // flash_ctrl_config_regwen_vseq
