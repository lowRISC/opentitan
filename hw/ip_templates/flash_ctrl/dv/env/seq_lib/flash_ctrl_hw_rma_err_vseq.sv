// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// flash_ctrl_hw_rma Test

import lc_ctrl_pkg::*;

class flash_ctrl_hw_rma_err_vseq extends flash_ctrl_hw_rma_vseq;
  `uvm_object_utils(flash_ctrl_hw_rma_err_vseq)

  `uvm_object_new

  // Body
  task body();

    // Local Variables
    logic [RmaSeedWidth-1:0] rma_seed;
    bit                      rma_done;

    `uvm_info(`gfn, "FLASH_CTRL_HW_RMA", UVM_LOW)

    // These are valid assertoff's.
    $assertoff(0, "tb.dut.u_flash_hw_if.ProgRdVerify_A");
    $assertoff(0, "tb.dut.u_flash_hw_if.DisableChk_A");

    // RMA TESTS

    // INITIALIZE FLASH REGIONS
    init_data_part();
    init_info_part();

    // Delay
    cfg.clk_rst_vif.wait_clks($urandom_range(10, 100));

    // Select Data Partition Start Address an Num Words for this iteration
    set_rand_data_page(FlashData0Part, data0_part_addr, data0_part_num_words);
    set_rand_data_page(FlashData1Part, data1_part_addr, data1_part_num_words);

    // ERASE

    `uvm_info(`gfn, "ERASE", UVM_LOW)
    do_flash_ops(flash_ctrl_pkg::FlashOpErase, ReadCheckNorm);
    cfg.clk_rst_vif.wait_clks($urandom_range(10, 100));

    // PROGRAM

    `uvm_info(`gfn, "PROGRAM", UVM_LOW)
    do_flash_ops(flash_ctrl_pkg::FlashOpProgram, ReadCheckNorm);
    cfg.clk_rst_vif.wait_clks($urandom_range(10, 100));

    // READ (Compare Expected Data with Data Read : EXPECT DATA MATCH)

    `uvm_info(`gfn, "READ", UVM_LOW)
    do_flash_ops(flash_ctrl_pkg::FlashOpRead, ReadCheckNorm);

    // SEND RMA REQUEST (Erases the Flash and Writes Random Data To All Partitions)
    fork
      begin
        cfg.clk_rst_vif.wait_clks($urandom_range(10, 100));
        fork
          begin
            `uvm_info(`gfn, "RMA REQUEST", UVM_LOW)
            rma_seed = $urandom;  // Random RMA Seed
            send_rma_req(rma_seed);
            cfg.clk_rst_vif.wait_clks($urandom_range(10, 100));
            // This should not happen
            if (cfg.rma_ack_polling_stop == 0) rma_done = 1;
          end
          begin
            csr_spinwait(.ptr(ral.debug_state),
                         .exp_data(flash_ctrl_env_pkg::FlashLcInvalid),
                         .spinwait_delay_ns(500_000),
                         .timeout_ns(2_000_000_000));
            cfg.clk_rst_vif.wait_clks(3);
            `uvm_info(`gfn, "RMA FAIL DUE TO Wipe out write data failure (expected)", UVM_LOW)
            collect_err_cov_status(ral.std_fault_status);
            csr_rd_check(.ptr(ral.std_fault_status.lcmgr_err), .compare_value(1));
          end
        join_any
      end
      begin
        // Assert flash_ctrl.INIT at the beginning of RMA or
        // in the middle
        int val = $urandom_range(0, 1);
        `uvm_info(`gfn, $sformatf("INIT val: %0d", val), UVM_MEDIUM)
        csr_wr(.ptr(ral.init), .value(val));

        if (val == 0) begin
          int my_wait = $urandom_range(1,100);
          val = $urandom_range(0, 1);
          #(my_wait * 1ms);
          csr_wr(.ptr(ral.init), .value(val));
        end
      end
      begin
        string path = {"tb.dut.u_eflash.gen_flash_cores[0].u_core.gen_prog_data",
                       ".u_prog.pack_data[31:0]"};

        `DV_SPINWAIT(wait(cfg.flash_ctrl_vif.rma_state == StRmaEraseWait);,
                     , cfg.seq_cfg.state_wait_timeout_ns)
        flip_2bits(path);
        cfg.clk_rst_vif.wait_clks(10);
        `DV_CHECK(uvm_hdl_release(path))
        // Fatal alert (std_fault_status.lcmgr_err) is checked in the other thread by
        // csr_rd_check
        cfg.scb_h.do_alert_check = 0;
      end
    join

    // RESET DUT
    `uvm_info("Test", "RMA END", UVM_LOW)
    `DV_CHECK_NE(rma_done, 1, "rma_done shouldn't be 1")
    // Stop rma polling
    cfg.rma_ack_polling_stop = 1;

    `uvm_info(`gfn, "RESET", UVM_LOW)
    lc_ctrl_if_rst();  // Restore lc_ctrl_if to Reset Values
    cfg.seq_cfg.disable_flash_init = 1;  // Disable Flash Random Initialisation
    apply_reset();

    // INITIALIZE FLASH REGIONS

    init_data_part();
    init_info_part();

    // READ (Compare Expected Data with Data Read : EXPECT DATA MISMATCH or STATUS FAIL)
    // After Reset and DUT Initialisation, Check the FLASH is written randomly and its contents
    // mismatch against its contents before the RMA took place.
    // This may get an occasional Hit ~ 1 in 32^2-1, per location
    // Additionally check that the Flash has not just been Erased, but has been overwritten.

    `uvm_info(`gfn, "READ", UVM_LOW)

    do_flash_ops(flash_ctrl_pkg::FlashOpRead, ReadCheckRand);
    cfg.clk_rst_vif.wait_clks($urandom_range(10, 100));

  endtask : body

endclass : flash_ctrl_hw_rma_err_vseq
