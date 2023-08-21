// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// flash_ctrl_hw_rma Test

// Pseudo Code
// Initialise (All)
// Loop {
//   Erase Partitions(#)
//   Program Partitions(#)
//   Read Partitions(#)
//   RMA REQUEST (Random Seed)
//   Check Software has NO Access to the FLASH
//   Reset DUT (No Flash Init)
//   Initialise
//   Read Partitions#() Compare Data (MISMATCH Expected)
//     (additionally check Data Read is not all 1's
//     indicating Erase but not RMA Wipe)
// }
// #Random Order : Creator(page), Owner(page), Isolation(page),
//                 Data0(random page), Data1(random page)

import lc_ctrl_pkg::*;

class flash_ctrl_hw_rma_vseq extends flash_ctrl_base_vseq;
  `uvm_object_utils(flash_ctrl_hw_rma_vseq)

  `uvm_object_new

  // Class Members
  data_q_t flash_creator_data;
  data_q_t flash_owner_data;
  data_q_t flash_isol_data;
  data_q_t flash_data0_data;
  data_q_t flash_data1_data;
  uint     data0_part_addr;
  uint     data0_part_num_words;
  uint     data1_part_addr;
  uint     data1_part_num_words;

  // Configure sequence knobs to tailor it to this seq
  virtual function void configure_vseq();

    // Enable NO memory protection regions
    cfg.seq_cfg.num_en_mp_regions   = 0;
    cfg.seq_cfg.poll_fifo_status_pc = 0;

    // Enable Checks Post Transaction
    cfg.seq_cfg.check_mem_post_tran = 1;

    // Randomize the 'Keys and Seeds' Setting to prove
    // this has no effect on the RMA
    cfg.seq_cfg.en_init_keys_seeds = $urandom;

  endfunction : configure_vseq

  // Body
  task body();

    // Local Variables
    logic [RmaSeedWidth-1:0] rma_seed;

    `uvm_info(`gfn, "FLASH_CTRL_HW_RMA", UVM_LOW)

    // RMA TESTS

    // INITIALIZE FLASH REGIONS
    init_data_part();
    init_info_part();

    // Delay
    cfg.clk_rst_vif.wait_clks($urandom_range(10, 100));

    // Iterate fixed Number of iterations as test time is VERY LONG.
    // Since this test is getting unbearably long in the closed-source, when running in the
    //  closed-source, this test will do only one iteration.
    num_trans = `PRIM_DEFAULT_IMPL==prim_pkg::ImplGeneric ? 2 : 1;
    for (int i=0; i<num_trans; i++) begin

      `uvm_info(`gfn, $sformatf("Iteration : %0d", i+1), UVM_LOW)

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
          `uvm_info(`gfn, "RMA REQUEST", UVM_LOW)
          rma_seed = $urandom;  // Random RMA Seed
          send_rma_req(rma_seed);
          cfg.clk_rst_vif.wait_clks($urandom_range(10, 100));
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
      join
      // CHECK HOST SOFTWARE HAS NO ACCESS TO THE FLASH

      // Attempt to Read from FLASH Controller
      do_flash_ctrl_access_check();

      // RESET DUT

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

    end

  endtask : body

  virtual task init_data_part();

    // DATA PARTITION

    flash_mp_region_cfg_t mp_regions [flash_ctrl_pkg::MpRegions];
    bit [flash_ctrl_pkg::NumBanks-1:0] bank_erase_en;
    mubi4_t default_region_read_en;
    mubi4_t default_region_program_en;
    mubi4_t default_region_erase_en;

    // No Protection Regions
    foreach (mp_regions[i]) begin
      mp_regions[i].en = MuBi4False;
    end

    // Configure MP Regions
    foreach (mp_regions[i]) begin
      flash_ctrl_mp_region_cfg(i, mp_regions[i]);
    end

    default_region_read_en    = MuBi4True;
    default_region_program_en = MuBi4True;
    default_region_erase_en   = MuBi4True;

    // Write to Default MP Regions
    flash_ctrl_default_region_cfg(.read_en    (default_region_read_en),
                                  .program_en (default_region_program_en),
                                  .erase_en   (default_region_erase_en));

    // Configure Bank Erasability
    foreach (bank_erase_en[i]) begin
      bank_erase_en[i] = 1;
    end
    flash_ctrl_bank_erase_cfg(.bank_erase_en(bank_erase_en));

  endtask : init_data_part

  virtual task init_info_part();

    // INFO REGION

    flash_bank_mp_info_page_cfg_t info_regions [flash_ctrl_reg_pkg::NumInfos0];

    // Enable All Info Regions for Read, Program and Erase

    foreach (info_regions[i]) begin
      info_regions[i].en         = MuBi4True;
      info_regions[i].read_en    = MuBi4True;
      info_regions[i].program_en = MuBi4True;
      info_regions[i].erase_en   = MuBi4True;
    end

    foreach (info_regions[i]) begin
      flash_ctrl_mp_info_page_cfg(.bank(0), .info_part(0), .page(i), .page_cfg(info_regions[i]));
    end

  endtask : init_info_part

  // Task to perform randomly ordered selected Flash Operations on thr Flash
  virtual task do_flash_ops (input flash_op_e op, input read_check_e cmp = ReadCheckNorm);
    uint order_q [$] = '{0, 1, 2, 3, 4};  // Operation Order Queue
    order_q.shuffle();  // Shuffle Queue Items

    // Process in random order
    foreach (order_q[i]) begin
      unique case(order_q[i])
        0 : do_flash_op_rma(FlashCreatorPart, op, flash_creator_data, cmp, 0, 0);
        1 : do_flash_op_rma(FlashOwnerPart,   op, flash_owner_data,   cmp, 0, 0);
        2 : do_flash_op_rma(FlashIsolPart,    op, flash_isol_data,    cmp, 0, 0);
        3 : do_flash_op_rma(FlashData0Part,   op, flash_data0_data,   cmp,  data0_part_addr,
              data0_part_num_words);
        4 : do_flash_op_rma(FlashData1Part,   op, flash_data1_data,   cmp,  data1_part_addr,
              data1_part_num_words);
        default: `uvm_error(`gfn, "Unrecognised Flash Operation, FAIL")
      endcase
    end
  endtask : do_flash_ops

  // Task to check for No access to Flash Controller following an RMA
  virtual task do_flash_ctrl_access_check();

    // Local Variables
    flash_op_t flash_op;
    data_q_t   data;
    bit        result;
    int        read_timeout_value_ns = 100000; // 100us
    `uvm_info(`gfn, "Attempting to READ from Flash", UVM_INFO)

    // Attempt to Read from FLASH, No Access Expected after RMA
    flash_op.op = flash_ctrl_pkg::FlashOpRead;

    // Select a Random Partition to try to Read From
    randcase
      1 : begin flash_op.addr = FlashCreatorPartStartAddr;  // Flash Creator Part
                flash_op.partition = FlashPartInfo;
                cfg.flash_ctrl_vif.lc_seed_hw_rd_en         = lc_ctrl_pkg::On;
                cfg.flash_ctrl_vif.lc_creator_seed_sw_rw_en = lc_ctrl_pkg::On;
          end
      1 : begin flash_op.addr = FlashOwnerPartStartAddr;  // Flash Owner Part
                flash_op.partition = FlashPartInfo;
                cfg.flash_ctrl_vif.lc_seed_hw_rd_en       = lc_ctrl_pkg::On;
                cfg.flash_ctrl_vif.lc_owner_seed_sw_rw_en = lc_ctrl_pkg::On;
          end
      1 : begin flash_op.addr = FlashIsolPartStartAddr;  // Flash Isolation Part
                flash_op.partition = FlashPartData;
                cfg.flash_ctrl_vif.lc_iso_part_sw_rd_en = lc_ctrl_pkg::On;
                cfg.flash_ctrl_vif.lc_iso_part_sw_wr_en = lc_ctrl_pkg::On;
          end
      1 : begin flash_op.addr = FlashData0StartAddr;  // Flash Data0 Part
                flash_op.partition = FlashPartData;
          end
      1 : begin flash_op.addr = FlashData1StartAddr;  // Flash Data1 Part
                flash_op.partition = FlashPartData;
          end
    endcase

    // Arbitrary num_words - Access should fail on the first attempt
    flash_op.num_words  = $urandom_range(8, 16);
    flash_op.erase_type = $urandom ? flash_ctrl_pkg::FlashErasePage :
                                     flash_ctrl_pkg::FlashEraseBank;

    // Start Read Operation
    flash_ctrl_start_op(flash_op);

    // Timeout Expected
    wait_flash_op_done_expect_timeout(.timeout_ns(read_timeout_value_ns), .result(result));

    // Expect a Timeout
    if (result == 1)
      `uvm_info(`gfn,  "Timeout Seen - Flash Not Accessible By Software, Expected, PASS", UVM_LOW)
    else
      `uvm_error(`gfn, "Timeout Not Seen - Flash Accessible By Software, Unexpected, FAIL")

  endtask : do_flash_ctrl_access_check

  // Task to Select a Random Data Partition Page, and return its address
  virtual task set_rand_data_page(input flash_sec_part_e part, output uint addr,
                                  output uint num_words);

    // Local Variables
    uint page;

    // Select a Random Data Partition Page
    page = $urandom_range(0, MaxNumPages-1);

    // Small rma only stash 2 pages
    if (cfg.en_small_rma) page = page % 2;

    // Assign Address based on Partition Selected, and fixed number of words
    unique case (part)
      FlashData0Part: addr = FlashData0StartAddr+(page*(FullPageNumWords*4)); // Base+Page Offset
      FlashData1Part: addr = FlashData1StartAddr+(page*(FullPageNumWords*4)); // Base+Page Offset
      default : `uvm_error(`gfn, "Unrecognised Partition, FAIL")
    endcase
    num_words = FullPageNumWords;

    `uvm_info(`gfn, $sformatf("Test Chose : %s : page : %0d, addr = 0x%0x, num_words : %0d",
      part.name(), page, addr, num_words), UVM_LOW)

  endtask : set_rand_data_page

endclass : flash_ctrl_hw_rma_vseq
