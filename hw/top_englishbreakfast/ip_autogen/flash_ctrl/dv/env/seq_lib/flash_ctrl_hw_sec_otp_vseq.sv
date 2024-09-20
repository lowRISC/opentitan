// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

//  Pseudo Code:
//  Randomize Flash Content (Backdoor)
//  Power Up Initialisation (With Secret Seeds and Keys Enabled)
//  Loop {
//    Randomize OTP Keys, Grab During INIT
//    Initialise Data and Info Partitions
//    FLASH READ    : Creator and Owner Partition and Compare Seeds Read with Key Manager.
//                    Additionally check Partitions with the previous data programmed
//                    after initial power (if programmed)
//    FLASH ERASE   : Creator and Owner Partitions (Backdoor Check)
//    FLASH PROGRAM : Creator and Owner Partitions (Backdoor Check)
//    FLASH READ    : Creator/Owner Partition (Save Programmed Data)
//    Check OTP Keys At Destination in Flash Ctrl Module
//    Reset DUT - Enable Secret Key INIT
//    Do Not Randomly Initialise Flash Content
//  Repeat
//  }

// flash_ctrl_hw_sec_otp Test

class flash_ctrl_hw_sec_otp_vseq extends flash_ctrl_base_vseq;
  `uvm_object_utils(flash_ctrl_hw_sec_otp_vseq)

  `uvm_object_new

  // Overloaded Constraint from Base Class
  constraint num_trans_c {num_trans inside {[32 : cfg.seq_cfg.max_num_trans]};}

  // Configure sequence knobs to tailor it to this seq
  virtual function void configure_vseq();

    // Max Num Iterations
    cfg.seq_cfg.max_num_trans = 256;

    // Enable NO memory protection regions
    cfg.seq_cfg.num_en_mp_regions = 0;

    // Enable Checks Post Transaction
    cfg.seq_cfg.check_mem_post_tran = 1;

    // Enable Initial Secret Seed Readout
    cfg.seq_cfg.en_init_keys_seeds = 1;

  endfunction : configure_vseq

  virtual task body();

    // Local Variables
    data_q_t flash_op_data;
    data_q_t exp_creator_data;
    data_q_t exp_owner_data;
    data_q_t dummy_data;  // Not Used (But Passed to Task)
    uint     case_sel;
    bit      creator_prog_flag;
    bit      owner_prog_flag;  // Indicates When Secret Partition Has Been Written

    `uvm_info(`gfn, "TEST : FLASH CTRL SECRET PARTITION & OTP KEY TESTS", UVM_LOW)

    // Initialise Partion Flags to Indicate Unwritten (from Frontdoor)
    creator_prog_flag = 1'b0;
    owner_prog_flag   = 1'b0;

    // Test over a number of RESET Cycles
    for (int iter = 0; iter < num_trans; iter++) begin

      // Configure the FLASH Controller

      // INITIALIZE FLASH REGIONS
      init_data_part();
      init_info_part();

      // READ and COMPARE CREATOR AND OWNER SEEDS

      `uvm_info(`gfn, "READ and COMPARE", UVM_LOW)

      // Read back Creator and Owner seeds via Host, and compare with the data presented to the Key Manager Interface.
      randcase
        1: begin
          do_flash_op_secret_part(FlashCreatorPart, flash_ctrl_pkg::FlashOpRead, flash_op_data);
          if (creator_prog_flag) check_data_match(flash_op_data, exp_creator_data);
          compare_secret_seed(FlashCreatorPart, flash_op_data);
        end
        1: begin
          do_flash_op_secret_part(FlashOwnerPart, flash_ctrl_pkg::FlashOpRead, flash_op_data);
          if (owner_prog_flag) check_data_match(flash_op_data, exp_owner_data);
          compare_secret_seed(FlashOwnerPart, flash_op_data);
        end
        1: begin
          do_flash_op_secret_part(FlashCreatorPart, flash_ctrl_pkg::FlashOpRead, flash_op_data);
          if (creator_prog_flag) check_data_match(flash_op_data, exp_creator_data);
          compare_secret_seed(FlashCreatorPart, flash_op_data);
          do_flash_op_secret_part(FlashOwnerPart, flash_ctrl_pkg::FlashOpRead, flash_op_data);
          if (owner_prog_flag) check_data_match(flash_op_data, exp_owner_data);
          compare_secret_seed(FlashOwnerPart, flash_op_data);
        end
        1: begin
          do_flash_op_secret_part(FlashOwnerPart, flash_ctrl_pkg::FlashOpRead, flash_op_data);
          if (owner_prog_flag) check_data_match(flash_op_data, exp_owner_data);
          compare_secret_seed(FlashOwnerPart, flash_op_data);
          do_flash_op_secret_part(FlashCreatorPart, flash_ctrl_pkg::FlashOpRead, flash_op_data);
          if (creator_prog_flag) check_data_match(flash_op_data, exp_creator_data);
          compare_secret_seed(FlashCreatorPart, flash_op_data);
        end
      endcase

      // ERASE CREATOR AND OWNER PARTITIONS

      // Choose an Erase/Program Test Order
      case_sel = $urandom_range(0, 3);

      `uvm_info(`gfn, "ERASE", UVM_LOW)

      // Choose Erase/Program Combination to perform this iteration
      unique case (case_sel)
        0: begin
          do_flash_op_secret_part(FlashCreatorPart, flash_ctrl_pkg::FlashOpErase, dummy_data);
        end
        1: begin
          do_flash_op_secret_part(FlashOwnerPart, flash_ctrl_pkg::FlashOpErase, dummy_data);
        end
        2: begin
          do_flash_op_secret_part(FlashCreatorPart, flash_ctrl_pkg::FlashOpErase, dummy_data);
          do_flash_op_secret_part(FlashOwnerPart, flash_ctrl_pkg::FlashOpErase, dummy_data);
        end
        3: begin
          do_flash_op_secret_part(FlashOwnerPart, flash_ctrl_pkg::FlashOpErase, dummy_data);
          do_flash_op_secret_part(FlashCreatorPart, flash_ctrl_pkg::FlashOpErase, dummy_data);
        end
        default: `uvm_error(`gfn, $sformatf("No case item match, FAIL"))
      endcase

      // PROGRAM CREATOR AND OWNER PARTITIONS

      `uvm_info(`gfn, "PROGRAM", UVM_LOW)

      // Note: Uses case_sel value from above
      unique case (case_sel)
        0: begin
          do_flash_op_secret_part(FlashCreatorPart, flash_ctrl_pkg::FlashOpProgram, dummy_data);
        end
        1: begin
          do_flash_op_secret_part(FlashOwnerPart, flash_ctrl_pkg::FlashOpProgram, dummy_data);
        end
        2: begin
          do_flash_op_secret_part(FlashCreatorPart, flash_ctrl_pkg::FlashOpProgram, dummy_data);
          do_flash_op_secret_part(FlashOwnerPart, flash_ctrl_pkg::FlashOpProgram, dummy_data);
        end
        3: begin
          do_flash_op_secret_part(FlashOwnerPart, flash_ctrl_pkg::FlashOpProgram, dummy_data);
          do_flash_op_secret_part(FlashCreatorPart, flash_ctrl_pkg::FlashOpProgram, dummy_data);
        end
        default: `uvm_error(`gfn, $sformatf("No case item match, FAIL"))
      endcase

      // READ CREATOR AND OWNER SEED PARTITIONS

      `uvm_info(`gfn, "READ", UVM_LOW)

      randcase
        1: begin
          do_flash_op_secret_part(FlashCreatorPart, flash_ctrl_pkg::FlashOpRead, exp_creator_data);
        end
        1: begin
          do_flash_op_secret_part(FlashOwnerPart, flash_ctrl_pkg::FlashOpRead, exp_owner_data);
        end
        1: begin
          do_flash_op_secret_part(FlashCreatorPart, flash_ctrl_pkg::FlashOpRead, exp_creator_data);
          do_flash_op_secret_part(FlashOwnerPart, flash_ctrl_pkg::FlashOpRead, exp_owner_data);
        end
        1: begin
          do_flash_op_secret_part(FlashOwnerPart, flash_ctrl_pkg::FlashOpRead, exp_owner_data);
          do_flash_op_secret_part(FlashCreatorPart, flash_ctrl_pkg::FlashOpRead, exp_creator_data);
        end
      endcase

      // OTP SCRAMBLE SEED TESTS - CONNECTIVITY TEST ONLY
      otp_scramble_key_test_connect();

      // RESET DUT

      `uvm_info(`gfn, ">>> RESET DUT <<<", UVM_LOW)

      lc_ctrl_if_rst();  // Restore lc_ctrl_if to Reset Values
      cfg.seq_cfg.disable_flash_init = 1;  // Disable Flash Random Initialisation
      apply_reset();

      // Delay
      cfg.clk_rst_vif.wait_clks($urandom_range(10, 100));

    end

  endtask : body

  virtual task init_data_part();

    // DATA PARTITION

    flash_mp_region_cfg_t mp_regions[flash_ctrl_pkg::MpRegions];
    mubi4_t default_region_read_en;
    mubi4_t default_region_program_en;
    mubi4_t default_region_erase_en;

    // MEMORY PROTECTION REGIONS

    // No Protection Regions
    foreach (mp_regions[i]) begin
      mp_regions[i].en = MuBi4False;
    end

    // Configure the flash based on the given settings
    foreach (mp_regions[i]) begin
      flash_ctrl_mp_region_cfg(i, mp_regions[i]);
    end

    // DEFAULT REGIONS

    default_region_read_en    = MuBi4True;
    default_region_program_en = MuBi4True;
    default_region_erase_en   = MuBi4True;

    // Memory Default Regions
    flash_ctrl_default_region_cfg(.read_en(default_region_read_en),
                                  .program_en(default_region_program_en),
                                  .erase_en(default_region_erase_en));

  endtask : init_data_part

  virtual task init_info_part();

    // INFO REGION

    flash_bank_mp_info_page_cfg_t info_regions[flash_ctrl_reg_pkg::NumInfos0];

    foreach (info_regions[i]) begin
      // Get secret partition cfg from flash_ctrl_pkg
      if ( i inside {1, 2}) begin
        // Copy protection from hw_cfg0.
        info_regions[i] = conv2env_mp_info(flash_ctrl_pkg::CfgAllowRead);
        // Update program and erase control for the test purpose.
        info_regions[i].program_en = MuBi4True;
        info_regions[i].erase_en   = MuBi4True;
      end else begin
        info_regions[i].en         = MuBi4True;
        info_regions[i].read_en    = MuBi4True;
        info_regions[i].program_en = MuBi4True;
        info_regions[i].erase_en   = MuBi4True;
      end
      flash_ctrl_mp_info_page_cfg(.bank(0), .info_part(0), .page(i), .page_cfg(info_regions[i]));
    end

  endtask : init_info_part

  // Tests the connections between the Flash OTP and the Scramble Block in the Flash Ctrl
  virtual task otp_scramble_key_test_connect();

    logic [KeyWidth-1:0] prb_otp_addr_key;
    logic [KeyWidth-1:0] prb_otp_data_key;
    logic [KeyWidth-1:0] prb_otp_addr_rand_key;
    logic [KeyWidth-1:0] prb_otp_data_rand_key;

    // OTP SCRAMBLE KEY TESTS - CONNECTIVITY TEST ONLY

    // OTP Acknowledge and Random Scramble Seeds are Provided by a model in the Base Seq
    // (flash_ctrl_base_vseq), called otp_model()

    `uvm_info(`gfn, "FLASH OTP KEY - Scramble Connectivity Check", UVM_LOW)

    // Probe Internal Scramble Signals
    prb_otp_addr_key = read_key_probe("tb.dut.u_eflash.u_scramble.addr_key_i");
    prb_otp_addr_rand_key = read_key_probe("tb.dut.u_eflash.u_scramble.rand_addr_key_i");
    prb_otp_data_key = read_key_probe("tb.dut.u_eflash.u_scramble.data_key_i");
    prb_otp_data_rand_key = read_key_probe("tb.dut.u_eflash.u_scramble.rand_data_key_i");

    // Compare OTP Keys - Probed vs Expected (For This Test Scenario)
    compare_key_probe("otp_addr_key", prb_otp_addr_key, otp_addr_key);
    compare_key_probe("otp_addr_rand_key", prb_otp_addr_rand_key, otp_addr_rand_key);
    compare_key_probe("otp_data_key", prb_otp_data_key, otp_data_key);
    compare_key_probe("otp_data_rand_key", prb_otp_data_rand_key, otp_data_rand_key);

  endtask : otp_scramble_key_test_connect

  // Function Reads the OTP Key values within the Flash Ctrl, at the Scrambing Module
  virtual function logic [KeyWidth-1:0] read_key_probe(input string dut_prb);
    if (!uvm_hdl_read(dut_prb, read_key_probe))
      `uvm_error(`gfn, $sformatf("Unable to Read from DUT Probe : %s, FAIL", dut_prb))
  endfunction : read_key_probe

  // Task that compares an expected Key with a given key
  virtual task compare_key_probe(input string dut_prb,
                                 input logic [KeyWidth-1:0] key,
                                 input logic [KeyWidth-1:0] expected_key);

    `uvm_info(`gfn, $sformatf("Compare OTP Key, Read : 0x%0x, Expected : 0x%0x", key, expected_key),
              UVM_MEDIUM)

    `DV_CHECK_EQ(key, expected_key, $sformatf(
                 {"Flash OTP Scramble Key Mismatch, Key : %s, Read : ",
                  "0x%0x, Expected : 0x%0x, FAIL"},
                   dut_prb, key, expected_key))

  endtask : compare_key_probe

endclass : flash_ctrl_hw_sec_otp_vseq
