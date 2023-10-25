// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class chip_sw_sram_ctrl_scrambled_access_vseq extends chip_sw_base_vseq;
  `uvm_object_utils(chip_sw_sram_ctrl_scrambled_access_vseq)

  `uvm_object_new

  // Number of words to write.
  localparam uint BACKDOOR_DATA_WORDS = 16;

  // Offsets in number of words for the locations in SRAM where we will write backdoor data.
  // For retention RAM this can be anywhere except at the base address which is
  // already used in the test for the scramble check.
  // For main SRAM after scrambling the runtime environment will have been trashed so we only need
  // to avoid the location of the scramble buffer. This will have been allocated by the
  // compiler close to the start of the RAM.
  // For both, an offset that is at the midpoint of the SRAM should suffice.
  localparam uint BACKDOOR_RET_OFFSET = (top_earlgrey_pkg::TOP_EARLGREY_SRAM_CTRL_RET_AON_RAM_SIZE_BYTES / 8);
  localparam uint BACKDOOR_MAIN_OFFSET = (top_earlgrey_pkg::TOP_EARLGREY_SRAM_CTRL_MAIN_RAM_SIZE_BYTES / 8);

  localparam string MAIN_INDEX = "0";
  localparam string MAIN_REQ_INDEX = "3";
  localparam string RET_INDEX = "1";
  localparam string RET_REQ_INDEX = "4";

  localparam string SRAM_CTRL_RET_HDL_PATH = "tb.dut.top_earlgrey.u_sram_ctrl_ret_aon";
  localparam string SRAM_CTRL_MAIN_HDL_PATH = "tb.dut.top_earlgrey.u_sram_ctrl_main";
  localparam string OTP_CTRL_KDI_HDL_PATH = "tb.dut.top_earlgrey.u_otp_ctrl.u_otp_ctrl_kdi";

  localparam string KEY_VALID_PATH = ".u_reg_regs.u_status_scr_key_valid.qs[0]";

  localparam string RET_NONCE_PATH = {
    OTP_CTRL_KDI_HDL_PATH, ".sram_otp_key_o[", RET_INDEX, "].nonce"
  };
  localparam string RET_KEY_PATH = {OTP_CTRL_KDI_HDL_PATH, ".sram_otp_key_o[", RET_INDEX, "].key"};
  localparam string RET_ACK_PATH = {OTP_CTRL_KDI_HDL_PATH, ".sram_otp_key_o[", RET_INDEX, "].ack"};
  localparam string RET_REQ_PATH = {OTP_CTRL_KDI_HDL_PATH, ".req[", RET_REQ_INDEX, "]"};

  localparam string MAIN_NONCE_PATH = {
    OTP_CTRL_KDI_HDL_PATH, ".sram_otp_key_o[", MAIN_INDEX, "].nonce"
  };
  localparam string MAIN_KEY_PATH = {
    OTP_CTRL_KDI_HDL_PATH, ".sram_otp_key_o[", MAIN_INDEX, "].key"
  };
  localparam string MAIN_ACK_PATH = {
    OTP_CTRL_KDI_HDL_PATH, ".sram_otp_key_o[", MAIN_INDEX, "].ack"
  };
  localparam string MAIN_REQ_PATH = {OTP_CTRL_KDI_HDL_PATH, ".req[", MAIN_REQ_INDEX, "]"};

  localparam string SRAM_CTRL_RET_SCR_KEY_VALID_PATH = {SRAM_CTRL_RET_HDL_PATH, KEY_VALID_PATH};
  localparam string SRAM_CTRL_MAIN_SCR_KEY_VALID_PATH = {SRAM_CTRL_MAIN_HDL_PATH, KEY_VALID_PATH};

  rand bit [7:0] backdoor_data[];
  constraint backdoor_data_c {backdoor_data.size() == (BACKDOOR_DATA_WORDS * 4);}

  bit [sram_scrambler_pkg::SRAM_BLOCK_WIDTH-1:0] sram_ret_nonce;
  bit [  sram_scrambler_pkg::SRAM_KEY_WIDTH-1:0] sram_ret_key;
  bit [sram_scrambler_pkg::SRAM_BLOCK_WIDTH-1:0] sram_main_nonce;
  bit [  sram_scrambler_pkg::SRAM_KEY_WIDTH-1:0] sram_main_key;

  typedef enum byte {
    PhaseSetup           = 0,
    kTestPhaseMainSram   = 1,
    kTestPhaseRetSram    = 2,
    PhaseDone            = 3
  } test_phases_e;

  virtual task check_hdl_paths();
    int retval;
    retval = uvm_hdl_check_path(RET_NONCE_PATH);
    `DV_CHECK_EQ_FATAL(retval, 1, $sformatf(
                       "Hierarchical path %0s appears to be invalid.", RET_NONCE_PATH))
    retval = uvm_hdl_check_path(RET_KEY_PATH);
    `DV_CHECK_EQ_FATAL(retval, 1, $sformatf(
                       "Hierarchical path %0s appears to be invalid.", RET_KEY_PATH))
    retval = uvm_hdl_check_path(RET_ACK_PATH);
    `DV_CHECK_EQ_FATAL(retval, 1, $sformatf(
                       "Hierarchical path %0s appears to be invalid.", RET_ACK_PATH))
    retval = uvm_hdl_check_path(RET_REQ_PATH);
    `DV_CHECK_EQ_FATAL(retval, 1, $sformatf(
                       "Hierarchical path %0s appears to be invalid.", RET_REQ_PATH))
    retval = uvm_hdl_check_path(MAIN_NONCE_PATH);
    `DV_CHECK_EQ_FATAL(retval, 1, $sformatf(
                       "Hierarchical path %0s appears to be invalid.", MAIN_NONCE_PATH))
    retval = uvm_hdl_check_path(MAIN_KEY_PATH);
    `DV_CHECK_EQ_FATAL(retval, 1, $sformatf(
                       "Hierarchical path %0s appears to be invalid.", MAIN_KEY_PATH))
    retval = uvm_hdl_check_path(MAIN_ACK_PATH);
    `DV_CHECK_EQ_FATAL(retval, 1, $sformatf(
                       "Hierarchical path %0s appears to be invalid.", MAIN_ACK_PATH))
    retval = uvm_hdl_check_path(MAIN_REQ_PATH);
    `DV_CHECK_EQ_FATAL(retval, 1, $sformatf(
                       "Hierarchical path %0s appears to be invalid.", MAIN_REQ_PATH))
    retval = uvm_hdl_check_path(SRAM_CTRL_RET_SCR_KEY_VALID_PATH);
    `DV_CHECK_EQ_FATAL(
        retval, 1, $sformatf(
        "Hierarchical path %0s appears to be invalid.", SRAM_CTRL_RET_SCR_KEY_VALID_PATH))
    retval = uvm_hdl_check_path(SRAM_CTRL_MAIN_SCR_KEY_VALID_PATH);
    `DV_CHECK_EQ_FATAL(
        retval, 1, $sformatf(
        "Hierarchical path %0s appears to be invalid.", SRAM_CTRL_MAIN_SCR_KEY_VALID_PATH))
  endtask

  virtual task get_ret_keys();
    int retval;
    int req;
    int ack;
    forever begin
      retval = uvm_hdl_read(RET_REQ_PATH, req);
      `DV_CHECK_EQ(retval, 1, $sformatf("uvm_hdl_read failed for %0s", RET_REQ_PATH))
      retval = uvm_hdl_read(RET_ACK_PATH, ack);
      `DV_CHECK_EQ(retval, 1, $sformatf("uvm_hdl_read failed for %0s", RET_ACK_PATH))
      if (req == 1 && ack == 1) begin
        retval = uvm_hdl_read(RET_NONCE_PATH, sram_ret_nonce);
        `DV_CHECK_EQ(retval, 1, $sformatf("uvm_hdl_read failed for %0s", RET_NONCE_PATH))
        retval = uvm_hdl_read(RET_KEY_PATH, sram_ret_key);
        `DV_CHECK_EQ(retval, 1, $sformatf("uvm_hdl_read failed for %0s", RET_KEY_PATH))
      end
      // The sampling cycle should be faster then otp clock.
      #1ns;
    end
  endtask

  virtual task get_main_keys();
    int retval;
    int req;
    int ack;
    forever begin
      retval = uvm_hdl_read(MAIN_REQ_PATH, req);
      `DV_CHECK_EQ(retval, 1, $sformatf("uvm_hdl_read failed for %0s", MAIN_REQ_PATH))
      retval = uvm_hdl_read(MAIN_ACK_PATH, ack);
      `DV_CHECK_EQ(retval, 1, $sformatf("uvm_hdl_read failed for %0s", MAIN_ACK_PATH))
      if (req == 1 && ack == 1) begin
        retval = uvm_hdl_read(MAIN_NONCE_PATH, sram_main_nonce);
        `DV_CHECK_EQ(retval, 1, $sformatf("uvm_hdl_read failed for %0s", MAIN_NONCE_PATH))
        retval = uvm_hdl_read(MAIN_KEY_PATH, sram_main_key);
        `DV_CHECK_EQ(retval, 1, $sformatf("uvm_hdl_read failed for %0s", MAIN_KEY_PATH))
      end
      // The sampling cycle should be fater then otp clock.
      #1ns;
    end
  endtask

  virtual task ret_backdoor_write(int addr);
    int retval;
    bit scr_key_valid;
    int offset = addr - top_earlgrey_pkg::TOP_EARLGREY_SRAM_CTRL_RET_AON_RAM_BASE_ADDR;
    forever begin
      retval = uvm_hdl_read(SRAM_CTRL_RET_SCR_KEY_VALID_PATH, scr_key_valid);
      `DV_CHECK_EQ(retval, 1, $sformatf(
                   "uvm_hdl_read failed for %0s", SRAM_CTRL_RET_SCR_KEY_VALID_PATH))
      // Wait for sram_ctrl.STATUS.SCR_KEY_VALID.
      if (scr_key_valid == 1) begin
        `uvm_info(`gfn, $sformatf("ret_backdoor_write start %x", offset), UVM_LOW)
        // Write the data to a known offset in the SRAM. The random byte data
        // is used little-endian.
        for (int i = 0; i < BACKDOOR_DATA_WORDS; i++) begin
         ret_sram_bkdr_write32(offset + (i * 4), {
                                backdoor_data[(i*4)+3],
                                backdoor_data[(i*4)+2],
                                backdoor_data[(i*4)+1],
                                backdoor_data[(i*4)+0]
                                }, sram_ret_key, sram_ret_nonce);
        end
        break;
      end
      #1ns;
    end
  endtask

  virtual task main_backdoor_write(int addr);
    int retval;
    bit scr_key_valid;
    int offset = addr - top_earlgrey_pkg::TOP_EARLGREY_SRAM_CTRL_MAIN_RAM_BASE_ADDR;
    forever begin
      retval = uvm_hdl_read(SRAM_CTRL_MAIN_SCR_KEY_VALID_PATH, scr_key_valid);
      `DV_CHECK_EQ(retval, 1, $sformatf(
                   "uvm_hdl_read failed for %0s", SRAM_CTRL_MAIN_SCR_KEY_VALID_PATH))
      // Wait for sram_ctrl.STATUS.SCR_KEY_VALID.
      if (scr_key_valid == 1) begin
        `uvm_info(`gfn, $sformatf("main_backdoor_write start %x", offset), UVM_LOW)
        // Write the data to a known offset in the SRAM. The random byte data
        // is used little-endian.
        for (int i = 0; i < BACKDOOR_DATA_WORDS; i++) begin
          main_sram_bkdr_write32(offset + (i * 4), {
                                 backdoor_data[(i*4)+3],
                                 backdoor_data[(i*4)+2],
                                 backdoor_data[(i*4)+1],
                                 backdoor_data[(i*4)+0]
                                 }, sram_main_key, sram_main_nonce);
        end
        break;
      end
      #1ns;
    end
  endtask

  virtual task cpu_init();
    super.cpu_init();
    // Init SRAM to avoid the software reading X after scrambling.
    for (int ram_idx = 0; ram_idx < cfg.num_ram_ret_tiles; ram_idx++) begin
      cfg.mem_bkdr_util_h[chip_mem_e'(RamRet0 + ram_idx)].set_mem();
    end
    for (int ram_idx = 0; ram_idx < cfg.num_ram_main_tiles; ram_idx++) begin
      cfg.mem_bkdr_util_h[chip_mem_e'(RamMain0 + ram_idx)].set_mem();
    end
  endtask: cpu_init

  virtual task sync_with_sw(input test_phases_e phase);
    `DV_WAIT(cfg.sw_test_status_vif.sw_test_status == SwTestStatusInWfi)
    `DV_WAIT(cfg.sw_test_status_vif.sw_test_status == SwTestStatusInTest)

     sw_symbol_backdoor_overwrite("kTestPhase", {<<8{phase}});
  endtask:sync_with_sw

  virtual task body();
    string mem_sel;
    int main_sram_offset;
    int ret_sram_offset ;
    super.body();

    // Disable SRAM data integrity checks.
    cfg.disable_d_user_data_intg_check_for_passthru_mem = 1;
    cfg.en_scb_mem_chk = 0;

    check_hdl_paths();

    sw_symbol_backdoor_overwrite("kBackdoorExpectedBytes", backdoor_data);

    `DV_WAIT(cfg.sw_logger_vif.printed_format == "RET_SRAM addr: %0h MAIN_SRAM addr: %0h");
    ret_sram_offset = int'(cfg.sw_logger_vif.printed_arg[0]);
    main_sram_offset = int'(cfg.sw_logger_vif.printed_arg[1]);
    sync_with_sw(kTestPhaseMainSram);

    `uvm_info(`gfn, $sformatf("Testing main sram addr: %x", main_sram_offset), UVM_LOW);
    fork
      get_main_keys();
      main_backdoor_write(main_sram_offset);
    join_none

    `DV_WAIT(cfg.sw_logger_vif.printed_format == "RET_SRAM addr: %0h MAIN_SRAM addr: %0h");
    ret_sram_offset = int'(cfg.sw_logger_vif.printed_arg[0]);
    main_sram_offset = int'(cfg.sw_logger_vif.printed_arg[1]);
    sync_with_sw(kTestPhaseRetSram);

    `uvm_info(`gfn, $sformatf("Testing ret sram addr: %x", ret_sram_offset), UVM_LOW);
    fork
      get_ret_keys();
      ret_backdoor_write(ret_sram_offset);
    join_none

  endtask

endclass : chip_sw_sram_ctrl_scrambled_access_vseq
