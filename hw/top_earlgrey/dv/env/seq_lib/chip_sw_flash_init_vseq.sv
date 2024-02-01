// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class chip_sw_flash_init_vseq extends chip_sw_base_vseq;
  `uvm_object_utils(chip_sw_flash_init_vseq)

  `uvm_object_new

  localparam string FLASH_DATA_KEY_PATH =
    "tb.dut.top_earlgrey.u_flash_ctrl.u_flash_hw_if.data_key_o";
  localparam string FLASH_ADDR_KEY_PATH =
    "tb.dut.top_earlgrey.u_flash_ctrl.u_flash_hw_if.addr_key_o";
  localparam string FLASH_INIT_BUSY_PATH =
    "tb.dut.top_earlgrey.u_flash_ctrl.u_flash_hw_if.init_busy_o";
  localparam string KEYMGR_SEEDS_PATH = "tb.dut.top_earlgrey.u_flash_ctrl.u_flash_hw_if.seeds_o";
  localparam string FLASH_LC_SEED_HW_RD_EN_PATH =
    "tb.dut.top_earlgrey.u_flash_ctrl.lc_seed_hw_rd_en_i";

  localparam string SRAM_CTRL_RET_HDL_PATH =
    "tb.dut.top_earlgrey.u_sram_ctrl_ret_aon.u_prim_ram_1p_scr";
  localparam string SRAM_CTRL_RET_NONCE_PATH = {SRAM_CTRL_RET_HDL_PATH, ".nonce_i"};
  localparam string SRAM_CTRL_RET_KEY_PATH = {SRAM_CTRL_RET_HDL_PATH, ".key_i"};

  localparam uint KeyWidthAddrBits = otp_ctrl_reg_pkg::FlashAddrKeySeedSize * 8;
  localparam uint KeyWidthAddrBytes = KeyWidthAddrBits / 8;
  localparam uint KeyWidthDataBits = otp_ctrl_reg_pkg::FlashDataKeySeedSize * 8;
  localparam uint KeyWidthDataBytes = KeyWidthDataBits / 8;
  localparam uint KeyWidthSramBits = otp_ctrl_reg_pkg::SramDataKeySeedSize * 8;
  localparam uint KeyWidthSramBytes = KeyWidthSramBits / 8;

  localparam uint SEED_WIDTH = flash_ctrl_pkg::SeedWidth;
  localparam uint FLASH_PAGE_SIZE_BYTES = flash_ctrl_reg_pkg::BytesPerPage;
  localparam uint FLASH_PAGES_PER_BANK = flash_ctrl_reg_pkg::RegPagesPerBank;
  localparam uint CREATOR_SECRET_PAGE_ID = flash_ctrl_pkg::CreatorInfoPage;
  localparam uint OWNER_SECRET_PAGE_ID = flash_ctrl_pkg::OwnerInfoPage;
  localparam uint ISO_PART_PAGE_ID = flash_ctrl_pkg::IsolatedInfoPage;

  localparam uint NUM_TEST_WORDS = 16;
  typedef enum {
    UnscrambledTest[0:2],
    ScrambledTest[0:1],
    BackdoorTest[0:1],
    KeyMgrPrep,
    KeyMgrTest[0:1],
    LastPhase
  } test_phases_e;

  bit [sram_scrambler_pkg::SRAM_BLOCK_WIDTH-1:0] sram_ret_nonce;
  bit [sram_scrambler_pkg::SRAM_KEY_WIDTH-1:0] sram_ret_key;

  rand bit [7:0] secret_flash_addr_key[KeyWidthAddrBytes];
  rand bit [7:0] secret_flash_data_key[KeyWidthDataBytes];
  rand bit [7:0] secret_sram_key[KeyWidthSramBytes];

  rand bit [31:0] creator_secret_data[NUM_TEST_WORDS];
  rand bit [31:0] owner_secret_data[NUM_TEST_WORDS];
  rand bit [31:0] iso_part_data[NUM_TEST_WORDS];
  rand bit [31:0] bank0_page0_data[NUM_TEST_WORDS];
  rand bit [31:0] bank1_page0_data[NUM_TEST_WORDS];
  rand bit [otp_ctrl_reg_pkg::CreatorRootKeyShare0Size*8-1:0] root_key0;
  rand bit [otp_ctrl_reg_pkg::CreatorRootKeyShare0Size*8-1:0] root_key1;
  bit [FlashKeyWidth-1:0] flash_data_key;
  bit [FlashKeyWidth-1:0] flash_addr_key;

  bit write_scrambled;
  bit do_keymgr_check;

  event init_done_event;

  typedef enum int {
    DV_EXP_RMA,
    DV_EXP_PROD
  } exp_lc_st_e;

  exp_lc_st_e exp_lc_st;
  virtual task ret_backdoor_data_write();
    `DV_CHECK(uvm_hdl_read(SRAM_CTRL_RET_NONCE_PATH, sram_ret_nonce));
    `DV_CHECK(uvm_hdl_read(SRAM_CTRL_RET_KEY_PATH, sram_ret_key));
    for (int i = 0; i < NUM_TEST_WORDS; i++) begin
      ret_sram_bkdr_write32((i * 4), creator_secret_data[i], sram_ret_key, sram_ret_nonce);
      ret_sram_bkdr_write32((NUM_TEST_WORDS * 4) + (i * 4), owner_secret_data[i], sram_ret_key,
                            sram_ret_nonce);
      ret_sram_bkdr_write32((NUM_TEST_WORDS * 8) + (i * 4), iso_part_data[i], sram_ret_key,
                            sram_ret_nonce);
      ret_sram_bkdr_write32((NUM_TEST_WORDS * 12) + (i * 4), bank0_page0_data[i], sram_ret_key,
                            sram_ret_nonce);
      ret_sram_bkdr_write32((NUM_TEST_WORDS * 16) + (i * 4), bank1_page0_data[i], sram_ret_key,
                            sram_ret_nonce);
    end
  endtask

  virtual task randomize_data();
    `DV_CHECK_STD_RANDOMIZE_FATAL(creator_secret_data)
    `DV_CHECK_STD_RANDOMIZE_FATAL(owner_secret_data)
    `DV_CHECK_STD_RANDOMIZE_FATAL(iso_part_data)
    `DV_CHECK_STD_RANDOMIZE_FATAL(bank0_page0_data)
    `DV_CHECK_STD_RANDOMIZE_FATAL(bank1_page0_data)
    `DV_CHECK_STD_RANDOMIZE_FATAL(root_key0)
    `DV_CHECK_STD_RANDOMIZE_FATAL(root_key1)
  endtask

  virtual function bit [KeyWidthAddrBits-1:0] get_flash_otp_key(
      bit [7:0] key_in[KeyWidthAddrBytes]);
    bit [kmac_pkg::AppDigestW-1:0] digest_bits;
    bit [7:0] dpi_digest[kmac_pkg::AppDigestW/8];

    digestpp_dpi_pkg::c_dpi_cshake128(key_in, "", "FLASH_CTRL", KeyWidthAddrBytes,
                                      kmac_pkg::AppDigestW / 8, dpi_digest);
    digest_bits = {<<byte{dpi_digest}};
    return (digest_bits[KeyWidthAddrBits-1:0]);
  endfunction

  virtual function bit [KeyWidthSramBits-1:0] get_sram_otp_key(
      bit [7:0] key_in[KeyWidthSramBytes]);
    bit [kmac_pkg::AppDigestW-1:0] digest_bits;
    bit [7:0] dpi_digest[kmac_pkg::AppDigestW/8];

    digestpp_dpi_pkg::c_dpi_cshake128(key_in, "", "SRAM_CTRL", KeyWidthSramBytes,
                                      kmac_pkg::AppDigestW / 8, dpi_digest);
    digest_bits = {<<byte{dpi_digest}};
    return (digest_bits[KeyWidthSramBits-1:0]);
  endfunction

  virtual task randomize_keys();
    `DV_CHECK_STD_RANDOMIZE_FATAL(secret_flash_addr_key)
    `DV_CHECK_STD_RANDOMIZE_FATAL(secret_flash_data_key)
    cfg.mem_bkdr_util_h[Otp].otp_write_secret1_partition(
        .flash_addr_key_seed(get_flash_otp_key(secret_flash_addr_key)),
        .flash_data_key_seed(get_flash_otp_key(secret_flash_data_key)),
        .sram_data_key_seed(get_sram_otp_key(secret_sram_key)));
  endtask

  virtual task calculate_and_write_scrambled();
    bit [15:0] base_addr_bytes;
    for (int i = 0; i < NUM_TEST_WORDS / 2; i++) begin
      base_addr_bytes = 16'h0;
      cfg.mem_bkdr_util_h[FlashBank0Data].flash_write_scrambled(
          {bank0_page0_data[(i*2)+1], bank0_page0_data[i*2]}, base_addr_bytes + (i * 8),
          flash_addr_key, flash_data_key);
      base_addr_bytes = FLASH_PAGE_SIZE_BYTES * FLASH_PAGES_PER_BANK;
      cfg.mem_bkdr_util_h[FlashBank1Data].flash_write_scrambled(
          {bank1_page0_data[(i*2)+1], bank1_page0_data[i*2]}, base_addr_bytes + (i * 8),
          flash_addr_key, flash_data_key);
      base_addr_bytes = FLASH_PAGE_SIZE_BYTES * CREATOR_SECRET_PAGE_ID;
      cfg.mem_bkdr_util_h[FlashBank0Info].flash_write_scrambled(
          {creator_secret_data[(i*2)+1], creator_secret_data[i*2]}, base_addr_bytes + (i * 8),
          flash_addr_key, flash_data_key);
      base_addr_bytes = FLASH_PAGE_SIZE_BYTES * OWNER_SECRET_PAGE_ID;
      cfg.mem_bkdr_util_h[FlashBank0Info].flash_write_scrambled(
          {owner_secret_data[(i*2)+1], owner_secret_data[i*2]}, base_addr_bytes + (i * 8),
          flash_addr_key, flash_data_key);
      base_addr_bytes = FLASH_PAGE_SIZE_BYTES * ISO_PART_PAGE_ID;
      cfg.mem_bkdr_util_h[FlashBank0Info].flash_write_scrambled(
          {iso_part_data[(i*2)+1], iso_part_data[i*2]}, base_addr_bytes + (i * 8), flash_addr_key,
          flash_data_key);
    end
  endtask

  virtual task check_hdl_paths();
    int retval;
    retval = uvm_hdl_check_path(FLASH_DATA_KEY_PATH);
    `DV_CHECK_EQ_FATAL(retval, 1, $sformatf(
                       "Hierarchical path %0s appears to be invalid.", FLASH_DATA_KEY_PATH))
    retval = uvm_hdl_check_path(FLASH_ADDR_KEY_PATH);
    `DV_CHECK_EQ_FATAL(retval, 1, $sformatf(
                       "Hierarchical path %0s appears to be invalid.", FLASH_ADDR_KEY_PATH))
    retval = uvm_hdl_check_path(FLASH_INIT_BUSY_PATH);
    `DV_CHECK_EQ_FATAL(retval, 1, $sformatf(
                       "Hierarchical path %0s appears to be invalid.", FLASH_INIT_BUSY_PATH))
    retval = uvm_hdl_check_path(KEYMGR_SEEDS_PATH);
    `DV_CHECK_EQ_FATAL(retval, 1, $sformatf(
                       "Hierarchical path %0s appears to be invalid.", KEYMGR_SEEDS_PATH))
    retval = uvm_hdl_check_path(FLASH_LC_SEED_HW_RD_EN_PATH);
    `DV_CHECK_EQ_FATAL(retval, 1, $sformatf(
                       "Hierarchical path %0s appears to be invalid.", FLASH_LC_SEED_HW_RD_EN_PATH))
    retval = uvm_hdl_check_path(SRAM_CTRL_RET_NONCE_PATH);
    `DV_CHECK_EQ_FATAL(retval, 1, $sformatf(
                       "Hierarchical path %0s appears to be invalid.", SRAM_CTRL_RET_NONCE_PATH))
    retval = uvm_hdl_check_path(SRAM_CTRL_RET_KEY_PATH);
    `DV_CHECK_EQ_FATAL(retval, 1, $sformatf(
                       "Hierarchical path %0s appears to be invalid.", SRAM_CTRL_RET_KEY_PATH))
  endtask

  virtual task wait_init_done();
    int retval;
    bit init_busy;
    bit init_busy_last_value;
    forever begin
      init_busy_last_value = init_busy;
      retval = uvm_hdl_read(FLASH_INIT_BUSY_PATH, init_busy);
      `DV_CHECK_EQ(retval, 1, $sformatf("uvm_hdl_read failed for %0s", FLASH_INIT_BUSY_PATH))
      if (init_busy == 0 && init_busy_last_value == 1) begin
        ->init_done_event;
      end
      // Use top level clock to advance time between samples.
      cfg.clk_rst_vif.wait_clks(1);
    end
  endtask

  virtual task get_keys();
    int retval;
    forever begin
      @(init_done_event);
      if (write_scrambled == 1) begin
        retval = uvm_hdl_read(FLASH_DATA_KEY_PATH, flash_data_key);
        `DV_CHECK_EQ(retval, 1, $sformatf("uvm_hdl_read failed for %0s", FLASH_DATA_KEY_PATH))
        retval = uvm_hdl_read(FLASH_ADDR_KEY_PATH, flash_addr_key);
        `DV_CHECK_EQ(retval, 1, $sformatf("uvm_hdl_read failed for %0s", FLASH_ADDR_KEY_PATH))
        calculate_and_write_scrambled();
      end
    end
  endtask

  virtual task check_keymgr_seeds();
    int retval;
    bit [(SEED_WIDTH*2)-1:0] seeds;
    bit [SEED_WIDTH-1:0] owner_seed;
    bit [SEED_WIDTH-1:0] creator_seed;
    bit [(SEED_WIDTH*2)-1:0] expected_owner_seed;
    bit [(SEED_WIDTH*2)-1:0] expected_creator_seed;
    bit [lc_ctrl_pkg::TxWidth-1:0] lc_seed_hw_rd_en;
    bit [(DecLcStateNumRep*DecLcStateWidth)-1:0] lc_state;
    dec_lc_state_e dec_lc_state;
    forever begin
      @(init_done_event);
      if (do_keymgr_check == 1) begin
        expected_owner_seed = {<<32{owner_secret_data}};
        expected_creator_seed = {<<32{creator_secret_data}};
        retval = uvm_hdl_read(FLASH_LC_SEED_HW_RD_EN_PATH, lc_seed_hw_rd_en);
        `DV_CHECK_EQ(retval, 1, $sformatf("uvm_hdl_read failed for %0s", FLASH_LC_SEED_HW_RD_EN_PATH
                     ))
        retval = uvm_hdl_read(KEYMGR_SEEDS_PATH, seeds);
        `DV_CHECK_EQ(retval, 1, $sformatf("uvm_hdl_read failed for %0s", KEYMGR_SEEDS_PATH))
        owner_seed   = seeds[(SEED_WIDTH*flash_ctrl_pkg::OwnerSeedIdx)+:SEED_WIDTH];
        creator_seed = seeds[(SEED_WIDTH*flash_ctrl_pkg::CreatorSeedIdx)+:SEED_WIDTH];

        // Check 'lc_seed_hw_rd_en'
        // This can be set to 'on' only if
        // 1. lc_state = RMA or
        // 2. otp.secret0_digest != 0 && otp.secret2_digest != 0.
        //    and lc state should be one of {DEV, PROD, PROD_END}
        `uvm_info("SEQ", $sformatf("EXP LC STATE: %s", exp_lc_st.name), UVM_MEDIUM)

        if (exp_lc_st == DV_EXP_RMA) begin
          `DV_CHECK(lc_seed_hw_rd_en, lc_ctrl_pkg::On)
        end else begin
          bit [63:0] secret0_digest, secret2_digest;
          secret0_digest = {csr_peek(ral.otp_ctrl_core.secret0_digest[1]),
                            csr_peek(ral.otp_ctrl_core.secret0_digest[0])};
          secret2_digest = {csr_peek(ral.otp_ctrl_core.secret2_digest[1]),
                            csr_peek(ral.otp_ctrl_core.secret2_digest[0])};
          `uvm_info("SEQ", $sformatf("read secret digest:  digest0:0x%16x  digest2:0x%16x",
                                     secret0_digest, secret2_digest), UVM_MEDIUM)
          if (secret0_digest == 0 || secret2_digest == 0) begin
            `DV_CHECK_NE(lc_seed_hw_rd_en, lc_ctrl_pkg::On)
          end else begin
            `DV_CHECK_EQ(lc_seed_hw_rd_en, lc_ctrl_pkg::On)
          end
        end

        // If 'lc_seed_hw_rd_en' is off, creator/owner seed cannot be updated and
        // retains the default value.
        // Make sure your bus is the right size cause
        // full 64bit bus might contain x's.
        if (lc_seed_hw_rd_en == lc_ctrl_pkg::Off) begin
          `DV_CHECK_EQ(creator_seed,
              top_earlgrey_rnd_cnst_pkg::RndCnstFlashCtrlAllSeeds[SEED_WIDTH-1:0]);
          `DV_CHECK_EQ(owner_seed,
              top_earlgrey_rnd_cnst_pkg::RndCnstFlashCtrlAllSeeds[SEED_WIDTH +: SEED_WIDTH]);
        end else begin
          `DV_CHECK_EQ(creator_seed, expected_creator_seed[SEED_WIDTH-1:0]);
          `DV_CHECK_EQ(owner_seed, expected_owner_seed[SEED_WIDTH-1:0]);
        end
      end
    end
  endtask

  virtual task body();
    bit [7:0] array_data[1];
    bit random_data = 0;
    super.body();
    check_hdl_paths();

    cfg.disable_d_user_data_intg_check_for_passthru_mem = 1;
    cfg.en_scb_mem_chk = 0;
    // Write randomly generated data to retention SRAM for use in SW.
    ret_backdoor_data_write();

    // Fork the tasks for monitoring the key updates and
    // checking the keymgr seed update where applicable.
    fork
      wait_init_done();
      get_keys();
      check_keymgr_seeds();
    join_none

    // Allow most test phases to write seed partition, but do not allow hardware to read
    cfg.mem_bkdr_util_h[Otp].otp_write_lc_partition_state(LcStProd);
    cfg.mem_bkdr_util_h[Otp].write64(otp_ctrl_reg_pkg::Secret2DigestOffset, 0);

    // Looping through all test phases.
    for (int current_phase = UnscrambledTest0; current_phase <= LastPhase; current_phase++) begin
      // Backdoor overwrite the SW variable for the test phase.
      array_data[0] = current_phase;
      sw_symbol_backdoor_overwrite("kTestPhase", array_data, SwTypeRom);
      `uvm_info(`gfn, $sformatf("Testing %d", current_phase), UVM_LOW)

      if (current_phase < LastPhase) begin
        do_keymgr_check = 0;
        write_scrambled = 0;
        random_data = 0;
        case (current_phase)
          UnscrambledTest0, UnscrambledTest1, UnscrambledTest2,
          ScrambledTest0, ScrambledTest1: begin
            random_data = 1;
          end

          BackdoorTest0, BackdoorTest1: begin
            write_scrambled = 1;
            random_data = 1;
          end

          KeyMgrPrep: begin
            write_scrambled = 1;
          end

          KeyMgrTest0: begin
            do_keymgr_check = 1;
            `uvm_info(`gfn, $sformatf("Lock OTP secret2 partition and enable seed reading"),
                      UVM_LOW)

            // The actual data is irrelevant as long as the partition becomes locked.
            cfg.mem_bkdr_util_h[Otp].otp_write_secret2_partition(
              .rma_unlock_token('0), .creator_root_key0('0), .creator_root_key1('0));
          end

          KeyMgrTest1: begin
            `uvm_info(`gfn, $sformatf("Zero secret2 partition and disable seed reading"),
                      UVM_LOW)
            cfg.mem_bkdr_util_h[Otp].write64(otp_ctrl_reg_pkg::Secret2DigestOffset, 0);
            do_keymgr_check = 1;
          end

          default:;

        endcase // case (current_phase)

        // Wait for the test to start and enter the WFI state,
        `uvm_info(`gfn, $sformatf("Wating to be in test"), UVM_MEDIUM)
        `DV_WAIT(cfg.sw_test_status_vif.sw_test_status == SwTestStatusInTest)
        `uvm_info(`gfn, $sformatf("Wating to be see WFI"), UVM_MEDIUM)
        `DV_WAIT(cfg.sw_test_status_vif.sw_test_status == SwTestStatusInWfi)

        // Randomize the data and keys for the next test phase.
        if (random_data) begin
          randomize_data();
          randomize_keys();
          ret_backdoor_data_write();
        end

        apply_reset();
        cfg.clk_rst_vif.wait_clks(1000);
      end else begin
        // final phase cleanup.
        disable fork;
      end
    end
  endtask

endclass
