// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class chip_sw_flash_ctrl_lc_rw_en_vseq extends chip_sw_base_vseq;
  `uvm_object_utils(chip_sw_flash_ctrl_lc_rw_en_vseq)

  `uvm_object_new

  localparam string FLASH_CTRL_HDL_PATH = "tb.dut.top_earlgrey.u_flash_ctrl";
  localparam string RW_EN_PATHS[5] = '{
      {FLASH_CTRL_HDL_PATH, ".lc_creator_seed_sw_rw_en_i"},
      {FLASH_CTRL_HDL_PATH, ".lc_owner_seed_sw_rw_en_i"},
      {FLASH_CTRL_HDL_PATH, ".lc_iso_part_sw_wr_en_i"},
      {FLASH_CTRL_HDL_PATH, ".lc_iso_part_sw_rd_en_i"},
      {FLASH_CTRL_HDL_PATH, ".lc_seed_hw_rd_en_i"}
  };

  virtual task dut_init(string reset_kind = "HARD");
    super.dut_init(reset_kind);
    // Override the LC partition to TestLocked state.
    cfg.mem_bkdr_util_h[Otp].otp_write_lc_partition_state(LcStTestLocked2);
  endtask

  virtual function lc_ctrl_pkg::lc_tx_t get_rw_en_signals(int rw_en_index);
    uvm_hdl_data_t read_value;
    `DV_CHECK_EQ_FATAL(uvm_hdl_check_path(RW_EN_PATHS[rw_en_index]), 1, $sformatf(
                       "Hierarchical path %0s appears to be invalid.", RW_EN_PATHS[rw_en_index]))
    `DV_CHECK_EQ_FATAL(uvm_hdl_read(RW_EN_PATHS[rw_en_index], read_value), 1, $sformatf(
                       "uvm_hdl_read failed for %0s", RW_EN_PATHS[rw_en_index]))
    return lc_ctrl_pkg::lc_tx_t'(read_value);
  endfunction

  virtual task body();

    super.body();

    // Starting LC state is TestLocked2. This state disables
    // CPU execution so we check the values by directly reading
    // the signals from the flash_ctrl inputs.

    for (int i = 0; i < 5; i++) begin
      `DV_CHECK_EQ_FATAL(get_rw_en_signals(i), lc_ctrl_pkg::Off,
                         "Mismatch for expected rw_en value [%0d] in TestLocked2 LC state", i)
    end

    // LC state changed to Dev. and reset, CPU will now be enabled.

    cfg.mem_bkdr_util_h[Otp].otp_write_lc_partition_state(LcStDev);
    apply_reset();

    `DV_WAIT(cfg.sw_test_status_vif.sw_test_status == SwTestStatusInTest, 50_000_000)
    `DV_WAIT(cfg.sw_test_status_vif.sw_test_status == SwTestStatusInWfi)

    // LC state changed to Prod.

    cfg.mem_bkdr_util_h[Otp].otp_write_lc_partition_state(LcStProd);
    apply_reset();

    `DV_WAIT(cfg.sw_test_status_vif.sw_test_status == SwTestStatusInTest)
    `DV_WAIT(cfg.sw_test_status_vif.sw_test_status == SwTestStatusInWfi)

    // LC state changed to Scrap. CPU not enabled so do the checks directly.

    cfg.mem_bkdr_util_h[Otp].otp_write_lc_partition_state(LcStScrap);
    apply_reset();

    for (int i = 0; i < 5; i++) begin
      `DV_CHECK_EQ_FATAL(get_rw_en_signals(i), lc_ctrl_pkg::Off,
                         "Mismatch for expected rw_en value [%0d] in Scrap LC state", i)
    end

    override_test_status_and_finish(.passed(1'b 1));

  endtask

endclass
