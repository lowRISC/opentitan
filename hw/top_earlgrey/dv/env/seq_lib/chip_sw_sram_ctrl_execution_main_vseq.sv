// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class chip_sw_sram_ctrl_execution_main_vseq extends chip_sw_base_vseq;
  `uvm_object_utils(chip_sw_sram_ctrl_execution_main_vseq)

  `uvm_object_new

  localparam logic [255:0] DEVICE_ID =
      256'hFA53B8058E157CB69F1F413E87242971B6B52A656A1CAB7FEBF21E5BF1F45EDD;
  localparam logic [255:0] MANUF_STATE =
      256'h41389646B3968A3B128F4AF0AFFC1AAC77ADEFF42376E09D523D5C06786AAC34;
  localparam logic [7:0] MUBI8TRUE = prim_mubi_pkg::MuBi8True;
  localparam logic [7:0] MUBI8FALSE = prim_mubi_pkg::MuBi8False;
  localparam logic [7:0] EN_CSRNG_SW_APP_READ = MUBI8FALSE;
  localparam logic [7:0] EN_ENTROPY_SRC_FW_READ = MUBI8FALSE;
  localparam logic [7:0] EN_ENTROPY_SRC_FW_OVER = MUBI8FALSE;


  virtual task do_test(logic [7:0] en_sram_ifetch, bit set_prod_lc);

    apply_reset();

    if (set_prod_lc) begin
      cfg.mem_bkdr_util_h[Otp].otp_write_lc_partition_state(LcStProd);
    end
    cfg.mem_bkdr_util_h[Otp].otp_write_hw_cfg_partition(
        .device_id(DEVICE_ID), .manuf_state(MANUF_STATE), .en_sram_ifetch(en_sram_ifetch),
        .en_csrng_sw_app_read(EN_CSRNG_SW_APP_READ),
        .en_entropy_src_fw_read(EN_ENTROPY_SRC_FW_READ),
        .en_entropy_src_fw_over(EN_ENTROPY_SRC_FW_OVER));

    `DV_WAIT(cfg.sw_test_status_vif.sw_test_status == SwTestStatusInTest)
    `DV_WAIT(cfg.sw_test_status_vif.sw_test_status == SwTestStatusInWfi)
  endtask

  virtual task body();

    super.body();

    // State 0 - SRAM_IFETCH = False, LC_STATE = LcStRma (default).
    do_test(MUBI8FALSE, 0);
    // State 1 - SRAM_IFETCH = True, LC_STATE = LcStRma (default).
    do_test(MUBI8TRUE, 0);
    // State 2 - SRAM_IFETCH = False, LC_STATE = LcStProd.
    do_test(MUBI8FALSE, 1);
    // State 3 - SRAM_IFETCH = True, LC_STATE = LcStProd.
    do_test(MUBI8TRUE, 1);

    override_test_status_and_finish(.passed(1'b 1));

  endtask

endclass
