// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// This class is used for the testes `chip_sw_entropy_src_fuse_en_fw_read_test` and
// `chip_sw_csrng_fuse_en_sw_app_read_test`. Please refer to the testplan for more
 // details regarding the OTP initialization values.
class chip_sw_entropy_src_fuse_vseq extends chip_sw_base_vseq;
  `uvm_object_utils(chip_sw_entropy_src_fuse_vseq)

  `uvm_object_new

  localparam logic [255:0] DEVICE_ID =
      256'hFA53B8058E157CB69F1F413E87242971B6B52A656A1CAB7FEBF21E5BF1F45EDD;
  localparam logic [255:0] MANUF_STATE =
      256'h41389646B3968A3B128F4AF0AFFC1AAC77ADEFF42376E09D523D5C06786AAC34;
  localparam logic [7:0] MUBI8TRUE = prim_mubi_pkg::MuBi8True;
  localparam logic [7:0] MUBI8FALSE = prim_mubi_pkg::MuBi8False;

  virtual task dut_init(string reset_kind = "HARD");
    super.dut_init(reset_kind);

    cfg.mem_bkdr_util_h[Otp].otp_write_hw_cfg0_partition(
      .device_id(DEVICE_ID), .manuf_state(MANUF_STATE));
    cfg.mem_bkdr_util_h[Otp].otp_write_hw_cfg1_partition(
      .en_sram_ifetch(MUBI8FALSE), .en_csrng_sw_app_read(MUBI8TRUE),
      .dis_rv_dm_late_debug(MUBI8TRUE));
  endtask

  virtual task body();
    super.body();

    forever begin
      `DV_WAIT(cfg.sw_logger_vif.printed_log == "Software resetting!",
        // 20ms
        20_000_000)

      if (cfg.sw_logger_vif.printed_log == "Software resetting!") begin
        cfg.mem_bkdr_util_h[Otp].otp_write_hw_cfg0_partition(
          .device_id(DEVICE_ID), .manuf_state(MANUF_STATE));
        cfg.mem_bkdr_util_h[Otp].otp_write_hw_cfg1_partition(
          .en_sram_ifetch(MUBI8FALSE), .en_csrng_sw_app_read(MUBI8FALSE),
          .dis_rv_dm_late_debug(MUBI8TRUE));
          break;
      end
    end
  endtask
endclass : chip_sw_entropy_src_fuse_vseq
