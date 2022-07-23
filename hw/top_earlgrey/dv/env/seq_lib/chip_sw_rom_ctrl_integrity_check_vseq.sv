// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class chip_sw_rom_ctrl_integrity_check_vseq extends chip_sw_base_vseq;
  `uvm_object_utils(chip_sw_rom_ctrl_integrity_check_vseq)

  `uvm_object_new

  localparam uint TimeoutNs = 1_000_000;  // 1ms

  // Overwrite the last expected digest word in the ROM which is
  // sufficient to cause an integrity failure.
  virtual task rom_digest_overwrite();
    int retval;
    string rom_nonce_hdl_path = "tb.dut.top_earlgrey.u_rom_ctrl.RndCnstScrNonce";
    bit [sram_scrambler_pkg::SRAM_BLOCK_WIDTH-1:0] rom_nonce;
    uint32_t addr = (cfg.mem_bkdr_util_h[Rom].get_depth() * 4) - 4;  // digest at last ROM location.

    // Get ROM nonce directly from rom_ctrl instance rather
    // than using a hard coded value.
    retval = uvm_hdl_check_path(rom_nonce_hdl_path);
    `DV_CHECK_EQ_FATAL(retval, 1, $sformatf(
                       "Hierarchical path %0s appears to be invalid.", rom_nonce_hdl_path))
    retval = uvm_hdl_read(rom_nonce_hdl_path, rom_nonce);
    `DV_CHECK_EQ(retval, 1, $sformatf("uvm_hdl_read failed for %0s", rom_nonce_hdl_path))

    // Write to ROM at last digest location with random data (which can be unscrambled).
    cfg.mem_bkdr_util_h[Rom].rom_encrypt_write32_integ(
        addr, $urandom(), sram_scrambler_pkg::SRAM_KEY_WIDTH'('b0), rom_nonce, 1'b0);
  endtask

  virtual task test_state_monitor();
    // wait for the test to boot and issue the WFI status
    `DV_WAIT(cfg.sw_test_status_vif.sw_test_status == SwTestStatusInTest)
    `DV_WAIT(cfg.sw_test_status_vif.sw_test_status == SwTestStatusInWfi)

    // update the lc state to a production state and do a reset
    cfg.mem_bkdr_util_h[Otp].otp_write_lc_partition_state(lc_ctrl_state_pkg::LcStProd);
    apply_reset();

    // At this point, a successful boot would be an error. We will start a
    // parallel timeout thread which will be expected to complete as the boot
    // process should be locked up.
    fork
      begin
        `DV_WAIT(cfg.sw_test_status_vif.sw_test_status == SwTestStatusInBootRom)
        `uvm_error(`gfn, "Unexpected successful boot in PROD LC_STATE.")
      end
      begin
        #(TimeoutNs * 1ns);
        cfg.sw_test_status_vif.sw_test_status = SwTestStatusPassed;
        cfg.sw_test_status_vif.sw_test_done   = 1'b1;
      end
    join_any
    disable fork;
  endtask

  // The test will do the standard setup and then overwrite the
  // expected ROM digest via the backdoor which is a condition
  // that when in non production LC state (the default) should still boot.
  // We then launch a task to monitor the test state and make changes
  // following the successful boot to change the lc state to a production
  // state then do a reset after which it should be expected not to boot.
  virtual task body();
    super.body();
    rom_digest_overwrite();
    test_state_monitor();
  endtask

endclass : chip_sw_rom_ctrl_integrity_check_vseq
