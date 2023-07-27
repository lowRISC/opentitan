// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class chip_sw_rom_ctrl_integrity_check_vseq extends chip_sw_base_vseq;
  `uvm_object_utils(chip_sw_rom_ctrl_integrity_check_vseq)
  `uvm_object_new

  localparam uint TimeoutNs = 5_000_000;  // 5ms

  bit rom_ctrl_done_checker_stop;

  virtual task pre_start();
    rom_ctrl_done_checker();
    super.pre_start();
  endtask

  virtual task cpu_init();
    super.cpu_init();
    corrupt_rom_image();
  endtask

  virtual task body();
    super.body();

    // Wait for the test to boot and reach WFI.
    `DV_WAIT(cfg.sw_test_status_vif.sw_test_status == SwTestStatusInTest)
    `DV_WAIT(cfg.sw_test_status_vif.sw_test_status == SwTestStatusInWfi)

    // Update the lc state to a production state and reboot the chip.
    cfg.mem_bkdr_util_h[Otp].otp_write_lc_partition_state(lc_ctrl_state_pkg::LcStProd);
    apply_reset();

    // At this point, a successful boot would be an error. We will start a parallel timeout thread
    // which will be expected to complete as the boot process should be locked up.
    `DV_WAIT(cfg.chip_vif.rom_ctrl_done)
    `DV_SPINWAIT_EXIT(
      // ~wait~ condition.
      #(TimeoutNs * 1ns);,
      // ~exit~ condition.
      wait (cfg.sw_test_status_vif.sw_test_status == SwTestStatusInBootRom);
      `uvm_error(`gfn, "CPU unexpectedly booted and reached the ROM stage")
    )
    rom_ctrl_done_checker_stop = 1'b1;
    override_test_status_and_finish(.passed(1'b1));
  endtask

  // ROM ctrl should always report a not-good image for this test.
  //
  // This non-blocking task spawns off a thread that can be disabled using the
  // rom_ctrl_done_checker_stop bit.
  virtual task rom_ctrl_done_checker();
    fork
      forever @(cfg.chip_vif.rom_ctrl_done or rom_ctrl_done_checker_stop) begin
        if (rom_ctrl_done_checker_stop) break;
        if (cfg.chip_vif.rom_ctrl_done) begin
          #(1ns);
          `DV_CHECK(!cfg.chip_vif.rom_ctrl_good)
        end
      end
    join_none
  endtask

  // Corrupt the preloaded ROM image by flipping a single bit in the digest portion.
  virtual function void corrupt_rom_image();
    bit [bus_params_pkg::BUS_AW-1:0]                addr;
    bit [38:0]                                      data;
    bit [38:0]                                      flip_bit;
    bit [sram_scrambler_pkg::SRAM_BLOCK_WIDTH-1:0]  nonce;
    bit [sram_scrambler_pkg::SRAM_KEY_WIDTH-1:0]    key;

    // Pick any random addr and corrupt a single bit. We limit the addr selection to the digest
    // portion, since we need the ROM code to execute properly to completion in the first phase of
    // the test. The upper 32 bytes of the ROM is reserved for storing the digest.
    `DV_CHECK_STD_RANDOMIZE_WITH_FATAL(
        addr,
        addr inside {[cfg.mem_bkdr_util_h[Rom].get_size_bytes()-32:
                      cfg.mem_bkdr_util_h[Rom].get_size_bytes()-1]};
        (addr % cfg.mem_bkdr_util_h[Rom].get_bytes_per_word()) == 0;
    )
    // TODO(lowrisc/opentitan#16072): Limiting the bit-flip to the data bits. Revisit later.
    `DV_CHECK_STD_RANDOMIZE_WITH_FATAL(flip_bit, $onehot(flip_bit); flip_bit[38:32] == 0;)
    nonce = top_earlgrey_rnd_cnst_pkg::RndCnstRomCtrlScrNonce;
    key = top_earlgrey_rnd_cnst_pkg::RndCnstRomCtrlScrKey;
    data = cfg.mem_bkdr_util_h[Rom].rom_encrypt_read32(addr, key, nonce, 0) ^ flip_bit;
    cfg.mem_bkdr_util_h[Rom].rom_encrypt_write32_integ(addr, data, key, nonce, 0);
  endfunction

endclass : chip_sw_rom_ctrl_integrity_check_vseq
