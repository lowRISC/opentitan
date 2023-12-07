// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class chip_sw_inject_scramble_seed_vseq extends chip_sw_base_vseq;
  `uvm_object_utils(chip_sw_inject_scramble_seed_vseq)

  `uvm_object_new

  localparam uint ISO_PART_SIZE = 8 * flash_phy_pkg::DataWidth/8;
  localparam uint ISO_PART_ADDR = flash_ctrl_pkg::IsolatedInfoPage *
                                  (flash_ctrl_pkg::WordsPerPage * (flash_ctrl_pkg::DataWidth / 8));
  rand bit [7:0] iso_part_data [ISO_PART_SIZE];

  virtual task dut_init(string reset_kind = "HARD");
    super.dut_init(reset_kind);

    // make sure it is unlocked and empty to start
    for (int i = 0; i < 4; i++) begin
      cfg.mem_bkdr_util_h[Otp].write64(otp_ctrl_reg_pkg::FlashAddrKeySeedOffset + i*8,
                                       '0);

      cfg.mem_bkdr_util_h[Otp].write64(otp_ctrl_reg_pkg::FlashDataKeySeedOffset + i*8,
                                       '0);

      cfg.mem_bkdr_util_h[Otp].write64(otp_ctrl_reg_pkg::SramDataKeySeedOffset + i*8,
                                       '0);
    end


    cfg.mem_bkdr_util_h[Otp].write64(otp_ctrl_reg_pkg::Secret1DigestOffset,
                                     '0);


    // make sure we are in prod state
    cfg.mem_bkdr_util_h[Otp].otp_write_lc_partition_state(LcStProd);

    // Randomize the expected data and write it into flash.
    `DV_CHECK_STD_RANDOMIZE_FATAL(iso_part_data);
    for (int i = 0; i < ISO_PART_SIZE; i++) begin
      // write some data into isolated partition
      cfg.mem_bkdr_util_h[FlashBank0Info].write8(ISO_PART_ADDR + i, iso_part_data[i]);
    end

  endtask // dut_init

  virtual task cpu_init();
    super.cpu_init();
    sw_symbol_backdoor_overwrite("kIsoPartExpData", iso_part_data);
  endtask


  virtual task body();
    super.body();

    `DV_SPINWAIT(wait(cfg.sw_logger_vif.printed_log ==
                      "Completed first phase, wait for reset");,
                 "timeout waiting for C side acknowledgement",
                 cfg.sw_test_timeout_ns)

    `uvm_info(`gfn, "Received C side acknowledgement", UVM_LOW)

    // setup triggers to bootstrap during the second run
    cfg.use_spi_load_bootstrap = 1'b1;

    `DV_SPINWAIT(wait(cfg.sw_logger_vif.printed_log ==
                      "Boot strap requested");,
                 "timeout waiting for C side acknowledgement",
                 cfg.sw_test_timeout_ns)

    `uvm_info(`gfn, "Received C side acknowledgement", UVM_LOW)

    spi_device_load_bootstrap({cfg.sw_images[SwTypeTestSlotA], ".64.scr.vmem"});
    cfg.use_spi_load_bootstrap = 1'b0;

    // After bootstrap, we need to write the expected values again,
    // since the boot-strap process wiped out the previous version.
    sw_symbol_backdoor_overwrite("kIsoPartExpData", iso_part_data);

    `DV_SPINWAIT(wait(cfg.sw_logger_vif.printed_log == "Hello World");,
             "timeout waiting for Hello World",
             cfg.sw_test_timeout_ns)

  endtask



endclass : chip_sw_inject_scramble_seed_vseq
