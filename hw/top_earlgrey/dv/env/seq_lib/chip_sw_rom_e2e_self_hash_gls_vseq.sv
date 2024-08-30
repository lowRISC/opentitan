// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class chip_sw_rom_e2e_self_hash_gls_vseq extends
  chip_sw_rom_e2e_base_vseq;
  `uvm_object_utils(chip_sw_rom_e2e_self_hash_gls_vseq)
  `uvm_object_new

  // Must match the `kSiliconGoldenRomHash` value in
  // `sw/device/silicon_creator/rom/e2e/release/rom_e2e_self_hash_test.c`.
  localparam string ROM_HASH = "5b2ba0baf66b45b5e5a4ddfcbd023b8a356bc7f1eeceb60abfa8034743b60e89";

  virtual task body();
    super.body();
    // Wait until we start executing from flash.
    `DV_WAIT(cfg.chip_vif.probed_cpu_pc.pc_wb >= 32'h2000_0000,
             $sformatf({"Timeout occurred when waiting for flash execution; ",
                        "Current pc_wb = 32x%0x, Timeout value = %0dns"},
                        cfg.chip_vif.probed_cpu_pc.pc_wb,
                        cfg.sw_test_timeout_ns),
             cfg.sw_test_timeout_ns)
    connect_rom_uart_agent();
    check_uart_output_msg($sformatf("ROM Hash: 0x%s\x0d\n", ROM_HASH));

    // DV test status window is not written to for silicon SW images, so we
    // must force the test pass flag to end the simulation.
    apply_reset();
    override_test_status_and_finish(.passed(1'b1));
    disconnect_rom_uart_agent();
  endtask

endclass : chip_sw_rom_e2e_self_hash_gls_vseq
