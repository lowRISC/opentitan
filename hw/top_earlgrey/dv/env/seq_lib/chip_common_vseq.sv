// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class chip_common_vseq extends chip_stub_cpu_base_vseq;
  `uvm_object_utils(chip_common_vseq)

  constraint num_trans_c {
    num_trans inside {[1:2]};
  }
  `uvm_object_new

  virtual task post_apply_reset(string reset_kind = "HARD");
    super.post_apply_reset(reset_kind);

    for (int ram_idx = 0; ram_idx < cfg.num_ram_ret_tiles; ram_idx++) begin
      cfg.mem_bkdr_util_h[chip_mem_e'(RamRet0 + ram_idx)].randomize_mem();
    end
    for (int ram_idx = 0; ram_idx < cfg.num_ram_main_tiles; ram_idx++) begin
      cfg.mem_bkdr_util_h[chip_mem_e'(RamMain0 + ram_idx)].randomize_mem();
    end
    wait_rom_check_done();
  endtask

  virtual task body();
    string csr_test_type;
    void'($value$plusargs("+csr_%0s", csr_test_type));
    // These types of CSR tests are quite long; run them only once.
    if (csr_test_type inside {"bit_bash", "aliasing"}) num_trans = 1;
    // Connect the dedicated SPI host to avoid CSR mismatches from the SPI device IP.
    cfg.chip_vif.enable_spi_host = 1;
    run_common_vseq_wrapper(num_trans);
  endtask : body

  virtual task pre_start();
    super.pre_start();
    // Disable assertions failed due to CSR random write value.
    $assertoff(0,
        "tb.dut.top_earlgrey.u_adc_ctrl_aon.u_adc_ctrl_core.u_adc_ctrl_fsm.LpSampleCntCfg_M");
    $assertoff(0,
        "tb.dut.top_earlgrey.u_adc_ctrl_aon.u_adc_ctrl_core.u_adc_ctrl_fsm.NpSampleCntCfg_M");
    $assertoff(0, "tb.dut.u_ast.u_jitter_en_sync.PrimMubi4SyncCheckTransients_A");
    $assertoff(0, "tb.dut.u_ast.u_jitter_en_sync.PrimMubi4SyncCheckTransients0_A");
    $assertoff(0, "tb.dut.u_ast.u_jitter_en_sync.PrimMubi4SyncCheckTransients1_A");
  endtask

  virtual task post_start();
    super.post_start();
    $asserton(0,
        "tb.dut.top_earlgrey.u_adc_ctrl_aon.u_adc_ctrl_core.u_adc_ctrl_fsm.LpSampleCntCfg_M");
    $asserton(0,
        "tb.dut.top_earlgrey.u_adc_ctrl_aon.u_adc_ctrl_core.u_adc_ctrl_fsm.NpSampleCntCfg_M");
    $asserton(0, "tb.dut.u_ast.u_jitter_en_sync.PrimMubi4SyncCheckTransients_A");
    $asserton(0, "tb.dut.u_ast.u_jitter_en_sync.PrimMubi4SyncCheckTransients0_A");
    $asserton(0, "tb.dut.u_ast.u_jitter_en_sync.PrimMubi4SyncCheckTransients1_A");
  endtask

endclass
