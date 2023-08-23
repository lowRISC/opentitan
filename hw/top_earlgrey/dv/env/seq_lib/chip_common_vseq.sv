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
  endtask

  virtual task body();
    string csr_test_type;
    void'($value$plusargs("+csr_%0s", csr_test_type));
    // sio are driven X when csb is inactive, but these pins can be configured as wakeup cause,
    // assign a known value to avoid X propagation in case that `PINMUX.WKUP_CAUSE` is programmed.
    cfg.chip_vif.spi_host_if.sio_out = $urandom;

    // These types of CSR tests are quite long; run them only once.
    if (csr_test_type inside {"bit_bash", "aliasing"}) num_trans = 1;
    run_common_vseq_wrapper(num_trans);
  endtask : body

  virtual task pre_start();
    // CSR tests write to chip CSRs, which includes the pinmux registers. Random writes to the
    // pinmux may inadvertently connect the chip IOs to peripherals, causing Xs to propagate, if
    // the chip MIOs are not initialized. Hence, we weakly pull down ALL MIOs for these tests.
    cfg.chip_vif.mios_if.pins_pd = '1;
    cfg.chip_vif.dios_if.pins_pd[top_earlgrey_pkg::DioPadSpiDevD3:
                                 top_earlgrey_pkg::DioPadSpiHostD0] = '1;

    super.pre_start();
    // Disable assertions failed due to CSR random write value.
    $assertoff(0,
        "tb.dut.top_earlgrey.u_adc_ctrl_aon.u_adc_ctrl_core.u_adc_ctrl_fsm.LpSampleCntCfg_M");
    $assertoff(0,
        "tb.dut.top_earlgrey.u_adc_ctrl_aon.u_adc_ctrl_core.u_adc_ctrl_fsm.NpSampleCntCfg_M");
  endtask

  virtual task post_start();
    super.post_start();
    $asserton(0,
        "tb.dut.top_earlgrey.u_adc_ctrl_aon.u_adc_ctrl_core.u_adc_ctrl_fsm.LpSampleCntCfg_M");
    $asserton(0,
        "tb.dut.top_earlgrey.u_adc_ctrl_aon.u_adc_ctrl_core.u_adc_ctrl_fsm.NpSampleCntCfg_M");
    cfg.chip_vif.mios_if.pins_pd = '0;
    cfg.chip_vif.dios_if.pins_pd[top_earlgrey_pkg::DioPadSpiDevD3:
                                 top_earlgrey_pkg::DioPadSpiHostD0] = '0;
  endtask

  // Wait for cpu fetch enable before primary sequence start
  // in stub cpu test.
  virtual task run_common_vseq_wrapper(int num_times = 1);
    wait(cfg.chip_vif.pwrmgr_cpu_fetch_en == 1);
    super.run_common_vseq_wrapper(num_times);
  endtask
endclass
