// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Verify pinmux can select the life_cycle, RISC-V, and DFT taps after reset.
// Verify that in TEST_UNLOCKED* and RMA states, pinmux can switch between the three TAPs
// without issuing reset.
// Verify in PROD state, only the LC tap can be selected.
// Verify in DEV state, only the LC tap and RISC-V taps can be selected.
// Verify DFT test mode straps are sampled and output to AST via

class chip_tap_straps_vseq extends chip_sw_base_vseq;
  string path_tb_jtag_tck = "tb.dut.chip_if.jtag_if.tck";
  string path_tb_jtag_tms = "tb.dut.chip_if.jtag_if.tms";
  string path_tb_jtag_trst_n = "tb.dut.chip_if.jtag_if.trst_n";
  string path_tb_jtag_tdi    = "tb.dut.chip_if.jtag_if.tdi";

  lc_ctrl_state_pkg::lc_state_e cur_lc_state;

  local uvm_reg lc_csrs[$];
  chip_jtag_tap_e select_jtag;

  `uvm_object_utils(chip_tap_straps_vseq)

  `uvm_object_new

  virtual task pre_start();
    // path check
    `DV_CHECK_FATAL(uvm_hdl_check_path(path_tb_jtag_tck))
    `DV_CHECK_FATAL(uvm_hdl_check_path(path_tb_jtag_tms))
    `DV_CHECK_FATAL(uvm_hdl_check_path(path_tb_jtag_trst_n))
    `DV_CHECK_FATAL(uvm_hdl_check_path(path_tb_jtag_tdi))

    // Disable checking as pinmux isn't enabled for uart
    foreach (cfg.m_uart_agent_cfgs[i]) cfg.m_uart_agent_cfgs[i].en_tx_monitor = 0;

    super.pre_start();
    enable_asserts_in_hw_reset_rand_wr = 0;
  endtask

  virtual task dut_init(string reset_kind = "HARD");
    bit lc_at_prod;

    `DV_CHECK_STD_RANDOMIZE_FATAL(select_jtag)
    cfg.chip_vif.tap_straps_if.drive(select_jtag);
    cfg.chip_vif.set_tdo_pull(0);

    super.dut_init(reset_kind);

    cur_lc_state = cfg.mem_bkdr_util_h[Otp].otp_read_lc_partition_state();

    // in LcStProd, we can only select LC tap at boot.
    // If it's not LC tap, effectively, no tap is selected.
    if (cur_lc_state == LcStProd) begin
      cfg.mem_bkdr_util_h[Otp].otp_write_lc_partition_state(LcStProd);
      // In Dev state, only pin0 of select_jtag is sampled. When it's set, select LC tap
      if (select_jtag[0] == 0) select_jtag = JtagTapNone;
      else                     select_jtag = JtagTapLc;
    end
  endtask

  virtual task body();
    chip_jtag_tap_e allowed_taps_q[$];

    ral.lc_ctrl_regs.get_registers(lc_csrs);

    // load rom/flash and wait for rom_check to complete
    cpu_init();
    wait_rom_check_done();
    `DV_WAIT(cfg.sw_test_status_vif.sw_test_status == SwTestStatusInBootRom)

    repeat ($urandom_range(3, 10)) begin
      random_enable_jtag_tap();
      test_jtag_tap();
    end
  endtask : body

  virtual task random_enable_jtag_tap();
    chip_jtag_tap_e tap;
    `DV_CHECK_STD_RANDOMIZE_FATAL(tap)

    if (is_lc_in_unlocked_or_rma()) begin
      enable_jtag_tap(tap);
    end else begin // switch won't take effect. tap_straps won't be sampled again
      enable_jtag_tap(select_jtag);
      cfg.chip_vif.tap_straps_if.drive(tap);
    end
  endtask

  virtual task enable_jtag_tap(chip_jtag_tap_e tap);
    if (select_jtag != tap) begin
      select_jtag = tap;
      // switching tap needs to reset the agent and re-init the tap
      reset_jtag_tap();
    end
    cfg.chip_vif.tap_straps_if.drive(select_jtag);

    case (select_jtag)
      JtagTapRvDm: begin
        if (!cfg.m_jtag_riscv_agent_cfg.rv_dm_activated) init_rv_dm();
        cfg.m_jtag_riscv_agent_cfg.is_rv_dm = 1;
      end
      JtagTapLc:begin
        cfg.m_jtag_riscv_agent_cfg.is_rv_dm = 0;
      end
      JtagTapDft, JtagTapNone: begin
      end
      default: begin
        `uvm_fatal(`gfn, "Unexpected tap")
      end
    endcase
  endtask

  virtual task reset_jtag_tap();
    cfg.m_jtag_riscv_agent_cfg.in_reset = 1;
    #1000ns;
    cfg.m_jtag_riscv_agent_cfg.in_reset = 0;
  endtask

  virtual task init_rv_dm(bit exp_to_be_activated = 1);
    jtag_riscv_dm_activation_seq jtag_dm_activation_seq =
        jtag_riscv_dm_activation_seq::type_id::create("jtag_dm_activation_seq");
    cfg.m_jtag_riscv_agent_cfg.allow_errors = 1;
    if (!exp_to_be_activated) cfg.m_jtag_riscv_agent_cfg.allow_rv_dm_activation_fail = 1;
    jtag_dm_activation_seq.start(p_sequencer.jtag_sequencer_h);
    cfg.m_jtag_riscv_agent_cfg.allow_errors = 0;
    cfg.m_jtag_riscv_agent_cfg.allow_rv_dm_activation_fail = 0;

    `DV_CHECK_EQ(cfg.m_jtag_riscv_agent_cfg.rv_dm_activated, exp_to_be_activated)
    `uvm_info(`gfn, $sformatf("rv_dm_activated: %0d", cfg.m_jtag_riscv_agent_cfg.rv_dm_activated),
              UVM_LOW)
  endtask

  virtual task test_jtag_tap();
    cfg.clk_rst_vif.wait_clks(100);
    `uvm_info(`gfn, $sformatf("Testing jtag tap %s", select_jtag), UVM_LOW)
    case (select_jtag)
      JtagTapRvDm: begin
        test_rv_dm_access_via_jtag();
      end
      JtagTapLc:begin
        test_lc_access_via_jtag();
      end
      JtagTapDft, JtagTapNone: begin
        test_no_tap_selected();
      end
      default: begin
        `uvm_fatal(`gfn, "Unexpected tap")
      end
    endcase

    cfg.clk_rst_vif.wait_clks(100);
  endtask

  virtual task test_rv_dm_access_via_jtag();
    test_mem_rw(.mem(ral.sram_ctrl_main_ram.ram), .max_access(10));
  endtask

  virtual task test_lc_access_via_jtag();
    foreach (ral.lc_ctrl_regs.device_id[i]) begin
      bit [31:0] act_device_id, exp_device_id;
      csr_peek(ral.lc_ctrl_regs.device_id[i], exp_device_id);
      jtag_riscv_agent_pkg::jtag_read_csr(ral.lc_ctrl_regs.device_id[i].get_offset(),
                                          p_sequencer.jtag_sequencer_h,
                                          act_device_id);
      `DV_CHECK_EQ(act_device_id, exp_device_id, $sformatf("device_id index: %0d", i))
    end
  endtask

  // if no tap is selected, expect to read all 0s
  virtual task test_no_tap_selected();
    repeat (10) begin
      randcase
        // enable rv_dm
        1: begin
          `uvm_info(`gfn, "Testing rv_dm to make sure it cannot be activated", UVM_LOW)
          cfg.m_jtag_riscv_agent_cfg.is_rv_dm = 1;
          init_rv_dm(.exp_to_be_activated(0));
        end
        // enable LC
        1: begin
          bit [TL_DW-1:0] rdata;
          `uvm_info(`gfn, "Testing lc_ctrl to make sure it cannot be read", UVM_LOW)
          cfg.m_jtag_riscv_agent_cfg.is_rv_dm = 0;
          lc_csrs.shuffle();
          jtag_riscv_agent_pkg::jtag_read_csr(lc_csrs[0].get_offset(),
                                              p_sequencer.jtag_sequencer_h,
                                              rdata);
          `DV_CHECK_EQ(rdata, 0)
        end
      endcase
    end
  endtask

  virtual function bit is_lc_in_unlocked_or_rma();
    return cur_lc_state inside {LcStRma,
        LcStTestUnlocked0, LcStTestUnlocked1, LcStTestUnlocked2, LcStTestUnlocked3,
        LcStTestUnlocked4, LcStTestUnlocked5, LcStTestUnlocked6, LcStTestUnlocked7};
  endfunction

endclass
