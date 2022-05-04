// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Verify pinmux can select the life_cycle, RISC-V, and DFT taps after reset.
// Verify that in TEST_UNLOCKED* and RMA states, pinmux can switch between the three TAPs
// without issuing reset.
// Verify in PROD state, only the LC tap can be selected.
// Verify in DEV state, only the LC tap and RISC-V taps can be selected.
// Verify DFT test mode straps are sampled and output to AST via
// top_earlgrey.dft_strap_test_o in TEST_UNLOCKED* and RMA states.
// Verify pimux.dft_strap_test_o is always 0 in the states other than TEST_UNLOCKED* and
// RMA, regardless of the value on DFT SW straps.
class chip_tap_straps_vseq extends chip_common_vseq;
  string path_dft_strap_test_o = {`DUT_HIER_STR, ".top_earlgrey.dft_strap_test_o"};
  bit init_rv_dm_done;
  lc_ctrl_state_pkg::lc_state_e cur_lc_state;

  local uvm_reg lc_csrs[$];

  `uvm_object_utils(chip_tap_straps_vseq)

  `uvm_object_new

  virtual task dut_init(string reset_kind = "HARD");
    init_rv_dm_done = 0;
    randomize_dft_straps();
    `DV_CHECK_STD_RANDOMIZE_FATAL(select_jtag)
    cfg.tap_straps_vif.drive(select_jtag);

    super.dut_init(reset_kind);
  endtask

  virtual task body();
    bit dft_straps_en = 1;
    chip_tap_type_e allowed_taps_q[$];

    `DV_CHECK_FATAL(uvm_hdl_check_path(path_dft_strap_test_o))

    ral.lc_ctrl.get_registers(lc_csrs);

    cur_lc_state = cfg.use_otp_image;
    check_dft_straps();

    // TODO, #12500 don't switch back to rv_dm again, limit to 2
    // repeat (2) begin
    //   random_enable_jtag_tap();
    //   test_jtag_tap();
    // end

    // reproduce #12500
    enable_jtag_tap(SelectRVJtagTap);
    test_jtag_tap();
    enable_jtag_tap(SelectLCJtagTap);
    test_jtag_tap();
    enable_jtag_tap(SelectRVJtagTap);
    test_jtag_tap();

    // check again, it shouldn't be changed
    check_dft_straps();
  endtask : body

  virtual task random_enable_jtag_tap();
    if (is_lc_in_unlocked_or_rma()) begin
      `DV_CHECK_STD_RANDOMIZE_FATAL(select_jtag)
    end else begin // switch won't take effect. tap_straps won't be sampled again
      cfg.tap_straps_vif.drive($urandom());
    end
    enable_jtag_tap(select_jtag);
  endtask

  // TODO, add DFT tap
  virtual task enable_jtag_tap(chip_tap_type_e tap);
    select_jtag = tap;
    cfg.tap_straps_vif.drive(select_jtag);
    case (select_jtag)
      SelectRVJtagTap: begin
        if (!init_rv_dm_done) begin
          init_rv_dm();
        end
        cfg.m_jtag_riscv_agent_cfg.is_rv_dm = 1;
      end
      SelectLCJtagTap:begin
        cfg.m_jtag_riscv_agent_cfg.is_rv_dm = 0;
      end
      DeselectJtagTap: begin
      end
      default: begin
        `uvm_fatal(`gfn, "Unexpected tap")
      end
    endcase
  endtask

  virtual task init_rv_dm();
    jtag_riscv_dm_activation_seq jtag_dm_activation_seq =
        jtag_riscv_dm_activation_seq::type_id::create("jtag_dm_activation_seq");

    cfg.m_jtag_riscv_agent_cfg.allow_errors = 1;
    jtag_dm_activation_seq.start(p_sequencer.jtag_sequencer_h);
    cfg.m_jtag_riscv_agent_cfg.allow_errors = 0;
  endtask

  virtual task test_jtag_tap();
    cfg.clk_rst_vif.wait_clks(100);
    `uvm_info(`gfn, $sformatf("Testing jtag tab %s", select_jtag), UVM_LOW)
    case (select_jtag)
      SelectRVJtagTap: begin
        test_rv_dm_access_via_jtag();
      end
      SelectLCJtagTap:begin
        test_lc_access_via_jtag();
      end
      DeselectJtagTap: begin
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
    foreach (ral.lc_ctrl.device_id[i]) begin
      bit [31:0] act_device_id, exp_device_id;
      ral.lc_ctrl.device_id[i].print(); // TODO, remove
      csr_peek(ral.lc_ctrl.device_id[i], exp_device_id);
      jtag_riscv_agent_pkg::jtag_read_csr(ral.lc_ctrl.device_id[i].get_offset(),
                                          p_sequencer.jtag_sequencer_h,
                                          act_device_id);
      `DV_CHECK_EQ(act_device_id, exp_device_id, $sformatf("device_id index: %0d", i))
    end
  endtask

  // if no tap is selected, expect to read all 0s
  virtual task test_no_tap_selected();
    bit [TL_DW-1:0] rdata;
    repeat (10) begin
      cfg.m_jtag_riscv_agent_cfg.is_rv_dm = $urandom_range(0, 1);
      randcase
        // enable rv_dm
        1: begin
          cfg.m_jtag_riscv_agent_cfg.is_rv_dm = 1;
          all_csrs.shuffle();
          csr_rd(all_csrs[0], rdata);
        end
        // enable LC
        1: begin
          cfg.m_jtag_riscv_agent_cfg.is_rv_dm = 0;
          lc_csrs.shuffle();
          jtag_riscv_agent_pkg::jtag_read_csr(lc_csrs[0].get_offset(),
                                              p_sequencer.jtag_sequencer_h,
                                              rdata);
        end
      endcase
      $display("wcy is_rv_dm %0d", cfg.m_jtag_riscv_agent_cfg.is_rv_dm);
      `DV_CHECK_EQ(rdata, 0)
    end
  endtask

  virtual function void randomize_dft_straps();
    bit [1:0] val = $urandom;

    `uvm_info(`gfn, $sformatf("Drive dft straps to %0d", val), UVM_LOW)
    cfg.dft_straps_vif.drive(val);
  endfunction

  virtual function void check_dft_straps();
    bit [1:0] exp_val, act_val;

    if (is_lc_in_unlocked_or_rma()) begin
      exp_val = cfg.dft_straps_vif.sample();
    end else begin
      exp_val = 0;
    end
    `DV_CHECK_FATAL(uvm_hdl_read(path_dft_strap_test_o, act_val))

    `DV_CHECK_EQ(act_val, exp_val)
  endfunction

  virtual function bit is_lc_in_unlocked_or_rma();
    return cur_lc_state inside {lc_ctrl_state_pkg::LcStRma,
        LcStTestUnlocked0, LcStTestUnlocked1, LcStTestUnlocked2, LcStTestUnlocked3,
        LcStTestUnlocked4, LcStTestUnlocked5, LcStTestUnlocked6, LcStTestUnlocked7};
  endfunction
endclass
