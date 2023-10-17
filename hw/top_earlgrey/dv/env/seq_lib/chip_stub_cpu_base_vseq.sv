// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// this is the base vseq that uses stub mode, this vseq can be extended for these tests
// 1. CSR tests
// 2. IP tests which run in chip-level and send TL items on ibex output
class chip_stub_cpu_base_vseq extends chip_base_vseq;
  `uvm_object_utils(chip_stub_cpu_base_vseq)

  `uvm_object_new

  virtual task pre_start();
    // In top-level uart RX pin may be selected in pinmux. CSR tests may randomly enable line
    // loopback, which will connect TX with RX. If RX isn't enabled in pinmux, it will be 0.
    // moniter will start to check the TX data when it changes from 1 to 0. But the length of 0 may
    // be not right in CSR test, which causes a protocal error on TX
    // In block-level, we always tie RX to 1 (idle) in CSR test so that we don't need to disable TX
    // monitor in block-level
    foreach (cfg.m_uart_agent_cfgs[i]) cfg.m_uart_agent_cfgs[i].en_tx_monitor = 0;

    // Select/Deselect JTAG interface.
    if (cfg.jtag_riscv_map != null || cfg.use_jtag_dmi == 1) begin
      `DV_GET_ENUM_PLUSARG(chip_common_pkg::chip_jtag_tap_e, cfg.select_jtag, select_jtag)
      cfg.chip_vif.tap_straps_if.drive(cfg.select_jtag);
    end
    enable_asserts_in_hw_reset_rand_wr = 0;
    super.pre_start();
  endtask

  task post_start();
    super.post_start();

    if (cfg.use_jtag_dmi == 0) begin
      // Random CSR rw might trigger alert. Some alerts will conintuously be triggered until reset
      // applied, which will cause alert_monitor phase_ready_to_end timeout.
      apply_reset();
    end
  endtask

  virtual task apply_reset(string kind = "HARD");
    super.apply_reset(kind);
    `DV_SPINWAIT(cfg.chip_vif.cpu_clk_rst_if.wait_for_reset();)
  endtask

  virtual task post_apply_reset(string reset_kind = "HARD");
    super.post_apply_reset(reset_kind);
    // Wait until rom_ctrl and lc_ctrl have finished to ensure stub_cpu
    // does not conflict with any background power-up activity

    // Add extra guard for closed source env.
    // Closed source has long reset period (> 1ms).
    // If `wait_rom_check_done()` is called during the reset period,
    // this task pass without checking and causes false failure.
    // wait for aon clock to make sure reset is de-asserted.
    @cfg.chip_vif.aon_clk_por_rst_if.cb;
    `uvm_info(`gfn, "Wait for ROM check to complete", UVM_MEDIUM)
    wait_rom_check_done();
  endtask

  virtual task dut_init(string reset_kind = "HARD");
    super.dut_init(reset_kind);
    // Program the AST with the configuration data loaded in OTP creator SW config region.
    `uvm_info(`gfn, "Perform AST configuration", UVM_MEDIUM)
    if (cfg.use_jtag_dmi == 0) do_ast_cfg();
  endtask

  // Write AST registers with the configuration data backdoor loaded into OTP creator SW cfg region.
  //
  // This mimics what the test ROM / ROM does in SW based tests, but for non-SW tests. Invoked
  // in dut_init(), which is called in pre_start().
  virtual task do_ast_cfg();
    logic [31:0] data;

    // The AST registers are defined differently between the open source and closed source repos.
    // Hence, we make no references to the AST registers defined in ral.ast. We instead find the
    // base address of the AST configuration space, and start writing what was dumped in the
    // corresponding OTP locations. The number of registers to program is provided by
    // ast_pkg::AstRegsNum, which includes the last AST register which "finalizes" the AST
    // initialization and asserts the `ast_init_done_o` signal.
    uvm_reg_addr_t ast_addr = ral.ast.default_map.get_base_addr();

    if (cfg.mem_bkdr_util_h[Otp].read32(otp_ctrl_reg_pkg::CreatorSwCfgAstInitEnOffset) ==
        prim_mubi_pkg::MuBi4True) begin
      for (int i = 0; i < ast_pkg::AstRegsNum; i++) begin
        data = cfg.mem_bkdr_util_h[Otp].read32(otp_ctrl_reg_pkg::CreatorSwCfgAstCfgOffset + i * 4);
        `uvm_info(`gfn, $sformatf("Writing 0x%0h to 0x%0h", data, ast_addr), UVM_MEDIUM)
        tl_access(.addr(ast_addr), .write(1), .data(data));
        predict_csr_wr(ral.get_default_map(), ast_addr, data);
        ast_addr += 4;
      end
    end
  endtask

  // Finds the register associated with the given address in the given map, and updates the
  // mirrored value with the data written.
  function void predict_csr_wr(uvm_reg_map map, uvm_reg_addr_t addr, uvm_reg_data_t data);
    uvm_reg rg = map.get_reg_by_offset(addr);
    if (rg != null) begin
      void'(rg.predict(.value(data), .kind(UVM_PREDICT_WRITE)));
    end else begin
      `uvm_error(`gfn, $sformatf("No register found at address 0x%0h in %0s", addr, map.`gfn))
    end
  endfunction

endclass
