// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// This sequence issues a read to the flash controller. Inside the flash controller
// a fault is injected into the address. The goal of this sequence is to check,
// whether the data XOR address infection triggers a data integrity violation.
class flash_ctrl_host_addr_infection_vseq extends flash_ctrl_legacy_base_vseq;
  `uvm_object_utils(flash_ctrl_host_addr_infection_vseq)
  `uvm_object_new

  task body();
    string path1, path2;
    int    state_timeout_ns = 100000; // 100us

    flash_op_t host;
    bit [TL_AW-1:0] tl_addr;
    bit [7:0]       addr_glitched;
    bit             saw_err, completed;
    data_4s_t rdata;

    flash_otf_region_cfg(.scr_mode(OTFCfgTrue), .ecc_mode(OTFCfgTrue));
    cfg.clk_rst_vif.wait_clks(10);

    cfg.scb_h.expected_alert["fatal_err"].expected = 1;
    cfg.scb_h.expected_alert["fatal_err"].max_delay = 2000;
    cfg.scb_h.exp_alert_contd["fatal_err"] = 10000;

    // We expect that the TL-UL integrity check fails because address used for
    // the access gets manipulated and the data XOR address mechanism infects the
    // data, resulting in an integrity error.
    cfg.scb_h.exp_tl_rsp_intg_err = 1;

    // Generate random address for the read access.
    tl_addr[OTFBankId] = $urandom_range(0, 1);
    tl_addr[OTFHostId-2:2] = $urandom();
    tl_addr[1:0] = 'h0;
    `uvm_info(`gfn, $sformatf("Original TL-UL address is 'h%0x", tl_addr), UVM_LOW)

    // Flip bits in address before the data XOR address infection is done.
    path1 = "tb.dut.u_eflash.gen_flash_cores[0].u_core.u_rd.addr_xor_muxed[8:1]";
    path2 = "tb.dut.u_eflash.gen_flash_cores[1].u_core.u_rd.addr_xor_muxed[8:1]";
    addr_glitched = tl_addr[8:1] ^ (1 << $urandom_range(0, 7));
    `uvm_info(`gfn, $sformatf("Forcing %s to value 'h%0x", path1, addr_glitched), UVM_LOW)
    `uvm_info(`gfn, $sformatf("Forcing %s to value 'h%0x", path2, addr_glitched), UVM_LOW)
    `DV_CHECK(uvm_hdl_force(path1, addr_glitched))
    `DV_CHECK(uvm_hdl_force(path2, addr_glitched))

    // Perform the memory access.
    tl_access_w_abort(.addr(tl_addr), .write(1'b0), .completed(completed),
                      .saw_err(saw_err),
                      .tl_access_timeout_ns(cfg.seq_cfg.erase_timeout_ns),
                      .data(rdata), .check_rsp(0), .blocking(1),
                      .tl_sequencer_h(p_sequencer.tl_sequencer_hs[cfg.flash_ral_name]));

    csr_utils_pkg::wait_no_outstanding_access();

    `uvm_info(`gfn, "Wait until all drain", UVM_LOW)
    cfg.clk_rst_vif.wait_clks(100);
    `DV_CHECK(uvm_hdl_release(path1))
    `DV_CHECK(uvm_hdl_release(path2))

    // reset for the next round
    cfg.seq_cfg.disable_flash_init = 1;
    cfg.seq_cfg.en_init_keys_seeds = 0;
    apply_reset();
    csr_wr(.ptr(ral.init), .value(1));
    `uvm_info("Test","OTP",UVM_LOW)
    otp_model();
    `DV_SPINWAIT(wait(cfg.flash_ctrl_vif.rd_buf_en == 1);,
                 "Timed out waiting for rd_buf_en",
                 state_timeout_ns)
    cfg.clk_rst_vif.wait_clks(10);

    // disable tlul_err_cnt check
    cfg.tlul_core_obs_cnt = cfg.tlul_core_exp_cnt;
  endtask

endclass
