// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// misc ports connectivity check
class flash_ctrl_connect_vseq extends flash_ctrl_base_vseq;
  `uvm_object_utils(flash_ctrl_connect_vseq)
  `uvm_object_new

  task body();
    jtag_pkg::jtag_req_t jtag_src_req, jtag_dst_req;
    jtag_pkg::jtag_rsp_t jtag_src_rsp, jtag_dst_rsp;
    string   dut_path = "tb.dut";
    bit      lc_nvm_debug_en;
    ast_pkg::ast_obs_ctrl_t obs_src, obs_dst;
    bit [7:0]      fla_src, fla_dst;

    string         mystr;
    uvm_hdl_data_t data;
    `uvm_info("seq", "connectivity test starts...", UVM_MEDIUM)

    // jtag
    `DV_CHECK_STD_RANDOMIZE_FATAL(jtag_src_req)
    `DV_CHECK_STD_RANDOMIZE_FATAL(jtag_src_rsp)
    `uvm_info("seq", $sformatf("src_req:%p src_rsp:%p", jtag_src_req, jtag_src_rsp), UVM_HIGH)
    mystr = {dut_path, ".cio_tck_i"};
    `DV_CHECK(uvm_hdl_force(mystr, jtag_src_req.tck))
    mystr = {dut_path, ".cio_tms_i"};
    `DV_CHECK(uvm_hdl_force(mystr, jtag_src_req.tms))
    mystr = {dut_path, ".cio_tdi_i"};
    `DV_CHECK(uvm_hdl_force(mystr, jtag_src_req.tdi))
    mystr = {cfg.seq_cfg.flash_path_str, ".tdo_o"};
    `DV_CHECK(uvm_hdl_force(mystr, jtag_src_rsp.tdo))
    // tdo_oe : dut.eflash
    $assertoff(0, "prim_lc_sync");
    lc_nvm_debug_en = $urandom_range(0, 1);
    cfg.flash_ctrl_vif.lc_nvm_debug_en = (lc_nvm_debug_en)?
      lc_ctrl_pkg::On : get_rand_lc_tx_val(.t_weight(0), .f_weight(1), .other_weight(4));

    // takes delay to propagate lc_nvm_debug_en
    cfg.clk_rst_vif.wait_clks(5);
    mystr = {cfg.seq_cfg.flash_path_str, ".tck_i"};
    `DV_CHECK(uvm_hdl_read(mystr, jtag_dst_req.tck))
    mystr = {cfg.seq_cfg.flash_path_str, ".tms_i"};
    `DV_CHECK(uvm_hdl_read(mystr, jtag_dst_req.tms))
    mystr = {cfg.seq_cfg.flash_path_str, ".tdi_i"};
    `DV_CHECK(uvm_hdl_read(mystr, jtag_dst_req.tdi))
    mystr = {dut_path, ".cio_tdo_o"};
    `DV_CHECK(uvm_hdl_read(mystr, jtag_dst_rsp.tdo))

    // Make non-declared port don't care.
    jtag_dst_req.trst_n = jtag_src_req.trst_n & lc_nvm_debug_en;
    jtag_dst_rsp.tdo_oe = jtag_src_rsp.tdo_oe & lc_nvm_debug_en;

    `DV_CHECK_EQ(jtag_dst_req, jtag_src_req & {4{lc_nvm_debug_en}})
    `DV_CHECK_EQ(jtag_dst_rsp, jtag_src_rsp & {2{lc_nvm_debug_en}})

    `uvm_info("seq", "jtag port check complete", UVM_MEDIUM)
    `uvm_info("seq", "Observability port check start", UVM_MEDIUM)
    `DV_CHECK_STD_RANDOMIZE_FATAL(obs_src)
    `DV_CHECK_STD_RANDOMIZE_FATAL(fla_src)
    mystr = {dut_path, ".obs_ctrl_i.obgsl"};
    `DV_CHECK(uvm_hdl_force(mystr, obs_src.obgsl))
    mystr = {dut_path, ".obs_ctrl_i.obmsl"};
    `DV_CHECK(uvm_hdl_force(mystr, obs_src.obmsl))
    mystr = {dut_path, ".obs_ctrl_i.obmen"};
    `DV_CHECK(uvm_hdl_force(mystr, obs_src.obmen))
    mystr = {cfg.seq_cfg.flash_path_str, ".fla_obs_o"};
    `DV_CHECK(uvm_hdl_force(mystr, fla_src))

    cfg.clk_rst_vif.wait_clks(1);
    mystr = {cfg.seq_cfg.flash_path_str, ".obs_ctrl_i.obgsl"};
    `DV_CHECK(uvm_hdl_read(mystr, obs_dst.obgsl))
    mystr = {cfg.seq_cfg.flash_path_str, ".obs_ctrl_i.obmsl"};
    `DV_CHECK(uvm_hdl_read(mystr, data))
    obs_dst.obmsl = ast_pkg::ast_omdl_e'(data);
    mystr = {cfg.seq_cfg.flash_path_str, ".obs_ctrl_i.obmen"};
    `DV_CHECK(uvm_hdl_read(mystr, data))
    obs_dst.obmen = mubi4_t'(data);
    mystr = {dut_path, ".fla_obs_o"};
    `DV_CHECK(uvm_hdl_read(mystr, fla_dst))
    `DV_CHECK_EQ(obs_dst, obs_src)
    `DV_CHECK_EQ(fla_dst, fla_src)
    `uvm_info("seq", "Observability port check complete", UVM_MEDIUM)
  endtask
endclass // flash_ctrl_connect_vseq
