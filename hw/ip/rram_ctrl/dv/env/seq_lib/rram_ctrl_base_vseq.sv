// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class rram_ctrl_base_vseq extends cip_base_vseq #(
    .RAL_T               (rram_ctrl_core_reg_block),
    .CFG_T               (rram_ctrl_env_cfg),
    .COV_T               (rram_ctrl_env_cov),
    .VIRTUAL_SEQUENCER_T (rram_ctrl_virtual_sequencer)
  );
  `uvm_object_utils(rram_ctrl_base_vseq)

  rram_macro_prim_reg_block prim_ral;

  // Standard SV/UVM methods
  extern function new(string name="");

  // Class specific methods
  extern function void set_handles();

  // Apply reset to both the primary and OTP clock domains in parallel so that both clock
  // generators get their reset.
  extern virtual task apply_reset(string kind = "HARD");

  // The base apply_resets_concurrently() only resets cfg.clk_rst_vifs, which excludes
  // otp_clk_rst_vif. Reset it here too so both domains stay in sync during rand-reset stress.
  extern virtual task apply_resets_concurrently(int reset_duration_ps = 0);

  // Resets the DUT and brings the RRAM controller out of reset.
  extern task dut_init(string reset_kind = "HARD");

  // Initializes the RRAM controller. Starts its init sequence that reads the scrambling keys
  // from otp_ctrl. Without this initialization, no software/host access is granted.
  extern task rram_ctrl_init();

  // Sends one request on the OTP macro interface, as otp_ctrl would, and waits for the response.
  // The completed transaction (including rdata and err) is returned in rsp_item.
  extern task otp_macro_req(output otp_macro_item                      rsp_item,
                            input  otp_ctrl_macro_pkg::cmd_e            cmd,
                            input  otp_ctrl_macro_pkg::otp_macro_addr_t addr  = '0,
                            input  otp_ctrl_macro_pkg::otp_macro_size_t size  = '0,
                            input  otp_ctrl_macro_pkg::otp_macro_data_t wdata = '0);

  // Sends Init on the OTP macro interface. rram_ctrl ignores every other OTP command until then.
  extern task otp_macro_init();

  // For `num_locations` random OTP locations: reads the current contents raw, writes random bits
  // on top of them, and reads them back with the integrity check. One time in four it then tries
  // to clear the bits it just set, which OTP does not allow, and reads the location again.
  // The scoreboard checks every response.
  extern task otp_macro_rand_rw(int unsigned num_locations);


endclass : rram_ctrl_base_vseq

function rram_ctrl_base_vseq::new(string name="");
  super.new(name);
endfunction : new

function void rram_ctrl_base_vseq::set_handles();
  super.set_handles();
  `downcast(prim_ral, cfg.ral_models[cfg.prim_ral_name]);
endfunction : set_handles

task rram_ctrl_base_vseq::apply_reset(string kind = "HARD");
  fork
    super.apply_reset(kind);
    cfg.otp_clk_rst_vif.apply_reset();
  join
endtask : apply_reset

task rram_ctrl_base_vseq::apply_resets_concurrently(int reset_duration_ps = 0);
  cfg.otp_clk_rst_vif.drive_rst_pin(0);
  super.apply_resets_concurrently(cfg.otp_clk_rst_vif.clk_period_ps);
  cfg.otp_clk_rst_vif.drive_rst_pin(1);
endtask : apply_resets_concurrently

task rram_ctrl_base_vseq::dut_init(string reset_kind = "HARD");
  // Run super.dut_init() first so rram_ctrl_init() always starts from a DUT that has just
  // settled out of reset.
  super.dut_init(reset_kind);
  rram_ctrl_init();
endtask : dut_init

task rram_ctrl_base_vseq::rram_ctrl_init();
  // poll phy_init_done
  csr_spinwait(.ptr(ral.phy_status.init_done), .exp_data(1'b1));

  // initialize controller
  csr_wr(.ptr(ral.init), .value('b1));

  // poll init_done
  csr_spinwait(.ptr(ral.status.init_done), .exp_data(1'b1));
endtask : rram_ctrl_init

task rram_ctrl_base_vseq::otp_macro_req(output otp_macro_item                      rsp_item,
                                        input  otp_ctrl_macro_pkg::cmd_e            cmd,
                                        input  otp_ctrl_macro_pkg::otp_macro_addr_t addr  = '0,
                                        input  otp_ctrl_macro_pkg::otp_macro_size_t size  = '0,
                                        input  otp_ctrl_macro_pkg::otp_macro_data_t wdata = '0);
  otp_macro_base_seq seq = otp_macro_base_seq::type_id::create("otp_macro_seq");
  seq.cmd   = cmd;
  seq.addr  = addr;
  seq.size  = size;
  seq.wdata = wdata;
  seq.start(p_sequencer.otp_macro_sequencer_h);
  rsp_item = seq.rsp_item;
endtask : otp_macro_req

task rram_ctrl_base_vseq::otp_macro_init();
  otp_macro_item rsp;
  otp_macro_req(rsp, otp_ctrl_macro_pkg::Init);
endtask : otp_macro_init

task rram_ctrl_base_vseq::otp_macro_rand_rw(int unsigned num_locations);
  repeat (num_locations) begin
    otp_macro_item                       rsp;
    otp_ctrl_macro_pkg::otp_macro_addr_t addr;
    otp_ctrl_macro_pkg::otp_macro_size_t size;
    otp_ctrl_macro_pkg::otp_macro_data_t wdata;
    bit                                  try_clear;

    `DV_CHECK_STD_RANDOMIZE_WITH_FATAL(size, size inside {0, 1, 3};)
    `DV_CHECK_STD_RANDOMIZE_WITH_FATAL(addr,
                                       (addr % (size + 1)) == 0;
                                       (addr + size) < otp_ctrl_macro_pkg::OtpDepth;)
    `DV_CHECK_STD_RANDOMIZE_FATAL(wdata)
    `DV_CHECK_STD_RANDOMIZE_WITH_FATAL(try_clear, try_clear dist {0 :/ 3, 1 :/ 1};)

    otp_macro_req(rsp, otp_ctrl_macro_pkg::ReadRaw, addr, size);

    // Behave like otp_ctrl: only add bits to what is already there.
    wdata |= rsp.rdata;
    otp_macro_req(rsp, otp_ctrl_macro_pkg::Write, addr, size, wdata);
    otp_macro_req(rsp, otp_ctrl_macro_pkg::Read, addr, size);

    if (try_clear) begin
      // Misbehave: try to clear every bit that is set. rram_ctrl must report
      // MacroWriteBlankError, and still sets the new bits.
      otp_macro_req(rsp, otp_ctrl_macro_pkg::Write, addr, size, ~wdata);
      otp_macro_req(rsp, otp_ctrl_macro_pkg::Read, addr, size);
    end
  end
endtask : otp_macro_rand_rw
