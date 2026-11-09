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

  // The sequencer that sends commands on the OTP macro interface. Set by the test.
  otp_macro_sequencer m_otp_macro_sequencer;

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

  // Sends one command on the OTP macro interface, as otp_ctrl would, and waits for the response.
  // The response (which holds the request in m_req) is returned in rsp, or null if a reset
  // interrupted the command.
  extern protected task otp_macro_req(output otp_macro_rsp_seq_item    rsp,
                                      input  otp_ctrl_macro_pkg::cmd_e cmd,
                                      input  otp_macro_addr_t          addr,
                                      input  otp_macro_size_t          size,
                                      input  otp_macro_data_t          wdata);

  // Sends Init on the OTP macro interface. rram_ctrl ignores every other OTP command until then.
  extern protected task otp_macro_init(output otp_macro_rsp_seq_item rsp);

  // Sends Read (or ReadRaw if raw is true) on the OTP macro interface.
  extern protected task otp_macro_read(output otp_macro_rsp_seq_item rsp,
                                       input  otp_macro_addr_t       addr,
                                       input  otp_macro_size_t       size,
                                       input  bit                    raw);

  // Sends Write (or WriteRaw if raw is true) on the OTP macro interface.
  extern protected task otp_macro_write(output otp_macro_rsp_seq_item rsp,
                                        input  otp_macro_addr_t       addr,
                                        input  otp_macro_size_t       size,
                                        input  otp_macro_data_t       wdata,
                                        input  bit                    raw);

  // Reads and writes num_locations random OTP locations (see otp_macro_rw_location), two at a
  // time so that their commands overlap. saw_reset is set if a reset interrupted a command, in
  // which case the task returns early.
  extern protected task otp_macro_rand_rw(input  int unsigned num_locations,
                                          output bit          saw_reset);

  // Reads the current contents of an OTP location raw, then 1 to 3 times writes random bits on top
  // of them and reads them back with the integrity check. One time in four it then writes the
  // inverse of those bits, which sets every bit and fails if any of them was already set, and reads
  // the location again. saw_reset is set if a reset interrupted a command, in which case the task
  // returns early.
  extern protected task otp_macro_rw_location(input  otp_macro_addr_t addr,
                                              input  otp_macro_size_t size,
                                              output bit              saw_reset);

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

task rram_ctrl_base_vseq::otp_macro_req(output otp_macro_rsp_seq_item    rsp,
                                        input  otp_ctrl_macro_pkg::cmd_e cmd,
                                        input  otp_macro_addr_t          addr,
                                        input  otp_macro_size_t          size,
                                        input  otp_macro_data_t          wdata);
  otp_macro_cmd_seq seq = otp_macro_cmd_seq::type_id::create("otp_macro_cmd_seq");

  if (m_otp_macro_sequencer == null) begin
    `uvm_fatal("no_otp_macro_sequencer", "Cannot send an OTP command: no sequencer.")
  end
  if (!seq.randomize() with {m_req.m_cmd   == cmd;
                             m_req.m_addr  == addr;
                             m_req.m_size  == size;
                             m_req.m_wdata == wdata;}) begin
    `uvm_fatal("rand_failed", "Failed to randomize the OTP command.")
  end
  seq.start(m_otp_macro_sequencer);
  rsp = seq.m_rsp;
endtask : otp_macro_req

task rram_ctrl_base_vseq::otp_macro_init(output otp_macro_rsp_seq_item rsp);
  otp_macro_req(rsp, otp_ctrl_macro_pkg::Init, '0, '0, '0);
endtask : otp_macro_init

task rram_ctrl_base_vseq::otp_macro_read(output otp_macro_rsp_seq_item rsp,
                                         input  otp_macro_addr_t       addr,
                                         input  otp_macro_size_t       size,
                                         input  bit                    raw);
  otp_macro_req(rsp, raw ? otp_ctrl_macro_pkg::ReadRaw : otp_ctrl_macro_pkg::Read, addr, size, '0);
endtask : otp_macro_read

task rram_ctrl_base_vseq::otp_macro_write(output otp_macro_rsp_seq_item rsp,
                                          input  otp_macro_addr_t       addr,
                                          input  otp_macro_size_t       size,
                                          input  otp_macro_data_t       wdata,
                                          input  bit                    raw);
  otp_macro_req(rsp, raw ? otp_ctrl_macro_pkg::WriteRaw : otp_ctrl_macro_pkg::Write, addr, size,
                wdata);
endtask : otp_macro_write

task rram_ctrl_base_vseq::otp_macro_rand_rw(input  int unsigned num_locations,
                                            output bit          saw_reset);
  // The integrity chunks that a worker is using. Each worker picks a different chunk, so that the
  // commands of one worker do not change what the other one reads.
  int unsigned busy_chunks[$];
  int unsigned num_left = num_locations;

  saw_reset = 1'b0;
  fork : isolation_fork begin
    repeat (2) begin
      fork begin
        while (num_left > 0 && !saw_reset) begin
          otp_macro_addr_t addr;
          otp_macro_size_t size;
          bit              loc_saw_reset;

          if (!std::randomize(addr, size) with {
                size inside {0, 1, 3};
                (addr % (size + 1)) == 0;
                (addr + size) < otp_ctrl_macro_pkg::OtpDepth;
                !((addr / OtpWordsPerChunk) inside {busy_chunks});
              }) begin
            `uvm_fatal("rand_failed", "Failed to pick an OTP location.")
          end
          num_left--;
          busy_chunks.push_back(addr / OtpWordsPerChunk);
          otp_macro_rw_location(addr, size, loc_saw_reset);
          foreach (busy_chunks[i]) begin
            if (busy_chunks[i] == addr / OtpWordsPerChunk) begin
              busy_chunks.delete(i);
              break;
            end
          end
          if (loc_saw_reset) saw_reset = 1'b1;
        end
      end join_none
    end
    wait fork;
  end join
endtask : otp_macro_rand_rw

task rram_ctrl_base_vseq::otp_macro_rw_location(input  otp_macro_addr_t addr,
                                                input  otp_macro_size_t size,
                                                output bit              saw_reset);
  otp_macro_rsp_seq_item rsp;
  otp_macro_data_t       data;
  int unsigned           num_writes;
  bit                    try_clear;

  if (!std::randomize(num_writes, try_clear) with {
        num_writes inside {[1:3]};
        try_clear dist {0 :/ 3, 1 :/ 1};
      }) begin
    `uvm_fatal("rand_failed", "Failed to randomize the OTP writes.")
  end

  saw_reset = 1'b1;
  otp_macro_read(rsp, addr, size, .raw(1'b1));
  if (rsp == null) return;
  data = rsp.m_rdata;

  // Behave like otp_ctrl: only add bits to what is already there. Sometimes add no bits at all.
  repeat (num_writes) begin
    otp_macro_data_t new_bits;
    if (!std::randomize(new_bits) with {new_bits dist {0 :/ 1, [1:$] :/ 7};}) begin
      `uvm_fatal("rand_failed", "Failed to randomize the OTP write data.")
    end
    data |= new_bits;
    otp_macro_write(rsp, addr, size, data, .raw(1'b0));
    if (rsp == null) return;
    otp_macro_read(rsp, addr, size, .raw(1'b0));
    if (rsp == null) return;
  end

  if (try_clear) begin
    // Misbehave: write the inverse of the bits that are set. This fails with MacroWriteBlankError
    // unless no bit was set.
    otp_macro_write(rsp, addr, size, ~data, .raw(1'b0));
    if (rsp == null) return;
    otp_macro_read(rsp, addr, size, .raw(1'b0));
    if (rsp == null) return;
  end
  saw_reset = 1'b0;
endtask : otp_macro_rw_location
