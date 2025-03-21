// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class racl_ctrl_scoreboard extends cip_base_scoreboard #(.CFG_T(racl_ctrl_env_cfg),
                                                         .RAL_T(racl_ctrl_reg_block),
                                                         .COV_T(racl_ctrl_env_cov));
  `uvm_component_utils(racl_ctrl_scoreboard)

  extern function new (string name="", uvm_component parent=null);

  extern function void build_phase(uvm_phase phase);
  extern task run_phase(uvm_phase phase);
  extern task process_tl_access(tl_seq_item item, tl_channels_e channel, string ral_name);

  // A dynamic array of bits (used as a return value)
  typedef bit bit_vec_t[];

  // A function that looks at cfg.policies_vif and checks that its values match those requested in
  // the policy registers.
  extern function void check_policies();

  // A task that watches cfg.policies_vif continuously, checking that the values always match the
  // ones requested by the policy registers.
  //
  // This performs a check just after each change to the output. To make sure everything stays in
  // sync, the process_tl_access task does an analogous check after each write to one of those
  // policies.
  extern task watch_policies();
endclass

function racl_ctrl_scoreboard::new (string name="", uvm_component parent=null);
  super.new(name, parent);
endfunction

function void racl_ctrl_scoreboard::build_phase(uvm_phase phase);
  super.build_phase(phase);
  // TODO: remove once support alert checking
  do_alert_check = 0;
endfunction

task racl_ctrl_scoreboard::run_phase(uvm_phase phase);
  // At the start of time, wait until rst_n is either 0 or 1 (skipping over any period where it's 'x
  // at the start)
  wait(!$isunknown(cfg.clk_rst_vif.rst_n));
  fork
    super.run_phase(phase);
    watch_policies();
  join
endtask

task racl_ctrl_scoreboard::process_tl_access(tl_seq_item item,
                                             tl_channels_e channel,
                                             string ral_name);
  uvm_reg csr;
  bit     do_read_check   = 1'b1;
  bit     write           = item.is_write();
  uvm_reg_addr_t csr_addr = cfg.ral_models[ral_name].get_word_aligned_addr(item.a_addr);

  bit addr_phase_read   = (!write && channel == AddrChannel);
  bit addr_phase_write  = (write && channel == AddrChannel);
  bit data_phase_read   = (!write && channel == DataChannel);
  bit data_phase_write  = (write && channel == DataChannel);

  // if access was to a valid csr, get the csr handle
  if (csr_addr inside {cfg.ral_models[ral_name].csr_addrs}) begin
    csr = cfg.ral_models[ral_name].default_map.get_reg_by_offset(csr_addr);
    `DV_CHECK_NE_FATAL(csr, null)
  end
  else begin
    `uvm_fatal(`gfn, $sformatf("Access unexpected addr 0x%0h", csr_addr))
  end

  // if incoming access is a write to a valid csr, then make updates right away
  if (addr_phase_write) begin
    void'(csr.predict(.value(item.a_data), .kind(UVM_PREDICT_WRITE), .be(item.a_mask)));
  end

  // If this is the D channel response for a write to one of the policy registers, check that it has
  // been applied to racl_policies_o.
  if (data_phase_write && cfg.regs.is_policy_reg(csr)) check_policies();

  // On reads, if do_read_check, is set, then check mirrored_value against item.d_data
  if (data_phase_read) begin
    if (do_read_check) begin
      `DV_CHECK_EQ(csr.get_mirrored_value(), item.d_data,
                   $sformatf("reg name: %0s", csr.get_full_name()))
    end
    void'(csr.predict(.value(item.d_data), .kind(UVM_PREDICT_READ)));
  end
endtask

function void racl_ctrl_scoreboard::check_policies();
  dv_base_reg  regs[$];
  cfg.regs.get_policy_registers(regs);

  for (int unsigned i = 0; i < regs.size(); i++) begin
    logic [31:0] seen     = cfg.policies_vif.get_policy(i);
    logic [31:0] expected = cfg.regs.get_policy(i);

    if (seen !== expected) begin
      `uvm_error(`gfn, $sformatf("Policy output mismatch for index %0d: seen %0x; expected %0x",
                                 i, seen, expected))
    end
  end
endfunction

task racl_ctrl_scoreboard::watch_policies();
  forever begin
    wait(!cfg.under_reset);

    check_policies();

    fork begin : isolation_fork
      fork
        wait(cfg.under_reset);
        begin
          @(cfg.policies_vif.policies);
          @(negedge cfg.clk_rst_vif.clk);
        end
      join_any
      disable fork;
    end join
  end
endtask
