// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Sequence that glitches inputs or outputs of the lockstep or the main Ibex core and ensures that
// suitable alerts are triggered.
class chip_sw_rv_core_ibex_lockstep_glitch_vseq extends chip_sw_base_vseq;
  `uvm_object_utils(chip_sw_rv_core_ibex_lockstep_glitch_vseq)

  `uvm_object_new

  typedef struct {
    string       name;
    int unsigned width; // >0: take this as width; 0: use width from parameter
    string       width_parameter_name;
    int unsigned unpacked_dim_width;
  } port_t;

  typedef logic [255:0] val_t;

  string ibex_top_path;
  string core_path;
  string lockstep_path;
  string lockstep_core_path;

  int unsigned data_open_cnt[2];
  int unsigned instr_open_cnt[2];

  bit seen_top_level_alert;

  function automatic bit cpu_is_executing_code();
    return cfg.sw_test_status_vif.sw_test_status inside {SwTestStatusInBootRom, SwTestStatusInTest};
  endfunction

  function automatic int unsigned hdl_read_int_unsigned(string path, string failure_msg);
    int unsigned val;
    `DV_CHECK_FATAL(uvm_hdl_read(path, val), failure_msg)
    return val;
  endfunction

  function automatic val_t mask(int unsigned width);
    return (val_t'(1) << width) - val_t'(1);
  endfunction

  function automatic val_t hdl_read_core_signal(string signal_subpath, bit lockstep_core,
                                                int unsigned width);
    val_t val;
    string path = $sformatf("%s.%s",
                            lockstep_core ? lockstep_core_path : core_path,
                            signal_subpath);
    `DV_CHECK_FATAL(uvm_hdl_read(path, val))
    return val & mask(width);
  endfunction

  function automatic void hdl_force_core_signal(string signal_subpath, bit lockstep_core,
                                                val_t value, int unsigned width);
    string path = $sformatf("%s.%s",
                            lockstep_core ? lockstep_core_path : core_path,
                            signal_subpath);
    `DV_CHECK_FATAL(uvm_hdl_force(path, value & mask(width)))
  endfunction

  task automatic wait_core_signal_value(string signal_subpath, bit lockstep_core, val_t val,
                                        int unsigned width);
    `DV_SPINWAIT(
      forever begin
        val_t current_val = hdl_read_core_signal(signal_subpath, lockstep_core, width);
        if (current_val == (val & mask(width))) break;
        @(cfg.chip_vif.cpu_clk_rst_if.cbn);
      end
    )
  endtask

  function automatic bit core_rf_read_used(string rf_port, bit lockstep_core);
    logic used, rf_ren, rf_rd_wb_match, rf_write_wb;
    rf_ren = hdl_read_core_signal($sformatf("rf_ren_%s", rf_port), lockstep_core, 1);
    rf_rd_wb_match = hdl_read_core_signal($sformatf("rf_rd_%s_wb_match", rf_port),
                                          lockstep_core, 1);
    rf_write_wb = hdl_read_core_signal("rf_write_wb", lockstep_core, 1);
    if (rf_port == "a") used = rf_ren && !rf_rd_wb_match;
    // If not forwarding from writeback, the LSU gets the write data from Port b of the RF.
    // This is then output on the data interface.
    else used = (rf_ren && !rf_rd_wb_match) || !(rf_rd_wb_match && rf_write_wb);
    return used;
  endfunction

  function automatic bit core_ic_scr_key_used(bit lockstep_core);
    logic [1:0] inval_state = hdl_read_core_signal("if_stage_i.gen_icache.icache_i.inval_state_q",
                                                   lockstep_core, 2);
    return (inval_state == 2'b01 /* AWAIT_SCRAMBLE_KEY */);
  endfunction

  task automatic wait_core_rf_read_used(string rf_port, bit lockstep_core);
    `DV_SPINWAIT(
      forever begin
        if (core_rf_read_used(rf_port, lockstep_core)) break;
        @(cfg.chip_vif.cpu_clk_rst_if.cbn);
      end
    )
  endtask

  function automatic string irq_field_name(int unsigned idx);
    string field_name;
    unique case (idx) inside
            3: field_name = "irq_software";
            7: field_name = "irq_timer";
           11: field_name = "irq_external";
      [16:30]: field_name = $sformatf("irq_fast[%0d]", idx - 16);
      default: `dv_fatal("Illegal IRQ index.")
    endcase
    return field_name;
  endfunction

  // Determine if a core is ready to serve an IRQ.  Idx:
  //    3 = software IRQ
  //    7 = timer IRQ
  //   11 = external IRQ
  // >=16 = fast IRQs 0 to 14
  function automatic bit core_irq_ready(int unsigned idx, bit lockstep_core);
    string field_name;
    logic mstatus_mie, mie, mip;
    field_name = irq_field_name(idx);
    mstatus_mie = hdl_read_core_signal("cs_registers_i.mstatus_q.mie", lockstep_core, 1);
    mie = hdl_read_core_signal($sformatf("cs_registers_i.mie_q.%s", field_name), lockstep_core, 1);
    mip = hdl_read_core_signal($sformatf("cs_registers_i.mip.%s", field_name), lockstep_core, 1);
    return (mstatus_mie & mie & ~mip);
  endfunction

  // Make a core ready to handle an IRQ.  This directly sets CSR bits inside the core, so that the
  // verification environment does not have to rely on software for enabling interrupts to test
  // glitches on them.
  task automatic make_core_irq_ready(int unsigned idx, bit lockstep_core);
    string field_name = irq_field_name(idx);
    `uvm_info(`gfn, "Forcing MSTATUS MIE", UVM_LOW)
    hdl_force_core_signal("cs_registers_i.mstatus_q.mie", lockstep_core, 1'b1, 1);
    `uvm_info(`gfn, "Forcing MIE", UVM_LOW)
    hdl_force_core_signal($sformatf("cs_registers_i.mie_q.%s", field_name),
                          lockstep_core, 1'b1, 1);
  endtask

  task automatic track_ibex_status(bit lockstep_core);
    forever begin
      logic data_gnt, data_req, data_rvalid;
      logic instr_gnt, instr_req, instr_rvalid;
      @(cfg.chip_vif.cpu_clk_rst_if.cbn or negedge cfg.chip_vif.cpu_clk_rst_if.rst_n);
      if (!cfg.chip_vif.cpu_clk_rst_if.rst_n) begin
        // Reset data interface status
        data_gnt = 1'b0;
        data_req = 1'b0;
        data_rvalid = 1'b0;
        data_open_cnt[lockstep_core] = 0;
        // Reset instruction interface status
        instr_gnt = 1'b0;
        instr_req = 1'b0;
        instr_rvalid = 1'b0;
        instr_open_cnt[lockstep_core] = 0;
      end else begin
        // Update data interface status
        data_gnt = hdl_read_core_signal("data_gnt_i", lockstep_core, 1);
        data_req = hdl_read_core_signal("data_req_o", lockstep_core, 1);
        if (data_req && data_gnt) data_open_cnt[lockstep_core]++;
        data_rvalid = hdl_read_core_signal("data_rvalid_i", lockstep_core, 1);
        if (data_rvalid) data_open_cnt[lockstep_core]--;
        // Update instruction interface status
        instr_gnt = hdl_read_core_signal("instr_gnt_i", lockstep_core, 1);
        instr_req = hdl_read_core_signal("instr_req_o", lockstep_core, 1);
        if (instr_req && instr_gnt) instr_open_cnt[lockstep_core]++;
        instr_rvalid = hdl_read_core_signal("instr_rvalid_i", lockstep_core, 1);
        if (instr_rvalid) instr_open_cnt[lockstep_core]--;
      end
    end
  endtask

  task automatic inject_glitches();
    port_t ports[];
    int unsigned port_idx;
    int unsigned port_width;
    string port_width_path;
    bit glitch_lockstep_core;
    string port_name;
    string glitch_core_path;
    string glitch_path;
    string glitch_path_lockstep;
    bit glitched_port_is_inp;
    int unsigned unpacked_idx;
    val_t orig_val;
    int unsigned bit_idx;
    val_t glitch_mask;
    val_t glitched_val;
    int unsigned lockstep_offset;
    int unsigned max_delay_clks;
    bit wait_for_inp_used;
    bit glitched_inp_used;
    string enable_cmp_path;
    bit exp_alert_major_internal;
    logic enable_cmp;
    string alert_major_internal_path;
    logic alert_major_internal;

    // Extract the lockstep offset.
    lockstep_offset = hdl_read_int_unsigned($sformatf("%s.LockstepOffset", lockstep_path),
                                            "Could not read LockstepOffset parameter.");

    // List of all ports and their bit widths (or the name of the parameter that defines the width
    // and/or the unpacked dimension).
    ports = new[45];
    ports = '{
      // `hart_id_i` and `boot_addr_i` are not glitch-protected by the lockstep core.
      // '{"hart_id_i",               1, "", 0},
      // '{"boot_addr_i",             1, "", 0},
      '{"instr_req_o",             1, "", 0},
      '{"instr_gnt_i",             1, "", 0},
      '{"instr_rvalid_i",          1, "", 0},
      '{"instr_addr_o",           32, "", 0},
      '{"instr_rdata_i",           0, "MemDataWidth", 0},
      '{"instr_err_i",             1, "", 0},
      '{"data_req_o",              1, "", 0},
      '{"data_gnt_i",              1, "", 0},
      '{"data_rvalid_i",           1, "", 0},
      '{"data_we_o",               1, "", 0},
      '{"data_be_o",               1, "", 0},
      '{"data_addr_o",            32, "", 0},
      '{"data_wdata_o",            0, "MemDataWidth", 0},
      '{"data_rdata_i",            0, "MemDataWidth", 0},
      '{"data_err_i",              1, "", 0},
      '{"dummy_instr_id_o",        1, "", 0},
      '{"rf_raddr_a_o",            5, "", 0},
      '{"rf_raddr_b_o",            5, "", 0},
      '{"rf_waddr_wb_o",           5, "", 0},
      '{"rf_we_wb_o",              1, "", 0},
      '{"rf_wdata_wb_ecc_o",       0, "RegFileDataWidth", 0},
      '{"rf_rdata_a_ecc_i",        0, "RegFileDataWidth", 0},
      '{"rf_rdata_b_ecc_i",        0, "RegFileDataWidth", 0},
      '{"ic_tag_req_o",            ibex_pkg::IC_NUM_WAYS, "", 0},
      '{"ic_tag_write_o",          1, "", 0},
      '{"ic_tag_addr_o",           ibex_pkg::IC_INDEX_W, "", 0},
      '{"ic_tag_wdata_o",          0, "TagSizeECC", 0},
      '{"ic_tag_rdata_i",          0, "TagSizeECC", ibex_pkg::IC_NUM_WAYS},
      '{"ic_data_req_o",           ibex_pkg::IC_NUM_WAYS, "", 0},
      '{"ic_data_write_o",         1, "", 0},
      '{"ic_data_addr_o",          ibex_pkg::IC_INDEX_W, "", 0},
      '{"ic_data_wdata_o",         0, "LineSizeECC", 0},
      '{"ic_data_rdata_i",         0, "LineSizeECC", ibex_pkg::IC_NUM_WAYS},
      '{"ic_scr_key_valid_i",      1, "", 0},
      '{"ic_scr_key_req_o",        1, "", 0},
      '{"irq_software_i",          1, "", 0},
      '{"irq_timer_i",             1, "", 0},
      '{"irq_external_i",          1, "", 0},
      '{"irq_fast_i",             15, "", 0},
      '{"irq_nm_i",                1, "", 0},
      '{"irq_pending_o",           1, "", 0},
      '{"debug_req_i",             1, "", 0},
      '{"crash_dump_o",            $bits(ibex_pkg::crash_dump_t), "", 0},
      '{"double_fault_seen_o",     1, "", 0},
      // `fetch_enable_i` is a multi-bit signal, and multi-bit FI is outside the threat model.
      // '{"fetch_enable_i",          1, "", 0},
      // The `alert_*` output signals are not compared between the regular core and the lockstep
      // core. Thus, those outputs are not protected against glitches.  This is intentional because
      // an alert is raised in reaction to a glitch (potentially an injected fault) inside the core.
      // To then also glitch the `alert_*` outputs, the attacker would need to be able to glitch two
      // signals at the same time, which is outside the threat model.  Thus, these signals are
      // excluded from the list of outputs in order to prevent false negative test results.
      // '{"alert_minor_o",           1, "", 0},
      // '{"alert_major_internal_o",  1, "", 0},
      // '{"alert_major_bus_o",       1, "", 0},
      '{"core_busy_o",             1, "", 0}
    };

    // Randomly pick a port (of either the lockstep core or the regular core) to glitch.
    port_idx = $urandom_range(ports.size() - 1);
    if (ports[port_idx].width > 0) begin
      port_width = ports[port_idx].width;
    end else begin
      port_width = hdl_read_int_unsigned($sformatf("%s.%s",
                                                   core_path,
                                                   ports[port_idx].width_parameter_name),
                                         "Could not obtain port width from parameter value.");
      `DV_CHECK_FATAL(port_width > 0, "Read zero port width from parameter value.")
    end
    glitch_lockstep_core = $urandom_range(1);
    glitch_core_path = glitch_lockstep_core ? lockstep_core_path : core_path;
    port_name = ports[port_idx].name;
    glitch_path = $sformatf("%s.%s", glitch_core_path, port_name);
    glitch_path_lockstep = $sformatf("%s.%s", lockstep_path, port_name);
    glitched_port_is_inp = (uvm_re_match("*_i", port_name) == 0);

    // If the port is an unpacked array, pick an index of the unpacked dimension to glitch and apply
    // that to the glitched signal path.
    if (ports[port_idx].unpacked_dim_width > 0) begin
      unpacked_idx = $urandom_range(ports[port_idx].unpacked_dim_width - 1);
      glitch_path = $sformatf("%s[%0d]", glitch_path, unpacked_idx);
      glitch_path_lockstep = $sformatf("%s[%0d]", glitch_path_lockstep, unpacked_idx);
    end

    // Pick one bit to glitch in the port.
    bit_idx = $urandom_range(port_width - 1);

    // Wait until the CPU is executing code, except if glitching the I$ scramble key valid port.
    // The reason is that the scramble key is provided shortly after reset and then not again until
    // the I$ is rescrambled, which may or may not happen for a given program.
    if (port_name != "ic_scr_key_valid_i") begin
      // Wait until the CPU is executing code (and it starts in Boot ROM).
      `DV_WAIT(cfg.sw_test_status_vif.sw_test_status == SwTestStatusInBootRom)

      // Randomize the instant at which the glitch is injected.
      if ($urandom_range(1)) begin
        // Glitch at some time at which the CPU is in Boot ROM, which currently takes up to 18k CPU
        // clock cycles to execute.
        cfg.chip_vif.cpu_clk_rst_if.wait_n_clks($urandom_range(1, 18000));
      end else begin
        // Glitch after Boot ROM, when the CPU is executing program code.
        `DV_WAIT(cfg.sw_test_status_vif.sw_test_status == SwTestStatusInTest)
        cfg.chip_vif.cpu_clk_rst_if.wait_n_clks($urandom_range(1, 1000));
      end
      // Ensure we are still running.  If not, skip the test without injecting an error.
      if (!cpu_is_executing_code()) begin
        `uvm_info(`gfn, "Skipping injection of error because CPU is not executing code.", UVM_LOW)
        return;
      end
    end

    // When glitching an input of a core, wait for the input being used so that it has an effect on
    // the core.  Don't always adhere to this waiting, though, to increase coverage and cross-check
    // the assumption that an unused glitch input does not affect the core.
    if (glitched_port_is_inp) begin
      wait_for_inp_used = $urandom_range(99) < 75;
      glitched_inp_used = 1'b0;
      if (wait_for_inp_used) begin
        `uvm_info(`gfn, $sformatf("Waiting for input port %s to become used.", glitch_path),
                  UVM_LOW)
        glitched_inp_used = 1'b1;
        case (port_name)
          "instr_gnt_i": begin
            wait_core_signal_value("instr_req_o", glitch_lockstep_core, 1'b1, 1);
          end
          "instr_rvalid_i": begin
            // `instr_open_cnt` is updated on the negative edge. If it's greater than zero one delta
            // delay later, we know `instr_rvalid_i` is being used in the next clock cycle.
            `DV_SPINWAIT(
              forever begin
                #1step;
                if (instr_open_cnt[glitch_lockstep_core] > 0) break;
                @(cfg.chip_vif.cpu_clk_rst_if.cbn);
              end
            )
            // `rvalid` gets used in the cycle after `req & gnt`, so wait one more clock cycle.
            @(cfg.chip_vif.cpu_clk_rst_if.cbn);
          end
          "instr_rdata_i", "instr_err_i": begin
            wait_core_signal_value("instr_rvalid_i", glitch_lockstep_core, 1'b1, 1);
          end
          "data_gnt_i": begin
            wait_core_signal_value("data_req_o", glitch_lockstep_core, 1'b1, 1);
          end
          "data_rvalid_i": begin
            // `data_open_cnt` is updated on the negative edge. If it's greater than zero one delta
            // delay later, we know `data_rvalid_i` is being used in the next clock cycle.
            `DV_SPINWAIT(
              forever begin
                #1step;
                if (data_open_cnt[glitch_lockstep_core] > 0) break;
                @(cfg.chip_vif.cpu_clk_rst_if.cbn);
              end
            )
            // `rvalid` gets used in the cycle after `req & gnt`, so wait one more clock cycle.
            @(cfg.chip_vif.cpu_clk_rst_if.cbn);
          end
          "data_rdata_i", "data_err_i": begin
            wait_core_signal_value("data_rvalid_i", glitch_lockstep_core, 1'b1, 1);
          end
          "rf_rdata_a_ecc_i": begin
            wait_core_rf_read_used("a", glitch_lockstep_core);
          end
          "rf_rdata_b_ecc_i": begin
            wait_core_rf_read_used("b", glitch_lockstep_core);
          end
          "ic_tag_rdata_i": begin
            wait_core_signal_value($sformatf("ic_tag_req_o[%0d]", unpacked_idx),
                                   glitch_lockstep_core, 1'b1, 1);
            // `rdata` gets used in the cycle after `req`, so wait one more clock cycle.
            @(cfg.chip_vif.cpu_clk_rst_if.cbn);
          end
          "ic_data_rdata_i": begin
            wait_core_signal_value($sformatf("ic_data_req_o[%0d]", unpacked_idx),
                                   glitch_lockstep_core, 1'b1, 1);
            // `rdata` gets used in the cycle after `req`, so wait one more clock cycle.
            @(cfg.chip_vif.cpu_clk_rst_if.cbn);
          end
          "ic_scr_key_valid_i": begin
            `DV_SPINWAIT(
              forever begin
                if (core_ic_scr_key_used(glitch_lockstep_core)) break;
                @(cfg.chip_vif.cpu_clk_rst_if.cbn);
              end
            )
          end
          // For the IRQs that can be masked (i.e., all IRQs except non-maskable (nm)), it's
          // not generally possible to wait for the core being ready to handle the IRQ because
          // software may never unmask it.  Thus, this test is more invasive for IRQs: it forces
          // signals in the glitched core to enable IRQs generally and unmask the IRQ that will be
          // glitched.  This is not considered part of the attack but of the condition that the core
          // is in when a (worst-case scenario) attack happens.
          "irq_software_i": make_core_irq_ready(3, glitch_lockstep_core);
          "irq_timer_i": make_core_irq_ready(7, glitch_lockstep_core);
          "irq_external_i": make_core_irq_ready(11, glitch_lockstep_core);
          "irq_fast_i": make_core_irq_ready(16 + bit_idx, glitch_lockstep_core);
          // For the non-maskable (nm) IRQ and the debug request, there is nothing to wait for
          // because the core always handles them.
          "irq_nm_i",
          "debug_req_i": ;
          // When the signal is not covered by this case statement, we cannot know whether the
          // glitched input is used.
          default: glitched_inp_used = 1'bx;
        endcase
      end else begin
        // Even though we did not wait for the input to be used, it could still be that it is.  We
        // have to check this to know whether to expect an alert or not.
        case (port_name)
          "instr_gnt_i": begin
            glitched_inp_used = (hdl_read_core_signal("instr_req_o", glitch_lockstep_core, 1) ==
                                 1'b1);
          end
          "instr_rvalid_i": begin
            // `instr_open_cnt` is updated on the negative edge. If it's greater than zero one delta
            // delay later, we know `instr_rvalid_i` is being used in the next clock cycle.
            #1step;
            glitched_inp_used = (instr_open_cnt[glitch_lockstep_core] > 0);
            @(cfg.chip_vif.cpu_clk_rst_if.cbn);
          end
          "instr_rdata_i", "instr_err_i": begin
            glitched_inp_used = (hdl_read_core_signal("instr_rvalid_i", glitch_lockstep_core, 1) ==
                                 1'b1);
          end
          "data_gnt_i": begin
            glitched_inp_used = (hdl_read_core_signal("data_req_o", glitch_lockstep_core, 1) ==
                                 1'b1);
          end
          "data_rvalid_i": begin
            // `data_open_cnt` is updated on the negative edge. If it's greater than zero one delta
            // delay later, we know `data_rvalid_i` is being used in the next clock cycle.
            #1step;
            glitched_inp_used = (data_open_cnt[glitch_lockstep_core] > 0);
            @(cfg.chip_vif.cpu_clk_rst_if.cbn);
            // Data integrity errors are always reported, even if the core isn't currently doing
            // a load or store instruction.
            glitched_inp_used |= (hdl_read_core_signal("load_store_unit_i.data_intg_err",
                glitch_lockstep_core, 1) == 1'b1);
          end
          "data_rdata_i", "data_err_i": begin
            glitched_inp_used = (hdl_read_core_signal("data_rvalid_i", glitch_lockstep_core, 1) ==
                                 1'b1);
          end
          "rf_rdata_a_ecc_i": begin
            glitched_inp_used = core_rf_read_used("a", glitch_lockstep_core);
          end
          "rf_rdata_b_ecc_i": begin
            glitched_inp_used = core_rf_read_used("b", glitch_lockstep_core);
          end
          "ic_scr_key_valid_i": begin
            glitched_inp_used = core_ic_scr_key_used(glitch_lockstep_core);
          end
          "irq_software_i": begin
            glitched_inp_used = core_irq_ready(3, glitch_lockstep_core);
          end
          "irq_timer_i": begin
            glitched_inp_used = core_irq_ready(7, glitch_lockstep_core);
          end
          "irq_external_i": begin
            glitched_inp_used = core_irq_ready(11, glitch_lockstep_core);
          end
          "irq_fast_i": begin
            glitched_inp_used = core_irq_ready(16 + bit_idx, glitch_lockstep_core);
          end
          "irq_nm_i": glitched_inp_used = 1'b1;
          "debug_req_i": glitched_inp_used = 1'b1;
          default: glitched_inp_used = 1'bx;
        endcase
      end
    end

    // When glitching an input that goes into the instruction cache, it's not guaranteed that the
    // input is really used.  Determine if the input is used in the cycle that we will glitch it but
    // before the value gets glitched.
    case (port_name)
      "instr_rdata_i", "instr_err_i": begin
        glitched_inp_used &= (hdl_read_core_signal("if_stage_i.gen_icache.icache_i.fill_data_rvd",
                                                   glitch_lockstep_core, 4) != '0);
      end
      "ic_tag_rdata_i": begin
        glitched_inp_used =
            (hdl_read_core_signal("if_stage_i.gen_icache.icache_i.lookup_valid_ic1",
                                  glitch_lockstep_core, 1) == 1'b1);
      end
      "ic_data_rdata_i": begin
        glitched_inp_used =
            (hdl_read_core_signal("if_stage_i.gen_icache.icache_i.lookup_valid_ic1",
                                  glitch_lockstep_core, 1) == 1'b1)
            &&
            (hdl_read_core_signal($sformatf("if_stage_i.gen_icache.icache_i.tag_match_ic1[%0d]",
                                            unpacked_idx), glitch_lockstep_core, 1) == 1'b1);
      end
      default: ;
    endcase

    `ASSERT_I(GlitchedInpUsedKnown_A, !$isunknown(glitched_inp_used))

    // Sample port value prior to glitching.
    `DV_CHECK_FATAL(uvm_hdl_read(glitch_path, orig_val))

    // Invert the bit selected for glitching.
    glitch_mask = 1 << bit_idx;
    glitched_val = orig_val ^ glitch_mask;

    // When glitching an input of a core, disable all assertions inside that core.  The rationale is
    // that the glitch is not bound to any interface specifications, so it may (and frequently will)
    // cause assertions to fail.  In silicon, however, there are no assertions, so we don't want
    // assertions to get into our way of testing countermeasures, which are part of silicon, in
    // simulation.
    if (glitched_port_is_inp) begin
      if (glitch_lockstep_core) begin
        // The path to the core unfortunately has to be duplicated for `$assertoff()` because that
        // system task only accepts literal strings.
        $assertoff(0, "tb.dut.top_earlgrey.u_rv_core_ibex.u_core.gen_lockstep.u_ibex_lockstep");
      end else begin
        $assertoff(0, "tb.dut.top_earlgrey.u_rv_core_ibex.u_core.u_ibex_core");
      end
    end

    if (!glitch_lockstep_core) begin
      case (port_name)
        // When glitching an input or output signal of the main core potentially feeding into the
        // bus interfaces, the core may no longer adhere to the TL-UL bus specification.
        // Therefore, assertions on the corresponding TL-UL device and host ports of the main
        // X-bar may need to be disabled.
        "instr_req_o",
        "instr_addr_o",
        // The RF read addresses impact the read data thereby changing a potential branching
        // decision and thus instr_req_o. Changing instr_req_o on the falling clock edge can
        // lead to failing assertions.
        "rf_raddr_a_o",
        "rf_raddr_b_o",
        // Glitching the instruction cache tag or data may trigger an ECC error and cause the cache
        // to immediately refetch the corresponding address from memory. As a result, instr_req_o
        // may go high on the falling clock edge leading to failing assertions.
        "ic_tag_rdata_i",
        "ic_data_rdata_i": begin
          $assertoff(0,
              "tb.dut.top_earlgrey.u_xbar_main.tlul_assert_host_rv_core_ibex__corei.gen_device");
          $assertoff(0,
              "tb.dut.top_earlgrey.u_xbar_main.tlul_assert_device_rom_ctrl__rom.gen_host");
          $assertoff(0,
              "tb.dut.top_earlgrey.u_xbar_main.tlul_assert_device_rv_dm__mem.gen_host");
          $assertoff(0,
              "tb.dut.top_earlgrey.u_xbar_main.tlul_assert_device_sram_ctrl_main__ram.gen_host");
          $assertoff(0,
              "tb.dut.top_earlgrey.u_xbar_main.tlul_assert_device_flash_ctrl__mem.gen_host");
        end
        "data_req_o",
        "data_we_o",
        "data_be_o",
        "data_addr_o",
        "data_wdata_o": begin
          $assertoff(0,
              "tb.dut.top_earlgrey.u_xbar_main.tlul_assert_host_rv_core_ibex__cored.gen_device");
        end
        // The RF read data obtained on Port b may feed into data_wdata_o even if Ibex isn't doing
        // a store.
        "rf_rdata_b_ecc_i": begin
          if (glitched_inp_used) begin
            $assertoff(0,
                "tb.dut.top_earlgrey.u_xbar_main.tlul_assert_host_rv_core_ibex__cored.gen_device");
          end
        end
        // There are several SVAs inside ibex_top ensuring correct behavior of crash dump. When
        // glitching crash dump it's expected that one or multiple of these SVAs will fire.
        "crash_dump_o": begin
          $assertoff(0, "tb.dut.top_earlgrey.u_rv_core_ibex.u_core");
        end
        default: ;
      endcase
    end

    // Force the glitched value onto the port for one cycle, then release it again.
    `DV_CHECK_FATAL(uvm_hdl_force(glitch_path, glitched_val));
    `uvm_info(`gfn, $sformatf("Forcing %s to value 'h%0x.", glitch_path, glitched_val), UVM_LOW)
    if (!glitch_lockstep_core && glitched_port_is_inp) begin
      // The input ports of the ibex_core module are defined as `logic` without an explicit net
      // type. According to the standard, simulation tools are thus supposed to model these inputs
      // using a `var` type. However, it turns out that some tools collapse input ports into a
      // single object to reduce the number of assignments to improve simulation performance.
      // As a result, glitches inserted to inputs of the non-lockstep core may propagate back and
      // also change the input of the lockstep core. If this happens, both cores are glitched
      // simultaneously without any alerts firing.
      //
      // To avoid this, we also glitch the corresponding input of the ibex_lockstep instance to
      // the opposite value. The ibex_lockstep instance is embedded inside prim_buf cells across
      // which glitches don't progagate back. Also, the delay lines are embedded inside the
      // ibex_lockstep instance. It's thus fine to apply the glitch simultaneously.
      //
      // It's further worth noting that:
      //
      // 1. For some top-level inputs there may exist single points of failure, e.g. some inputs
      //    without integrity protection, some control signals without spurious enable detection.
      //    There are always such single points of failures. Where and how many there are depends
      //    on the surrounding modules, backend etc. and is out of scope for the lockstep
      //    countermeasure.
      // 2. To verify the lockstep countermeasure, we should actually be glitching internal core
      //    signals instead of inputs to the ibex_core module. However, the problem with this is
      //    that it's infeasible to always correctly model how the glitching of any internal signal
      //    impacts core behavior and ultimately whether this should be detected. Forcing inputs
      //    of ibex_core is a way to make the test feasible in the first place.
      //
      // For more details refer to https://github.com/lowRISC/ibex/pull/1967 .
      `DV_CHECK_FATAL(uvm_hdl_force(glitch_path_lockstep, orig_val));
      `uvm_info(`gfn, $sformatf("Forcing %s to value 'h%0x.", glitch_path_lockstep, orig_val),
          UVM_LOW)
    end
    cfg.chip_vif.cpu_clk_rst_if.wait_n_clks(1);
    if ((uvm_re_match("irq_*_i", port_name) != 0) && (port_name != "debug_req_i")) begin
      // If the port is not an interrupt or debug request, which are level-sensitive signals,
      // release the forcing at this point.
      `DV_CHECK_FATAL(uvm_hdl_release(glitch_path));
      `uvm_info(`gfn, $sformatf("Releasing force of %s.", glitch_path), UVM_LOW)
      if (!glitch_lockstep_core && glitched_port_is_inp) begin
        // In case we glitched an input port of the non-lockstep core, we must now also release
        // the force applied to the corresponding port of the ibex_lockstep instance.
        `DV_CHECK_FATAL(uvm_hdl_release(glitch_path_lockstep));
        `uvm_info(`gfn, $sformatf("Releasing force of %s.", glitch_path_lockstep), UVM_LOW)
      end
    end

    // An alert should be triggered, so we check for that. Depending on the glitched signal and
    // core it may take several clock cycles for a potential alert to fire. We wait for at most
    // max_delay_clks cycles.
    max_delay_clks = 10 + lockstep_offset;

    // Assert that `enable_cmp_q` in `ibex_lockstep` is 1.  When coming out of reset and
    // starting execution, it takes `LockstepOffset` clock cycles for this to happen.
    enable_cmp_path = $sformatf("%s.enable_cmp_q", lockstep_path);
    for (int i = 0; i < lockstep_offset; i++) begin
      `DV_CHECK_FATAL(uvm_hdl_read(enable_cmp_path, enable_cmp))
      if (enable_cmp) begin
        break;
      end else begin
        cfg.chip_vif.cpu_clk_rst_if.wait_n_clks(1);
      end
    end
    `DV_CHECK_EQ_FATAL(enable_cmp, 1'b1, "Lockstep comparison disabled, which is illegal.")

    // Calculate whether we expect a major alert.
    exp_alert_major_internal = 1'b0;
    if (glitched_port_is_inp) begin
      // Expect a major alert for a *used* glitched input.
      if (glitched_inp_used) begin
        exp_alert_major_internal = 1'b1;
        `uvm_info(`gfn, "Expecting an internal major alert because glitched input is used.",
                  UVM_LOW)
      end else begin
        exp_alert_major_internal = 1'b0;
        `uvm_info(`gfn, "Expecting no internal major alert because glitched input is not used.",
                  UVM_LOW)
      end
    end else begin
      // Always expect a major alert for a glitched output.
      exp_alert_major_internal = 1'b1;
      `uvm_info(`gfn, "Expecting an internal major alert due to glitched output.", UVM_LOW)
    end

    if (exp_alert_major_internal) begin
      seen_top_level_alert = 1'b0;
      // Give the rv_core_ibex_fatal_hw_err alert a few more cycles to propagate out compared to the
      // alert signal at the ibex top level.
      check_alert_occurs("rv_core_ibex_fatal_hw_err", max_delay_clks + 5);
    end

    // Check that `alert_major_internal_o` of `ibex_lockstep` matches our expectation. Depending on
    // the glitched signal and core it may take several clock cycles for a potential alert to fire.
    // We wait for at most max_delay_clks cycles.
    alert_major_internal_path = $sformatf("%s.alert_major_internal_o", lockstep_path);
    for (int i = 0; i <= max_delay_clks; i++) begin
      `uvm_info(`gfn, $sformatf("Checking for potential alert in cycle %0d.", i), UVM_MEDIUM)
      `DV_CHECK_FATAL(uvm_hdl_read(alert_major_internal_path, alert_major_internal))
      if (exp_alert_major_internal) begin
        if (alert_major_internal) begin
          `uvm_info(`gfn, $sformatf("Major alert expectedly fired in cycle %0d.", i), UVM_LOW)
          break;
        end
      end else begin
        `DV_CHECK_EQ_FATAL(alert_major_internal, exp_alert_major_internal,
                           $sformatf("Major alert unexpectedly fired in cycle %0d.", i))
      end
      cfg.chip_vif.cpu_clk_rst_if.wait_n_clks(1);
    end

    `DV_CHECK_EQ_FATAL(alert_major_internal, exp_alert_major_internal,
                       "Major alert did not match expectation.")

    `DV_WAIT(!exp_alert_major_internal || seen_top_level_alert);

    // Complete the test at this point (i.e., before the binary has completed execution), because
    // the glitch may cause all sorts of problems.  This test currently only checks that the
    // lockstep module outputs a major alert.
    dv_test_status_pkg::dv_test_status(1); // Test passed.
    $finish();
  endtask

  task check_alert_occurs(string alert_name, int timeout);
    fork begin
      `DV_CHECK_FATAL(cfg.m_alert_agent_cfgs.exists(alert_name))

      `uvm_info(`gfn, $sformatf("Checking for alert %s, expected in not more than %0d cycles",
        alert_name, timeout), UVM_LOW)

      for (int i = 0; i <= timeout; i++) begin
        if (cfg.m_alert_agent_cfgs[alert_name].vif.get_alert()) begin
          `uvm_info(`gfn, $sformatf("Alert %s has been seen", alert_name), UVM_LOW)
          seen_top_level_alert = 1'b1;
        end

        cfg.chip_vif.cpu_clk_rst_if.wait_n_clks(1);
      end

      if (!seen_top_level_alert) begin
        `DV_CHECK_FATAL(1'b0,
          $sformatf("Alert %s was not seen within %0d cycles", alert_name, timeout))
      end
    end join_none
  endtask

  virtual task dut_init(string reset_kind = "HARD");
    super.dut_init(reset_kind);
    // Initialize instruction cache memories to all zeros. Without this, glitching e.g.
    // ic_data_addr_o may lead to cache entries being read before writing them, leading to
    // X-propagation into the main crossbar and SRAM. In contrast, reading an all-zero
    // entry triggers ECC integrity errors which the design can handle.
    cfg.mem_bkdr_util_h[ICacheWay0Tag].clear_mem();
    cfg.mem_bkdr_util_h[ICacheWay1Tag].clear_mem();
    cfg.mem_bkdr_util_h[ICacheWay0Data].clear_mem();
    cfg.mem_bkdr_util_h[ICacheWay1Data].clear_mem();
  endtask

  virtual task body();
    super.body();

    // Set paths to the core and the shadow core inside the lockstep instance.
    ibex_top_path = "tb.dut.top_earlgrey.u_rv_core_ibex.u_core";
    core_path = $sformatf("%s.u_ibex_core", ibex_top_path);
    lockstep_path = $sformatf("%s.gen_lockstep.u_ibex_lockstep", ibex_top_path);
    lockstep_core_path = $sformatf("%s.u_shadow_core", lockstep_path);

    fork
      inject_glitches();
      track_ibex_status(1'b0);
      track_ibex_status(1'b1);
    join
  endtask
endclass
