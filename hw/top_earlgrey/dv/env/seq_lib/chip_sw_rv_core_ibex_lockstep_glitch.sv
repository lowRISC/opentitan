// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Sequence that glitches
// - outputs of the lockstep or the main Ibex core
// and ensures that suitable alerts are triggered.
class chip_sw_rv_core_ibex_lockstep_glitch_vseq extends chip_sw_base_vseq;
  `uvm_object_utils(chip_sw_rv_core_ibex_lockstep_glitch_vseq)

  `uvm_object_new

  typedef struct {
    string       name;
    int unsigned width; // >0: take this as width; 0: use width from parameter
    string       width_parameter_name;
  } port_t;

  function bit cpu_is_executing_code();
    return cfg.sw_test_status_vif.sw_test_status inside {SwTestStatusInBootRom, SwTestStatusInTest};
  endfunction

  function int unsigned hdl_read_int_unsigned(string path, string failure_msg);
    int unsigned val;
    `DV_CHECK_FATAL(uvm_hdl_read(path, val), failure_msg)
    return val;
  endfunction

  virtual task body();
    port_t output_ports[];
    string ibex_top_path;
    string core_path;
    string lockstep_path;
    string lockstep_core_path;
    int unsigned port_idx;
    int unsigned port_width;
    string port_width_path;
    bit glitch_lockstep_core;
    string glitch_core_path;
    string glitch_path;
    logic [255:0] orig_val;
    int unsigned bit_idx;
    logic [255:0] glitch_mask;
    logic [255:0] glitched_val;
    string enable_cmp_path;
    logic enable_cmp;
    string alert_major_internal_path;
    logic alert_major_internal;

    super.body();
    // Wait until the CPU is executing code (and it starts in Boot ROM).
    `DV_WAIT(cfg.sw_test_status_vif.sw_test_status == SwTestStatusInBootRom)

    // Randomize the instant at which the glitch is injected.
    if ($urandom_range(1)) begin
      // Glitch at some time at which the CPU is in Boot ROM, which currently takes up to 18k CPU
      // clock cycles to execute.
      cfg.chip_vif.cpu_clk_rst_if.wait_n_clks($urandom_range(18000));
    end else begin
      // Glitch after Boot ROM, when the CPU is executing program code.
      `DV_WAIT(cfg.sw_test_status_vif.sw_test_status == SwTestStatusInTest)
      cfg.chip_vif.cpu_clk_rst_if.wait_n_clks($urandom_range(1000));
    end
    // Ensure we are still running.  If not, skip the test without injecting an error.
    if (!cpu_is_executing_code()) begin
      `uvm_info(`gfn, "Skipping injection of error because CPU is not executing code.", UVM_LOW)
      return;
    end

    // List of all outputs and their bit widths.
    output_ports = new[26];
    output_ports = '{
      '{"instr_req_o",             1, ""},
      '{"instr_addr_o",           32, ""},
      '{"data_req_o",              1, ""},
      '{"data_we_o",               1, ""},
      '{"data_be_o",               1, ""},
      '{"data_addr_o",            32, ""},
      '{"data_wdata_o",            0, "MemDataWidth"},
      '{"dummy_instr_id_o",        1, ""},
      '{"rf_raddr_a_o",            5, ""},
      '{"rf_raddr_b_o",            5, ""},
      '{"rf_raddr_wb_o",           5, ""},
      '{"rf_we_wb_o",              1, ""},
      '{"rf_wdata_wb_ecc_o",       0, "RegFileDataWidth"},
      '{"ic_tag_req_o",            0, "IC_NUM_WAYS"},
      '{"ic_tag_write_o",          1, ""},
      '{"ic_tag_addr_o",           0, "IC_INDEX_W"},
      '{"ic_tag_wdata_o",          0, "TagSizeECC"},
      '{"ic_data_req_o",           0, "IC_NUM_WAYS"},
      '{"ic_data_write_o",         1, ""},
      '{"ic_data_addr_o",          0, "IC_INDEX_W"},
      '{"ic_data_wdata_o",         0, "LineSizeECC"},
      '{"ic_scr_key_req_o",        1, ""},
      '{"irq_pending_o",           1, ""},
      '{"crash_dump_o",            $bits(ibex_pkg::crash_dump_t), ""},
      '{"double_fault_seen_o",     1, ""},
      // The `alert_*` output signals are not compared between the regular core and the lockstep
      // core. Thus, those outputs are not protected against glitches.  This is intentional because
      // an alert is raised in reaction to a glitch (potentially an injected fault) inside the core.
      // To then also glitch the `alert_*` outputs, the attacker would need to be able to glitch two
      // signals at the same time, which is outside the threat model.  Thus, these signals are
      // excluded from the list of outputs in order to prevent false negative test results.
      // '{"alert_minor_o",           1, ""},
      // '{"alert_major_internal_o",  1, ""},
      // '{"alert_major_bus_o",       1, ""},
      '{"core_busy_o",             1, ""}
    };

    // Set paths to the core and the shadow core inside the lockstep instance.
    ibex_top_path = "tb.dut.top_earlgrey.u_rv_core_ibex.u_core";
    core_path = $sformatf("%s.u_ibex_core", ibex_top_path);
    lockstep_path = $sformatf("%s.gen_lockstep.u_ibex_lockstep", ibex_top_path);
    lockstep_core_path = $sformatf("%s.u_shadow_core", lockstep_path);

    // Randomly pick a port (of either the lockstep core or the regular core) to glitch.
    port_idx = $urandom_range(output_ports.size() - 1);
    if (output_ports[port_idx].width > 0) begin
      port_width = output_ports[port_idx].width;
    end else begin
      port_width = hdl_read_int_unsigned($sformatf("%s.%s",
                                                   core_path,
                                                   output_ports[port_idx].width_parameter_name),
                                         "Could not obtain port width from parameter value.");
      `DV_CHECK_FATAL(port_width > 0, "Read zero port width from parameter value.")
    end
    glitch_lockstep_core = $urandom_range(1);
    glitch_core_path = glitch_lockstep_core ? lockstep_core_path : core_path;
    glitch_path = $sformatf("%s.%s", glitch_core_path, output_ports[port_idx].name);

    // Sample port value prior to glitching.
    `DV_CHECK_FATAL(uvm_hdl_read(glitch_path, orig_val))

    // Pick one bit in the port and glitch it.
    bit_idx = $urandom_range(port_width - 1);
    glitch_mask = 1 << bit_idx;
    glitched_val = orig_val ^ glitch_mask;

    // Force the glitched value onto the port for one cycle, then release it again.
    `DV_CHECK_FATAL(uvm_hdl_force(glitch_path, glitched_val));
    `uvm_info(`gfn, $sformatf("Forcing %s to value 'h%0x.", glitch_path, glitched_val), UVM_LOW)
    cfg.chip_vif.cpu_clk_rst_if.wait_n_clks(1);
    `DV_CHECK_FATAL(uvm_hdl_release(glitch_path));
    `uvm_info(`gfn, $sformatf("Releasing force of %s.", glitch_path), UVM_LOW)

    // An alert should be triggered, so we check for that.

    if (!glitch_lockstep_core) begin
      // We glitched the non-lockstep core, so the alert is delayed by the number of cycles it takes
      // the lockstep core to produce the output to compare.
      int unsigned delay_clks = hdl_read_int_unsigned($sformatf("%s.LockstepOffset", lockstep_path),
                                                      "Could not read LockstepOffset parameter.");
      cfg.chip_vif.cpu_clk_rst_if.wait_n_clks(delay_clks);
    end

    // Assert that `enable_cmp_q` in `ibex_lockstep` is 1.  This should always be the case as soon
    // as the lockstep core starts executing.
    enable_cmp_path = $sformatf("%s.enable_cmp_q", lockstep_path);
    `DV_CHECK_FATAL(uvm_hdl_read(enable_cmp_path, enable_cmp))
    `DV_CHECK_EQ_FATAL(enable_cmp, 1'b1, "Lockstep comparison disabled, which is illegal.")

    // Check that `alert_major_internal_o` of `ibex_lockstep` is set.
    alert_major_internal_path = $sformatf("%s.alert_major_internal_o", lockstep_path);
    `DV_CHECK_FATAL(uvm_hdl_read(alert_major_internal_path, alert_major_internal))
    `DV_CHECK_EQ_FATAL(alert_major_internal, 1'b1, "Glitch did not result in major alert.")

    // Complete the test at this point (i.e., before the binary has completed execution), because
    // the glitch may cause all sorts of problems.  This test currently only checks that the
    // lockstep module outputs a major alert.
    dv_test_status_pkg::dv_test_status(1); // Test passed.
    $finish();
  endtask
endclass
