// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

package pwm_env_pkg;
  // dep packages
  import uvm_pkg::*;
  import top_pkg::*;
  import dv_utils_pkg::*;
  import dv_lib_pkg::*;
  import tl_agent_pkg::*;
  import cip_base_pkg::*;
  import dv_base_reg_pkg::*;
  import csr_utils_pkg::*;
  import pwm_monitor_pkg::*;
  import pwm_reg_pkg::*;
  import pwm_ral_pkg::*;

  parameter uint PWM_NUM_CHANNELS = pwm_reg_pkg::NOutputs;

  // macro includes
  `include "uvm_macros.svh"
  `include "dv_macros.svh"

  // parameters
  // alerts
  parameter uint NUM_ALERTS = 1;
  parameter string LIST_OF_ALERTS[] = {"fatal_fault"};
  parameter bit [31:0] MAX_32 = 32'hFFFF_FFFF;
  parameter bit [15:0] MAX_16 = 16'hFFFF;
  parameter bit [26:0] MAX_27 = 27'h7FF_FFFF;
  parameter uint NUM_CYCLES = 'd1_049_000;
  parameter bit [26:0] MAX_CLK_DIV = 15;

  // datatype
  typedef enum bit {
    Enable  = 1'b1,
    Disable = 1'b0
  } pwm_status_e;

  typedef struct packed {
    bit [26:0]   ClkDiv;
    bit [3:0]    DcResn;
    bit          CntrEn;
  } cfg_reg_t;

  typedef struct packed {
    bit          BlinkEn;
    bit          HtbtEn;
    bit [15:0]   PhaseDelay;
  } param_reg_t;

  typedef struct packed {
    bit [15:0]   B;
    bit [15:0]   A;
  } dc_blink_t;

  // Split a name of the form "foo_bar_123" into a base name ("foo_bar") and an index (123). Returns
  // 1'b1 if the split is possible (the name ends with an underscore and then some digits).
  //
  // If the split is not successful, index is set to 0, base_name is set to full_name and the
  // function returns 1'b0.
  function bit split_multireg_name(input string full_name,
                                   output string base_name,
                                   output int    index);
    automatic int underscore_idx = full_name.len() - 1;
    while (underscore_idx > 0) begin
      automatic string ch = full_name.getc(underscore_idx);

      if (ch == "_") break;

      // If this isn't a digit, we should fail. Do so by setting the index to zero (so it looks like
      // we walked past the whole string)
      if (ch < "0" || "9" < ch) begin
        underscore_idx = 0;
        break;
      end

      underscore_idx--;
    end

    // If underscore_idx is zero then we either saw a non-digit character or the while loop ran
    // through the whole string without seeing an underscore. The split was not successful.
    if (underscore_idx == 0) begin
      base_name = full_name;
      index = 0;
      return 1'b0;
    end

    // If we get here then the last underscore is at underscore_idx and there is a nonempty base
    // name before it. Split and convert. Note that atoi returns 0 if the string isn't a number and
    // we aren't checking for this.
    base_name = full_name.substr(0, underscore_idx-1);
    index = full_name.substr(underscore_idx+1, full_name.len() - 1).atoi();
    return 1'b1;
  endfunction

  // package sources
  `include "pwm_seq_cfg.sv"
  `include "pwm_env_cfg.sv"
  `include "pwm_env_cov.sv"
  `include "pwm_virtual_sequencer.sv"
  `include "pwm_scoreboard.sv"
  `include "pwm_env.sv"
  `include "pwm_vseq_list.sv"

endpackage : pwm_env_pkg
