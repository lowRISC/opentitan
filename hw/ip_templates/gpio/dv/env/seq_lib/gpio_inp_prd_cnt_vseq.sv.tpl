// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
<%
  vseq_name = f"{module_instance_name}_inp_prd_cnt_vseq"
%>\
% if num_inp_period_counters > 0:

class ${vseq_name} extends gpio_base_vseq;
  `uvm_object_utils(${vseq_name})

  // Random variables
  // - GPIO inputs (driven by DV)
  rand bit [NUM_GPIOS-1:0] gpio_i;
  // - input period counter to test
  rand int unsigned cnt_idx;
  // - input to test
  rand int unsigned inp_idx;

  `uvm_object_new

  task enable_inp_prd_cnt(bit continuous_mode,
                          int unsigned prescaler);
    ral.inp_prd_cnt_ctrl[cnt_idx].enable.set(1);
    ral.inp_prd_cnt_ctrl[cnt_idx].continuous_mode.set(continuous_mode);
    ral.inp_prd_cnt_ctrl[cnt_idx].input_select.set(inp_idx);
    ral.inp_prd_cnt_ctrl[cnt_idx].prescaler.set(prescaler);
    csr_update(.csr(ral.inp_prd_cnt_ctrl[cnt_idx]));
  endtask

  task disable_inp_prd_cnt();
    ral.inp_prd_cnt_ctrl[cnt_idx].enable.set(0);
    csr_update(.csr(ral.inp_prd_cnt_ctrl[cnt_idx]));
  endtask

  task drive_gpio(bit value);
    `DV_CHECK_MEMBER_RANDOMIZE_FATAL(gpio_i)
    gpio_i[inp_idx] = value;
    cfg.gpio_vif.drive(gpio_i);
  endtask

  task drive_10_pattern(int unsigned cycles_after_0);
    drive_gpio(.value(1'b1));
    cfg.clk_rst_vif.wait_clks_or_rst(1);
    drive_gpio(.value(1'b0));
    cfg.clk_rst_vif.wait_clks_or_rst(cycles_after_0);
  endtask

  task drive_1010_pattern(int unsigned cycles_between_1);
    drive_10_pattern(.cycles_after_0(cycles_between_1));
    drive_10_pattern(.cycles_after_0(0));
  endtask

  task test_non_continuous(int unsigned prescaler,
                           int unsigned cycles_between_1,
                           int unsigned exp_val);
    bit [TL_DW-1:0] act_val;

    enable_inp_prd_cnt(.continuous_mode(0), .prescaler(prescaler));
    drive_1010_pattern(.cycles_between_1(cycles_between_1));

    // It may take up to `prescaler` cycles for the counter to be updated.
    cfg.clk_rst_vif.wait_clks_or_rst(prescaler);

    // Read the value of the input pattern counter and check that it matches the expected value.
    csr_rd(.ptr(ral.inp_prd_cnt_val[cnt_idx]), .value(act_val));
    `DV_CHECK_EQ(act_val, exp_val)
  endtask

  task test_continuous_two_patterns(int unsigned prescaler,
                                    int unsigned cycles_between_first_1,
                                    int unsigned cycles_between_second_1,
                                    int unsigned exp_val);
    bit [TL_DW-1:0] act_val;

    enable_inp_prd_cnt(.continuous_mode(1), .prescaler(prescaler));
    drive_10_pattern(.cycles_after_0(cycles_between_first_1));
    drive_1010_pattern(.cycles_between_1(cycles_between_second_1));

    // It may take up to `prescaler` cycles for the counter to be updated.
    cfg.clk_rst_vif.wait_clks_or_rst(prescaler);

    // Read the value of the input pattern counter and check that it matches the expected value.
    csr_rd(.ptr(ral.inp_prd_cnt_val[cnt_idx]), .value(act_val));
    `DV_CHECK_EQ(act_val, exp_val)

    // Disable the input pattern counter ahead of the next continuous test case.
    disable_inp_prd_cnt();
  endtask

  task body();
    // Randomize vseq variables.
    `DV_CHECK_MEMBER_RANDOMIZE_WITH_FATAL(cnt_idx, cnt_idx < NUM_INP_PRD_CNT;)
    `DV_CHECK_MEMBER_RANDOMIZE_WITH_FATAL(inp_idx, inp_idx < NUM_GPIOS;)

    // Initialize GPIO inputs (zero for selected input, random for all others).
    drive_gpio(.value(1'b0));

    // Test case 1: 1010 pattern in non-continuous mode and with prescaler 0.
    test_non_continuous(.prescaler(0), .cycles_between_1(1), .exp_val(1));

    // Test case 2: 10010 pattern in non-continuous mode and with prescaler 0.
    test_non_continuous(.prescaler(0), .cycles_between_1(2), .exp_val(2));

    // Test case 3: 10010 pattern in non-continuous mode and with prescaler 1.
    test_non_continuous(.prescaler(1), .cycles_between_1(2), .exp_val(1));

    // Test case 4: 101010 pattern in continuous mode and with prescaler 0.
    test_continuous_two_patterns(.prescaler(0), .cycles_between_first_1(1),
                                 .cycles_between_second_1(1), .exp_val(1));

    // Test case 5: 1010010 pattern in continuous mode and with prescaler 0.
    test_continuous_two_patterns(.prescaler(0), .cycles_between_first_1(1),
                                 .cycles_between_second_1(2), .exp_val(2));

    // TODO(#26544): Test many more random patterns with different settings.
  endtask

endclass
% endif
