// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class chip_sw_sysrst_ctrl_inputs_vseq extends chip_sw_base_vseq;
  `uvm_object_utils(chip_sw_sysrst_ctrl_inputs_vseq)

  `uvm_object_new

  localparam string PAD_KEY0_PATH = "tb.dut.IOB3";
  localparam string PAD_KEY1_PATH = "tb.dut.IOB6";
  localparam string PAD_KEY2_PATH = "tb.dut.IOB8";
  localparam string PAD_PWRB_PATH = "tb.dut.IOR13";
  localparam string PAD_ACPRES_PATH = "tb.dut.IOC7";
  localparam string PAD_LIDOPEN_PATH = "tb.dut.IOC9";
  localparam string PAD_ECRST_PATH = "tb.dut.IOR8";
  localparam string PAD_FLASHWP_PATH = "tb.dut.IOR9";
  localparam uint NUM_TEST_PHASES = 10;

  virtual function void set_pads(input bit [7:0] pad_values);
    `DV_CHECK(uvm_hdl_force(PAD_KEY0_PATH, pad_values[0]));
    `DV_CHECK(uvm_hdl_force(PAD_KEY1_PATH, pad_values[1]));
    `DV_CHECK(uvm_hdl_force(PAD_KEY2_PATH, pad_values[2]));
    `DV_CHECK(uvm_hdl_force(PAD_PWRB_PATH, pad_values[3]));
    `DV_CHECK(uvm_hdl_force(PAD_ACPRES_PATH, pad_values[4]));
    `DV_CHECK(uvm_hdl_force(PAD_LIDOPEN_PATH, pad_values[5]));
    `DV_CHECK(uvm_hdl_force(PAD_ECRST_PATH, pad_values[6]));
    `DV_CHECK(uvm_hdl_force(PAD_FLASHWP_PATH, pad_values[7]));
  endfunction

  virtual function void write_test_phase_and_expected(input int phase, input bit [7:0] expected);
    bit [7:0] test_phase[1];
    bit [7:0] test_expected[1];
    test_phase[0] = phase;
    test_expected[0] = expected;
    sw_symbol_backdoor_overwrite("kTestPhase", test_phase);
    sw_symbol_backdoor_overwrite("kTestExpected", test_expected);
  endfunction

  virtual task body();
    bit [7:0] pads_to_set = '0;
    super.body();

    for (int current_phase = 0; current_phase < NUM_TEST_PHASES; current_phase++) begin
      // set each pad individually then all together.
      case (current_phase)
        1: pads_to_set = 8'b00000001;
        2: pads_to_set = 8'b00000010;
        3: pads_to_set = 8'b00000100;
        4: pads_to_set = 8'b00001000;
        5: pads_to_set = 8'b00010000;
        6: pads_to_set = 8'b00100000;
        7: pads_to_set = 8'b01000000;
        8: pads_to_set = 8'b10000000;
        9: pads_to_set = 8'b11111111;
        default: pads_to_set = 8'b00000000;
      endcase

      set_pads(pads_to_set);
      #1us;
      write_test_phase_and_expected(current_phase, pads_to_set);

      `DV_WAIT(cfg.sw_test_status_vif.sw_test_status == SwTestStatusInTest)
      `DV_WAIT(cfg.sw_test_status_vif.sw_test_status == SwTestStatusInWfi)
    end
  endtask

endclass
