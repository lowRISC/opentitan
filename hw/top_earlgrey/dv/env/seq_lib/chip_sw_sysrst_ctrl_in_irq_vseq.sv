// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class chip_sw_sysrst_ctrl_in_irq_vseq extends chip_sw_base_vseq;
  `uvm_object_utils(chip_sw_sysrst_ctrl_in_irq_vseq)

  `uvm_object_new

  localparam string PAD_KEY0_PATH = "tb.dut.IOB3";
  localparam string PAD_KEY1_PATH = "tb.dut.IOB6";
  localparam string PAD_KEY2_PATH = "tb.dut.IOB8";
  localparam string PAD_PWRB_PATH = "tb.dut.IOR13";
  localparam string PAD_ACPRES_PATH = "tb.dut.IOC7";
  localparam string PAD_LIDOPEN_PATH = "tb.dut.IOC9";
  localparam string PAD_ECRST_PATH = "tb.dut.IOR8";
  localparam string PAD_FLASHWP_PATH = "tb.dut.IOR9";

  int test_phase = 0;

  virtual function void set_pads(input bit [7:0] pad_values);
    `DV_CHECK(uvm_hdl_force(PAD_PWRB_PATH, pad_values[0]));
    `DV_CHECK(uvm_hdl_force(PAD_KEY0_PATH, pad_values[1]));
    `DV_CHECK(uvm_hdl_force(PAD_KEY1_PATH, pad_values[2]));
    `DV_CHECK(uvm_hdl_force(PAD_KEY2_PATH, pad_values[3]));
    `DV_CHECK(uvm_hdl_force(PAD_ACPRES_PATH, pad_values[4]));
    `DV_CHECK(uvm_hdl_force(PAD_ECRST_PATH, pad_values[5]));
    `DV_CHECK(uvm_hdl_force(PAD_FLASHWP_PATH, pad_values[6]));
    `DV_CHECK(uvm_hdl_force(PAD_LIDOPEN_PATH, pad_values[7]));
  endfunction

  virtual function void write_test_phase(input int phase);
    bit [7:0] test_phase[1];
    test_phase[0] = phase;
    sw_symbol_backdoor_overwrite("kCurrentTestPhase", test_phase);
  endfunction

  virtual task create_glitch_on_pads(int glitch_duration_ns, bit [7:0] pad_values_prev,
                                     bit [7:0] pad_values_next);
    int glitch_pulse_duration_ns;
    while (glitch_duration_ns > 0) begin
      glitch_pulse_duration_ns = $urandom_range(0, glitch_duration_ns);
      glitch_duration_ns -= glitch_pulse_duration_ns;
      set_pads(pad_values_prev);
      #(glitch_pulse_duration_ns * 1ns);

      glitch_pulse_duration_ns = $urandom_range(0, glitch_duration_ns);
      glitch_duration_ns -= glitch_pulse_duration_ns;
      set_pads(pad_values_next);
      #(glitch_pulse_duration_ns * 1ns);
    end
  endtask

  virtual task sync_with_sw();
    `DV_WAIT(cfg.sw_test_status_vif.sw_test_status == SwTestStatusInTest)
    `DV_WAIT(cfg.sw_test_status_vif.sw_test_status == SwTestStatusInWfi)
  endtask

  virtual task set_pads_and_synch(int glitch_duration_ns, bit [7:0] pad_values_prev,
                                  bit [7:0] pad_values_next);
    sync_with_sw();

    // Apply glitch with a total length less than the detection timer and check
    // that the interrupt is not triggered in sw side.
    set_pads(pad_values_prev);
    create_glitch_on_pads(glitch_duration_ns, pad_values_prev, pad_values_next);
    set_pads(pad_values_prev);
    #10us;

    write_test_phase(++test_phase);

    sync_with_sw();

    // Apply an input pulse with a glitch and check that there is only one
    // interrupt is triggered in sw side, not multiple.
    set_pads(pad_values_prev);
    #10us;
    create_glitch_on_pads(glitch_duration_ns, pad_values_prev, pad_values_next);
    set_pads(pad_values_next);

    write_test_phase(++test_phase);
  endtask

  virtual task body();
    super.body();

    // Set initial value.
    set_pads(8'b00000000);

    // Test 7 H2L input transition.
    for (int i = 0; i < 7; i++) begin
      set_pads_and_synch(500, (8'b00000001 << i), 8'b00000000);
    end

    // Test 7 L2H input transition.
    for (int i = 0; i < 7; i++) begin
      set_pads_and_synch(500, 8'b00000000, (8'b00000001 << i));
    end

    // Test 4 different combo key intr sources with 2, 3, 4 and 5 combo key
    // transition H2L.
    set_pads_and_synch(500, 8'b00000011, 8'b00000000);

    set_pads_and_synch(500, 8'b00011100, 8'b00000000);

    set_pads_and_synch(500, 8'b00011011, 8'b00000000);

    set_pads_and_synch(500, 8'b00011111, 8'b00000000);

    // Last sync with sw.
    `DV_WAIT(cfg.sw_test_status_vif.sw_test_status == SwTestStatusInTest)
  endtask

endclass
