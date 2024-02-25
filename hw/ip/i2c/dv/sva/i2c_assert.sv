// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Module to check for SDA, SCL unstable and interference interrupts
// For each interrupt there are two assertions
// - One to check if the interrupt is asserted when an trigger event is observed
// - Another to check if the interrupt is asserted then there is a past triggering event
// The second assertion is to make sure there are no false alarms
module i2c_assert(
  input                     clk_i,
  input                     rst_ni,

  // Generic IO
  input                     scl_i,
  input logic               cio_scl_o,
  input logic               cio_scl_en_o,
  input                     sda_i,
  input logic               cio_sda_o,
  input logic               cio_sda_en_o,

  // Interrupts
  input logic              intr_scl_interference_o,
  input logic              intr_sda_interference_o,
  input logic              intr_sda_unstable_o
);
  // Indicates the number of cycle it takes for an event to to generate interrupt at DUT kevek
  localparam int EVENT_TO_INTR_DELAY = 5;

  logic sda_q, scl_q;
  // I2C registers required for assertions
  logic host_mode_en;
  logic [15:0] thigh;
  logic [15:0] tlow;
  logic [15:0] t_r;
  logic [15:0] t_f;
  logic [15:0] tsu_sta; // Setup time for Start condition after posedge of SCL
  logic [15:0] thd_sta; // Hold time for Start codition before negedge of SCL
  logic [15:0] tsu_sto; // Setup time for Stop condition after posedge of SCL
  logic [15:0] tsu_dat; // Setup time for Data bit before posedge of SCL
  logic [15:0] thd_dat; // Hold time for Data bit after negedge of SCL

  bit host_transmit_mode;// Indicates when host is transmitting data on SDA line
  logic start_detected;
  logic stop_detected;
  logic active_transmission;
  logic posedge_scl;
  logic negedge_scl;
  int byte_count = 0;
  int bit_count = 0;
  bit rwbit = 0;
  // SDA interference check variables
  logic sda_interference_intr_en;
  logic sda_interference_intr_trigger;
  logic sda_interference_intr_expected;
  logic sda_interference_cycle_count = 0;
  // SCL interference check variables
  logic scl_interference_intr_en;
  logic scl_interference_intr_trigger;
  logic scl_interference_cycle_count = 0;
  logic scl_interference_intr_expected;
  // SDA unstable check variables
  logic sda_unstable_intr_en;
  logic sda_unstable_intr_trigger;
  logic sda_unstable_cycle_count = 0;
  logic sda_unstable_intr_expected;

  int scl_high_period = 0;
  int scl_low_period = 0;

 `ifndef I2C_HIER
    `define I2C_HIER $root.tb.dut.i2c_core
  `endif

  assign thigh           = `I2C_HIER.reg2hw.timing0.thigh.q;
  assign tlow            = `I2C_HIER.reg2hw.timing0.tlow.q;
  assign t_r             = `I2C_HIER.reg2hw.timing1.t_r.q;
  assign t_f             = `I2C_HIER.reg2hw.timing1.t_f.q;
  assign tsu_sta         = `I2C_HIER.reg2hw.timing2.tsu_sta.q;
  assign thd_sta         = `I2C_HIER.reg2hw.timing2.thd_sta.q;
  assign tsu_dat         = `I2C_HIER.reg2hw.timing3.tsu_dat.q;
  assign thd_dat         = `I2C_HIER.reg2hw.timing3.thd_dat.q;
  assign tsu_sto         = `I2C_HIER.reg2hw.timing4.tsu_sto.q;
  assign host_mode_en    = `I2C_HIER.reg2hw.ctrl.enablehost.q;
  assign sda_interference_intr_en = `I2C_HIER.reg2hw.intr_enable.sda_interference;
  assign scl_interference_intr_en = `I2C_HIER.reg2hw.intr_enable.scl_interference;
  assign sda_unstable_intr_en = `I2C_HIER.reg2hw.intr_enable.sda_unstable;

  assign start_detected  = scl_q && scl_i && sda_q && !sda_i;
  assign stop_detected   = scl_q && scl_i && !sda_q && sda_i;
  assign posedge_scl     = !scl_q && scl_i;
  assign negedge_scl     = scl_q && !scl_i;
  // Interrupt triggers
  assign sda_interference_intr_trigger = scl_i && scl_q && !sda_i && !cio_sda_en_o &&
            host_transmit_mode;
  assign sda_unstable_intr_trigger = !host_transmit_mode &&
                                     !stop_detected && // Ignore Stop condition
                                     !start_detected && // Ignore Start condition
                                     scl_q && scl_i &&  // SCL high
                                     sda_q != sda_i; // SDA toggle

  // Sample the clock and data lines
  always@(posedge clk_i or negedge rst_ni) begin
    if(!rst_ni) begin
      sda_q <= 1'b1;
      scl_q <= 1'b1;
    end
    else begin
      sda_q <= sda_i;
      scl_q <= scl_i;
    end
  end

  // Block to keep track of when intr_sda_interference_o is expected to assert
  initial begin
    sda_interference_intr_expected = 0;
    forever begin
      @(posedge sda_interference_intr_trigger);
      sda_interference_intr_expected = 1;
      repeat (EVENT_TO_INTR_DELAY) @(posedge clk_i);
      sda_interference_intr_expected = 0;
    end
  end

  // Block to keep track of when intr_sda_unstable_o is expected to assert
  initial begin
    sda_unstable_intr_expected = 0;
    forever begin
      @(posedge sda_unstable_intr_trigger);
      sda_unstable_intr_expected = 1;
      repeat (EVENT_TO_INTR_DELAY) @(posedge clk_i);
        sda_unstable_intr_expected = 0;
    end
  end

  // Block to keep track of the bus state and whether Host or device is transmitting data
  // Host drives SDA line in the following states
  // - Address byte
  // - Read data ACK/NACK
  // - Write data
  always @(posedge clk_i) begin
    if (!rst_ni) begin
      bit_count = 0;
      byte_count = 0;
      host_transmit_mode = 0;
      rwbit = 0;
      active_transmission = 0;
    end else begin
      // Start of Stop condition detected
      if (start_detected || stop_detected) begin
        active_transmission = start_detected && !stop_detected;
        bit_count = 0;
        byte_count = 0;
        host_transmit_mode = 1;
        rwbit = 0;
      end else begin
        if (posedge_scl) begin
          case (bit_count) inside
            'd0 : begin
              if (byte_count == 0 ) begin
                host_transmit_mode = 1; // Address byte transmission
                end else begin
                host_transmit_mode = !rwbit; // Data byte transmission
              end
              bit_count++;
            end
            ['d1:'d6]: begin
              host_transmit_mode = !rwbit; // Data or Address byte transmission
              bit_count++;
            end
            'd7: begin
              if (byte_count == 0) begin
                rwbit = sda_i; // Read or Write bit
              end
              bit_count++;
            end
            'd8: begin
              if (byte_count == 0) begin
                host_transmit_mode = 0; // NACK or ACK bit from Device
              end else begin
                host_transmit_mode = rwbit; // NACK or ACK bit from Host
              end
              bit_count = 0;
              byte_count++;
            end
          endcase
        end
      end
    end
  end

  // Block to keep track of High and Low period of SCL
  always @(posedge clk_i) begin
    if (!rst_ni) begin
      scl_high_period = 0;
      scl_low_period = 0;
    end else begin
      if (scl_i) begin
        if (scl_low_period > 0) scl_low_period = 0;
        scl_high_period++;
      end else begin
        if (scl_high_period > 0) scl_high_period = 0;
        scl_low_period++;
      end
    end
  end

  // Block to keep track of when intr_scl_interference_o is expected to assert
  initial begin
    scl_interference_intr_expected = 0;
    forever begin
      @(posedge scl_interference_intr_trigger);
      scl_interference_intr_expected = 1;
      repeat (EVENT_TO_INTR_DELAY) @(posedge clk_i);
        scl_interference_intr_expected = 0;
      end
  end

  // Block to update trigger for scl interference
  always@(scl_i or negedge rst_ni) begin
    if (!rst_ni) begin
      scl_interference_intr_trigger = 0;
    end
    else begin
      scl_interference_intr_trigger =  (posedge_scl && scl_low_period < tlow) ||
                                       (negedge_scl && scl_high_period < thigh);
    end
  end

  // SCL and SDA interference
  // When the I2C module is in transmit mode, the scl_interference or sda_interference
  // interrupts will be asserted if the IP identifies that some other device (host or target)
  // on the bus is forcing either signal low and interfering with the transmission.
  // It should be noted that the scl_interference interrupt is not raised in the case when
  // the target device is stretching the clock. (However, it may be raised if the target allows
  // SCL to go high and then pulls SCL down before the end of the current clock cycle.)

  // Check for SDA interference interrupt when host is transmitting data
  property sda_interference_intr_p;
    @(posedge clk_i)
    disable iff (!rst_ni || !host_mode_en || !sda_interference_intr_en || !active_transmission)
    // When SCL is high during data transmission mode,
    // SDA should not be driven low by any other device on the bus
    // if not so, intr_sda_interference_o should be asserted within 5 cycles
    sda_interference_intr_trigger |-> ##[1:EVENT_TO_INTR_DELAY] intr_sda_interference_o;
  endproperty

  // Checks for faulty assertion of sda_interference interrupt when host is not transmitting data
  property sda_interference_intr_no_assert_p;
    @(posedge clk_i) disable iff (!rst_ni || !host_mode_en || !sda_interference_intr_en ||
                                  !active_transmission)
    // intr_sda_interference_o should not be asserted when trigger event is not detected
    $rose(intr_sda_interference_o) |-> sda_interference_intr_expected;
  endproperty

  I2C_SDA_INTERFERENCE_ASSERT : assert property(sda_interference_intr_p) else begin
    $error("SDA interference interrupt expected but not raised");
  end

  I2C_SDA_INTERFERENCE_NO_ASSERT : assert property(sda_interference_intr_no_assert_p) else begin
    $error("SDA interference interrupt raised when not expected");
  end

  // SCL interference assertion
  // If SCL is pulled low during an SCL pulse which has already started,
  // this interruption of the SCL pulse will be registered as an exception by the I2C core, which
  // will then assert the scl_interference interrupt
  property scl_interference_intr_p;
    @(posedge clk_i) disable iff (!host_mode_en || !active_transmission ||
      !scl_interference_intr_en || !rst_ni)
    // SCL should be high for at least thigh cycles after posedge of SCL
    // SCL should be low for at least tlow cycles after negedge of SCL
    scl_interference_intr_trigger |-> ##[1:EVENT_TO_INTR_DELAY] intr_scl_interference_o;
  endproperty

  property scl_interference_intr_no_assert_p;
    @(posedge clk_i) disable iff (!host_mode_en || !active_transmission ||
      !scl_interference_intr_en || !rst_ni)
    // intr_scl_interference_o should not be asserted when trigger event is not detected
    $rose(intr_scl_interference_o) |=> scl_interference_intr_expected;
  endproperty

  I2C_SCL_INTERFERENCE_ASSERT : assert property(scl_interference_intr_p) else begin
    $error("SCL interference interrupt expected but not raised");
  end

  I2C_SCL_INTERFERENCE_NO_ASSERT : assert property(scl_interference_intr_no_assert_p) else begin
    $error("SCL interference interrupt raised when not expected");
  end

  // SDA unstable assertion
  // The sda_unstable interrupt is asserted if, when receiving data or acknowledgement pulse,
  // the value of the SDA signal does not remain constant over the duration of the SCL pulse.
  property sda_unstable_intr_p;
    @(posedge clk_i) disable iff (!host_mode_en || !active_transmission || !sda_unstable_intr_en ||
                                  !rst_ni)
    sda_unstable_intr_trigger |-> ##[1:EVENT_TO_INTR_DELAY] intr_sda_unstable_o;
  endproperty

  property sda_unstable_intr_no_assert_p;
    @(posedge clk_i) disable iff (!host_mode_en || !active_transmission || !sda_unstable_intr_en ||
                                  !rst_ni)
    // intr_sda_unstable_o should not be asserted when trigger event is not detected
    $rose(intr_sda_unstable_o) |=> sda_unstable_intr_expected;
  endproperty

  I2C_SDA_UNSTABLE_ASSERT : assert property(sda_unstable_intr_p) else begin
    $error("SDA unstable interrupt expected but not raised");
  end

  I2C_SDA_UNSTABLE_NO_ASSERT : assert property(sda_unstable_intr_no_assert_p) else begin
    $error("SDA unstable interrupt raised when not expected");
  end

  sequence dynamic_delay(count);
    int v;
    (1, v=count) ##0 first_match((1, v=v-1'b1) [*0:$] ##1 v<=0);
  endsequence

  // Timing assertions
  property start_condition_setup_timing_p;
    int cycle_count; // To count the number of cycles SDA is held high after posedge of SCL
    @(posedge clk_i) disable iff (!host_mode_en || !rst_ni)
    (scl_i && sda_i, cycle_count = 0) ##0 // initialize local variable; SCL and SDA high
    (scl_i && sda_i, cycle_count++)[*0:$] ##1 // SDA and SCL high
    (scl_i && sda_q && !sda_i, cycle_count++) |-> // Start condition
    cycle_count >= tsu_sta; // Setup time for Start condition
  endproperty

  property start_condition_hold_timing_p;
    int cycle_count; // To count the number of cycles SDA is held low before negedge of SCL
    @(posedge clk_i) disable iff (!host_mode_en || !rst_ni)
    (scl_i && sda_q && !sda_i, cycle_count = 0) |-> // Start condition
    (scl_i && !sda_i, cycle_count++)[*0:$] ##1 // SCL high and SDA low
    (!scl_i && scl_q && !sda_i, cycle_count++) ##0 // SCL negedge
    cycle_count >= thd_sta; // Hold time for Start condition
  endproperty

  property hold_time_sda_p;
    int cycle_count; // To count the number of cycles SDA is stable after negedge of SCL
    @(posedge clk_i) disable iff (!host_mode_en || !rst_ni)
    ((sda_q == sda_i) && scl_q && !scl_i, cycle_count = 0) |-> // SCL negedge
    ((sda_q == sda_i) && !scl_i, cycle_count++) [*0:$] ##0 // SDA stable and SCL low
    cycle_count >= thd_dat; // Hold time for Data bit
  endproperty

  property stop_condition_setup_timing_p;
    int cycle_count; // To count the number of cycles SDA is held low after posedge of SCL
    @(posedge clk_i) disable iff (!host_mode_en || !rst_ni)
    (scl_i && !sda_i, cycle_count = 0) ##0
    (scl_i && !sda_i, cycle_count++)[*0:$] ##1 // SCL high and SDA low
    (scl_i && !sda_q && sda_i, cycle_count++) |-> // Stop condition
    cycle_count >= tsu_sto; // Setup time for Stop condition
  endproperty

  I2C_SETUP_START_ASSERT : assert property(start_condition_setup_timing_p) else begin
    $error("Start condition setup timing violated");
  end

  I2C_HOLD_START_ASSERT : assert property(start_condition_hold_timing_p) else begin
    $error("Start condition hold timing violated");
  end

  I2C_HOLD_SDA_ASSERT : assert property(hold_time_sda_p) else begin
    $error("SDA hold timing violated");
  end

  I2C_SETUP_STOP_ASSERT : assert property(stop_condition_setup_timing_p) else begin
    $error("Stop condition setup timing violated");
  end

endmodule
