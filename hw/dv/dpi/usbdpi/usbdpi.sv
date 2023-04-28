// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// USBDPI -- act as a simple host for usbuart device

// Bits in LOG_LEVEL sets what is output on socket
// 0x01 -- monitor_usb (packet level)
// 0x02 -- more verbose monitor
// 0x08 -- bit level

module usbdpi #(
  parameter string NAME = "usb0",
  parameter int LOG_LEVEL = 1
)(
  input  logic clk_i,
  input  logic rst_ni,
  input  logic clk_48MHz_i,
  input  logic enable,
  output logic dp_en_p2d,
  output logic dp_p2d,
  input  logic dp_d2p,
  input  logic dp_en_d2p,
  output logic dn_en_p2d,
  output logic dn_p2d,
  input  logic dn_d2p,
  input  logic dn_en_d2p,
  output logic d_p2d,
  input  logic d_d2p,
  input  logic d_en_d2p,
  input  logic se0_d2p,
  input  logic rx_enable_d2p,
  input  logic tx_use_d_se0_d2p,

  output logic sense_p2d,
  input  logic pullupdp_d2p,
  input  logic pullupdn_d2p
);
  import "DPI-C" function
    chandle usbdpi_create(input string name, input int loglevel);

  import "DPI-C" function
    void usbdpi_device_to_host(input chandle ctx, input bit [10:0] d2p);

  import "DPI-C" function
    void usbdpi_close(input chandle ctx);

  import "DPI-C" function
    byte usbdpi_host_to_device(input chandle ctx, input bit [10:0] d2p);

  import "DPI-C" function
    void usbdpi_diags(input chandle ctx, output bit [95:0] diags);

  chandle ctx;

  initial begin
    ctx = usbdpi_create(NAME, LOG_LEVEL);
  end

  final begin
    usbdpi_close(ctx);
  end

  // USB Packet IDentifier values, for waveform viewing
  typedef enum bit [7:0] {
    OUT = 8'hE1,
    IN = 8'h69,
    SOF = 8'hA5,
    SETUP = 8'h2D,
    DATA0 = 8'hC3,
    DATA1 = 8'h4B,
    ACK = 8'hD2,
    NAK = 8'h5A,
    STALL = 8'h1E,
    NYET = 8'h96,
    PING = 8'hB4
  } usb_pid_t;

  // Host state
  // Note: MUST be kept consistent with usbdpi_host_state_t in usbdpi.h
  typedef enum bit [4:0] {
    HS_STARTFRAME = 0,
    HS_WAITACK = 1,
    HS_SET_DATASTAGE = 2,
    HS_DS_RXDATA = 3,
    HS_DS_SENDACK = 4,
    HS_DONEDADR = 5,
    HS_REQDATA = 6,
    HS_WAITDATA = 7,
    HS_SENDACK = 8,
    HS_WAIT_PKT = 9,
    HS_ACKIFDATA = 10,
    HS_SENDHI = 11,
    HS_EMPTYDATA = 12,
    HS_WAITACK2 = 13,
    HS_STREAMOUT = 14,
    HS_STREAMIN = 15,
    HS_NEXTFRAME = 16,
    HS_ERROR = 17
  } usbdpi_host_state_t;

  // Bus state
  // Note: MUST be kept consistent with usbdpi_bus_state in usbdpi.h
  typedef enum bit [4:0] {
    kUsbIdle = 0,
    kUsbControlSetup,
    kUsbControlSetupAck,
    kUsbControlDataOut,
    kUsbControlDataOutAck,  // 4
    kUsbControlStatusInToken,
    kUsbControlStatusInData,
    kUsbControlStatusInAck,

    kUsbControlDataInToken,  // 8
    kUsbControlDataInData,
    kUsbControlDataInAck,
    kUsbControlStatusOut,
    kUsbControlStatusOutAck,  // 0xc

    // Isochronous Transfers
    kUsbIsoOut,
    kUsbIsoInToken,
    kUsbIsoInData,

    // Bulk Transfers
    kUsbBulkOut,  // 0x10
    kUsbBulkOutAck,
    kUsbBulkInToken,
    kUsbBulkInData,

    // Interrupt transfers
    kUsbInterruptOut,  // 0x14
    kUsbInterruptOutAck,
    kUsbInterruptInToken,
    kUsbInterruptInData
  } usbdpi_bus_state_t;

  // USB monitor state
  // Note: MUST be kept consistent with usbdpi_monitor_state_t in usb_monitor.c
  typedef enum bit [1:0] {
    MS_IDLE = 0,
    MS_GET_PID,
    MS_GET_BYTES
  } usb_monitor_state_t;

  // USB driver state
  // Note: MUST be kept consistent with usbdpi_drv_state_t in usbdpi.h
  typedef enum bit [3:0] {
    ST_IDLE = 0,
    ST_SEND = 1,
    ST_GET = 2,
    ST_SYNC = 3,
    ST_EOP = 4,
    ST_EOP0 = 5
  } usbdpi_drv_state_t;

  // Test steps
  typedef enum bit [6:0] {

    STEP_BUS_RESET = 7'h0,
    STEP_SET_DEVICE_ADDRESS,
    STEP_GET_DEVICE_DESCRIPTOR,
    STEP_GET_CONFIG_DESCRIPTOR,
    STEP_GET_FULL_CONFIG_DESCRIPTOR,
    STEP_SET_DEVICE_CONFIG,

    STEP_GET_TEST_CONFIG,
    STEP_SET_TEST_STATUS,

    // usbdev_test
    STEP_FIRST_READ,
    STEP_READ_BAUD,
    STEP_SECOND_READ,
    STEP_SET_BAUD,
    STEP_THIRD_READ,
    STEP_TEST_ISO1,
    STEP_TEST_ISO2,
    STEP_ENDPT_UNIMPL_SETUP,
    STEP_ENDPT_UNIMPL_OUT,
    STEP_ENDPT_UNIMPL_IN,
    STEP_DEVICE_UK_SETUP,
    STEP_IDLE_START,
    STEP_IDLE_END = STEP_IDLE_START + 7'h4,

    // usbdev_stream_test
    STEP_STREAM_SERVICE = 7'h20,

    // Disconnect the device and stop
    STEP_BUS_DISCONNECT = 7'h7f
  } usbdpi_test_step_t;

  // Make usb_monitor diagnostic information viewable in waveforms
  bit [9:0] c_spare1;
  usb_monitor_state_t c_mon_state;
  bit [3:0] c_mon_bits;
  bit [7:0] c_mon_byte;
  usb_pid_t c_mon_pid;
  // Make usbdpi diagnostic information viewable in waveforms
  usbdpi_test_step_t c_step;
  usbdpi_bus_state_t c_bus_state;
  bit [31:0] c_tickbits;
  bit [10:0] c_frame;
  usbdpi_host_state_t c_hostSt;
  usbdpi_drv_state_t c_state;
  always @(posedge clk_48MHz_i)
    usbdpi_diags(ctx, {c_spare1, c_mon_state, c_mon_bits, c_mon_byte, c_mon_pid,
                       c_step, c_bus_state, c_tickbits, c_frame, c_hostSt,
                       c_state});

  logic [10:0] d2p;
  logic [10:0] d2p_r;
  logic       unused_dummy;
  logic       unused_clk = clk_i;
  logic       unused_rst = rst_ni;
  logic       dp_int, dn_int, d_last;
  logic       flip_detect, pullup_detect, rx_enable;

  // Detect a request to flip pins by the DN resistor being applied;
  //   it's a full speed device so the pullup resistor is on the D+ signal
  assign flip_detect = pullupdn_d2p;
  assign pullup_detect = pullupdp_d2p || pullupdn_d2p;
  assign rx_enable = rx_enable_d2p;

  assign d2p = {dp_d2p, dp_en_d2p, dn_d2p, dn_en_d2p, d_d2p, d_en_d2p, se0_d2p, tx_use_d_se0_d2p,
                pullupdp_d2p, pullupdn_d2p, rx_enable};
  always_ff @(posedge clk_48MHz_i or negedge rst_ni) begin
    if (!rst_ni) begin
      sense_p2d <= 1'b0;
      dp_en_p2d <= 1'b0;
      dn_en_p2d <= 1'b0;
      d_last <= 0;
      dp_int <= 0;
      dn_int <= 0;
    end else if (enable) begin
      if (!sense_p2d || pullup_detect) begin
        automatic byte p2d = usbdpi_host_to_device(ctx, d2p);
        d_last <= d_p2d;
        dp_en_p2d <= p2d[4];
        dn_en_p2d <= p2d[4];
        dp_int <= p2d[2];
        dn_int <= p2d[1];
        sense_p2d <= p2d[0];
        unused_dummy <= |p2d[7:5];
        d2p_r <= d2p;
        if (d2p_r != d2p) begin
          usbdpi_device_to_host(ctx, d2p);
        end
      end else begin
        d_last <= 0;
        dp_int <= 0;
        dn_int <= 0;
      end
    end
  end

  always_comb begin : proc_data
    d_p2d = d_last;
    if (rx_enable) begin
      // Differential receiver is enabled.
      // If host is driving, update d_p2d only if there is a valid differential
      // value.
      if (d_en_d2p) begin
        d_p2d = d_d2p;
      end else if (dp_int && !dn_int) begin
        d_p2d = 1'b1;
      end else if (!dp_int && dn_int) begin
        d_p2d = 1'b0;
      end
    end
    if (dp_en_d2p) begin
      if (tx_use_d_se0_d2p) begin
        dp_p2d = se0_d2p ? 1'b0 : flip_detect ^ d_d2p;
      end else begin
        dp_p2d = dp_d2p;
      end
    end else begin
      dp_p2d = dp_int;
    end
    if (dn_en_d2p) begin
      if (tx_use_d_se0_d2p) begin
        dn_p2d = se0_d2p ? 1'b0 : flip_detect ^ ~d_d2p;
      end else begin
        dn_p2d = dn_d2p;
      end
    end else begin
      dn_p2d = dn_int;
    end
  end
endmodule
