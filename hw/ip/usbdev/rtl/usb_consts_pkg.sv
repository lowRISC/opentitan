// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

package usb_consts_pkg;

  // Definitions for USB Packet Identifier (called PID in the spec)

  // Bottom two bits of the PID are type
  typedef enum logic [1:0] {
    UsbPidTypeSpecial    = 2'b00,
    UsbPidTypeToken      = 2'b01,
    UsbPidTypeHandshake  = 2'b10,
    UsbPidTypeData       = 2'b11
  } usb_pid_type_e;

  // Direct from USB 2.0 Spec Table 8-1
  typedef enum logic [3:0] {
    // TOKEN
    UsbPidOut   = 4'b0001,
    UsbPidIn    = 4'b1001,
    UsbPidSof   = 4'b0101,
    UsbPidSetup = 4'b1101,
    // DATA
    UsbPidData0 = 4'b0011,
    UsbPidData1 = 4'b1011,
    UsbPidData2 = 4'b0111, // Only valid for High Speed
    UsbPidMData = 4'b1111, // Only valid for High Speed
    // HANDSHAKE
    UsbPidAck   = 4'b0010,
    UsbPidNak   = 4'b1010,
    UsbPidStall = 4'b1110,
    UsbPidNyet  = 4'b0110
  } usb_pid_e;


  // USB SETUP packet commands (USB2.0 Table 9-4)
  typedef enum logic [7:0] {
    SetupGetStatus        = 8'd0,
    SetupClearFeature     = 8'd1,
    SetupSetFeature       = 8'd3,
    SetupSetAddress       = 8'd5,
    SetupGetDescriptor    = 8'd6,
    SetupSetDescriptor    = 8'd7,
    SetupGetConfiguration = 8'd8,
    SetupSetConfiguration = 8'd9,
    SetupGetInterface     = 8'd10,
    SetupSetInterface     = 8'd11,
    SetupSynchFrame       = 8'd12
  } usb_setup_request_e;

  // USB Descriptor Types (USB2.0 Table 9-5)
  typedef enum logic [7:0] {
    DscrTypeDevice        = 8'd1,
    DscrTypeConfiguration = 8'd2,
    DscrTypeString        = 8'd3,
    DscrTypeInterface     = 8'd4,
    DscrTypeEndpoint      = 8'd5,
    DscrTypeDevQual       = 8'd6,
    DscrTypeOthrSpd       = 8'd7,
    DscrTypeIntPwr        = 8'd8
  } usb_dscr_type_e;

endpackage
