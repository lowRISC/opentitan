// Copyright lowRISC contributors.
// Copyright Luke Valenty (TinyFPGA project)
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Converted from common/usb_serial_ctrl_ep.v
// -- move from CDC to Google simple serial protocol
// -- conform to lowRISC coding style

module usb_serial_ctrl_ep  #(
  parameter int unsigned MaxPktSizeByte = 32,

  // Derived parameters
  localparam int unsigned PktW = $clog2(MaxPktSizeByte)
) (
  input              clk_i,
  input              rst_ni,
  output logic [6:0] dev_addr,

  ////////////////////////////
  // out endpoint interface //
  ////////////////////////////
  input              out_ep_data_put_i,
  input [PktW - 1:0] out_ep_put_addr_i,
  input [7:0]        out_ep_data_i,
  input              out_ep_acked_i,
  input              out_ep_rollback_i,
  input              out_ep_setup_i,
  output logic       out_ep_full_o,
  output logic       out_ep_stall_o,


  ///////////////////////////
  // in endpoint interface //
  ///////////////////////////
  input              in_ep_rollback_i,
  input              in_ep_acked_i,
  input [PktW - 1:0] in_ep_get_addr_i,
  input              in_ep_data_get_i,
  output logic       in_ep_stall_o,
  output logic       in_ep_has_data_o,
  output logic [7:0] in_ep_data_o,
  output logic       in_ep_data_done_o
);

  // suppress errors
  logic                unused_1;
  logic [PktW-1:0]     unused_2;
  assign unused_1 = in_ep_rollback_i;
  assign unused_2 = in_ep_get_addr_i;

  import usb_consts_pkg::*;

  // State machine for control transfers
  typedef enum logic [2:0] {
    StIdle      = 3'h0,
    StSetup     = 3'h1,
    StDataIn    = 3'h2,
    StDataOut   = 3'h3,
    StStatusIn  = 3'h4,
    StStatusOut = 3'h5
  } state_ctrl_xfr_e;

  state_ctrl_xfr_e ctrl_xfr_state;
  state_ctrl_xfr_e ctrl_xfr_state_next;
  logic setup_stage_end;
  logic status_stage_end;
  logic send_zero_length_data_pkt;

  // the default control endpoint gets assigned the device address
  logic [6:0] dev_addr_int;
  logic [6:0] new_dev_addr;

  assign dev_addr = dev_addr_int;

  assign out_ep_stall_o = 1'b0;
  assign out_ep_full_o = 1'b0;

  // keep track of new out data start and end
  logic pkt_start;
  logic pkt_end;

  assign pkt_start = (out_ep_put_addr_i == 0) && out_ep_data_put_i;
  assign pkt_end = out_ep_acked_i || out_ep_rollback_i;

  // need to record the 8 bytes of setup data
  logic [7:0] bmRequestType, raw_setup_data [8];
  // Alias for the setup bytes using names from USB spec
  usb_setup_request_e bRequest;
  logic [15:0] wValue, wLength, wIndex;

  logic setup_pkt_start, has_data_stage, out_data_stage, in_data_stage;
  assign setup_pkt_start = pkt_start && out_ep_setup_i;
  assign has_data_stage = wLength != 16'h0;
  assign out_data_stage = has_data_stage && !bmRequestType[7];
  assign in_data_stage = has_data_stage && bmRequestType[7];

  logic [7:0] bytes_sent;
  logic [6:0] rom_length;
  logic all_data_sent, more_data_to_send, in_data_transfer_done;

  // if any upper bits in wLength are set the rom_length will trigger first
  // here any request for >127 will generate a check based on >128
  assign all_data_sent = (bytes_sent >= {1'b0, rom_length}) ||
                         (bytes_sent >= {|wLength[15:7], wLength[6:0]});

  assign more_data_to_send = !all_data_sent;

  rising_edge_detector detect_in_data_transfer_done (
    .clk_i (clk_i),
    .rst_ni(rst_ni),
    .in_i  (all_data_sent),
    .out_o (in_data_transfer_done)
  );

  assign in_ep_has_data_o = more_data_to_send || send_zero_length_data_pkt;
  assign in_ep_data_done_o = (in_data_transfer_done && (ctrl_xfr_state == StDataIn)) ||
                           send_zero_length_data_pkt;

  logic [6:0] rom_addr;
  logic save_dev_addr;
  ////////////////////////////////////
  // control transfer state machine //
  ////////////////////////////////////

  always_comb begin
    setup_stage_end = 1'b0;
    status_stage_end = 1'b0;
    send_zero_length_data_pkt = 1'b0;

    unique case (ctrl_xfr_state)
      StIdle: begin
        if (setup_pkt_start) begin
          ctrl_xfr_state_next = StSetup;
        end else begin
          ctrl_xfr_state_next = StIdle;
        end
      end

      StSetup: begin
        if (pkt_end) begin
          // rollback here is most likely a CRC error on the SETUP packet
          if (out_ep_rollback_i) begin
            ctrl_xfr_state_next = StIdle;
          end else if (in_data_stage) begin
            ctrl_xfr_state_next = StDataIn;
            setup_stage_end = 1'b1;
          end else if (out_data_stage) begin
            ctrl_xfr_state_next = StDataOut;
            setup_stage_end = 1'b1;
          end else begin
            ctrl_xfr_state_next = StStatusIn;
            send_zero_length_data_pkt = 1'b1;
            setup_stage_end = 1'b1;
          end
        end else begin
          ctrl_xfr_state_next = StSetup;
        end
      end

      StDataIn: begin
        if (in_ep_stall_o) begin
          ctrl_xfr_state_next = StIdle;
          status_stage_end = 1'b1;
        end else if (in_ep_acked_i && all_data_sent) begin
          ctrl_xfr_state_next = StStatusOut;
        end else begin
          ctrl_xfr_state_next = StDataIn;
        end
      end

      StDataOut: begin
        if (out_ep_acked_i) begin
          ctrl_xfr_state_next = StStatusIn;
          send_zero_length_data_pkt = 1'b1;
        end else begin
          ctrl_xfr_state_next = StDataOut;
        end
      end

      StStatusIn: begin
        if (in_ep_acked_i) begin
          ctrl_xfr_state_next = StIdle;
          status_stage_end = 1'b1;
        end else begin
          ctrl_xfr_state_next = StStatusIn;
          send_zero_length_data_pkt = 1'b1;
        end
      end

      StStatusOut: begin
        if (out_ep_acked_i) begin
          ctrl_xfr_state_next = StIdle;
          status_stage_end = 1'b1;
        end else begin
          ctrl_xfr_state_next = StStatusOut;
        end
      end

      default begin
        ctrl_xfr_state_next = StIdle;
      end
    endcase
  end

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      ctrl_xfr_state <= StIdle;
    end else begin
      ctrl_xfr_state <= ctrl_xfr_state_next;
    end
  end

  assign bmRequestType = raw_setup_data[0];
  assign bRequest = usb_setup_request_e'(raw_setup_data[1]);
  assign wValue = {raw_setup_data[3][7:0], raw_setup_data[2][7:0]};
  assign wIndex = {raw_setup_data[5][7:0], raw_setup_data[4][7:0]};
  assign wLength = {raw_setup_data[7][7:0], raw_setup_data[6][7:0]};
  // suppress warning
  logic [6:0]  unused_bmR;
  logic        unused_wValue;
  logic [15:0] unused_wIndex;
  assign unused_bmR = bmRequestType[6:0];
  assign unused_wValue = wValue[7];
  assign unused_wIndex = wIndex;

  // Check of upper put_addr bits needed because CRC will be sent (10 bytes total)
  always_ff @(posedge clk_i) begin
    if (out_ep_setup_i && out_ep_data_put_i && (out_ep_put_addr_i[PktW - 1:3] == '0)) begin
      raw_setup_data[out_ep_put_addr_i[2:0]] <= out_ep_data_i;
    end
  end

  // Send setup data (which will be empty in case of a SET operation and
  // come from the ROM in the case of a GET)
  usb_dscr_type_e dscr_type;
  assign dscr_type = usb_dscr_type_e'(wValue[15:8]);
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      dev_addr_int <= '0;
      save_dev_addr <= 1'b0;
      in_ep_stall_o <= 1'b0;
    end else begin
      if (setup_stage_end) begin
        bytes_sent <= '0;
        // Command (bRequest) and sub-command (wValue) come from USB spec
        unique case (bRequest)
          SetupGetDescriptor: begin
            unique case (dscr_type)
              DscrTypeDevice: begin
                in_ep_stall_o <= 1'b0;
                rom_addr      <= 7'h00;
                rom_length    <= 7'h12;
              end

              DscrTypeConfiguration: begin
                in_ep_stall_o <= 1'b0;
                rom_addr      <= 7'h12;
                rom_length    <= 7'h20; // 9+9+7+7
              end

              DscrTypeDevQual: begin
                in_ep_stall_o <= 1'b1;
                rom_addr      <= 7'h00;
                rom_length    <= 7'h00;
              end

              default begin
                in_ep_stall_o <= 1'b0;
                rom_addr      <= 7'h00;
                rom_length    <= 7'h00;
              end
            endcase
          end

          SetupSetAddress: begin
            in_ep_stall_o <= 1'b0;
            rom_addr      <= 7'h00;
            rom_length    <= 7'h00;

            // we need to save the address after the status stage ends
            // this is because the status stage token will still be using
            // the old device address
            save_dev_addr <= 1'b1;
            new_dev_addr <= wValue[6:0];
          end

          SetupSetConfiguration: begin
            in_ep_stall_o <= 1'b0;
            rom_addr      <= 7'h00;
            rom_length    <= 7'h00;
          end

          default begin
            in_ep_stall_o <= 1'b0;
            rom_addr      <= 7'h00;
            rom_length    <= 7'h00;
          end
        endcase
      end else if ((ctrl_xfr_state == StDataIn) && more_data_to_send && in_ep_data_get_i) begin
        rom_addr   <= rom_addr + 7'h1;
        bytes_sent <= bytes_sent + 8'h1;
      end else if (status_stage_end) begin
        bytes_sent <= '0;
        rom_addr <= '0;
        rom_length <= '0;
        if (save_dev_addr) begin
          save_dev_addr <= 1'b0;
          dev_addr_int <= new_dev_addr;
        end
      end
    end
  end

  always_comb begin
    unique case (rom_addr)
      // device descriptor
      'h000: in_ep_data_o = 8'd18;   // bLength
      'h001: in_ep_data_o = {DscrTypeDevice};    // bDescriptorType
      'h002: in_ep_data_o = 8'h00; // bcdUSB[0]
      'h003: in_ep_data_o = 8'h02; // bcdUSB[1]
      'h004: in_ep_data_o = 8'h00; // bDeviceClass (defined at interface level)
      'h005: in_ep_data_o = 8'h00; // bDeviceSubClass
      'h006: in_ep_data_o = 8'h00; // bDeviceProtocol
      'h007: in_ep_data_o = 8'd32;   // bMaxPacketSize0

      'h008: in_ep_data_o = 8'hd1; // idVendor[0] 0x18d1 Google Inc.
      'h009: in_ep_data_o = 8'h18; // idVendor[1]
      'h00A: in_ep_data_o = 8'h39; // idProduct[0] Simple Serial USB IP
      'h00B: in_ep_data_o = 8'h50; // idProduct[1] (Allocated in Chrome OS block for this IP)

      'h00C: in_ep_data_o = 8'h0;    // bcdDevice[0]
      'h00D: in_ep_data_o = 8'h1;  // bcdDevice[1]
      'h00E: in_ep_data_o = 8'h0;    // iManufacturer
      'h00F: in_ep_data_o = 8'h0;    // iProduct
      'h010: in_ep_data_o = 8'h0;    // iSerialNumber
      'h011: in_ep_data_o = 8'h1;    // bNumConfigurations

      // configuration descriptor
      'h012: in_ep_data_o = 8'd9;    // bLength
      'h013: in_ep_data_o = {DscrTypeConfiguration};    // bDescriptorType
      'h014: in_ep_data_o = 8'(9+9+7+7); // wTotalLength[0]
      'h015: in_ep_data_o = 8'h0;    // wTotalLength[1]
      'h016: in_ep_data_o = 8'h1;    // bNumInterfaces
      'h017: in_ep_data_o = 8'h1;    // bConfigurationValue
      'h018: in_ep_data_o = 8'h0;    // iConfiguration
      'h019: in_ep_data_o = 8'hC0; // bmAttributes: must-be-one, self-powered
      'h01A: in_ep_data_o = 8'd50;   // bMaxPower

      // interface descriptor, USB spec 9.6.5, page 267-269, Table 9-12
      'h01B: in_ep_data_o = 8'd9;    // bLength
      'h01C: in_ep_data_o = {DscrTypeInterface};    // bDescriptorType
      'h01D: in_ep_data_o = 8'h0;    // bInterfaceNumber
      'h01E: in_ep_data_o = 8'h0;    // bAlternateSetting
      'h01F: in_ep_data_o = 8'h2;    // bNumEndpoints (must follow below)
      'h020: in_ep_data_o = 8'hff; // bInterfaceClass (Vendor Specific Class)
      'h021: in_ep_data_o = 8'h50; // bInterfaceSubClass (Simple serial)
      'h022: in_ep_data_o = 8'h1;    // bInterfaceProtocol (standard)
      'h023: in_ep_data_o = 8'h0;    // iInterface

      // endpoint descriptor, USB spec 9.6.6, page 269-271, Table 9-13
      'h024: in_ep_data_o = 8'd7;    // bLength
      'h025: in_ep_data_o = {DscrTypeEndpoint};    // bDescriptorType
      'h026: in_ep_data_o = 8'h1;    // bEndpointAddress, OUT
      'h027: in_ep_data_o = 8'h02; // bmAttributes (0x02=bulk, data)
      'h028: in_ep_data_o = 8'd32;   // wMaxPacketSize[0]
      'h029: in_ep_data_o = 8'h0;    // wMaxPacketSize[1]
      'h02A: in_ep_data_o = 8'h0;    // bInterval

      // endpoint descriptor, USB spec 9.6.6, page 269-271, Table 9-13
      'h02B: in_ep_data_o = 8'd7;    // bLength
      'h02C: in_ep_data_o = {DscrTypeEndpoint};    // bDescriptorType
      'h02D: in_ep_data_o = 8'h81; // bEndpointAddress, IN
      'h02E: in_ep_data_o = 8'h02; // bmAttributes (0x02=bulk, data)
      'h02F: in_ep_data_o = 8'd32;   // wMaxPacketSize[0]
      'h030: in_ep_data_o = 8'h0;    // wMaxPacketSize[1]
      'h031: in_ep_data_o = 8'h4;    // bInterval (4 vs 10 in twinkie)

      default begin
        in_ep_data_o = 0;
      end
    endcase
  end

endmodule
