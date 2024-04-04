// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Covergroups for I2C protocol transitions
module i2c_protocol_cov(
  input                    clk,
  input                    rst_n,
  // I2C IO
  input wire               scl,
  input wire               sda,
  input wire               intr_cmd_complete,
  input wire               intr_tx_stretch
);
  localparam int NUM_I2C_ADDR_BITS = 7;

  typedef enum {
    Idle,
    Start,
    RStart,
    Addr,
    Read,
    Write,
    ReadAddrACK,
    ReadAddrNACK,
    WriteAddrACK,
    WriteAddrNACK,
    ReadData,
    WriteData,
    ReadDataACK,
    ReadDataNACK,
    WriteDataACK,
    WriteDataNACK,
    Stop
  } bus_state_e;

  logic sda_q, scl_q;
  // I2C registers required for assertions
  logic host_mode_en;
  logic [15:0] thigh;
  logic [15:0] tlow;
  logic [15:0] t_r;
  logic [15:0] t_f;

  logic stop_detected = 0;

  bus_state_e bus_state_q, bus_state_d, current_txn_start;
  int num_addr_bits_seen = 0;
  int num_data_bits_seen = 0;
  int num_wr_bytes = 0;
  int num_rd_bytes = 0;
  bit [NUM_I2C_ADDR_BITS-1:0] address;
  bit [NUM_I2C_ADDR_BITS-1:0] address_0_mask;
  bit [NUM_I2C_ADDR_BITS-1:0] address_1_mask;
  bit [NUM_I2C_ADDR_BITS-1:0] address_0_val;
  bit [NUM_I2C_ADDR_BITS-1:0] address_1_val;
  wire address_match;
  bit write_txn;
  bit read_txn;
  bit [7:0] fbyte;

  `ifndef I2C_HIER
    `define I2C_HIER $root.tb.dut.i2c_core
  `endif

  assign thigh           = `I2C_HIER.reg2hw.timing0.thigh.q;
  assign tlow            = `I2C_HIER.reg2hw.timing0.tlow.q;
  assign t_r             = `I2C_HIER.reg2hw.timing1.t_r.q;
  assign t_f             = `I2C_HIER.reg2hw.timing1.t_f.q;
  assign host_mode_en    = `I2C_HIER.reg2hw.ctrl.enablehost.q;
  assign address_0_mask  = `I2C_HIER.reg2hw.target_id.mask0;
  assign address_1_mask  = `I2C_HIER.reg2hw.target_id.mask1;
  assign address_0_val   = `I2C_HIER.reg2hw.target_id.address0;
  assign address_1_val   = `I2C_HIER.reg2hw.target_id.address1;

  assign address_match = ((address & address_0_mask) == address_0_val) ||
                         ((address & address_1_mask) == address_1_val);

  // Sample the clock and data lines
  always@(posedge clk or negedge rst_n) begin
    if(!rst_n) begin
      sda_q <= 1'b1;
      scl_q <= 1'b1;
    end
    else begin
      sda_q <= sda;
      scl_q <= scl;
    end
  end

  function automatic bit start();
    return scl && scl_q && sda_q && !sda;
  endfunction

  function automatic bit stop();
    return scl && scl_q && !sda_q && sda;
  endfunction

  function automatic bit posedge_scl();
    return scl && !scl_q;
  endfunction

  // Flop the state value that was updated on 'scl' or 'sda' events.
  // This ensures that when we sample for coverage, we don't race against new events.
  always@(posedge clk or negedge rst_n) begin
    if(!rst_n) begin
      bus_state_q <= Idle;
    end else begin
      bus_state_q <= bus_state_d;
    end
  end

//////////////////////////////////
// This FSM updates 'bus_state_d' sensitive to events on 'sda' and 'scl'.
// The state is the flopped into 'bus_state_q' on the 'clk' signal
// (coverage is sampled on this signal)
// The values of 'bus_state_d' represent the last event detected on the bus.
//
// bus_state_d == Idle -> No active transactions on I2C bus
// bus_state_d == Start -> Detected a Start condition, and are waiting for the next
//                         bus event. In this case, we are waiting for the next posedge of scl, at
//                         which point we sample sda as the first bit of the address and move to the
//                         'Addr' state.
// bus_state_d == Stop -> Detected a Stop condition, 'bus_state_d' will be reset to Idle to make sure
//                        further requests are sampled.
// bus_state_d == Addr -> Sample Address data bytes on every posedge_scl() until complete address is
//                        captured.
// bus_state_d == Read -> Detected a 'Read' event. ('sda' == '1' on posedge_scl() after
//                        all 7 addr bits). We are now waiting for the next posedge_scl() event,
//                        which would represent an ACK or NACK. Upon observing an ACK 'bus_state_d'
//                        will be updated to ReadAddrACK else Idle.
// bus_state_d == Write -> Detected a 'Write' event. ('sda' == '0' on posedge_scl() after
//                         all 7 addr bits). We are now waiting for the next posedge_scl() event,
//                         which would represent an ACK or NACK. Upon observing an ACK 'bus_state_d'
//                         will be updated to WriteAddrACK else Idle.
// bus_state_d == WriteAddrACK -> Detected a ACK response for Write Address byte and 'bus_state_d'
//                                will be updated to WriteData.
// bus_state_d == ReadAddrACK -> Detected a ACK response for Read Address byte and 'bus_state_d' will
//                               be updated to ReadData.
// bus_state_d == ReadData -> Sample read data bytes on every posedge_scl() until complete byte is
//                            captured.
// bus_state_d == WriteData -> Sample write data bytes on every posedge_scl() until complete byte is
//                             captured.
// bus_state_d == ReadDataACK -> Detected a ACK response for Read data byte and 'bus_state_d'
//                               will be updated to ReadData to capture next byte
// bus_state_d == WriteDataACK -> Detected a ACK response for Write data byte and 'bus_state_d'
//                                will be updated to WriteData to capture next byte
// bus_state_d == WriteDataNACK -> Detected a NACK response for Write data byte. FSM remains in the
//                                 state unless Start or Stop condition is detected
// bus_state_d == ReadDataNACK -> Detected a NACK response for Read data byte. FSM remains in the
//                                state unless Start or Stop condition is detected
//////////////////////////////////
  always@(scl or sda or scl_q or sda_q) begin
    if(!rst_n) begin
      bus_state_d = Idle;
      num_addr_bits_seen = 0;
      num_data_bits_seen = 0;
      stop_detected = 1; // initially bus is in stop/Idle state
      num_rd_bytes = 0;
      num_wr_bytes = 0;
      address = {NUM_I2C_ADDR_BITS{1'b0}};
      current_txn_start = Start;
      write_txn = 0;
      read_txn = 0;
    end else if (start()) begin // Start
      bus_state_d = stop_detected ? Start : RStart;
      num_addr_bits_seen = 0;
      num_data_bits_seen = 0;
      stop_detected = 0;
      num_rd_bytes = 0;
      num_wr_bytes = 0;
      address = {NUM_I2C_ADDR_BITS{1'b0}};
      current_txn_start = bus_state_d;
    end else if (stop()) begin // Stop
      bus_state_d = Stop;
      num_addr_bits_seen = 0;
      num_data_bits_seen = 0;
      stop_detected = 1;
      num_rd_bytes = 0;
      num_wr_bytes = 0;
      address = {NUM_I2C_ADDR_BITS{1'b0}};
    end else if(posedge_scl()) begin
      case(bus_state_d)
        Idle: begin // Remain in the same state
          bus_state_d = Idle;
        end
        // We are in this state after we received a start.
        Start, RStart: begin
          bus_state_d = Addr;
          // Since MSB os address is NUM_I2C_ADDR_BITS, the update is on NUM_I2C_ADDR_BITS -1 bit
          address[NUM_I2C_ADDR_BITS - 1] = sda;
          num_addr_bits_seen = 1;
        end
        // We have already received one address bit and are waiting for the next 6 and the
        // read/write bit.
        Addr: begin
          if (num_addr_bits_seen < 7) begin
            // Updates to address variable must start from MSB
            address[(NUM_I2C_ADDR_BITS - 1) - num_addr_bits_seen] = sda;
            num_addr_bits_seen++;
          end else begin
            if (address_match) begin
              // We've received a read/write bit and are now waiting for an ack/nack
              bus_state_d = sda ? Read : Write;
              read_txn = sda ? 1 : 0;
              write_txn = sda ? 0 : 1;
            end else begin
              bus_state_d = Idle;
              write_txn = 0;
              read_txn = 0;
            end
            num_addr_bits_seen = 0;
          end
        end
        Read: begin
          bus_state_d = !sda ? ReadAddrACK : ReadAddrNACK;
          address = {NUM_I2C_ADDR_BITS{1'b0}};
        end
        Write: begin
          bus_state_d = !sda ? WriteAddrACK : WriteAddrNACK;
          address = {NUM_I2C_ADDR_BITS{1'b0}};
        end
        // We've received an ack and are waiting for the first data bit.
        ReadAddrACK: begin
          bus_state_d = ReadData;
          num_addr_bits_seen = 0;
          num_data_bits_seen = 1;
        end
        WriteAddrACK: begin
          bus_state_d = WriteData;
          num_addr_bits_seen = 0;
          num_data_bits_seen = 1;
        end
        ReadAddrNACK, WriteAddrNACK: begin
          // Remain in the same state if NACK is received
          bus_state_d = bus_state_d;
        end
        // We've already received 1 data bit and now waiting for the next 7 and the ack/nack.
        ReadData: begin
          if (num_data_bits_seen < 8) begin
            fbyte[num_data_bits_seen] = sda;
            num_data_bits_seen++;
          end else begin
            // Receiving ack/nack.
            bus_state_d = !sda ? ReadDataACK : ReadDataNACK;
            num_data_bits_seen = 0;
            num_rd_bytes++;
          end
        end
        WriteData: begin
          if (num_data_bits_seen < 8) begin
            fbyte[num_data_bits_seen] = sda;
            num_data_bits_seen++;
          end else begin
            bus_state_d = !sda ? WriteDataACK : WriteDataNACK;
            num_data_bits_seen = 0;
            num_wr_bytes++;
          end
        end
        // We've already received an ack/nack at this point, so waiting for the first bit of data
        // or a stop/rstart which are handled above this case statement.
        ReadDataACK, ReadDataNACK: begin
          // Remain in the same state if NACK is received, else move to ReadData
          bus_state_d = (bus_state_d != ReadDataNACK) ? ReadData : ReadDataNACK;
          num_addr_bits_seen = 0;
          num_data_bits_seen = (bus_state_d != ReadDataNACK) ? 1 : 0;
        end
        // Waiting for the first bit of data.
        WriteDataACK, WriteDataNACK: begin
          // Remain in the same state if NACK is received, else move to WriteData
          bus_state_d = (bus_state_d != WriteDataNACK) ? WriteData : WriteDataNACK;
          num_addr_bits_seen = 0;
          num_data_bits_seen = (bus_state_d != WriteDataNACK) ? 1 : 0;
        end
        Stop: begin
          bus_state_d = Idle;
        end
        default: begin
          $warning("i2c_protocol_cov:: Invalid bus state");
        end
      endcase
    end
  end

  covergroup i2c_protocol_cov_cg;
    option.name         = "i2c_protocol_cov_cg";
    option.per_instance = 1;

    bus_state_cp : coverpoint bus_state_q {
      bins start = {Start};
      bins rstart = {RStart};
      bins addr = {Addr};
      bins read = {Read};
      bins write = {Write};
      bins read_addr_ack = {ReadAddrACK};
      bins read_addr_nack = {ReadAddrNACK};
      bins write_addr_ack = {WriteAddrACK};
      bins write_addr_nack = {WriteAddrNACK};
      bins read_data = {ReadData};
      bins write_data = {WriteData};
      bins read_data_ack = {ReadDataACK};
      bins read_data_nack = {ReadDataNACK};
      bins write_data_ack = {WriteDataACK};
      bins write_data_nack = {WriteDataNACK};
      bins stop = {Stop};
      bins idle = {Idle};
    }
    ip_mode_cp : coverpoint host_mode_en {
      bins host = {1};
      bins device = {0};
    }
    // Cover number of Write bytes transferred
    num_wr_bytes_cp : coverpoint num_wr_bytes {
      bins one = {1};
      bins low = {[2:21]};
      bins mid = {[22:43]};
      bins high = {[44:63]};
      bins sixtyfour = {64};
    }
    // Cover number of Read bytes transferred
    num_rd_bytes_cp : coverpoint num_rd_bytes {
      bins one = {1};
      bins low = {[2:21]};
      bins mid = {[22:43]};
      bins high = {[44:63]};
      bins sixtyfour = {64};
    }
    // Cover Bus transitions
    Stop_after_write_data_ack_cp : coverpoint bus_state_q {
      bins Stop_after_write_data_ack = (WriteDataACK => WriteData => Stop);
    }
    // bus_state_q automatically transitions to ReadData after ReadDataACK,
    // so included ReadData in transition sequence
    Stop_after_read_data_ack_cp : coverpoint bus_state_q {
      bins Stop_after_read_data_ack = (ReadDataACK => ReadData => Stop);
    }
    Stop_after_write_data_Nack_cp : coverpoint bus_state_q {
      bins Stop_after_write_data_Nack = (WriteDataNACK => Stop);
    }
    Stop_after_read_data_Nack_cp : coverpoint bus_state_q {
      bins Stop_after_read_data_Nack = (ReadDataNACK => Stop);
    }
    // bus_state_q automatically transitions to WriteData after WriteDataACK,
    // so included WriteData in transition sequence
    Rstart_after_Address_Ack_cp : coverpoint bus_state_q {
      bins Rstart_after_Address_Ack = (ReadAddrACK, WriteAddrACK => ReadData, WriteData => RStart);
    }
    Rstart_after_Address_Nack_cp : coverpoint bus_state_q {
      bins Rstart_after_Address_Nack = (WriteAddrNACK => RStart);
    }
    // Mistimed RStart or Stop glitches, applicable only in Target mode of operation
    RStart_during_address_transmission_cp : coverpoint bus_state_q iff (!host_mode_en) {
      bins Start_during_address_transmission = (Addr => RStart);
    }
    RStart_during_rw_bit_cp : coverpoint bus_state_q iff (!host_mode_en) {
      bins Start_during_rw_bit = (Read, Write => RStart);
    }
    RStart_during_address_Ack_cp : coverpoint bus_state_q iff (!host_mode_en) {
      bins Start_during_address_Acknowledge =
        (ReadAddrACK, ReadAddrNACK, WriteAddrACK, WriteAddrNACK => RStart);
    }
    RStart_during_write_data_cp : coverpoint bus_state_q iff (!host_mode_en) {
      bins Start_during_write_data = (WriteData => RStart);
    }
    RStart_during_read_data_cp : coverpoint bus_state_q iff (!host_mode_en) {
      bins Start_during_read_data = (ReadData => RStart);
    }
    RStart_before_read_data_ACK_cp : coverpoint bus_state_q iff (!host_mode_en) {
      bins Start_before_read_data_ACK_Nack = (ReadDataACK, ReadDataNACK => RStart);
    }
    Stop_without_ACK_after_addr_cp : coverpoint bus_state_q iff (!host_mode_en) {
      bins Stop_without_ACK_after_addr = (Addr => Stop);
    }
    Stop_without_ACK_after_read_cp : coverpoint bus_state_q iff (!host_mode_en) {
      bins Stop_without_ACK_after_read = (ReadAddrACK, ReadAddrNACK => Stop);
    }
    Stop_without_ACK_after_write_cp : coverpoint bus_state_q iff (!host_mode_en) {
      bins Stop_without_ACK_after_write = (WriteAddrACK, WriteAddrNACK => Stop);
    }
    Stop_without_ACK_after_data_cp : coverpoint bus_state_q iff (!host_mode_en) {
      bins Stop_without_ACK_after_data = (WriteData, ReadData => Stop);
    }
    Read_data_ack_before_stop_cp : coverpoint bus_state_q iff (!host_mode_en) {
      bins Read_data_ack_before_stop = (ReadDataACK => ReadData =>  Stop);
    }
    // If Stop is detected after RStart then next start of transaction is Start
    Start_followed_by_Rstart_cp : coverpoint current_txn_start == RStart && bus_state_q == Stop {
      ignore_bins unused = {0};
    }

    // Cross Coverage
    // Cover the protocol states in each mode
    bus_state_x_ip_mode_cp : cross bus_state_cp, ip_mode_cp;
    // Cover number of bytes transferred in each mode
    num_rd_bytes_x_ip_mode_cp : cross ip_mode_cp, num_rd_bytes_cp;
    num_wr_bytes_x_ip_mode_cp : cross ip_mode_cp, num_wr_bytes_cp;

    // Cover bus transitions for each mode
    Stop_after_write_data_ack_x_ip_mode_cp : cross Stop_after_write_data_ack_cp, ip_mode_cp;
    Stop_after_read_data_ack_x_ip_mode_cp : cross Stop_after_read_data_ack_cp, ip_mode_cp;
    Stop_after_write_data_Nack_x_ip_mode_cp : cross Stop_after_write_data_Nack_cp, ip_mode_cp;
    Stop_after_read_data_Nack_x_ip_mode_cp : cross Stop_after_read_data_Nack_cp, ip_mode_cp;
    Rstart_after_Address_Ack_x_ip_mode_cp : cross Rstart_after_Address_Ack_cp, ip_mode_cp;
    Rstart_after_Address_Nack_x_ip_mode_cp : cross Rstart_after_Address_Nack_cp, ip_mode_cp;
    Start_followed_by_Rstart_cp_x_ip_mode_cp : cross Start_followed_by_Rstart_cp, ip_mode_cp;
  endgroup

  // Cover read write bytes in host and target modes
  covergroup i2c_rd_wr_cg;
    option.per_instance = 1;
    // option.auto_bin_max = 64;
    option.name         = "i2c_rd_wr_cg";
    // Mode of operation
    ip_mode_cp : coverpoint host_mode_en {
      bins host = {1};
      bins device = {0};
    }
    // Cover address match
    cp_address_match : coverpoint {write_txn, read_txn, address_match} {
      bins write_addr_match    = {3'b101};
      bins write_addr_no_match = {3'b100};
      bins read_addr_match     = {3'b011};
      bins read_addr_no_match  = {3'b010};
      wildcard illegal_bins illegal = {3'b11?};
      wildcard ignore_bins  ignore  = {3'b00?};
    }
    // Write byte values
    cp_write_byte : coverpoint fbyte iff (write_txn){
      bins all_zero = {0};
      bins low = {[1: 100]};
      bins med = {[101: 200]};
      bins high = {[201: 254]};
      bins all_one  = {255};
    }
    // Read byte values
    cp_read_byte : coverpoint fbyte iff (read_txn){
      bins all_zero = {0};
      bins low = {[1: 100]};
      bins med = {[101: 200]};
      bins high = {[201: 254]};
      bins all_one  = {255};
    }
    // Cover address match with mode of operation
    cross_address_match_x_ip_mode: cross address_match, ip_mode_cp;
    // Cover write byte values in host mode and target mode
    cross_write_byte_x_ip_mode: cross cp_write_byte, ip_mode_cp;
    // Cover read byte values in host mode and target mode
    cross_read_byte_x_ip_mode: cross cp_write_byte, ip_mode_cp;
  endgroup: i2c_rd_wr_cg

  // Cover cmd_complete interrupt
  covergroup i2c_cmd_complete_cg;
    option.per_instance = 1;

    cp_cmd_complete : coverpoint intr_cmd_complete{
      bins complete = {1};
    }
    // Mode of operation
    cp_ip_mode : coverpoint host_mode_en {
      bins host = {1};
      bins device = {0};
    }
    cp_read_x_complete    : cross cp_cmd_complete, cp_ip_mode iff (read_txn);
    cp_write_x_complete   : cross cp_cmd_complete, cp_ip_mode iff (write_txn);
  endgroup : i2c_cmd_complete_cg

  initial begin
    bit en_cov;
    void'($value$plusargs("en_cov=%b", en_cov));
    if (en_cov) begin
      i2c_protocol_cov_cg   i2c_protocol_cov = new();
      i2c_rd_wr_cg          i2c_rd_wr_cov = new();
      i2c_cmd_complete_cg   cmd_complete_cg = new();
      fork
        begin
            forever begin
            @(sda or scl);
            if(rst_n) begin
              i2c_protocol_cov.sample();
              i2c_rd_wr_cov.sample();
            end
          end
        end
        begin
          wait(intr_cmd_complete);
          cmd_complete_cg.sample();
        end
      join
    end
  end

endmodule
