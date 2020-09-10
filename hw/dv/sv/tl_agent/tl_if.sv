// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// ---------------------------------------------
// TileLink interface
// ---------------------------------------------
interface tl_if(input clk, input rst_n);

  wire tlul_pkg::tl_h2d_t h2d; // req
  wire tlul_pkg::tl_d2h_t d2h; // rsp

  tlul_pkg::tl_h2d_t h2d_int; // req (internal)
  tlul_pkg::tl_d2h_t d2h_int; // rsp (internal)

  tlul_pkg::tl_h2d_t h2d_int_final; // req (internal, with randomize data when ready is low)
  tlul_pkg::tl_d2h_t d2h_int_final; // rsp (internal, with randomize data when ready is low)
  tlul_pkg::tl_h2d_t h2d_int_rand; // req (internal, contain randomize data)
  tlul_pkg::tl_d2h_t d2h_int_rand; // rsp (internal, contain randomize data)
  // knobs to randomize data control info when ready is low
  bit randomize_data_ctrl_when_ready_low = 1;
  // xbar may use addr and source to route the item to device and set ready, randomize source may
  // create deadloop
  bit randomize_addr_when_ready_low = 1;
  bit [bus_params_pkg::BUS_AIW-1:0] a_source_randomize_mask_when_ready_low = '1;
  bit [bus_params_pkg::BUS_AIW-1:0] d_source_randomize_mask_when_ready_low = '1;

  dv_utils_pkg::if_mode_e if_mode; // interface mode - Host or Device

  modport dut_host_mp(output h2d_int, input d2h_int);
  modport dut_device_mp(input h2d_int, output d2h_int);

  clocking host_cb @(posedge clk);
    input  rst_n;
    output h2d_int;
    input  d2h;
  endclocking
  modport host_mp(clocking host_cb);

  clocking device_cb @(posedge clk);
    input  rst_n;
    input  h2d;
    output d2h_int;
  endclocking
  modport device_mp(clocking device_cb);

  clocking mon_cb @(posedge clk);
    input  rst_n;
    input  h2d;
    input  d2h;
  endclocking
  modport mon_mp(clocking mon_cb);

  assign h2d = (if_mode == dv_utils_pkg::Host) ? h2d_int_final : 'z;
  assign d2h = (if_mode == dv_utils_pkg::Device) ? d2h_int_final : 'z;

  always @(posedge clk or negedge rst_n) begin
    if (!rst_n || randomize_data_ctrl_when_ready_low && h2d_int.a_valid && d2h.a_ready) begin
      h2d_int_rand.a_address <= $urandom;
      h2d_int_rand.a_opcode  <= $urandom;
      h2d_int_rand.a_size    <= $urandom;
      h2d_int_rand.a_param   <= $urandom;
      h2d_int_rand.a_data    <= $urandom;
      h2d_int_rand.a_mask    <= $urandom;
      h2d_int_rand.a_source  <= $urandom;
    end
  end

  always_comb begin
    if (if_mode == dv_utils_pkg::Host) begin
      h2d_int_final.a_valid = h2d_int.a_valid;
      h2d_int_final.d_ready = h2d_int.d_ready;
      h2d_int_final.a_user  = h2d_int.a_user;
      if (!randomize_data_ctrl_when_ready_low || !h2d_int.a_valid || d2h.a_ready) begin
        h2d_int_final = h2d_int;
      end else if (h2d_int.a_valid && !d2h.a_ready) begin
        h2d_int_final.a_address = randomize_addr_when_ready_low ? h2d_int_rand.a_address :
                                                                  h2d_int.a_address;
        h2d_int_final.a_opcode  = h2d_int_rand.a_opcode;
        h2d_int_final.a_size    = h2d_int_rand.a_size;
        h2d_int_final.a_param   = h2d_int_rand.a_param;
        h2d_int_final.a_data    = h2d_int_rand.a_data;
        h2d_int_final.a_mask    = h2d_int_rand.a_mask;
        h2d_int_final.a_source  = (a_source_randomize_mask_when_ready_low & h2d_int_rand.a_source) |
                                  (~a_source_randomize_mask_when_ready_low & h2d_int.a_source);
      end
    end
  end

  always @(posedge clk or negedge rst_n) begin
    if (!rst_n || randomize_data_ctrl_when_ready_low && d2h_int.d_valid && h2d.d_ready) begin
      d2h_int_rand.d_opcode <= $urandom;
      d2h_int_rand.d_data   <= $urandom;
      d2h_int_rand.d_param  <= $urandom;
      d2h_int_rand.d_error  <= $urandom;
      d2h_int_rand.d_sink   <= $urandom;
      d2h_int_rand.d_size   <= $urandom;
      d2h_int_rand.d_source <= $urandom;
    end
  end

  always_comb begin
    if (if_mode == dv_utils_pkg::Device) begin
      d2h_int_final.d_valid = d2h_int.d_valid;
      d2h_int_final.a_ready = d2h_int.a_ready;
      d2h_int_final.d_user  = d2h_int.d_user;
      if (!randomize_data_ctrl_when_ready_low || !d2h_int.d_valid || h2d.d_ready) begin
        d2h_int_final = d2h_int;
      end else if (d2h_int.d_valid && !h2d.d_ready) begin
        d2h_int_final.d_opcode = d2h_int_rand.d_opcode;
        d2h_int_final.d_data   = d2h_int_rand.d_data;
        d2h_int_final.d_param  = d2h_int_rand.d_param;
        d2h_int_final.d_error  = d2h_int_rand.d_error;
        d2h_int_final.d_sink   = d2h_int_rand.d_sink;
        d2h_int_final.d_size   = d2h_int_rand.d_size;
        d2h_int_final.d_source = (d_source_randomize_mask_when_ready_low & d2h_int_rand.d_source) |
                                 (~d_source_randomize_mask_when_ready_low & d2h_int.d_source);
      end
    end
  end

endinterface : tl_if
