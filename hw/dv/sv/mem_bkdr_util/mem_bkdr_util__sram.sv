// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Wrapper functions for SRAM's encrypted read/write operations.
// This file is included in `mem_bkdr_util.sv` as a continuation of `mem_bkdr_util` class.

function logic [bus_params_pkg::BUS_AW-1:0] get_sram_encrypt_addr (
  logic [bus_params_pkg::BUS_AW-1:0] addr,
  logic [SRAM_BLOCK_WIDTH-1:0] nonce,
  logic [31:0] extra_addr_bits = '0);

  int full_addr_width = addr_width + extra_addr_bits;

  logic [bus_params_pkg::BUS_AW-1:0] scr_addr;
  logic scr_addr_arr   [] = new[full_addr_width];
  logic addr_arr       [] = new[full_addr_width];
  logic nonce_arr      [] = new[SRAM_BLOCK_WIDTH];

  nonce_arr = {<<{nonce}};
  for (int i = 0; i < full_addr_width; i++) begin
    addr_arr[i] = addr[addr_lsb + i];
  end

  // calculate scrambled address
  scr_addr_arr = sram_scrambler_pkg::encrypt_sram_addr(addr_arr, full_addr_width, nonce_arr);

  // convert to bus address output
  for (int i = 0; i < addr_lsb; i++) begin
    scr_addr[i] = addr[i];
  end

  for (int i = 0; i < full_addr_width; i++) begin
    scr_addr[addr_lsb + i] = scr_addr_arr[i];
  end

  return scr_addr;

endfunction // get_sram_encrypt_addr

function logic [38:0] get_sram_encrypt32_intg_data (
  logic [bus_params_pkg::BUS_AW-1:0] addr,
  logic [31:0]                       data,
  logic [SRAM_KEY_WIDTH-1:0]         key,
  logic [SRAM_BLOCK_WIDTH-1:0]       nonce,
  int                                extra_addr_bits=0);

  logic [38:0]                       integ_data;
  logic [38:0]                       scrambled_data;

  int full_addr_width = addr_width + extra_addr_bits;
  logic wdata_arr      [] = new[39];
  logic addr_arr       [] = new[full_addr_width];
  logic key_arr        [] = new[SRAM_KEY_WIDTH];
  logic nonce_arr      [] = new[SRAM_BLOCK_WIDTH];

  key_arr   = {<<{key}};
  nonce_arr = {<<{nonce}};

  for (int i = 0; i < full_addr_width; i++) begin
    addr_arr[i] = addr[addr_lsb + i];
  end

  // Calculate the integrity constant
  integ_data = prim_secded_pkg::prim_secded_inv_39_32_enc(data);

  // Calculate the scrambled data
  wdata_arr = {<<{integ_data}};
  wdata_arr = sram_scrambler_pkg::encrypt_sram_data(
      wdata_arr, 39, 39, addr_arr, full_addr_width, key_arr, nonce_arr
  );
  scrambled_data = {<<{wdata_arr}};

  return scrambled_data;

endfunction // get_sram_encrypt32_intg_data

virtual function logic [38:0] sram_encrypt_read32_integ(logic [bus_params_pkg::BUS_AW-1:0] addr,
                                                        logic [SRAM_KEY_WIDTH-1:0]         key,
                                                        logic [SRAM_BLOCK_WIDTH-1:0]       nonce);
  logic [bus_params_pkg::BUS_AW-1:0] scr_addr;
  logic [38:0]                       rdata = '0;

  logic rdata_arr     [] = new[39];
  logic addr_arr      [] = new[addr_width];
  logic key_arr       [] = new[SRAM_KEY_WIDTH];
  logic nonce_arr     [] = new[SRAM_BLOCK_WIDTH];

  key_arr   = {<<{key}};
  nonce_arr = {<<{nonce}};
  for (int i = 0; i < addr_width; i++) begin
    addr_arr[i] = addr[addr_lsb + i];
  end

  // Calculate the scrambled address
  scr_addr = get_sram_encrypt_addr(addr, nonce);

  // Read memory and return the decrypted data
  rdata = read39integ(scr_addr);
  `uvm_info(`gfn, $sformatf("scr data: 0x%0x", rdata), UVM_HIGH)
  rdata_arr = {<<{rdata}};
  rdata_arr = sram_scrambler_pkg::decrypt_sram_data(
      rdata_arr, 39, 39, addr_arr, addr_width, key_arr, nonce_arr
  );
  rdata = {<<{rdata_arr}};
  // Only return the data payload without ECC bits.
  return rdata[31:0];

endfunction

virtual function void sram_encrypt_write32_integ(logic [bus_params_pkg::BUS_AW-1:0] addr,
                                                 logic [31:0]                       data,
                                                 logic [SRAM_KEY_WIDTH-1:0]         key,
                                                 logic [SRAM_BLOCK_WIDTH-1:0]       nonce,
                                                 bit   [38:0]                       flip_bits = 0);
  logic [bus_params_pkg::BUS_AW-1:0] scr_addr;
  logic [38:0]                       integ_data;
  logic [38:0]                       scrambled_data;

  logic wdata_arr      [] = new[39];
  logic addr_arr       [] = new[addr_width];
  logic key_arr        [] = new[SRAM_KEY_WIDTH];
  logic nonce_arr      [] = new[SRAM_BLOCK_WIDTH];

  key_arr   = {<<{key}};
  nonce_arr = {<<{nonce}};

  for (int i = 0; i < addr_width; i++) begin
    addr_arr[i] = addr[addr_lsb + i];
  end

  // Calculate the scrambled address
  scr_addr = get_sram_encrypt_addr(addr, nonce);

  // Calculate the integrity constant
  integ_data = prim_secded_pkg::prim_secded_inv_39_32_enc(data);

  // flip some bits to inject integrity fault
  integ_data ^= flip_bits;

  // Calculate the scrambled data
  wdata_arr = {<<{integ_data}};
  wdata_arr = sram_scrambler_pkg::encrypt_sram_data(
      wdata_arr, 39, 39, addr_arr, addr_width, key_arr, nonce_arr
  );
  scrambled_data = {<<{wdata_arr}};

  // Write the scrambled data to memory
  write39integ(scr_addr, scrambled_data);
endfunction
