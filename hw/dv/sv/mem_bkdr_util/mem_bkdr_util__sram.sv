// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Wrapper functions for SRAM's encrypted read/write operations.
// This file is included in `mem_bkdr_util.sv` as a continuation of `mem_bkdr_util` class.

// Returns the address after scrambling it using the given nonce.
function logic [bus_params_pkg::BUS_AW-1:0] get_sram_encrypt_addr (
  logic [bus_params_pkg::BUS_AW-1:0] addr,
  logic [SRAM_BLOCK_WIDTH-1:0] nonce,
  logic [31:0] extra_addr_bits);

  int full_addr_width = addr_width + extra_addr_bits;

  logic [bus_params_pkg::BUS_AW-1:0] scr_addr;
  logic scr_addr_arr   [] = new[full_addr_width];
  logic addr_arr       [] = new[full_addr_width];
  logic nonce_arr      [] = new[SRAM_BLOCK_WIDTH];

  nonce_arr = {<<{nonce}};
  for (int i = 0; i < full_addr_width; i++) begin
    addr_arr[i] = addr[addr_lsb + i];
  end

  scr_addr_arr = sram_scrambler_pkg::encrypt_sram_addr(addr_arr, full_addr_width, nonce_arr);

  // Convert to bus address output.
  for (int i = 0; i < addr_lsb; i++) begin
    scr_addr[i] = addr[i];
  end
  for (int i = 0; i < full_addr_width; i++) begin
    scr_addr[addr_lsb + i] = scr_addr_arr[i];
  end
  return scr_addr;
endfunction : get_sram_encrypt_addr

// Returns the data after adding integrity bits and encrypting it with the given key and nonce.
// If flip_bits is non-zero it may introduce integrity errors, but notice there is a small chance
// after descrambling the data the errors will not be detected.
function logic [38:0] get_sram_encrypt32_intg_data (
  logic [bus_params_pkg::BUS_AW-1:0] addr,
  logic [31:0]                       data,
  logic [SRAM_KEY_WIDTH-1:0]         key,
  logic [SRAM_BLOCK_WIDTH-1:0]       nonce,
  int                                extra_addr_bits,
  bit   [38:0]                       flip_bits = '0);

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

  integ_data = prim_secded_pkg::prim_secded_inv_39_32_enc(data);
  integ_data ^= flip_bits;

  wdata_arr = {<<{integ_data}};
  wdata_arr = sram_scrambler_pkg::encrypt_sram_data(
      wdata_arr, 39, 39, addr_arr, full_addr_width, key_arr, nonce_arr
  );
  scrambled_data = {<<{wdata_arr}};
  return scrambled_data;
endfunction : get_sram_encrypt32_intg_data

// Returns the data at the given address after descrambling the address and decrypting the data.
// It simply ignores the integrity bits.
virtual function logic [38:0] sram_encrypt_read32_integ(logic [bus_params_pkg::BUS_AW-1:0] addr,
                                                        logic [SRAM_KEY_WIDTH-1:0]         key,
                                                        logic [SRAM_BLOCK_WIDTH-1:0]       nonce,
                                                        int extra_addr_bits);
  logic [bus_params_pkg::BUS_AW-1:0] scr_addr = get_sram_encrypt_addr(addr, nonce, extra_addr_bits);
  logic [38:0] rdata39 = _sram_decrypt_read39(addr, scr_addr, key, nonce, extra_addr_bits);
  return rdata39[31:0];
endfunction : sram_encrypt_read32_integ

// This reads the data at a scrambled address and decrypts it. It returns the data and
// integrity bits.
local function logic [38:0] _sram_decrypt_read39(
    logic [bus_params_pkg::BUS_AW-1:0] addr,
    logic [bus_params_pkg::BUS_AW-1:0] scr_addr,
    logic [SRAM_KEY_WIDTH-1:0]   key,
    logic [SRAM_BLOCK_WIDTH-1:0] nonce,
    int extra_addr_bits);
  logic [38:0]                       rdata39 = '0;

  logic rdata_arr     [] = new[39];
  logic addr_arr      [] = new[addr_width];
  logic key_arr       [] = new[SRAM_KEY_WIDTH];
  logic nonce_arr     [] = new[SRAM_BLOCK_WIDTH];
  int   full_addr_width = addr_width + extra_addr_bits;

  key_arr   = {<<{key}};
  nonce_arr = {<<{nonce}};
  for (int i = 0; i < full_addr_width; i++) begin
    addr_arr[i] = addr[addr_lsb + i];
  end

  rdata39 = read39integ(scr_addr);
  `uvm_info(`gfn, $sformatf("scr data: 0x%0x", rdata39), UVM_HIGH)
  rdata_arr = {<<{rdata39}};
  rdata_arr = sram_scrambler_pkg::decrypt_sram_data(
      rdata_arr, 39, 39, addr_arr, full_addr_width, key_arr, nonce_arr
  );
  rdata39 = {<<{rdata_arr}};
  return rdata39;
endfunction : _sram_decrypt_read39

// Writes the data at the given address. It scrambles the address and encrypts the data after
// adding integrity bits. If flip_bits is non-zero it may introduce ecc errors.
virtual function void sram_encrypt_write32_integ(logic [bus_params_pkg::BUS_AW-1:0] addr,
                                                 logic [31:0]                       data,
                                                 logic [SRAM_KEY_WIDTH-1:0]         key,
                                                 logic [SRAM_BLOCK_WIDTH-1:0]       nonce,
                                                 int                                extra_addr_bits,
                                                 bit   [38:0]                       flip_bits = 0);
  logic [bus_params_pkg::BUS_AW-1:0] scr_addr = get_sram_encrypt_addr(addr, nonce, extra_addr_bits);
  _sram_encrypt_write39(addr, scr_addr, data, key, nonce, extra_addr_bits, flip_bits);
endfunction : sram_encrypt_write32_integ


// This encrypts, possibly flips some bits to inject errors, and writes the resulting data
// to a scrambled address.
local function void _sram_encrypt_write39(logic [bus_params_pkg::BUS_AW-1:0] addr,
                                          logic [bus_params_pkg::BUS_AW-1:0] scr_addr,
                                          logic [31:0]                 data,
                                          logic [SRAM_KEY_WIDTH-1:0]   key,
                                          logic [SRAM_BLOCK_WIDTH-1:0] nonce,
                                          int                          extra_addr_bits,
                                          bit [38:0]                   flip_bits);
  logic [38:0] scrambled_data = get_sram_encrypt32_intg_data(addr, data, key, nonce, extra_addr_bits, flip_bits);
  write39integ(scr_addr, scrambled_data);
endfunction : _sram_encrypt_write39

// This injects integrity errors in sram for an original address and the corresponding
// scrambled address. It needs to pass both addresses even though only the scrambled address
// is affected, since the original address is used to encrypt the data.
//
// This code needs to try multiple random data since it is possible after encryption the
// bit pattern will not result in a data error, as described in issue #10976
virtual function void sram_inject_integ_error(logic [bus_params_pkg::BUS_AW-1:0] addr,
                                              logic [bus_params_pkg::BUS_AW-1:0] scr_addr,
                                              logic [SRAM_KEY_WIDTH-1:0]   key,
                                              logic [SRAM_BLOCK_WIDTH-1:0] nonce,
                                              int extra_addr_bits);
  int max_attempts = 40;
  int attempt = 0;

  while (attempt < max_attempts) begin
    bit [31:0] data = $urandom();
    bit [38:0] rdata_integ;
    prim_secded_pkg::secded_inv_39_32_t dec;
    // The specific bits to be flipped should be irrelevant.
    _sram_encrypt_write39(addr, scr_addr, data, key, nonce, extra_addr_bits, 39'h1001);
    rdata_integ = _sram_decrypt_read39(addr, scr_addr, key, nonce, extra_addr_bits);
    dec = prim_secded_pkg::prim_secded_inv_39_32_dec(rdata_integ);
    if (dec.err) begin
      `uvm_info(`gfn, $sformatf(
                "sram_inject_integ_error addr 0x%x, data 0x%x injects error %b after %0d attempts",
                addr, rdata_integ, dec.err, attempt),
                UVM_MEDIUM)
      break;
    end
    ++attempt;
  end
  `DV_CHECK_LT(attempt, max_attempts, "Too many attempts in sram_inject_ecc_error")
endfunction : sram_inject_integ_error
