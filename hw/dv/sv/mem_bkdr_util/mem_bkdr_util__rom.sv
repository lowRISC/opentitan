// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Wrapper functions for ROM's encrypted read operation.
// This file is included in `mem_bkdr_util.sv` as a continuation of `mem_bkdr_util` class.

// The data decoding is different from SRAM, but most of the underlying SRAM functions are reused
// Also note that this function returns the raw data rather than data + syndrome + error because
// the rom_ctrl testbench needs this for checking.
virtual function bit [38:0] rom_encrypt_read32(bit [bus_params_pkg::BUS_AW-1:0] addr,
                                               logic [SRAM_KEY_WIDTH-1:0]       key,
                                               logic [SRAM_BLOCK_WIDTH-1:0]     nonce,
                                               bit                              unscramble_data);

  logic [bus_params_pkg::BUS_AW-1:0] mem_addr = '0;
  logic [38:0]                       data = '0;

  logic addr_arr      [] = new[addr_width];
  logic scrambled_addr[] = new[addr_width];
  logic data_arr      [] = new[39];
  logic key_arr       [] = new[SRAM_KEY_WIDTH];
  logic nonce_arr     [] = new[SRAM_BLOCK_WIDTH];
  logic keystream     [] = new[SRAM_BLOCK_WIDTH];
  logic zero_key      [] = new[39];

  key_arr   = {<<{key}};
  nonce_arr = {<<{nonce}};

  for (int i = 0; i < addr_width; i++) begin
    addr_arr[i] = addr[addr_lsb + i];
  end

  // Calculate the scrambled address
  scrambled_addr = sram_scrambler_pkg::encrypt_sram_addr(addr_arr, addr_width, nonce_arr);

  for (int i = 0; i < addr_width; i++) begin
    mem_addr[i] = scrambled_addr[i];
  end

  // Read memory and get the encrypted data
  if (!check_addr_valid(mem_addr << addr_lsb)) begin
    return 'x;
  end

  // 39-bit memory word includes 32-bit data + 7-bit ECC
  data = read(mem_addr << addr_lsb);

  if (!unscramble_data) begin
    return data;
  end

  data_arr = {<<{data}};

  // Generate the keystream
  keystream = sram_scrambler_pkg::gen_keystream(addr_arr, addr_width, key_arr, nonce_arr);

  for (int i = 0; i < 39; i++) begin
    zero_key[i] = '0;
  end

  data_arr = sram_scrambler_pkg::sp_decrypt(data_arr, 39, zero_key);
  for (int i = 0; i < 39; i++) begin
    data[i] = data_arr[i] ^ keystream[i];
  end

  return data;
endfunction


virtual function void rom_encrypt_write32_integ(logic [bus_params_pkg::BUS_AW-1:0] addr,
                                                logic [31:0]                       data,
                                                logic [SRAM_KEY_WIDTH-1:0]         key,
                                                logic [SRAM_BLOCK_WIDTH-1:0]       nonce,
                                                bit                                scramble_data,
                                                bit   [38:0]                       flip_bits = 0);
  logic [bus_params_pkg::BUS_AW-1:0] bus_addr = '0;
  logic [38:0]                       integ_data;
  logic [38:0]                       scrambled_data;

  logic wdata_arr      [] = new[39];
  logic scrambled_addr [] = new[addr_width];
  logic rom_addr       [] = new[addr_width];
  logic key_arr        [] = new[SRAM_KEY_WIDTH];
  logic nonce_arr      [] = new[SRAM_BLOCK_WIDTH];

  key_arr   = {<<{key}};
  nonce_arr = {<<{nonce}};

  for (int i = 0; i < addr_width; i++) begin
    rom_addr[i] = addr[addr_lsb + i];
  end

  // Calculate the scrambled address
  scrambled_addr = sram_scrambler_pkg::encrypt_sram_addr(rom_addr, addr_width, nonce_arr);

  if(scramble_data) begin
    // Calculate the integrity constant
    integ_data = prim_secded_pkg::prim_secded_inv_39_32_enc(data);

    // flip some bits to inject integrity fault
    integ_data ^= flip_bits;
  
    // Calculate the scrambled data
    wdata_arr = {<<{integ_data}};
    wdata_arr = sram_scrambler_pkg::encrypt_sram_data(
        wdata_arr, 39, 39, rom_addr, addr_width, key_arr, nonce_arr
    );
    scrambled_data = {<<{wdata_arr}};
  end
  else begin
    scrambled_data = data;
  end

  // Construct bus representation of the address
  for (int i = 0; i < addr_lsb; i++) begin
    bus_addr[i] = addr[i];
  end
  for (int i = 0; i < addr_width; i++) begin
    bus_addr[addr_lsb + i] = scrambled_addr[i];
  end
  // Write the scrambled data to memory
  write39integ(bus_addr, scrambled_data);
endfunction
