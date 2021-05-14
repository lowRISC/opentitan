// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Description: mem_bkdr_if binds to the ram/rom instance to do a backdoor write / read to the
// memory array directly. It needs to be bound to the right ram / rom wrappers to work. Currently,
// these are limited to: prim_ram_1p, prim_ram_2p, prim_rom
//
// The following assumptions are made:
// 1. This interface will be bound to one of the following modules:
//    prim_ram_1p, prim_ram_2p, prim_rom
// 2. The sub hierarchy from within these instances to the memory element will be fixed to
//    'gen_generic.u_impl_generic.mem'
//
// If these assumptions are met, then the generic interface can be used to bind to any instance with
// any parameter set and can be set into the uvm_config_db to allow us to manipulate the mem
// contents from the testbench without having us to add heirarchy information, making the chip
// testbench portable.


// The `MEM_PARITY` parameter.
//
// The `MEM_PARITY` parameter is used to indicate whether the target memory uses parity checks.
// If so, we need to take care to modify the read/write indices, as the total memory width will be
// `mem_bytes_per_word * 8 + mem_bytes_per_word` as we have one parity bit per data byte.
// Enabling this parameter also allows access to parity error injection functionality - to use this
// all that needs to be done is to set the `inject_err` argument in any of the backdoor write
// functions.


// The `MEM_ECC` parameter.
//
// The `MEM_ECC` parameter is used to indicate whether the target memory uses an ECC implementation,
// so we can ensure to use the proper data encoding scheme.
// The value of this parameter must be a `prim_secded_e` enumerated value, which can be found in
// `hw/ip/prim/rtl/prim_secded_pkg.sv`.
// Setting this parameter to `SecdedNone` disables ECC functionality, and setting it to any other
// enum value configures this interface to use the correct ECC bit-widths.
// Enabling ECC also allows access to ECC error injection functionality - to use this
// all that needs to be done is to set the `inject_err` argument in any of the backdoor write
// functions.
//
// One important note when using this parameter is that the normal `read##()` functions cannot be
// used if it is desired to access ECC-related syndrome and error information.
// In this case, it is required to use the `ecc_read##()` functions, which will return a struct
// containing read data, syndrome, and error data fields.


// The `MEM_PARITY` and `MEM_ECC` parameters must not be enabled concurrently,
// all resultant behavior is undefined.
//
// Note: The maximum data width currently supported by this interface is 64-bits (8 bytes).
//       If support for wider memories is desired, it will need to be implemented.

interface mem_bkdr_if #(
    parameter bit MEM_PARITY = 0,
    parameter prim_secded_pkg::prim_secded_e MEM_ECC = prim_secded_pkg::SecdedNone
) ();

  import uvm_pkg::*;
  import bus_params_pkg::BUS_AW;
  import sram_scrambler_pkg::*;
  import prim_secded_pkg::*;

  `include "uvm_macros.svh"
  `include "dv_macros.svh"

  // sub hierarchy slice to the memory element
  // TODO: need to publicize this info - user needs to set the below macro correctly when swapping
  // out srams with vendor library models. Also, need to address the scenario where not all ram
  // instances are replaced with vendor library models.
`ifndef MEM_ARR_PATH_SLICE
  `define MEM_ARR_PATH_SLICE gen_generic.u_impl_generic.mem
`endif

  // Represents the highest bit position of a data byte.
  // If parity is enabled, it is 9 because we add a parity tag bit.
  // If parity is disabled, then no extra bits are added to this parameter.
  localparam int MEM_BYTE_MSB = (MEM_PARITY) ? 9 : 8;

  localparam int ECC_PARITY_BITS = prim_secded_pkg::get_ecc_parity_width(MEM_ECC);

  localparam int ECC_DATA_WIDTH = prim_secded_pkg::get_ecc_data_width(MEM_ECC);

  localparam int MAX_MEM_WIDTH = (MEM_ECC == SecdedNone) ?
      (MEM_BYTE_MSB * 8) : ECC_DATA_WIDTH + ECC_PARITY_BITS;

  // derive memory specifics such as depth, width, addr_msb mem size etc.
  bit initialized;
  int mem_depth;
  int mem_width;
  int mem_bytes_per_word;
  int mem_size_bytes;
  int mem_addr_lsb;
  int mem_addr_width;
  int mem_byte_addr_width;
  string path = $sformatf("%m");

  // A pair of integers.
  typedef struct {
    int x;
    int y;
  } int_pair_t;

  // A helper function tto split a given number randomly into 2 pairs.
  function automatic int_pair_t rand_split(int num);
    rand_split.x = $urandom_range(0, num);
    rand_split.y = num - rand_split.x;
  endfunction

  function automatic bit [MAX_MEM_WIDTH-1:0] inject_errors(bit [MAX_MEM_WIDTH-1:0] data,
                                                           int inject_num_errors);
    bit [MAX_MEM_WIDTH-1:0] err_mask;
    `DV_CHECK_STD_RANDOMIZE_WITH_FATAL(err_mask, $countones(err_mask) == inject_num_errors;,
                                       , path)
    inject_errors = data ^ err_mask;
  endfunction

  function automatic void init();
    if (!initialized) begin
      // Check that both MEM_PARITY and MEM_ECC are not concurrently enabled
      `DV_CHECK_FATAL(!(MEM_PARITY && MEM_ECC != SecdedNone),
          "Cannot enable both parity checks and ECC",
          path)
      `DV_CHECK_FATAL(MAX_MEM_WIDTH != 0,
          $sformatf("MEM_ECC %0s is incorrect!", MEM_ECC),
          path)

      mem_depth = $size(`MEM_ARR_PATH_SLICE);
      mem_width = $bits(`MEM_ARR_PATH_SLICE) / mem_depth;
      // Need to account for any extra ecc parity bits when doing this calculation
      mem_bytes_per_word = (mem_width - ECC_PARITY_BITS) / MEM_BYTE_MSB;
      mem_size_bytes = mem_depth * mem_bytes_per_word;
      mem_addr_lsb = $clog2(mem_bytes_per_word);
      mem_addr_width = $clog2(mem_depth);
      mem_byte_addr_width = mem_addr_width + mem_addr_lsb;
      `uvm_info(path, $sformatf("mem_depth = %0d", mem_depth), UVM_HIGH)
      `uvm_info(path, $sformatf("mem_addr_width =  %0d", mem_addr_width), UVM_HIGH)
      `uvm_info(path, $sformatf("mem_width = %0d", mem_width), UVM_HIGH)
      `uvm_info(path, $sformatf("mem_bytes_per_word = %0d", mem_bytes_per_word), UVM_HIGH)
      `uvm_info(path, $sformatf("mem_size_bytes = %0d", mem_size_bytes), UVM_HIGH)
      `uvm_info(path, $sformatf("mem_addr_lsb = %0d", mem_addr_lsb), UVM_HIGH)
      `uvm_info(path, $sformatf("mem_byte_msb = %0d", MEM_BYTE_MSB), UVM_HIGH)
      `DV_CHECK_LE_FATAL(mem_bytes_per_word, 8, "mem data width > 8 bytes is not supported", path)
      initialized = 1'b1;
    end
  endfunction

  // input addr is assumed to be the byte addressable address into memory starting at 0
  // user assumes the responsibility of masking the upper bits
  function automatic bit is_addr_valid(input bit [bus_params_pkg::BUS_AW-1:0] addr);
    init();
    if (addr >= mem_size_bytes) begin
      `uvm_error(path, $sformatf("addr = %0h is out of bounds (size = %0d)", addr, mem_size_bytes))
      return 1'b0;
    end
    return 1'b1;
  endfunction

  // read a single byte at specified address
  function automatic logic [7:0] read8(input bit [bus_params_pkg::BUS_AW-1:0] addr);
    if (is_addr_valid(addr)) begin
      int mem_index = addr >> mem_addr_lsb;
      bit [MAX_MEM_WIDTH-1:0] mem_data = `MEM_ARR_PATH_SLICE[mem_index];
      case (mem_bytes_per_word)
        1: begin
          return mem_data[7:0];
        end
        2: begin
          return mem_data[addr[0] * MEM_BYTE_MSB +: 8];
        end
        4: begin
          return mem_data[addr[1:0] * MEM_BYTE_MSB +: 8];
        end
        8: begin
          return mem_data[addr[2:0] * MEM_BYTE_MSB +: 8];
        end
        default: ;
      endcase
    end
    return 'x;
  endfunction

  function automatic logic [15:0] read16(input bit [bus_params_pkg::BUS_AW-1:0] addr);
    `DV_CHECK_EQ_FATAL(addr[0], '0, $sformatf("addr 0x%0h not 16-bit aligned", addr), path)
    if (is_addr_valid(addr)) begin
      return {read8(addr + 1), read8(addr)};
    end
    return 'x;
  endfunction

  function automatic logic [31:0] read32(input bit [bus_params_pkg::BUS_AW-1:0] addr);
    `DV_CHECK_EQ_FATAL(addr[1:0], '0, $sformatf("addr 0x%0h not 32-bit aligned", addr), path)
    if (is_addr_valid(addr)) begin
      return {read16(addr + 2), read16(addr)};
    end
    return 'x;
  endfunction

  function automatic logic [63:0] read64(input bit [bus_params_pkg::BUS_AW-1:0] addr);
    `DV_CHECK_EQ_FATAL(addr[2:0], '0, $sformatf("addr 0x%0h not 64-bit aligned", addr), path)
    if (is_addr_valid(addr)) begin
      return {read32(addr + 4), read32(addr)};
    end
    return 'x;
  endfunction

  function automatic void write8(input bit [bus_params_pkg::BUS_AW-1:0] addr,
                                 input bit [7:0] data,
                                 input int inject_num_errors = 0);
    if (is_addr_valid(addr)) begin
      int mem_index = addr >> mem_addr_lsb;
      bit [MAX_MEM_WIDTH-1:0] rw_data = `MEM_ARR_PATH_SLICE[mem_index];

      // Prepare corrupted data if an parity error injection is requested.
      //
      // We want to randomly inject errors into the parity bits themselves for better error
      // coverage.
      int idx_to_corrupt = $urandom_range(0, MEM_BYTE_MSB - 1);

      bit [MEM_BYTE_MSB-1:0] corrupted_data;

      // If inject ECC error, check the number of injected ecc_err is available.
      if (MEM_ECC != SecdedNone) begin
        `DV_CHECK_LE(inject_num_errors, MAX_MEM_WIDTH,
                     $sformatf("Max %0d bits to inject ECC error", MAX_MEM_WIDTH), , path)
      end

      // TODO: check with designer, current testbench only support 1 bit parity error.
      if (MEM_PARITY) begin
        `DV_CHECK_LE(inject_num_errors, 1, "Parity only support 1 bit error", , path)
      end

      // Note that if memory parity checks are enabled,
      // we have to write the correct parity bit as well.
      // Odd parity is used, rather than even parity checking.
      //
      // TODO: odd/even parity checks could be made configurable.
      case (mem_bytes_per_word)
        // ECC is unavailable if only 1 byte in each memory word
        1: begin
          rw_data[0 +: 8] = data;
          if (MEM_PARITY) begin
            rw_data[0 + 8] = ~(^data);
            if (inject_num_errors) begin
              corrupted_data = rw_data[0 +: MEM_BYTE_MSB];
              corrupted_data[idx_to_corrupt] = !corrupted_data[idx_to_corrupt];
              rw_data[0 +: MEM_BYTE_MSB] = corrupted_data;
            end
          end
        end
        2: begin
          rw_data[addr[0] * MEM_BYTE_MSB +: 8] = data;
          if (MEM_PARITY) begin
            rw_data[addr[0] * MEM_BYTE_MSB + 8] = ~(^data);
            if (inject_num_errors) begin
              corrupted_data = rw_data[addr[0] * MEM_BYTE_MSB +: MEM_BYTE_MSB];
              corrupted_data[idx_to_corrupt] = !corrupted_data[idx_to_corrupt];
              rw_data[addr[0] * MEM_BYTE_MSB +: MEM_BYTE_MSB] = corrupted_data;
            end
          end else if (MEM_ECC != SecdedNone) begin
            case (MEM_ECC)
              Secded_22_16: begin
                rw_data = prim_secded_22_16_enc(rw_data[ECC_DATA_WIDTH-1:0]);
              end
              SecdedHamming_22_16: begin
                rw_data = prim_secded_hamming_22_16_enc(rw_data[ECC_DATA_WIDTH-1:0]);
              end
              default: begin
                `uvm_error(path,
                    $sformatf("MEM_ECC %0s is unsupported at mem_width[%0d]", MEM_ECC, mem_width))
              end
            endcase
            if (inject_num_errors) rw_data = inject_errors(rw_data, inject_num_errors);
          end
        end
        4: begin
          rw_data[addr[1:0] * MEM_BYTE_MSB +: 8] = data;
          if (MEM_PARITY) begin
            rw_data[addr[1:0] * MEM_BYTE_MSB + 8] = ~(^data);
            if (inject_num_errors) begin
              corrupted_data = rw_data[addr[1:0] * MEM_BYTE_MSB +: MEM_BYTE_MSB];
              corrupted_data[idx_to_corrupt] = !corrupted_data[idx_to_corrupt];
              rw_data[addr[1:0] * MEM_BYTE_MSB +: MEM_BYTE_MSB] = corrupted_data;
            end
          end else if (MEM_ECC != SecdedNone) begin
            case (MEM_ECC)
              Secded_39_32: begin
                rw_data = prim_secded_39_32_enc(rw_data[ECC_DATA_WIDTH-1:0]);
              end
              SecdedHamming_39_32: begin
                rw_data = prim_secded_hamming_39_32_enc(rw_data[ECC_DATA_WIDTH-1:0]);
              end
              default: begin
                `uvm_error(path,
                    $sformatf("MEM_ECC %0s is unsupported at mem_width[%0d]", MEM_ECC, mem_width))
              end
            endcase
            if (inject_num_errors) rw_data = inject_errors(rw_data, inject_num_errors);
          end
        end
        8: begin
          rw_data[addr[2:0] * MEM_BYTE_MSB +: 8] = data;
          if (MEM_PARITY) begin
            rw_data[addr[2:0] * MEM_BYTE_MSB + 8] = ~(^data);
            if (inject_num_errors) begin
              corrupted_data = rw_data[addr[2:0] * MEM_BYTE_MSB +: MEM_BYTE_MSB];
              corrupted_data[idx_to_corrupt] = !corrupted_data[idx_to_corrupt];
              rw_data[addr[2:0] * MEM_BYTE_MSB +: MEM_BYTE_MSB] = corrupted_data;
            end
          end else if (MEM_ECC != SecdedNone) begin
            case (MEM_ECC)
              Secded_72_64: begin
                rw_data = prim_secded_72_64_enc(rw_data[ECC_DATA_WIDTH-1:0]);
              end
              SecdedHamming_72_64: begin
                rw_data = prim_secded_hamming_72_64_enc(rw_data[ECC_DATA_WIDTH-1:0]);
              end
              default: begin
                `uvm_error(path,
                    $sformatf("MEM_ECC %0s is unsupported at mem_width[%0d]", MEM_ECC, mem_width))
              end
            endcase
            if (inject_num_errors) rw_data = inject_errors(rw_data, inject_num_errors);
          end
        end
        default: ;
      endcase
      `MEM_ARR_PATH_SLICE[mem_index] = rw_data;
    end
  endfunction

  function automatic void write16(input bit [bus_params_pkg::BUS_AW-1:0] addr,
                                  input bit [15:0] data,
                                  input int inject_num_errors = 0);
    `DV_CHECK_EQ_FATAL(addr[0], '0, $sformatf("addr 0x%0h not 16-bit aligned", addr), path)
    if (is_addr_valid(addr)) begin
      // Split the number of errors into different sub-byte write.
      int_pair_t inject_num_errors_split = rand_split(inject_num_errors);
      write8(addr, data[7:0], inject_num_errors_split.x);
      write8(addr + 1, data[15:8], inject_num_errors_split.y);
    end
  endfunction

  function automatic void write32(input bit [bus_params_pkg::BUS_AW-1:0] addr,
                                  input bit [31:0] data,
                                  input int inject_num_errors = 0);
    `DV_CHECK_EQ_FATAL(addr[1:0], '0, $sformatf("addr 0x%0h not 32-bit aligned", addr), path)
    if (is_addr_valid(addr)) begin
      // Split the number of errors into different sub-byte write.
      int_pair_t inject_num_errors_split = rand_split(inject_num_errors);
      write16(addr, data[15:0], inject_num_errors_split.x);
      write16(addr + 2, data[31:16], inject_num_errors_split.y);
    end
  endfunction

  function automatic void write64(input bit [bus_params_pkg::BUS_AW-1:0] addr,
                                  input bit [63:0] data,
                                  input int inject_num_errors = 0);
    // Split the number of errors into different sub-byte write.
    int_pair_t inject_num_errors_split = rand_split(inject_num_errors);
    `DV_CHECK_EQ_FATAL(addr[2:0], '0, $sformatf("addr 0x%0h not 64-bit aligned", addr), path)
    write32(addr, data[31:0], inject_num_errors_split.x);
    write32(addr + 4, data[63:32], inject_num_errors_split.y);
  endfunction

  /////////////////////////////////////////////////////////
  // Wrapper functions for memory reads with ECC enabled //
  /////////////////////////////////////////////////////////
  // Some notes:
  // - ECC isn't supported for 8-bit wide memories
  // - (28, 22) and (64, 57) ECC configurations aren't supported

  // Intended for use with memories which have data width of 16 bits and 6 ECC bits.
  function automatic secded_22_16_t ecc_read16(input bit [bus_params_pkg::BUS_AW-1:0] addr);
    if (is_addr_valid(addr)) begin
      int mem_index = addr >> mem_addr_lsb;
      // 22-bit wide memory word includes 16-bit data, 6-bit ECC bits
      bit [MAX_MEM_WIDTH-1:0] mem_data = `MEM_ARR_PATH_SLICE[mem_index];
      case (MEM_ECC)
        Secded_22_16:        return prim_secded_22_16_dec(mem_data);
        SecdedHamming_22_16: return prim_secded_hamming_22_16_dec(mem_data);
        default:             return 'x;
      endcase
    end
    return 'x;
  endfunction

  // Intended for use with memories which have data width of 32 bits and 7 ECC bits.
  function automatic secded_39_32_t ecc_read32(input bit [bus_params_pkg::BUS_AW-1:0] addr);
    if (is_addr_valid(addr)) begin
      int mem_index = addr >> mem_addr_lsb;
      // 39-bit wide memory word includes 32-bit data, 7-bit ECC bits
      bit [MAX_MEM_WIDTH-1:0] mem_data = `MEM_ARR_PATH_SLICE[mem_index];
      case (MEM_ECC)
        Secded_39_32:        return prim_secded_39_32_dec(mem_data);
        SecdedHamming_39_32: return prim_secded_hamming_39_32_dec(mem_data);
        default:             return 'x;
      endcase
    end
    return 'x;
  endfunction

  // Intended for use with memories which have data width of 64 bits and 8 ECC bits.
  function automatic secded_72_64_t ecc_read64(input bit [bus_params_pkg::BUS_AW-1:0] addr);
    if (is_addr_valid(addr)) begin
      int mem_index = addr >> mem_addr_lsb;
      // 72-bit wide memory word includes 64-bit data, 8-bit ECC bits
      bit [MAX_MEM_WIDTH-1:0] mem_data = `MEM_ARR_PATH_SLICE[mem_index];
      case (MEM_ECC)
        Secded_72_64:        return prim_secded_72_64_dec(mem_data);
        SecdedHamming_72_64: return prim_secded_hamming_72_64_dec(mem_data);
        default:             return 'x;
      endcase
    end
    return 'x;
  endfunction

  ///////////////////////////////////////////////////////////
  // Wrapper functions for encrypted read/write operations //
  ///////////////////////////////////////////////////////////

  function automatic logic [7:0] sram_encrypt_read8(input logic [bus_params_pkg::BUS_AW-1:0] addr,
                                                    input logic [SRAM_KEY_WIDTH-1:0]         key,
                                                    input logic [SRAM_BLOCK_WIDTH-1:0]       nonce);
    logic [7:0] rdata;
    logic [bus_params_pkg::BUS_AW-1:0] bus_addr;

    logic rdata_arr[]       = new[8];
    logic scrambled_addr[]  = new[mem_addr_width];
    logic sram_addr[]       = new[mem_addr_width];
    logic key_arr[]         = new[SRAM_KEY_WIDTH];
    logic nonce_arr[]       = new[SRAM_BLOCK_WIDTH];

    key_arr   = {<< {key}};
    nonce_arr = {<< {nonce}};

    for (int i = 0; i < mem_addr_width; i++) begin
      sram_addr[i] = addr[mem_addr_lsb + i];
    end

    // Calculate the scrambled address
    scrambled_addr = sram_scrambler_pkg::encrypt_sram_addr(sram_addr, mem_addr_width, nonce_arr);

    // Construct bus representation of the address
    for (int i = 0; i < mem_addr_lsb; i++) begin
      bus_addr[i] = addr[i];
    end
    for (int i = 0; i < mem_addr_width; i++) begin
      bus_addr[mem_addr_lsb + i] = scrambled_addr[i];
    end

    // Read memory, and return the decrypted data
    rdata = read8(bus_addr);
    rdata_arr = {<< {rdata}};

    rdata_arr = sram_scrambler_pkg::decrypt_sram_data(rdata_arr, 8,
                                                      sram_addr, mem_addr_width,
                                                      key_arr, nonce_arr);
    rdata = {<< {rdata_arr}};
    return rdata;
  endfunction

  function automatic logic [15:0]
  sram_encrypt_read16(input logic [bus_params_pkg::BUS_AW-1:0] addr,
                      input logic [SRAM_KEY_WIDTH-1:0]         key,
                      input logic [SRAM_BLOCK_WIDTH-1:0]       nonce);
    logic [15:0] rdata;
    logic [bus_params_pkg::BUS_AW-1:0] bus_addr;

    logic rdata_arr[]       = new[16];
    logic scrambled_addr[]  = new[mem_addr_width];
    logic sram_addr[]       = new[mem_addr_width];
    logic key_arr[]         = new[SRAM_KEY_WIDTH];
    logic nonce_arr[]       = new[SRAM_BLOCK_WIDTH];

    key_arr   = {<< {key}};
    nonce_arr = {<< {nonce}};

    for (int i = 0; i < mem_addr_width; i++) begin
      sram_addr[i] = addr[mem_addr_lsb + i];
    end

    // Calculate the scrambled address
    scrambled_addr = sram_scrambler_pkg::encrypt_sram_addr(sram_addr, mem_addr_width, nonce_arr);

    // Construct bus representation of the address
    for (int i = 0; i < mem_addr_lsb; i++) begin
      bus_addr[i] = addr[i];
    end
    for (int i = 0; i < mem_addr_width; i++) begin
      bus_addr[mem_addr_lsb + i] = scrambled_addr[i];
    end

    // Read memory and return the decrypted data
    rdata = read16(bus_addr);
    rdata_arr = {<< {rdata}};

    rdata_arr = sram_scrambler_pkg::decrypt_sram_data(rdata_arr, 16,
                                                      sram_addr, mem_addr_width,
                                                      key_arr, nonce_arr);
    rdata = {<< {rdata_arr}};
    return rdata;
  endfunction

  function automatic logic [31:0]
  sram_encrypt_read32(input logic [bus_params_pkg::BUS_AW-1:0] addr,
                      input logic [SRAM_KEY_WIDTH-1:0]         key,
                      input logic [SRAM_BLOCK_WIDTH-1:0]       nonce);
    logic [31:0] rdata = '0;
    logic [bus_params_pkg::BUS_AW-1:0] bus_addr = '0;

    logic rdata_arr[]       = new[32];
    logic scrambled_addr[]  = new[mem_addr_width];
    logic sram_addr[]       = new[mem_addr_width];
    logic key_arr[]         = new[SRAM_KEY_WIDTH];
    logic nonce_arr[]       = new[SRAM_BLOCK_WIDTH];

    key_arr   = {<< {key}};
    nonce_arr = {<< {nonce}};

    for (int i = 0; i < mem_addr_width; i++) begin
      sram_addr[i] = addr[mem_addr_lsb + i];
    end

    // Calculate the scrambled address
    scrambled_addr = sram_scrambler_pkg::encrypt_sram_addr(sram_addr, mem_addr_width, nonce_arr);

    // Construct bus representation of the address
    for (int i = 0; i < mem_addr_lsb; i++) begin
      bus_addr[i] = addr[i];
    end
    for (int i = 0; i < mem_addr_width; i++) begin
      bus_addr[mem_addr_lsb + i] = scrambled_addr[i];
    end

    `uvm_info(path, $sformatf("bus_addr: 0x%0x", bus_addr), UVM_HIGH)

    // Read memory and return the decrypted data
    rdata = read32(bus_addr);
    rdata_arr = {<< {rdata}};

    rdata_arr = sram_scrambler_pkg::decrypt_sram_data(rdata_arr, 32,
                                                      sram_addr, mem_addr_width,
                                                      key_arr, nonce_arr);
    rdata = {<< {rdata_arr}};
    return rdata;

  endfunction

  function automatic logic [63:0]
  sram_encrypt_read64(input logic [bus_params_pkg::BUS_AW-1:0] addr,
                      input logic [SRAM_KEY_WIDTH-1:0]         key,
                      input logic [SRAM_BLOCK_WIDTH-1:0]       nonce);
    logic [63:0] rdata;
    logic [bus_params_pkg::BUS_AW-1:0] bus_addr = '0;

    logic rdata_arr[]       = new[64];
    logic scrambled_addr[]  = new[mem_addr_width];
    logic sram_addr[]       = new[mem_addr_width];
    logic key_arr[]         = new[SRAM_KEY_WIDTH];
    logic nonce_arr[]       = new[SRAM_BLOCK_WIDTH];

    key_arr   = {<< {key}};
    nonce_arr = {<< {nonce}};

    for (int i = 0; i < mem_addr_width; i++) begin
      sram_addr[i] = addr[mem_addr_lsb + i];
    end

    // Calculate the scrambled address
    scrambled_addr = sram_scrambler_pkg::encrypt_sram_addr(sram_addr, mem_addr_width, nonce_arr);

    // Construct bus representation of the address
    for (int i = 0; i < mem_addr_lsb; i++) begin
      bus_addr[i] = addr[i];
    end
    for (int i = 0; i < mem_addr_width; i++) begin
      bus_addr[mem_addr_lsb + i] = scrambled_addr[i];
    end

    // Read memory and return the decrypted data
    rdata = read64(bus_addr);
    rdata_arr = {<< {rdata}};

    rdata_arr = sram_scrambler_pkg::decrypt_sram_data(rdata_arr, 64,
                                                      sram_addr, mem_addr_width,
                                                      key_arr, nonce_arr);
    rdata = {<< {rdata_arr}};
    return rdata;

  endfunction

  function automatic void sram_encrypt_write8(input logic [bus_params_pkg::BUS_AW-1:0] addr,
                                              input logic [7:0]                        data,
                                              input logic [SRAM_KEY_WIDTH-1:0]         key,
                                              input logic [SRAM_BLOCK_WIDTH-1:0]       nonce);
    logic [7:0] scrambled_data;
    logic [bus_params_pkg::BUS_AW-1:0] bus_addr = '0;

    logic wdata_arr[]       = new[8];
    logic scrambled_addr[]  = new[mem_addr_width];
    logic sram_addr[]       = new[mem_addr_width];
    logic key_arr[]         = new[SRAM_KEY_WIDTH];
    logic nonce_arr[]       = new[SRAM_BLOCK_WIDTH];

    key_arr   = {<< {key}};
    nonce_arr = {<< {nonce}};

    for (int i = 0; i < mem_addr_width; i++) begin
      sram_addr[i] = addr[mem_addr_lsb + i];
    end

    // Calculate the scrambled address
    scrambled_addr = sram_scrambler_pkg::encrypt_sram_addr(sram_addr, mem_addr_width, nonce_arr);

    // Calculate the scrambled data
    wdata_arr = {<< {data}};
    wdata_arr = sram_scrambler_pkg::encrypt_sram_data(wdata_arr, 8,
                                                      sram_addr, mem_addr_width,
                                                      key_arr, nonce_arr);
    // Construct bus representation of the address
    for (int i = 0; i < mem_addr_lsb; i++) begin
      bus_addr[i] = addr[i];
    end
    for (int i = 0; i < mem_addr_width; i++) begin
      bus_addr[mem_addr_lsb + i] = scrambled_addr[i];
    end

    // Write the scrambled data to memory
    scrambled_data = {<< {wdata_arr}};
    write8(bus_addr, scrambled_data);
  endfunction

  function automatic void sram_encrypt_write16(input logic [bus_params_pkg::BUS_AW-1:0] addr,
                                               input logic [15:0]                       data,
                                               input logic [SRAM_KEY_WIDTH-1:0]         key,
                                               input logic [SRAM_BLOCK_WIDTH-1:0]       nonce);
    logic [15:0] scrambled_data;
    logic [bus_params_pkg::BUS_AW-1:0] bus_addr = '0;

    logic wdata_arr[]       = new[16];
    logic scrambled_addr[]  = new[mem_addr_width];
    logic sram_addr[]       = new[mem_addr_width];
    logic key_arr[]         = new[SRAM_KEY_WIDTH];
    logic nonce_arr[]       = new[SRAM_BLOCK_WIDTH];

    key_arr   = {<< {key}};
    nonce_arr = {<< {nonce}};

    for (int i = 0; i < mem_addr_width; i++) begin
      sram_addr[i] = addr[mem_addr_lsb + i];
    end

    // Calculate the scrambled address
    scrambled_addr = sram_scrambler_pkg::encrypt_sram_addr(sram_addr, mem_addr_width, nonce_arr);

    // Calculate the scrambled data
    wdata_arr = {<< {data}};
    wdata_arr = sram_scrambler_pkg::encrypt_sram_data(wdata_arr, 16,
                                                      sram_addr, mem_addr_width,
                                                      key_arr, nonce_arr);
    // Construct bus representation of the address
    for (int i = 0; i < mem_addr_lsb; i++) begin
      bus_addr[i] = addr[i];
    end
    for (int i = 0; i < mem_addr_width; i++) begin
      bus_addr[mem_addr_lsb + i] = scrambled_addr[i];
    end

    // Write the scrambled data to memory
    scrambled_data = {<< {wdata_arr}};
    write16(bus_addr, scrambled_data);
  endfunction

  function automatic void sram_encrypt_write32(input logic [bus_params_pkg::BUS_AW-1:0] addr,
                                               input logic [31:0]                       data,
                                               input logic [SRAM_KEY_WIDTH-1:0]         key,
                                               input logic [SRAM_BLOCK_WIDTH-1:0]       nonce);
    logic [31:0] scrambled_data;
    logic [bus_params_pkg::BUS_AW-1:0] bus_addr = '0;

    logic wdata_arr[]       = new[32];
    logic scrambled_addr[]  = new[mem_addr_width];
    logic sram_addr[]       = new[mem_addr_width];
    logic key_arr[]         = new[SRAM_KEY_WIDTH];
    logic nonce_arr[]       = new[SRAM_BLOCK_WIDTH];

    key_arr   = {<< {key}};
    nonce_arr = {<< {nonce}};

    for (int i = 0; i < mem_addr_width; i++) begin
      sram_addr[i] = addr[mem_addr_lsb + i];
    end

    // Calculate the scrambled address
    scrambled_addr = sram_scrambler_pkg::encrypt_sram_addr(sram_addr, mem_addr_width, nonce_arr);

    // Calculate the scrambled data
    wdata_arr = {<< {data}};
    wdata_arr = sram_scrambler_pkg::encrypt_sram_data(wdata_arr, 32,
                                                      sram_addr, mem_addr_width,
                                                      key_arr, nonce_arr);
    // Construct bus representation of the address
    for (int i = 0; i < mem_addr_lsb; i++) begin
      bus_addr[i] = addr[i];
    end
    for (int i = 0; i < mem_addr_width; i++) begin
      bus_addr[mem_addr_lsb + i] = scrambled_addr[i];
    end

    // Write the scrambled data to memory
    scrambled_data = {<< {wdata_arr}};
    write32(bus_addr, scrambled_data);
  endfunction

  function automatic void sram_encrypt_write64(input logic [bus_params_pkg::BUS_AW-1:0] addr,
                                               input logic [63:0]                       data,
                                               input logic [SRAM_KEY_WIDTH-1:0]         key,
                                               input logic [SRAM_BLOCK_WIDTH-1:0]       nonce);
    logic [63:0] scrambled_data;
    logic [bus_params_pkg::BUS_AW-1:0] bus_addr = '0;

    logic wdata_arr[]       = new[64];
    logic scrambled_addr[]  = new[mem_addr_width];
    logic sram_addr[]       = new[mem_addr_width];
    logic key_arr[]         = new[SRAM_KEY_WIDTH];
    logic nonce_arr[]       = new[SRAM_BLOCK_WIDTH];

    key_arr   = {<< {key}};
    nonce_arr = {<< {nonce}};

    for (int i = 0; i < mem_addr_width; i++) begin
      sram_addr[i] = addr[mem_addr_lsb + i];
    end

    // Calculate the scrambled address
    scrambled_addr = sram_scrambler_pkg::encrypt_sram_addr(sram_addr, mem_addr_width, nonce_arr);

    // Calculate the scrambled data
    wdata_arr = {<< {data}};
    wdata_arr = sram_scrambler_pkg::encrypt_sram_data(wdata_arr, 64,
                                                      sram_addr, mem_addr_width,
                                                      key_arr, nonce_arr);
    // Construct bus representation of the address
    for (int i = 0; i < mem_addr_lsb; i++) begin
      bus_addr[i] = addr[i];
    end
    for (int i = 0; i < mem_addr_width; i++) begin
      bus_addr[mem_addr_lsb + i] = scrambled_addr[i];
    end

    // Write the scrambled data to memory
    scrambled_data = {<< {wdata_arr}};
    write64(bus_addr, scrambled_data);
  endfunction

  // Wrapper function for encrypted ROM reads
  // The data decoding is different from SRAM, but most of the underlying SRAM functions are reused
  // Also note that this function returns the raw data rather than data + syndrome + error because
  // the rom_ctrl testbench needs this for checking
  function automatic bit [39:0] rom_encrypt_read32(
      input bit [bus_params_pkg::BUS_AW-1:0] addr,
      input logic [SRAM_KEY_WIDTH-1:0]       key,
      input logic [SRAM_BLOCK_WIDTH-1:0]     nonce,
      input bit                              unscramble_data);

    logic [bus_params_pkg::BUS_AW-1:0] mem_addr = '0;
    logic [39:0]                       rdata    = '0;

    logic addr_arr[]       = new[mem_addr_width];
    logic scrambled_addr[] = new[mem_addr_width];
    logic rdata_arr[]      = new[40];
    logic key_arr[]        = new[SRAM_KEY_WIDTH];
    logic nonce_arr[]      = new[SRAM_BLOCK_WIDTH];
    logic keystream[]      = new[SRAM_BLOCK_WIDTH];
    logic zero_key[]       = new[40];

    key_arr   = {<< {key}};
    nonce_arr = {<< {nonce}};

    for (int i = 0; i < mem_addr_width; i++) begin
      addr_arr[i] = addr[i+mem_addr_lsb];
    end

    // Calculate the scrambled address
    scrambled_addr = sram_scrambler_pkg::encrypt_sram_addr(addr_arr, mem_addr_width, nonce_arr);

    for (int i = 0; i < mem_addr_width; i++) begin
      mem_addr[i] = scrambled_addr[i];
    end

    // Read memory and get the encrypted data
    if (!is_addr_valid(mem_addr << mem_addr_lsb)) begin
      return 'x;
    end

    // 39-bit memory word includes 32-bit data + 7-bit ECC
    rdata = `MEM_ARR_PATH_SLICE[mem_addr];

    if (!unscramble_data) begin
      return rdata;
    end

    rdata_arr = {<< {rdata}};

    // Generate the keystream
    keystream = sram_scrambler_pkg::gen_keystream(addr_arr, mem_addr_width, key_arr, nonce_arr);

    for (int i = 0; i < 40; i++) begin
      zero_key[i] = '0;
    end

    rdata_arr = sram_scrambler_pkg::sp_decrypt(rdata_arr, 40, zero_key);

    for (int i = 0; i < 40; i++) begin
      rdata[i] = rdata_arr[i] ^ keystream[i];
    end

    return rdata;

  endfunction

  // check if input file is read/writable
  function automatic void check_file(string file, bit wr);
    string mode = wr ? "w": "r";
    int fh = $fopen(file, mode);
    init();
    if (!fh) begin
      `uvm_fatal(path, $sformatf("file %0s could not be opened for %0s mode", file, mode))
    end
    else begin
      $fclose(fh);
    end
  endfunction

  // load mem from file
  function automatic void load_mem_from_file(string file);
    check_file(file, 1'b0);
    init();
    `uvm_info(path, $sformatf("Reading mem contents from file:\n%0s", file), UVM_LOW)
    $readmemh(file, `MEM_ARR_PATH_SLICE);
  endfunction

  // save mem contents to file
  function automatic void write_mem_to_file(string file);
    check_file(file, 1'b1);
    init();
    `uvm_info(path, $sformatf("Writing mem contents to file:\n%0s", file), UVM_LOW)
    $writememh(file, `MEM_ARR_PATH_SLICE, 0, mem_depth - 1);
  endfunction

  // print mem
  function automatic void print_mem();
    init();
    for (int i = 0; i < mem_depth; i++) begin
      `uvm_info(path, $sformatf("mem[%0d] = 0x%0h", i, `MEM_ARR_PATH_SLICE[i]), UVM_NONE)
    end
  endfunction

  // clear or set memory
  function automatic void clear_mem();
    init();
    `uvm_info(path, "Clear memory", UVM_LOW)
    if (MEM_PARITY || MEM_ECC != SecdedNone) begin
      // Have to manually loop over memory and clear to avoid overwriting any parity bits.
      for (int i = 0; i < mem_size_bytes; i++) begin
        write8(i, '0);
      end
    end else begin
      `MEM_ARR_PATH_SLICE = '{default:'0};
    end

  endfunction // clr_mem

  function automatic void set_mem();
    init();
    `uvm_info(path, "Set memory", UVM_LOW)
    if (MEM_PARITY || MEM_ECC != SecdedNone) begin
      // Have to manually loop over memory and set to avoid overwriting any parity bits.
      for (int i = 0; i < mem_size_bytes; i++) begin
        write8(i, '1);
      end
    end else begin
      `MEM_ARR_PATH_SLICE = '{default:'1};
    end
  endfunction

  // randomize the memory
  function automatic void randomize_mem();
    logic [7:0] rand_val;
    init();
    `uvm_info(path, "Randomizing mem contents", UVM_LOW)
    for (int i = 0; i < mem_size_bytes; i++) begin
      `DV_CHECK_STD_RANDOMIZE_FATAL(rand_val, "Randomization failed!", path)
      write8(i, rand_val);
    end
  endfunction

  // invalidate the memory.
  function automatic void invalidate_mem();
    init();
    `uvm_info(path, "Invalidating (Xs) mem contents", UVM_LOW)
    `MEM_ARR_PATH_SLICE = '{default:'X};
  endfunction

endinterface
