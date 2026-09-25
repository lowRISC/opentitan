// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Package-level (not class-bound) helpers for backdoor-accessing one row of the open-source
// rram_macro's storage arrays.
//
// Free functions that can be used by rram_ctrl_bkdr_util and its otp variant.
//
// rram_macro.sv protects each 128-bit word with two independent Hamming(72,64) SECDED codes, one
// per 64-bit half.
// These are computed via prim_secded_pkg::prim_secded_hamming_72_64_enc/_dec, the same primitive
// used all over OpenTitan, not a hand-derived encoding.
// The physical row layout groups both 8-bit check-bit bytes at the MSBs, with the 128 data bits
// unchanged and contiguous below:
//   {ecc_hi[7:0], ecc_lo[7:0], data_hi[63:0], data_lo[63:0]}
// This does not match mem_bkdr_util's generic subword-ECC mechanism, which assumes each subword's
// check bits sit next to that subword's own data, not grouped together.
// So these functions bypass that mechanism entirely and encode/decode the row directly.
//
//   emul_encode_word: 128-bit data word to 144-bit physical row.
//   rram_row_write:   encode and backdoor-deposit a data word at a row path.
//   rram_row_read:    backdoor-read a row path and extract back to a data word.
//
// Bulk vmem loading (load_mem_from_file() in rram_ctrl_bkdr_util.sv/rram_ctrl_otp_bkdr_util.sv)
// no longer needs a conversion helper here: gen-rram-img.py always emits full 144-bit physical
// rows now, matching this array's own width directly.

localparam int unsigned EmulDataWidth     = 128;
localparam int unsigned EmulEccWordWidth  = 64;
localparam int unsigned EmulEccCodeWidth  = 72;
localparam int unsigned EmulEccCheckWidth = EmulEccCodeWidth - EmulEccWordWidth; // 8
localparam int unsigned EmulFullRowWidth  = EmulDataWidth + 2 * EmulEccCheckWidth; // 144

// Encodes a 128-bit data word into rram_macro's native 144-bit physical row:
//   {ecc_hi[7:0], ecc_lo[7:0], data_hi[63:0], data_lo[63:0]}
// Mirrors rram_macro.sv's own encode path (two prim_secded_hamming_72_64_enc instances, one per
// 64-bit half), so backdoor-loaded images match what the real encoder would produce.
function automatic bit [EmulFullRowWidth-1:0] emul_encode_word(bit [EmulDataWidth-1:0] data);
  bit [EmulEccWordWidth-1:0] data_lo, data_hi;
  bit [EmulEccCodeWidth-1:0] codeword_lo, codeword_hi;

  data_lo = data[EmulEccWordWidth-1:0];
  data_hi = data[EmulDataWidth-1:EmulEccWordWidth];

  codeword_lo = prim_secded_pkg::prim_secded_hamming_72_64_enc(data_lo);
  codeword_hi = prim_secded_pkg::prim_secded_hamming_72_64_enc(data_hi);

  return {codeword_hi[EmulEccCodeWidth-1:EmulEccWordWidth],
          codeword_lo[EmulEccCodeWidth-1:EmulEccWordWidth],
          data};
endfunction

// Backdoor-deposits `data`'s low 128 bits into rram_macro's row at `row_path` (a full hierarchical
// reference to a single row, e.g. "tb.dut...u_data_array.mem[123]"), packed into its native 144-bit
// physical representation with freshly-computed ECC (see `emul_encode_word()`).
//
// Every write recomputes ECC fresh from the 128 data bits being written.
// It does not attempt to preserve or merge with any previously-stored ECC bits.
function automatic void rram_row_write(string row_path, bit [EmulDataWidth-1:0] data);
  if (!uvm_hdl_deposit(row_path, emul_encode_word(data))) begin
    `uvm_error("rram_row_write", $sformatf("Failed to deposit %0s with uvm_hdl_deposit.", row_path))
  end
endfunction

// Backdoor-reads rram_macro's row at `row_path` and returns only the low 128 data bits.
//
// Does not run the ECC decoder (prim_secded_hamming_72_64_dec).
// This reads back whatever data bits are stored, without detecting or correcting errors in the
// codeword.
// That's sufficient for reading back known-good backdoor-loaded data, but not for exercising the
// macro's own error detection/correction.
function automatic bit [EmulDataWidth-1:0] rram_row_read(string row_path);
  uvm_hdl_data_t raw;
  if (!uvm_hdl_read(row_path, raw)) begin
    `uvm_error("rram_row_read", $sformatf("Failed to read %0s with uvm_hdl_read.", row_path))
  end
  return raw[EmulDataWidth-1:0];
endfunction
