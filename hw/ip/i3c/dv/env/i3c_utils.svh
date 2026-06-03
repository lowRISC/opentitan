// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// I3C Helper functions; behavioral implementations of I3C-related operations.
//
// - May be useful in constructing a proper DV test bench/environment.
// - These are used within the basic IP test bench for now.

// Calculate/update parity bits for HDR messages.
function automatic bit [1:0] update_parity(bit data[], bit [1:0] parity = 2'b01);
  // NOTE: This assumes that every block of bits supplied to the parity calculation
  // has an even number of bits, except possibly the last.
  for (int unsigned b = 0; b < data.size(); b++) begin
    if (b[0]) parity[0] ^= data[b];
    else parity[1] ^= data[b];
  end
  return parity;
endfunction

// Calculate/update a CRC-5 value
function automatic bit [4:0] update_crc5(bit data[], bit [4:0] crc5 = 5'h1F);
  for (int unsigned b = 0; b < data.size(); b++) begin
    crc5 = {crc5[3:2], data[b] ^ crc5[4] ^ crc5[1], crc5[0], data[b] ^ crc5[4]};
  end
  return crc5;
endfunction

// Report the contents of a Device Address Table entry.
function automatic void report_dat_entry(int unsigned idx, i3c_pkg::i3c_dat_entry_t dat);
  $display("%02x: STAT_ADDR %02x IBI_PAYLOAD %d IBI_REJECT %d CRR_REJECT %d TS %d DYN_ADDR %02x",
           idx, dat.static_address, dat.ibi_payload, dat.ibi_reject, dat.crr_reject, dat.ts,
           dat.dynamic_address);
  $display("    RING_ID %d NACK_RETRY_CNT %d I2C %d AUTOCMD_MASK %02x VALUE %02x MODE %d HDR %02x",
           dat.ring_id, dat.dev_nack_retry_cnt, dat.device, dat.autocmd_mask, dat.autocmd_value,
           dat.autocmd_mode, dat.autocmd_hdr_code);
endfunction

// Report the contents of a Device Characteristics Table entry.
function automatic void report_dct_entry(int unsigned idx, i3c_pkg::i3c_dct_entry_t dct);
  $display("%02x: PID %08x%04x DCR %02x BCR %02x DYN_ADDR %02x", idx,
           dct.pid_hi, dct.pid_lo, dct.dcr, dct.bcr, dct.dynamic_address);
endfunction
