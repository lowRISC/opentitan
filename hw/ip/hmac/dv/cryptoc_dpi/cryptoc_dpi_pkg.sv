// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

package cryptoc_dpi_pkg;
  // dep packages
  import uvm_pkg::*;

  // macro includes
  `include "uvm_macros.svh"

  // DPI-C imports
  import "DPI-C" context function void c_dpi_SHA_hash(input bit[7:0] msg[],
                                                      input longint unsigned len,
                                                      output int unsigned hash[8]);

  import "DPI-C" context function void c_dpi_SHA256_hash(input bit[7:0] msg[],
                                                         input longint unsigned len,
                                                         output int unsigned hash[8]);

  import "DPI-C" context function void c_dpi_HMAC_SHA(input bit[7:0] key[],
                                                      input longint unsigned key_len,
                                                      input bit[7:0] msg[],
                                                      input longint unsigned msg_len,
                                                      output int unsigned hmac[8]);

  import "DPI-C" context function void c_dpi_HMAC_SHA256(input bit[7:0] key[],
                                                         input longint unsigned key_len,
                                                         input bit[7:0] msg[],
                                                         input longint unsigned msg_len,
                                                         output int unsigned hmac[8]);

  // sv wrapper functions
  function automatic void sv_dpi_get_sha_digest(input bit[7:0] msg[],
                                                output int unsigned hash[8]);
    c_dpi_SHA_hash(msg, msg.size(), hash);
  endfunction

  function automatic void sv_dpi_get_sha256_digest(input bit[7:0] msg[],
                                                   output int unsigned hash[8]);
    c_dpi_SHA256_hash(msg, msg.size(), hash);
  endfunction

  function automatic void sv_dpi_get_hmac_sha(input bit[31:0] key[],
                                              input bit[7:0] msg[],
                                              output int unsigned hmac[8]);
    bit [7:0] ckey[];
    int ckey_size_bytes = $bits(key) / 8;
    ckey = new[ckey_size_bytes];
    {>>{ckey}} = key;
    c_dpi_HMAC_SHA(ckey, ckey.size(), msg, msg.size(), hmac);
  endfunction

  function automatic void sv_dpi_get_hmac_sha256(input bit[31:0] key[],
                                                 input bit[7:0]  msg[],
                                                 output int unsigned hmac[8]);
    bit [7:0] ckey[];
    int ckey_size_bytes = $bits(key) / 8;
    ckey = new[ckey_size_bytes];
    {>>{ckey}} = key;
    c_dpi_HMAC_SHA256(ckey, ckey.size(), msg, msg.size(), hmac);
  endfunction

endpackage
