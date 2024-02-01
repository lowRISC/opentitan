// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

package cryptoc_dpi_pkg;
  // dep packages
  import uvm_pkg::*;

  // macro includes
  `include "uvm_macros.svh"

  // DPI-C imports
  //
  // Note: alas we must supply the array lengths as additional parameters to appease xcelium
  //       which would otherwise raise E,MEMALC when the DPI-C code even tries to invoke
  //       svSize(msg, 1) on an empty one-dimensional array.
  import "DPI-C" context function void c_dpi_SHA_hash(input bit[7:0] msg[],
                                                      input longint unsigned len,
                                                      output int unsigned hash[8]);

  import "DPI-C" context function void c_dpi_SHA256_hash(input bit[7:0] msg[],
                                                         input longint unsigned len,
                                                         output int unsigned hash[8]);

  import "DPI-C" context function void c_dpi_SHA384_hash(input bit[7:0] msg[],
                                                         input longint unsigned len,
                                                         output int unsigned hash[12]);

  import "DPI-C" context function void c_dpi_SHA512_hash(input bit[7:0] msg[],
                                                         input longint unsigned len,
                                                         output int unsigned hash[16]);

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

  import "DPI-C" context function void c_dpi_HMAC_SHA384(input bit[7:0] key[],
                                                         input longint unsigned key_len,
                                                         input bit[7:0] msg[],
                                                         input longint unsigned msg_len,
                                                         output int unsigned hmac[12]);

  import "DPI-C" context function void c_dpi_HMAC_SHA512(input bit[7:0] key[],
                                                         input longint unsigned key_len,
                                                         input bit[7:0] msg[],
                                                         input longint unsigned msg_len,
                                                         output int unsigned hmac[16]);

  // sv wrapper functions
  function automatic void sv_dpi_get_sha_digest(input bit[7:0] msg[],
                                                output int unsigned hash[8]);
    c_dpi_SHA_hash(msg, msg.size(), hash);
  endfunction

  function automatic void sv_dpi_get_sha256_digest(input bit[7:0] msg[],
                                                   output int unsigned hash[8]);
    c_dpi_SHA256_hash(msg, msg.size(), hash);
  endfunction

  function automatic void sv_dpi_get_sha384_digest(input bit[7:0] msg[],
                                                   output int unsigned hash[12]);
    c_dpi_SHA384_hash(msg, msg.size(), hash);
  endfunction

  function automatic void sv_dpi_get_sha512_digest(input bit[7:0] msg[],
                                                   output int unsigned hash[16]);
    c_dpi_SHA512_hash(msg, msg.size(), hash);
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

  function automatic void sv_dpi_get_hmac_sha384(input bit[31:0] key[],
                                                 input bit[7:0]  msg[],
                                                 output int unsigned hmac[12]);
    bit [7:0] ckey[];
    int ckey_size_bytes = $bits(key) / 8;
    ckey = new[ckey_size_bytes];
    {>>{ckey}} = key;
    c_dpi_HMAC_SHA384(ckey, ckey.size(), msg, msg.size(), hmac);
  endfunction

  function automatic void sv_dpi_get_hmac_sha512(input bit[31:0] key[],
                                                 input bit[7:0]  msg[],
                                                 output int unsigned hmac[16]);
    bit [7:0] ckey[];
    int ckey_size_bytes = $bits(key) / 8;
    ckey = new[ckey_size_bytes];
    {>>{ckey}} = key;
    c_dpi_HMAC_SHA512(ckey, ckey.size(), msg, msg.size(), hmac);
  endfunction

endpackage
