// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

package digestpp_dpi_pkg;

  // dep packages

  // macro includes

  // parameters

  // DPI-C imports
  import "DPI-C" context function void c_dpi_sha3_224(
    input bit[7:0]      msg[],
    input int unsigned  msg_len,
    output bit[7:0]     digest[]
  );

  import "DPI-C" context function void c_dpi_sha3_256(
    input bit[7:0]      msg[],
    input int unsigned  msg_len,
    output bit[7:0]     digest[]
  );

  import "DPI-C" context function void c_dpi_sha3_384(
    input bit[7:0]      msg[],
    input int unsigned  msg_len,
    output bit[7:0]     digest[]
  );

  import "DPI-C" context function void c_dpi_sha3_512(
    input bit[7:0]      msg[],
    input int unsigned  msg_len,
    output bit[7:0]     digest[]
  );

  import "DPI-C" context function void c_dpi_shake128(
    input bit[7:0]          msg[],
    input longint unsigned  msg_len,
    input longint unsigned  output_len,
    output bit[7:0]         digest[]
  );

  import "DPI-C" context function void c_dpi_shake256(
    input bit[7:0]          msg[],
    input longint unsigned  msg_len,
    input longint unsigned  output_len,
    output bit[7:0]         digest[]
  );

  import "DPI-C" context function void c_dpi_cshake128(
    input bit[7:0]          msg[],
    input string            function_name,
    input string            customization_str,
    input longint unsigned  msg_len,
    input longint unsigned  output_len,
    output bit[7:0]         digest[]
  );

  import "DPI-C" context function void c_dpi_cshake256(
    input bit[7:0]          msg[],
    input string            function_name,
    input string            customization_str,
    input longint unsigned  msg_len,
    input longint unsigned  output_len,
    output bit[7:0]         digest[]
  );

  import "DPI-C" context function void c_dpi_kmac128(
    input bit[7:0]          msg[],
    input longint unsigned  msg_len,
    input bit[7:0]          key[],
    input longint unsigned  key_len,
    input string            customization_str,
    input longint unsigned  output_len,
    output bit[7:0]         digest[]
  );

  import "DPI-C" context function void c_dpi_kmac128_xof(
    input bit[7:0]          msg[],
    input longint unsigned  msg_len,
    input bit[7:0]          key[],
    input longint unsigned  key_len,
    input string            customization_str,
    input longint unsigned  output_len,
    output bit[7:0]         digest[]
  );

  import "DPI-C" context function void c_dpi_kmac256(
    input bit[7:0]          msg[],
    input longint unsigned  msg_len,
    input bit[7:0]          key[],
    input longint unsigned  key_len,
    input string            customization_str,
    input longint unsigned  output_len,
    output bit[7:0]         digest[]
  );

  import "DPI-C" context function void c_dpi_kmac256_xof(
    input bit[7:0]          msg[],
    input longint unsigned  msg_len,
    input bit[7:0]          key[],
    input longint unsigned  key_len,
    input string            customization_str,
    input longint unsigned  output_len,
    output bit[7:0]         digest[]
  );

endpackage
