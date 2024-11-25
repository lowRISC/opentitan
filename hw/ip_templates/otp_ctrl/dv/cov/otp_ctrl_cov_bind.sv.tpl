// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Binds OTP_CTRL functional coverage interaface to the top level OTP_CTRL module.
//
${gen_comment}
<%
from topgen.lib import Name

# The unsavory ${"\\"} tokens are used to escape the macros newline handling.
%>\
`define PART_MUBI_COV(__part_name, __index)                                           ${"\\"}
  bind otp_ctrl cip_mubi_cov_if #(.Width(8)) ``__part_name``_read_lock_mubi_cov_if (  ${"\\"}
    .rst_ni (rst_ni),                                                                 ${"\\"}
    .mubi   (part_access[``__index``].read_lock)                                      ${"\\"}
  );                                                                                  ${"\\"}
  bind otp_ctrl cip_mubi_cov_if #(.Width(8)) ``__part_name``_write_lock_mubi_cov_if ( ${"\\"}
    .rst_ni (rst_ni),                                                                 ${"\\"}
    .mubi   (part_access[``__index``].write_lock)                                     ${"\\"}
  );

`define DAI_MUBI_COV(__part_name, __index)                                                ${"\\"}
  bind otp_ctrl cip_mubi_cov_if #(.Width(8)) dai_``__part_name``_read_lock_mubi_cov_if (  ${"\\"}
    .rst_ni (rst_ni),                                                                     ${"\\"}
    .mubi   (part_access_dai[``__index``].read_lock)                                      ${"\\"}
  );                                                                                      ${"\\"}
  bind otp_ctrl cip_mubi_cov_if #(.Width(8)) dai_``__part_name``_write_lock_mubi_cov_if ( ${"\\"}
    .rst_ni (rst_ni),                                                                     ${"\\"}
    .mubi   (part_access_dai[``__index``].write_lock)                                     ${"\\"}
  );

module otp_ctrl_cov_bind;
  import otp_ctrl_part_pkg::*;

  bind otp_ctrl otp_ctrl_cov_if u_otp_ctrl_cov_if (
    .pwr_otp_o        (pwr_otp_o),
    .lc_otp_program_i (lc_otp_program_i),
    .lc_escalate_en_i (lc_escalate_en_i),
    .flash_otp_key_i  (flash_otp_key_i),
    .sram_otp_key_i   (sram_otp_key_i),
    .otbn_otp_key_i   (otbn_otp_key_i)
  );

  bind otp_ctrl cip_lc_tx_cov_if u_lc_creator_seed_sw_rw_en_cov_if (
    .rst_ni (rst_ni),
    .val    (lc_creator_seed_sw_rw_en_i)
  );

  bind otp_ctrl cip_lc_tx_cov_if u_lc_seed_hw_rd_en_cov_if (
    .rst_ni (rst_ni),
    .val    (lc_seed_hw_rd_en_i)
  );

  bind otp_ctrl cip_lc_tx_cov_if u_lc_dft_en_cov_if (
    .rst_ni (rst_ni),
    .val    (lc_dft_en_i)
  );

  bind otp_ctrl cip_lc_tx_cov_if u_lc_escalate_en_cov_if (
    .rst_ni (rst_ni),
    .val    (lc_escalate_en_i)
  );

  bind otp_ctrl cip_lc_tx_cov_if u_lc_check_byp_en_cov_if (
    .rst_ni (rst_ni),
    .val    (lc_check_byp_en_i)
  );

  // Mubi internal coverage for buffered and unbuffered partitions.
% for part in otp_mmap.config["partitions"][:-1]:
<% part_name = Name.from_snake_case(part["name"]) %>\
  `PART_MUBI_COV(${part_name.as_snake_case()}, otp_ctrl_part_pkg::${part_name.as_camel_case()}Idx)
% endfor

  // Mubi internal coverage for DAI interface access
% for part in otp_mmap.config["partitions"][:-1]:
<% part_name = Name.from_snake_case(part["name"]) %>\
  `DAI_MUBI_COV(${part_name.as_snake_case()}, otp_ctrl_part_pkg::${part_name.as_camel_case()}Idx)
% endfor

`undef PART_MUBI_COV
`undef DAI_MUBI_COV
endmodule
