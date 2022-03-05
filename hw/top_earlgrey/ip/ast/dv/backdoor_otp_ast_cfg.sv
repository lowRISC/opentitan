// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Backdoor OTP Load for AST Setup
cfg.mem_bkdr_util_h[Otp].write32(otp_ctrl_reg_pkg::CreatorSwCfgAstCfgOffset,     32'h00000000);  // 0x000
cfg.mem_bkdr_util_h[Otp].write32(otp_ctrl_reg_pkg::CreatorSwCfgAstCfgOffset+4,   32'h00010001);  // 0x004
cfg.mem_bkdr_util_h[Otp].write32(otp_ctrl_reg_pkg::CreatorSwCfgAstCfgOffset+8,   32'h00020002);  // 0x008
cfg.mem_bkdr_util_h[Otp].write32(otp_ctrl_reg_pkg::CreatorSwCfgAstCfgOffset+12,  32'h00030003);  // 0x00C
cfg.mem_bkdr_util_h[Otp].write32(otp_ctrl_reg_pkg::CreatorSwCfgAstCfgOffset+16,  32'h00040004);  // 0x010
cfg.mem_bkdr_util_h[Otp].write32(otp_ctrl_reg_pkg::CreatorSwCfgAstCfgOffset+20,  32'h00050005);  // 0x014
cfg.mem_bkdr_util_h[Otp].write32(otp_ctrl_reg_pkg::CreatorSwCfgAstCfgOffset+24,  32'h00060006);  // 0x018
cfg.mem_bkdr_util_h[Otp].write32(otp_ctrl_reg_pkg::CreatorSwCfgAstCfgOffset+28,  32'h00070007);  // 0x01C
cfg.mem_bkdr_util_h[Otp].write32(otp_ctrl_reg_pkg::CreatorSwCfgAstCfgOffset+32,  32'h00080008);  // 0x020
cfg.mem_bkdr_util_h[Otp].write32(otp_ctrl_reg_pkg::CreatorSwCfgAstCfgOffset+36,  32'h00090009);  // 0x024
cfg.mem_bkdr_util_h[Otp].write32(otp_ctrl_reg_pkg::CreatorSwCfgAstCfgOffset+40,  32'h00100010);  // 0x028
cfg.mem_bkdr_util_h[Otp].write32(otp_ctrl_reg_pkg::CreatorSwCfgAstCfgOffset+44,  32'h00110011);  // 0x02C
cfg.mem_bkdr_util_h[Otp].write32(otp_ctrl_reg_pkg::CreatorSwCfgAstCfgOffset+48,  32'h00120012);  // 0x030
cfg.mem_bkdr_util_h[Otp].write32(otp_ctrl_reg_pkg::CreatorSwCfgAstCfgOffset+52,  32'h00130013);  // 0x034
cfg.mem_bkdr_util_h[Otp].write32(otp_ctrl_reg_pkg::CreatorSwCfgAstCfgOffset+56,  32'h00140014);  // 0x038
cfg.mem_bkdr_util_h[Otp].write32(otp_ctrl_reg_pkg::CreatorSwCfgAstCfgOffset+60,  32'h00150015);  // 0x03C
cfg.mem_bkdr_util_h[Otp].write32(otp_ctrl_reg_pkg::CreatorSwCfgAstCfgOffset+64,  32'h00160016);  // 0x040
cfg.mem_bkdr_util_h[Otp].write32(otp_ctrl_reg_pkg::CreatorSwCfgAstCfgOffset+68,  32'h00170017);  // 0x044
cfg.mem_bkdr_util_h[Otp].write32(otp_ctrl_reg_pkg::CreatorSwCfgAstCfgOffset+72,  32'h00180018);  // 0x048
cfg.mem_bkdr_util_h[Otp].write32(otp_ctrl_reg_pkg::CreatorSwCfgAstCfgOffset+76,  32'h00190019);  // 0x04C
cfg.mem_bkdr_util_h[Otp].write32(otp_ctrl_reg_pkg::CreatorSwCfgAstCfgOffset+80,  32'h00200020);  // 0x050
cfg.mem_bkdr_util_h[Otp].write32(otp_ctrl_reg_pkg::CreatorSwCfgAstCfgOffset+84,  32'h00210021);  // 0x054
cfg.mem_bkdr_util_h[Otp].write32(otp_ctrl_reg_pkg::CreatorSwCfgAstCfgOffset+88,  32'h00220022);  // 0x058
cfg.mem_bkdr_util_h[Otp].write32(otp_ctrl_reg_pkg::CreatorSwCfgAstCfgOffset+92,  32'h00230023);  // 0x05C
cfg.mem_bkdr_util_h[Otp].write32(otp_ctrl_reg_pkg::CreatorSwCfgAstCfgOffset+96,  32'h00240024);  // 0x060
cfg.mem_bkdr_util_h[Otp].write32(otp_ctrl_reg_pkg::CreatorSwCfgAstCfgOffset+100, 32'h00250025);  // 0x064
cfg.mem_bkdr_util_h[Otp].write32(otp_ctrl_reg_pkg::CreatorSwCfgAstCfgOffset+104, 32'h00260026);  // 0x068
cfg.mem_bkdr_util_h[Otp].write32(otp_ctrl_reg_pkg::CreatorSwCfgAstCfgOffset+108, 32'h00270027);  // 0x06C
cfg.mem_bkdr_util_h[Otp].write32(otp_ctrl_reg_pkg::CreatorSwCfgAstCfgOffset+112, 32'h00280028);  // 0x070
cfg.mem_bkdr_util_h[Otp].write32(otp_ctrl_reg_pkg::CreatorSwCfgAstCfgOffset+116, 32'h00290029);  // 0x074
cfg.mem_bkdr_util_h[Otp].write32(otp_ctrl_reg_pkg::CreatorSwCfgAstCfgOffset+120, 32'h00300030);  // 0x078
cfg.mem_bkdr_util_h[Otp].write32(otp_ctrl_reg_pkg::CreatorSwCfgAstCfgOffset+124, 32'h00310031);  // 0x07C
