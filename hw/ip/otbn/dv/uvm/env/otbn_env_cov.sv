// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

/**
 * Covergoups that are dependent on run-time parameters that may be available
 * only in build_phase can be defined here
 * Covergroups may also be wrapped inside helper classes if needed.
 */

class otbn_env_cov extends cip_base_env_cov #(.CFG_T(otbn_env_cfg));
  `uvm_component_utils(otbn_env_cov)

  covergroup insn_cg
    with function sample(mnem_str_t mnemonic);

    // A coverpoint for the instruction mnemonic. There's a manually specified bin for each valid
    // instruction name. The bins are listed separately like this (rather than having a single bins
    // line with each value) so that the names appear in the coverage report. The "mnem_" prefix is
    // just to avoid SystemVerilog reserved words like "and".
    mnemonic_cp: coverpoint mnemonic {
        bins mnem_add           = {mnem_str_t'("add")};
        bins mnem_addi          = {mnem_str_t'("addi")};
        bins mnem_lui           = {mnem_str_t'("lui")};
        bins mnem_sub           = {mnem_str_t'("sub")};
        bins mnem_sll           = {mnem_str_t'("sll")};
        bins mnem_slli          = {mnem_str_t'("slli")};
        bins mnem_srl           = {mnem_str_t'("srl")};
        bins mnem_srli          = {mnem_str_t'("srli")};
        bins mnem_sra           = {mnem_str_t'("sra")};
        bins mnem_srai          = {mnem_str_t'("srai")};
        bins mnem_and           = {mnem_str_t'("and")};
        bins mnem_andi          = {mnem_str_t'("andi")};
        bins mnem_or            = {mnem_str_t'("or")};
        bins mnem_ori           = {mnem_str_t'("ori")};
        bins mnem_xor           = {mnem_str_t'("xor")};
        bins mnem_xori          = {mnem_str_t'("xori")};
        bins mnem_lw            = {mnem_str_t'("lw")};
        bins mnem_sw            = {mnem_str_t'("sw")};
        bins mnem_beq           = {mnem_str_t'("beq")};
        bins mnem_bne           = {mnem_str_t'("bne")};
        bins mnem_jal           = {mnem_str_t'("jal")};
        bins mnem_jalr          = {mnem_str_t'("jalr")};
        bins mnem_csrrs         = {mnem_str_t'("csrrs")};
        bins mnem_csrrw         = {mnem_str_t'("csrrw")};
        bins mnem_ecall         = {mnem_str_t'("ecall")};
        bins mnem_loop          = {mnem_str_t'("loop")};
        bins mnem_loopi         = {mnem_str_t'("loopi")};
        bins mnem_bn_add        = {mnem_str_t'("bn.add")};
        bins mnem_bn_addc       = {mnem_str_t'("bn.addc")};
        bins mnem_bn_addi       = {mnem_str_t'("bn.addi")};
        bins mnem_bn_addm       = {mnem_str_t'("bn.addm")};
        bins mnem_bn_mulqacc    = {mnem_str_t'("bn.mulqacc")};
        bins mnem_bn_mulqacc_wo = {mnem_str_t'("bn.mulqacc.wo")};
        bins mnem_bn_mulqacc_so = {mnem_str_t'("bn.mulqacc.so")};
        bins mnem_bn_sub        = {mnem_str_t'("bn.sub")};
        bins mnem_bn_subb       = {mnem_str_t'("bn.subb")};
        bins mnem_bn_subi       = {mnem_str_t'("bn.subi")};
        bins mnem_bn_subm       = {mnem_str_t'("bn.subm")};
        bins mnem_bn_and        = {mnem_str_t'("bn.and")};
        bins mnem_bn_or         = {mnem_str_t'("bn.or")};
        bins mnem_bn_not        = {mnem_str_t'("bn.not")};
        bins mnem_bn_xor        = {mnem_str_t'("bn.xor")};
        bins mnem_bn_rshi       = {mnem_str_t'("bn.rshi")};
        bins mnem_bn_sel        = {mnem_str_t'("bn.sel")};
        bins mnem_bn_cmp        = {mnem_str_t'("bn.cmp")};
        bins mnem_bn_cmpb       = {mnem_str_t'("bn.cmpb")};
        bins mnem_bn_lid        = {mnem_str_t'("bn.lid")};
        bins mnem_bn_sid        = {mnem_str_t'("bn.sid")};
        bins mnem_bn_mov        = {mnem_str_t'("bn.mov")};
        bins mnem_bn_movr       = {mnem_str_t'("bn.movr")};
        bins mnem_bn_wsrr       = {mnem_str_t'("bn.wsrr")};
        bins mnem_bn_wsrw       = {mnem_str_t'("bn.wsrw")};
    }
  endgroup

  function new(string name, uvm_component parent);
    super.new(name, parent);

    insn_cg = new;
  endfunction

endclass
