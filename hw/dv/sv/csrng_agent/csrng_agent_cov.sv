// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class csrng_agent_cov extends dv_base_agent_cov#(csrng_agent_cfg);
  `uvm_component_utils(csrng_agent_cov)

  // covergroups
  covergroup cmd_cg with function sample(csrng_item item, bit sts);
    option.name         = "csrng_cmd_cg";
    option.per_instance = 1;

    csrng_cmd_cp: coverpoint item.acmd {
      bins inv = {INV};
      bins ins = {INS};
      bins res = {RES};
      bins gen = {GEN};
      bins upd = {UPD};
      bins genb = {GENB};
      bins genu = {GENU};
      illegal_bins il = default;
    }
    csrng_clen_cp: coverpoint item.clen {
      bins zero = {0};
      bins other_bins[2] = {[1:15]};
    }
    // TODO: do not use enum to sample non-true/false data
    csrng_flag_cp: coverpoint item.flags {
      bins mubi_true = {MuBi4True};
      bins mubi_false = {MuBi4False};
    }
    csrng_sts: coverpoint sts {
      bins pass = {0};
      bins fail = {1};
    }

    csrng_cmd_cross: cross csrng_cmd_cp, csrng_clen_cp, csrng_sts, csrng_flag_cp;
  endgroup

  covergroup genbits_cg with function sample(csrng_item item, bit sts);
    option.name         = "csrng_genbits_cg";
    option.per_instance = 1;

    csrng_glen: coverpoint item.glen {
      // TODO: current max length is limited.
      bins glens[5] = {[1:80]};
    }
    csrng_sts: coverpoint sts {
      bins pass = {0};
      bins fail = {1};
    }

    csrng_genbits_cross: cross csrng_glen, csrng_sts;
  endgroup

  function new(string name, uvm_component parent);
    super.new(name, parent);
    cmd_cg = new();
    genbits_cg = new();
  endfunction

  function void sample_csrng_cmds(csrng_item item, bit sts);
    cmd_cg.sample(item, cfg.vif.cmd_rsp.csrng_rsp_sts);
    if (item.acmd == csrng_pkg::GEN) genbits_cg.sample(item, cfg.vif.cmd_rsp.csrng_rsp_sts);
  endfunction

endclass
