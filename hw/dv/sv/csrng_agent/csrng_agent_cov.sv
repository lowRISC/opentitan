// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// covergroups
// Depends on whether the agent is device or host mode, the "csrng_cmd_cp" are slightly different:
// In device mode: acmd INV, GENB, GENU are in the illegal bin.
covergroup device_cmd_cg with function sample(csrng_item item, bit sts);
  option.name         = "csrng_device_cmd_cg";
  option.per_instance = 1;

  csrng_cmd_cp: coverpoint item.acmd {
    bins ins = {INS};
    bins res = {RES};
    bins gen = {GEN};
    bins upd = {UPD};
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

covergroup host_cmd_cg with function sample(csrng_item item, bit sts);
  option.name         = "csrng_host_cmd_cg";
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

class csrng_agent_cov extends dv_base_agent_cov#(csrng_agent_cfg);
  host_cmd_cg   m_host_cmd_cg;
  device_cmd_cg m_device_cmd_cg;
  genbits_cg    m_genbits_cg;

  `uvm_component_utils(csrng_agent_cov)
  `uvm_component_new

  function void build_phase(uvm_phase phase);
    super.build_phase(phase);

    m_genbits_cg = new();
    if (cfg.if_mode == dv_utils_pkg::Device) m_device_cmd_cg = new();
    else                                     m_host_cmd_cg = new();
  endfunction

  function void sample_csrng_cmds(csrng_item item, bit sts);
    if (cfg.if_mode == dv_utils_pkg::Device) begin
      m_device_cmd_cg.sample(item, cfg.vif.cmd_rsp.csrng_rsp_sts);
    end else begin
      m_host_cmd_cg.sample(item, cfg.vif.cmd_rsp.csrng_rsp_sts);
    end

    if (item.acmd == csrng_pkg::GEN) m_genbits_cg.sample(item, cfg.vif.cmd_rsp.csrng_rsp_sts);
  endfunction

endclass
