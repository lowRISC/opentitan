// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Covergroup: pending_req_on_rst_cg
// define bins for having pending request while on reset
covergroup pending_req_on_rst_cg(string name, string path) with function
    sample(bit req_pending);
  option.per_instance = 1;
  option.name         = {path, "::", name};

  cp_req_pending: coverpoint req_pending {
    bins values[] = {0, 1};
  }
endgroup

// coverage for sampling all the values of outstanding req, up to its max
covergroup max_outstanding_cg(string name, int max_outstanding, string path) with function
    sample(int num_outstanding);
  option.per_instance = 1;
  option.name         = {path, "::", name};

  cp_num_of_outstanding: coverpoint num_outstanding {
    bins values[]  = {[1:max_outstanding]};
  }
endgroup : max_outstanding_cg

covergroup tl_a_chan_cov_cg(string name, int valid_source_width, string path) with function
      sample(tl_seq_item item);
  option.per_instance = 1;
  option.name         = {path, "::", name};

  cp_opcode: coverpoint item.a_opcode {
    bins values[] = {Get, PutFullData, PutPartialData};
  }
  cp_mask: coverpoint item.a_mask {
    bins all_enables  = {'1};
    bins others       = default;
  }
  cp_size: coverpoint item.a_size {
    bins biggest_size = {$clog2(DataWidth >> 3)};
    bins others       = default;
  }
  cp_source: coverpoint item.a_source {
    bins valid_sources[] = {[0 : 2 << (valid_source_width - 1) - 1]};
  }
  cross cp_opcode, cp_mask, cp_size;
endgroup : tl_a_chan_cov_cg

covergroup tl_d_chan_cov_cg(string name, string path) with function sample(tl_seq_item item);
  option.per_instance = 1;
  option.name         = {path, "::", name};

  cp_opcode: coverpoint item.d_opcode {
    bins values[] = {AccessAckData, AccessAckData};
  }
  cp_size: coverpoint item.a_size {
    bins biggest_size = {$clog2(DataWidth >> 3)};
    bins others       = default;
  }
  cp_error:  coverpoint item.d_error;
  cross cp_opcode, cp_size;
endgroup : tl_d_chan_cov_cg

class tl_agent_cov extends dv_base_agent_cov #(tl_agent_cfg);
  // sample these at proper location, for example, m_pending_req_on_rst_cg called after reset
  pending_req_on_rst_cg m_pending_req_on_rst_cg;
  max_outstanding_cg    m_max_outstanding_cg;
  bit_toggle_cg_wrap    m_outstanding_item_w_same_addr_cov_obj;

  // knob to create m_outstanding_item_w_same_addr_cov_obj, even design supports more than
  // 1 outstanding items, but may not support they use the same address
  // TODO(#16840): may need to disable it for spi_device and hmac even they support 2 oustanding
  // items
  bit en_cov_outstanding_item_w_same_addr = 1;

  // item coverage, call sample(item) at the end of transaction to sample them
  tl_a_chan_cov_cg   m_tl_a_chan_cov_cg; // host mode
  tl_d_chan_cov_cg   m_tl_d_chan_cov_cg; // device mode
  bit_toggle_cg_wrap m_tl_error_cov_objs[string]; // host mode

  `uvm_component_utils(tl_agent_cov)
  `uvm_component_new

  function void build_phase(uvm_phase phase);
    string tl_error_names[] = {"invalid_a_opcode",
                               "PutFullData_mask_not_match_size",
                               "addr_not_align_mask",
                               "addr_not_align_size",
                               "mask_not_in_enabled_lanes",
                               "size_over_max"};
    super.build_phase(phase);
    m_pending_req_on_rst_cg = new("m_pending_req_on_rst_cg", `gfn);
    m_max_outstanding_cg    = new("m_max_outstanding_cg", cfg.max_outstanding_req, `gfn);

    if (cfg.max_outstanding_req > 1 && en_cov_outstanding_item_w_same_addr) begin
      m_outstanding_item_w_same_addr_cov_obj = new(.name("m_outstanding_item_w_same_addr_cov_obj"),
                                                   .path(`gfn));
    end

    if (cfg.if_mode == dv_utils_pkg::Host) begin
      m_tl_a_chan_cov_cg = new("m_tl_a_chan_cov_cg", cfg.valid_a_source_width, `gfn);
      foreach (tl_error_names[i]) begin
        m_tl_error_cov_objs[tl_error_names[i]] = new(.name(tl_error_names[i]), .path(`gfn));
      end
    end else begin // device mode
      m_tl_d_chan_cov_cg = new("m_tl_d_chan_cov_cg", `gfn);
    end
  endfunction : build_phase

  // sample info that is within the seq_item, this will be called at the end of transaction
  virtual function void sample(tl_seq_item item);
    if (cfg.if_mode == dv_utils_pkg::Host) begin
      if (!item.get_exp_d_error()) begin // no error
        m_tl_a_chan_cov_cg.sample(item);
      end else begin // error cases
        m_tl_error_cov_objs["invalid_a_opcode"].sample(item.get_error_a_opcode_invalid());
        m_tl_error_cov_objs["PutFullData_mask_not_match_size"].sample(
            item.get_error_PutFullData_mask_size_mismatched());
        m_tl_error_cov_objs["addr_not_align_mask"].sample(item.get_error_addr_size_misaligned());
        m_tl_error_cov_objs["addr_not_align_size"].sample(item.get_error_addr_size_misaligned());
        m_tl_error_cov_objs["mask_not_in_enabled_lanes"].sample(
            item.get_error_mask_not_in_enabled_lanes());
        m_tl_error_cov_objs["size_over_max"].sample(item.get_error_size_over_max());
      end
    end else begin // device mode
      m_tl_d_chan_cov_cg.sample(item);
    end
  endfunction : sample

endclass
