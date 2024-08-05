// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class edn_common_vseq extends edn_base_vseq;
  `uvm_object_utils(edn_common_vseq)

  constraint num_trans_c {
    num_trans inside {[1:2]};
  }
  `uvm_object_new

  virtual task pre_start();
    do_edn_init = 1'b0;

    super.pre_start();
  endtask

  virtual task body();
    run_common_vseq_wrapper(num_trans);
  endtask : body

  // For each round, randomly enable EDN to make sure the EDN won't provide valid response during
  // fatal alerts.
  virtual task sec_cm_inject_fault(sec_cm_pkg::sec_cm_base_if_proxy if_proxy);
    if ($urandom_range(0, 4) == 4) csr_wr(.ptr(ral.ctrl.edn_enable), .value(MuBi4True));
    super.sec_cm_inject_fault(if_proxy);
  endtask : sec_cm_inject_fault

  virtual task check_sec_cm_fi_resp(sec_cm_pkg::sec_cm_base_if_proxy if_proxy);
    bit [31:0] backdoor_err_code_val;
    if (!uvm_re_match("*.cnt_q*", if_proxy.path)) begin
      csr_rd_check(.ptr(ral.err_code.edn_cntr_err), .compare_value(1'b1));
      if (cfg.en_cov) begin
        csr_rd(.ptr(ral.err_code), .value(backdoor_err_code_val));
        cov_vif.cg_error_sample(.err_code(backdoor_err_code_val));
      end
    end else if (!uvm_re_match("*.u_edn_ack_sm_ep*", if_proxy.path)) begin
      csr_rd_check(.ptr(ral.err_code.edn_ack_sm_err), .compare_value(1'b1));
      if (cfg.en_cov) begin
        csr_rd(.ptr(ral.err_code), .value(backdoor_err_code_val));
        cov_vif.cg_error_sample(.err_code(backdoor_err_code_val));
      end
    end else if (!uvm_re_match("*.u_edn_main_sm*", if_proxy.path)) begin
      csr_rd_check(.ptr(ral.err_code.edn_main_sm_err), .compare_value(1'b1));
      if (cfg.en_cov) begin
        csr_rd(.ptr(ral.err_code), .value(backdoor_err_code_val));
        cov_vif.cg_error_sample(.err_code(backdoor_err_code_val));
      end
    end

    // Check main_sm_state goes to error st.
    csr_rd_check(.ptr(ral.main_sm_state), .compare_value(edn_pkg::Error));

    // Check no EDN responses.
    send_edn_requests_during_fatal_alerts();
  endtask

  virtual task send_edn_requests_during_fatal_alerts();
    bit [edn_pkg::StateWidth-1:0] state;
    bit req;
    push_pull_host_seq#(edn_pkg::FIPS_ENDPOINT_BUS_WIDTH) m_endpoint_pull_seq[MAX_NUM_ENDPOINTS];
    bit [MAX_NUM_ENDPOINTS-1:0] send_edn_reqs = $urandom();

    `uvm_info(`gfn, $sformatf("Send %0h EDN reqs during fatal alert", send_edn_reqs), UVM_HIGH)

    foreach (send_edn_reqs[i]) begin
      if (send_edn_reqs[i]) begin
        automatic int index = i;
        m_endpoint_pull_seq[index] = push_pull_host_seq#(FIPS_ENDPOINT_BUS_WIDTH)::
            type_id::create($sformatf("m_endpoint_pull_seq[%0d]", index));
        m_endpoint_pull_seq[index].num_trans = 1;
        `uvm_info(`gfn, $sformatf("Send EDN_%0d req during fatal alert", index), UVM_LOW)

        // Assertion in design will check EDN should not respond during fatal alert.
        fork
          m_endpoint_pull_seq[index].start(p_sequencer.endpoint_sequencer_h[index]);
          begin
            `DV_SPINWAIT(
                do begin
                  uvm_hdl_read($sformatf("%0s[%0d].edn_req", "tb.dut.u_edn_core.edn_i", index),
                               req);
                  cfg.clk_rst_vif.wait_clks(1);
                end while (!req);,
                $sformatf("Waiting for EDN endpoint request timeout")
            )
            csr_rd(.ptr(ral.main_sm_state.main_sm_state), .value(state), .backdoor(1));
            if (edn_pkg::state_e'(state) == edn_pkg::Error) begin
              cov_vif.cg_edn_endpoint_err_req_sample(.endpoint(index));
            end
          end
        join_none
      end
    end
    cfg.clk_rst_vif.wait_clks($urandom_range(0, 100));
  endtask

  `define RESCMD_FIFO tb.dut.u_edn_core.u_prim_fifo_sync_rescmd
  `define GENCMD_FIFO tb.dut.u_edn_core.u_prim_fifo_sync_gencmd

  `define HIER_PATH(prefix, suffix) `"prefix.suffix`"

  virtual task pre_run_sec_cm_fi_vseq();
    $assertoff(0, `HIER_PATH(`RESCMD_FIFO, DataKnown_A));
    $assertoff(0, `HIER_PATH(`GENCMD_FIFO, DataKnown_A));
    $assertoff(0, `HIER_PATH(`RESCMD_FIFO, gen_normal_fifo.depthShallNotExceedParamDepth));
    $assertoff(0, `HIER_PATH(`GENCMD_FIFO, gen_normal_fifo.depthShallNotExceedParamDepth));
  endtask

  virtual task post_run_sec_cm_fi_vseq();
    $asserton(0, `HIER_PATH(`RESCMD_FIFO, DataKnown_A));
    $asserton(0, `HIER_PATH(`GENCMD_FIFO, DataKnown_A));
    $asserton(0, `HIER_PATH(`RESCMD_FIFO, gen_normal_fifo.depthShallNotExceedParamDepth));
    $asserton(0, `HIER_PATH(`GENCMD_FIFO, gen_normal_fifo.depthShallNotExceedParamDepth));
  endtask

  `undef RESCMD_FIFO
  `undef GENCMD_FIFO

  `undef HIER_PATH

endclass
