// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class csrng_base_vseq extends cip_base_vseq #(
    .RAL_T               (csrng_reg_block),
    .CFG_T               (csrng_env_cfg),
    .COV_T               (csrng_env_cov),
    .VIRTUAL_SEQUENCER_T (csrng_virtual_sequencer)
  );
  `uvm_object_utils(csrng_base_vseq)

  // various knobs to enable certain routines
  bit do_csrng_init = 1'b1;

  `uvm_object_new

  push_pull_device_seq#(entropy_src_pkg::FIPS_CSRNG_BUS_WIDTH)   m_entropy_src_pull_seq;
  push_pull_host_seq#(csrng_pkg::CSRNG_CMD_WIDTH)                m_edn_push_seq[NUM_HW_APPS];

  virtual task dut_init(string reset_kind = "HARD");
    super.dut_init(reset_kind);
    if (do_csrng_init) csrng_init();
  endtask

  virtual task dut_shutdown();
    // check for pending csrng operations and wait for them to complete
    // TODO
  endtask

  // setup basic csrng features
  virtual task csrng_init();
    cfg.otp_en_cs_sw_app_read_vif.drive(.val(cfg.otp_en_cs_sw_app_read));

    // Enables
    ral.ctrl.enable.set(cfg.enable);
    ral.ctrl.sw_app_enable.set(cfg.sw_app_enable);
    csr_update(.csr(ral.ctrl));
  endtask

  // write csrng command request register
  virtual task wr_cmd_req(bit[3:0] acmd, bit[3:0] clen, bit[3:0] flags, bit[18:0] glen,
                          bit [31:0] data_q[$] = '{});
    csr_wr(.ptr(ral.cmd_req), .value({1'b0, glen, flags, clen, acmd}));
  endtask

  task automatic send_cmd_req(uint hwapp, csrng_item cs_item);
    bit [csrng_pkg::CSRNG_CMD_WIDTH-1:0]   cmd;
    // Gen cmd_req
    cmd = {cs_item.glen, cs_item.flags, cs_item.clen, 1'b0, cs_item.acmd};
    cfg.m_edn_agent_cfg[hwapp].m_cmd_push_agent_cfg.add_h_user_data(cmd);
    m_edn_push_seq[hwapp].num_trans = cs_item.clen + 1;
    for (int i = 0; i < cs_item.clen; i++)
      cfg.m_edn_agent_cfg[hwapp].m_cmd_push_agent_cfg.add_h_user_data(cs_item.cmd_data_q.pop_front());
    fork
      // Drive cmd_req
      m_edn_push_seq[hwapp].start(p_sequencer.edn_sequencer_h[hwapp].m_cmd_push_sequencer);
    join_none
    // Wait for ack
    cfg.m_edn_agent_cfg[hwapp].vif.wait_cmd_ack();
  endtask

endclass : csrng_base_vseq
