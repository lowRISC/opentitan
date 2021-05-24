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

  bit [csrng_pkg::CSRNG_CMD_WIDTH-1:0]   cmd_data_q[$];

  // various knobs to enable certain routines
  bit do_csrng_init = 1'b1;

  `uvm_object_new

  push_pull_device_seq#(entropy_src_pkg::FIPS_CSRNG_BUS_WIDTH)   m_entropy_src_pull_seq;
  push_pull_host_seq#(csrng_pkg::CSRNG_CMD_WIDTH)                m_edn_push_seq;

  virtual task dut_init(string reset_kind = "HARD");
    super.dut_init();
    if (do_csrng_init) csrng_init();
  endtask

  virtual task dut_shutdown();
    // check for pending csrng operations and wait for them to complete
    // TODO
  endtask

  // setup basic csrng features
  virtual task csrng_init();
    cfg.efuse_sw_app_enable_vif.drive_pin(.idx(0), .val(cfg.efuse_sw_app_enable));
  endtask

  // write csrng command request register
  virtual task wr_cmd_req(bit[3:0] acmd, bit[3:0] clen, bit[3:0] flags, bit[18:0] glen,
                          bit [31:0] data_q[$] = '{});
    csr_wr(.ptr(ral.cmd_req), .value({1'b0, glen, flags, clen, acmd}));
  endtask

  // send csrng command request
  // TODO: make csrng_item-based
  virtual task send_cmd_req(bit[3:0] acmd, bit[3:0] clen, bit[3:0] flags, bit[18:0] glen,
                            bit[31:0] data_q[$] = '{});
    // Gen cmd_req
    cfg.m_edn_agent_cfg.m_cmd_push_agent_cfg.add_h_user_data({glen, flags, clen, acmd});
      m_edn_push_seq.num_trans = 1 + clen;
      for (int i = 0; i < clen; i++)
        cfg.m_edn_agent_cfg.m_cmd_push_agent_cfg.add_h_user_data(data_q.pop_front());
    // Drive cmd_req
    m_edn_push_seq.start(p_sequencer.edn_sequencer_h.m_cmd_push_sequencer);
    // Wait for cmd_ack
    cfg.m_edn_agent_cfg.vif.wait_cmd_ack();
  endtask // send_cmd_req

endclass : csrng_base_vseq
