// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class edn_base_vseq extends cip_base_vseq #(
    .RAL_T               (edn_reg_block),
    .CFG_T               (edn_env_cfg),
    .COV_T               (edn_env_cov),
    .VIRTUAL_SEQUENCER_T (edn_virtual_sequencer)
  );
  `uvm_object_utils(edn_base_vseq)
  `uvm_object_new

  bit do_edn_init = 1'b1;
  bit [csrng_pkg::GENBITS_BUS_WIDTH - 1:0]      genbits;
  bit [entropy_src_pkg::FIPS_BUS_WIDTH - 1:0]   fips;
  bit [3:0]                                     clen, additional_data, flags;
  bit [csrng_pkg::CSRNG_CMD_WIDTH - 1:0]        cmd_data;

  virtual edn_cov_if                            cov_vif;

  virtual task body();
    if (!uvm_config_db#(virtual edn_cov_if)::get(null, "*.env" , "edn_cov_if", cov_vif)) begin
      `uvm_fatal(`gfn, $sformatf("Failed to get edn_cov_if from uvm_config_db"))
    end

    cov_vif.cg_cfg_sample(.cfg(cfg));
  endtask

  virtual task dut_init(string reset_kind = "HARD");
    super.dut_init(reset_kind);

    if (do_edn_init) begin
      // Initialize DUT and start device sequence
      edn_init();
      device_init();
    end
  endtask

  virtual task device_init();
    csrng_device_seq   m_dev_seq;

    m_dev_seq = csrng_device_seq::type_id::create("m_dev_seq");
    fork
      m_dev_seq.start(p_sequencer.csrng_sequencer_h);
    join_none
  endtask

  virtual task edn_init(string reset_kind = "HARD");
    if (cfg.boot_req_mode == MuBi4True) begin
      `DV_CHECK_STD_RANDOMIZE_FATAL(flags)
      wr_cmd(.cmd_type("boot_ins"), .acmd(csrng_pkg::INS), .clen(0), .flags(flags), .glen(0));
      `DV_CHECK_STD_RANDOMIZE_FATAL(flags)
      wr_cmd(.cmd_type("boot_gen"), .acmd(csrng_pkg::GEN), .clen(0), .flags(flags),
             .glen(cfg.num_boot_reqs));
    end

    // Enable edn, set modes
    ral.ctrl.edn_enable.set(cfg.enable);
    ral.ctrl.boot_req_mode.set(cfg.boot_req_mode);
    ral.ctrl.auto_req_mode.set(cfg.auto_req_mode);
    csr_update(.csr(ral.ctrl));

    if (cfg.auto_req_mode == MuBi4True) begin
      // Verify CMD_FIFO_RST bit
      for (int i = 0; i < 12; i++) begin
        `DV_CHECK_STD_RANDOMIZE_FATAL(cmd_data)
        csr_wr(.ptr(ral.generate_cmd), .value(cmd_data));
      end
      ral.ctrl.cmd_fifo_rst.set(MuBi4True);
      csr_update(.csr(ral.ctrl));
      // TODO: Verify can't write until reset
      ral.ctrl.cmd_fifo_rst.set(MuBi4False);
      csr_update(.csr(ral.ctrl));

      `DV_CHECK_STD_RANDOMIZE_WITH_FATAL(clen, clen inside { [0:12] };)
      `DV_CHECK_STD_RANDOMIZE_FATAL(flags)
      wr_cmd(.cmd_type("reseed"), .acmd(csrng_pkg::RES), .clen(clen), .flags(flags), .glen(0));
      for (int i = 0; i < clen; i++) begin
        `DV_CHECK_STD_RANDOMIZE_FATAL(cmd_data)
        wr_cmd(.cmd_type("reseed"), .cmd_data(cmd_data));
      end
      `DV_CHECK_STD_RANDOMIZE_WITH_FATAL(clen, clen inside { [0:12] };)
      `DV_CHECK_STD_RANDOMIZE_FATAL(flags)
      wr_cmd(.cmd_type("generate"), .acmd(csrng_pkg::GEN), .clen(clen), .flags(flags), .glen(1));
      for (int i = 0; i < clen; i++) begin
        `DV_CHECK_STD_RANDOMIZE_FATAL(cmd_data)
        wr_cmd(.cmd_type("generate"), .cmd_data(cmd_data));
      end
    end
  endtask

  virtual task dut_shutdown();
    // check for pending edn operations and wait for them to complete
    // TODO
  endtask

  virtual task wr_cmd(string cmd_type = "", csrng_pkg::acmd_e acmd = csrng_pkg::INV,
                      bit[3:0] clen = '0, bit[3:0] flags = '0, bit[17:0] glen = '0,
                      bit [csrng_pkg::CSRNG_CMD_WIDTH - 1:0] cmd_data = '0);

    case (cmd_type)
      "boot_ins": csr_wr(.ptr(ral.boot_ins_cmd), .value({glen, flags, clen, 1'b0, acmd}));
      "boot_gen": csr_wr(.ptr(ral.boot_gen_cmd), .value({glen, flags, clen, 1'b0, acmd}));
      "generate": begin
                    if (additional_data) begin
                      csr_wr(.ptr(ral.generate_cmd), .value(cmd_data));
                      additional_data -= 1;
                    end
                    else begin
                      csr_wr(.ptr(ral.generate_cmd), .value({glen, flags, clen, 1'b0, acmd}));
                      additional_data = clen;
                    end
                  end
      "reseed"  : begin
                    if (additional_data) begin
                      csr_wr(.ptr(ral.reseed_cmd), .value(cmd_data));
                      additional_data -= 1;
                    end
                    else begin
                      csr_wr(.ptr(ral.reseed_cmd), .value({glen, flags, clen, 1'b0, acmd}));
                      additional_data = clen;
                    end
                  end
      "sw"      : begin
                    if (additional_data) begin
                      csr_wr(.ptr(ral.sw_cmd_req), .value(cmd_data));
                      additional_data -= 1;
                    end
                    else begin
                      csr_spinwait(.ptr(ral.sw_cmd_sts.cmd_rdy), .exp_data(1'b1));
                      csr_wr(.ptr(ral.sw_cmd_req), .value({glen, flags, clen, 1'b0, acmd}));
                      additional_data = clen;
                    end
                    if (!additional_data) begin
                      wait_cmd_req_done();
                    end
                  end
      default   : `uvm_fatal(`gfn, $sformatf("Invalid cmd_type: %0s", cmd_type))
    endcase
  endtask

  virtual task wait_cmd_req_done();
    // Expect/Clear interrupt bit
    csr_spinwait(.ptr(ral.intr_state.edn_cmd_req_done), .exp_data(1'b1));
    check_interrupts(.interrupts((1 << CmdReqDone)), .check_set(1'b1));
  endtask

endclass : edn_base_vseq
