// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class csrng_monitor extends dv_base_monitor #(
    .ITEM_T (csrng_item),
    .CFG_T  (csrng_agent_cfg),
    .COV_T  (csrng_agent_cov)
  );
  `uvm_component_utils(csrng_monitor)

  // the base class provides the following handles for use:
  // csrng_agent_cfg: cfg
  // csrng_agent_cov: cov
  // uvm_analysis_port #(csrng_item): analysis_port

  // Analysis port for the csrng_rsp_sts.
  uvm_analysis_port #(bit) rsp_sts_ap;

  uvm_tlm_analysis_fifo#(push_pull_item#(.HostDataWidth(csrng_pkg::CSRNG_CMD_WIDTH)))
      csrng_cmd_fifo;

  `uvm_component_new

  function void build_phase(uvm_phase phase);
    super.build_phase(phase);

    csrng_cmd_fifo = new("csrng_cmd_fifo", this);
    rsp_sts_ap     = new("rsp_sts_ap", this);
  endfunction

  task run_phase(uvm_phase phase);
    @(posedge cfg.vif.rst_n);
    fork
      handle_reset();
      collect_valid_trans();
      // We only need to monitor incoming requests if the agent is configured
      // in device mode.
      if (cfg.if_mode == dv_utils_pkg::Device) begin
        collect_request();
      end
    join_none
  endtask

  virtual protected task handle_reset();
    forever begin
      @(negedge cfg.vif.rst_n);
      cfg.under_reset = 1;
      csrng_cmd_fifo.flush();
      // TODO: sample any reset-related covergroups
      @(posedge cfg.vif.rst_n);
      cfg.under_reset = 0;
    end
  endtask

  virtual task collect_valid_trans();
    forever begin
      wait (cfg.under_reset == 0);

      `DV_SPINWAIT_EXIT(
          push_pull_item#(.HostDataWidth(csrng_pkg::CSRNG_CMD_WIDTH))  item;
          csrng_item   cs_item = csrng_item::type_id::create("cs_item");
          for (int i = 0; i <= cs_item.clen; i++) begin
            csrng_cmd_fifo.get(item);
            `uvm_info(`gfn, $sformatf("Received cs_item: %s", item.convert2string()), UVM_HIGH)
            if (i == 0) begin
              cs_item.acmd  = acmd_e'(item.h_data[3:0]);
              cs_item.clen  = item.h_data[7:4];
              if (item.h_data[11:8] == MuBi4True) begin
                cs_item.flags = MuBi4True;
              end else begin
                cs_item.flags = MuBi4False;
              end
              cs_item.glen  = item.h_data[23:12];
              cs_item.cmd_data_q.delete();
            end else begin
              cs_item.cmd_data_q.push_back(item.h_data);
            end
          end
          if (cs_item.acmd == csrng_pkg::GEN) begin
            for (int i = 0; i < cs_item.glen; i++) begin
              @(posedge cfg.vif.mon_cb.cmd_rsp.genbits_valid);
              cs_item.genbits_q.push_back(cfg.vif.mon_cb.cmd_rsp.genbits_bus);
            end
          end
          // Illegal commands fail without getting acknowledged.
          if (!(cs_item.acmd inside {csrng_pkg::INV, csrng_pkg::GENB,
                                     csrng_pkg::GENU})) begin
            cfg.vif.wait_cmd_ack_or_rst_n();
          end
          `uvm_info(`gfn, $sformatf("Writing analysis_port: %s", cs_item.convert2string()),
                    UVM_HIGH)
          analysis_port.write(cs_item);
          if (cfg.en_cov) cov.sample_csrng_cmds(cs_item, cfg.vif.cmd_rsp.csrng_rsp_sts);

          ,

          // Wait reset
          wait (cfg.under_reset);)
     end
  endtask

  // This task is only used for device agents responding
  // It will pick up any incoming requests from the DUT and send a signal to the
  // sequencer (in the form of a sequence item), which will then be forwarded to
  // the sequence, which then generates the appropriate response item.
  //
  // TODO: This assumes no requests can be dropped, and might need to be fixed
  //       if this is not allowed.
  virtual protected task collect_request();
    csrng_item   cs_item;
    forever begin
      wait(cfg.under_reset == 0);
      @(cfg.vif.cmd_push_if.mon_cb);
      if ((cfg.vif.cmd_push_if.mon_cb.valid) && (cfg.vif.cmd_push_if.mon_cb.ready)) begin
        // TODO: sample any covergroups
        // TODO: Implement suggestion in PR #5456
        cs_item = csrng_item::type_id::create("cs_item");
        cs_item.acmd = acmd_e'(cfg.vif.mon_cb.cmd_req.csrng_req_bus[3:0]);
        cs_item.clen = cfg.vif.mon_cb.cmd_req.csrng_req_bus[7:4];
        if (cfg.vif.mon_cb.cmd_req.csrng_req_bus[11:8] == MuBi4True) begin
          cs_item.flags = MuBi4True;
        end
        else begin
          cs_item.flags = MuBi4False;
        end
        if (cs_item.acmd == csrng_pkg::GEN) begin
          cs_item.glen = cfg.vif.mon_cb.cmd_req.csrng_req_bus[23:12];
        end

        `DV_SPINWAIT_EXIT(
            for (int i = 0; i < cs_item.clen; i++) begin
              do begin
                @(cfg.vif.cmd_push_if.mon_cb);
              end
              while (!(cfg.vif.cmd_push_if.mon_cb.valid) || !(cfg.vif.cmd_push_if.mon_cb.ready));
              cs_item.cmd_data_q.push_back(cfg.vif.mon_cb.cmd_req.csrng_req_bus);
            end,
            wait(cfg.under_reset))

        `uvm_info(`gfn, $sformatf("Writing req_analysis_port: %s", cs_item.convert2string()),
             UVM_HIGH)
        req_analysis_port.write(cs_item);
        // After picking up a request, wait until a response is sent before
        // detecting another request, as this is not a pipelined protocol.
        `DV_SPINWAIT_EXIT(while (!cfg.vif.mon_cb.cmd_rsp.csrng_rsp_ack) @(cfg.vif.mon_cb);,
                          wait(cfg.under_reset))

        // Increment the counters only if ack is sent.
        if (!cfg.under_reset) begin
          if (cs_item.acmd == csrng_pkg::RES) cfg.reseed_cnt += 1;
          if (cs_item.acmd == csrng_pkg::GEN) begin
            cfg.generate_cnt += 1;
            if (cfg.reseed_cnt == 1) cfg.generate_between_reseeds_cnt += 1;
          end
        end

        rsp_sts_ap.write(cfg.vif.cmd_rsp.csrng_rsp_sts);
       end
    end
  endtask
endclass
