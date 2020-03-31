// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// TL host sequence supports multiple outstanding requests
// It generates 'req_cnt' number of completely random requests
class tl_host_seq extends dv_base_seq #(.REQ        (tl_seq_item),
                                        .CFG_T      (tl_agent_cfg),
                                        .SEQUENCER_T(tl_sequencer)
  );

  rand int unsigned req_cnt;
  tl_seq_item       pending_req[$];
  int               min_req_delay = 0;
  int               max_req_delay = 10;

  `uvm_object_utils(tl_host_seq)
  `uvm_object_new

  virtual task body();
    set_response_queue_depth(p_sequencer.cfg.max_outstanding_req);
    fork
      begin : wait_response_thread
        for (int i = 0; i < req_cnt; i++) begin
          tl_seq_item req;
          bit         found_req;
          get_response(rsp);
          `uvm_info(`gfn, $sformatf("Received rsp[%0d] : %0s",
                                     i, rsp.convert2string()), UVM_HIGH)
          // in case of out of order rsp, find req that has same source as rsp
          foreach (pending_req[i]) begin
            if (rsp.d_source == pending_req[i].a_source) begin
              req = pending_req[i];
              pending_req.delete(i);
              process_response(req, rsp);
              found_req = 1;
              break;
            end
          end // foreach
          if (!found_req && !csr_utils_pkg::under_reset) begin
            `uvm_error(`gfn, $sformatf("fail to find matching req for rsp[%0d]: %0s",
                                       i, rsp.convert2string()))
          end
        end // for
      end : wait_response_thread
      begin : request_thread
        `uvm_info(`gfn, $sformatf("Start sending %0d host requests", req_cnt), UVM_HIGH)
        for (int i = 0; i < req_cnt; i++) begin
          req = tl_seq_item::type_id::create("req");
          pre_start_item(req);
          start_item(req);
          randomize_req(req, i);
          finish_item(req);
          `uvm_info(`gfn, $sformatf("Sent req[%0d] : %0s",
                                     i, req.convert2string()), UVM_HIGH)
          pending_req.push_back(req);
        end
      end : request_thread
    join
    `uvm_info(`gfn, $sformatf("Finished sending %0d host requests", req_cnt), UVM_HIGH)
  endtask

  // Request randomization, override this functiont to do custom request generation
  virtual function void randomize_req(tl_seq_item req, int idx);
    if (!(req.randomize() with {
        a_valid_delay inside {[min_req_delay:max_req_delay]};})) begin
      `uvm_fatal(`gfn, "Cannot randomize req")
    end
  endfunction

  // A reserved function that can be extended to process response packet
  virtual function void process_response(tl_seq_item req, tl_seq_item rsp);
  endfunction

  // A reserved task that prevents seq runs out of source ID
  virtual task pre_start_item(tl_seq_item req);
  endtask

endclass : tl_host_seq
