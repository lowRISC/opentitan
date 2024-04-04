// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// TL host sequence supports multiple outstanding requests
// It generates 'req_cnt' number of completely random requests
class tl_host_seq #(type REQ_T = tl_seq_item) extends tl_host_base_seq #(REQ_T);

  rand int unsigned req_cnt;
  // if enabled, req will be aborted if it's not accepted after given valid length
  rand bit          req_abort_after_a_valid_len;
  // chance to abort req
  int               req_abort_pct = 0;

  REQ               pending_req[$];
  int               min_req_delay = 0;
  int               max_req_delay = 10;

  `uvm_object_param_utils(tl_host_seq #(REQ_T))
  `uvm_object_new

  constraint req_abort_after_a_valid_len_c {
    req_abort_after_a_valid_len dist {
      1 :/ req_abort_pct,
      0 :/ 100 - req_abort_pct
    };
  }

  virtual task body();
    set_response_queue_depth(-1);
    fork
      begin : wait_response_thread
        for (int i = 0; i < req_cnt; i++) begin
          REQ req;
          bit found_req;
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
          req = REQ::type_id::create("req");
          pre_start_item(req);
          start_item(req);
          randomize_req(req, i);
          post_randomize_req(req, i);
          pending_req.push_back(req); // in case of device same cycle response
          finish_item(req);
          `uvm_info(`gfn, $sformatf("Sent req[%0d] : %0s",
                                     i, req.convert2string()), UVM_HIGH)
        end
      end : request_thread
    join
    `uvm_info(`gfn, $sformatf("Finished sending %0d host requests", req_cnt), UVM_HIGH)
  endtask

  // Invoked after creating the req and before invoking start_item(req). Suitable for inserting
  // delays before start_item(). Example: avoid running out of source IDs.
  virtual task pre_start_item(REQ req);
  endtask

  // Request randomization, override this function to do custom request generation. Invoked after
  // start_item(). Not suitable for setting a_source, since that is handled in
  // `tl_host_base_seq::finish_item()` instead, to facilitate late randomization when accesses are
  // initiated from UVM RAL.
  virtual function void randomize_req(REQ req, int idx);
    if (!(req.randomize() with {
        a_valid_delay inside {[min_req_delay:max_req_delay]};})) begin
      `uvm_fatal(`gfn, "Cannot randomize req")
    end
  endfunction

  // callback after randomize seq, extened seq can override it to handle some non-rand variables
  virtual function void post_randomize_req(REQ req, int idx);
    `DV_CHECK_MEMBER_RANDOMIZE_FATAL(req_abort_after_a_valid_len)
    req.req_abort_after_a_valid_len = req_abort_after_a_valid_len;
  endfunction

  // A reserved function that can be extended to process response packet
  virtual function void process_response(REQ req, REQ rsp);
  endfunction

endclass : tl_host_seq
