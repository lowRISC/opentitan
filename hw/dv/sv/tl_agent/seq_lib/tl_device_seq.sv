// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// A forever running sequence that responds to a TL request.
//
// This sequence supports in-order and out-of-order responses. It maintains a
// memory to record the write requests, so that when the same address is read,
// the originally written data is returned. This sequence runs forever, i.e.
// it needs to be forked off as a separate thread. It can be stopped gracefully
// by invoking the seq_stop() method.
class tl_device_seq #(type REQ = tl_seq_item) extends dv_base_seq #(
    .REQ        (REQ),
    .CFG_T      (tl_agent_cfg),
    .SEQUENCER_T(tl_sequencer));

  // if enabled, rsp will be aborted if it's not accepted after given valid length
  rand bit                 rsp_abort_after_d_valid_len;
  // chance to abort rsp
  int                      rsp_abort_pct = 0;

  int                      min_rsp_delay = 0;
  int                      max_rsp_delay = 10;
  mem_model_pkg::mem_model mem;
  REQ                      req_q[$];
  bit                      out_of_order_rsp = 0;

  // Stops running this sequence.
  protected bit stop;

  // chance to set d_error
  int                      d_error_pct = 0;

  `uvm_object_param_utils(tl_device_seq #(REQ))
  `uvm_object_new

  constraint en_req_abort_after_d_valid_len_c {
    rsp_abort_after_d_valid_len dist {
      1 :/ rsp_abort_pct,
      0 :/ 100 - rsp_abort_pct
    };
  }

  // In case this seq start in the middle of other body.
  // If we set `stop` at the beginning of this body, then
  // there is a risk to get the race when start and stop are called
  // at the same time.
  virtual task pre_body();
    stop = 0;
  endtask

  virtual task body();
    fork
      begin: isolation_thread
        fork
          collect_request_thread();
          send_response_thread();
        join_any
        // Wait for all requests to be serviced.
        wait (req_q.size() == 0);
        disable fork;
      end
    join
  endtask

  // A blocking task that retrieves a request from the TLM fifo, unless the seq is stopped.
  //
  // req: A req item retrieved from the TLM fifo and returned back to the caller.
  protected virtual task get_a_chan_req(output REQ req);
    fork
      begin: isolation_thread
        fork
          begin
            tl_seq_item item;
            p_sequencer.a_chan_req_fifo.get(item);
            `downcast(req, item)
          end
          wait (stop);
        join_any
        // Allow the rest of the statements in the same time-step to finish executing in the "other"
        // thread, before disabling the fork.
        #0;
        disable fork;
      end
    join
  endtask

  // A perpetually running task that collects and enqueues the incoming TL requests.
  //
  // The task finishes when the sequence is stopped, which is done be invoking the seq_stop()
  // method.
  protected virtual task collect_request_thread();
    int req_cnt;
    forever begin
      REQ req;
      get_a_chan_req(req);
      if (req != null) begin
        req_q.push_back(req);
        `uvm_info(`gfn, $sformatf("Received req[%0d] : %0s",
                                  req_cnt, req.convert2string()), UVM_HIGH)
        req_cnt++;
      end
      if (stop) break;
    end
  endtask

  // A perpetually running task that pops requests from the collected request queue and sends
  // randomized responses.
  protected virtual task send_response_thread();
    int rsp_cnt;
    forever begin
      REQ req, rsp;
      wait(req_q.size > 0);
      if (out_of_order_rsp) req_q.shuffle();
      req = req_q[0];  // 'peek' pop_front.
      `downcast(rsp, req.clone())
      randomize_rsp(rsp);
      post_randomize_rsp(rsp);
      update_mem(rsp);
      start_item(rsp);
      finish_item(rsp);
      get_response(rsp);
      // Remove from req_q if response is completed.
      if (rsp.rsp_completed) begin
        req_q = req_q[1:$];
        `uvm_info(`gfn, $sformatf("Sent rsp[%0d] : %0s, req: %0s",
                                  rsp_cnt, rsp.convert2string(), req.convert2string()), UVM_HIGH)
        rsp_cnt++;
      end
    end
  endtask

  // User-overridable function to randomize the response. The response is already cloned from the
  // request, so the request (a_channel) information is already present.
  virtual function void randomize_rsp(REQ rsp);
    rsp.disable_a_chan_randomization();
    if (d_error_pct > 0) rsp.no_d_error_c.constraint_mode(0);
    if (!(rsp.randomize() with
           {rsp.d_valid_delay inside {[min_rsp_delay : max_rsp_delay]};
            if (rsp.a_opcode == tlul_pkg::Get) {
              rsp.d_opcode == tlul_pkg::AccessAckData;
            } else {
              rsp.d_opcode == tlul_pkg::AccessAck;
            }
            rsp.d_size == rsp.a_size;
            rsp.d_source == rsp.a_source;
            d_error dist {0 :/ (100 - d_error_pct), 1 :/ d_error_pct};
        })) begin
      `uvm_fatal(`gfn, "Cannot randomize rsp")
    end
  endfunction

  // callback after randomize seq, extended seq can override it to handle some non-rand variables
  virtual function void post_randomize_rsp(REQ rsp);
    `DV_CHECK_MEMBER_RANDOMIZE_FATAL(rsp_abort_after_d_valid_len)
    rsp.rsp_abort_after_d_valid_len = rsp_abort_after_d_valid_len;
  endfunction

  virtual function void update_mem(REQ rsp);
    if (mem != null) begin
      if (rsp.a_opcode inside {PutFullData, PutPartialData}) begin
        bit [tl_agent_pkg::DataWidth-1:0] data;
        data = rsp.a_data;
        for (int i = 0; i < $bits(rsp.a_mask); i++) begin
          if (rsp.a_mask[i]) begin
            mem.write_byte(rsp.a_addr + i, data[7:0]);
          end
          data = data >> 8;
        end
      end else begin
        for (int i = 2**rsp.a_size - 1; i >= 0; i--) begin
          rsp.d_data = rsp.d_data << 8;
          rsp.d_data[7:0] = mem.read_byte(rsp.a_addr+i);
        end
      end
    end
  endfunction

  // Stop running this seq and wait until it has finished gracefully.
  virtual task seq_stop();
    stop = 1'b1;
    wait_for_sequence_state(UVM_FINISHED);
  endtask

endclass : tl_device_seq
