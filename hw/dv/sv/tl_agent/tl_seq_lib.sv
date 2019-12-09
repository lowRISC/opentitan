// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// ---------------------------------------------
// TileLink agent sequence library
// ---------------------------------------------

// Host sequence, support multiple outstanding request
// generates 'req_cnt' number of completely random requests
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

// extend host seq to send single specific item constructed by the caller
class tl_host_single_seq extends tl_host_seq;
    rand bit [top_pkg::TL_AW-1:0]  addr;
    rand bit [OpcodeWidth-1:0]     opcode;
    rand bit [top_pkg::TL_SZW-1:0] size;
    rand bit [top_pkg::TL_AIW-1:0] source;
    rand bit [top_pkg::TL_DBW-1:0] mask;
    rand bit [top_pkg::TL_DW-1:0]  data;

  `uvm_object_utils(tl_host_single_seq)
  `uvm_object_new

  constraint req_cnt_eq_1_c { req_cnt == 1; }

  virtual function void randomize_req(tl_seq_item req, int idx);
    if (!(req.randomize() with {
        a_valid_delay inside {[min_req_delay:max_req_delay]};
        a_addr        == addr;
        a_opcode      == opcode;
        a_size        == size;
        a_source      == source;
        a_mask        == mask;
        a_data        == data;})) begin
      `uvm_fatal(`gfn, "Cannot randomize req")
    end
  endfunction

endclass

// disable TL protocol related constraint on a_chan for error cases
class tl_host_custom_seq extends tl_host_single_seq;

  `uvm_object_utils(tl_host_custom_seq)
  `uvm_object_new

  virtual function void randomize_req(REQ req, int idx);
    req.disable_a_chan_protocol_constraint();
    super.randomize_req(req, idx);
  endfunction

endclass

// this seq will send an item that triggers d_error due to protocol violation
class tl_host_protocol_err_seq extends tl_host_single_seq;

  `uvm_object_utils(tl_host_protocol_err_seq)
  `uvm_object_new

  // forever randomize the item until we find one that violates the TL protocol
  virtual function void randomize_req(REQ req, int idx);
    req.a_valid_delay = $urandom_range(min_req_delay, max_req_delay);
    req.a_valid_delay.rand_mode(0);
    req.randomize_a_chan_with_protocol_error();
  endfunction

endclass

// Device sequence, currently support in-order response
class tl_device_seq extends dv_base_seq #(.REQ        (tl_seq_item),
                                          .CFG_T      (tl_agent_cfg),
                                          .SEQUENCER_T(tl_sequencer)
  );

  int                      min_rsp_delay = 0;
  int                      max_rsp_delay = 10;
  mem_model_pkg::mem_model mem;
  tl_seq_item              req_q[$];
  bit                      out_of_order_rsp = 0;

  `uvm_object_utils(tl_device_seq)
  `uvm_object_new

  virtual task body();
    fork
      forever begin // collect req thread
        int         req_cnt;
        tl_seq_item req;

        p_sequencer.a_chan_req_fifo.get(req);
        req_q.push_back(req);
        `uvm_info(`gfn, $sformatf("Received req[%0d] : %0s",
                                   req_cnt, req.convert2string()), UVM_HIGH)
        req_cnt++;
      end
      forever begin // response thread
        int         rsp_cnt;
        tl_seq_item req, rsp;

        wait(req_q.size > 0);
        if (out_of_order_rsp) req_q.shuffle();
        req = req_q.pop_front();
        $cast(rsp, req.clone());
        randomize_rsp(rsp);
        update_mem(rsp);
        start_item(rsp);
        finish_item(rsp);
        `uvm_info(`gfn, $sformatf("Sent rsp[%0d] : %0s, req: %0s",
                                   rsp_cnt, rsp.convert2string(), req.convert2string()), UVM_HIGH)
        rsp_cnt++;
      end
    join
  endtask

  virtual function void randomize_rsp(tl_seq_item rsp);
    rsp.disable_a_chan_randomization();
    if (!(rsp.randomize() with
           {rsp.d_valid_delay inside {[min_rsp_delay : max_rsp_delay]};
            if (rsp.a_opcode == tlul_pkg::Get) {
              rsp.d_opcode == tlul_pkg::AccessAckData;
            } else {
              rsp.d_opcode == tlul_pkg::AccessAck;
            }
            rsp.d_size == rsp.a_size;
            rsp.d_user == '0; // TODO: Not defined yet, tie it to zero
            rsp.d_source == rsp.a_source;})) begin
      `uvm_fatal(`gfn, "Cannot randomize rsp")
    end
  endfunction

  virtual function void update_mem(tl_seq_item rsp);
    if (mem != null) begin
      if (req.a_opcode inside {PutFullData, PutPartialData}) begin
        bit [tl_agent_pkg::DataWidth-1:0] data;
        data = req.a_data;
        for (int i = 0; i < $bits(req.a_mask); i++) begin
          if (req.a_mask[i]) begin
            mem.write_byte(req.a_addr + i, data[7:0]);
          end
          data = data >> 8;
        end
      end else begin
        for (int i = 2**req.a_size - 1; i >= 0; i--) begin
          rsp.d_data = rsp.d_data << 8;
          rsp.d_data[7:0] = mem.read_byte(req.a_addr+i);
        end
      end
    end
  endfunction

endclass : tl_device_seq
