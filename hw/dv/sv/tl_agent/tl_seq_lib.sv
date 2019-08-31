// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// ---------------------------------------------
// TileLink agent sequence library
// ---------------------------------------------

// Host sequence, support multiple outstanding request
// generates 'req_cnt' number of completely random requests
class tl_host_seq extends uvm_sequence#(.REQ(tl_seq_item));
  `uvm_declare_p_sequencer(tl_sequencer)

  rand int unsigned req_cnt;
  tl_seq_item       pending_req[$];
  int               min_req_delay = 0;
  int               max_req_delay = 10;

  `uvm_object_utils(tl_host_seq)
  `uvm_object_new

  virtual task body();
    fork
      begin : wait_response_thread
        for (int i = 0; i < req_cnt; i++) begin
          get_response(rsp);
          `uvm_info(get_full_name(), $sformatf("Received rsp[%0d] : %0s",
                                     i, req.convert2string()), UVM_HIGH)
          process_response(pending_req.pop_front(), rsp);
        end
      end
      begin : request_thread
        `uvm_info(get_full_name(), $sformatf("Start sending %0d host requests", req_cnt), UVM_HIGH)
        for (int i = 0; i < req_cnt; i++) begin
          req = tl_seq_item::type_id::create("req");
          start_item(req);
          randomize_req(req, i);
          finish_item(req);
          `uvm_info(get_full_name(), $sformatf("Sent req[%0d] : %0s",
                                     i, req.convert2string()), UVM_HIGH)
          pending_req.push_back(req);
        end
      end
    join
    `uvm_info(get_full_name(), $sformatf("Finished sending %0d host requests", req_cnt), UVM_HIGH)
  endtask

  // Request randomization, override this functiont to do custom request generation
  virtual function void randomize_req(tl_seq_item req, int idx);
    if (!(req.randomize() with {
        a_valid_delay inside {[min_req_delay:max_req_delay]};})) begin
      `uvm_fatal(get_full_name(), "Cannot randomize req")
    end
  endfunction

  // A reserved function that can be extended to process response packet
  virtual function void process_response(tl_seq_item req, tl_seq_item rsp);
  endfunction

endclass : tl_host_seq

// extend host seq to send single specific item constructed by the caller
class tl_host_single_seq extends tl_host_seq;
    rand bit [top_pkg::TL_AW-1:0]  addr;
    rand tlul_pkg::tl_a_op_e       opcode;
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
      `uvm_fatal(get_full_name(), "Cannot randomize req")
    end
  endfunction

endclass

// Device sequence, currently support in-order response
class tl_device_seq extends uvm_sequence#(.REQ(tl_seq_item));

  int unsigned             rsp_cnt;
  int                      min_rsp_delay = 0;
  int                      max_rsp_delay = 10;
  mem_model_pkg::mem_model mem;

  `uvm_object_utils(tl_device_seq)
  `uvm_declare_p_sequencer(tl_sequencer)

  function new (string name = "");
    super.new(name);
  endfunction : new

  virtual task body();
    tl_seq_item req;
    tl_seq_item rsp;
    forever begin
      p_sequencer.a_chan_req_fifo.get(req);
      rsp = randomize_rsp(req);
      `uvm_info(get_full_name(), $sformatf("Sent rsp[%0d] : %0s, req: %0s",
                                 rsp_cnt, rsp.convert2string(), req.convert2string()), UVM_HIGH)
      start_item(rsp);
      finish_item(rsp);
      `uvm_info(get_full_name(), $sformatf("Sent rsp[%0d] : %0s",
                                 rsp_cnt, rsp.convert2string()), UVM_HIGH)
      rsp_cnt++;
    end
  endtask

  virtual function tl_seq_item randomize_rsp(tl_seq_item req);
    tl_seq_item rsp;
    $cast(rsp, req.clone());
    rsp.disable_a_chan_randomization();
    if (!(rsp.randomize() with
           {rsp.d_valid_delay inside {[min_rsp_delay : max_rsp_delay]};
            if (rsp.a_opcode inside {PutFullData, PutPartialData}) {
              rsp.d_opcode == tlul_pkg::AccessAck;
            } else {
              rsp.d_opcode == tlul_pkg::AccessAckData;
            }
            rsp.d_size == rsp.a_size;
            rsp.d_user == '0; // TODO: Not defined yet, tie it to zero
            rsp.d_source == rsp.a_source;})) begin
      `uvm_fatal(get_full_name(), "Cannot randomize rsp")
    end
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
    return rsp;
  endfunction

endclass : tl_device_seq
