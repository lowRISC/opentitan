// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// TL device sequence supports in-order and out-of-order response
class tl_device_seq extends dv_base_seq #(.REQ        (tl_seq_item),
                                          .CFG_T      (tl_agent_cfg),
                                          .SEQUENCER_T(tl_sequencer)
  );

  // if enabled, rsp will be aborted if it's not accepted after given valid length
  rand bit                 rsp_abort_after_d_valid_len;
  // chance to abort rsp
  int                      rsp_abort_pct = 0;

  int                      min_rsp_delay = 0;
  int                      max_rsp_delay = 10;
  mem_model_pkg::mem_model mem;
  tl_seq_item              req_q[$];
  bit                      out_of_order_rsp = 0;

  // chance to set d_error
  int                      d_error_pct = 0;

  `uvm_object_utils(tl_device_seq)
  `uvm_object_new

  constraint en_req_abort_after_d_valid_len_c {
    rsp_abort_after_d_valid_len dist {
      1 :/ rsp_abort_pct,
      0 :/ 100 - rsp_abort_pct
    };
  }

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
        post_randomize_rsp(rsp);
        update_mem(rsp);
        start_item(rsp);
        finish_item(rsp);
        get_response(rsp);
        // put it back to the top of queue to re-send rsp later if it's not completed
        if (!rsp.rsp_completed) req_q.push_front(rsp);
        `uvm_info(`gfn, $sformatf("Sent rsp[%0d] : %0s, req: %0s",
                                   rsp_cnt, rsp.convert2string(), req.convert2string()), UVM_HIGH)
        rsp_cnt++;
      end
    join
  endtask

  virtual function void randomize_rsp(tl_seq_item rsp);
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
            rsp.d_user == '0; // TODO: Not defined yet, tie it to zero
            rsp.d_source == rsp.a_source;
            d_error dist {0 :/ (100 - d_error_pct), 1 :/ d_error_pct};
        })) begin
      `uvm_fatal(`gfn, "Cannot randomize rsp")
    end
  endfunction

  // callback after randomize seq, extened seq can override it to handle some non-rand variables
  virtual function void post_randomize_rsp(tl_seq_item rsp);
    `DV_CHECK_MEMBER_RANDOMIZE_FATAL(rsp_abort_after_d_valid_len)
    rsp.rsp_abort_after_d_valid_len = rsp_abort_after_d_valid_len;
  endfunction

  virtual function void update_mem(tl_seq_item rsp);
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

endclass : tl_device_seq
