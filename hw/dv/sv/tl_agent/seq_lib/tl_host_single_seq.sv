// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Extend host seq to send single specific item constructed by the caller
class tl_host_single_seq #(type REQ_T = tl_seq_item) extends tl_host_seq #(REQ_T);
    rand bit                    write;
    rand bit [AddrWidth-1:0]    addr;
    rand bit [OpcodeWidth-1:0]  opcode;
    rand bit [SizeWidth-1:0]    size;
    rand bit [SourceWidth-1:0]  source;
    rand bit [MaskWidth-1:0]    mask;
    rand bit [DataWidth-1:0]    data;

    // for most cases, upper seq just needs to provide addr[$:2], data, mask value, write.
    // addr[1:0]/size/source/opcode can be randomized in tl_seq_item based on mask value
    bit control_addr_alignment = 0;
    bit control_rand_size      = 0;
    bit control_rand_source    = 0;
    bit control_rand_opcode    = 0;

  `uvm_object_param_utils(tl_host_single_seq #(REQ_T))
  `uvm_object_new

  constraint req_cnt_eq_1_c { req_cnt == 1; }

  virtual function void randomize_req(REQ req, int idx);
    if (!(req.randomize() with {
        a_valid_delay inside {[min_req_delay:max_req_delay]};
        a_data == data;
        a_mask == mask;
        a_addr[AddrWidth-1:2]   == addr[AddrWidth-1:2];
        control_addr_alignment  -> a_addr[1:0] == addr[1:0];
        control_rand_size       -> a_size == size;
        control_rand_source     -> a_source == source;
        if (control_rand_opcode) {
          a_opcode == opcode;
        } else {
          if (write) {
            a_opcode inside {tlul_pkg::PutPartialData, tlul_pkg::PutFullData};
          } else {
            a_opcode  == tlul_pkg::Get;
          }
        }
        })) begin
      `uvm_fatal(`gfn, "Cannot randomize req")
    end
  endfunction

endclass
