// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Default base class sequence that overrides base UVM functions.
//
// This sequence is not meant to be run standalone by itself (fatal error will be thrown if you
// do). It is instead meant to provide base utilities to construct different flavors of host
// sequences on top of it. These are as follows:
//
// 1. Provide late randomization for a_source
// a_source value needs to be randomized such that it does not equal to an in-flight request that
// has not yet returned. This means at the time of randomization, the DUT must already be ready to
// consume the req and apply it to the interface immediately. The tl_host_seq::randomize_req()
// performs exactly this function. However, it does not cater to the next bullet - driving TL
// transactions over the RAL model, which is done completely within the RAL layers. We need to
// ensure that the a_source value is randomized right before the DUT is ready to consume it, so we
// override the finish_item() to do so instead.
//
// 2. Serve as the parent_sequence for the RAL adapter
// The RAL map uses a dummy sequence to synchronize with the driver, after creating the bus req
// using the adapter. It does not provide any ability to perform "late randomization" of
// request. This causes our a_source constraints to be violated. Since we need this to ensure that
// the a_source is set taking into account the most up-to-date DUT state, we supply this sequence
// as the adapter's parent_seqeunce instead (see tl_reg_adapter for more details). The UVM map then
// uses this sequence instead of the dummy one to invoke start_item(), finish_item() and
// get_response() instead. So, instead of doing the late randomization in randomize_req(), we do it
// in finish_item() instead.
//
// 3. Provide ability to override and "fix" the a_source to a particular value.
// This is done to satisfy the use case where the TL host sends ALL requests with the same source
// ID.
class tl_host_base_seq #(type REQ_T = tl_seq_item) extends dv_base_seq #(
    .REQ        (REQ_T),
    .CFG_T      (tl_agent_cfg),
    .SEQUENCER_T(tl_sequencer));

  // The knob below allows the user to fix a_source in the reqs from a higher level sequence. It is
  // the responsibility of the higher level sequence to ensure that the overridden_a_source_val is
  // not illegal. To avoid painful debug, refrain from changing override_a_source_val while the
  // sequence is still running.
  bit override_a_source_val = 0;
  bit [SourceWidth-1:0] overridden_a_source_val;

  `uvm_object_param_utils_begin(tl_host_base_seq #(REQ_T))
    `uvm_field_int(override_a_source_val, UVM_DEFAULT | UVM_NOCOMPARE | UVM_NOPACK)
    `uvm_field_int(overridden_a_source_val, UVM_DEFAULT | UVM_NOCOMPARE | UVM_NOPACK)
  `uvm_object_utils_end

  `uvm_object_new

  virtual function void get_cfg(uvm_sequence_item item);
    if (p_sequencer != null) begin
      cfg = p_sequencer.cfg;
    end else begin
      tl_sequencer seqr;
      `downcast(seqr, item.get_sequencer())
      cfg = seqr.cfg;
    end
  endfunction

  // Overrides the base class implementation to late randomize / set a_source.
  virtual task finish_item(uvm_sequence_item item, int set_priority = -1);
    REQ req;

    `downcast(req, item)
    if (cfg == null) get_cfg(req);
    if (override_a_source_val) begin
      req.a_source_is_overridden = 1'b1;
      req.a_source = overridden_a_source_val;
      cfg.add_to_a_source_pend_q(req.a_source);
    end else begin
      cfg.randomize_a_source_in_req(req);
    end
    super.finish_item(item, set_priority);
  endtask

  // Called after the rsp is received.
  virtual task get_base_response(output uvm_sequence_item response, input int transaction_id = -1);
    REQ rsp;
    super.get_base_response(response, transaction_id);
    `downcast(rsp, response)
    if (cfg == null) get_cfg(rsp);
    cfg.remove_from_a_source_pend_q(rsp.d_source);
  endtask

endclass
