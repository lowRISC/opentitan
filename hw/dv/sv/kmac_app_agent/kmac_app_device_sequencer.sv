// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// The sequencer used by kmac_app_device_agent, a reactive agent.
//
// The request fifo (m_req_fifo) is given items by (kmac_app_device_driver) when it sees a request
// packet. This can be consumed by a sequence, which can generate kmac_app_rsp_item responses which
// it feeds back to the sequencer.

class kmac_app_device_sequencer extends dv_base_sequencer #(.ITEM_T (kmac_app_rsp_item),
                                                            .CFG_T  (kmac_app_agent_cfg));
  `uvm_component_utils(kmac_app_device_sequencer)

  // A request fifo that receives packets from the driver.
  uvm_tlm_analysis_fifo #(kmac_app_req_packet_item) m_req_fifo;

  extern function new (string name, uvm_component parent);
endclass

function kmac_app_device_sequencer::new (string name, uvm_component parent);
  super.new(name, parent);
  m_req_fifo = new("m_req_fifo", this);
endfunction
