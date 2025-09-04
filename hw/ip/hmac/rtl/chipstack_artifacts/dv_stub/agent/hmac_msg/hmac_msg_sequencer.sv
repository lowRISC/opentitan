`ifndef _HMAC_MSG_SEQUENCER_SV_
`define _HMAC_MSG_SEQUENCER_SV_

class hmac_msg_sequencer extends uvm_sequencer #(hmac_msg_item);
  `uvm_component_utils(hmac_msg_sequencer)
  `uvm_component_new
endclass

`endif // _HMAC_MSG_SEQUENCER_SV_

