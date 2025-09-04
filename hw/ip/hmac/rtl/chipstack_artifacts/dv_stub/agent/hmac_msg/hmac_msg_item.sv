`ifndef _HMAC_MSG_ITEM_SV_
`define _HMAC_MSG_ITEM_SV_

class hmac_msg_item extends uvm_sequence_item;
  `uvm_object_utils(hmac_msg_item)

  // Payload to push into MSG_FIFO (bytes)
  rand bit [7:0] payload[];

  // Control flags for command sequencing
  rand bit do_start;
  rand bit do_process;
  rand bit do_stop;
  rand bit do_continue;

  // Optional key programming via CSRs before starting
  rand bit        program_key;
  rand bit [31:0] key_words[32];

  // Basic constraints: payload size may be empty if just issuing commands
  constraint c_payload_size { payload.size() inside { [0:4096] }; }

  function new(string name = "hmac_msg_item");
    super.new(name);
  endfunction

  function string convert2string();
    return $sformatf("start=%0b cont=%0b process=%0b stop=%0b bytes=%0d prog_key=%0b",
                     do_start, do_continue, do_process, do_stop, payload.size(), program_key);
  endfunction
endclass

`endif // _HMAC_MSG_ITEM_SV_

