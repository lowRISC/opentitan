// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class spi_segment_item extends uvm_sequence_item;

  `uvm_object_utils(spi_segment_item)
  `uvm_object_new

  // knobs
  // command reg
  // the direction knobs are speciel,
  // the setting is vs standart
  // i.e a rx pc of 20 will result in
  // 20 of RX transactions will be RX only the
  // remailing 80% will be standard.
  // similar for tx pct
  // i.e the rx setting does not affect
  // the tx distribution
  // for the use the knob for the cmd
  int                           rx_only_weight     = 20;
  int                           tx_only_weight     = 20;
  int                           dummy_weight       = 0;

  // num dummy cycles
  int                           num_dummy          = 0;
  //num_addr_bytes
  int                           num_cmd_bytes      = 4;

  // transaction len
  int                           spi_len_min        = 2;
  int                           spi_len_max        = 4;

  spi_cmd_e                     cmd;
  spi_segment_type_e            seg_type           = Data;
  rand spi_host_command_t       command_reg;
  rand bit                [7:0] spi_data      [$];

  constraint command_reg_direction_c {
    //make sure the direction matches the segtype /cmd address are always tx/standard

    // Alternative command just generates any kind of allowed segment combination
    if (cmd inside {AltCmd} && (seg_type inside {Dummy, Data})) {
      // Bidirectional commands only allow in standard speed
      (command_reg.direction == Bidir) -> (command_reg.mode == Standard);
      command_reg.direction dist {
        None   := 25,
        TxOnly := 25,
        RxOnly := 25,
        Bidir  := 25
      };
    } else
    if ((cmd inside {ReadStd}) && (seg_type inside {Dummy, Data})) {
      command_reg.direction dist {
        RxOnly := rx_only_weight,
        None   := dummy_weight / 2,
        Bidir  := 100 - (rx_only_weight + dummy_weight)
      };
    } else
    if ((cmd inside {ReadDual, ReadQuad}) && (seg_type inside {Dummy, Data})) {
      command_reg.direction dist {
        RxOnly := rx_only_weight,
        None   := dummy_weight / 2
      };
    } else
    if ((cmd inside {WriteDual, WriteQuad}) && (seg_type inside {Dummy, Data})) {
      command_reg.direction dist {
        TxOnly := tx_only_weight,
        None   := dummy_weight / 2
      };
    } else {
      command_reg.direction dist {
        TxOnly := tx_only_weight,
        None   := dummy_weight / 2,
        Bidir  := 100 - (tx_only_weight + dummy_weight)
      };
    }

  }
  constraint command_reg_mode_c {

    if (seg_type == Command) {
      command_reg.mode == Standard;
    } else {
      if (cmd inside {ReadStd, WriteStd}) {
        command_reg.mode == Standard;
      } else
      if (cmd inside {ReadDual, WriteDual}) {
        command_reg.mode == Dual;
      } else {
        command_reg.mode == Quad;
      }
    }
 }

  constraint command_reg_lencsaat_c {
    if (seg_type == Command) {
      command_reg.len == num_cmd_bytes - 1;
    } else
    if (seg_type == Dummy) {
      command_reg.len == num_dummy - 1;
    } else {
      command_reg.len inside {[spi_len_min - 1 : spi_len_max - 1]};
    }

    // ensure we only half or full word writes
    (command_reg.len + 1) % 2 == 0;
    // default set keep transaction going
    command_reg.csaat == 1;
  }

  constraint data_c {
    if (seg_type == Command) {
      spi_data.size() == num_cmd_bytes;
    } else
    if (seg_type == Dummy) {
      spi_data.size() == num_dummy;
    } else {
      spi_data.size() == command_reg.len + 1;
    }

    solve command_reg.len before spi_data;
  }


  virtual function void do_copy(uvm_object rhs);
    spi_segment_item rhs_;
    `downcast(rhs_, rhs);
    super.do_copy(rhs);
    cmd                   = rhs_.cmd;
    rx_only_weight        = rhs_.rx_only_weight;
    tx_only_weight        = rhs_.tx_only_weight;
    num_dummy             = rhs_.num_dummy;
    num_cmd_bytes         = rhs_.num_cmd_bytes;
    seg_type              = rhs_.seg_type;
    command_reg.csaat     = rhs_.command_reg.csaat;
    command_reg.direction = rhs_.command_reg.direction;
    command_reg.mode      = rhs_.command_reg.mode;
    command_reg.len       = rhs_.command_reg.len;
    spi_data              = rhs_.spi_data;
  endfunction


  function void post_randomize();
    if (seg_type == Command) begin
      spi_data[0] = cmd;
    end
  endfunction


  function string convert2string();
    string txt = "";

    txt = {txt, $sformatf("\n ----| Command Register |----")};
    txt = {txt, $sformatf("\n ----| Command: %s", cmd.name)};
    txt = {txt, $sformatf("\n ----| Segment %s", seg_type.name)};
    txt = {txt, $sformatf("\n ----| Length: %d", command_reg.len)};
    txt = {txt, $sformatf("\n ----| Mode: %s", command_reg.mode.name)};
    txt = {txt, $sformatf("\n ----| CSAAT: %d", command_reg.csaat)};
    txt = {txt, $sformatf("\n ----| Direction: %s", command_reg.direction.name)};
    txt = {txt, $sformatf("\n ----| DATA |----")};
    foreach (spi_data[i]) begin
      txt = {txt, $sformatf("\n ----| [%d] %2h |----", i, spi_data[i])};
    end
    return txt;
  endfunction
endclass
