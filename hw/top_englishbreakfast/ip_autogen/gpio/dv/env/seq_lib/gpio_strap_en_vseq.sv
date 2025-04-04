// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class gpio_strap_en_vseq extends  uvm_sequence #(gpio_seq_item);
  `uvm_object_utils(gpio_strap_en_vseq)

  gpio_seq_item item;
  bit strap_en;

  function new(string name = "gpio_strap_en_vseq");
      super.new(name);
      item = gpio_seq_item::type_id::create("item");
  endfunction

  task body();
      start_item(item);
      assert(item.randomize() with {strap_en_i == strap_en;});
      finish_item(item);
  endtask : body

endclass : gpio_strap_en_vseq
