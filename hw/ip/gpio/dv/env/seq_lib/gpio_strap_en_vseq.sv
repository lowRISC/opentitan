// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class gpio_strap_en_vseq extends gpio_base_vseq;
    `uvm_object_utils(gpio_strap_en_vseq)

    gpio_seq_item strap_en_item;

    function new(string name = "gpio_strap_en_vseq");
        super.new(name);
        strap_en_item = gpio_seq_item::type_id::create("strap_en_item");
    endfunction
  
    task body();
        start_item(strap_en_item);
        assert(strap_en_item.randomize());
        finish_item(strap_en_item);
    endtask : body
  
  endclass : gpio_strap_en_vseq
  