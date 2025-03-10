// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class ${module_instance_name}_strap_en_vseq extends  uvm_sequence #(${module_instance_name}_seq_item);
    `uvm_object_utils(${module_instance_name}_strap_en_vseq)

    ${module_instance_name}_seq_item item;
    bit strap_en;

    function new(string name = "${module_instance_name}_strap_en_vseq");
        super.new(name);
        item = ${module_instance_name}_seq_item::type_id::create("item");
    endfunction

    task body();
        start_item(item);
        assert(item.randomize() with {strap_en_i == strap_en;});
        finish_item(item);
    endtask : body

  endclass : ${module_instance_name}_strap_en_vseq
