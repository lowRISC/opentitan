// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

`ifndef GPIO_SEQ_ITEM_SV
`define GPIO_SEQ_ITEM_SV

import ${module_instance_name}_pkg::*;
import tlul_pkg::*;
class ${module_instance_name}_seq_item extends uvm_sequence_item;

    `uvm_object_utils(${module_instance_name}_seq_item)

    // Input and output variables
    rand bit                 strap_en_i;
    rand bit                 alert_rx_i;
    rand tl_h2d_t            tl_i;
    rand bit [NUM_GPIOS-1:0] cio_${module_instance_name}_i;

    tl_d2h_t            tl_o;
    ${module_instance_name}_straps_t       sampled_straps_o;
    bit                 intr_${module_instance_name}_o;
    bit                 alert_tx_o;
    bit [NUM_GPIOS-1:0] cio_${module_instance_name}_o;
    bit [NUM_GPIOS-1:0] cio_${module_instance_name}_en_o;

    // Constructor
    function new(string name = "${module_instance_name}_seq_item");
        super.new(name);
    endfunction
endclass
`endif // GPIO_SEQ_ITEM_SV
