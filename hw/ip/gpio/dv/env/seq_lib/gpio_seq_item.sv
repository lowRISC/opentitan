// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

`ifndef GPIO_SEQ_ITEM_SV
`define GPIO_SEQ_ITEM_SV

import gpio_pkg::*;
import tlul_pkg::*;
class gpio_seq_item extends uvm_sequence_item;

    `uvm_object_utils(gpio_seq_item)

    // Input and output variables
    rand bit strap_en_i;
    rand gpio_straps_t sampled_straps_o;

    rand tl_h2d_t tl_i;
    rand tl_d2h_t tl_o;

    rand bit intr_gpio_o;

    rand bit alert_rx_i;
    rand bit alert_tx_o;

    rand bit [NUM_GPIOS-1:0] cio_gpio_i;
    rand bit [NUM_GPIOS-1:0] cio_gpio_o;
    rand bit [NUM_GPIOS-1:0] cio_gpio_en_o;

    // Constructor
    function new(string name = "gpio_seq_item");
        super.new(name);
    endfunction

    // Copy function
    function void do_copy(uvm_object rhs);
        gpio_seq_item rhs_;
        if (!$cast(rhs_, rhs)) begin
            `uvm_fatal("do_copy", "Cast failed")
        end
        this.strap_en_i = rhs_.strap_en_i;
        this.sampled_straps_o = rhs_.sampled_straps_o;
        this.tl_i = rhs_.tl_i;
        this.tl_o = rhs_.tl_o;
        this.intr_gpio_o = rhs_.intr_gpio_o;
        this.alert_rx_i = rhs_.alert_rx_i;
        this.alert_tx_o = rhs_.alert_tx_o;
        this.cio_gpio_i = rhs_.cio_gpio_i;
        //printer.print_field("tl_i", tl_i, $bits(tl_i));
        //printer.print_generic("tl_o", tl_o.convert2string());
    endfunction

    // Print function
    // This function prints the fields of the gpio_seq_item class using the provided UVM printer.
    // It is used for debugging and logging purposes to display the current values of the class fields.
    function void do_print(uvm_printer printer);
        super.do_print(printer);
        printer.print_field("strap_en_i", strap_en_i, $bits(strap_en_i));
        //printer.print_generic("sampled_straps_o", sampled_straps_o.data.convert2string());
        //printer.print_generic("tl_i", tl_i);
        printer.print_field("tl_o", tl_o, $bits(tl_o));
        printer.print_field("intr_gpio_o", intr_gpio_o, $bits(intr_gpio_o));
        printer.print_field("alert_rx_i", alert_rx_i, $bits(alert_rx_i));
        printer.print_field("alert_tx_o", alert_tx_o, $bits(alert_tx_o));
        printer.print_field("cio_gpio_i", cio_gpio_i, $bits(cio_gpio_i));
        printer.print_field("cio_gpio_o", cio_gpio_o, $bits(cio_gpio_o));
        printer.print_field("cio_gpio_en_o", cio_gpio_en_o, $bits(cio_gpio_en_o));
    endfunction

endclass

`endif // GPIO_SEQ_ITEM_SV