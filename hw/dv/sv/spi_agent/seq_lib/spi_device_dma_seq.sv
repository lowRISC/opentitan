// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// --------------------
// Device sequence
// --------------------
class spi_device_dma_seq extends spi_base_seq;

  `uvm_object_utils(spi_device_dma_seq)

  spi_item data;

  typedef bit[7:0] data_t[];

  function new(string name="");
    super.new(name);
    data = spi_item::type_id::create("data");
    data = new();
    `DV_CHECK_RANDOMIZE_WITH_FATAL(data,
                                   item_type == SpiTransNormal;
                                   // Size must be in sync with test dma_inline_hashing.c
                                   data.size() == 512;
                                  )
  endfunction : new

  function data_t get_data();
    return data.data;
  endfunction : get_data

  virtual task body();
    forever begin
      start_item(data);
      finish_item(data);
      get_response(data);
    end
  endtask : body

endclass : spi_device_dma_seq
