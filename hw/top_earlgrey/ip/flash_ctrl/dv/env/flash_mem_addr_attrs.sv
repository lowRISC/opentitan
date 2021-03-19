// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Provides abstraction for mapping a flash memory address in flash organization.
class flash_mem_addr_attrs;
    bit [TL_AW-1:0] addr;             // Input addr (this is aligned to the bus word)
    bit [TL_AW-1:0] bank_addr;        // Addr within the bank.

    bit [TL_AW-1:0] bank_start_addr;  // Start addr of the bank.
    bit [TL_AW-1:0] page_start_addr;  // Start addr of the page within the bank.

    uint            bank;             // The bank the address belongs to.
    uint            page;             // The page within the bank.
    uint            line;             // The word line within the page.

  function new(bit [TL_AW-1:0] addr = 0);
    set_attrs(addr);
  endfunction

  // Set attributes from a sample input addr.
  function void set_attrs(bit [TL_AW-1:0] addr);
    this.addr = {addr[TL_AW-1:TL_SZW], {TL_SZW{1'b0}}};
    bank_addr = this.addr[FlashMemAddrPageMsbBit : 0];

    bank_start_addr = {addr[TL_AW-1 : FlashMemAddrPageMsbBit+1], {FlashMemAddrPageMsbBit+1{1'b0}}};
    page_start_addr = {addr[FlashMemAddrPageMsbBit : FlashMemAddrLineMsbBit+1],
                       {FlashMemAddrLineMsbBit+1{1'b0}}};

    bank = addr[FlashMemAddrBankMsbBit : FlashMemAddrPageMsbBit+1];
    page = addr[FlashMemAddrPageMsbBit : FlashMemAddrLineMsbBit+1];
    line = addr[FlashMemAddrLineMsbBit : FlashMemAddrWordMsbBit+1];
  endfunction

  function void incr(bit [TL_AW-1:0] offset);
    // TODO: Check for overflow
    set_attrs(addr + offset);
  endfunction

  function string sprint();
    return $sformatf({{"addr_attrs: addr = 0x%0h, bank_addr = 0x%0h "},
                      {"bank_start_addr = 0x%0h, page_start_addr = 0x%0h "},
                      {"bank = %0d, page = %0d, line = %0d"}},
                     addr, bank_addr, bank_start_addr, page_start_addr,
                     bank, page, line);
  endfunction

endclass
