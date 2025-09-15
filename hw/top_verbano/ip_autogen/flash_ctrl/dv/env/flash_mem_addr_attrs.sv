// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Provides abstraction for mapping a flash memory address in flash organization.
class flash_mem_addr_attrs;

    addr_t addr;               // Input addr, bus-word aligned.
    addr_t bank_addr;          // Addr within the bank, bus-word aligned.
    addr_t word_addr;          // Addr within the bank, flash word aligned.
    int    offset;             // Byte offset within the flash word.

    addr_t bank_start_addr;    // Start addr of the bank (bus word aligned).
    addr_t page_start_addr;    // Start addr of the page within the bank.

    uint            bank;               // The bank the address belongs to.
    uint            page;               // The page within the bank.
    uint            line;               // The word line within the page.
    uint            byte_offset;        // Byte offset within the flash word.

  function new(addr_t addr = 0);
    set_attrs(addr);
  endfunction

  // Set attributes from a sample input addr.
  function void set_attrs(addr_t addr);
    this.addr = {addr[TL_AW-1:TL_SZW], {TL_SZW{1'b0}}};
    bank_addr = this.addr[FlashMemAddrPageMsbBit : 0];
    word_addr = {bank_addr[TL_AW-1:FlashDataByteWidth], {FlashDataByteWidth{1'b0}}};

    bank_start_addr = {addr[TL_AW-1 : FlashMemAddrPageMsbBit+1], {FlashMemAddrPageMsbBit+1{1'b0}}};
    page_start_addr = {addr[FlashMemAddrPageMsbBit : FlashMemAddrLineMsbBit+1],
                       {FlashMemAddrLineMsbBit+1{1'b0}}};

    bank = addr[FlashMemAddrBankMsbBit : FlashMemAddrPageMsbBit+1];
    page = addr[FlashMemAddrPageMsbBit : FlashMemAddrLineMsbBit+1];
    line = addr[FlashMemAddrLineMsbBit : FlashMemAddrWordMsbBit+1];
    byte_offset = addr[FlashDataByteWidth-1 : 0];
  endfunction

  function void incr(addr_t offset);
    set_attrs(addr + offset);
  endfunction

  function string sprint();
    return $sformatf({{"addr_attrs: addr = 0x%0h, word_addr = 0x%0h, bank_addr = 0x%0h "},
                      {"bank_start_addr = 0x%0h, page_start_addr = 0x%0h "},
                      {"bank = %0d, page = %0d, line = %0d, byte_offset = %0d"}},
                     addr, word_addr, bank_addr, bank_start_addr, page_start_addr,
                     bank, page, line, byte_offset);
  endfunction

endclass
