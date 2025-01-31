// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class mem_util extends uvm_object;

  // Handle to a `mem_bkdr_util` instance for low-level word read/write via backdoor.
  protected mem_bkdr_util mem_bkdr_util_h;

  // Number of PRINCE half rounds for scrambling, can be [1..5].
  protected uint32_t num_prince_rounds_half;

  // Address range of this memory in the system address map.
  protected addr_range_t addr_range;

  // Construct an instance called name.
  //
  // Required arguments:
  //
  //   path:                 A hierarchical HDL path to the memory.
  //
  //   depth:                The number of memory rows.
  //
  //   n_bits:               The total size of the memory in bits.
  //
  //   err_detection_scheme  The error detection scheme that is implemented for the memory.
  //
  // Optional arguments:
  //
  //  num_prince_rounds_half   The number of rounds of PRINCE used to scramble the memory. This is
  //                           used for scrambled memories. This defaults to 3.
  //
  //  extra_bits_per_subword   When ECC is enabled, the words of the memory are divided into
  //                           separate subwords that are used for ECC checks. This gives the number
  //                           of extra bits added to each subword (to contain additional SECDED
  //                           metadata). This defaults to zero.
  //
  //  system_base_addr         The memory words accessed through this backdoor would normally be
  //                           indexed from zero. If this value is non-zero, the backdoor starts at
  //                           some higher index.
  //
  //  tiling_path              A path used for constructing HDL paths to individual tiles (used
  //                           when tile_depth < depth). By default this is empty because there are
  //                           no tiles that would need paths at all.
  //
  //  tile_depth               The number of rows of a single tle. By default, this is the entire
  //                           memory.
  function new(string name = "", string path, int unsigned depth,
               longint unsigned n_bits, err_detection_e err_detection_scheme,
               uint32_t num_prince_rounds_half = 3,
               uint32_t extra_bits_per_subword = 0, uint32_t system_base_addr = 0,
               string tiling_path = "", uint32_t tile_depth = depth);

    mem_bkdr_util_h = new({name, "::mem_bkdr_util", path, depth, n_bits, err_detection_scheme,
                          extra_bits_per_subword, tiling_path, tile_depth);

// TODO:
//            $sformatf("addr_range.start_addr = 0x%0h\n", addr_range.start_addr),
//            $sformatf("addr_range.end_addr = 0x%0h\n", addr_range.end_addr)};

    addr_range.start_addr = system_base_addr;
    addr_range.end_addr = system_base_addr + size_bytes - 1;

    this.num_prince_rounds_half = num_prince_rounds_half;
  endfunction

  function int get_num_prince_rounds_half();
    return num_prince_rounds_half;
  endfunction

  function bit is_valid_addr(int unsigned system_addr);
    return system_addr inside {[addr_range.start_addr:addr_range.end_addr]};
  endfunction

  // Convenience macro to check the addr for each flavor of read and write functions.
  `define _ACCESS_CHECKS(_ADDR, _DW) \
    `DV_CHECK_EQ_FATAL(_ADDR % (_DW / 8), 0, $sformatf("addr 0x%0h not ``_DW``-bit aligned", _ADDR))

  // Read the entire word at the given address.
  //
  // addr is the byte address starting at offset 0. Mask the upper address bits as needed before
  // invocation.
  //
  // Returns the entire width of the memory at the given address, including the ECC bits. The data
  // returned is 'raw' i.e. it includes the parity bits. It also does not de-scramble the data if
  // encryption is enabled.
  virtual function uvm_hdl_data_t read(bit [bus_params_pkg::BUS_AW-1:0] addr);
    return mem_bkdr_util_h.read(addr);
  endfunction

  // Read a single byte at specified address.
  //
  // The data returned does not include the parity bits.
  virtual function logic [7:0] read8(bit [bus_params_pkg::BUS_AW-1:0] addr);
    uvm_hdl_data_t data = mem_bkdr_util_h.read(addr);
    int byte_offset = addr % bytes_per_word;
    return (data >> (byte_offset * byte_width)) & 8'hff;
  endfunction

  virtual function logic [15:0] read16(bit [bus_params_pkg::BUS_AW-1:0] addr);
    `_ACCESS_CHECKS(addr, 16)
    return {read8(addr + 1), read8(addr)};
  endfunction

  virtual function logic [31:0] read32(bit [bus_params_pkg::BUS_AW-1:0] addr);
    `_ACCESS_CHECKS(addr, 32)
    return {read16(addr + 2), read16(addr)};
  endfunction

  // this is used to read 32bit of data plus 7 raw integrity bits.
  virtual function logic [38:0] read39integ(bit [bus_params_pkg::BUS_AW-1:0] addr);
    `_ACCESS_CHECKS(addr, 32) // this is essentially an aligned 32bit access.
    return read(addr) & 39'h7fffffffff;
  endfunction

  virtual function logic [63:0] read64(bit [bus_params_pkg::BUS_AW-1:0] addr);
    `_ACCESS_CHECKS(addr, 64)
    return {read32(addr + 4), read32(addr)};
  endfunction

  virtual function logic [127:0] read128(bit [bus_params_pkg::BUS_AW-1:0] addr);
    `_ACCESS_CHECKS(addr, 128)
    return {read64(addr + 8), read64(addr)};
  endfunction

  virtual function logic [255:0] read256(bit [bus_params_pkg::BUS_AW-1:0] addr);
    `_ACCESS_CHECKS(addr, 256)
    return {read128(addr + 16), read128(addr)};
  endfunction

  // Write the entire word at the given address with the specified data.
  //
  // addr is the byte address starting at offset 0. Mask the upper address bits as needed before
  // invocation.
  //
  // Updates the entire width of the memory at the given address, including the ECC bits.
  virtual function void write(bit [bus_params_pkg::BUS_AW-1:0] addr, uvm_hdl_data_t data);
    mem_bkdr_util_h.write(addr);
  endfunction

  // Write a single byte at specified address.
  //
  // Does a read-modify-write on the whole word. It updates the byte at the given address and
  // computes the parity and ECC bits as applicable.
  virtual function void write8(bit [bus_params_pkg::BUS_AW-1:0] addr, logic [7:0] data);
    uvm_hdl_data_t rw_data;
    uint32_t word_idx;
    uint32_t byte_idx;

    if (!check_addr_valid(addr)) return;

    rw_data  = mem_bkdr_util_h.read(addr);
    word_idx = addr >> addr_lsb;
    byte_idx = addr - (word_idx << addr_lsb);

    if (`HAS_PARITY) begin
      bit parity = (err_detection_scheme == ParityOdd) ? ~(^data) : (^data);
      rw_data[byte_idx * 9 +: 9] = {parity, data};
      write(addr, rw_data);
      return;
    end

    // Update the byte index with the new value.
    rw_data[byte_idx * 8 +: 8] = data;

    // Compute & set the new ECC value.
    rw_data = get_ecc_computed_data(rw_data);

    // Write the whole array back to the memory.
    mem_bkdr_util_h.write(addr, rw_data);
  endfunction

  virtual function void write16(bit [bus_params_pkg::BUS_AW-1:0] addr, logic [15:0] data);
    `_ACCESS_CHECKS(addr, 16)
    if (!check_addr_valid(addr)) return;
    write8(addr, data[7:0]);
    write8(addr + 1, data[15:8]);
  endfunction

  virtual function void write32(bit [bus_params_pkg::BUS_AW-1:0] addr, logic [31:0] data);
    `_ACCESS_CHECKS(addr, 32)
    if (!check_addr_valid(addr)) return;
    write16(addr, data[15:0]);
    write16(addr + 2, data[31:16]);
  endfunction

  // this is used to write 32bit of data plus 7 raw integrity bits.
  virtual function void write39integ(bit [bus_params_pkg::BUS_AW-1:0] addr, logic [38:0] data);
    `_ACCESS_CHECKS(addr, 32) // this is essentially an aligned 32bit access.
    if (!check_addr_valid(addr)) return;
    write(addr, data);
  endfunction

  virtual function void write64(bit [bus_params_pkg::BUS_AW-1:0] addr, logic [63:0] data);
    `_ACCESS_CHECKS(addr, 64)
    if (!check_addr_valid(addr)) return;
    write32(addr, data[31:0]);
    write32(addr + 4, data[63:32]);
  endfunction

  virtual function void write128(bit [bus_params_pkg::BUS_AW-1:0] addr, logic [127:0] data);
    `_ACCESS_CHECKS(addr, 128)
    if (!check_addr_valid(addr)) return;
    write64(addr, data[63:0]);
    write64(addr + 8, data[127:63]);
  endfunction

  virtual function void write256(bit [bus_params_pkg::BUS_AW-1:0] addr, logic [255:0] data);
    `_ACCESS_CHECKS(addr, 256)
    if (!check_addr_valid(addr)) return;
    write128(addr, data[127:0]);
    write128(addr + 16, data[255:128]);
  endfunction

  // load mem from file
  virtual task load_mem_from_file(string file);
    mem_bkdr_util_h.load_mem_from_file(file);
  endtask

  // save mem contents to file
  virtual function void write_mem_to_file(string file);
    mem_bkdr_util_h.write_mem_to_file(file);
  endfunction

  // Clear the memory to all 0s.
  virtual function void clear_mem();
    mem_bkdr_util_h.clear_mem();
  endfunction

  // Set the memory to all 1s.
  virtual function void set_mem();
    mem_bkdr_util_h.set_mem();
  endfunction

  // Randomize the memory with correct ECC.
  virtual function void randomize_mem();
    mem_bkdr_util_h.randomize_mem();
  endfunction

  // Invalidate the memory.
  virtual function void invalidate_mem();
    mem_bkdr_util_h.invalid_mem();
  endfunction

  `undef _ACCESS_CHECKS

endclass : mem_util
