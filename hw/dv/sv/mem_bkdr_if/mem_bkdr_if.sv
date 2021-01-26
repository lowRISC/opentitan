// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Description: mem_bkdr_if binds to the ram/rom instance to do a backdoor write / read to the
// memory array directly. It needs to be bound to the right ram / rom wrappers to work. Currently,
// these are limited to: prim_ram_1p, prim_ram_2p, prim_rom
//
// The following assumptions are made:
// 1. This interface will be bound to one of the following modules:
//    prim_ram_1p, prim_ram_2p, prim_rom
// 2. The sub hierarchy from within these instances to the memory element will be fixed to
//    'gen_generic.u_impl_generic.mem'
//
// If these assumptions are met, then the generic interface can be used to bind to any instance with
// any parameter set and can be set into the uvm_config_db to allow us to manipulate the mem
// contents from the testbench without having us to add heirarchy information, making the chip
// testbench portable.
interface mem_bkdr_if();
  import uvm_pkg::*;
  import bus_params_pkg::BUS_AW;
  `include "uvm_macros.svh"
  `include "dv_macros.svh"

  // sub hierarchy slice to the memory element
  // TODO: need to publicize this info - user needs to set the below macro correctly when swapping
  // out srams with vendor library models. Also, need to address the scenario where not all ram
  // instances are replaced with vendor library models.
`ifndef MEM_ARR_PATH_SLICE
  `define MEM_ARR_PATH_SLICE gen_generic.u_impl_generic.mem
`endif

  // derive memory specifics such as depth, width, addr_msb mem size etc.
  bit initialized;
  int mem_depth;
  int mem_width;
  int mem_bytes_per_index;
  int mem_size_bytes;
  int mem_addr_lsb;
  string path = $sformatf("%m");

  function automatic void init();
    if (!initialized) begin
      mem_depth = $size(`MEM_ARR_PATH_SLICE);
      mem_width = $bits(`MEM_ARR_PATH_SLICE) / mem_depth;
      mem_bytes_per_index = mem_width / 8;
      mem_size_bytes = mem_depth * mem_bytes_per_index;
      mem_addr_lsb = $clog2(mem_bytes_per_index);
      `uvm_info(path, $sformatf("mem_depth = %0d", mem_depth), UVM_HIGH)
      `uvm_info(path, $sformatf("mem_width = %0d", mem_width), UVM_HIGH)
      `uvm_info(path, $sformatf("mem_bytes_per_index = %0d", mem_bytes_per_index), UVM_HIGH)
      `uvm_info(path, $sformatf("mem_size_bytes = %0d", mem_size_bytes), UVM_HIGH)
      `uvm_info(path, $sformatf("mem_addr_lsb = %0d", mem_addr_lsb), UVM_HIGH)
      `DV_CHECK_LE_FATAL(mem_bytes_per_index, 8, "mem data width > 8 bytes is not supported", path)
      initialized = 1'b1;
    end
  endfunction

  // input addr is assumed to be the byte addressable address into memory starting at 0
  // user assumes the responsibility of masking the upper bits
  function automatic bit is_addr_valid(input bit [bus_params_pkg::BUS_AW-1:0] addr);
    init();
    if (addr >= mem_size_bytes) begin
      `uvm_error(path, $sformatf("addr = %0h is out of bounds (size = %0d)", addr, mem_size_bytes))
      return 1'b0;
    end
    return 1'b1;
  endfunction

  // read a single byte at specified address
  function automatic logic [7:0] read8(input bit [bus_params_pkg::BUS_AW-1:0] addr);
    if (is_addr_valid(addr)) begin
      int mem_index = addr >> mem_addr_lsb;
      logic [63:0] mem_data = `MEM_ARR_PATH_SLICE[mem_index];
      case (mem_bytes_per_index)
        1: begin
          return mem_data[7:0];
        end
        2: begin
          case (addr[0])
            1'b0:  return mem_data[7:0];
            1'b1:  return mem_data[15:8];
            default: ;
          endcase
        end
        4: begin
          case (addr[1:0])
            2'b00:  return mem_data[7:0];
            2'b01:  return mem_data[15:8];
            2'b10:  return mem_data[23:16];
            2'b11:  return mem_data[31:24];
            default: ;
          endcase
        end
        8: begin
          case (addr[2:0])
            3'b000:  return mem_data[7:0];
            3'b001:  return mem_data[15:8];
            3'b010:  return mem_data[23:16];
            3'b011:  return mem_data[31:24];
            3'b100:  return mem_data[39:32];
            3'b101:  return mem_data[47:40];
            3'b110:  return mem_data[55:48];
            3'b111:  return mem_data[63:56];
            default: ;
          endcase
        end
        default: ;
      endcase
    end
    return 'x;
  endfunction

  function automatic logic [15:0] read16(input bit [bus_params_pkg::BUS_AW-1:0] addr);
    `DV_CHECK_EQ_FATAL(addr[0], '0, $sformatf("addr 0x%0h not 16-bit aligned", addr), path)
    if (is_addr_valid(addr)) begin
      int mem_index = addr >> mem_addr_lsb;
      logic [63:0] mem_data = `MEM_ARR_PATH_SLICE[mem_index];
      case (mem_bytes_per_index)
        1: begin
          return {read8(addr + 1), mem_data[7:0]};
        end
        2: begin
          return mem_data[15:0];
        end
        4: begin
          case (addr[1])
            1'b0:  return mem_data[15:0];
            1'b1:  return mem_data[31:16];
            default: ;
          endcase
        end
        8: begin
          case (addr[2:1])
            2'b00:  return mem_data[15:0];
            2'b01:  return mem_data[31:16];
            2'b10:  return mem_data[47:32];
            2'b11:  return mem_data[63:48];
            default: ;
          endcase
        end
        default: ;
      endcase
    end
    return 'x;
  endfunction

  function automatic logic [31:0] read32(input bit [bus_params_pkg::BUS_AW-1:0] addr);
    `DV_CHECK_EQ_FATAL(addr[1:0], '0, $sformatf("addr 0x%0h not 32-bit aligned", addr), path)
    if (is_addr_valid(addr)) begin
      int mem_index = addr >> mem_addr_lsb;
      logic [63:0] mem_data = `MEM_ARR_PATH_SLICE[mem_index];
      case (mem_bytes_per_index)
        1: begin
          return {read16(addr + 2), read8(addr + 1), mem_data[7:0]};
        end
        2: begin
          return {read16(addr + 2), mem_data[15:0]};
        end
        4: begin
          return mem_data[31:0];
        end
        8: begin
          case (addr[2])
            1'b0:  return mem_data[31:0];
            1'b1:  return mem_data[63:32];
            default: ;
          endcase
        end
        default: ;
      endcase
    end
    return 'x;
  endfunction

  function automatic logic [63:0] read64(input bit [bus_params_pkg::BUS_AW-1:0] addr);
    `DV_CHECK_EQ_FATAL(addr[2:0], '0, $sformatf("addr 0x%0h not 64-bit aligned", addr), path)
    return {read32(addr + 4), read32(addr)};
  endfunction

  function automatic void write8(input bit [bus_params_pkg::BUS_AW-1:0] addr, input bit [7:0] data);
    if (is_addr_valid(addr)) begin
      int mem_index = addr >> mem_addr_lsb;
      bit [63:0] rw_data = `MEM_ARR_PATH_SLICE[mem_index];
      case (mem_bytes_per_index)
        1: begin
          rw_data[7:0] = data;
        end
        2: begin
          case (addr[0])
            1'b0:  rw_data[7:0] = data;
            1'b1:  rw_data[15:8] = data;
            default: ;
          endcase
        end
        4: begin
          case (addr[1:0])
            2'b00:  rw_data[7:0] = data;
            2'b01:  rw_data[15:8] = data;
            2'b10:  rw_data[23:16] = data;
            2'b11:  rw_data[31:24] = data;
            default: ;
          endcase
        end
        8: begin
          case (addr[2:0])
            3'b000: rw_data[7:0] = data;
            3'b001: rw_data[15:8] = data;
            3'b010: rw_data[23:16] = data;
            3'b011: rw_data[31:24] = data;
            3'b100: rw_data[39:32] = data;
            3'b101: rw_data[47:40] = data;
            3'b110: rw_data[55:48] = data;
            3'b111: rw_data[63:56] = data;
            default: ;
          endcase
        end
        default: ;
      endcase
      `MEM_ARR_PATH_SLICE[mem_index] = rw_data;
    end
  endfunction

  function automatic void write16(input bit [bus_params_pkg::BUS_AW-1:0] addr,
                                  input bit [15:0] data);
    `DV_CHECK_EQ_FATAL(addr[0], '0, $sformatf("addr 0x%0h not 16-bit aligned", addr), path)
    if (is_addr_valid(addr)) begin
      int mem_index = addr >> mem_addr_lsb;
      bit [63:0] rw_data = `MEM_ARR_PATH_SLICE[mem_index];
      case (mem_bytes_per_index)
        1: begin
          rw_data[7:0] = data[7:0];
          write8(addr + 1, data[15:8]);
        end
        2: begin
          rw_data[15:0] = data;
        end
        4: begin
          case (addr[1])
            1'b0: rw_data[15:0] = data;
            1'b1: rw_data[31:16] = data;
            default: ;
          endcase
        end
        8: begin
          case (addr[2:1])
            2'b00:  rw_data[15:0] = data;
            2'b01:  rw_data[32:16] = data;
            2'b10:  rw_data[47:32] = data;
            2'b11:  rw_data[63:48] = data;
            default: ;
          endcase
        end
        default: ;
      endcase
      `MEM_ARR_PATH_SLICE[mem_index] = rw_data;
    end
  endfunction

  function automatic void write32(input bit [bus_params_pkg::BUS_AW-1:0] addr,
                                  input bit [31:0] data);
    `DV_CHECK_EQ_FATAL(addr[1:0], '0, $sformatf("addr 0x%0h not 32-bit aligned", addr), path)
    if (is_addr_valid(addr)) begin
      int mem_index = addr >> mem_addr_lsb;
      bit [63:0] rw_data = `MEM_ARR_PATH_SLICE[mem_index];
      case (mem_bytes_per_index)
        1: begin
          rw_data[7:0] = data[7:0];
          write8(addr + 1, data[15:8]);
          write16(addr + 2, data[31:16]);
        end
        2: begin
          rw_data[15:0] = data[15:0];
          write16(addr + 2, data[31:16]);
        end
        4: begin
          rw_data[31:0] = data;
        end
        8: begin
          case (addr[2])
            1'b0:  rw_data[31:0] = data;
            1'b1:  rw_data[63:32] = data;
            default: ;
          endcase
        end
        default: ;
      endcase
      `MEM_ARR_PATH_SLICE[mem_index] = rw_data;
    end
  endfunction

  function automatic void write64(input bit [bus_params_pkg::BUS_AW-1:0] addr,
                                  input bit [63:0] data);
    `DV_CHECK_EQ_FATAL(addr[2:0], '0, $sformatf("addr 0x%0h not 64-bit aligned", addr), path)
    write32(addr, data[31:0]);
    write32(addr + 4, data[63:32]);
  endfunction

  // check if input file is read/writable
  function automatic void check_file(string file, bit wr);
    string mode = wr ? "w": "r";
    int fh = $fopen(file, mode);
    init();
    if (!fh) begin
      `uvm_fatal(path, $sformatf("file %0s could not be opened for %0s mode", file, mode))
    end
    else begin
      $fclose(fh);
    end
  endfunction

  // load mem from file
  function automatic void load_mem_from_file(string file);
    check_file(file, 1'b0);
    init();
    `uvm_info(path, $sformatf("Reading mem contents from file:\n%0s", file), UVM_LOW)
    $readmemh(file, `MEM_ARR_PATH_SLICE);
  endfunction

  // save mem contents to file
  function automatic void write_mem_to_file(string file);
    check_file(file, 1'b1);
    init();
    `uvm_info(path, $sformatf("Writing mem contents to file:\n%0s", file), UVM_LOW)
    $writememh(file, `MEM_ARR_PATH_SLICE, 0, mem_depth - 1);
  endfunction

  // print mem
  function automatic void print_mem();
    init();
    for (int i = 0; i < mem_depth; i++) begin
      `uvm_info(path, $sformatf("mem[%0d] = 0x%0h", i, `MEM_ARR_PATH_SLICE[i]), UVM_NONE)
    end
  endfunction

  // clear or set memory
  function automatic void clear_mem();
    init();
    `uvm_info(path, "Clear memory", UVM_LOW)
    `MEM_ARR_PATH_SLICE = '{default:'0};
  endfunction // clr_mem

  function automatic void set_mem();
    init();
    `uvm_info(path, "Set memory", UVM_LOW)
    `MEM_ARR_PATH_SLICE = '{default:'1};
  endfunction

  // randomize the memory
  function automatic void randomize_mem();
    init();
    `uvm_info(path, "Randomizing mem contents", UVM_LOW)
    foreach (`MEM_ARR_PATH_SLICE[i]) `MEM_ARR_PATH_SLICE[i] = {$urandom, $urandom};
  endfunction

  // invalidate the memory.
  function automatic void invalidate_mem();
    init();
    `uvm_info(path, "Invalidating (Xs) mem contents", UVM_LOW)
    `MEM_ARR_PATH_SLICE = '{default:'X};
  endfunction

endinterface
