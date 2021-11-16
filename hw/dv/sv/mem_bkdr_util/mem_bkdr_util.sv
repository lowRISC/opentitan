// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Provides a mechanism to manipulate and access a memory instance in the design via backdoor.
//
// This is a class based implementation, which on initialization (`new()`) takes the path to the
// memory hierarchy, the size in bits, the depth, integrity protection and scrambling needs as
// arguments. All memory specifics are set / computed at runtime. There are no parameterizations, so
// that the implementation is flexible, extensible, and easy to use.
//
// Create an instance of this class in the testbench module itself, so that the hierarchical path to
// the memory element and its size and depth information is available. Pass the instance to the UVM
// side via uvm_config_db.
class mem_bkdr_util extends uvm_object;
  // Hierarchical path to the memory.
  protected string path;

  // The depth of the memory.
  protected uint32_t depth;

  // The width of the memory.
  protected uint32_t width;

  // Indicates the error detection scheme implemented for this memory.
  protected err_detection_e err_detection_scheme = ErrDetectionNone;

  // Convenience macro to check if ECC / parity is enabled.
  `define HAS_ECC (!(err_detection_scheme inside {ErrDetectionNone, ParityEven, ParityOdd}))
  `define HAS_PARITY (err_detection_scheme inside {ParityEven, ParityOdd})

  // TODO: Indicates whether the memory implements scrambling.

  // Other memory specifics derived from the settings above.
  protected uint32_t data_width;  // ignoring ECC bits
  protected uint32_t byte_width;
  protected uint32_t bytes_per_word;  // addressable bytes
  protected uint32_t size_bytes;  // addressable bytes
  protected uint32_t addr_lsb;
  protected uint32_t addr_width;
  protected uint32_t byte_addr_width;

  // Indicates the maximum number of errors that can be injected.
  //
  // If parity is enabled, this limit applies to a single byte in the memory width. We cannot inject
  // more than 1 error per each byte of data. In case of ECC, it applies to the entire width.
  protected uint32_t max_errors;

  // File operations.
  //
  // We unfortunately cannot use the system tasks $readmemh and $writememh due to class based
  // implementation. This is done externally in the testbench module where the class instance is
  // created instead. The following signals and events are used by the testbench to know when to
  // read or write the memory with the contents of the file.
  protected string file;
  event readmemh_event;
  event writememh_event;

  // Initialize the class instance.
  function new(string name = "", string path, int unsigned depth,
               longint unsigned n_bits, err_detection_e err_detection_scheme);

    bit res;
    super.new(name);
    `DV_CHECK_FATAL(!(n_bits % depth), "n_bits must be divisible by depth.")
    res = uvm_hdl_check_path(path);
    `DV_CHECK_EQ_FATAL(res, 1, $sformatf("Hierarchical path %0s appears to be invalid.", path))

    this.path  = path;
    this.depth = depth;
    this.width = n_bits / depth;
    this.err_detection_scheme = err_detection_scheme;

    if (`HAS_ECC) begin
      import prim_secded_pkg::prim_secded_e;
      import prim_secded_pkg::get_ecc_data_width;
      import prim_secded_pkg::get_ecc_parity_width;

      prim_secded_e secded_eds = prim_secded_e'(err_detection_scheme);
      int non_ecc_bits_per_subword = get_ecc_data_width(secded_eds);
      int ecc_bits_per_subword = get_ecc_parity_width(secded_eds);
      int bits_per_subword = non_ecc_bits_per_subword + ecc_bits_per_subword;
      int subwords_per_word;

      // We shouldn't truncate the actual data word. This check ensures that err_detection_scheme
      // and width are related sensibly. This only checks we've got enough space for one data word
      // and at least one check bit. The next check will make sure that we don't truncate if there
      // are multiple subwords.
      `DV_CHECK_FATAL(non_ecc_bits_per_subword < this.width)

      // Normally, we'd want width to be divisible by bits_per_subword, which means that we get a
      // whole number of subwords in a word. As a special case, we also allow a having exactly one
      // subword and only keeping some of the bits. This is used by the flash controller.
      `DV_CHECK_FATAL((this.width < bits_per_subword) || (this.width % bits_per_subword == 0),
                      "With multiple subwords, mem width must be a multiple of the ECC width")

      subwords_per_word = (width + bits_per_subword - 1) / bits_per_subword;
      this.data_width = subwords_per_word * non_ecc_bits_per_subword;
    end else begin
      this.data_width = width;
    end

    byte_width = `HAS_PARITY ? 9 : 8;
    bytes_per_word = data_width / byte_width;
    `DV_CHECK_LE_FATAL(bytes_per_word, 32, "data width > 32 bytes is not supported")
    size_bytes = depth * bytes_per_word;
    addr_lsb   = $clog2(bytes_per_word);
    addr_width = $clog2(depth);
    byte_addr_width = addr_width + addr_lsb;
    max_errors = width;
    if (name == "") set_name({path, "::mem_bkdr_util"});
    `uvm_info(`gfn, this.convert2string(), UVM_MEDIUM)
  endfunction

  virtual function string convert2string();
    return {"\n",
            $sformatf("path = %0s\n", path),
            $sformatf("depth = %0d\n", depth),
            $sformatf("width = %0d\n", width),
            $sformatf("err_detection_scheme = %0s\n", err_detection_scheme.name),
            $sformatf("data_width = %0d\n", data_width),
            $sformatf("byte_width = %0d\n", byte_width),
            $sformatf("bytes_per_word = %0d\n", bytes_per_word),
            $sformatf("size_bytes = 0x%0h\n", size_bytes),
            $sformatf("addr_lsb = %0d\n", addr_lsb),
            $sformatf("addr_width = %0d\n", addr_width),
            $sformatf("byte_addr_width = %0d\n", byte_addr_width),
            $sformatf("max_errors = %0d\n", max_errors)};
  endfunction

  function string get_path();
    return path;
  endfunction

  function uint32_t get_depth();
    return depth;
  endfunction

  function uint32_t get_width();
    return width;
  endfunction

  function err_detection_e get_err_detection_scheme();
    return err_detection_scheme;
  endfunction

  function uint32_t get_data_width();
    return data_width;
  endfunction

  function uint32_t get_byte_width();
    return byte_width;
  endfunction

  function uint32_t get_bytes_per_word();
    return bytes_per_word;
  endfunction

  function uint32_t get_size_bytes();
    return size_bytes;
  endfunction

  function uint32_t get_addr_lsb();
    return addr_lsb;
  endfunction

  function uint32_t get_addr_width();
    return addr_width;
  endfunction

  function uint32_t get_byte_addr_width();
    return byte_addr_width;
  endfunction

  function string get_file();
    return file;
  endfunction

  // Returns 1 if the given address falls within the memory's range, else 0.
  //
  // If addr is invalid, it throws UVM error before returning 0.
  protected virtual function bit check_addr_valid(bit [bus_params_pkg::BUS_AW-1:0] addr);
    if (addr >= size_bytes) begin
      `uvm_error(`gfn, $sformatf("addr %0h is out of bounds: size = %0h", addr, size_bytes))
      return 1'b0;
    end
    return 1'b1;
  endfunction

  // Read the entire word at the given address.
  //
  // addr is the byte address starting at offset 0. Mask the upper address bits as needed before
  // invocation.
  //
  // Returns the entire width of the memory at the given address, including the ECC bits. The data
  // returned is 'raw' i.e. it includes the parity bits. It also does not de-scramble the data if
  // encryption is enabled.
  //
  // TODO: Factor in encryption into this function itself?
  virtual function uvm_hdl_data_t read(bit [bus_params_pkg::BUS_AW-1:0] addr);
    bit res;
    uint32_t index;
    uvm_hdl_data_t data;
    if (!check_addr_valid(addr)) return 'x;
    index = addr >> addr_lsb;
    res   = uvm_hdl_read($sformatf("%0s[%0d]", path, index), data);
    `DV_CHECK_EQ(res, 1, $sformatf("uvm_hdl_read failed at index %0d", index))
    return data;
  endfunction

  // Convenience macro to check the addr for each flavor of read and write functions.
  `define _ACCESS_CHECKS(_ADDR, _DW) \
    `DV_CHECK_EQ_FATAL(_ADDR % (_DW / 8), 0, $sformatf("addr 0x%0h not ``_DW``-bit aligned", _ADDR))

  // Read a single byte at specified address.
  //
  // The data returned does not include the parity bits.
  virtual function logic [7:0] read8(bit [bus_params_pkg::BUS_AW-1:0] addr);
    uvm_hdl_data_t data = read(addr);
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
    bit res;
    uint32_t index;
    if (!check_addr_valid(addr)) return;
    index = addr >> addr_lsb;
    res   = uvm_hdl_deposit($sformatf("%0s[%0d]", path, index), data);
    `DV_CHECK_EQ(res, 1, $sformatf("uvm_hdl_deposit failed at index %0d", index))
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

    rw_data  = read(addr);
    word_idx = addr >> addr_lsb;
    byte_idx = addr - (word_idx << addr_lsb);

    if (`HAS_PARITY) begin
      bit parity = (err_detection_scheme == ParityOdd) ? ~(^data) : (^data);
      rw_data[byte_idx * 9 +: 9] = {parity, data};
      write(addr, rw_data);
      return;
    end

    rw_data[byte_idx * 8 +: 8] = data;
    case (err_detection_scheme)
      ErrDetectionNone: ;
      Ecc_22_16: begin
        rw_data = prim_secded_pkg::prim_secded_22_16_enc(rw_data[15:0]);
      end
      EccHamming_22_16: begin
        rw_data = prim_secded_pkg::prim_secded_hamming_22_16_enc(rw_data[15:0]);
      end
      Ecc_39_32: begin
        rw_data = prim_secded_pkg::prim_secded_39_32_enc(rw_data[31:0]);
      end
      EccHamming_39_32: begin
        rw_data = prim_secded_pkg::prim_secded_hamming_39_32_enc(rw_data[31:0]);
      end
      Ecc_72_64: begin
        rw_data = prim_secded_pkg::prim_secded_72_64_enc(rw_data[63:0]);
      end
      EccHamming_72_64: begin
        rw_data = prim_secded_pkg::prim_secded_hamming_72_64_enc(rw_data[63:0]);
      end
      EccHamming_76_68: begin
        rw_data = prim_secded_pkg::prim_secded_hamming_76_68_enc(rw_data[63:0]);
      end
      EccInv_22_16: begin
        rw_data = prim_secded_pkg::prim_secded_inv_22_16_enc(rw_data[15:0]);
      end
      EccInvHamming_22_16: begin
        rw_data = prim_secded_pkg::prim_secded_inv_hamming_22_16_enc(rw_data[15:0]);
      end
      EccInv_39_32: begin
        rw_data = prim_secded_pkg::prim_secded_inv_39_32_enc(rw_data[31:0]);
      end
      EccInvHamming_39_32: begin
        rw_data = prim_secded_pkg::prim_secded_inv_hamming_39_32_enc(rw_data[31:0]);
      end
      EccInv_72_64: begin
        rw_data = prim_secded_pkg::prim_secded_inv_72_64_enc(rw_data[63:0]);
      end
      EccInvHamming_72_64: begin
        rw_data = prim_secded_pkg::prim_secded_inv_hamming_72_64_enc(rw_data[63:0]);
      end
      EccInvHamming_76_68: begin
        rw_data = prim_secded_pkg::prim_secded_inv_hamming_76_68_enc(rw_data[63:0]);
      end
      default: begin
        `uvm_error(`gfn, $sformatf("ECC scheme %0s is unsupported.", err_detection_scheme))
      end
    endcase
    write(addr, rw_data);
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

  `undef _ACCESS_CHECKS

  /////////////////////////////////////////////////////////
  // Wrapper functions for memory reads with ECC enabled //
  /////////////////////////////////////////////////////////
  // Some notes:
  // - ECC isn't supported for 8-bit wide memories
  // - (28, 22) and (64, 57) ECC configurations aren't supported

  // Intended for use with memories which have data width of 16 bits and 6 ECC bits.
  virtual function secded_22_16_t ecc_read16(bit [bus_params_pkg::BUS_AW-1:0] addr);
    uvm_hdl_data_t data;
    if (!check_addr_valid(addr)) return 'x;
    data = read(addr);
    case (err_detection_scheme)
      Ecc_22_16: begin
        return prim_secded_pkg::prim_secded_22_16_dec(data);
      end
      EccHamming_22_16: begin
        return prim_secded_pkg::prim_secded_hamming_22_16_dec(data);
      end
      EccInv_22_16: begin
        return prim_secded_pkg::prim_secded_inv_22_16_dec(data);
      end
      EccInvHamming_22_16: begin
        return prim_secded_pkg::prim_secded_inv_hamming_22_16_dec(data);
      end
      default: return 'x;
    endcase
  endfunction

  // Intended for use with memories which have data width of 32 bits and 7 ECC bits.
  virtual function secded_39_32_t ecc_read32(bit [bus_params_pkg::BUS_AW-1:0] addr);
    uvm_hdl_data_t data;
    if (!check_addr_valid(addr)) return 'x;
    data = read(addr);
    case (err_detection_scheme)
      Ecc_39_32: begin
        return prim_secded_pkg::prim_secded_39_32_dec(data);
      end
      EccHamming_39_32: begin
        return prim_secded_pkg::prim_secded_hamming_39_32_dec(data);
      end
      EccInv_39_32: begin
        return prim_secded_pkg::prim_secded_inv_39_32_dec(data);
      end
      EccInvHamming_39_32: begin
        return prim_secded_pkg::prim_secded_inv_hamming_39_32_dec(data);
      end
      default: return 'x;
    endcase
  endfunction

  // Intended for use with memories which have data width of 64 bits and 8 ECC bits.
  virtual function secded_72_64_t ecc_read64(bit [bus_params_pkg::BUS_AW-1:0] addr);
    uvm_hdl_data_t data;
    if (!check_addr_valid(addr)) return 'x;
    data = read(addr);
    case (err_detection_scheme)
      Ecc_72_64: begin
        return prim_secded_pkg::prim_secded_72_64_dec(data);
      end
      EccHamming_72_64: begin
        return prim_secded_pkg::prim_secded_hamming_72_64_dec(data);
      end
      EccInv_72_64: begin
        return prim_secded_pkg::prim_secded_inv_72_64_dec(data);
      end
      EccInvHamming_72_64: begin
        return prim_secded_pkg::prim_secded_inv_hamming_72_64_dec(data);
      end
      default: return 'x;
    endcase
  endfunction

  // check if input file is read/writable
  virtual function void check_file(string file, string mode);
    int fh = $fopen(file, mode);
    if (!fh) begin
      `uvm_fatal(`gfn, $sformatf("file %0s could not be opened for %0s mode", file, mode))
    end
    $fclose(fh);
  endfunction

  // load mem from file
  virtual function void load_mem_from_file(string file);
    check_file(file, "r");
    this.file = file;
    ->readmemh_event;
  endfunction

  // save mem contents to file
  virtual function void write_mem_to_file(string file);
    check_file(file, "w");
    this.file = file;
    ->writememh_event;
  endfunction

  // print mem
  virtual function void print_mem();
    for (int i = 0; i < depth; i++) begin
      `uvm_info(`gfn, $sformatf("mem[%0d] = 0x%0h", i, read(i)), UVM_LOW)
    end
  endfunction

  // clear or set memory
  virtual function void clear_mem();
    `uvm_info(`gfn, "Clear memory", UVM_LOW)
    for (int i = 0; i < size_bytes; i++) begin
      write8(i, '0);
    end
  endfunction

  virtual function void set_mem();
    `uvm_info(`gfn, "Set memory", UVM_LOW)
    for (int i = 0; i < size_bytes; i++) begin
      write8(i, '1);
    end
  endfunction

  // randomize the memory
  virtual function void randomize_mem();
    logic [7:0] rand_val;
    `uvm_info(`gfn, "Randomizing mem contents", UVM_LOW)
    for (int i = 0; i < size_bytes; i++) begin
      `DV_CHECK_STD_RANDOMIZE_FATAL(rand_val, "Randomization failed!", path)
      write8(i, rand_val);
    end
  endfunction

  // invalidate the memory.
  virtual function void invalidate_mem();
    `uvm_info(`gfn, "Invalidating (Xs) mem contents", UVM_LOW)
    for (int i = 0; i < size_bytes; i++) begin
      write8(i, 'x);
    end
  endfunction

  // Inject ECC or parity errors to the memory word at the given address.
  virtual function void inject_errors(bit [bus_params_pkg::BUS_AW-1:0] addr,
                                      uint32_t inject_num_errors);
    uvm_hdl_data_t rw_data, err_mask;
    if (!check_addr_valid(addr)) return;
    `DV_CHECK_LE_FATAL(inject_num_errors, max_errors)
    `DV_CHECK_STD_RANDOMIZE_WITH_FATAL(err_mask,
                                       $countones(err_mask) == inject_num_errors;
                                       (err_mask >> width) == '0;)
    rw_data = read(addr);
    write(addr, rw_data ^ err_mask);
    `uvm_info(`gfn, $sformatf(
              "Addr: %0h, original data: %0h, error_mask: %0h, backdoor inject data: %0h",
              addr, rw_data, err_mask, rw_data ^ err_mask), UVM_HIGH)
  endfunction

  // Wrapper function for backdoor write OTP partitions.
  `include "mem_bkdr_util__otp.sv"

  // Wrapper functions for encrypted SRAM reads and writes.
  `include "mem_bkdr_util__sram.sv"

  // Wrapper function for encrypted ROM reads.
  `include "mem_bkdr_util__rom.sv"

  `undef HAS_ECC
  `undef HAS_PARITY

endclass

// Convenience macro to enable file operations on the memory.
//
// The class based approach prevents us from invoking the system tasks $readmemh and $writememh
// directly. This macro is invoked in the top level testbench where the instance of the backdoor
// accessor is created, within an initial block. It forks off two threads that monitor separately
// events when the UVM sequences invoke either the task `load_mem_from_file()` to write to the
// memory with the contents of the file and `write_mem_to_file()` methods, to read the contents of
// the memory into the file.
//
// inst is the mem_bkdr_util instance created in the tesbench module.
// path is the raw path to the memory element in the design.
`define MEM_BKDR_UTIL_FILE_OP(inst, path) \
  fork \
    forever begin \
      string file; \
      @(inst.readmemh_event); \
      file = inst.get_file(); \
      `uvm_info(inst.`gfn, $sformatf("Loading mem from file:\n%0s", file), UVM_LOW) \
      $readmemh(file, path); \
    end \
    forever begin \
      string file; \
      @(inst.writememh_event); \
      file = inst.get_file(); \
      `uvm_info(inst.`gfn, $sformatf("Writing mem to file:\n%0s", file), UVM_LOW) \
      $writememh(file, path); \
    end \
  join_none
