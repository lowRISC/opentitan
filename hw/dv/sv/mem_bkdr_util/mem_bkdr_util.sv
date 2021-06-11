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

  // A pair of integers.
  typedef struct {
    int x;
    int y;
  } int_pair_t;

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

    data_width = `HAS_ECC ? prim_secded_pkg::get_ecc_data_width(
        prim_secded_pkg::prim_secded_e'(err_detection_scheme)) : width;
    byte_width = `HAS_PARITY ? 9 : 8;
    bytes_per_word = data_width / byte_width;
    `DV_CHECK_LE_FATAL(bytes_per_word, 16, "data width > 16 bytes is not supported")
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

  // Convenience macro to check the addr and data width for each flavor of read and write functions.
  `define _ADDR_DW_CHECKS(_ADDR, _DW) \
    `DV_CHECK_GE_FATAL(data_width, _DW, $sformatf("data_width %0d is < ``_DW``!", data_width)) \
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
    `_ADDR_DW_CHECKS(addr, 16)
    return {read8(addr + 1), read8(addr)};
  endfunction

  virtual function logic [31:0] read32(bit [bus_params_pkg::BUS_AW-1:0] addr);
    `_ADDR_DW_CHECKS(addr, 32)
    return {read16(addr + 2), read16(addr)};
  endfunction

  virtual function logic [63:0] read64(bit [bus_params_pkg::BUS_AW-1:0] addr);
    `_ADDR_DW_CHECKS(addr, 64)
    return {read32(addr + 4), read32(addr)};
  endfunction

  virtual function logic [127:0] read128(bit [bus_params_pkg::BUS_AW-1:0] addr);
    `_ADDR_DW_CHECKS(addr, 128)
    return {read64(addr + 8), read64(addr)};
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
  // computes the parity and ECC bits as applicable. Before writing the word back, it injects
  // 'inject_num_errors' errors if set to a positive value.
  virtual function void write8(bit [bus_params_pkg::BUS_AW-1:0] addr, logic [7:0] data,
                               uint32_t inject_num_errors = 0);
    uvm_hdl_data_t rw_data;
    uint32_t word_idx;
    uint32_t byte_idx;

    `DV_CHECK_LE_FATAL(inject_num_errors, max_errors)
    if (!check_addr_valid(addr)) return;

    rw_data  = read(addr);
    word_idx = addr >> addr_lsb;
    byte_idx = addr - (word_idx << addr_lsb);

    if (`HAS_PARITY) begin
      bit parity = (err_detection_scheme == ParityOdd) ? ~(^data) : (^data);
      bit [8:0] lane = {parity, data};
      if (inject_num_errors) begin
        lane ^= (1 << $urandom_range(0, byte_width - 1));
      end
      rw_data[byte_idx * 9 +: 9] = lane;
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
      default: begin
        `uvm_error(`gfn, $sformatf("ECC scheme %0s is unsupported.", err_detection_scheme))
      end
    endcase
    if (inject_num_errors) rw_data = inject_errors(rw_data, inject_num_errors);
    write(addr, rw_data);
  endfunction

  virtual function void write16(bit [bus_params_pkg::BUS_AW-1:0] addr, logic [15:0] data,
                                uint32_t inject_num_errors = 0);
    int_pair_t inject_num_errors_split;
    `_ADDR_DW_CHECKS(addr, 16)
    if (!check_addr_valid(addr)) return;
    // Split the number of errors into different sub-byte write.
    inject_num_errors_split = rand_split(inject_num_errors);
    write8(addr, data[7:0], inject_num_errors_split.x);
    write8(addr + 1, data[15:8], inject_num_errors_split.y);
  endfunction

  virtual function void write32(bit [bus_params_pkg::BUS_AW-1:0] addr, logic [31:0] data,
                                uint32_t inject_num_errors = 0);
    int_pair_t inject_num_errors_split;
    `_ADDR_DW_CHECKS(addr, 32)
    if (!check_addr_valid(addr)) return;
    // Split the number of errors into different sub-byte write.
    inject_num_errors_split = rand_split(inject_num_errors);
    write16(addr, data[15:0], inject_num_errors_split.x);
    write16(addr + 2, data[31:16], inject_num_errors_split.y);
  endfunction

  virtual function void write64(bit [bus_params_pkg::BUS_AW-1:0] addr, logic [63:0] data,
                                uint32_t inject_num_errors = 0);
    int_pair_t inject_num_errors_split;
    `_ADDR_DW_CHECKS(addr, 64)
    if (!check_addr_valid(addr)) return;
    // Split the number of errors into different sub-byte write.
    inject_num_errors_split = rand_split(inject_num_errors);
    write32(addr, data[31:0], inject_num_errors_split.x);
    write32(addr + 4, data[63:32], inject_num_errors_split.y);
  endfunction

  virtual function void write128(bit [bus_params_pkg::BUS_AW-1:0] addr, logic [127:0] data,
                                 uint32_t inject_num_errors = 0);
    int_pair_t inject_num_errors_split;
    `_ADDR_DW_CHECKS(addr, 128)
    if (!check_addr_valid(addr)) return;
    // Split the number of errors into different sub-byte write.
    inject_num_errors_split = rand_split(inject_num_errors);
    write64(addr, data[63:0], inject_num_errors_split.x);
    write64(addr + 4, data[127:63], inject_num_errors_split.y);
  endfunction

  `undef _ADDR_DW_CHECKS

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
      default: return 'x;
    endcase
  endfunction

  ///////////////////////////////////////////////////////////
  // Wrapper functions for encrypted read/write operations //
  ///////////////////////////////////////////////////////////

  virtual function logic [7:0] sram_encrypt_read8(logic [bus_params_pkg::BUS_AW-1:0] addr,
                                                  logic [SRAM_KEY_WIDTH-1:0]         key,
                                                  logic [SRAM_BLOCK_WIDTH-1:0]       nonce);
    logic [bus_params_pkg::BUS_AW-1:0] bus_addr = '0;
    logic [7:0]                        rdata = '0;

    logic rdata_arr     [] = new[8];
    logic scrambled_addr[] = new[addr_width];
    logic sram_addr     [] = new[addr_width];
    logic key_arr       [] = new[SRAM_KEY_WIDTH];
    logic nonce_arr     [] = new[SRAM_BLOCK_WIDTH];

    key_arr   = {<<{key}};
    nonce_arr = {<<{nonce}};

    for (int i = 0; i < addr_width; i++) begin
      sram_addr[i] = addr[addr_lsb + i];
    end

    // Calculate the scrambled address
    scrambled_addr = sram_scrambler_pkg::encrypt_sram_addr(sram_addr, addr_width, nonce_arr);

    // Construct bus representation of the address
    for (int i = 0; i < addr_lsb; i++) begin
      bus_addr[i] = addr[i];
    end
    for (int i = 0; i < addr_width; i++) begin
      bus_addr[addr_lsb + i] = scrambled_addr[i];
    end

    // Read memory, and return the decrypted data
    rdata = read8(bus_addr);
    rdata_arr = {<<{rdata}};
    rdata_arr = sram_scrambler_pkg::decrypt_sram_data(
        rdata_arr, 8, sram_addr, addr_width, key_arr, nonce_arr
    );
    rdata = {<<{rdata_arr}};
    return rdata;
  endfunction

  virtual function logic [15:0] sram_encrypt_read16(logic [bus_params_pkg::BUS_AW-1:0] addr,
                                                    logic [SRAM_KEY_WIDTH-1:0]         key,
                                                    logic [SRAM_BLOCK_WIDTH-1:0]       nonce);
    logic [bus_params_pkg::BUS_AW-1:0] bus_addr = '0;
    logic [15:0]                       rdata = '0;

    logic rdata_arr     [] = new[16];
    logic scrambled_addr[] = new[addr_width];
    logic sram_addr     [] = new[addr_width];
    logic key_arr       [] = new[SRAM_KEY_WIDTH];
    logic nonce_arr     [] = new[SRAM_BLOCK_WIDTH];

    key_arr   = {<<{key}};
    nonce_arr = {<<{nonce}};

    for (int i = 0; i < addr_width; i++) begin
      sram_addr[i] = addr[addr_lsb + i];
    end

    // Calculate the scrambled address
    scrambled_addr = sram_scrambler_pkg::encrypt_sram_addr(sram_addr, addr_width, nonce_arr);

    // Construct bus representation of the address
    for (int i = 0; i < addr_lsb; i++) begin
      bus_addr[i] = addr[i];
    end
    for (int i = 0; i < addr_width; i++) begin
      bus_addr[addr_lsb + i] = scrambled_addr[i];
    end

    // Read memory and return the decrypted data
    rdata = read16(bus_addr);
    rdata_arr = {<<{rdata}};
    rdata_arr = sram_scrambler_pkg::decrypt_sram_data(
        rdata_arr, 16, sram_addr, addr_width, key_arr, nonce_arr
    );
    rdata = {<<{rdata_arr}};
    return rdata;
  endfunction

  virtual function logic [31:0] sram_encrypt_read32(logic [bus_params_pkg::BUS_AW-1:0] addr,
                                                    logic [SRAM_KEY_WIDTH-1:0]         key,
                                                    logic [SRAM_BLOCK_WIDTH-1:0]       nonce);
    logic [bus_params_pkg::BUS_AW-1:0] bus_addr = '0;
    logic [31:0]                       rdata = '0;

    logic rdata_arr     [] = new[32];
    logic scrambled_addr[] = new[addr_width];
    logic sram_addr     [] = new[addr_width];
    logic key_arr       [] = new[SRAM_KEY_WIDTH];
    logic nonce_arr     [] = new[SRAM_BLOCK_WIDTH];

    key_arr   = {<<{key}};
    nonce_arr = {<<{nonce}};

    for (int i = 0; i < addr_width; i++) begin
      sram_addr[i] = addr[addr_lsb + i];
    end

    // Calculate the scrambled address
    scrambled_addr = sram_scrambler_pkg::encrypt_sram_addr(sram_addr, addr_width, nonce_arr);

    // Construct bus representation of the address
    for (int i = 0; i < addr_lsb; i++) begin
      bus_addr[i] = addr[i];
    end
    for (int i = 0; i < addr_width; i++) begin
      bus_addr[addr_lsb + i] = scrambled_addr[i];
    end

    // Read memory and return the decrypted data
    rdata = read32(bus_addr);
    rdata_arr = {<<{rdata}};
    rdata_arr = sram_scrambler_pkg::decrypt_sram_data(
        rdata_arr, 32, sram_addr, addr_width, key_arr, nonce_arr
    );
    rdata = {<<{rdata_arr}};
    return rdata;

  endfunction

  virtual function logic [63:0] sram_encrypt_read64(logic [bus_params_pkg::BUS_AW-1:0] addr,
                                                    logic [SRAM_KEY_WIDTH-1:0]         key,
                                                    logic [SRAM_BLOCK_WIDTH-1:0]       nonce);
    logic [bus_params_pkg::BUS_AW-1:0] bus_addr = '0;
    logic [63:0]                       rdata = '0;

    logic rdata_arr     [] = new[64];
    logic scrambled_addr[] = new[addr_width];
    logic sram_addr     [] = new[addr_width];
    logic key_arr       [] = new[SRAM_KEY_WIDTH];
    logic nonce_arr     [] = new[SRAM_BLOCK_WIDTH];

    key_arr   = {<<{key}};
    nonce_arr = {<<{nonce}};

    for (int i = 0; i < addr_width; i++) begin
      sram_addr[i] = addr[addr_lsb + i];
    end

    // Calculate the scrambled address
    scrambled_addr = sram_scrambler_pkg::encrypt_sram_addr(sram_addr, addr_width, nonce_arr);

    // Construct bus representation of the address
    for (int i = 0; i < addr_lsb; i++) begin
      bus_addr[i] = addr[i];
    end
    for (int i = 0; i < addr_width; i++) begin
      bus_addr[addr_lsb + i] = scrambled_addr[i];
    end

    // Read memory and return the decrypted data
    rdata = read64(bus_addr);
    rdata_arr = {<<{rdata}};
    rdata_arr = sram_scrambler_pkg::decrypt_sram_data(
        rdata_arr, 64, sram_addr, addr_width, key_arr, nonce_arr
    );
    rdata = {<<{rdata_arr}};
    return rdata;

  endfunction

  virtual function void sram_encrypt_write8(logic [bus_params_pkg::BUS_AW-1:0] addr,
                                            logic [7:0]                        data,
                                            logic [SRAM_KEY_WIDTH-1:0]         key,
                                            logic [SRAM_BLOCK_WIDTH-1:0]       nonce);
    logic [bus_params_pkg::BUS_AW-1:0] bus_addr = '0;
    logic [7:0]                        scrambled_data;

    logic wdata_arr      [] = new[8];
    logic scrambled_addr [] = new[addr_width];
    logic sram_addr      [] = new[addr_width];
    logic key_arr        [] = new[SRAM_KEY_WIDTH];
    logic nonce_arr      [] = new[SRAM_BLOCK_WIDTH];

    key_arr   = {<<{key}};
    nonce_arr = {<<{nonce}};

    for (int i = 0; i < addr_width; i++) begin
      sram_addr[i] = addr[addr_lsb + i];
    end

    // Calculate the scrambled address
    scrambled_addr = sram_scrambler_pkg::encrypt_sram_addr(sram_addr, addr_width, nonce_arr);

    // Calculate the scrambled data
    wdata_arr = {<<{data}};
    wdata_arr = sram_scrambler_pkg::encrypt_sram_data(
        wdata_arr, 8, sram_addr, addr_width, key_arr, nonce_arr
    );
    scrambled_data = {<<{wdata_arr}};

    // Construct bus representation of the address
    for (int i = 0; i < addr_lsb; i++) begin
      bus_addr[i] = addr[i];
    end
    for (int i = 0; i < addr_width; i++) begin
      bus_addr[addr_lsb + i] = scrambled_addr[i];
    end

    // Write the scrambled data to memory
    write8(bus_addr, scrambled_data);
  endfunction

  virtual function void sram_encrypt_write16(logic [bus_params_pkg::BUS_AW-1:0] addr,
                                             logic [15:0]                       data,
                                             logic [SRAM_KEY_WIDTH-1:0]         key,
                                             logic [SRAM_BLOCK_WIDTH-1:0]       nonce);
    logic [bus_params_pkg::BUS_AW-1:0] bus_addr = '0;
    logic [15:0]                       scrambled_data;

    logic wdata_arr      [] = new[16];
    logic scrambled_addr [] = new[addr_width];
    logic sram_addr      [] = new[addr_width];
    logic key_arr        [] = new[SRAM_KEY_WIDTH];
    logic nonce_arr      [] = new[SRAM_BLOCK_WIDTH];

    key_arr   = {<<{key}};
    nonce_arr = {<<{nonce}};

    for (int i = 0; i < addr_width; i++) begin
      sram_addr[i] = addr[addr_lsb + i];
    end

    // Calculate the scrambled address
    scrambled_addr = sram_scrambler_pkg::encrypt_sram_addr(sram_addr, addr_width, nonce_arr);

    // Calculate the scrambled data
    wdata_arr = {<<{data}};
    wdata_arr = sram_scrambler_pkg::encrypt_sram_data(
        wdata_arr, 16, sram_addr, addr_width, key_arr, nonce_arr
    );
    scrambled_data = {<<{wdata_arr}};

    // Construct bus representation of the address
    for (int i = 0; i < addr_lsb; i++) begin
      bus_addr[i] = addr[i];
    end
    for (int i = 0; i < addr_width; i++) begin
      bus_addr[addr_lsb + i] = scrambled_addr[i];
    end

    // Write the scrambled data to memory
    write16(bus_addr, scrambled_data);
  endfunction

  virtual function void sram_encrypt_write32(logic [bus_params_pkg::BUS_AW-1:0] addr,
                                             logic [31:0]                       data,
                                             logic [SRAM_KEY_WIDTH-1:0]         key,
                                             logic [SRAM_BLOCK_WIDTH-1:0]       nonce);
    logic [bus_params_pkg::BUS_AW-1:0] bus_addr = '0;
    logic [31:0]                       scrambled_data;

    logic wdata_arr      [] = new[32];
    logic scrambled_addr [] = new[addr_width];
    logic sram_addr      [] = new[addr_width];
    logic key_arr        [] = new[SRAM_KEY_WIDTH];
    logic nonce_arr      [] = new[SRAM_BLOCK_WIDTH];

    key_arr   = {<<{key}};
    nonce_arr = {<<{nonce}};

    for (int i = 0; i < addr_width; i++) begin
      sram_addr[i] = addr[addr_lsb + i];
    end

    // Calculate the scrambled address
    scrambled_addr = sram_scrambler_pkg::encrypt_sram_addr(sram_addr, addr_width, nonce_arr);

    // Calculate the scrambled data
    wdata_arr = {<<{data}};
    wdata_arr = sram_scrambler_pkg::encrypt_sram_data(
        wdata_arr, 32, sram_addr, addr_width, key_arr, nonce_arr
    );
    scrambled_data = {<<{wdata_arr}};

    // Construct bus representation of the address
    for (int i = 0; i < addr_lsb; i++) begin
      bus_addr[i] = addr[i];
    end
    for (int i = 0; i < addr_width; i++) begin
      bus_addr[addr_lsb + i] = scrambled_addr[i];
    end

    // Write the scrambled data to memory
    write32(bus_addr, scrambled_data);
  endfunction

  virtual function void sram_encrypt_write64(logic [bus_params_pkg::BUS_AW-1:0] addr,
                                             logic [63:0]                       data,
                                             logic [SRAM_KEY_WIDTH-1:0]         key,
                                             logic [SRAM_BLOCK_WIDTH-1:0]       nonce);
    logic [bus_params_pkg::BUS_AW-1:0] bus_addr = '0;
    logic [63:0]                       scrambled_data;

    logic wdata_arr      [] = new[64];
    logic scrambled_addr [] = new[addr_width];
    logic sram_addr      [] = new[addr_width];
    logic key_arr        [] = new[SRAM_KEY_WIDTH];
    logic nonce_arr      [] = new[SRAM_BLOCK_WIDTH];

    key_arr   = {<<{key}};
    nonce_arr = {<<{nonce}};

    for (int i = 0; i < addr_width; i++) begin
      sram_addr[i] = addr[addr_lsb + i];
    end

    // Calculate the scrambled address
    scrambled_addr = sram_scrambler_pkg::encrypt_sram_addr(sram_addr, addr_width, nonce_arr);

    // Calculate the scrambled data
    wdata_arr = {<<{data}};
    wdata_arr = sram_scrambler_pkg::encrypt_sram_data(
        wdata_arr, 64, sram_addr, addr_width, key_arr, nonce_arr
    );
    scrambled_data = {<<{wdata_arr}};

    // Construct bus representation of the address
    for (int i = 0; i < addr_lsb; i++) begin
      bus_addr[i] = addr[i];
    end
    for (int i = 0; i < addr_width; i++) begin
      bus_addr[addr_lsb + i] = scrambled_addr[i];
    end

    // Write the scrambled data to memory
    write64(bus_addr, scrambled_data);
  endfunction

  // Wrapper function for encrypted ROM reads.
  //
  // The data decoding is different from SRAM, but most of the underlying SRAM functions are reused
  // Also note that this function returns the raw data rather than data + syndrome + error because
  // the rom_ctrl testbench needs this for checking
  virtual function bit [39:0] rom_encrypt_read32(bit [bus_params_pkg::BUS_AW-1:0] addr,
                                                 logic [SRAM_KEY_WIDTH-1:0]       key,
                                                 logic [SRAM_BLOCK_WIDTH-1:0]     nonce,
                                                 bit                              unscramble_data);

    logic [bus_params_pkg::BUS_AW-1:0] mem_addr = '0;
    logic [39:0]                       data = '0;

    logic addr_arr      [] = new[addr_width];
    logic scrambled_addr[] = new[addr_width];
    logic data_arr      [] = new[40];
    logic key_arr       [] = new[SRAM_KEY_WIDTH];
    logic nonce_arr     [] = new[SRAM_BLOCK_WIDTH];
    logic keystream     [] = new[SRAM_BLOCK_WIDTH];
    logic zero_key      [] = new[40];

    key_arr   = {<<{key}};
    nonce_arr = {<<{nonce}};

    for (int i = 0; i < addr_width; i++) begin
      addr_arr[i] = addr[addr_lsb + i];
    end

    // Calculate the scrambled address
    scrambled_addr = sram_scrambler_pkg::encrypt_sram_addr(addr_arr, addr_width, nonce_arr);

    for (int i = 0; i < addr_width; i++) begin
      mem_addr[i] = scrambled_addr[i];
    end

    // Read memory and get the encrypted data
    if (!check_addr_valid(mem_addr << addr_lsb)) begin
      return 'x;
    end

    // 39-bit memory word includes 32-bit data + 7-bit ECC
    data = read(mem_addr << addr_lsb);

    if (!unscramble_data) begin
      return data;
    end

    data_arr = {<<{data}};

    // Generate the keystream
    keystream = sram_scrambler_pkg::gen_keystream(addr_arr, addr_width, key_arr, nonce_arr);

    for (int i = 0; i < 40; i++) begin
      zero_key[i] = '0;
    end

    data_arr = sram_scrambler_pkg::sp_decrypt(data_arr, 40, zero_key);
    for (int i = 0; i < 40; i++) begin
      data[i] = data_arr[i] ^ keystream[i];
    end

    return data;
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

  // A helper function that splits a given number randomly into a pair.
  virtual function int_pair_t rand_split(uint32_t num);
    rand_split.x = $urandom_range(0, num);
    rand_split.y = num - rand_split.x;
  endfunction

  virtual function uvm_hdl_data_t inject_errors(uvm_hdl_data_t data, uint32_t inject_num_errors);
    uvm_hdl_data_t err_mask;
    `DV_CHECK_STD_RANDOMIZE_WITH_FATAL(err_mask,
                                       $countones(err_mask) == inject_num_errors;
                                       (err_mask >> width) == '0;)
    return data ^ err_mask;
  endfunction

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
