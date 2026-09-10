// Copyright lowRISC contributors (OpenTitan project).
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

  // If set to a value different to "", a path to the tile memory, based on path and tiling_path,
  // is used to perform the backdoor access
  protected string tiling_path;

  // Format string to provide the tiling suffix. Must contain a %d for the tile and %s for the
  // tiling_path path. Can be overwritten for different hierarchies, ie., when DFT is enabled.
  protected string tiling_suffix_fmt_str;

  // The depth of the memory.
  protected uint32_t depth;

  // The depth of a single SRAM tile.
  protected uint32_t tile_depth;

  // Number of logical (row_data_t-sized) words folded into each physical HDL row of a single
  // tile's storage array. 1 (the default) means no folding: one physical row per logical word.
  protected uint32_t words_per_row;

  // Number of macro instances that jointly form one logical word by bit-slicing it (each instance
  // contributing an equal-sized slice, read/written on every access), rather than each covering
  // the whole word. 1 (the default) means no bit-slicing.
  protected uint32_t num_bit_slices;

  // Analogous to `tiling_path`/`tiling_suffix_fmt_str` above, but for selecting a bit slice's
  // instance (which should be less than num_bit_slices) instead of an address-based tile.
  protected string bit_slice_tiling_path;
  protected string bit_slice_tiling_suffix_fmt_str;

  // The logical width of the memory in bits, not including extra bits added by the row adapter.
  protected uint32_t width;

  // The number of subword entries in the whole memory
  protected uint32_t num_entries;

  // Indicates the error detection scheme implemented for this memory.
  protected err_detection_e err_detection_scheme = ErrDetectionNone;

  // Adapter to access the underlying memory organization
  // Integrators can provide a custom row adapter for their SRAM primitives
  protected mem_bkdr_util_row_adapter row_adapter;

  // Convenience macro to check if ECC / parity is enabled.
  `define HAS_ECC (!(err_detection_scheme inside {ErrDetectionNone, ParityEven, ParityOdd}))
  `define HAS_PARITY (err_detection_scheme inside {ParityEven, ParityOdd})

  // Other memory specifics derived from the settings above.
  protected uint32_t data_width;  // ignoring ECC bits
  protected uint32_t byte_width;
  protected uint32_t bytes_per_word;  // addressable bytes
  protected uint32_t size_bytes;  // addressable bytes
  protected uint32_t addr_lsb;
  protected uint32_t addr_width;
  protected uint32_t byte_addr_width;

  // Address range of this memory in the system address map.
  protected addr_range_t addr_range;

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

  // Number of PRINCE half rounds for scrambling, can be [1..5].
  protected uint32_t num_prince_rounds_half;

  // Construct an instance called name.
  //
  // Required arguments:
  //
  //   path:                 A hierarchical HDL path to the memory.
  //
  //   depth:                The number memory rows.
  //
  //   n_bits:               The total size of the memory in bits.
  //
  //   err_detection_scheme  The error detection scheme that is implemented for the memory.
  //
  // Optional arguments:
  //
  //  row_adapter              Adapter to access the internal row of a memory. Integrators can
  //                           provide a custom adapter for a different memory architecture.
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
  //  tiling_suffix_fmt_str    Format string to provide the tiling suffix. Must contain a %d for the
  //                           tile and %s for the tiling_path path. If the testbench uses a
  //                           different path, i.e., in a DFT environment, you can pass a different
  //                           format string to construct the tiling path.
  //
  //  tile_depth               The number of rows of a single tle. By default, this is the entire
  //                           memory.
  //
  //  num_bit_slices           Number of macro instances that jointly form one logical word by
  //                           bit-slicing it, rather than each covering the whole word (as opposed
  //                           to tiling, above, where different addresses map to different
  //                           instances, here every instance is read/written on every access, each
  //                           contributing an equal-sized slice of the word). 1 (the default)
  //                           means no bit-slicing: the whole word comes from a single access, as
  //                           `tiling_path`/`tile_depth` alone already describe.
  //
  //  bit_slice_tiling_path/
  //  bit_slice_tiling_suffix_fmt_str  Analogous to `tiling_path`/`tiling_suffix_fmt_str`, but
  //                           selecting a bit slice's instance (which should be less than
  //                           num_bit_slices) instead of an address-based tile.
  function new(string name = "", string path, int unsigned depth,
               longint unsigned n_bits, err_detection_e err_detection_scheme,
               mem_bkdr_util_row_adapter row_adapter = null,
               uint32_t num_prince_rounds_half = 3,
               uint32_t extra_bits_per_subword = 0, uint32_t system_base_addr = 0,
               string tiling_path = "", string tiling_suffix_fmt_str = ".gen_ram_inst[%0d].%s",
               uint32_t tile_depth = depth, uint32_t words_per_row = 1,
               uint32_t num_bit_slices = 1, string bit_slice_tiling_path = "",
               string bit_slice_tiling_suffix_fmt_str = ".gen_ram_inst[%0d].%s");
    super.new(name);
    `DV_CHECK_FATAL(!(n_bits % depth), "n_bits must be divisible by depth.")
    `DV_CHECK_FATAL(!(tile_depth % words_per_row),
                    "tile_depth must be a whole number of physical rows")
    `DV_CHECK_FATAL(!((n_bits / depth) % num_bit_slices),
                    "the logical word width must be a whole number of bit slices")
    this.words_per_row                   = words_per_row;
    this.num_bit_slices                  = num_bit_slices;
    this.bit_slice_tiling_path           = bit_slice_tiling_path;
    this.bit_slice_tiling_suffix_fmt_str = bit_slice_tiling_suffix_fmt_str;

    if (row_adapter != null) begin
      this.row_adapter = row_adapter;
    end else begin
      this.row_adapter = new();
    end

    this.path                   = path;
    this.tiling_path            = tiling_path;
    this.depth                  = depth;
    this.tile_depth             = tile_depth;
    this.tiling_suffix_fmt_str  = tiling_suffix_fmt_str;
    this.width                  = (n_bits / depth) - this.row_adapter.get_num_extra_bits();
    this.err_detection_scheme   = err_detection_scheme;
    this.num_prince_rounds_half = num_prince_rounds_half;

    // Check if the inferred path to each tile (or the whole memory) really exist
    for (int i = 0; i < (depth + tile_depth - 1) / tile_depth; i++) begin
      string full_path = get_full_path(i);
      `DV_CHECK_FATAL(uvm_hdl_check_path(get_full_path(i)) == 1,
                      $sformatf("Hierarchical path %0s appears to be invalid.", full_path))
    end

    // Likewise, for each bit slice's instance.
    for (int unsigned i = 0; i < num_bit_slices; i++) begin
      string slice_path = get_bit_slice_path(i);
      `DV_CHECK_FATAL(uvm_hdl_check_path(slice_path) == 1,
                      $sformatf("Hierarchical path %0s appears to be invalid.", slice_path))
    end

    if (`HAS_ECC) begin
      import prim_secded_pkg::prim_secded_e;
      import prim_secded_pkg::get_ecc_data_width;
      import prim_secded_pkg::get_ecc_parity_width;

      prim_secded_e secded_eds = prim_secded_e'(err_detection_scheme);
      int non_ecc_bits_per_subword = get_ecc_data_width(secded_eds);
      int ecc_bits_per_subword = get_ecc_parity_width(secded_eds);
      int bits_per_subword = non_ecc_bits_per_subword + ecc_bits_per_subword +
                             extra_bits_per_subword;
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
      this.num_entries = depth * subwords_per_word;
    end else begin
      this.data_width = width;
      this.num_entries = depth;
    end

    byte_width = `HAS_PARITY ? 9 : 8;
    bytes_per_word = data_width / byte_width;
    `DV_CHECK_LE_FATAL(bytes_per_word, 64, "data width > 64 bytes is not supported")
    size_bytes = depth * bytes_per_word;
    addr_lsb   = $clog2(bytes_per_word);
    addr_width = $clog2(depth);
    byte_addr_width = addr_width + addr_lsb;
    addr_range.start_addr = system_base_addr;
    addr_range.end_addr = system_base_addr + size_bytes - 1;
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
            $sformatf("max_errors = %0d\n", max_errors),
            $sformatf("addr_range.start_addr = 0x%0h\n", addr_range.start_addr),
            $sformatf("addr_range.end_addr = 0x%0h\n", addr_range.end_addr)};
  endfunction

  function string get_path();
    return path;
  endfunction

  function string get_full_path(int unsigned tile);
    string base = get_path();
    string tile_suffix = "";

    `DV_CHECK_FATAL(tile > 0 -> tiling_path.len() > 0,
                    $sformatf("Positive tile index (%0d) with empty tiling path.", tile))

    if (tiling_path != "") begin
      tile_suffix = $sformatf(tiling_suffix_fmt_str, tile, tiling_path);
    end

    return {base, tile_suffix};
  endfunction

  // Analogous to `get_full_path()` above, but for a bit slice's instance instead of an
  // address-based tile.
  function string get_bit_slice_path(int unsigned slice);
    string base = get_path();
    string slice_suffix = "";

    if (slice > 0) begin
      `DV_CHECK_FATAL(bit_slice_tiling_path.len() > 0,
                      $sformatf("Positive bit slice index (%0d) with empty tiling path.", slice))
    end

    if (bit_slice_tiling_path != "") begin
      slice_suffix = $sformatf(bit_slice_tiling_suffix_fmt_str, slice, bit_slice_tiling_path);
    end

    return {base, slice_suffix};
  endfunction

  function uint32_t get_depth();
    return depth;
  endfunction

  function uint32_t get_tile_depth();
    return tile_depth;
  endfunction

  function uint32_t get_width();
    return width;
  endfunction

  function err_detection_e get_err_detection_scheme();
    return err_detection_scheme;
  endfunction

  function int get_num_prince_rounds_half();
    return num_prince_rounds_half;
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

  function bit is_valid_addr(int unsigned system_addr);
    return system_addr inside {[addr_range.start_addr:addr_range.end_addr]};
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

  // HDL path for the `row_width`-bit physical row at `tile_path[phys_row_index]`, shared by
  // `read_phys_row()`/`write_phys_row()` below.
  local function string get_phys_row_access_path(string tile_path, int unsigned phys_row_index,
                                                 int unsigned row_width);
    return $sformatf("%0s[%0d][%0d:0]", tile_path, phys_row_index, row_width - 1);
  endfunction

  // Reads the entire `row_width`-bit physical row at `tile_path[phys_row_index]` in one access,
  // rather than looping over `bits_per_backdoor_access`-sized chunks (broken for a row wider than
  // one chunk). `row_data_t`/`uvm_hdl_data_t` are `UVM_HDL_MAX_WIDTH` (1024) bits wide, enough for
  // one access.
  local function row_data_t read_phys_row(string tile_path, int unsigned phys_row_index,
                                          int unsigned row_width);
    uvm_hdl_data_t data;
    string         access_path = get_phys_row_access_path(tile_path, phys_row_index, row_width);
    if (!uvm_hdl_read(access_path, data)) begin
      `uvm_error(get_name(), $sformatf("Failed to access %0s with uvm_hdl_read.", access_path))
    end
    return row_data_t'(data);
  endfunction

  // Writes `data` (an entire `row_width`-bit physical row) at `tile_path[phys_row_index]`.
  local function void write_phys_row(string tile_path, int unsigned phys_row_index,
                                     row_data_t data, int unsigned row_width);
    string access_path = get_phys_row_access_path(tile_path, phys_row_index, row_width);
    if (!uvm_hdl_deposit(access_path, uvm_hdl_data_t'(data))) begin
      `uvm_error(get_name(), $sformatf("Failed to access %0s with uvm_hdl_deposit.", access_path))
    end
  endfunction

  // Maps bit `bit_idx` of word `word_idx` (out of `words_per_row` words folded into one row) to
  // its physical bit position within the row.
  //
  // For example, for `words_per_row == 2`, the bit vector `x0 x1 .. xN y0 y1 .. yN` (two logical
  // words, `x` and `y`) is stored interleaved as `x0 y0 x1 y1 .. xN yN`.
  local function uint32_t phys_row_bit_position(uint32_t bit_idx, uint32_t word_idx);
    return bit_idx * words_per_row + word_idx;
  endfunction

  // Read a `width`-bit logical word from physical row `rel_row_index` in the tile at `tile_path`.
  //
  // This row index is already relative to the tile (so any address-based tiling has already been
  // resolved by the caller). If the row contains multiple words (because `words_per_row` is
  // greater than 1), this function extracts just the requested word.
  local function row_data_t read_word(string tile_path, int unsigned rel_row_index,
                                      int unsigned width);
    int unsigned word_idx_in_row, phys_row_index, phys_row_width;
    row_data_t   phys_row, word_data;

    word_idx_in_row = rel_row_index % words_per_row;
    phys_row_index  = rel_row_index / words_per_row;
    phys_row_width  = width * words_per_row;

    phys_row  = read_phys_row(tile_path, phys_row_index, phys_row_width);
    word_data = '0;
    for (int unsigned k = 0; k < width; k++) begin
      word_data[k] = phys_row[phys_row_bit_position(k, word_idx_in_row)];
    end
    return word_data;
  endfunction

  // Read the memory row that contains the given address.
  //
  // addr is the byte address, starting at offset 0. Mask the upper address bits as needed before
  // invocation.
  //
  // Returns the entire width of the memory at the given address, including the ECC bits. The data
  // returned is 'raw' i.e. it includes the parity bits. It also does not de-scramble the data if
  // encryption is enabled.
  virtual function row_data_t read(bit [bus_params_pkg::BUS_AW-1:0] addr);
    int unsigned row_index, rel_row_index, row_width;
    row_data_t   word_data;

    if (!check_addr_valid(addr)) return 'x;

    // Convert addr to the index of the row (there are 2 ** addr_lsb items in each row)
    row_index = addr >> this.addr_lsb;
    rel_row_index = row_index % this.tile_depth;

    // The row itself contains this.width data bits plus (possibly) some extra bits, as defined by
    // the row adapter.
    row_width = this.width + this.row_adapter.get_num_extra_bits();

    if (num_bit_slices == 1) begin
      // Get an HDL path for tile that contains this row index.
      string tile_path = this.get_full_path(row_index / this.tile_depth);
      word_data = read_word(tile_path, rel_row_index, row_width);
    end else begin
      // Every bit slice's instance is read on every access. Each instance contributes an
      // equal-sized slice of the word (as opposed to tiling, where the address selects a single
      // instance).
      int unsigned slice_width = row_width / num_bit_slices;
      word_data = '0;
      for (int unsigned s = 0; s < num_bit_slices; s++) begin
        row_data_t slice_data = read_word(get_bit_slice_path(s), rel_row_index, slice_width);
        word_data |= slice_data << (s * slice_width);
      end
    end

    return this.row_adapter.decode_row(word_data);
  endfunction

  // Convenience macro to check the addr for each flavor of read and write functions.
  `define _ACCESS_CHECKS(_ADDR, _DW) \
    `DV_CHECK_EQ_FATAL(_ADDR % (_DW / 8), 0, $sformatf("addr 0x%0h not ``_DW``-bit aligned", _ADDR))

  // Read a single byte at specified address.
  //
  // The data returned does not include the parity bits.
  virtual function logic [7:0] read8(bit [bus_params_pkg::BUS_AW-1:0] addr);
    row_data_t data = read(addr);
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

  // Returns data with correctly computed ECC.
  virtual function uvm_hdl_data_t get_ecc_computed_data(uvm_hdl_data_t data);
    case (err_detection_scheme)
      ErrDetectionNone: ;
      Ecc_22_16: begin
        data = prim_secded_pkg::prim_secded_22_16_enc(data[15:0]);
      end
      EccHamming_22_16: begin
        data = prim_secded_pkg::prim_secded_hamming_22_16_enc(data[15:0]);
      end
      Ecc_39_32: begin
        data = prim_secded_pkg::prim_secded_39_32_enc(data[31:0]);
      end
      EccHamming_39_32: begin
        data = prim_secded_pkg::prim_secded_hamming_39_32_enc(data[31:0]);
      end
      Ecc_72_64: begin
        data = prim_secded_pkg::prim_secded_72_64_enc(data[63:0]);
      end
      EccHamming_72_64: begin
        data = prim_secded_pkg::prim_secded_hamming_72_64_enc(data[63:0]);
      end
      EccHamming_76_68: begin
        data = prim_secded_pkg::prim_secded_hamming_76_68_enc(data[67:0]);
      end
      EccInv_22_16: begin
        data = prim_secded_pkg::prim_secded_inv_22_16_enc(data[15:0]);
      end
      EccInvHamming_22_16: begin
        data = prim_secded_pkg::prim_secded_inv_hamming_22_16_enc(data[15:0]);
      end
      EccInv_39_32: begin
        data = prim_secded_pkg::prim_secded_inv_39_32_enc(data[31:0]);
      end
      EccInvHamming_39_32: begin
        data = prim_secded_pkg::prim_secded_inv_hamming_39_32_enc(data[31:0]);
      end
      EccInv_72_64: begin
        data = prim_secded_pkg::prim_secded_inv_72_64_enc(data[63:0]);
      end
      EccInvHamming_72_64: begin
        data = prim_secded_pkg::prim_secded_inv_hamming_72_64_enc(data[63:0]);
      end
      EccInvHamming_76_68: begin
        data = prim_secded_pkg::prim_secded_inv_hamming_76_68_enc(data[67:0]);
      end
      default: begin
        `uvm_fatal(`gfn, $sformatf("ECC scheme %0s is unsupported.", err_detection_scheme))
      end
    endcase
    return data;
  endfunction

  // Write a `width`-bit logical word `data` to physical row `rel_row_index` in the tile at
  // `tile_path`.
  //
  // This row index is already relative to the tile (so any address-based tiling has already been
  // resolved by the caller). If the row holds multiple words (`words_per_row > 1`), this is a
  // read-modify-write of the whole physical row, so the other logical words already in it are
  // preserved; if not (`words_per_row == 1`), the row is written directly without reading it first.
  local function void write_word(string tile_path, int unsigned rel_row_index,
                                 int unsigned width, row_data_t data);
    int unsigned word_idx_in_row, phys_row_index, phys_row_width;
    row_data_t   phys_row;

    word_idx_in_row = rel_row_index % words_per_row;
    phys_row_index  = rel_row_index / words_per_row;
    phys_row_width  = width * words_per_row;

    phys_row = (words_per_row == 1) ? '0 : read_phys_row(tile_path, phys_row_index, phys_row_width);
    for (int unsigned k = 0; k < width; k++) begin
      phys_row[phys_row_bit_position(k, word_idx_in_row)] = data[k];
    end
    write_phys_row(tile_path, phys_row_index, phys_row, phys_row_width);
  endfunction

  // Write the entire word at the given address with the specified data.
  //
  // addr is the byte address starting at offset 0. Mask the upper address bits as needed before
  // invocation.
  //
  // Updates the entire width of the memory at the given address, including the ECC bits.
  virtual function void write(bit [bus_params_pkg::BUS_AW-1:0] addr, row_data_t data);
    row_data_t   encoded_row;
    int unsigned row_index, rel_row_index, row_width;

    if (!check_addr_valid(addr)) return;

    // Convert addr to the row_index of the row (there are 2 ** addr_lsb items in each row)
    row_index = addr >> this.addr_lsb;
    rel_row_index = row_index % this.tile_depth;

    // The row itself contains this.width data bits plus (possibly) some extra bits, as defined by
    // the row adapter.
    row_width = this.width + this.row_adapter.get_num_extra_bits();

    encoded_row = this.row_adapter.encode_row(data);

    if (num_bit_slices == 1) begin
      // Get an HDL path for tile that contains this row index.
      string tile_path = this.get_full_path(row_index / this.tile_depth);
      write_word(tile_path, rel_row_index, row_width, encoded_row);
    end else begin
      // Every bit slice's instance is written on every access. Each instance gets an equal-sized
      // slice of the word (as opposed to tiling, where the address selects a single instance).
      int unsigned slice_width = row_width / num_bit_slices;
      row_data_t   slice_mask  = (row_data_t'(1) << slice_width) - 1;
      for (int unsigned s = 0; s < num_bit_slices; s++) begin
        row_data_t slice_data = (encoded_row >> (s * slice_width)) & slice_mask;
        write_word(get_bit_slice_path(s), rel_row_index, slice_width, slice_data);
      end
    end

    `uvm_info(`gfn, $sformatf("Backdoor write: addr 0x%0h, data 0x%0h", addr, data), UVM_HIGH)
  endfunction

  // Write a single byte at specified address.
  //
  // Does a read-modify-write on the whole word. It updates the byte at the given address and
  // computes the parity and ECC bits as applicable.
  virtual function void write8(bit [bus_params_pkg::BUS_AW-1:0] addr, logic [7:0] data);
    row_data_t rw_data;
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

    // Update the byte index with the new value.
    rw_data[byte_idx * 8 +: 8] = data;

    // Compute & set the new ECC value.
    rw_data = get_ecc_computed_data(rw_data);

    // Write the whole array back to the memory.
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
    row_data_t rw_data;
    `_ACCESS_CHECKS(addr, 32) // this is essentially an aligned 32bit access.
    if (!check_addr_valid(addr)) return;
    // Perform a read-modify-write to access the underlying memory architecture
    rw_data = read(addr);
    rw_data = row_adapter.write_row_data_39b(addr, data, rw_data);
    // Note the write function takes care of interleaving, if used.
    write(addr, rw_data);
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
    write64(addr + 8, data[127:64]);
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
    row_data_t data;
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
    row_data_t data;
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
    row_data_t data;
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

  // Returns 1 if the memory is composed of more than one tile.
  //
  // The `$readmemh` and `$writememh` system tasks invoked by `MEM_BKDR_UTIL_FILE_OP` can only
  // target a single unpacked array, so tiled memories need the file operations below instead.
  virtual function bit is_tiled();
    return tile_depth < depth;
  endfunction

  // Returns 1 if the memory is bit-sliced across more than one macro instance. Like a tiled
  // memory, this can't be targeted by a single `$readmemh`/`$writememh` either (each instance only
  // holds part of every word), so `MEM_BKDR_UTIL_FILE_OP` should not be used for it.
  virtual function bit is_bit_sliced();
    return num_bit_slices > 1;
  endfunction

  // Load the memory from a VMEM file through the tile-aware `write()`.
  //
  // `$readmemh` cannot target a tiled memory, because its tiles are separate arrays, but it can
  // fill a temporary array of the same depth. Parsing the file therefore stays with the system
  // task, exactly as for an untiled memory, and only the deposit is done word by word.
  protected virtual task load_mem_from_file_tiled(string file);
    // Words that the file does not cover keep this value and are not written, so that a partial
    // image does not clobber the rest of the memory.
    row_data_t unset = 'x;
    row_data_t mem_words[] = new[depth];

    foreach (mem_words[i]) mem_words[i] = unset;

    `uvm_info(`gfn, $sformatf("Loading mem from file:\n%0s", file), UVM_LOW)
    $readmemh(file, mem_words);

    foreach (mem_words[i]) begin
      if (mem_words[i] !== unset) write(i * bytes_per_word, mem_words[i]);
    end
  endtask

  // Write the memory to a VMEM file one word at a time, through the tile-aware `read()`.
  //
  // `$writememh` cannot serve here either: besides not being able to target a tiled memory, it
  // would write the full width of `row_data_t` rather than the width of the memory.
  protected virtual function void write_mem_to_file_tiled(string file);
    int    fh;
    string word;
    int    num_digits = (width + 3) / 4;

    fh = $fopen(file, "w");
    `DV_CHECK_FATAL(fh != 0, $sformatf("Could not open %0s for writing.", file))

    for (int i = 0; i < depth; i++) begin
      // `read()` returns a full `row_data_t`, and a field width in a format specifier pads rather
      // than truncates, so keep the low-order digits of the formatted value to get one word of the
      // memory width, like `$writememh` writes.
      word = $sformatf("%h", read(i * bytes_per_word));
      $fwrite(fh, "%0s\n", word.substr(word.len() - num_digits, word.len() - 1));
    end

    $fclose(fh);
  endfunction

  // load mem from file
  virtual task load_mem_from_file(string file, bit recompute_ecc = 0);
    check_file(file, "r");
    if (is_tiled()) begin
      load_mem_from_file_tiled(file);
    end else begin
      this.file = file;
      ->readmemh_event;
    end
    // The delay below avoids a race condition between this mem backdoor load and a subsequent
    // backdoor write to a particular location.
    #0;

    // Recompute ECC if indicated (this allows to load an image that does not have ECC present).
    if (recompute_ecc) begin
      case (err_detection_scheme)
        Ecc_22_16, EccHamming_22_16, EccInv_22_16, EccInvHamming_22_16: begin
          for (int addr = 0; addr < depth; addr += bytes_per_word) begin
            write16(addr, read(addr));
          end
        end
        Ecc_39_32, EccHamming_39_32, EccInv_39_32, EccInvHamming_39_32: begin
          for (int addr = 0; addr < depth; addr += bytes_per_word) begin
            write32(addr, read(addr));
          end
        end
        Ecc_72_64, EccHamming_72_64, EccInv_72_64, EccInvHamming_72_64: begin
          for (int addr = 0; addr < depth; addr += bytes_per_word) begin
            write64(addr, read(addr));
          end
        end
        // Nothing to recompute
        default: ;
      endcase
    end
  endtask

  // save mem contents to file
  virtual function void write_mem_to_file(string file);
    check_file(file, "w");
    if (is_tiled()) begin
      write_mem_to_file_tiled(file);
    end else begin
      this.file = file;
      ->writememh_event;
    end
  endfunction

  // Print the contents of the memory.
  virtual function void print_mem();
    `uvm_info(`gfn, "Print memory", UVM_LOW)
    for (int i = 0; i < depth; i++) begin
      row_data_t data = read(i * bytes_per_word);
      `uvm_info(`gfn, $sformatf("mem[%0d] = 0x%0h", i, data), UVM_LOW)
    end
  endfunction

  // Clear the memory to all 0s.
  virtual function void clear_mem();
    `uvm_info(`gfn, "Clear memory", UVM_LOW)
    for (int i = 0; i < depth; i++) begin
      row_data_t data = '{default:0};
      write(i * bytes_per_word, data);
    end
  endfunction

  // Set the memory to all 1s.
  virtual function void set_mem();
    `uvm_info(`gfn, "Set memory", UVM_LOW)
    for (int i = 0; i < depth; i++) begin
      row_data_t data = '{default:1};
      write(i * bytes_per_word, data);
    end
  endfunction

  // Randomize the memory with correct ECC.
  virtual function void randomize_mem();
    `uvm_info(`gfn, "Randomizing mem contents", UVM_LOW)
    for (int i = 0; i < depth; i++) begin
      row_data_t data;
      `DV_CHECK_STD_RANDOMIZE_FATAL(data, "Randomization failed!", path)
      if (`HAS_PARITY) begin
        row_data_t raw_data = data;
        for (int byte_idx = 0; byte_idx < bytes_per_word; byte_idx++) begin
          bit raw_byte = raw_data[byte_idx * 8 +: 8];
          bit parity = (err_detection_scheme == ParityOdd) ? ~(^raw_byte) : (^raw_byte);
          data[byte_idx * 9 +: 9] = {parity, raw_byte};
        end
      end else begin
        data = get_ecc_computed_data(data);
      end
      write(i * bytes_per_word, data);
    end
  endfunction

  // Invalidate the memory.
  virtual function void invalidate_mem();
    `uvm_info(`gfn, "Invalidating (Xs) mem contents", UVM_LOW)
    for (int i = 0; i < depth; i++) begin
      row_data_t data;
      write(i * bytes_per_word, data);
    end
  endfunction

  // Inject ECC or parity errors to the memory word at the given address.
  virtual function void inject_errors(bit [bus_params_pkg::BUS_AW-1:0] addr,
                                      uint32_t inject_num_errors);
    row_data_t rw_data, err_mask;
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
// inst is the mem_bkdr_util instance created in the testbench module.
// path is the raw path to the memory element in the design.
//
// This serves a memory that is a single unpacked array. A tiled memory, for which
// mem_bkdr_util::is_tiled() returns 1, is handled inside the class instead and never triggers the
// events below, so the testbench does not need to invoke this macro for it.
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
