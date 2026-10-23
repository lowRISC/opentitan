// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// mem_bkdr_util specialization for the OTP region of the RRAM data array.
//
// otp_ctrl's macro interface didn't change when otp_macro was swapped for rram_ctrl, so
// otp_ctrl_reg_pkg's partition offsets (e.g. LcStateOffset) still apply as-is.
// RRAM stores OTP in the tail pages of the same array as RramData (OtpStartPage).
// This bkdr_util implementation targets the same RramData array as the rram_bkdr_loader but only
// writing to the last segment of it.
// It write/reads data, and maintains the OTP integrity page by storing the Hamming(72,64) integrity
// word in it.

class rram_ctrl_otp_bkdr_util extends mem_bkdr_util;

  // Byte offsets into the shared array where OTP data and its integrity page start.
  // Mirror OtpStartAddr / OtpIntgStartAddr in rram_ctrl_otp.sv.
  localparam int unsigned OtpDataByteOffset =
      (rram_ctrl_pkg::OtpStartPage + 1) << (rram_ctrl_pkg::BusAddrByteW - rram_ctrl_pkg::PageW);
  localparam int unsigned OtpIntgByteOffset =
      rram_ctrl_pkg::OtpStartPage << (rram_ctrl_pkg::BusAddrByteW - rram_ctrl_pkg::PageW);

  // Integrity rows actually written by update_integrity(), keyed by byte address.
  // Lets load_mem_from_file() skip verifying unused padding rows it never computed.
  protected bit touched_intg_row[bit [bus_params_pkg::BUS_AW-1:0]];

  // path/depth/n_bits cover the whole RRAM data array, same as RramData/RramInfo.
  // This shares the same physical array as RramData, and so the same rram_macro inline ECC,
  // handled explicitly by this class's own read()/write() below.
  // OTP's own, separate software integrity scheme in update_integrity() is layered on top of
  // that, not a replacement for it.
  // err_detection_scheme is always ErrDetectionNone.
  // OTP's integrity is handled in update_integrity() below instead of via a generic ECC scheme.
  function new(string name = "", string path, int unsigned depth,
               longint unsigned n_bits, err_detection_e err_detection_scheme,
               mem_bkdr_util_row_adapter row_adapter = null,
               int num_prince_rounds_half = 3,
               int extra_bits_per_subword = 0, int unsigned system_base_addr = 0);
    super.new(name, path, depth, n_bits, err_detection_scheme, row_adapter,
              num_prince_rounds_half, extra_bits_per_subword, system_base_addr);

    `DV_CHECK_EQ_FATAL(err_detection_scheme, mem_bkdr_util_pkg::ErrDetectionNone,
                        {"OTP integrity is handled explicitly by this class, not via a generic ",
                         "ECC scheme."})

    // Re-derive the fields `mem_bkdr_util::new()` computed from `n_bits`/`depth`, based on the
    // 128-bit logical word size instead of the physical 144-bit row width.
    // See `rram_ctrl_bkdr_util::new()` for why.
    this.width                 = EmulDataWidth;
    this.data_width            = EmulDataWidth;
    this.bytes_per_word        = EmulDataWidth / 8;
    this.addr_lsb              = $clog2(this.bytes_per_word);
    this.byte_addr_width       = this.addr_width + this.addr_lsb;
    this.size_bytes            = this.depth * this.bytes_per_word;
    this.addr_range.start_addr = system_base_addr;
    this.addr_range.end_addr   = system_base_addr + this.size_bytes - 1;
    this.max_errors            = EmulDataWidth;
  endfunction

  // read8/16/32/64/128 all funnel through here.
  virtual function row_data_t read(bit [bus_params_pkg::BUS_AW-1:0] addr);
    bit [bus_params_pkg::BUS_AW-1:0] abs_addr = addr + OtpDataByteOffset;
    return row_data_t'(rram_row_read($sformatf("%0s[%0d]", get_full_path(0),
                                                abs_addr >> this.addr_lsb)));
  endfunction

  // write8/16/32/64/128 funnel through here.
  virtual function void write(bit [bus_params_pkg::BUS_AW-1:0] addr, row_data_t data);
    bit [bus_params_pkg::BUS_AW-1:0] abs_addr  = addr + OtpDataByteOffset;
    int unsigned                     row_index = abs_addr >> this.addr_lsb;
    string                           row_path  = $sformatf("%0s[%0d]", get_full_path(0),
                                                             row_index);
    rram_row_write(row_path, data[EmulDataWidth-1:0]);
    update_integrity(addr, data);
  endfunction

  // Corrupts the data word or its integrity byte, chosen at random. See inject_intg_error().
  virtual function void inject_errors(bit [bus_params_pkg::BUS_AW-1:0] addr,
                                      uint32_t inject_num_errors);
    bit data_word;
    `DV_CHECK_STD_RANDOMIZE_FATAL(data_word)
    inject_intg_error(addr, inject_num_errors, data_word);
  endfunction

  // Flips `inject_num_errors` bits in the 64b chunk that holds `addr` if `data_word` is set, or in
  // its integrity byte otherwise. rram_ctrl_otp checks only that pair when reading `addr`; one or
  // two flipped bits always make them mismatch.
  virtual function void inject_intg_error(bit [bus_params_pkg::BUS_AW-1:0] addr,
                                          uint32_t inject_num_errors, bit data_word);
    localparam int unsigned ChunkBits = rram_ctrl_pkg::OtpIntgDataWidth;
    int unsigned byte_addr, row_addr, field_lsb, field_bits;
    string row_path;
    bit [EmulDataWidth-1:0] rw_data, err_mask, field_mask;

    // Checking `addr` alone first keeps the sum below from wrapping onto a valid row.
    if (!check_addr_valid(addr) || !check_addr_valid(addr + OtpDataByteOffset)) return;
    if (data_word) begin
      byte_addr  = addr + OtpDataByteOffset;
      field_bits = ChunkBits;
    end else begin
      byte_addr  = get_intg_byte_addr(addr);
      field_bits = rram_ctrl_pkg::OtpIntgWidth;
    end
    row_addr  = (byte_addr / this.bytes_per_word) * this.bytes_per_word;
    field_lsb = ((byte_addr - row_addr) / (field_bits / 8)) * field_bits;
    `DV_CHECK_LE_FATAL(inject_num_errors, field_bits)
    field_mask = ((EmulDataWidth'(1) << field_bits) - 1) << field_lsb;
    `DV_CHECK_STD_RANDOMIZE_WITH_FATAL(err_mask,
                                       $countones(err_mask) == inject_num_errors;
                                       (err_mask & ~field_mask) == '0;)
    // Bypasses write() above, which would also recompute the integrity byte. rram_row_write()
    // re-encodes the macro's own ECC, so the macro neither corrects nor flags the flipped bits.
    row_path = $sformatf("%0s[%0d]", get_full_path(0), row_addr >> this.addr_lsb);
    rw_data  = rram_row_read(row_path);
    rram_row_write(row_path, rw_data ^ err_mask);
    `uvm_info(`gfn, $sformatf(
              "Addr: %0h, data_word: %0b, row: %0h, original data: %0h, error_mask: %0h",
              addr, data_word, row_addr, rw_data, err_mask), UVM_HIGH)
  endfunction

  // Byte address in the shared array of the integrity byte for the 64b chunk that holds `addr`.
  protected function int unsigned get_intg_byte_addr(bit [bus_params_pkg::BUS_AW-1:0] addr);
    return OtpIntgByteOffset + addr / (rram_ctrl_pkg::OtpIntgDataWidth / 8);
  endfunction

  // Updates the integrity byte(s) for the row `write()` just touched: one 8-bit Hamming(72,64)
  // syndrome per 64b chunk, stored in a separate integrity page.
  //
  // Goes through rram_row_read()/rram_row_write() directly at already-absolute addresses, rather
  // than through write8()/read() or even super.read()/super.write().
  // write8()/read() are inherited unmodified from mem_bkdr_util, but call the virtual
  // read()/write() above internally, which would double-apply OtpDataByteOffset and recurse back
  // into this function.
  // super.read()/super.write() (mem_bkdr_util's own) would bypass this class's ECC encoding
  // entirely, leaving the row's inline check bits stale relative to the data byte just spliced
  // into it.
  protected function void update_integrity(bit [bus_params_pkg::BUS_AW-1:0] addr, row_data_t data);
    localparam int unsigned ChunkBits = rram_ctrl_pkg::OtpIntgDataWidth;
    int unsigned row_start = (addr / this.bytes_per_word) * this.bytes_per_word;

    for (int unsigned lsb = 0; lsb < this.width; lsb += ChunkBits) begin
      // Compute integrity
      bit [ChunkBits-1:0] chunk = data[lsb +: ChunkBits];
      bit [71:0] enc = prim_secded_pkg::prim_secded_hamming_72_64_enc(chunk);
      bit [7:0] intg = enc[71:64];
      // Compute integrity word address and index
      int unsigned intg_byte_addr = get_intg_byte_addr(row_start + lsb / 8);
      int unsigned intg_row_addr = (intg_byte_addr / this.bytes_per_word) * this.bytes_per_word;
      int unsigned byte_idx = intg_byte_addr - intg_row_addr;
      int unsigned intg_row_index = intg_row_addr >> this.addr_lsb;
      string row_path = $sformatf("%0s[%0d]", get_full_path(0), intg_row_index);
      // Read the full row, update the integrity byte within it, write the full row back
      bit [EmulDataWidth-1:0] row = rram_row_read(row_path);
      row[byte_idx * 8 +: 8] = intg;
      rram_row_write(row_path, row);
      touched_intg_row[intg_row_addr] = 1'b1;
    end
  endfunction

  // Parses an OTP image already in RRAM layout (gen-rram-img.py's --out-otp-vmem output: 144b
  // physical rows for OTP's data, plus its Hamming(72,64) integrity page) and writes it.
  // Each line is "@<word_addr> <row_val>", word_addr an absolute 128b-word address in the shared
  // array.
  //
  // Each row's top 16 bits are rram_macro's own physical ECC (see gen-rram-img.py's _rram_ecc()),
  // which write128()/rram_row_write() below recompute fresh for the same scheme.
  // Those bits are discarded here, not reused.
  //
  // Data rows (word_addr*bytes_per_word >= OtpDataByteOffset) are written via write128(), which
  // recomputes and deposits their integrity bytes as a side effect through write() above.
  // Integrity rows are not written directly.
  // They're stashed and, once all data rows are in, compared against what update_integrity()
  // actually computed.
  // A mismatch means this class's and gen-rram-img.py's integrity computations have diverged.
  virtual task load_mem_from_file(string file, bit recompute_ecc = 0);
    int fd;
    string line;
    int unsigned num_data_rows = 0;
    int unsigned num_verified_intg_rows = 0;
    int unsigned num_unused_intg_rows = 0;
    bit [bus_params_pkg::BUS_AW-1:0] intg_addrs[$];
    logic [127:0]                    intg_vals[$];

    fd = $fopen(file, "r");
    `DV_CHECK_FATAL(fd, $sformatf("Could not open file %0s for reading.", file))

    while (!$feof(fd)) begin
      bit [31:0]    word_addr;
      logic [143:0] row_full;
      logic [127:0] row;
      bit [bus_params_pkg::BUS_AW-1:0] byte_addr;

      if ($fgets(line, fd) == 0) continue;
      if ($sscanf(line, "@%h %h", word_addr, row_full) != 2) continue;  // header/comment line
      row = row_full[127:0];

      byte_addr = word_addr * this.bytes_per_word;
      if (byte_addr >= OtpDataByteOffset) begin
        this.write128(byte_addr - OtpDataByteOffset, row);
        num_data_rows++;
      end else begin
        intg_addrs.push_back(byte_addr);
        intg_vals.push_back(row);
      end
    end
    $fclose(fd);

    foreach (intg_addrs[i]) begin
      // Goes through rram_row_read()/rram_row_write() directly at already-absolute addresses, for
      // the same reason update_integrity() does.
      // super.read()/super.write() (mem_bkdr_util's own) would bypass this class's ECC encoding,
      // leaving the row's inline check bits stale.
      string row_path = $sformatf("%0s[%0d]", get_full_path(0), intg_addrs[i] >> this.addr_lsb);
      if (touched_intg_row.exists(intg_addrs[i])) begin
        logic [127:0] actual = rram_row_read(row_path);
        `DV_CHECK_EQ_FATAL(actual, intg_vals[i],
            $sformatf({"OTP image %0s: integrity row at byte 0x%0h doesn't match what ",
                       "update_integrity() computed while loading this file."},
                      file, intg_addrs[i]))
        num_verified_intg_rows++;
      end else begin
        // Unused padding.
        // update_integrity() never wrote this row, so there's nothing to verify it against.
        // Write the file's value directly instead.
        rram_row_write(row_path, intg_vals[i]);
        num_unused_intg_rows++;
      end
    end

    `uvm_info(`gfn, $sformatf({"Loaded %0d OTP data rows from %0s, verified %0d integrity rows, ",
                               "wrote %0d unused integrity rows as-is"},
                              num_data_rows, file, num_verified_intg_rows,
                              num_unused_intg_rows), UVM_MEDIUM)
  endtask

endclass
