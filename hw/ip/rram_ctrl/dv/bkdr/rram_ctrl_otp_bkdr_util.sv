// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// mem_bkdr_util specialization for the OTP region of the RRAM data array.
//
// otp_ctrl's macro interface didn't change when otp_macro was swapped for rram_ctrl, so
// otp_ctrl_reg_pkg's partition offsets (e.g. LcStateOffset) still apply as-is. RRAM stores OTP in
// the tail pages of the same array as RramData (OtpStartPage).
// This bkdr_util implementation targets the same RramData array as the rram_bkdr_loader but only
// writing to the last segment of it.
// It write/reads data, and maintains the OTP integrity page by storing the Hamming(72,64) integrity
// word in it.

class rram_ctrl_otp_bkdr_util extends mem_bkdr_util;

  // Byte offsets into the shared array where OTP data and its integrity page start. Mirror
  // OtpStartAddr / OtpIntgStartAddr in rram_ctrl_otp.sv.
  localparam int unsigned OtpDataByteOffset =
      (rram_ctrl_pkg::OtpStartPage + 1) << (rram_ctrl_pkg::BusAddrByteW - rram_ctrl_pkg::PageW);
  localparam int unsigned OtpIntgByteOffset =
      rram_ctrl_pkg::OtpStartPage << (rram_ctrl_pkg::BusAddrByteW - rram_ctrl_pkg::PageW);

  // Integrity rows actually written by update_integrity(), keyed by byte address. Lets
  // load_mem_from_file() skip verifying unused padding rows it never computed.
  protected bit touched_intg_row[bit [bus_params_pkg::BUS_AW-1:0]];

  // Set for the duration of inject_errors() below, so write() can skip recomputing integrity for
  // the corrupted word - otherwise the injected error would always be masked by a freshly valid
  // syndrome, making it undetectable by rram_ctrl_otp.
  protected bit suppress_integrity_update = 1'b0;

  // path/depth/n_bits cover the whole RRAM data array, same as RramData/RramInfo.
  // err_detection_scheme is always ErrDetectionNone - OTP's integrity is handled in
  // update_integrity() below instead of via a generic ECC scheme.
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
  endfunction

  // read8/16/32/64/128 all funnel through here.
  virtual function row_data_t read(bit [bus_params_pkg::BUS_AW-1:0] addr);
    return super.read(addr + OtpDataByteOffset);
  endfunction

  // write8/16/32/64/128 funnel through here.
  virtual function void write(bit [bus_params_pkg::BUS_AW-1:0] addr, row_data_t data);
    super.write(addr + OtpDataByteOffset, data);
    if (!suppress_integrity_update) update_integrity(addr, data);
  endfunction

  // inject_errors funnels through write() above (inherited unmodified from mem_bkdr_util), which
  // would otherwise recompute a fresh, self-consistent integrity byte for the corrupted data -
  // masking the injected error instead of making it detectable. Suppress that for the single
  // write() call the base implementation makes.
  virtual function void inject_errors(bit [bus_params_pkg::BUS_AW-1:0] addr,
                                      uint32_t inject_num_errors);
    suppress_integrity_update = 1'b1;
    super.inject_errors(addr, inject_num_errors);
    suppress_integrity_update = 1'b0;
  endfunction

  // Updates the integrity byte(s) for the row `write()` just touched: one 8-bit Hamming(72,64)
  // syndrome per 64b chunk, stored in a separate integrity page.
  //
  // Goes through super.read()/super.write() directly rather than write8()/read(): those are
  // inherited unmodified from mem_bkdr_util, but still call the virtual read()/write() above
  // internally, which would double-apply OtpDataByteOffset and recurse back into this function.
  protected function void update_integrity(bit [bus_params_pkg::BUS_AW-1:0] addr, row_data_t data);
    localparam int unsigned ChunkBits  = rram_ctrl_pkg::OtpIntgDataWidth;
    localparam int unsigned ChunkBytes = ChunkBits / 8;
    int unsigned row_start = (addr / this.bytes_per_word) * this.bytes_per_word;

    for (int unsigned lsb = 0; lsb < this.width; lsb += ChunkBits) begin
      // Compute integrity
      bit [ChunkBits-1:0] chunk = data[lsb +: ChunkBits];
      bit [71:0] enc = prim_secded_pkg::prim_secded_hamming_72_64_enc(chunk);
      bit [7:0] intg = enc[71:64];
      // Compute integrity word address and index
      int unsigned intg_byte_addr = OtpIntgByteOffset + (row_start + lsb / 8) / ChunkBytes;
      int unsigned intg_row_addr = (intg_byte_addr / this.bytes_per_word) * this.bytes_per_word;
      int unsigned byte_idx = intg_byte_addr - intg_row_addr;
      // Read the full row
      row_data_t   row = super.read(intg_row_addr);
      // Update integrity
      row[byte_idx * 8 +: 8] = intg;
      // Write back the full row
      super.write(intg_row_addr, row);
      touched_intg_row[intg_row_addr] = 1'b1;
    end
  endfunction

  // Parses an OTP image already in RRAM layout (gen-rram-img.py's --out-otp-vmem output: 128b
  // rows for OTP's data, plus its Hamming(72,64) integrity page) and writes it.
  // Each line is "@<word_addr> <row_val>",
  // word_addr an absolute 128b-word address in the shared array.
  //
  // Data rows (word_addr*bytes_per_word >= OtpDataByteOffset) are written via write128(), which
  // - through write() above - recomputes and deposits their integrity bytes as a side effect.
  // Integrity rows are not written directly; they're stashed and, once all data rows are in,
  // compared against what update_integrity() actually computed. A mismatch means this class's and
  // gen-rram-img.py's integrity computations have diverged.
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
      bit [31:0] word_addr;
      logic [127:0] row;
      bit [bus_params_pkg::BUS_AW-1:0] byte_addr;

      if ($fgets(line, fd) == 0) continue;
      if ($sscanf(line, "@%h %h", word_addr, row) != 2) continue;  // header/comment line

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
      if (touched_intg_row.exists(intg_addrs[i])) begin
        // row_data_t is a generic container much wider than the 128b RRAM actually uses here;
        // read() only ever populates the low 128 bits and leaves the rest at their default (X).
        // Slice down to those 128 bits explicitly, rather than comparing the full row_data_t
        // against intg_vals[i] (now itself a plain logic [127:0], so there's no equivalent
        // upper-bits ambiguity on that side to begin with).
        logic [127:0] actual = super.read(intg_addrs[i])[127:0];
        `DV_CHECK_EQ_FATAL(actual, intg_vals[i],
            $sformatf({"OTP image %0s: integrity row at byte 0x%0h doesn't match what ",
                       "update_integrity() computed while loading this file."},
                      file, intg_addrs[i]))
        num_verified_intg_rows++;
      end else begin
        // Unused padding - update_integrity() never wrote this row, so there's nothing to
        // verify it against. Write the file's value directly instead.
        super.write(intg_addrs[i], intg_vals[i]);
        num_unused_intg_rows++;
      end
    end

    `uvm_info(`gfn, $sformatf({"Loaded %0d OTP data rows from %0s, verified %0d integrity rows, ",
                               "wrote %0d unused integrity rows as-is"},
                              num_data_rows, file, num_verified_intg_rows,
                              num_unused_intg_rows), UVM_MEDIUM)
  endtask

endclass
