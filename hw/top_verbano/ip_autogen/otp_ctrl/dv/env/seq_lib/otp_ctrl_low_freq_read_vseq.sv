// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// This sequence backdoor write OTP memory and use a low clock frequency to read out OTP memory.
class otp_ctrl_low_freq_read_vseq extends otp_ctrl_base_vseq;
  `uvm_object_utils(otp_ctrl_low_freq_read_vseq)

  `uvm_object_new

  virtual task pre_start();
    cfg.en_scb = 0;
    super.pre_start();
    write_unused_addr = 0;
    cfg.clk_rst_vif.set_freq_mhz(6);
  endtask

  virtual task post_start();
    super.post_start();

    // restore original clock frequency
    cfg.clk_rst_vif.set_freq_mhz(cfg.clk_freq_mhz);
  endtask : post_start

  virtual task body();
    // Backdoor write all partitions.
    for (int addr = VendorTestOffset / 4; addr < LifeCycleOffset / 4; addr++) begin
      int dai_addr = addr * 4;
      if (cfg.stop_transaction_generators()) return;
      cfg.mem_bkdr_util_h.write32(dai_addr, dai_addr);
      `uvm_info(`gfn, $sformatf("backdoor write dai addr %0h", dai_addr), UVM_HIGH)
    end

    // Use low clock frequency to read out each OTP memory.
    for (int addr = VendorTestOffset / 4; addr < LifeCycleOffset / 4; addr++) begin
      bit [31:0] dai_addr = addr * 4;
      int        part_idx = get_part_index(dai_addr);
      if (cfg.stop_transaction_generators()) break;

      if (!is_digest(dai_addr)) begin
        // If read memory is in secret partitions, descramble the backdoor write data.
        if (is_secret(dai_addr)) begin
          bit [SCRAMBLE_DATA_SIZE-1:0] secret_data = {normalize_dai_addr(dai_addr) + 4,
                                                      normalize_dai_addr(dai_addr)};
          bit [SCRAMBLE_DATA_SIZE-1:0] data = descramble_data(secret_data, part_idx);
          dai_rd_check(dai_addr, data[TL_DW-1:0], data[SCRAMBLE_DATA_SIZE-1:TL_DW]);
        end else begin
          dai_rd_check(dai_addr, dai_addr);
        end

        // If the partition is sw partition, also check TLUL access.
        if (is_sw_part(dai_addr)) begin
          bit [TL_DW-1:0] tlul_val;
          uvm_reg_addr_t tlul_addr = cfg.ral.get_addr_from_offset(get_sw_window_offset(dai_addr));
          tl_access(.addr(tlul_addr), .write(0), .data(tlul_val), .blocking(1));
          if (!cfg.under_reset) begin
            `DV_CHECK_EQ(tlul_val, dai_addr,
                         $sformatf("sw parts read out mismatch at tlul_addr %0h, dai_addr %0h",
                                    tlul_addr, dai_addr))
          end
        end
      end else begin
        dai_rd_check(dai_addr, normalize_dai_addr(dai_addr), normalize_dai_addr(dai_addr) + 4);
      end
    end
  endtask

endclass
