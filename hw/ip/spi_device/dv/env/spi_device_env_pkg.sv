// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

package spi_device_env_pkg;
  // dep packages
  import uvm_pkg::*;
  import top_pkg::*;
  import dv_utils_pkg::*;
  import dv_lib_pkg::*;
  import csr_utils_pkg::*;
  import tl_agent_pkg::*;
  import spi_agent_pkg::*;
  import cip_base_pkg::*;
  import mem_model_pkg::*;
  import spi_device_ral_pkg::*;
  import dv_base_reg_pkg::*;

  // macro includes
  `include "uvm_macros.svh"
  `include "dv_macros.svh"

  // local parameters and types
  typedef enum {
    RxFifoFull,
    RxFifoGeLevel,
    TxFifoLtLevel,
    RxFwModeErr,
    RxFifoOverflow,
    TxFifoUnderflow,
    CmdFifoNotEmpty,
    PayloadNotEmpty,
    PayloadOverflow,
    ReadbufWatermark,
    ReadbufFlip,
    TpmHeaderNotEmpty,
    NumSpiDevIntr
  } spi_device_intr_e;

  typedef enum bit {
    SramDataAvail,
    SramSpaceAvail
  } sram_avail_type_e;

  typedef enum bit {
    TpmFifoMode,
    TpmCrbMode
  } tpm_cfg_mode_e;

  typedef enum {
    GenericMode,
    FlashMode,
    PassthroughMode
  } device_mode_e;

  typedef enum bit {
    PayloadIn,
    PayloadOut
  } payload_dir_e;

  typedef enum int {
    ReadAddrWithinMailbox,
    ReadAddrCrossIntoMailbox,
    ReadAddrCrossOutOfMailbox,
    ReadAddrCrossAllMailbox,
    ReadAddrOutsideMailbox
  } read_addr_size_type_e;

  typedef struct packed {
    bit [21:0] other_status;
    bit wel;
    bit busy;
  } flash_status_t;

  // alerts
  parameter uint NUM_ALERTS = 1;
  parameter string LIST_OF_ALERTS[] = {"fatal_fault"};

  // SPI SRAM is 2kB
  parameter uint SRAM_OFFSET                     = 'h1000;
  parameter uint SRAM_SIZE                       = 4096; // 672 depth
  parameter uint SRAM_MSB                        = $clog2(SRAM_SIZE) - 1;
  parameter uint SRAM_PTR_PHASE_BIT              = SRAM_MSB + 1;
  parameter uint SRAM_WORD_SIZE                  = 4;
  parameter uint ASYNC_FIFO_SIZE                 = 8;
  parameter uint READ_BUFFER_START_ADDR          = SRAM_OFFSET;
  parameter uint READ_BUFFER_SIZE                = 2048;
  parameter uint READ_BUFFER_HALF_SIZE           = READ_BUFFER_SIZE / 2;
  // MAILBOX_START_ADDR is 0x800
  parameter uint MAILBOX_START_ADDR              = READ_BUFFER_START_ADDR + READ_BUFFER_SIZE;
  parameter uint MAILBOX_BUFFER_SIZE             = 1024;
  // SFDP_START_ADDR is 0xc00
  parameter uint SFDP_START_ADDR                 = MAILBOX_START_ADDR + MAILBOX_BUFFER_SIZE;
  parameter uint SFDP_SIZE                       = 256;
  parameter uint PAYLOAD_FIFO_START_ADDR         = SFDP_START_ADDR + SFDP_SIZE; // 0xd00
  parameter uint PAYLOAD_FIFO_SIZE               = 256;
  // CMD_FIFO_START_ADDR is 0xe00
  parameter uint CMD_FIFO_START_ADDR             = PAYLOAD_FIFO_START_ADDR + PAYLOAD_FIFO_SIZE;
  parameter uint CMD_FIFO_SIZE                   = 32;
  parameter uint ADDR_FIFO_START_ADDR            = CMD_FIFO_START_ADDR + CMD_FIFO_SIZE; // 0xe20
  parameter uint ADDR_FIFO_SIZE                  = 32;

  parameter uint FW_FLASH_CSB_ID                 = 0; // for both FW and flash/passthrough mode
  parameter uint TPM_CSB_ID                      = 1;

  parameter bit[23:0] TPM_BASE_ADDR              = 24'hD40000;
  parameter bit[23:0] TPM_BASE_ADDR_MASK         = 24'hFF0000;
  parameter byte TPM_ACTIVE_LOCALITY_BIT_POS     = 5;
  parameter byte MAX_SUPPORT_TPM_SIZE            = 64;
  parameter byte MAX_TPM_LOCALITY                = 5;
  parameter byte TPM_OFFSET_WIDTH                = 12;
  parameter byte TPM_LOCALITY_WIDTH              = 4;
  // TPM HW-returned register offset
  parameter bit[11:0] TPM_ACCESS_OFFSET          = 0;
  parameter byte      TPM_ACCESS_BYTE_SIZE       = 1;
  parameter bit[11:0] TPM_INT_ENABLE_OFFSET      = 12'h8;
  parameter byte      TPM_INT_ENABLE_BYTE_SIZE   = 4;
  parameter bit[11:0] TPM_INT_VECTOR_OFFSET      = 12'hC;
  parameter byte      TPM_INT_VECTOR_BYTE_SIZE   = 1;
  parameter bit[11:0] TPM_INT_STATUS_OFFSET      = 12'h10;
  parameter byte      TPM_INT_STATUS_BYTE_SIZE   = 4;
  parameter bit[11:0] TPM_INTF_CAPABILITY_OFFSET = 12'h14;
  parameter byte      TPM_INTF_CAPABILITY_BYTE_SIZE = 4;
  parameter bit[11:0] TPM_STS_OFFSET             = 12'h18;
  parameter byte      TPM_STS_BYTE_SIZE          = 4;
  parameter bit[11:0] TPM_HASH_START_OFFSET      = 12'h28;
  parameter byte      TPM_HASH_START_BYTE_SIZE   = 1;
  parameter bit[11:0] TPM_DID_VID_OFFSET         = 12'hF00;
  parameter byte      TPM_DID_VID_BYTE_SIZE      = 4;
  parameter bit[11:0] TPM_RID_OFFSET             = 12'hF04;
  parameter byte      TPM_RID_BYTE_SIZE          = 1;
  parameter bit[11:0] ALL_TPM_HW_REG_OFFSETS[] = {
      TPM_ACCESS_OFFSET, TPM_INT_ENABLE_OFFSET, TPM_INT_VECTOR_OFFSET,
      TPM_INT_STATUS_OFFSET, TPM_INT_STATUS_OFFSET, TPM_STS_OFFSET,
      TPM_HASH_START_OFFSET, TPM_DID_VID_OFFSET, TPM_RID_OFFSET};
  parameter string ALL_TPM_HW_REG_NAMES[] = {
      "tpm_access_0", "tpm_access_1", "tpm_access_2", "tpm_access_3", "tpm_access_4",
      "tpm_sts", "tpm_intf_capability", "tpm_int_enable", "tpm_int_status", "tpm_int_vector",
      "tpm_did_vid", "tpm_rid", "tpm_hash_start"};

  parameter uint     NUM_INTERNAL_PROCESSED_CMD  = 11; // exclude WREN, WRDI, EN4B, EX4B
  parameter bit[7:0] READ_JEDEC                  = 8'h9F;
  parameter bit[7:0] READ_SFDP                   = 8'h5A;
  parameter bit[7:0] READ_STATUS_1               = 8'h05;
  parameter bit[7:0] READ_STATUS_2               = 8'h35;
  parameter bit[7:0] READ_STATUS_3               = 8'h15;
  parameter bit[7:0] READ_NORMAL                 = 8'h03;
  parameter bit[7:0] READ_FAST                   = 8'h0B;
  parameter bit[7:0] READ_DUAL                   = 8'h3B;
  parameter bit[7:0] READ_QUAD                   = 8'h6B;
  parameter bit[7:0] READ_DUALIO                 = 8'hBB;
  parameter bit[7:0] READ_QUADIO                 = 8'hEB;
  parameter bit[7:0] WREN                        = 8'h06;
  parameter bit[7:0] WRDI                        = 8'h04;
  parameter bit[7:0] EN4B                        = 8'hB7;
  parameter bit[7:0] EX4B                        = 8'hE9;

  `define ALL_READ_CMDS \
      READ_NORMAL, READ_FAST, READ_DUAL, READ_QUAD, READ_DUALIO, READ_QUADIO
  `define ALL_INTERNAL_PROCESS_CMDS \
      READ_JEDEC, READ_SFDP, READ_STATUS_1, READ_STATUS_2, READ_STATUS_3, `ALL_READ_CMDS
  parameter bit[7:0] READ_CMD_LIST[] = {`ALL_READ_CMDS};
  // exclude WREN, WRDI, EN4B, EX4B
  parameter bit[7:0] INTERNAL_PROCESS_CMD_LIST[] = {`ALL_INTERNAL_PROCESS_CMDS};

  string msg_id = "spi_device_env_pkg";

  // functions
  // get size of empty space in mem
  function automatic uint get_sram_space_bytes(uint wptr, uint rptr, uint sram_size_bytes,
                                               string msg = msg_id);
    bit wptr_phase_bit = wptr[SRAM_PTR_PHASE_BIT];
    bit rptr_phase_bit = rptr[SRAM_PTR_PHASE_BIT];
    wptr[SRAM_PTR_PHASE_BIT] = 0;
    rptr[SRAM_PTR_PHASE_BIT] = 0;
    if (wptr_phase_bit == rptr_phase_bit) rptr += sram_size_bytes;
    `DV_CHECK_GE(rptr, wptr, "get_sram_space_bytes::", error, msg)
    return rptr - wptr;
  endfunction

  // get size of filled data in mem
  function automatic uint get_sram_filled_bytes(uint wptr, uint rptr, uint sram_size_bytes,
                                                string msg = msg_id);
    bit wptr_phase_bit = wptr[SRAM_PTR_PHASE_BIT];
    bit rptr_phase_bit = rptr[SRAM_PTR_PHASE_BIT];
    wptr[SRAM_PTR_PHASE_BIT] = 0;
    rptr[SRAM_PTR_PHASE_BIT] = 0;
    if (wptr_phase_bit != rptr_phase_bit) wptr += sram_size_bytes;
    `DV_CHECK_GE(wptr, rptr, "get_sram_filled_bytes", error, msg)
    return wptr - rptr;
  endfunction

  // get the memory size
  function automatic uint get_allocated_sram_size_bytes(uint base, uint limit);
    // Lower 2 bits are ignored
    base[1:0]  = 0;
    limit[1:0] = 0;
    return limit + SRAM_WORD_SIZE - base;
  endfunction

  // use this function to calculate the new ptr value
  // if new rx_rptr exceeds programmed sram size in bytes, then wrap it and flip the phase bit
  // else, restore the 'saved' phase bit
  function automatic uint get_sram_new_ptr(uint ptr,
                                           uint increment,
                                           uint sram_size_bytes);
    bit [TL_DW-1:0] ptr_wo_phase_bit = ptr[SRAM_MSB:0];
    bit             ptr_phase_bit    = ptr[SRAM_PTR_PHASE_BIT];
    uint            new_ptr          = ptr_wo_phase_bit + increment;
    if (new_ptr >= sram_size_bytes) begin
      new_ptr -= sram_size_bytes;
      new_ptr[SRAM_PTR_PHASE_BIT] = ~ptr_phase_bit;
    end else begin
      new_ptr[SRAM_PTR_PHASE_BIT] = ptr_phase_bit;
    end
    return new_ptr;
  endfunction

  // Get TPM address for locality TODO expand to other HW regs
  function automatic bit[23:0] get_tpm_addr(bit[3:0] locality,
                                            bit [TPM_OFFSET_WIDTH-1:0] base_offset);
    return TPM_BASE_ADDR | (locality << TPM_OFFSET_WIDTH) | base_offset;
  endfunction

  // return locality index from the addr
  function automatic bit[23:0] get_locality_from_addr(bit[TPM_ADDR_WIDTH-1:0] addr);
    uint loc = addr[TPM_OFFSET_WIDTH + TPM_LOCALITY_WIDTH - 1 : TPM_OFFSET_WIDTH];
    return loc;
  endfunction

  // return the index the cmd_filter for the input opcode
  function automatic int get_cmd_filter_index(bit[7:0] opcode);
    return opcode / 32;
  endfunction

  // return the field offset of the cmd_filter for the input opcode
  function automatic int get_cmd_filter_offset(bit[7:0] opcode);
    return opcode % 32;
  endfunction

  // return the field offset of the cmd_filter for the input opcode
  function automatic bit[31:0] convert_addr_from_byte_queue(const ref bit[7:0] addr_byte_q[$]);
    bit[31:0] addr;
    foreach (addr_byte_q[i]) begin
      if (i > 0) addr = addr << 8;
      addr[7:0] = addr_byte_q[i];
    end
    return addr;
  endfunction

  // if byte_q.size % 4 > 0, the last word is packed with random value to form the full word
  function automatic void byte_q_to_word_q(input bit [7:0] byte_q[$], output bit [31:0] word_q[$]);
    for (int i = 0; i < byte_q.size; i += 4) begin
      bit [31:0] word_data;
      for (int j = 0 ; j < 4 ; j++) begin
        if (i + j < byte_q.size()) begin
          word_data[8*j+:8] = byte_q[i + j];
        end else begin
          word_data[8*j+:8] = $urandom();
        end
      end
      word_q.push_back(word_data);
    end
  endfunction

  // macros
  `define GET_TX_ALLOCATED_SRAM_SIZE_BYTES \
    get_allocated_sram_size_bytes(ral.txf_addr.base.get_mirrored_value(), \
                                  ral.txf_addr.limit.get_mirrored_value())

  `define GET_RX_ALLOCATED_SRAM_SIZE_BYTES \
    get_allocated_sram_size_bytes(ral.rxf_addr.base.get_mirrored_value(), \
                                  ral.rxf_addr.limit.get_mirrored_value())

  `define GET_OPCODE_VALID_AND_MATCH(CSR, OPCODE) \
    (`gmv(ral.CSR.valid) == 1 && `gmv(ral.CSR.opcode) == OPCODE)

  // package sources
  `include "spi_device_env_cfg.sv"
  `include "spi_device_env_cov.sv"
  `include "spi_device_virtual_sequencer.sv"
  `include "spi_device_scoreboard.sv"
  `include "spi_device_env.sv"
  `include "spi_device_vseq_list.sv"

  `undef GET_TX_ALLOCATED_SRAM_SIZE_BYTES
  `undef GET_RX_ALLOCATED_SRAM_SIZE_BYTES
  `undef GET_OPCODE_VALID_AND_MATCH
endpackage
