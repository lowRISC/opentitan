// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Structures defined by the following Controller-side specifications:
// - MIPI Alliance Specification for I3C TCRI, Version 1.0 (Public Release Edition).
// - MIPI Alliance Specification for I3C HCI, Version 1.2 (Public Release Edition).

package i3c_hci_pkg;
  import i3c_consts_pkg::*;

  // --- HCI/TCRI structure descriptions ---

  // Full DAT Entry as per the HCI Specification (HCI 8.1).
  typedef struct packed {
    logic [63:59] reserved2;
    logic [58:51] autocmd_hdr_code;
    logic [50:48] autocmd_mode;
    logic [47:40] autocmd_value;
    logic [39:32] autocmd_mask;
    logic         device;
    logic [30:29] dev_nack_retry_cnt;
    logic [28:26] ring_id;
    logic [25:24] reserved1;
    logic [23:16] dynamic_address;
    logic         ts;
    logic         crr_reject;
    logic         ibi_reject;
    logic         ibi_payload;
    logic [11:7]  reserved0;
    logic [6:0]   static_address;
  } i3c_dat_entry_t;

  // Packed DAT Entry as stored internally; as above but without the reserved fields.
  typedef struct packed {
    logic [58:51] autocmd_hdr_code;
    logic [50:48] autocmd_mode;
    logic [47:40] autocmd_value;
    logic [39:32] autocmd_mask;
    logic         device;
    logic [30:29] dev_nack_retry_cnt;
    logic [28:26] ring_id;
    logic [23:16] dynamic_address;
    logic         ts;
    logic         crr_reject;
    logic         ibi_reject;
    logic         ibi_payload;
    logic [6:0]   static_address;
  } i3c_dat_mem_t;

  // Full DCT Entry as per the HCI Specification (HCI 8.2).
  typedef struct packed {
    logic [127:104] reserved2;
    logic [103:96]  dynamic_address;
    logic [95:80]   reserved1;
    logic [79:72]   bcr;
    logic [71:64]   dcr;
    logic [63:48]   reserved0;
    logic [47:32]   pid_lo;
    logic [31:0]    pid_hi;
  } i3c_dct_entry_t;

  // Packed DCT Entry as stored internally; as above but without the reserved fields.
  typedef struct packed {
    logic [103:96]  dynamic_address;
    logic [79:72]   bcr;
    logic [71:64]   dcr;
    logic [47:32]   pid_lo;
    logic [31:0]    pid_hi;
  } i3c_dct_mem_t;

  // Immediate Data Transfer Command. Format 1 (TCRI 7.1.2.1).
  // - many fields are present in all command types; annotated here.
  typedef struct packed {
    logic     [7:0] data_byte_4;
    logic     [7:0] data_byte_3;
    logic     [7:0] data_byte_2;
    logic     [7:0] data_byte_1;
    logic           toc;        // Terminate On Completion.
    logic           wroc;       // Write Response On Completion.
    logic           rnw;        // Direction (Read, not Write).
    i3c_xfer_mode_e mode;       // Mode and Speed.
    logic     [2:0] dtt;        // Data Transfer Type and byte count.
    logic     [1:0] reserved;
    logic     [4:0] dev_index;  // Index into DAT, to retrieve device/group properties.
    logic           cp;         // Command Present.
    i3c_ccc_e       cmd;        // Command, used for CCC or HDR Command Word, iff `cp` set.
    logic     [3:0] tid;        // Transaction ID.
    i3c_cmd_attr_e  cmd_attr;   // Command Attribute (specifies command type).
  } i3c_xfer_cmd_imm_t;

  // Regular Transfer Command. Format 1 (TCRI 7.1.2.2).
  typedef struct packed {
    logic    [15:0] data_length;
    logic     [7:0] reserved1;
    logic     [7:0] def_byte;        // Defining Byte, if used.
    logic           toc;
    logic           wroc;
    logic           rnw;
    i3c_xfer_mode_e mode;
    logic           dbp;             // Defining Byte Present.
    logic           short_read_err;  // Short Read is Error; fewer bytes not allowed.
    logic     [2:0] reserved;
    logic     [4:0] dev_index;
    logic           cp;
    i3c_ccc_e       cmd;
    logic     [3:0] tid;
    i3c_cmd_attr_e  cmd_attr;
  } i3c_xfer_cmd_reg_t;

  // Combo Transfer Command. Format 1 (TCRI 7.1.2.3).
  typedef struct packed {
    logic    [15:0] data_length;
    logic    [15:0] offset;
    logic           toc;
    logic           wroc;
    logic           rnw;
    i3c_xfer_mode_e mode;
    logic           suboff_16b;
    logic           fpm;
    logic     [1:0] dlp;
    logic           reserved;
    logic     [4:0] dev_index;
    logic           cp;
    i3c_ccc_e       cmd;
    logic     [3:0] tid;
    i3c_cmd_attr_e  cmd_attr;
  } i3c_xfer_cmd_combo_t;

  // Address Assignment Command. (HCI 8.4.1).
  typedef struct packed {
    logic    [31:0] reserved2;
    logic           toc;
    logic           wroc;
    logic     [3:0] dev_count;
    logic     [4:0] reserved1;
    logic     [4:0] dev_index;
    logic           reserved;
    i3c_ccc_e       cmd;
    logic     [3:0] tid;
    i3c_cmd_attr_e  cmd_attr;
  } i3c_xfer_cmd_addr_assgn_t;

  // Internal Control Command (HCI 8.4.2).
  typedef struct packed {
    logic    [31:0] vendor_specific;
    logic   [31:12] mipi_reserved;
    i3c_mipi_cmd_e  mipi_cmd;
    logic           vend_info_present;
    logic     [3:0] tid;
    i3c_cmd_attr_e  cmd_attr;
  } i3c_xfer_cmd_intern_ctrl_t;

  // Command Descriptor.
  typedef union packed {
    // All command descriptors overlap exactly; use `cmd_attr` member to differentiate.
    i3c_xfer_cmd_imm_t cmd_imm;
    i3c_xfer_cmd_reg_t cmd_reg;
    i3c_xfer_cmd_combo_t cmd_combo;
    i3c_xfer_cmd_addr_assgn_t cmd_daa;
    i3c_xfer_cmd_intern_ctrl_t cmd_intn;
  } i3c_xfer_cmd_desc_t;

  // Response Descriptor (TCRI 7.1.3).
  typedef struct packed {
    i3c_err_status_e err_status;
    logic      [3:0] tid;
    logic      [7:0] reserved;
    logic     [15:0] data_length;
  } i3c_xfer_rsp_t;

  // IBI Status Descriptor (HCI 8.6).
  typedef struct packed {
    logic             ibi_sts;
    logic             error;
    i3c_ibi_status_e  status_type;
    logic             reserved;
    logic             ts;
    logic             last_status;
    logic       [7:0] chunks;
    logic       [7:0] ibi_id;
    logic       [7:0] data_length;
  } i3c_ibi_status_t;

  // --- End of HCI/TCRI structure descriptions ---

endpackage
