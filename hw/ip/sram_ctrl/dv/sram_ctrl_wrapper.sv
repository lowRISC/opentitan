// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0


// Wrapper module for DV that instantiates all 3 requisite module to form the full SRAM:
// - sram_ctrl
// - tlul_adapter_sram
// - prim_ram_1p_scr
module sram_ctrl_wrapper
  // dep packages
  import sram_ctrl_pkg::*;
  import sram_ctrl_reg_pkg::*;
#(
  parameter int unsigned AddrWidth = 14,
  parameter int unsigned DataWidth = 32
) (
  // clock/reset for sram_ctrl
  input                                             clk_i,
  input                                             rst_ni,
  // clock/reset for otp_ctrl
  input                                             clk_otp_i,
  input                                             rst_otp_ni,
  // TLUL interface for CSR regfile
  input tlul_pkg::tl_h2d_t                          csr_tl_i,
  output tlul_pkg::tl_d2h_t                         csr_tl_o,
  // TLUL interface for the SRAM memory
  input tlul_pkg::tl_h2d_t                          sram_tl_i,
  output tlul_pkg::tl_d2h_t                         sram_tl_o,
  // Alert I/O
  input prim_alert_pkg::alert_rx_t [NumAlerts-1:0]  alert_rx_i,
  output prim_alert_pkg::alert_tx_t [NumAlerts-1:0] alert_tx_o,
  // Life-cycle escalation input
  input lc_ctrl_pkg::lc_tx_t                        lc_escalate_en_i,
  // Key request to OTP
  output otp_ctrl_pkg::sram_otp_key_req_t           sram_otp_key_o,
  input otp_ctrl_pkg::sram_otp_key_rsp_t            sram_otp_key_i
);

  // Scrambling key interface between sram_ctrl and scrambling RAM
  sram_scr_req_t scr_req;
  sram_scr_rsp_t scr_rsp;

  // SRAM interface between TLUL adapter and scrambling RAM
  wire                  req;
  wire                  gnt;
  wire                  we;
  wire [AddrWidth-1:0]  addr;
  wire [DataWidth-1:0]  wdata;
  wire [DataWidth-1:0]  wmask;
  wire [DataWidth-1:0]  rdata;
  wire                  rvalid;

  // SRAM Controller
  sram_ctrl u_sram_ctrl (
    // main clock
    .clk_i            (clk_i            ),
    .rst_ni           (rst_ni           ),
    // OTP clock
    .clk_otp_i        (clk_otp_i        ),
    .rst_otp_ni       (rst_otp_ni       ),
    // TLUL interface for CSRs
    .tl_i             (csr_tl_i         ),
    .tl_o             (csr_tl_o         ),
    // Alert I/O
    .alert_rx_i       (alert_rx_i       ),
    .alert_tx_o       (alert_tx_o       ),
    // Life cycle escalation
    .lc_escalate_en_i (lc_escalate_en_i ),
    // OTP key derivation interface
    .sram_otp_key_o   (sram_otp_key_o   ),
    .sram_otp_key_i   (sram_otp_key_i   ),
    // Interface with SRAM memory scrambling
    .sram_scr_o       (scr_req          ),
    .sram_scr_i       (scr_rsp          )
  );

  // TLUL Adapter SRAM
  tlul_adapter_sram #(
    .SramAw(AddrWidth),
    .SramDw(DataWidth)
  ) u_tl_adapter_sram (
    .clk_i    (clk_i          ),
    .rst_ni   (rst_ni         ),
    // TLUL interface to SRAM memory
    .tl_i     (sram_tl_i      ),
    .tl_o     (sram_tl_o      ),
    // Corresponding SRAM request interface
    .req_o    (req            ),
    .gnt_i    (gnt            ),
    .we_o     (we             ),
    .addr_o   (addr           ),
    .wdata_o  (wdata          ),
    .wmask_o  (wmask          ),
    .rdata_i  (rdata          ),
    .rvalid_i (rvalid         ),
    .rerror_i (scr_rsp.rerror )
  );

  // Scrambling memory
  prim_ram_1p_scr #(
    .Width(DataWidth),
    .Depth(2 ** AddrWidth)
  ) u_ram1p_sram (
    .clk_i      (clk_i          ),
    .rst_ni     (rst_ni         ),
    // Key interface
    .key_valid_i(scr_req.valid  ),
    .key_i      (scr_req.key    ),
    .nonce_i    (scr_req.nonce  ),
    // SRAM response interface to TLUL adapter
    .req_i      (req            ),
    .gnt_o      (gnt            ),
    .write_i    (we             ),
    .addr_i     (addr           ),
    .wdata_i    (wdata          ),
    .wmask_i    (wmask          ),
    .rdata_o    (rdata          ),
    .rvalid_o   (rvalid         ),
    .rerror_o   (scr_rsp.rerror ),
    .raddr_o    (scr_rsp.raddr  ),
    .cfg_i      ('0             )
  );

endmodule
