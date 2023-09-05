// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

`include "prim_assert.sv"

module mbx_ombx #(
  parameter int unsigned CfgSramAddrWidth   = 32,
  parameter int unsigned CfgSramDataWidth   = 32,
  parameter int unsigned CfgOmbxDwCntWidth  = 11
) (
  input  logic                          clk_i,
  input  logic                          rst_ni,
  output logic                          ombx_state_error_o,
  output logic                          ombx_pending_o,
  output logic                          ombx_status_ready_update_o,
  output logic                          ombx_status_ready_o,
    input  logic                          hostif_range_valid_i,
  input  logic [CfgSramAddrWidth-1:0]   hostif_base_i,
  input  logic [CfgSramAddrWidth-1:0]   hostif_limit_i,
  // Control signals from the host and system interface
  input  logic                          hostif_control_abort_set_i,
  input  logic                          hostif_status_error_set_i,
  input  logic                          sysif_status_ready_i,
  input  logic                          sysif_control_abort_set_i,
  input  logic                          sysif_read_data_read_valid_i,
  input  logic                          sysif_read_data_write_valid_i,
  // Interface for the object size register
  input logic                           hostif_ombx_object_size_write_i,
  input logic [CfgOmbxDwCntWidth-1:0]   hostif_ombx_object_size_i,
  output logic                          hostif_ombx_object_size_read_o,
  output logic [CfgOmbxDwCntWidth-1:0]  hostif_ombx_object_size_o,
  // DOE data coming from the SRAM
  output  logic [CfgSramDataWidth-1:0]  ombx_read_data_o,
  // Host interface to the private SRAM
  output logic                          ombx_sram_read_req_o,
  input  logic                          ombx_sram_read_gnt_i,
  output logic [CfgSramAddrWidth-1:0]   ombx_sram_read_ptr_o,
  input  logic                          ombx_sram_read_resp_valid_i,
  input  logic [CfgSramDataWidth-1:0]   ombx_sram_read_resp_i
);
  localparam int unsigned LCFG_SRM_ADDRINC = CfgSramDataWidth / 8;

  logic [CfgSramAddrWidth-1:0] sram_read_ptr_d, sram_read_ptr_q;
  logic [CfgSramAddrWidth-1:0] sram_read_ptr_limit_d, sram_read_ptr_limit_q;

  // Status signals from the FSM
  logic mbx_empty, mbx_read, mbx_sys_abort;
  logic set_pop_entry, clear_pop_entry;

  // Generate the read request
  // - mbx reader ACK the current RdData and pop another DW from outbound mailbox
  // 1st pop is initiated by mbx owner writes ObDwCnt
  logic read_req, pop_entry_q;
  assign read_req = pop_entry_q |
                    (mbx_read & sysif_read_data_write_valid_i &
                    (sram_read_ptr_q <= sram_read_ptr_limit_q));

  // Backpressure the next read data until the current write data brings back the data from SRAM
  // Exclude last ack
  logic set_pending, clear_pending;

  // Block the request from TLUL until the SRAM read is complete
  assign set_pending   = mbx_read & sysif_read_data_write_valid_i &
                        (sram_read_ptr_q <= sram_read_ptr_limit_q);
  assign clear_pending = ombx_sram_read_resp_valid_i;

  prim_flop #(
    .Width(1)
  ) u_pending (
    .clk_i ( clk_i                                           ),
    .rst_ni( rst_ni                                          ),
    .d_i   ( set_pending | (ombx_pending_o & ~clear_pending) ),
    .q_o   ( ombx_pending_o                                  )
  );

   // Create a sticky TLUL read request until its granted
  logic req_q;
  assign ombx_sram_read_req_o = read_req | req_q;

  prim_flop #(
    .Width(1)
  ) u_req_state (
    .clk_i ( clk_i                                            ),
    .rst_ni( rst_ni                                           ),
    .d_i   ( ombx_sram_read_req_o & ~ombx_sram_read_gnt_i ),
    .q_o   ( req_q                                            )
  );

  logic writer_close_mbx;
  // move FSM to MBRead (Ready) after the 1st read comes back
  assign writer_close_mbx = mbx_empty & ombx_sram_read_resp_valid_i;

  // Terminate mbx_read state (Ready = 1 -> 0) if ombx is already drained (sram_read is not issued)
  logic sys_read_all;
  assign  sys_read_all = mbx_read                      &
                        sysif_read_data_write_valid_i  &
                        (sram_read_ptr_q == sram_read_ptr_limit_q);

  logic host_clear_abort;
  assign host_clear_abort = hostif_control_abort_set_i & mbx_sys_abort;

  // SRAM read pointer management
  logic load_read_ptr, advance_read_ptr;

  // Rewind the read pointer to the base
  assign load_read_ptr = set_pop_entry | sys_read_all | host_clear_abort;

  // Advance the read pointer when one request went through
  assign  advance_read_ptr = ombx_sram_read_req_o;

  always_comb begin
    sram_read_ptr_d = sram_read_ptr_q;

    if (load_read_ptr) begin
      sram_read_ptr_d = hostif_base_i;
    end else if (advance_read_ptr) begin
      sram_read_ptr_d = sram_read_ptr_q + LCFG_SRM_ADDRINC;
    end
  end

  prim_generic_flop_en #(
    .Width(CfgSramAddrWidth)
  ) u_sram_read_ptr (
    .clk_i ( clk_i                            ),
    .rst_ni( rst_ni                           ),
    .en_i  ( load_read_ptr | advance_read_ptr ),
    .d_i   ( sram_read_ptr_d                  ),
    .q_o   ( sram_read_ptr_q                  )
  );
  assign ombx_sram_read_ptr_o = sram_read_ptr_q;

  // Advance the SRAM read response to read data
  prim_generic_flop_en #(
    .Width(CfgSramDataWidth)
  ) u_sram_read_data (
    .clk_i ( clk_i                                        ),
    .rst_ni( rst_ni                                       ),
    .en_i  ( ombx_sram_read_resp_valid_i | sys_read_all ),
    .d_i   ( {CfgSramDataWidth{~sys_read_all}} & ombx_sram_read_resp_i                  ),
    .q_o   ( ombx_read_data_o                             )
  );

  logic host_write_ob_dw_count_q;
  logic ombx_dw_count_update_valid_q;

  prim_flop #(
    .Width(1)
  ) u_host_write_ob_dw_count (
    .clk_i ( clk_i                                                           ),
    .rst_ni( rst_ni                                                          ),
    .d_i   ( hostif_ombx_object_size_write_i & ~ombx_dw_count_update_valid_q ),
    .q_o   ( host_write_ob_dw_count_q                                        )
  );


  logic [CfgOmbxDwCntWidth-1:0] hostif_ob_object_size_minus_one;
  assign hostif_ob_object_size_minus_one = hostif_ombx_object_size_i - 1;
  // Zero out OMBX DW Count on the abort
  assign hostif_ombx_object_size_o = {CfgOmbxDwCntWidth{~sysif_control_abort_set_i}} &
                                   hostif_ob_object_size_minus_one;

  assign hostif_ombx_object_size_read_o = (read_req & ombx_sram_read_gnt_i) |
                                           sysif_control_abort_set_i;
  prim_flop #(
    .Width(1)
  ) u_host_ombx_dw_count_update_valid (
    .clk_i ( clk_i                            ),
    .rst_ni( rst_ni                           ),
    .d_i   ( hostif_ombx_object_size_read_o ),
    .q_o   ( ombx_dw_count_update_valid_q     )
  );

  // Compute the read pointer limit after DW count is written
  assign sram_read_ptr_limit_d = hostif_base_i + {hostif_ombx_object_size_i, 2'b0};

  prim_generic_flop_en #(
    .Width(CfgSramAddrWidth)
  ) u_sram_read_ptr_limit (
    .clk_i ( clk_i                                ),
    .rst_ni( rst_ni                               ),
    // Factor in ~mbx_read because HW update can trigger host_write_ob_dw_count_q
    .en_i  ( host_write_ob_dw_count_q & ~mbx_read ),
    .d_i   ( sram_read_ptr_limit_d                ),
    .q_o   ( sram_read_ptr_limit_q                )
  );

  // mbx_empty means the ombx has not been read yet (not really empty)
  // Add (|hostif_ombx_object_size_i) to exclude the write-0-DwCnt initialization
  assign set_pop_entry   = mbx_empty & host_write_ob_dw_count_q & (|hostif_ombx_object_size_i);
  assign clear_pop_entry = ombx_sram_read_gnt_i;

  prim_flop #(
    .Width(1)
  ) u_pop_entry (
    .clk_i ( clk_i                                            ),
    .rst_ni( rst_ni                                           ),
    .d_i   ( set_pop_entry | (pop_entry_q & ~clear_pop_entry) ),
    .q_o   ( pop_entry_q                                      )
  );

  mbx_fsm #(
    .CfgOmbx ( 1 )
  ) u_mbxfsm(
    .clk_i                     ( clk_i                      ),
    .rst_ni                    ( rst_ni                     ),
    .mbx_range_valid_i         ( hostif_range_valid_i       ),
    .hostif_abort_ack_i        ( hostif_control_abort_set_i ),
    .hostif_status_error_set_i ( hostif_status_error_set_i  ),
    .hostif_status_busy_clear_i( 1'b0                       ),
    .sysif_control_abort_set_i ( sysif_control_abort_set_i  ),
    .sys_read_all_i            ( sys_read_all               ),
    .writer_close_mbx_i        ( writer_close_mbx           ),
    .writer_write_valid_i      ( 1'b0                       ),
    // Status signals
    .mbx_empty_o               ( mbx_empty                  ),
    .mbx_write_o               (                            ),
    .mbx_read_o                ( mbx_read                   ),
    .mbx_sys_abort_o           ( mbx_sys_abort              ),
    .mbx_ob_ready_update_o     ( ombx_status_ready_update_o ),
    .mbx_ob_ready_o            ( ombx_status_ready_o        ),
    .mbx_state_error_o         ( ombx_state_error_o         )
  );

  //////////////////////////////////////////////////////////////////////////////
  // Assertions
  //////////////////////////////////////////////////////////////////////////////

  // Read req should e de-asserted after the read is ACKed by the TLUL adapter
  `ASSERT_NEVER(DeassertReqAfterAck_A, ombx_sram_read_req_o & ombx_sram_read_resp_valid_i)
  // When reading from the ombx doe_status.ready must have been asserted
  `ASSERT_NEVER(ReadyAssertedWhenRead_A, ombx_sram_read_req_o &
                ~(pop_entry_q | sysif_status_ready_i))
  // System write-to-read data is non-posted.  No subsequential read or write comes before the
  // write is ACKed
  `ASSERT_NEVER(NoReadBeforeWriteAcked_A, ombx_pending_o &
                (sysif_read_data_read_valid_i | sysif_read_data_write_valid_i))
  // Never read the SRAM if it is empty
  logic ombx_is_empty;
  assign  ombx_is_empty = (sram_read_ptr_q == sram_read_ptr_limit_q);
  `ASSERT_NEVER(NeverReadWhenEmpty_A, ombx_sram_read_req_o & ombx_is_empty)
  // Never let the read pointer run out of the limit
  `ASSERT_NEVER(NeverRunOutOfLimit_A, sram_read_ptr_q > sram_read_ptr_limit_q)

`ifdef INC_ASSERT

  logic[CfgSramAddrWidth-1:0] sram_read_ptr_assert_q;
  prim_flop #(
    .Width(CfgSramAddrWidth)
  ) u_sram_ptr_assert (
    .clk_i ( clk_i                  ),
    .rst_ni( rst_ni                 ),
    .d_i   ( sram_read_ptr_d        ),
    .q_o   ( sram_read_ptr_assert_q )
  );
  // A granted write by the host adapter must advance the write pointer
  `ASSERT_IF(GntMustAdvanceReadPtr_A, sram_read_ptr_assert_q == sram_read_ptr_q,
             ombx_sram_read_gnt_i)
`endif
endmodule
