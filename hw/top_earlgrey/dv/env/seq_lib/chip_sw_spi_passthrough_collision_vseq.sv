// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// This sequence tests read commands that pass through and write commands that
// are uploaded to software. Software is then expected to relay write commands
// back out through the spi_host IP to the device agent.
class chip_sw_spi_passthrough_collision_vseq extends chip_sw_spi_passthrough_vseq;
  `uvm_object_utils(chip_sw_spi_passthrough_collision_vseq)

  `uvm_object_new

  // Generate a random permutation of the following opcodes, then insert
  // a SpiFlashWriteEnable before each write command and a SpiFlashReadSts1
  // after each write command:
  //   - SpiFlashReadNormal
  //   - SpiFlashReadFast
  //   - SpiFlashReadDual
  //   - SpiFlashReadQuad
  //   - SpiFlashChipErase
  //   - SpiFlashSectorErase
  //   - SpiFlashPageProgram
  //   - SpiFlashWriteSts1
  virtual function void generate_spi_flash_sequence();
    spi_flash_cmd_e opcodes[] = '{
      SpiFlashReadNormal,
      SpiFlashReadFast,
      SpiFlashReadDual,
      SpiFlashReadQuad,
      SpiFlashChipErase,
      SpiFlashSectorErase,
      SpiFlashPageProgram,
      SpiFlashWriteSts1
    };
    opcodes.shuffle();
    foreach (opcodes[i]) begin
      case (opcodes[i])
        SpiFlashChipErase,
        SpiFlashSectorErase,
        SpiFlashPageProgram,
        SpiFlashWriteSts1: begin
          // Write commands use the following sequence:
          //   - WriteEnable
          //   - The write command
          //   - ReadSts1 (to check for busy, which is always 0 from the agent)
          test_opcodes.push_back(SpiFlashWriteEnable);
          test_opcodes.push_back(opcodes[i]);
          test_opcodes.push_back(SpiFlashReadSts1);
        end
        default:
          test_opcodes.push_back(opcodes[i]);
      endcase
    end
  endfunction

  // Send the sequence of commands indicated by the `test_opcodes` member.
  // These commands must be registered with the host and device agents, as the
  // command info determines the actions takes for each opcode. Random data of
  // random size will be generated for each command that has a payload phase.
  virtual task execute_spi_flash_sequence();
    const int max_payload_size = 256;
    spi_device_flash_seq m_spi_device_seq;
    spi_host_flash_seq m_spi_host_seq;
    spi_item host_rsp, device_rsp;
    spi_item host_rsp_q[$], device_rsp_q[$];
    spi_agent_cfg agent_cfg = cfg.m_spi_host_agent_cfg;
    bit defer_response_compare;
    spi_flash_cmd_e device_ops[$] = test_opcodes;

    fork begin : isolation_fork
      fork
        // The device agent handles the incoming command with random data,
        // except for SpiFlashReadSts1, which always returns 0. The software
        // sends the exact same sequence of commands as the host agent, except
        // for eliminating repeated SpiFlashReadSts1 commands.
        begin
          while (device_ops.size() > 0) begin
            bit [7:0] device_op = device_ops.pop_front();
            `uvm_create_on(m_spi_device_seq, p_sequencer.spi_device_sequencer_hs[0]);
            if (device_op == SpiFlashReadSts1) begin
              // For simplicity, report that the device agent is never busy.
              m_spi_device_seq.byte_data_q = {8'h0};
            end
            `uvm_send(m_spi_device_seq);
            `DV_CHECK_EQ(m_spi_device_seq.rsp.opcode, device_op);
            device_rsp_q.push_back(m_spi_device_seq.rsp);
          end
        end
      join_none

      while (test_opcodes.size() > 0) begin
        bit [7:0] opcode = test_opcodes.pop_front();

        // Starting with the WriteEnable in a write command sequence, defer
        // response comparison until the WIP and WEL status bits are cleared.
        // Software will issue commands to the device agent later.  The sequence
        // from the DUT spi_host will be WriteEnable, <write command>, ReadSts1.
        if (opcode == SpiFlashWriteEnable) begin
          defer_response_compare = 1'b1;
        end else if (opcode == SpiFlashReadSts1) begin
          defer_response_compare = 1'b0;
        end

        `uvm_create_on(m_spi_host_seq, p_sequencer.spi_host_sequencer_h);
        // Prepare for specific opcode. The address_q is kept empty, which will
        // trigger m_spi_host_seq to do the lookup and supply a random value.
        if (opcode == SpiFlashWriteSts1 || opcode == SpiFlashReadSts1) begin
          `DV_CHECK_RANDOMIZE_WITH_FATAL(m_spi_host_seq,
                                         opcode == local::opcode;
                                         address_q.size() == 0;
                                         payload_q.size() == 1;
                                         read_size == payload_q.size(););
        end else begin
          `DV_CHECK_RANDOMIZE_WITH_FATAL(m_spi_host_seq,
                                         opcode == local::opcode;
                                         address_q.size() == 0;
                                         payload_q.size() <= local::max_payload_size;
                                         read_size == payload_q.size(););
        end
        `uvm_send(m_spi_host_seq);
        if (opcode == SpiFlashReadSts1 && m_spi_host_seq.rsp.payload_q[0][0] != 0) begin
          // Wait until software clears the WIP and WEL bits.
          spi_host_wait_on_busy();
        end
        host_rsp_q.push_back(m_spi_host_seq.rsp);

        // Check that uploaded commands modify CSRs as expected.
        case (opcode)
          SpiFlashWriteSts1,
          SpiFlashChipErase,
          SpiFlashSectorErase,
          SpiFlashPageProgram: begin
            // Ensure there is an interrupt.
            csr_spinwait(
              .ptr(ral.spi_device.intr_state.upload_cmdfifo_not_empty),
              .exp_data(1'b1),
              .backdoor(1),
              .spinwait_delay_ns(20));
            // Check the depths.
            csr_rd_check(
              .ptr(ral.spi_device.upload_status.cmdfifo_depth),
              .backdoor(1),
              .compare_value(1)
            );
            csr_rd_check(
              .ptr(ral.spi_device.upload_status.addrfifo_depth),
              .backdoor(1),
              .compare_value((m_spi_host_seq.rsp.address_q.size() == 0) ? 0 : 1)
            );
            csr_rd_check(
              .ptr(ral.spi_device.upload_status2.payload_depth),
              .backdoor(1),
              .compare_value(m_spi_host_seq.rsp.payload_q.size())
            );
            csr_rd_check(
              .ptr(ral.spi_device.upload_status2.payload_start_idx),
              .backdoor(1),
              .compare_value(0)
            );
            `DV_CHECK_EQ(device_rsp_q.size(), 0);
          end
          default: begin
            // Software is only involved for uploaded commands. For commands
            // that aren't uploaded, wait for a small delay to allow the device
            // agent to push the response into the queue.
            #1ps;
          end
        endcase

        if (!defer_response_compare) begin
          // Check that the command, address, and data sent matches on both sides.
          `DV_CHECK_EQ(host_rsp_q.size(), device_rsp_q.size());
          while (host_rsp_q.size() > 0) begin
            host_rsp = host_rsp_q.pop_front();
            device_rsp = device_rsp_q.pop_front();
            if (opcode == SpiFlashReadSts1) begin
              // Nullify the comparison of status registers between host and
              // device for reads, as the DUT will track changes, but the device
              // agent and this sequence do not.
              host_rsp.payload_q = {device_rsp.payload_q};
            end
            if (!host_rsp.compare(device_rsp)) begin
              `uvm_error(`gfn, $sformatf("Compare mismatch\nhost_rsp:\n%sdevice_rsp:\n%s",
                                         host_rsp.sprint(), device_rsp.sprint()))
            end
          end
        end
      end
      disable fork;
      // Ensure all responses have been checked.
      `DV_CHECK_EQ(device_rsp_q.size(), 0);
      `DV_CHECK_EQ(host_rsp_q.size(), 0);
    end join
  endtask

  virtual task cpu_init();
    // Set up passthrough filters and the upload configuration. Pass this
    // information down to software.
    bit [7:0] sw_filter_config[4];
    bit [7:0] upload_config[1] = {8'h1};
    super.cpu_init();
    passthrough_filters[spi_device_pkg::CmdInfoReadStatus3:spi_device_pkg::CmdInfoReadStatus1] = '1;
    passthrough_filters[spi_device_pkg::CmdInfoReadCmdEnd:spi_device_pkg::CmdInfoReadCmdStart] = '0;
    passthrough_filters[spi_device_pkg::NumTotalCmdInfo-1:spi_device_pkg::CmdInfoReserveStart] = '1;
    sw_filter_config = {<<byte{passthrough_filters}};
    sw_symbol_backdoor_overwrite("kFilteredCommands", sw_filter_config);
    sw_symbol_backdoor_overwrite("kUploadWriteCommands", upload_config);
  endtask

endclass : chip_sw_spi_passthrough_collision_vseq
