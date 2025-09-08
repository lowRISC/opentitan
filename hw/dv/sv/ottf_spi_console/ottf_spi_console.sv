// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// This class can be instantiated as a testbench object to provide routines to interact
// with an OTTF SPI console using an OpenTitan spi_host agent.
//
// See the ottf_spi_console_pkg header for a fuller description.

class ottf_spi_console extends uvm_component;
  `uvm_component_utils(ottf_spi_console)

  function new(string name = "", uvm_component parent = null);
    super.new(name, parent);
  endfunction : new

  virtual clk_rst_if clk_rst_vif;
  virtual pins_if #(.Width(2), .PullStrength("Weak")) flow_ctrl_vif;

  uvm_sequence seq_h;
  spi_sequencer spi_host_sequencer_h;

  // Define local macros which function like `uvm_create and `uvm_send, except using the
  // class-local handles to the parent sequence 'seq_h' and sequencer 'spi_host_sequencer_h'.
  `ifndef spi_console_uvm_create
    // verilog_lint: waive macro-name-style
    `define spi_console_uvm_create(SEQ_) \
      begin \
        uvm_object_wrapper type_var = SEQ_.get_type(); \
        // Create item, returned attached to a uvm_sequence_item handle, so \
        // cast to the original subclass sequence type handle \
        $cast(SEQ_, spi_console_create_item(type_var, `"SEQ_`")); \
      end
  `endif
  `ifndef spi_console_uvm_send
    // verilog_lint: waive macro-name-style
    `define spi_console_uvm_send(SEQ_) \
      begin \
        SEQ_.start(/*sequencer*/ spi_host_sequencer_h, /*parent_sequence*/ seq_h); \
      end
  `endif

  // This function replaces the 'create_item()' method in the uvm base classes,
  // except 'seq_h' is always used as the parent_seq, and 'spi_host_sequencer_h' is always
  // used as the sequencer.
  function uvm_sequence_item spi_console_create_item(uvm_object_wrapper type_var,
                                                     string name = "");
    // Get factory
    uvm_coreservice_t cs = uvm_coreservice_t::get();
    uvm_factory factory = cs.get_factory();
    // Use factory to construct the object
    uvm_object obj = factory.create_object_by_type(type_var, seq_h.get_full_name(), name);
    // Cast object to assign to the uvm_sequence_item handle
    uvm_sequence_item item;
    $cast(item, obj);
    // Attach new sequence object to parent sequence / sequencer registered with the class.
    item.set_item_context(seq_h, spi_host_sequencer_h);

    return item;
  endfunction

  // Helper-methods

  // Checks for a pattern match in a sting using uvm_re_match(), and print upon success.
  extern protected function bit findStrRe(string pattern, string str);
  // Reverse byte endianess in a 32-bit word (0x12345678 -> 0x78563412)
  extern protected function bit [31:0] reverse_endianess(bit [31:0] inp);
  // Format an array of bytes as an ascii string.
  extern protected function string byte_array_as_str(bit [7:0] q[]);
  // Format a queue of bytes as an ascii string.
  extern protected function string byte_q_as_str(bit [7:0] q[$]);
  // Format a queue of bytes as a hexadecimal-formatted integer.
  extern protected function string byte_q_as_hex(bit [7:0] q[$]);
  // Wait for a given value of one of the console sideband flow control signals.
  extern protected task await_flow_ctrl_signal(flow_ctrl_idx_e idx,
                                               bit val = 1'b1,
                                               uint timeout_ns = await_flow_ctrl_timeout_ns);

  // spi_console implementation details (taken from the corresponding software components)
  //
  // CONSTANTS
  // const SPI_FRAME_HEADER_SIZE           : usize =   12;
  // const SPI_FLASH_READ_BUFFER_SIZE      : u32   = 2048;
  // const SPI_FLASH_PAYLOAD_BUFFER_SIZE   : usize =  256;
  // const SPI_MAX_DATA_LENGTH             : usize = 2036;
  // const SPI_FRAME_MAGIC_NUMBER          : u32   = 0xa5a5beef;
  // const SPI_TX_LAST_CHUNK_MAGIC_ADDRESS : u32   =      0x100;
  // const SPI_BOOT_MAGIC_PATTERN          : u32   = 0xcafeb002;
  //
  //
  // DEVICE->HOST transfers
  // (READS)
  //
  //   FRAME STRUCTURE
  //
  //    -----------------------------------------------
  //    |      Magic Number     | 4-bytes  |          |
  //    -----------------------------------|          |
  //    |      Frame Number     | 4-bytes  |  Header  |
  //    -----------------------------------|          |
  //    |   Data Length (bytes) | 4-bytes  |          |
  //    -----------------------------------|----------|
  //    |      Data (word aligned)         |          |
  //    -----------------------------------|   Data   |
  //    |     0xFF Pad Bytes    | <4-bytes |          |
  //    -----------------------------------|----------|
  //
  //   - tx_ready_gpio (IOA5 here...)
  //     - Flow-control mechanism for DEVICE->HOST transfers
  //     - ENABLED for ft_personalize.c (`console_tx_indicator.enable = true`)
  //     - The DEVICE sets the sideband 'tx_ready' gpio when the SPI console buffer has data,
  //       and clears the gpio when there is no longer data available.
  //     - When using the TX-indicator pin feature, we always write each SPI frame at the
  //       beginning of the flash buffer, and wait for the host to read it out before writing
  //       another frame.
  //
  //
  // HOST->DEVICE transfers
  // (WRITES)
  //
  //   - DEVICE signals ready by asserting a sideband RX-indicator pin (rx_ready)
  //   - Message is chunked in payloads, each of which are written (via upload command) to
  //     address zero.
  //     - After each upload, HOST polls busy to await the DEVICE reading the buffer contents.
  //   - For final chunk, HOST uploads it to a special address (SPI_TX_LAST_CHUNK_MAGIC_ADDRESS)
  //   - After DEVICE reads the final chunk, it de-asserts the RX-indicator pin (rx_ready)

  ///////////////////////
  // CONSOLE READ IMPL //
  ///////////////////////

  // READ CONSTANTS
  // (constants also taken from the corresponding software components)
  uint SPI_FLASH_READ_BUFFER_SIZE = 2048; // To ensure we don't overwrite our PAYLOAD BUFFER
  uint SPI_MAX_DATA_LENGTH = 2036;
  uint SPI_FRAME_HEADER_SIZE = 12;
  bit [31:0] SPI_FRAME_MAGIC_NUMBER = 32'ha5a5beef;
  // Derived constants from ottf_console_internal.h
  uint kSpiDeviceBufferPreservedSizeBytes = SPI_FRAME_HEADER_SIZE;
  uint kSpiDeviceMaxFramePayloadSizeBytes = SPI_FLASH_READ_BUFFER_SIZE -
                                            SPI_FRAME_HEADER_SIZE -
                                            kSpiDeviceBufferPreservedSizeBytes - 4;

  // READ METHODS
  //
  // Drive a single ReadNormal operation to the DEVICE spi_console.
  extern protected task host_spi_console_read(input int        size,
                                              input bit [31:0] addr,
                                              output bit [7:0] chunk_q[$]);
  // Read a single frame from the DEVICE spi console.
  extern protected task host_spi_console_read_frame(ref bit [7:0] chunk_q[$]);
  // Await the DEVICE signalling a read, and check the payload contains the given string.
  extern task host_spi_console_read_wait_for(input string wait_for);
  // Await the DEVICE signalling a read, and return the payload as an array of bytes.
  //
  // For this method, we know the maximum expected payload length. Keep awaiting new frames until
  // either the maximum total payload length is reached/exceeded, or we see a frame which is less
  // than the max length for a single frame.
  extern task host_spi_console_read_payload(output bit [7:0] outbuf[], input int max_len);

  ////////////////////////
  // CONSOLE WRITE IMPL //
  ////////////////////////

  // WRITE CONSTANTS
  //
  uint SPI_FLASH_PAYLOAD_BUFFER_SIZE = 256; // Don't overwrite the PAYLOAD BUFFER
  bit [31:0] SPI_TX_ADDRESS = '0;
  bit [31:0] SPI_TX_LAST_CHUNK_MAGIC_ADDRESS = 9'h100;

  // WRITE METHODS
  //
  // Poll the DEVICE flash busy bit, returning when a status of NOT-BUSY is returned.
  extern protected task host_spi_console_wait_while_busy(uint timeout_ns = wait_on_busy_timeout_ns);
  // Perform a single write operation, enabling writes and then waiting for not-busy after
  // having driven the write_seq.
  extern protected task host_spi_console_write_op(spi_host_flash_seq write_seq);
  // Write a single buffer of data to the DEVICE.
  // This task enforces a maximum buffer size of SPI_FLASH_PAYLOAD_BUFFER_SIZE, which prevents
  // data-loss on the DEVICE side by overwriting the payload buffer.
  extern protected task host_spi_console_write_buf(input bit [7:0] bytes_q[$],
                                                   input bit [31:0] addr);
  // Write a generic buffer of data to the console DEVICE. This method will chunk up the payload
  // into smaller operations if it is larger than the DEVICE's payload buffer.
  extern protected task host_spi_console_write(input bit [7:0] bytes[]);
  // Wait until the DEVICE signals it is awaiting a write, then perform one or more console write
  // operations. This task tries to write all given payloads successively before waiting for the
  // device to clear the sideband flow_control signal, and cannot short-circuit or early return.
  extern task host_spi_console_write_when_ready(input bit [7:0] bytes[][],
                                                uint timeout_ns = write_completion_timeout_ns);

endclass : ottf_spi_console

/////////////
// HELPERS //
/////////////

function bit ottf_spi_console::findStrRe(string pattern, string str);
  string re_pattern = $sformatf("*%0s*", pattern);
  bit    match = !uvm_re_match(re_pattern, str);
  // After negation, match = 1 / nomatch = 0
  if (match) begin
    `uvm_info(`gfn,
              $sformatf("findStrRe() MATCH=%0d, string: \"%s\", pattern: \"%s\"",
                        match, str, re_pattern),
              UVM_DEBUG)
  end
  return match;
endfunction

function bit [31:0] ottf_spi_console::reverse_endianess(bit [31:0] inp);
  return {>>{ {<<8{inp}} }};
endfunction

function string ottf_spi_console::byte_array_as_str(bit [7:0] q[]);
  string str = "";
  foreach (q[i]) $sformat(str, "%s%0s", str, q[i]);
  return str;
endfunction

function string ottf_spi_console::byte_q_as_str(bit [7:0] q[$]);
  string str = "";
  foreach (q[i]) $sformat(str, "%s%0s", str, q[i]);
  return str;
endfunction

function string ottf_spi_console::byte_q_as_hex(bit [7:0] q[$]);
  string str = "";
  foreach (q[i]) $sformat(str, "%s%02x", str, q[i]);
  return str;
endfunction

task ottf_spi_console::await_flow_ctrl_signal(flow_ctrl_idx_e idx,
                                              bit val = 1'b1,
                                              uint timeout_ns = await_flow_ctrl_timeout_ns);
  `uvm_info(`gfn, $sformatf("Waiting for pin:%0d to be %0d now...", idx, val), UVM_HIGH)
  `DV_WAIT(
    /*WAIT_COND_*/  flow_ctrl_vif.pins[idx] == val,
    /*MSG_*/        $sformatf("Timed out waiting for pin '%0s' to be 1'b%0b.", idx.name(), val),
    /*TIMEOUT_NS_*/ timeout_ns)
  `uvm_info(`gfn, $sformatf("Saw idx:%0d as %0d now!", idx, val), UVM_HIGH)
endtask: await_flow_ctrl_signal

//////////////////
// CONSOLE READ //
//////////////////

task ottf_spi_console::host_spi_console_read(input int        size,
                                             input bit [31:0] addr,
                                             output bit [7:0] chunk_q[$]);
  // Set the flash read address
  bit [7:0] byte_addr_q[$] = {addr[23:16], addr[15:8], addr[7:0]};

  spi_host_flash_seq m_spi_host_seq;
  `spi_console_uvm_create(m_spi_host_seq);

  `DV_CHECK_RANDOMIZE_WITH_FATAL(m_spi_host_seq,
    opcode == SpiFlashReadNormal;
    address_q.size() == byte_addr_q.size();
    foreach (byte_addr_q[i]) address_q[i] == byte_addr_q[i];
    payload_q.size() == size;
    read_size == size;
  )

  `uvm_info(`gfn, "host_spi_console_read() - Start.", UVM_HIGH)
  `spi_console_uvm_send(m_spi_host_seq)
  `uvm_info(`gfn, "host_spi_console_read() - End.", UVM_HIGH)
  // Get data out of the sequence once completed.
  foreach (m_spi_host_seq.rsp.payload_q[i]) chunk_q.push_back(m_spi_host_seq.rsp.payload_q[i]);

endtask : host_spi_console_read

task ottf_spi_console::host_spi_console_read_frame(ref bit [7:0] chunk_q[$]);
  bit [31:0] header_data_bytes = 0;

  // First, get the header of the current frame.
  begin : get_header
    bit [31:0] header_magic_number;
    bit [31:0] header_frame_number;
    bit [7:0]  header_q[$];
    host_spi_console_read(.size(SPI_FRAME_HEADER_SIZE), .addr(0), .chunk_q(header_q));
    header_magic_number = reverse_endianess({>>{header_q[0:3]}});
    header_frame_number = reverse_endianess({>>{header_q[4:7]}});
    header_data_bytes   = reverse_endianess({>>{header_q[8:11]}});
    `uvm_info(`gfn, $sformatf("Got header : 0x%0s", byte_q_as_hex(header_q)), UVM_HIGH)
    `uvm_info(`gfn,
              $sformatf("Magic Number : 0x%02x Frame Number : 0x%02x, Num_Data_Bytes : 0x%02x",
                        header_magic_number, header_frame_number, header_data_bytes),
              UVM_HIGH)
    `DV_CHECK_EQ(header_magic_number, SPI_FRAME_MAGIC_NUMBER, "Bad spi_console Header MAGIC_NUM")
    `DV_CHECK_LT(header_data_bytes, SPI_MAX_DATA_LENGTH, "Cannot handle this many data bytes!")
  end

  // Add an arbitrary delay here to slow things down.
  // The ottf_console_spi.c code in spi_device_send_frame() relies on manually querying the
  // value of CSB (via reading the HW status register) and observing it change state 4 times
  // to know that two full SPI transfers have taken place.
  // If there is not adequate space between the two transfers, the software will miss its
  // measurement here of the chip select returning high/inactive.
  #(min_interval_ns);

  // Next, get all the data_bytes from the frame.
  while (header_data_bytes > 0) begin
    bit [7:0] data_q[$] = {};
    host_spi_console_read(.size(header_data_bytes),
                          .addr(SPI_FRAME_HEADER_SIZE),
                          .chunk_q(data_q));
    `uvm_info(`gfn, $sformatf("Got data_bytes in chunk : %0s", byte_q_as_str(data_q)), UVM_HIGH)
    // #TODO Assume we read all bytes in one go, for now. The DV_CHECK_EQ in the header block will
    // stop us dead for now if the payload is too large.
    header_data_bytes = 0;

    // Append the bytes from this read transfer to the overall queue.
    chunk_q = {chunk_q, data_q};
  end

  // Again, add the arbitrary delay to allow the DEVICE sw time to ready CSB low to detect the
  // end of the frame.
  #(min_interval_ns);

endtask : host_spi_console_read_frame

task ottf_spi_console::host_spi_console_read_wait_for(input string wait_for);
  bit [7:0] chunk_q[$];
  string    chunk_q_as_str;

  `uvm_info(`gfn, $sformatf("Waiting to read the following string in the spi_console : %0s",
    wait_for), UVM_LOW)

  `uvm_info(`gfn, "Waiting for the DEVICE to set 'tx_ready' (IOA5)", UVM_HIGH)
  await_flow_ctrl_signal(tx_ready, 1'b1);
  `uvm_info(`gfn, "DEVICE set 'tx_ready' now.", UVM_HIGH)

  // Next, get all the data_bytes from the frame until we see the expected message in the buffer.
  do begin
    bit [7:0] data_q[$] = {};
    host_spi_console_read_frame(.chunk_q(data_q));
    `uvm_info(`gfn, $sformatf("Got data_bytes : %0s", byte_q_as_str(data_q)), UVM_HIGH)
    // Append the bytes from this read transfer to the overall queue.
    chunk_q = {chunk_q, data_q};
  end while (!findStrRe(wait_for, byte_q_as_str(chunk_q)));
  `uvm_info(`gfn, $sformatf("Got expected string from spi_console : '%0s'", wait_for), UVM_LOW)

  // (If not already de-asserted) wait for the SPI console TX ready to be cleared by the DEVICE.
  `uvm_info(`gfn, "Waiting for the DEVICE to clear 'tx_ready' (IOA5)", UVM_HIGH)
  await_flow_ctrl_signal(tx_ready, 1'b0);
  `uvm_info(`gfn, "DEVICE cleared 'tx_ready' now.", UVM_HIGH)

endtask : host_spi_console_read_wait_for

task ottf_spi_console::host_spi_console_read_payload(output bit [7:0] outbuf[],
                                                     input int        max_len);
  bit [7:0] payload_byte_q[$] = {};
  int       len_ctr = 0;
  `uvm_info(`gfn, $sformatf("Awaiting read_payload. (max %0d bytes)", max_len), UVM_LOW)

  `uvm_info(`gfn, "Waiting for the DEVICE to set 'tx_ready' (IOA5)", UVM_HIGH)
  await_flow_ctrl_signal(tx_ready, 1'b1);
  `uvm_info(`gfn, "DEVICE set 'tx_ready' now.", UVM_HIGH)

  // Keep getting spi console frames until we determine the payload has completed by length.
  while (len_ctr < max_len) begin
    bit [7:0] frame_byte_q[$] = {};

    fork
      // Capture a single spi_console frame. Return as soon as the data transfer has completed.
      begin : capture_frames
        host_spi_console_read_frame(.chunk_q(frame_byte_q));
        payload_byte_q = {payload_byte_q, frame_byte_q};
        len_ctr += frame_byte_q.size();
        `uvm_info(`gfn, $sformatf("Got %0d data bytes in frame : %0s", frame_byte_q.size(),
          byte_q_as_str(frame_byte_q)), UVM_MEDIUM)
        `uvm_info(`gfn, $sformatf("Got %0d / %0d(max) data bytes in expected payload.",
          len_ctr, max_len), UVM_MEDIUM)
      end
      // The DEVICE will de-assert tx_ready after the first CSB edge, knowing that both sides
      // understand that two full spi transfers need to complete (header + data). It won't
      // re-assert tx_ready until after the 4th CSB edge (the end of the second transfer)
      begin : await_tx_ready_deassert
        `uvm_info(`gfn, "Waiting for the DEVICE to clear 'tx_ready' (IOA5)", UVM_HIGH)
        await_flow_ctrl_signal(tx_ready, 1'b0);
        `uvm_info(`gfn, "DEVICE cleared 'tx_ready' now.", UVM_HIGH)
      end
    join

    // If the frame is any less than the maximum size, assume this is the end of the
    // payload. I'm not going to implement a message parser / deserializer here.
    if (frame_byte_q.size() < kSpiDeviceMaxFramePayloadSizeBytes) begin
      `uvm_info(`gfn, "Got less-than-max-size frame, assuming payload end now.", UVM_MEDIUM)
      break;
    end

    // If the payload isn't complete, wait for the device to indicate the next frame is ready...
    if (len_ctr < max_len) begin
      `uvm_info(`gfn, "Payload not yet complete, awaiting next frame...", UVM_MEDIUM)
      await_flow_ctrl_signal(tx_ready, 1'b1);
    end

  end

  outbuf = {>>{payload_byte_q}};

endtask : host_spi_console_read_payload

///////////////////
// CONSOLE WRITE //
///////////////////

task ottf_spi_console::host_spi_console_wait_while_busy(uint timeout_ns = wait_on_busy_timeout_ns);
  spi_host_flash_seq m_spi_host_seq;
  `spi_console_uvm_create(m_spi_host_seq);

  `DV_SPINWAIT(
    // WAIT_
    do begin
      `uvm_info(`gfn, "host_spi_console_wait_while_busy() - Polling DEVICE busy bit...", UVM_DEBUG)

      // Wait before polling.
      #(min_interval_ns);
      clk_rst_vif.wait_clks($urandom_range(1, 100));

      `DV_CHECK_RANDOMIZE_WITH_FATAL(m_spi_host_seq,
        opcode == SpiFlashReadSts1;
        address_q.size() == 0;
        payload_q.size() == 1;
        read_size == 1;
      )
      `spi_console_uvm_send(m_spi_host_seq)

      // Check the busy bit (bit[0]) and loop while the DEVICE still reports busy (==1)
    end while (m_spi_host_seq.rsp.payload_q[0][0] === 1);,
    // MSG_
    "Timed-out awaiting the spi_console DEVICE to report not-busy after a write operation",
    // TIMEOUT_NS_
    timeout_ns
  )

  `uvm_info(`gfn, "host_spi_console_wait_while_busy() - DEVICE not-busy, continuing...", UVM_DEBUG)
endtask : host_spi_console_wait_while_busy

task ottf_spi_console::host_spi_console_write_op(spi_host_flash_seq write_seq);

  // First, enable writes.
  spi_host_flash_seq m_spi_host_seq;
  `spi_console_uvm_create(m_spi_host_seq);
  m_spi_host_seq.opcode = SpiFlashWriteEnable;
  `spi_console_uvm_send(m_spi_host_seq)

  // Next, perform the write
  `spi_console_uvm_send(write_seq)

  // Finally, wait for the busy status bit to be cleared
  host_spi_console_wait_while_busy();

endtask : host_spi_console_write_op

task ottf_spi_console::host_spi_console_write_buf(input bit [7:0]  bytes_q[$],
                                                  input bit [31:0] addr);
  uint bytes_q_size = bytes_q.size();

  spi_host_flash_seq m_spi_host_seq;
  `spi_console_uvm_create(m_spi_host_seq);

  m_spi_host_seq.opcode = SpiFlashPageProgram;
  m_spi_host_seq.address_q = {addr[23:16], addr[15:8], addr[7:0]};
  `DV_CHECK(bytes_q_size <= SPI_FLASH_PAYLOAD_BUFFER_SIZE)
  for (int i = 0; i < bytes_q_size; i++) begin
    m_spi_host_seq.payload_q.push_back(bytes_q.pop_front());
  end

  `uvm_info(`gfn, $sformatf("Sending payload data_bytes(hex) : 0x%0s",
    byte_q_as_hex(m_spi_host_seq.payload_q)), UVM_HIGH)
  `uvm_info(`gfn, $sformatf("Sending payload data_bytes(str) : %0s",
    byte_q_as_str(m_spi_host_seq.payload_q)), UVM_HIGH)

  host_spi_console_write_op(m_spi_host_seq);
endtask : host_spi_console_write_buf

task ottf_spi_console::host_spi_console_write(input bit [7:0] bytes[]);
  uint written_data_len = 0;

  `uvm_info(`gfn, $sformatf("console_write() :: len=%0d : %0s", $size(bytes),
    byte_array_as_str(bytes)), UVM_MEDIUM)

  do begin
    // - chunk_len holds the size of the current chunk we are about to write
    // - write_address is the address the current chunk will be written to
    uint chunk_len;
    bit [31:0] write_address;

    uint remaining_len = $size(bytes) - written_data_len;

    if (remaining_len > SPI_FLASH_PAYLOAD_BUFFER_SIZE) begin
      // If the remaining data cannot fit inside a single write operation
      // (limited by the size of the DEVICE payload buffer size), then
      // just send a max-size chunk this time around.
      chunk_len = SPI_FLASH_PAYLOAD_BUFFER_SIZE;
      write_address = SPI_TX_ADDRESS;
    end else begin
      // The remaining data fits in a single chunk. Send this chunk to the
      // MAGIC_ADDRESS to signal to the DEVICE it is the final chunk.
      chunk_len = remaining_len;
      write_address = SPI_TX_LAST_CHUNK_MAGIC_ADDRESS;
    end
    `uvm_info(`gfn,
              $sformatf("console_write() :: remaining=%0d, chunk_len=%0d, addr=32'h%8x",
                        remaining_len, chunk_len, write_address),
              UVM_DEBUG)
    begin : write_chunk
      bit [7:0] bytes_q[$];
      for (int i = 0; i < chunk_len; i++) begin
        bytes_q.push_back(bytes[i + written_data_len]);
      end
      host_spi_console_write_buf(bytes_q, write_address);
    end
    written_data_len += chunk_len;

  end while ($size(bytes) - written_data_len > 0);

endtask : host_spi_console_write

task ottf_spi_console::host_spi_console_write_when_ready(
  input bit [7:0] bytes[][],
  uint timeout_ns = write_completion_timeout_ns
);

  `uvm_info(`gfn, "Waiting for the DEVICE to set 'rx_ready' (IOA6)", UVM_HIGH)
  await_flow_ctrl_signal(rx_ready, 1'b1);
  `uvm_info(`gfn, "DEVICE set 'rx_ready' now.", UVM_HIGH)

  `DV_SPINWAIT(
    /* WAIT_ */       foreach (bytes[i]) host_spi_console_write(bytes[i]);,
    /* MSG_ */        "Timeout waiting for spi_console_write_when_ready() to complete.",
    /* TIMEOUT_NS_ */ timeout_ns
  )

  `uvm_info(`gfn, "Waiting for the DEVICE to clear 'rx_ready' (IOA6)", UVM_HIGH)
  await_flow_ctrl_signal(rx_ready, 1'b0);
  `uvm_info(`gfn, "DEVICE cleared 'rx_ready' now.", UVM_HIGH)

endtask : host_spi_console_write_when_ready

`undef spi_console_uvm_create
`undef spi_console_uvm_send
