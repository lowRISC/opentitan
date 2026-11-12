// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// A virtual sequence that performs a SW operation (using CONTROL / ADDR and the FIFO)

class rram_ctrl_sw_vseq extends uvm_sequence;
  `uvm_object_utils(rram_ctrl_sw_vseq)

  // An enum for the different values of CONTROL.OP
  typedef enum bit [1:0] {
    Read    = 0,
    Write   = 1,
    Rewrite = 2
  } op_t;

  // An enum for the different partitions in CONTROL.PARTITION
  typedef enum bit {
    Data = 0,
    Info = 1
  } partition_t;

  // The operation to perform (written to CONTROL.OP)
  rand op_t m_op;

  // The partition to address (written to CONTROL.PARTITION)
  rand partition_t m_partition;

  // One less than the number of bus words addressed by the operation (written to CONTROL.NUM)
  rand bit [9:0] m_num;

  // The start address for the operation (written to ADDR.START)
  rand bit [20:0] m_addr;

  // A status that accumulates the results of all the register transactions in the sequence. When
  // start finishes, it will either be UVM_IS_OK (if everything worked) or UVM_NOT_OK (if anything
  // failed responded with an error code).
  uvm_status_e m_status = UVM_IS_OK;

  // If this bit is set, the body will abort, completing with m_status = UVM_NOT_OK as soon as any
  // register operation finishes. Set this by calling abort().
  local bit m_abort;

  // The RRAM register block. Set this by calling set_ral() before starting the sequence.
  local rram_ctrl_core_reg_block m_ral;

  // Information about the various configured regions. These give the byte address and length, then
  // whether the region is enabled and whether it allows reads and writes.
  //
  // They are computed from the predicted register contents in pre_randomize().
  local uvm_reg_addr_t [NumRegions-1:0] m_region_start_addrs;
  local uvm_reg_addr_t [NumRegions-1:0] m_region_byte_sizes;
  local bit [NumRegions-1:0]            m_region_en;
  local bit [NumRegions-1:0]            m_region_rd_en;
  local bit [NumRegions-1:0]            m_region_wr_en;

  // Information about configured info pages. These give whether each page is enabled and whether it
  // allows reads and writes.
  //
  // They are computed from the predicted register contents in pre_randomize().
  local bit [NumInfoPages-1:0]          m_page_en;
  local bit [NumInfoPages-1:0]          m_page_rd_en;
  local bit [NumInfoPages-1:0]          m_page_wr_en;

  // The index of the region being addressed (if m_partition is Data).
  //
  // This is constrained to be zero if m_partition == Info (to avoid extra unused state space)
  local rand int unsigned m_region_idx;

  // The index of the page being addressed (if m_partition is Info).
  //
  // This is constrained to be zero if m_partition == Data (to avoid extra unused state space)
  local rand int unsigned m_page_idx;

  extern function new(string name="");
  extern function void pre_randomize();

  extern virtual function void do_print(uvm_printer printer);
  extern task pre_start();
  extern task body();

  // Abort this sequence so that it stops running register operations and returns with m_status set
  // to UVM_NOT_OK as soon as the currently running operation finishes.
  extern function void abort();

  // Set the register block that the virtual sequence will configure. Call this before starting the
  // sequence.
  extern function void set_ral(rram_ctrl_core_reg_block ral);

  // Read m_num+1 bus words from the read FIFO
  extern local task read_fifo();

  // Write m_num+1 bus words to the write FIFO
  extern local task write_fifo();

  // A constraint for when addressing the Data partition. This guarantees that m_addr and m_num give
  // bytes that lie in the region with index m_region_idx and that this region is enabled for the
  // given operation.
  extern constraint region_c;

  // A constraint for when addressing the Info partition. This guarantees that m_addr and m_num give
  // bytes that lie in info m_page_idx and that the page is enabled for the given operation.
  extern constraint page_c;
endclass

function rram_ctrl_sw_vseq::new(string name="");
  super.new(name);
endfunction

function void rram_ctrl_sw_vseq::pre_randomize();
  import rram_ctrl_reg_pkg::BytesPerPage;

  if (m_ral == null) begin
    `uvm_fatal("no_ral", "Register model not set.")
  end

  for (int unsigned i = 0; i < NumRegions; i++) begin
    m_region_start_addrs[i] = m_ral.mp_region[i].base.get_mirrored_value() * BytesPerPage;
    m_region_byte_sizes[i] = (m_ral.mp_region[i].size.get_mirrored_value() + 1) * BytesPerPage;
    m_region_en[i] = (m_ral.mp_region_cfg[i].en.get_mirrored_value() == MuBi4True);
    m_region_rd_en[i] = (m_ral.mp_region_cfg[i].rd_en.get_mirrored_value() == MuBi4True);
    m_region_wr_en[i] = (m_ral.mp_region_cfg[i].wr_en.get_mirrored_value() == MuBi4True);
  end
  for (int unsigned i = 0; i < NumInfoPages; i++) begin
    m_page_en[i] = (m_ral.info_page_cfg[i].en.get_mirrored_value() == MuBi4True);
    m_page_rd_en[i] = (m_ral.info_page_cfg[i].rd_en.get_mirrored_value() == MuBi4True);
    m_page_wr_en[i] = (m_ral.info_page_cfg[i].wr_en.get_mirrored_value() == MuBi4True);
  end
endfunction

function void rram_ctrl_sw_vseq::do_print(uvm_printer printer);
  string op_name = (m_op.name() == "") ? "??" : m_op.name();
  string status_name = (m_status.name() == "") ? "??" : m_status.name();

  super.do_print(printer);

  printer.print_generic("m_op", "op_t", $bits(op_t), $sformatf("%0s (%0d)", op_name, m_op));

  printer.print_generic("m_partition", "partition_t", $bits(partition_t),
                        $sformatf("%0s (%0d)", m_partition.name(), m_partition));

  printer.print_field_int("m_num", m_num, 10);
  printer.print_field_int("m_addr", m_addr, 21);

  printer.print_generic("m_status", "uvm_status_e", $bits(m_status),
                        $sformatf("%0s (0x%0h)", status_name, m_status));

  // Only print out the configuration inferred from registers under UVM_FULL
  if (uvm_report_enabled(UVM_FULL, UVM_INFO, "config")) begin
    for (int unsigned i = 0; i < NumRegions; i++) begin
      printer.print_field_int($sformatf("m_region_start_addrs[%0d]", i),
                              m_region_start_addrs[i],
                              $bits(uvm_reg_addr_t),
                              UVM_HEX);
    end
    for (int unsigned i = 0; i < NumRegions; i++) begin
      printer.print_field_int($sformatf("m_region_byte_sizes[%0d]", i),
                              m_region_byte_sizes[i],
                              $bits(uvm_reg_addr_t),
                              UVM_HEX);
    end
    printer.print_field("m_region_en", m_region_en, NumRegions, UVM_BIN);
    printer.print_field("m_region_rd_en", m_region_rd_en, NumRegions, UVM_BIN);
    printer.print_field("m_region_wr_en", m_region_wr_en, NumRegions, UVM_BIN);

    printer.print_field("m_page_en", m_page_en, NumInfoPages, UVM_BIN);
    printer.print_field("m_page_rd_en", m_page_rd_en, NumInfoPages, UVM_BIN);
    printer.print_field("m_page_wr_en", m_page_wr_en, NumInfoPages, UVM_BIN);
  end

  printer.print_field_int("m_region_idx", m_region_idx, 32);
  printer.print_field_int("m_page_idx", m_page_idx, 32);
endfunction

task rram_ctrl_sw_vseq::pre_start();
  m_abort = 0;
  super.pre_start();
endtask

task rram_ctrl_sw_vseq::body();
  // At UVM_MEDIUM, print the configuration we're about to write
  if (uvm_report_enabled(UVM_MEDIUM, UVM_INFO, "sw_op")) begin
    `uvm_info("sw_op", "Randomized SW operation:", UVM_MEDIUM)
    print();
  end

  if (m_abort) begin
    m_status = UVM_NOT_OK;
    return;
  end

  // Start by writing ADDR
  m_ral.addr.start.set(m_addr);
  m_ral.addr.update(m_status);
  if (m_abort) m_status = UVM_NOT_OK;
  if (m_status != UVM_IS_OK) return;

  // Now write CONTROL
  m_ral.control.start.set(1);
  m_ral.control.op.set(m_op);
  m_ral.control.partition.set(m_partition);
  m_ral.control.num.set(m_num);
  m_ral.control.update(m_status);
  if (m_abort) m_status = UVM_NOT_OK;
  if (m_status != UVM_IS_OK) return;

  fork
    // Poll OP_STATUS.DONE, which will also return early if reset is asserted. Note that the "abort"
    // machinery isn't otherwise supported. To make that work without a reset, we'd need to
    // implement a spinwait sequence and port csr_utils_pkg::csr_spinwait to use it.
    csr_spinwait(.ptr(m_ral.op_status.done), .exp_data(1'b1));

    // Read from or write to the FIFO (depending on the operation chosen). Nothing to do here for a
    // Rewrite operation.
    case (m_op)
      Read: read_fifo();
      Write: write_fifo();
      default: begin end
    endcase
  join

  if (m_abort) m_status = UVM_NOT_OK;
endtask

function void rram_ctrl_sw_vseq::abort();
  m_abort = 1;
endfunction

function void rram_ctrl_sw_vseq::set_ral(rram_ctrl_core_reg_block ral);
  m_ral = ral;
endfunction

task rram_ctrl_sw_vseq::read_fifo();
  rram_ctrl_fifo_read_vseq vseq = rram_ctrl_fifo_read_vseq::type_id::create("vseq");
  vseq.set_window(m_ral.rd_fifo);
  vseq.m_num_words = m_num + 1;

  if (!vseq.randomize()) `uvm_fatal("rand_failed", "Failed to randomize FIFO read vseq.")

  fork : isolation_fork begin
    fork
      vseq.start(null);
      begin
        wait(m_abort);
        vseq.abort();
        m_status = UVM_NOT_OK;
        wait(0);
      end
    join_any
    disable fork;
  end join

  if (vseq.m_status != UVM_IS_OK) begin
    m_status = UVM_NOT_OK;
  end
endtask

task rram_ctrl_sw_vseq::write_fifo();
  rram_ctrl_fifo_write_vseq vseq = rram_ctrl_fifo_write_vseq::type_id::create("vseq");
  vseq.set_window(m_ral.wr_fifo);
  vseq.m_num_words = m_num + 1;

  if (!vseq.randomize()) `uvm_fatal("rand_failed", "Failed to randomize FIFO write vseq.")

  fork : isolation_fork begin
    fork
      vseq.start(null);
      begin
        wait(m_abort);
        vseq.abort();
        m_status = UVM_NOT_OK;
        wait(0);
      end
    join_any
    disable fork;
  end join

  if (vseq.m_status != UVM_IS_OK) begin
    m_status = UVM_NOT_OK;
  end
endtask

constraint rram_ctrl_sw_vseq::region_c {
  if (m_partition == Data) {
    // Choose a valid region index
    m_region_idx < NumRegions;
    // The region must be enabled
    m_region_en[m_region_idx];

    // A Read operation needs the region to have rd_en asserted
    (m_op == Read) -> m_region_rd_en[m_region_idx];
    // A Write operation needs the region to have wr_en asserted
    (m_op == Write) -> m_region_wr_en[m_region_idx];

    // The starting address for the operation needs to be after the start of the region
    m_region_start_addrs[m_region_idx] <= m_addr;

    // The top of the operation also needs to fit in the region. This is encoded by saying that the
    // first address after the operation minus the start of the region (which must be non-negative
    // because of the previous requirement) must be bounded above by the byte size of the region.
    (m_addr + 4 * (1 + m_num) -
     m_region_start_addrs[m_region_idx]) <= m_region_byte_sizes[m_region_idx];
  } else {
    m_region_idx == 0;
  }
}

constraint rram_ctrl_sw_vseq::page_c {
  if (m_partition == Data) {
    m_page_idx == 0;
  } else {
    // Choose a valid page index
    m_page_idx < NumInfoPages;

    // The page must be enabled
    m_page_en[m_page_idx];

    // A Read operation needs the page to have rd_en asserted
    (m_op == Read) -> m_page_rd_en[m_page_idx];
    // A Write operation needs the page to have wr_en asserted
    (m_op == Write) -> m_page_wr_en[m_page_idx];

    // The starting address for the operation needs to be after the start of the page
    m_page_idx * rram_ctrl_reg_pkg::BytesPerPage <= m_addr;

    // The top of the operation also needs to fit in the page. This is encoded by saying that the
    // first address after the operation minus the start of the page (which must be non-negative
    // because of the previous requirement) must be at most BytesPerPage.
    (m_addr + 4 * (1 + m_num) -
     m_page_idx * rram_ctrl_reg_pkg::BytesPerPage) <= rram_ctrl_reg_pkg::BytesPerPage;
  }
}
