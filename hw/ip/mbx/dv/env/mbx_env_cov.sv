// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

`ifdef MBX_ENV_COV_32B_ADDR_BINS
  `dv_fatal("Did not expected MBX_ENV_COV_32B_ADDR_BINS to be defined already.");
`else
  `define MBX_ENV_COV_32B_ADDR_BINS \
    bins less_than_1MiB = {[0:'hf_ffff]}; \
    bins between_1MiB_and_2_GiB = {['h10_0000:'h7fff_ffff]}; \
    bins between_2_and_4_GiB = {['h8000_0000:'hffff_ffff]};
`endif

// Check that we have seen all significant Inbound and Outbound mailbox addresses within
// the RoT address space so that there are no restrictions upon the physical memory map,
// e.g. MSB clear as well as MSB set.
covergroup mbx_mem_range_cg with function sample(bit [top_pkg::TL_AW-1:0] imbx_base,
                                                 bit [top_pkg::TL_AW-1:0] ombx_base);
  option.per_instance = 1;
  option.name = "mem_range_cg";

  cp_imbx_base: coverpoint imbx_base {
    `MBX_ENV_COV_32B_ADDR_BINS
  }

  cp_ombx_base: coverpoint ombx_base {
    `MBX_ENV_COV_32B_ADDR_BINS
  }

  cr_imbx_base_X_ombx_base: cross
    cp_imbx_base,
    cp_ombx_base;

endgroup

// Check that all RoT-side CONTROL bits have been stimulated/unstimulated.
covergroup mbx_rot_control_cg with function sample(bit abort,
                                                   bit error,
                                                   bit sys_async_msg);
  option.per_instance = 1;
  option.name = "rot_control_cg";

  cp_abort: coverpoint abort;
  cp_error: coverpoint error;
  cp_sys_async_msg: coverpoint sys_async_msg;

endgroup

// Check that all RoT-side STATUS indicators have been observed both asserted and deasserted.
covergroup mbx_rot_status_cg with function sample(bit busy,
                                                  bit sys_intr_state,
                                                  bit sys_intr_enable,
                                                  bit sys_async_enable);
  option.per_instance = 1;
  option.name = "rot_status_cg";

  cp_busy: coverpoint busy;
  cp_sys_intr_state: coverpoint sys_intr_state;
  cp_sys_intr_enable: coverpoint sys_intr_enable;
  cp_sys_async_enable: coverpoint sys_async_enable;

endgroup

// Check that all SoC-side CONTROL bits have been stimulated.
covergroup mbx_soc_control_cg with function sample(bit abort,
                                                   bit doe_intr_en,
                                                   bit doe_async_msg_en,
                                                   bit go);
  option.per_instance = 1;
  option.name = "soc_control_cg";

  cp_abort: coverpoint abort;
  cp_doe_intr_en: coverpoint doe_intr_en;
  cp_doe_async_msg_en: coverpoint doe_async_msg_en;
  cp_go: coverpoint go;

endgroup

// Ensure that we have observed all SoC-side STATUS indicators both asserted and deasserted.
covergroup mbx_soc_status_cg with function sample(bit busy,
                                                  bit doe_intr_status,
                                                  bit error,
                                                  bit doe_async_msg_status,
                                                  bit ready);
  option.per_instance = 1;
  option.name = "soc_status_cg";

  cp_busy: coverpoint busy;
  cp_doe_intr_status: coverpoint doe_intr_status;
  cp_error: coverpoint error;
  cp_doe_async_msg_status: coverpoint doe_async_msg_status;
  cp_ready: coverpoint ready;

endgroup

// Check that we have observed corner-case response lengths.
covergroup mbx_object_size_cg with function sample(bit [10:0] object_size);
  option.per_instance = 1;
  option.name = "object_size_cg";

  cp_object_size: coverpoint object_size {
    bins one_word = {1};
    bins below_256 = {[2:255]};
    bins above_256 = {[256:1023]};
    bins max_size = {1024};
  }

endgroup

// Collect coverage of the interrupt pin(s) on the SoC side.
// RoT-side interrupt pins are sampled in the CIP layer.
covergroup mbx_soc_intr_pins_cg (uint num_interrupts) with function sample(uint intr_pin,
                                                                           bit  intr_pin_value);
  cp_intr_pin: coverpoint intr_pin {
    bins all_pins[] = {[0:num_interrupts-1]};
  }
  cp_intr_pin_value: coverpoint intr_pin_value {
    bins values[] = {0, 1};
    bins transitions[] = (0 => 1), (1 => 0);
  }
  cp_intr_pins_all_values: cross cp_intr_pin, cp_intr_pin_value;
endgroup

// Check that different DOE interrupt message address/data values have been observed,
// on both register interfaces (RoT- and SoC-side).
//
// The DOE_INTR_MSG_ADDR and DOE_INTR_MSG_DATA registers are simply 32-bit channels
// presented from the SoC interface to the RoT interface; just ensure that each
// bit has independently been seen in both possible states.
covergroup mbx_doe_intr_msg_addr_cg(uint addr_width) with function sample(uint addr_bit,
                                                                          uint addr_bit_value);
  cp_addr_bit: coverpoint addr_bit {
    bins all_bits[] = {[0:addr_width-1]};
  }
  cp_addr_bit_value: coverpoint addr_bit_value {
    bins values[] = {0, 1};
    bins transitions[] = (0 => 1), (1 => 0);
  }
  cr_addr_bit_X_addr_bit_value: cross cp_addr_bit, cp_addr_bit_value;
endgroup

covergroup mbx_doe_intr_msg_data_cg(uint data_width) with function sample(uint data_bit,
                                                                          uint data_bit_value);
  cp_data_bit: coverpoint data_bit {
    bins all_bits[] = {[0:data_width-1]};
  }
  cp_data_bit_value: coverpoint data_bit_value {
    bins values[] = {0, 1};
    bins transitions[] = (0 => 1), (1 => 0);
  }
  cr_data_bit_X_data_bit_value: cross cp_data_bit, cp_data_bit_value;
endgroup

class mbx_env_cov extends cip_base_env_cov #(.CFG_T(mbx_env_cfg));
  `uvm_component_utils(mbx_env_cov)

  mbx_mem_range_cg mem_range_cg;
  mbx_rot_control_cg rot_control_cg;
  mbx_rot_status_cg rot_status_cg;
  mbx_soc_control_cg soc_control_cg;
  mbx_soc_status_cg soc_status_cg;
  mbx_object_size_cg object_size_cg;
  mbx_doe_intr_msg_addr_cg doe_intr_msg_addr_cg;
  mbx_doe_intr_msg_data_cg doe_intr_msg_data_cg;

  function new(string name, uvm_component parent);
    super.new(name, parent);
    mem_range_cg = new();
    rot_control_cg = new();
    rot_status_cg = new();
    soc_control_cg = new();
    soc_status_cg = new();
    object_size_cg = new();
    doe_intr_msg_addr_cg = new(top_pkg::TL_AW);
    doe_intr_msg_data_cg = new(top_pkg::TL_DW);
  endfunction : new

  virtual function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    // [or instantiate covergroups here]
    // Please instantiate sticky_intr_cov array of objects for all interrupts that are sticky
    // See cip_base_env_cov for details
  endfunction

endclass
