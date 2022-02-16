// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

package cip_base_pkg;
  // dep packages
  import uvm_pkg::*;
  import bus_params_pkg::*;
  import dv_utils_pkg::*;
  import csr_utils_pkg::*;
  import dv_lib_pkg::*;
  import dv_base_reg_pkg::*;
  import tlul_pkg::*;
  import tl_agent_pkg::*;
  import alert_esc_agent_pkg::*;
  import push_pull_agent_pkg::*;
  import mem_model_pkg::*;
  import prim_mubi_pkg::*;
  import sec_cm_pkg::*;

  // macro includes
  `include "uvm_macros.svh"
  `include "dv_macros.svh"
  `include "cip_macros.svh"

  // package variables
  string msg_id = "cip_base_pkg";
  parameter uint EDN_BUS_WIDTH = 32;
  parameter uint EDN_DATA_WIDTH = EDN_BUS_WIDTH + 1; // 32 bits bus data, 1 bit fips
  parameter uint MAX_TL_ECC_ERRORS = 3;

  typedef enum {
    err_update,
    err_storage
  } shadow_reg_alert_e;

  typedef enum bit [1:0] {
    TlIntgErrNone,
    TlIntgErrCmd,
    TlIntgErrData,
    TlIntgErrBoth  // Inject errors in both command and data.
  } tl_intg_err_e;

  typedef class cip_tl_seq_item;
  typedef virtual rst_shadowed_if rst_shadowed_vif;

  // functions
  function automatic tl_intg_err_e get_tl_intg_err_type(bit is_cmd_ok, bit is_data_ok);
    case ({is_cmd_ok, is_data_ok})
      2'b11: return TlIntgErrNone;
      2'b01: return TlIntgErrCmd;
      2'b10: return TlIntgErrData;
      2'b00: return TlIntgErrBoth;
      default: ;
    endcase
  endfunction

  // get mem attributes to know what error cases can be triggered
  function automatic void get_all_mem_attrs(input dv_base_reg_block reg_block,
                                            output bit has_mem_byte_access_err,
                                            output bit has_wo_mem,
                                            output bit has_ro_mem);
    uvm_mem mems[$];
    reg_block.get_memories(mems);

    foreach (mems[i]) begin
      dv_base_mem dv_mem;
      `downcast(dv_mem, mems[i], , , msg_id)
      if (!dv_mem.get_mem_partial_write_support() && dv_mem.get_access() == "RO") begin
        has_mem_byte_access_err = 1;
      end
      if (dv_mem.get_access() == "WO") has_wo_mem = 1;
      if (dv_mem.get_access() == "RO") has_ro_mem = 1;
    end
  endfunction

  // Create functions that return a random value for the mubi type variable, based on weight
  // settings.
  //
  // The function is `get_rand_mubi4|8|16_val(t_weight, f_weight, other_weight)`
  // t_weight: randomization weight of the value True
  // f_weight: randomization weight of the value False
  // other_weight: collective randomization weight of all values other than True or False
  `define _DV_MUBI_RAND_VAL(WIDTH_)                                         \
    function automatic mubi``WIDTH_``_t get_rand_mubi``WIDTH_``_val(        \
        int t_weight = 2, int f_weight = 2, int other_weight = 1);          \
      bit[WIDTH_-1:0] val;                                                  \
      `DV_CHECK_STD_RANDOMIZE_WITH_FATAL(val,                               \
          `DV_MUBI``WIDTH_``_DIST(val, t_weight, f_weight, other_weight), , \
                                         msg_id)                            \
      return mubi``WIDTH_``_t'(val);                                        \
    endfunction

  // Create function - get_rand_mubi4_val.
  `_DV_MUBI_RAND_VAL(4)

  // Create function - get_rand_mubi8_val.
  `_DV_MUBI_RAND_VAL(8)

  // Create function - get_rand_mubi12_val.
  `_DV_MUBI_RAND_VAL(12)

  // Create function - get_rand_mubi16_val.
  `_DV_MUBI_RAND_VAL(16)

  `undef _DV_MUBI_RAND_VAL

  function automatic lc_ctrl_pkg::lc_tx_t get_rand_lc_tx_val(int t_weight = 2,
                                                             int f_weight = 2,
                                                             int other_weight = 1);
    bit[3:0] val;
    `DV_CHECK_STD_RANDOMIZE_WITH_FATAL(val,
        `DV_LC_TX_DIST(val, t_weight, f_weight, other_weight), , msg_id)

    return lc_ctrl_pkg::lc_tx_t'(val);
  endfunction

  // package sources
  // base env
  `include "cip_base_env_cfg.sv"
  `include "cip_base_env_cov.sv"
  `include "cip_base_virtual_sequencer.sv"
  `include "cip_base_scoreboard.sv"
  `include "cip_base_env.sv"

  // sequences
  `include "cip_seq_list.sv"

  // tests
  `include "cip_base_test.sv"

endpackage
