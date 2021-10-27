// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Imports for the functions defined in otbn_model.h. There are documentation comments explaining
// what the functions do there.
`ifndef SYNTHESIS
package otbn_model_pkg;

  import otbn_pkg::WLEN;

  import "DPI-C" context function chandle otbn_model_init(string mem_scope,
                                                          string design_scope,
                                                          int unsigned imem_words,
                                                          int unsigned dmem_words);

  import "DPI-C" function void otbn_model_destroy(chandle model);

  import "DPI-C" function void edn_model_flush(chandle model);

  import "DPI-C" function void edn_model_rnd_step(chandle model,
                                                  logic [31:0] edn_rnd_data);

  import "DPI-C" function void edn_model_urnd_step(chandle model,
                                                   logic [31:0] edn_urnd_data);

  import "DPI-C" function
    void edn_model_urnd_cdc_done(chandle model);

  import "DPI-C" function
    void edn_model_rnd_cdc_done(chandle model);

  import "DPI-C" context function
    int unsigned otbn_model_step(chandle          model,
                                 logic            start,
                                 int unsigned     model_state,
                                 inout bit [7:0]  status,
                                 inout bit [31:0] insn_cnt,
                                 inout bit [31:0] err_bits,
                                 inout bit [31:0] stop_pc);

  import "DPI-C" context function int otbn_model_invalidate_imem(chandle model);

  import "DPI-C" function void otbn_model_reset(chandle model);

  import "DPI-C" function void otbn_take_loop_warps(chandle model, chandle memutil);

endpackage
`endif // SYNTHESIS
