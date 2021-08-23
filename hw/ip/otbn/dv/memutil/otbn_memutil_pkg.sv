// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Imports for the functions defined in otbn_memutil.h. There are documentation comments explaining
// what the functions do there.
`ifndef SYNTHESIS
package otbn_memutil_pkg;

  import "DPI-C" function chandle OtbnMemUtilMake(string top_scope);

  import "DPI-C" function void OtbnMemUtilFree(chandle mem_util);

  import "DPI-C" context function bit OtbnMemUtilLoadElf(chandle mem_util, string elf_path);

  import "DPI-C" function bit OtbnMemUtilStageElf(chandle mem_util, string elf_path);

  import "DPI-C" function int OtbnMemUtilGetSegCount(chandle mem_util, bit is_imem);

  import "DPI-C" function bit OtbnMemUtilGetSegInfo(chandle mem_util, bit is_imem, int seg_idx,
                                                    output bit [31:0] seg_off,
                                                    output bit [31:0] seg_size);

  import "DPI-C" function bit OtbnMemUtilGetSegData(chandle mem_util, bit is_imem, int word_off,
                                                    output bit [31:0] data_value);

  import "DPI-C" function int OtbnMemUtilGetExpEndAddr(chandle mem_util);

  import "DPI-C" function bit OtbnMemUtilGetLoopWarp(chandle           mem_util,
                                                     bit [31:0]        addr,
                                                     bit [31:0]        from_cnt,
                                                     output bit [31:0] to_cnt);

  import "DPI-C" function int OtbnMemUtilGetNumLoopWarps(chandle mem_util);

  import "DPI-C" function void OtbnMemUtilGetLoopWarpByIndex(chandle           mem_util,
                                                             int               idx,
                                                             output bit [31:0] addr,
                                                             output bit [31:0] from_cnt,
                                                             output bit [31:0] to_cnt);
endpackage
`endif // SYNTHESIS
