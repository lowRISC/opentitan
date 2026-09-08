// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

`ifndef MEM_BKDR_UTIL_HIER_SVH
`define MEM_BKDR_UTIL_HIER_SVH

// Layout of every `prim_ram_1p`-backed memory's array(s), relative to that memory's own
// `..._MEM_INST_HIER` macro (defined in chip_hier_macros.svh, one per memory).
//
// A technology-specific `prim_ram_1p` may compose a memory from several vendor macros whose own
// internal storage folds several logical words into each physical HDL row (as opposed to a flat,
// one-physical-row-per-logical-word array), and/or bit-slices a wide logical word across several
// macro instances sharing one address (as opposed to one macro covering the whole word). These
// macros describe that layout to the testbench, which passes it on to `mem_bkdr_util`/
// `sram_ctrl_bkdr_util`. The implementation mapped in for a build supplies its own version of this
// file. See `mem_bkdr_util_hier.core`.
//
// This is the version for the open-source `prim_ram_1p`: every memory below is a single flat array
// named `mem` (no folding, no bit-slicing, not tiled).

// sram_ctrl_main. See RAM_MAIN_MEM_INST_HIER in chip_hier_macros.svh.
`define RAM_MAIN_MEM_TILE_PATH mem
`define RAM_MAIN_MEM_NUM_TILES  1
`define RAM_MAIN_MEM_TILE_DEPTH $size(`RAM_MAIN_MEM_INST_HIER.`RAM_MAIN_MEM_TILE_PATH)
`define RAM_MAIN_MEM_WORDS_PER_ROW 1
`define RAM_MAIN_MEM_BKDR_PATH(prim_ram_1p_) `DV_STRINGIFY(prim_ram_1p_.`RAM_MAIN_MEM_TILE_PATH)
`define RAM_MAIN_MEM_TILING_PATH ""
`define RAM_MAIN_MEM_TILING_FMT  ""

// sram_ctrl_ret_aon. Not tiled, so depth equals tile depth and there is no tiling path/format.
`define RAM_RET_MEM_TILE_PATH      mem
`define RAM_RET_MEM_DEPTH          $size(`RAM_RET_MEM_INST_HIER.`RAM_RET_MEM_TILE_PATH)
`define RAM_RET_MEM_WORDS_PER_ROW  1

// rv_core_ibex icache way 0/1 tag and data arrays. All four are single, untiled arrays.
`define ICACHE_TAG_MEM_TILE_PATH      mem
`define ICACHE_TAG_MEM_WORDS_PER_ROW  1
`define ICACHE0_TAG_MEM_DEPTH         $size(`ICACHE0_TAG_MEM_INST_HIER.`ICACHE_TAG_MEM_TILE_PATH)
`define ICACHE1_TAG_MEM_DEPTH         $size(`ICACHE1_TAG_MEM_INST_HIER.`ICACHE_TAG_MEM_TILE_PATH)
`define ICACHE_DATA_MEM_TILE_PATH     mem
`define ICACHE_DATA_MEM_WORDS_PER_ROW 1
`define ICACHE0_DATA_MEM_DEPTH        $size(`ICACHE0_DATA_MEM_INST_HIER.`ICACHE_DATA_MEM_TILE_PATH)
`define ICACHE1_DATA_MEM_DEPTH        $size(`ICACHE1_DATA_MEM_INST_HIER.`ICACHE_DATA_MEM_TILE_PATH)

// otbn imem. Not tiled.
`define OTBN_IMEM_MEM_TILE_PATH      mem
`define OTBN_IMEM_MEM_DEPTH          $size(`OTBN_IMEM_MEM_INST_HIER.`OTBN_IMEM_MEM_TILE_PATH)
`define OTBN_IMEM_MEM_WORDS_PER_ROW  1

// otbn dmem. A single flat array already covers the full (wide) logical word, so it needs no
// bit-slicing: `OTBN_DMEM_MEM_NUM_BIT_SLICES` is 1, and the bit-slice tiling path/format are unused
// (mirroring how an un-tiled memory leaves `..._TILING_PATH` empty).
`define OTBN_DMEM_MEM_TILE_PATH          mem
`define OTBN_DMEM_MEM_DEPTH              $size(`OTBN_DMEM_MEM_INST_HIER.`OTBN_DMEM_MEM_TILE_PATH)
`define OTBN_DMEM_MEM_WORDS_PER_ROW      1
`define OTBN_DMEM_MEM_BKDR_PATH(prim_ram_1p_) `DV_STRINGIFY(prim_ram_1p_.`OTBN_DMEM_MEM_TILE_PATH)
`define OTBN_DMEM_MEM_NUM_BIT_SLICES     1
`define OTBN_DMEM_MEM_BIT_SLICE_TILING_PATH ""
`define OTBN_DMEM_MEM_BIT_SLICE_TILING_FMT  ""

// usbdev buffer memory. Not tiled.
`define USBDEV_BUF_MEM_TILE_PATH      mem
`define USBDEV_BUF_MEM_DEPTH          $size(`USBDEV_BUF_MEM_INST_HIER.`USBDEV_BUF_MEM_TILE_PATH)
`define USBDEV_BUF_MEM_WORDS_PER_ROW  1

`endif // MEM_BKDR_UTIL_HIER_SVH
