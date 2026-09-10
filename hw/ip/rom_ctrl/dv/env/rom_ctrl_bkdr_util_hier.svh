// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

`ifndef ROM_CTRL_BKDR_UTIL_HIER_SVH
`define ROM_CTRL_BKDR_UTIL_HIER_SVH

// Layout of the ROM memory array, relative to the `prim_rom` instance.
//
// A technology-specific `prim_rom` may compose the ROM from several memory macros, in which case
// there is no single array spanning the whole ROM.  These macros describe the layout to the
// testbenches, which pass them on to `rom_ctrl_bkdr_util`.  The implementation that is mapped in
// for a build supplies its own version of this file; see
// `hw/ip/rom_ctrl/dv/env/rom_ctrl_bkdr_util_hier.core`.
//
// This is the version for the open-source `prim_rom`, which is a single array named `mem`.

// Path from the `prim_rom` instance to the memory array of one tile.  All tiles have the same
// geometry, so `$size()` and `$bits()` of this array give the depth and the width of every tile.
`define ROM_MEM_TILE_PATH   mem

// Number of tiles the ROM is composed of.
`define ROM_MEM_NUM_TILES   1

// The `path` argument of `mem_bkdr_util::new` for the `prim_rom` instance `prim_rom_`.
//
// A single array gets no tile suffix from `get_full_path()`, so `path` has to be the array itself.
// An implementation with several tiles passes their common prefix, the `prim_rom` instance.
`define ROM_MEM_BKDR_PATH(prim_rom_) `DV_STRINGIFY(prim_rom_.`ROM_MEM_TILE_PATH)

// The `tiling_path` and `tiling_suffix_fmt_str` arguments of `mem_bkdr_util::new`.
//
// A single array needs no tile suffix, so `tiling_path` is empty, and `get_full_path()` then
// returns `path` unchanged without applying the format string.
`define ROM_MEM_TILING_PATH ""
`define ROM_MEM_TILING_FMT  ""

`endif // ROM_CTRL_BKDR_UTIL_HIER_SVH
