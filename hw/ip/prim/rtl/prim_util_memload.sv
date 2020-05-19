// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

/**
 * Memory loader for simulation
 *
 * Include this file in a memory primitive to load a memory array from
 * simulation.
 *
 * Requirements:
 * - A memory array named `mem`.
 * - A parameter `Width` giving the memory width (word size) in bit.
 * - A parameter `Depth` giving the memory depth in words.
 * - A parameter `MemInitFile` with a file path of a VMEM file to be loaded into
*    the memory if not empty.
 */

`ifdef VERILATOR
  // Task for loading 'mem' with SystemVerilog system task $readmemh()
  export "DPI-C" task simutil_verilator_memload;

  task simutil_verilator_memload;
    input string file;
    $readmemh(file, mem);
  endtask

  // Width must be a multiple of 32bit for this function to work
  // Note that the DPI export and function definition must both be in the same generate
  // context to get the correct name.
  if ((Width % 32) == 0) begin : gen_set_mem
    // Function for setting a specific element in |mem|
    // Returns 1 (true) for success, 0 (false) for errors.
    export "DPI-C" function simutil_verilator_set_mem;

    function int simutil_verilator_set_mem(input int index,
                                           input bit [Width-1:0] val);
      if (index >= Depth) begin
        return 0;
      end

      mem[index] = val;
      return 1;
    endfunction
  end else begin : gen_other
    // Function doesn't work unless Width % 32 so just return 0
    export "DPI-C" function simutil_verilator_set_mem;

    function int simutil_verilator_set_mem(input int index,
                                           input bit [Width-1:0] val);
      return 0;
    endfunction
  end
`endif

initial begin
  if (MemInitFile != "") begin : gen_meminit
      $display("Initializing memory %m from file '%s'.", MemInitFile);
      $readmemh(MemInitFile, mem);
  end
end
