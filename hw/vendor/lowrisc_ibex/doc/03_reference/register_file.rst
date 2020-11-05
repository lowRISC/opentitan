.. _register-file:

Register File
=============
Source Files: :file:`rtl/ibex_register_file_ff.sv` :file:`rtl/ibex_register_file_fpga.sv` :file:`rtl/ibex_register_file_latch.sv`

Ibex has either 31 or 15 32-bit registers if the RV32E extension is disabled or enabled, respectively.
Register ``x0`` is statically bound to 0 and can only be read, it does not contain any sequential logic.

The register file has two read ports and one write port, register file data is available the same cycle a read is requested.
There is no write to read forwarding path so if one register is being both read and written the read will return the current value rather than the value being written.

There are three flavors of register file available, each having their own benefits and trade-offs.
The register file flavor is selected via the enumerated parameter ``RegFile`` defined in :file:`rtl/ibex_pkg.sv`.

Flip-Flop-Based Register File
-----------------------------

The flip-flop-based register file uses regular, positive-edge-triggered flip-flops to implement the registers.

This makes it the **first choice when simulating the design using Verilator**.

This implementation can be selected by setting the ``RegFile`` parameter to "ibex_pkg::RegFileFF".
It is the default selection.

FPGA Register File
------------------

The FPGA register file leverages synchronous-write / asynchronous-read RAM design elements, where available on FPGA targets.

For Xilinx FPGAs, synthesis results in an implementation using RAM32M primitives. Using this design with a Xilinx Artya7-100 FPGA conserves around 600 Logic LUTs and 1000 flip-flops at the expense of 48 LUTRAMs for the 31-entry register file as compared to the flip-flop-based register file.

This makes it the **first choice for FPGA synthesis**.

To select the FPGA register file, set the ``RegFile`` parameter to "ibex_pkg::RegFileFPGA".

Latch-Based Register File
-------------------------

The latch-based register file uses level-sensitive latches to implement the registers.

This allows for significant area savings compared to an implementation using regular flip-flops and thus makes the latch-based register file the **first choice for ASIC implementations**.
Simulation of the latch-based register file is possible using commercial tools.

.. note:: The latch-based register file cannot be simulated using Verilator.

The latch-based register file can also be used for FPGA synthesis, but this is not recommended as FPGAs usually do not well support latches.

To select the latch-based register file, set the ``RegFile`` parameter to "ibex_pkg::RegFileLatch".
In addition, a technology-specific clock gating cell must be provided to keep the clock inactive when the latches are not written.
This cell must be wrapped in a module called ``prim_clock_gating``.
For more information regarding the clock gating cell, checkout :ref:`getting-started`.

.. note:: The latch-based register file requires the gated clock to be enabled in the cycle after the write enable ``we_a_i`` signal was set high.
   This can be achieved by latching ``we_a_i`` in the clock gating cell during the low phase of ``clk_i``.

   The resulting behavior of the latch-based register file is visualized in :numref:`timing`.
   The input data ``wdata_a_i`` is sampled into a flip-flop-based register ``wdata_a_q`` using ``clk_int``.
   The actual latch-based registers ``mem[1]`` and ``mem[2]`` are transparent during high phases of ``mem_clk[1]`` and ``mem_clk[2]``, respectively.
   Their content is sampled from ``wdata_a_q`` on falling edges of these clocks.

   .. wavedrom::
      :name: timing
      :caption: Latch-based register file operation

      {"signal":
        [
          {"name": "clk_i",      "wave": "hlhlhlhl"},
          {"name": "we_a_i",     "wave": "0.1...0."},
          {"name": "waddr_a_i",  "wave": "xx=.=.xx", "data": ["1","2"]},
          {"name": "wdata_a_i",  "wave": "xx=.=.xx", "data": ["Data1","Data2"]},
          {"name": "clk_int",    "wave": "0...HlHl"},
          {"name": "wdata_a_q",  "wave": "xxxx=.=.", "data": ["Data1", "Data2"]},
          {"name": "mem_clk[1]", "wave": "0...hL.."},
          {"name": "mem[1]",     "wave": "xxxx=...", "data": ["Data1"]},
          {"name": "mem_clk[2]", "wave": "0.....hL"},
          {"name": "mem[2]",     "wave": "xxxxxx=.", "data": ["Data2"]}
        ],
        "config": { "hscale": 2 }
       }
