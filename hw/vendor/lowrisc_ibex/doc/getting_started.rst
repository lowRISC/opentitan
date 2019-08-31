.. _getting-started:

Getting Started with Ibex
=========================

This page discusses initial steps and requirements to start using Ibex in your design.

Register File
-------------

Ibex comes with two different register file implementations.
Depending on the target technology, either the implementation in ``ibex_register_file_ff.sv`` or the one in ``ibex_register_file_latch.sv`` should be selected.
For more information about the two register file implementations and their trade-offs, check out :ref:`register-file`.

Clock Gating Cell
-----------------

Ibex requires clock gating cells.
This cells are usually specific to the selected target technology and thus not provided as part of the RTL design.
It is assumed that the clock gating cell is wrapped in a module called ``prim_clock_gating`` that has the following ports:

* ``clk_i``: Clock Input
* ``en_i``: Clock Enable Input
* ``test_en_i``: Test Enable Input (activates the clock even though ``en_i`` is not set)
* ``clk_o``: Gated Clock Output

Inside Ibex, clock gating cells are used both in ``ibex_core.sv`` and ``ibex_register_file_latch.sv``.
For more information on the expected behavior of the clock gating cell when using the latch-based register file check out :ref:`register-file`.
