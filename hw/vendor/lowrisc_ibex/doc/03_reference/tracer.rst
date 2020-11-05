.. _tracer:

Tracer
======

The module ``ibex_tracer`` can be used to create a log of the executed instructions.
It is used by ``ibex_core_tracing`` which forwards the `RVFI signals <https://github.com/SymbioticEDA/riscv-formal/blob/master/docs/rvfi.md>`_ to the tracer (see also :ref:`rvfi`).

Output file
-----------

All traced instructions are written to a log file.
By default, the log file is named ``trace_core_<HARTID>.log``, with ``<HARTID>`` being the 8 digit hart ID of the core being traced.

The file name base, defaulting to ``trace_core`` can be set using the ``ibex_tracer_file_base`` plusarg passed to the simulation.
For example, ``+ibex_tracer_file_base=ibex_my_trace`` will produce log files named ``ibex_my_trace_<HARTID>.log``.
The exact syntax of passing plusargs to a simulation depends on the simulator.

Disabling the tracer
--------------------

If the instruction log is not needed for a specific simulation run, the tracer can be disabled.

The plusarg ``ibex_tracer_enable`` controls the tracer.
The tracer is enabled by default.
To disable the tracer use ``ibex_tracer_enable=0`` with the correct plusarg syntax of the simulator.

Trace output format
-------------------

The trace output is in tab-separated columns.

1. **Time**: The current simulation time.
2. **Cycle**: The number of cycles since the last reset.
3. **PC**: The program counter
4. **Instr**: The executed instruction (base 16).
   32 bit wide instructions (8 hex digits) are uncompressed instructions, 16 bit wide instructions (4 hex digits) are compressed instructions.
5. **Decoded instruction**:
   The decoded (disassembled) instruction in a format equal to what objdump produces when calling it like ``objdump -Mnumeric -Mno-aliases -D``.

   - Unsigned numbers are given in hex (prefixed with ``0x``), signed numbers are given as decimal numbers.
   - Numeric register names are used (e.g. ``x1``).
   - Symbolic CSR names are used.
   - Jump/branch targets are given as absolute address if possible (PC + immediate).

6. **Register and memory contents**: For all accessed registers, the value before and after the instruction execution is given. Writes to registers are indicated as ``registername=value``, reads as ``registername:value``. For memory accesses, the address and the loaded and stored data are given.

.. code-block:: text

  Time          Cycle      PC       Instr    Decoded instruction Register and memory contents
            130         61 00000150 4481     c.li    x9,0        x9=0x00000000
            132         62 00000152 00008437 lui     x8,0x8      x8=0x00008000
            134         63 00000156 fff40413 addi    x8,x8,-1    x8:0x00008000  x8=0x00007fff
            136         64 0000015a 8c65     c.and   x8,x9       x8:0x00007fff  x9:0x00000000  x8=0x00000000
            142         67 0000015c c622     c.swsp  x8,12(x2)   x2:0x00002000  x8:0x00000000 PA:0x0000200c store:0x00000000  load:0xffffffff
