.. _performance-counters:

Performance Counters
====================

Ibex implements performance counters according to the RISC-V Privileged Specification, version 1.11 (see Hardware Performance Monitor, Section 3.1.11).
The performance counters are placed inside the Control and Status Registers (CSRs) and can be accessed with the ``CSRRW(I)`` and ``CSRRS/C(I)`` instructions.

Ibex implements the clock cycle counter ``mcycle(h)``, the retired instruction counter ``minstret(h)``, as well as the 29 event counters ``mhpmcounter3(h)`` - ``mhpmcounter31(h)`` and the corresponding event selector CSRs ``mhpmevent3`` - ``mhpmevent31``, and the ``mcountinhibit`` CSR to individually enable/disable the counters.
``mcycle(h)`` and ``minstret(h)`` are always available and 64 bit wide.
The ``mhpmcounter`` performance counters are optional (unavailable by default) and parametrizable in width.

Event Selector
--------------

The following events can be monitored using the performance counters of Ibex.

+--------------+------------------+---------------------------------------------------------+
| Event ID/Bit | Event Name       | Event Description                                       |
+==============+==================+=========================================================+
|            0 | NumCycles        | Number of cycles                                        |
+--------------+------------------+---------------------------------------------------------+
|            2 | NumInstrRet      | Number of instructions retired                          |
+--------------+------------------+---------------------------------------------------------+
|            3 | NumCyclesLSU     | Number of cycles waiting for data memory                |
+--------------+------------------+---------------------------------------------------------+
|            4 | NumCyclesIF      | Cycles waiting for instruction fetches, i.e., number of |
|              |                  | instructions wasted due to non-ideal caching            |
+--------------+------------------+---------------------------------------------------------+
|            5 | NumLoads         | Number of data memory loads. Misaligned accesses are    |
|              |                  | counted as two accesses                                 |
+--------------+------------------+---------------------------------------------------------+
|            6 | NumStores        | Number of data memory stores. Misaligned accesses are   |
|              |                  | counted as two accesses                                 |
+--------------+------------------+---------------------------------------------------------+
|            7 | NumJumps         | Number of unconditional jumps (j, jal, jr, jalr)        |
+--------------+------------------+---------------------------------------------------------+
|            8 | NumBranches      | Number of branches (conditional)                        |
+--------------+------------------+---------------------------------------------------------+
|            9 | NumBranchesTaken | Number of taken branches (conditional)                  |
+--------------+------------------+---------------------------------------------------------+
|           10 | NumInstrRetC     | Number of compressed instructions retired               |
+--------------+------------------+---------------------------------------------------------+
|           11 | NumCyclesMulWait | Cycles waiting for multiply to complete                 |
+--------------+------------------+---------------------------------------------------------+
|           12 | NumCyclesDivWait | Cycles waiting for divide to complete                   |
+--------------+------------------+---------------------------------------------------------+

The event selector CSRs ``mhpmevent3`` - ``mhpmevent31`` define which of these events are counted by the event counters ``mhpmcounter3(h)`` - ``mhpmcounter31(h)``.
If a specific bit in an event selector CSR is set to 1, this means that events with this ID are being counted by the counter associated with that selector CSR.
If an event selector CSR is 0, this means that the corresponding counter is not counting any event.

Controlling the counters from software
--------------------------------------

By default, all available counters are enabled after reset.
They can be individually enabled/disabled by overwriting the corresponding bit in the ``mcountinhibit`` CSR at address ``0x320`` as described in the RISC-V Privileged Specification, version 1.11 (see Machine Counter-Inhibit CSR, Section 3.1.13).
In particular, to enable/disable ``mcycle(h)``, bit 0 must be written. For ``minstret(h)``, it is bit 2. For event counter ``mhpmcounterX(h)``, it is bit X.

The lower 32 bits of all counters can be accessed through the base register, whereas the upper 32 bits are accessed through the ``h``-register.
Reads to all these registers are non-destructive.

Parametrization at synthesis time
---------------------------------

The ``mcycle(h)`` and ``minstret(h)`` counters are always available and 64 bit wide.

The event counters ``mhpmcounter3(h)`` - ``mhpmcounter31(h)`` are parametrizable.
Their width can be parametrized between 1 and 64 bit through the ``WidthMHPMCounters`` parameter, which defaults to 40 bit wide counters.

The number of available event counters ``mhpmcounterX(h)`` can be controlled via the ``NumMHPMCounters`` parameter.
By default (``NumMHPMCounters`` set to 0), no counters are available to software.
Set ``NumMHPMCounters`` to a value between 1 and 8 to make the counters ``mhpmcounter3(h)`` - ``mhpmcounter10(h)`` available as listed below.
Setting ``NumMHPMCounters`` to values larger than 8 does not result in any more performance counters.

Unavailable counters always read 0.

The association of events with the ``mphmcounter`` registers is hardwired as listed in the following table.

+----------------------+----------------+--------------+------------------+
| Event Counter        | CSR Address    | Event ID/Bit | Event Name       |
+======================+================+==============+==================+
| ``mcycle(h)``        | 0xB00 (0xB80)  |            0 | NumCycles        |
+----------------------+----------------+--------------+------------------+
| ``minstret(h)``      | 0xB02 (0xB82)  |            2 | NumInstrRet      |
+----------------------+----------------+--------------+------------------+
| ``mhpmcounter3(h)``  | 0xB03 (0xB83)  |            3 | NumCyclesLSU     |
+----------------------+----------------+--------------+------------------+
| ``mhpmcounter4(h)``  | 0xB04 (0xB84)  |            4 | NumCyclesIF      |
|                      |                |              |                  |
+----------------------+----------------+--------------+------------------+
| ``mhpmcounter5(h)``  | 0xB05 (0xB85)  |            5 | NumLoads         |
|                      |                |              |                  |
+----------------------+----------------+--------------+------------------+
| ``mhpmcounter6(h)``  | 0xB06 (0xB86)  |            6 | NumStores        |
|                      |                |              |                  |
+----------------------+----------------+--------------+------------------+
| ``mhpmcounter7(h)``  | 0xB07 (0xB87)  |            7 | NumJumps         |
+----------------------+----------------+--------------+------------------+
| ``mhpmcounter8(h)``  | 0xB08 (0xB88)  |            8 | NumBranches      |
+----------------------+----------------+--------------+------------------+
| ``mhpmcounter9(h)``  | 0xB09 (0xB89)  |            9 | NumBranchesTaken |
+----------------------+----------------+--------------+------------------+
| ``mhpmcounter10(h)`` | 0xB0A (0xB8A)  |           10 | NumInstrRetC     |
+----------------------+----------------+--------------+------------------+
| ``mhpmcounter11(h)`` | 0xB0B (0xB8B)  |           11 | NumCyclesMulWait |
+----------------------+----------------+--------------+------------------+
| ``mhpmcounter12(h)`` | 0xB0C (0xB8C)  |           12 | NumCyclesDivWait |
+----------------------+----------------+--------------+------------------+

Similarly, the event selector CSRs are hardwired as follows.
The remaining event selector CSRs are tied to 0, i.e., no events are counted by the corresponding counters.

+----------------------+-------------+-------------+--------------+
| Event Selector       | CSR Address | Reset Value | Event ID/Bit |
+======================+=============+=============+==============+
| ``mhpmevent3(h)``    | 0x323       | 0x0000_0008 |            3 |
+----------------------+-------------+-------------+--------------+
| ``mhpmevent4(h)``    | 0x324       | 0x0000_0010 |            4 |
+----------------------+-------------+-------------+--------------+
| ``mhpmevent5(h)``    | 0x325       | 0x0000_0020 |            5 |
+----------------------+-------------+-------------+--------------+
| ``mhpmevent6(h)``    | 0x326       | 0x0000_0040 |            6 |
+----------------------+-------------+-------------+--------------+
| ``mhpmevent7(h)``    | 0x327       | 0x0000_0080 |            7 |
+----------------------+-------------+-------------+--------------+
| ``mhpmevent8(h)``    | 0x328       | 0x0000_0100 |            8 |
+----------------------+-------------+-------------+--------------+
| ``mhpmevent9(h)``    | 0x329       | 0x0000_0200 |            9 |
+----------------------+-------------+-------------+--------------+
| ``mhpmevent10(h)``   | 0x32A       | 0x0000_0400 |           10 |
+----------------------+-------------+-------------+--------------+
| ``mhpmevent11(h)``   | 0x32B       | 0x0000_0800 |           11 |
+----------------------+-------------+-------------+--------------+
| ``mhpmevent12(h)``   | 0x32C       | 0x0000_1000 |           12 |
+----------------------+-------------+-------------+--------------+

FPGA Targets
------------

For FPGA targets the performance counters constitute a particularily large structure.
Implementing the maximum 29 event counters 32, 48 and 64 bit wide results in relative logic utilizations of the core of 100%, 111% and 129% respectively.
The relative numbers of flip-flops are 100%, 125% and 150%.
It is recommended to implement event counters of 32 bit width where possible.

For Xilinx FPGA devices featuring the `DSP48E1` DSP slice or similar, counter logic can be absorbed into the DSP slice for widths up to 48 bits.
The resulting relative logic utilizations with respect to the non-DSP 32 bit counter implementation are 83% and 89% respectively for 32 and 48 bit DSP counters.
This comes at the expense of 1 DSP slice per counter.
For 32 bit counters only, the corresponding flip-flops can be incorporated into the DSP's output pipeline register, resulting in a reduction of the number of flip-flops to 50%.
In order to infer DSP slices for performance counters, define the preprocessor variable ``FPGA_XILINX``.
