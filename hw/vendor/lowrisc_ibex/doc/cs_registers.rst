.. _cs-registers:

Control and Status Registers
============================

Ibex implements all the Control and Status Registers (CSRs) listed in the following table according to the RISC-V Privileged Specification, version 1.11.

+---------+--------------------+--------+-----------------------------------------------+
| Address |   Name             | Access | Description                                   |
+=========+====================+========+===============================================+
|  0x300  | ``mstatus``        | WARL   | Machine Status                                |
+---------+--------------------+--------+-----------------------------------------------+
|  0x301  | ``misa``           | WARL   | Machine ISA and Extensions                    |
+---------+--------------------+--------+-----------------------------------------------+
|  0x304  | ``mie``            | WARL   | Machine Interrupt Enable Register             |
+---------+--------------------+--------+-----------------------------------------------+
|  0x305  | ``mtvec``          | WARL   | Machine Trap-Vector Base Address              |
+---------+--------------------+--------+-----------------------------------------------+
|  0x320  | ``mcountinhibit``  | RW     | Machine Counter-Inhibit Register              |
+---------+--------------------+--------+-----------------------------------------------+
|  0x323  | ``mhpmevent3``     | WARL   | Machine Performance-Monitoring Event Selector |
+---------+--------------------+--------+-----------------------------------------------+
|     .             .               .                    .                              |
+---------+--------------------+--------+-----------------------------------------------+
|  0x33F  | ``mhpmevent31``    | WARL   | Machine Performance-Monitoring Event Selector |
+---------+--------------------+--------+-----------------------------------------------+
|  0x340  | ``mscratch``       | RW     | Machine Scratch Register                      |
+---------+--------------------+--------+-----------------------------------------------+
|  0x341  | ``mepc``           | WARL   | Machine Exception Program Counter             |
+---------+--------------------+--------+-----------------------------------------------+
|  0x342  | ``mcause``         | WLRL   | Machine Cause Register                        |
+---------+--------------------+--------+-----------------------------------------------+
|  0x343  | ``mtval``          | WARL   | Machine Trap Value Register                   |
+---------+--------------------+--------+-----------------------------------------------+
|  0x344  | ``mip``            | R      | Machine Interrupt Pending Register            |
+---------+--------------------+--------+-----------------------------------------------+
|  0x3A0  | ``pmpcfg0``        | WARL   | PMP Configuration Register                    |
+---------+--------------------+--------+-----------------------------------------------+
|     .             .               .                    .                              |
+---------+--------------------+--------+-----------------------------------------------+
|  0x3A3  | ``pmpcfg3``        | WARL   | PMP Configuration Register                    |
+---------+--------------------+--------+-----------------------------------------------+
|  0x3B0  | ``pmpaddr0``       | WARL   | PMP Address Register                          |
+---------+--------------------+--------+-----------------------------------------------+
|     .             .               .                    .                              |
+---------+--------------------+--------+-----------------------------------------------+
|  0x3BF  | ``pmpaddr15``      | WARL   | PMP Address Register                          |
+---------+--------------------+--------+-----------------------------------------------+
|  0x7B0  | ``dcsr``           | RW     | Debug Control and Status Register             |
+---------+--------------------+--------+-----------------------------------------------+
|  0x7B1  | ``dpc``            | RW     | Debug PC                                      |
+---------+--------------------+--------+-----------------------------------------------+
|  0x7B2  | ``dscratch0``      | RW     | Debug Scratch Register 0                      |
+---------+--------------------+--------+-----------------------------------------------+
|  0x7B3  | ``dscratch1``      | RW     | Debug Scratch Register 1                      |
+---------+--------------------+--------+-----------------------------------------------+
|  0xB00  | ``mcycle``         | RW     | Machine Cycle Counter                         |
+---------+--------------------+--------+-----------------------------------------------+
|  0xB02  | ``minstret``       | RW     | Machine Instructions-Retired Counter          |
+---------+--------------------+--------+-----------------------------------------------+
|  0xB03  | ``mhpmcounter3``   | WARL   | Machine Performance-Monitoring Counter        |
+---------+--------------------+--------+-----------------------------------------------+
|     .             .               .                    .                              |
+---------+--------------------+--------+-----------------------------------------------+
|  0xB1F  | ``mhpmcounter31``  | WARL   | Machine Performance-Monitoring Counter        |
+---------+--------------------+--------+-----------------------------------------------+
|  0xB80  | ``mcycleh``        | RW     | Upper 32 bits of ``mcycle``                   |
+---------+--------------------+--------+-----------------------------------------------+
|  0xB82  | ``minstreth``      | RW     | Upper 32 bits of ``minstret``                 |
+---------+--------------------+--------+-----------------------------------------------+
|  0xB83  | ``mhpmcounter3h``  | WARL   | Upper 32 bits of ``mhmpcounter3``             |
+---------+--------------------+--------+-----------------------------------------------+
|     .             .               .                    .                              |
+---------+--------------------+--------+-----------------------------------------------+
|  0xB9F  | ``mhpmcounter31h`` | WARL   | Upper 32 bits of ``mhmpcounter31``            |
+---------+--------------------+--------+-----------------------------------------------+
|  0xF14  | ``mhartid``        | R      | Hardware Thread ID                            |
+---------+--------------------+--------+-----------------------------------------------+

See the :ref:`performance-counters` documentation for a description of the counter registers.


Machine Status (mstatus)
------------------------

CSR Address: ``0x300``

Reset Value: ``0x0000_1800``

+-------+-----+---------------------------------------------------------------------------------+
| Bit#  | R/W | Description                                                                     |
+-------+-----+---------------------------------------------------------------------------------+
| 12:11 | R   | **MPP:** Statically 2'b11 and cannot be altered (read-only).                    |
+-------+-----+---------------------------------------------------------------------------------+
| 7     | RW  | **Previous Interrupt Enable (MPIE)**, i.e., before entering exception handling. |
+-------+-----+---------------------------------------------------------------------------------+
| 3     | RW  | **Interrupt Enable (MIE):** If set to 1'b1, interrupts are globally enabled.    |
+-------+-----+---------------------------------------------------------------------------------+

When an exception is encountered, ``mstatus``.MPIE will be set to ``mstatus``.MIE.
When the MRET instruction is executed, the value of MPIE will be stored back to ``mstatus``.MIE.

If you want to enable interrupt handling in your exception handler, set ``mstatus``.MIE to 1'b1 inside your handler code.


Machine ISA Register (misa)
---------------------------

CSR Address: ``0x301``

``misa`` is a WARL register which describes the ISA supported by the hart.
On Ibex, ``misa`` is hard-wired, i.e. it will remain unchanged after any write.


Machine Interrupt Enable Register (mie)
---------------------------------------

CSR Address: ``0x304``

Reset Value: ``0x0000_0000``

``mie`` is a WARL register which allows to individually enable/disable local interrupts.
After reset, all interrupts are disabled.

+-------+--------------------------------------------------------------------------------------+
| Bit#  | Interrupt                                                                            |
+-------+--------------------------------------------------------------------------------------+
| 30:16 | Machine Fast Interrupt Enables: Set bit x+16 to enable                               |
|       | fast interrupt ``irq_fast_i[x]``.                                                    |
+-------+--------------------------------------------------------------------------------------+
| 11    | **Machine External Interrupt Enable (MEIE):** If set, ``irq_external_i`` is enabled. |
+-------+--------------------------------------------------------------------------------------+
| 7     | **Machine Timer Interrupt Enable (MTIE):** If set, ``irq_timer_i`` is enabled.       |
+-------+--------------------------------------------------------------------------------------+
| 3     | **Machine Software Interrupt Enable (MSIE):** if set, ``irq_software_i`` is enabled. |
+-------+--------------------------------------------------------------------------------------+


Machine Trap-Vector Base Address (mtvec)
----------------------------------------

CSR Address: ``0x305``

Reset Value: ``0x0000_0001``

``mtvec`` is a WARL register which contains the machine trap-vector base address.

+-------+--------------------------------------------------------------------------------------+
| Bit#  | Interrupt                                                                            |
+-------+--------------------------------------------------------------------------------------+
| 31:2  | **BASE:** The trap-vector base address, always aligned to 256 bytes, i.e.,           |
|       | ``mtvec[7:2]`` is always set to 6'b0.                                                |
+-------+--------------------------------------------------------------------------------------+
| 1:0   | **MODE:** Always set to 2'b01 to indicate vectored interrupt handling (read-only).   |
+-------+--------------------------------------------------------------------------------------+


Machine Exception PC (mepc)
---------------------------

CSR Address: ``0x341``

Reset Value: ``0x0000_0000``

When an exception is encountered, the current program counter is saved in ``mepc``, and the core jumps to the exception address.
When an MRET instruction is executed, the value from ``mepc`` replaces the current program counter.


Machine Cause (mcause)
----------------------

CSR Address: ``0x342``

Reset Value: ``0x0000_0000``

+-------+-----+------------------------------------------------------------------+
| Bit#  | R/W | Description                                                      |
+-------+-----+------------------------------------------------------------------+
| 31    | R   | **Interrupt:** This bit is set when the exception was triggered  |
|       |     | by an interrupt.                                                 |
+-------+-----+------------------------------------------------------------------+
| 4:0   | R   | **Exception Code**                                               |
+-------+-----+------------------------------------------------------------------+

When an exception is encountered, the corresponding exception code is stored in this register.


Machine Trap Value (mtval)
--------------------------

CSR Address: ``0x343``

Reset Value: ``0x0000_0000``

When an exception is encountered, this register can hold exception-specific information to assist software in handling the trap.

 * In the case of errors in the load-store unit ``mtval`` holds the address of the transaction causing the error.
 * If this transaction is misaligned, ``mtval`` holds the address of the missing transaction part.
 * In the case of illegal instruction exceptions, ``mtval`` holds the actual faulting instruction.

For all other exceptions, ``mtval`` is 0.


Machine Interrupt Pending Register (mip)
----------------------------------------

CSR Address: ``0x344``

Reset Value: ``0x0000_0000``

``mip`` is a read-only register indicating pending interrupt requests.
A particular bit in the register reads as one if the corresponding interrupt input signal is high and if the interrupt is enabled in the ``mie`` CSR.

+-------+---------------------------------------------------------------------------------------+
| Bit#  | Interrupt                                                                             |
+-------+---------------------------------------------------------------------------------------+
| 30:16 | Machine Fast Interrupts Pending: If bit x+16 is set,                                  |
|       | fast interrupt ``irq_fast_i[x]`` is pending.                                          |
+-------+---------------------------------------------------------------------------------------+
| 11    | **Machine External Interrupt Pending (MEIP):** If set, ``irq_external_i`` is pending. |
+-------+---------------------------------------------------------------------------------------+
| 7     | **Machine Timer Interrupt Pending (MTIP):** If set, ``irq_timer_i`` is pending.       |
+-------+---------------------------------------------------------------------------------------+
| 3     | **Machine Software Interrupt Pending (MSIP):** if set, ``irq_software_i`` is pending. |
+-------+---------------------------------------------------------------------------------------+

PMP Configuration Register (pmpcfgx)
----------------------------------------

CSR Address: ``0x3A0 - 0x3A3``

Reset Value: ``0x0000_0000``

``pmpcfgx`` are registers to configure PMP regions. Each register configures 4 PMP regions.

+---------------------------------------+
|  31:24  |  23:16  |  15:8   |   7:0   |
+---------------------------------------+
| pmp3cfg | pmp2cfg | pmp1cfg | pmp0cfg |
+---------------------------------------+

The configuration fields for each region are as follows:

+-------+--------------------------+
| Bit#  |  Definition              |
+-------+--------------------------+
|    7  | Lock                     |
+-------+--------------------------+
|  6:5  | Reserved (Read as zero)  |
+-------+--------------------------+
|  4:3  | Mode                     |
+-------+--------------------------+
|    2  | Execute permission       |
+-------+--------------------------+
|    1  | Write permission         |
+-------+--------------------------+
|    0  | Read permission          |
+-------+--------------------------+

Details of these configuration bits can be found in the RISC-V Privileged Specification, version 1.11 (see Physical Memory Protection CSRs, Section 3.6.1).

Note that the combination of Write permission = 1, Read permission = 0 is reserved, and will be treated by the core as Read/Write permission = 0.

PMP Address Register (pmpaddrx)
----------------------------------------

CSR Address: ``0x3B0 - 0x3BF``

Reset Value: ``0x0000_0000``

``pmpaddrx`` are registers to set address matching for PMP regions.

+----------------+
|     31:0       |
+----------------+
| address[33:2]  |
+----------------+

.. _csr-mhartid:

Hardware Thread ID (mhartid)
----------------------------

CSR Address: ``0xF14``

Reset Value: Defined

+-------+-----+------------------------------------------------------------------+
| Bit#  | R/W | Description                                                      |
+-------+-----+------------------------------------------------------------------+
| 10:5  | R   | **Cluster ID:** ID of the cluster                                |
+-------+-----+------------------------------------------------------------------+
| 3:0   | R   | **Core ID:** ID of the core within the cluster                   |
+-------+-----+------------------------------------------------------------------+
