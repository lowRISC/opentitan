.. _exceptions-interrupts:

Exceptions and Interrupts
=========================

Ibex implements trap handling for interrupts and exceptions according to the RISC-V Privileged Specification, version 1.11.

All exceptions cause the core to jump to the base address of the vector table in the ``mtvec`` CSR.
Interrupts are handled in vectored mode, i.e., the core jumps to the base address plus four times the interrupt ID.

The base address of the vector table is initialized to the boot address (must be aligned to 256 bytes, i.e., its least significant byte must be 0x00) when the core is booting.
The base address can be changed after bootup by writing to the ``mtvec`` CSR.
For more information, see the :ref:`cs-registers` documentation.

The core starts fetching at the address made by concatenating the most significant 3 bytes of the boot address and the reset value (0x80) as the least significant byte.
It is assumed that the boot address is supplied via a register to avoid long paths to the instruction fetch unit.

Privilege Modes
---------------

Ibex supports operation in Machine Mode (M-Mode) and User Mode (U-Mode).
The core resets into M-Mode and will jump to M-Mode on any interrupt or exception.
On execution of an MRET instruction, the core will return to the Privilege Mode stored in ``mstatus``.MPP.

Interrupts
----------

Ibex supports the following interrupts.

+-------------------------+-------+--------------------------------------------------+
| Interrupt Input Signal  | ID    | Description                                      |
+=========================+=======+==================================================+
| ``irq_nm_i``            | 31    | Non-maskable interrupt (NMI)                     |
+-------------------------+-------+--------------------------------------------------+
| ``irq_fast_i[14:0]``    | 30:16 | 15 fast, local interrupts                        |
+-------------------------+-------+--------------------------------------------------+
| ``irq_external_i``      | 11    | Connected to platform-level interrupt controller |
+-------------------------+-------+--------------------------------------------------+
| ``irq_timer_i``         | 7     | Connected to timer module                        |
+-------------------------+-------+--------------------------------------------------+
| ``irq_software_i``      | 3     | Connected to memory-mapped (inter-processor)     |
|                         |       | interrupt register                               |
+-------------------------+-------+--------------------------------------------------+

All interrupts except for the non-maskable interrupt (NMI) are controlled via the ``mstatus``, ``mie`` and ``mip`` CSRs.
After reset, all interrupts are disabled.
To enable interrupts, both the global interrupt enable (MIE) bit in the ``mstatus`` CSR and the corresponding individual interrupt enable bit in the ``mie`` CSR need to be set.
For more information, see the :ref:`cs-registers` documentation.

If multiple interrupts are pending, the highest priority is given to the interrupt with the highest ID.

The NMI is enabled independent of the values in the ``mstatus`` and ``mie`` CSRs, and it is not visible through the ``mip`` CSR.
It has interrupt ID 31, i.e., it has the highest priority of all interrupts and the core jumps to the trap-handler base address (in ``mtvec``) plus 0x7C to handle the NMI.

All interrupt lines are level-sensitive.
It is assumed that the interrupt handler signals completion of the handling routine to the interrupt source, e.g., through a memory-mapped register, which then deasserts the corresponding interrupt line.

In Debug Mode, all interrupts including the NMI are ignored independent of ``mstatus``.MIE and the content of the ``mie`` CSR.


Recoverable Non-Maskable Interrupt
----------------------------------

To support recovering from an NMI happening during a trap handling routine, Ibex features additional CSRs for backing up ``mstatus``.MPP, ``mstatus``.MPIE, ``mepc`` and ``mcause``.
These CSRs are not accessible by software running on the core.

These CSRs are nonstandard.
For more information, see `the corresponding proposal <https://github.com/riscv/riscv-isa-manual/issues/261>`_.


Exceptions
----------

Ibex can trigger an exception due to the following exception causes:

+----------------+---------------------------------------------------------------+
| Exception Code | Description                                                   |
+----------------+---------------------------------------------------------------+
|              1 | Instruction access fault                                      |
+----------------+---------------------------------------------------------------+
|              2 | Illegal instruction                                           |
+----------------+---------------------------------------------------------------+
|              3 | Breakpoint                                                    |
+----------------+---------------------------------------------------------------+
|              5 | Load access fault                                             |
+----------------+---------------------------------------------------------------+
|              7 | Store access fault                                            |
+----------------+---------------------------------------------------------------+
|              8 | Environment call from U-Mode (ECALL)                          |
+----------------+---------------------------------------------------------------+
|             11 | Environment call from M-Mode (ECALL)                          |
+----------------+---------------------------------------------------------------+

The illegal instruction exception, instruction access fault, LSU error exceptions and ECALL instruction exceptions cannot be disabled and are always active.


Handling
--------

Ibex does support nested interrupt/exception handling.
Exceptions inside interrupt/exception handlers cause another exception.
However, exceptions during the critical part of your exception handlers, i.e. before having saved the ``mepc`` and ``mstatus``, will cause those CSRs to be overwritten.
Interrupts during interrupt/exception handlers are thus disabled by default, but can be explicitly enabled if desired.

When entering an interrupt/exception handler, the core sets ``mepc`` to the current program counter and saves ``mstatus``.MIE to ``mstatus``.MPIE.
Upon executing an MRET instruction, the core jumps to the program counter saved in the ``mepc`` CSR and restores ``mstatus``.MPIE to ``mstatus``.MIE.
