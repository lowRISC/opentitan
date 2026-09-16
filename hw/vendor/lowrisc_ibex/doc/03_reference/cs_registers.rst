.. _cs-registers:

Control and Status Registers
============================

Ibex implements all the Control and Status Registers (CSRs) listed in the following table according to the RISC-V Privileged Specification, version 1.11.

When CHERIoT mode is active (``BaseIsa == BaseIsaRV32IorCHERIoT`` and ``cheriot_enable_i == IbexMuBiOn``),
additional CHERIoT-specific registers are accessible.
These are summarised in a separate table below.

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
|  0x306  | ``mcounteren``     | WARL   | Machine Counter-Enable Register               |
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
|  0x5A8  | ``scontext``       | WARL   | Supervisor Context Register                   |
+---------+--------------------+--------+-----------------------------------------------+
|  0x747  | ``mseccfg``        | WARL   | Machine Security Configuration                |
+---------+--------------------+--------+-----------------------------------------------+
|  0x757  | ``mseccfgh``       | WARL   | Upper 32 bits of ``mseccfg``                  |
+---------+--------------------+--------+-----------------------------------------------+
|  0x7A0  | ``tselect``        | WARL   | Trigger Select Register                       |
+---------+--------------------+--------+-----------------------------------------------+
|  0x7A1  | ``tdata1``         | WARL   | Trigger Data Register 1                       |
+---------+--------------------+--------+-----------------------------------------------+
|  0x7A2  | ``tdata2``         | WARL   | Trigger Data Register 2                       |
+---------+--------------------+--------+-----------------------------------------------+
|  0x7A3  | ``tdata3``         | WARL   | Trigger Data Register 3                       |
+---------+--------------------+--------+-----------------------------------------------+
|  0x7A8  | ``mcontext``       | WARL   | Machine Context Register                      |
+---------+--------------------+--------+-----------------------------------------------+
|  0x7AA  | ``mscontext``      | WARL   | Machine Supervisor Context Register           |
+---------+--------------------+--------+-----------------------------------------------+
|  0x7B0  | ``dcsr``           | WARL   | Debug Control and Status Register             |
+---------+--------------------+--------+-----------------------------------------------+
|  0x7B1  | ``dpc``            | RW     | Debug PC                                      |
+---------+--------------------+--------+-----------------------------------------------+
|  0x7B2  | ``dscratch0``      | RW     | Debug Scratch Register 0                      |
+---------+--------------------+--------+-----------------------------------------------+
|  0x7B3  | ``dscratch1``      | RW     | Debug Scratch Register 1                      |
+---------+--------------------+--------+-----------------------------------------------+
|  0x7C0  | ``cpuctrlsts``     | WARL   | CPU Control and Status Register (Custom CSR)  |
+---------+--------------------+--------+-----------------------------------------------+
|  0x7C1  | ``secureseed``     | WARL   | Security feature random seed (Custom CSR)     |
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
|  0xBC1  | ``mshwm``          | WARL   | Machine Stack High Watermark (CHERIoT only)   |
+---------+--------------------+--------+-----------------------------------------------+
|  0xBC2  | ``mshwmb``         | WARL   | Machine Stack High Watermark Base (CHERIoT)   |
+---------+--------------------+--------+-----------------------------------------------+
|  0xC00  | ``cycle``          | R      | Cycle Counter (U-mode alias of ``mcycle``)    |
+---------+--------------------+--------+-----------------------------------------------+
|  0xC02  | ``instret``        | R      | Instructions-Retired (U-mode alias of         |
|         |                    |        | ``minstret``)                                 |
+---------+--------------------+--------+-----------------------------------------------+
|  0xC03  | ``hpmcounter3``    | R      | Performance-Monitoring Counter (U-mode alias) |
+---------+--------------------+--------+-----------------------------------------------+
|     .             .               .                    .                              |
+---------+--------------------+--------+-----------------------------------------------+
|  0xC1F  | ``hpmcounter31``   | R      | Performance-Monitoring Counter (U-mode alias) |
+---------+--------------------+--------+-----------------------------------------------+
|  0xC80  | ``cycleh``         | R      | Upper 32 bits of ``cycle``                    |
+---------+--------------------+--------+-----------------------------------------------+
|  0xC82  | ``instreth``       | R      | Upper 32 bits of ``instret``                  |
+---------+--------------------+--------+-----------------------------------------------+
|  0xC83  | ``hpmcounter3h``   | R      | Upper 32 bits of ``hpmcounter3``              |
+---------+--------------------+--------+-----------------------------------------------+
|     .             .               .                    .                              |
+---------+--------------------+--------+-----------------------------------------------+
|  0xC9F  | ``hpmcounter31h``  | R      | Upper 32 bits of ``hpmcounter31``             |
+---------+--------------------+--------+-----------------------------------------------+
|  0xF11  | ``mvendorid``      | R      | Machine Vendor ID                             |
+---------+--------------------+--------+-----------------------------------------------+
|  0xF12  | ``marchid``        | R      | Machine Architecture ID                       |
+---------+--------------------+--------+-----------------------------------------------+
|  0xF13  | ``mimpid``         | R      | Machine Implementation ID                     |
+---------+--------------------+--------+-----------------------------------------------+
|  0xF14  | ``mhartid``        | R      | Hardware Thread ID                            |
+---------+--------------------+--------+-----------------------------------------------+

See the :ref:`performance-counters` documentation for a description of the counter registers.


Machine Status (mstatus)
------------------------

CSR Address: ``0x300``

Reset Value: ``0x0000_0080``

+-------+-----+---------------------------------------------------------------------------------+
| Bit#  | R/W | Description                                                                     |
+-------+-----+---------------------------------------------------------------------------------+
| 21    | RW  | **TW:** Timeout Wait (WFI executed in User Mode will trap to Machine Mode).     |
+-------+-----+---------------------------------------------------------------------------------+
| 17    | RW  | **MPRV:** Modify Privilege (Loads and stores use MPP for privilege checking).   |
+-------+-----+---------------------------------------------------------------------------------+
| 12:11 | RW  | **MPP:** Machine Previous Privilege mode.                                       |
+-------+-----+---------------------------------------------------------------------------------+
| 7     | RW  | **Previous Interrupt Enable (MPIE)**, i.e., before entering exception handling. |
+-------+-----+---------------------------------------------------------------------------------+
| 3     | RW  | **Interrupt Enable (MIE):** If set to 1'b1, interrupts are globally enabled.    |
+-------+-----+---------------------------------------------------------------------------------+

When an exception is encountered, ``mstatus``.MPIE will be set to ``mstatus``.MIE, and ``mstatus``.MPP will be set to the current privilege mode.
When the MRET instruction is executed, the value of MPIE will be stored back to ``mstatus``.MIE, and the privilege mode will be restored from ``mstatus``.MPP.

If you want to enable interrupt handling in your exception handler, set ``mstatus``.MIE to 1'b1 inside your handler code.

Only Machine Mode and User Mode are supported.
Any write to ``mstatus``.MPP of an unsupported value will be interpreted as Machine Mode.

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


Machine Counter-Enable Register (mcounteren)
--------------------------------------------

CSR Address: ``0x306``

Reset Value: ``0x0000_0000``

``mcounteren`` is a WARL register that controls which performance counters are accessible in User Mode.
When a bit is set, the corresponding counter can be read from U-mode, when clear, a U-mode access to that counter raises an illegal instruction exception.

+--------+------+-------------------------------------------------------------------------------------+
| Bit#   | R/W  | Description                                                                         |
+========+======+=====================================================================================+
| 31:3   | WARL | **HPMx:** Enable U-mode access to ``hpmcounterX`` / ``hpmcounterXh`` (bits 3–31,    |
|        |      | where the bit index matches the counter number).                                    |
|        |      | Bits above ``MHPMCounterNum + 2`` always read as zero.                              |
+--------+------+-------------------------------------------------------------------------------------+
| 2      | RW   | **IR:** Enable U-mode access to ``instret`` / ``instreth``.                         |
+--------+------+-------------------------------------------------------------------------------------+
| 1      | R    | **TM:** Always reads as zero. The ``time`` CSR is not implemented.                  |
+--------+------+-------------------------------------------------------------------------------------+
| 0      | RW   | **CY:** Enable U-mode access to ``cycle`` / ``cycleh``.                             |
+--------+------+-------------------------------------------------------------------------------------+

Writes to ``mcounteren`` are only accepted when the ``mcounteren_writable_i`` input is set to ``IbexMuBiOn``.
If ``mcounteren_writable_i`` is not ``IbexMuBiOn``, writes are silently ignored, effectively locking the register.
This allows a system integrator to prevent software from granting U-mode counter access after an initial configuration phase.
See :ref:`performance-counters` for the synthesis-time parameters that control counter availability.


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
------------------------------------

CSR Address: ``0x3A0 - 0x3A3``

Reset Value: ``0x0000_0000``

``pmpcfgx`` are registers to configure PMP regions. Each register configures 4 PMP regions.

+---------+---------+---------+---------+
|  31:24  |  23:16  |  15:8   |   7:0   |
+---------+---------+---------+---------+
| pmp3cfg | pmp2cfg | pmp1cfg | pmp0cfg |
+---------+---------+---------+---------+

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
-------------------------------

CSR Address: ``0x3B0 - 0x3BF``

Reset Value: ``0x0000_0000``

``pmpaddrx`` are registers to set address matching for PMP regions.

+----------------+
|     31:0       |
+----------------+
| address[33:2]  |
+----------------+

Machine Security Configuration (mseccfg/mseccfgh)
-------------------------------------------------

CSR Address: ``mseccfg``: ``0x747``  ``mseccfg``: ``0x757``

Reset Value: ``0x0000_0000_0000_0000``

+------+-----------------------------------------------------------------------------------------------------------------------------------+
| Bit# | Definition                                                                                                                        |
+------+-----------------------------------------------------------------------------------------------------------------------------------+
| 2    | **Rule Locking Bypass (RLB):** If set locked PMP entries can be modified                                                          |
+------+-----------------------------------------------------------------------------------------------------------------------------------+
| 1    | **Machine Mode Whitelist Policy (MMWP):** If set default policy for PMP is deny for M-Mode accesses that don't match a PMP region |
+------+-----------------------------------------------------------------------------------------------------------------------------------+
| 0    | **Machine Mode Lockdown (MML):** Alters behaviour of ``pmpcfgX`` bits                                                             |
+------+-----------------------------------------------------------------------------------------------------------------------------------+

``mseccfg`` is specified in the Trusted Execution Environment (TEE) working group proposal `PMP Enhancements for memory access and execution prevention on Machine mode (Smepmp) version 0.9.3 <https://github.com/riscv/riscv-tee/blob/61455747230a26002d741f64879dd78cc9689323/Smepmp/Smepmp.pdf>`_, which gives the full details of it's functionality including the new PMP behaviour when ``mseccfg.MML`` is set.
Note that the reset value means PMP behavior out of reset matches the RISC-V Privileged Architecture.
A write to ``mseccfg`` is required to change it.
Note ``mseccfgh`` reads as all 0s and ignores all writes.
Any access to ``mseccfg`` or ``mseccfgh`` when using an Ibex configuration without PMP (``PMPEnable`` is 0) will trigger an illegal instruction exception.

.. _csr-tselect:

Trigger Select Register (tselect)
---------------------------------

CSR Address: ``0x7A0``

Reset Value: ``0x0000_0000``

Accessible in Debug Mode or M-Mode when trigger support is enabled (using the DbgTriggerEn parameter).

Number of the currently selected trigger starting at 0.
The number of triggers is configured by the DbgHwNumLen parameter.

Writing a value larger than or equal to the number of supported triggers will write the highest valid index.
This allows a debugger to detect the allowed number of triggers by reading back the value.

.. _csr-tdata1:

Trigger Data Register 1 (tdata1)
--------------------------------

CSR Address: ``0x7A1``

Reset Value: ``0x2800_1000``

Accessible in Debug Mode or M-Mode when trigger support is enabled (using the DbgTriggerEn parameter).
Since native triggers are not supported, writes to this register from M-Mode will be ignored.

Ibex only implements one type of trigger, instruction address match.
Most fields of this register will read as a fixed value to reflect the mode that is supported.

+-------+------+------------------------------------------------------------------+
| Bit#  | R/W  | Description                                                      |
+-------+------+------------------------------------------------------------------+
| 31:28 | R    | **type:** 2 = Address/Data match trigger type.                   |
+-------+------+------------------------------------------------------------------+
| 27    | R    | **dmode:** 1 = Only debug mode can write tdata registers         |
+-------+------+------------------------------------------------------------------+
| 26:21 | R    | **maskmax:** 0 = Only exact matching supported.                  |
+-------+------+------------------------------------------------------------------+
| 20    | R    | **hit:** 0 = Hit indication not supported.                       |
+-------+------+------------------------------------------------------------------+
| 19    | R    | **select:** 0 = Only address matching is supported.              |
+-------+------+------------------------------------------------------------------+
| 18    | R    | **timing:** 0 = Break before the instruction at the specified    |
|       |      | address.                                                         |
+-------+------+------------------------------------------------------------------+
| 17:16 | R    | **sizelo:** 0 = Match accesses of any size.                      |
+-------+------+------------------------------------------------------------------+
| 15:12 | R    | **action:** 1 = Enter debug mode on match.                       |
+-------+------+------------------------------------------------------------------+
| 11    | R    | **chain:** 0 = Chaining not supported.                           |
+-------+------+------------------------------------------------------------------+
| 10:7  | R    | **match:** 0 = Match the whole address.                          |
+-------+------+------------------------------------------------------------------+
| 6     | R    | **m:** 1 = Match in M-Mode.                                      |
+-------+------+------------------------------------------------------------------+
| 5     | R    | zero.                                                            |
+-------+------+------------------------------------------------------------------+
| 4     | R    | **s:** 0 = S-Mode not supported.                                 |
+-------+------+------------------------------------------------------------------+
| 3     | R    | **u:** 1 = Match in U-Mode.                                      |
+-------+------+------------------------------------------------------------------+
| 2     | RW   | **execute:** Enable matching on instruction address.             |
+-------+------+------------------------------------------------------------------+
| 1     | R    | **store:** 0 = Store address / data matching not supported.      |
+-------+------+------------------------------------------------------------------+
| 0     | R    | **load:** 0 = Load address / data matching not supported.        |
+-------+------+------------------------------------------------------------------+

Details of these configuration bits can be found in the RISC-V Debug Specification, version 0.13.2 (see Trigger Registers, Section 5.2).

.. _csr-tdata2:

Trigger Data Register 2 (tdata2)
--------------------------------

CSR Address: ``0x7A2``

Reset Value: ``0x0000_0000``

Accessible in Debug Mode or M-Mode when trigger support is enabled (using the DbgTriggerEn parameter).
Since native triggers are not supported, writes to this register from M-Mode will be ignored.

This register stores the instruction address to match against for a breakpoint trigger.

Trigger Data Register 3 (tdata3)
--------------------------------

CSR Address: ``0x7A3``

Reset Value: ``0x0000_0000``

Accessible in Debug Mode or M-Mode when trigger support is enabled (using the DbgTriggerEn parameter).

Ibex does not support the features requiring this register, so writes are ignored and it will always read as zero.

Machine Context Register (mcontext)
-----------------------------------

CSR Address: ``0x7A8``

Reset Value: ``0x0000_0000``

Accessible in Debug Mode or M-Mode when trigger support is enabled (using the DbgTriggerEn parameter).

Ibex does not support the features requiring this register, so writes are ignored and it will always read as zero.

Supervisor Context Register (scontext)
--------------------------------------

CSR Address: ``0x7AA``

Reset Value: ``0x0000_0000``

Accessible in Debug Mode or M-Mode when trigger support is enabled (using the DbgTriggerEn parameter).

Ibex does not support the features requiring this register, so writes are ignored and it will always read as zero.

.. _csr-dcsr:

Debug Control and Status Register (dcsr)
----------------------------------------

CSR Address: ``0x7B0``

Reset Value: ``0x4000_0003``

Accessible in Debug Mode only.
Ibex implements the following bit fields.
Other bit fields read as zero.

+-------+------+------------------------------------------------------------------+
| Bit#  | R/W  | Description                                                      |
+-------+------+------------------------------------------------------------------+
| 31:28 | R    | **xdebugver:** 4 = External spec-compliant debug support exists. |
+-------+------+------------------------------------------------------------------+
| 15    | RW   | **ebreakm:** EBREAK in M-Mode behaves as described in Privileged |
|       |      | Spec (0), or enters Debug Mode (1).                              |
+-------+------+------------------------------------------------------------------+
| 12    | WARL | **ebreaku:** EBREAK in U-Mode behaves as described in Privileged |
|       |      | Spec (0), or enters Debug Mode (1).                              |
+-------+------+------------------------------------------------------------------+
| 8:6   | R    | **cause:** 1 = EBREAK, 2 = trigger, 3 = halt request, 4 = step   |
+-------+------+------------------------------------------------------------------+
| 2     | RW   | **step:** When set and not in Debug Mode, execute a single       |
|       |      | instruction and enter Debug Mode.                                |
+-------+------+------------------------------------------------------------------+
| 1:0   | WARL | **prv:** Privilege level the core was operating in when Debug    |
|       |      | Mode was entered. May be modified by debugger to change          |
|       |      | privilege level. Ibex allows transitions to all supported modes. |
|       |      | (M- and U-Mode).                                                 |
+-------+------+------------------------------------------------------------------+

Details of these configuration bits can be found in the RISC-V Debug Specification, version 0.13.2 (see Core Debug Registers, Section 4.8).
Note that **ebreaku** and **prv** are accidentally specified as RW in version 0.13.2 of the RISC-V Debug Specification.
More recent versions of the specification define these fields correctly as WARL.

.. _csr-dpc:

Debug PC Register (dpc)
-----------------------

CSR Address: ``0x7B1``

Reset Value: ``0x0000_0000``

When entering Debug Mode, ``dpc`` is updated with the address of the next instruction that would be executed (if Debug Mode would not have been entered).
When resuming, the PC is set to the address stored in ``dpc``.
The debug module may modify ``dpc``.
Accessible in Debug Mode only.

Debug Scratch Register 0 (dscratch0)
------------------------------------

CSR Address: ``0x7B2``

Reset Value: ``0x0000_0000``

Scratch register to be used by the debug module.
Accessible in Debug Mode only.

Debug Scratch Register 1 (dscratch1)
------------------------------------

CSR Address: ``0x7B3``

Reset Value: ``0x0000_0000``

Scratch register to be used by the debug module.
Accessible in Debug Mode only.

CPU Control and Status Register (cpuctrlsts)
--------------------------------------------

CSR Address: ``0x7C0``

Reset Value: ``0x0000_0000``

Custom CSR to control runtime configuration of CPU components.
Accessible in Machine Mode only.
Ibex implements the following bit fields.
Other bit fields read as zero.

+-------+------+------------------------------------------------------------------+
| Bit#  | R/W  | Description                                                      |
+=======+======+==================================================================+
| 8     | R    | **ic_scr_key_valid:** The icache scrambling key is valid. A      |
|       |      | ``fence.i`` instruction is guaranteed to fetch a new key. If     |
|       |      | the instruction cache has not been configured or the core has    |
|       |      | not been configured with security features  (ICache parameter    |
|       |      | == 0 or SecureIbex parameter == 0), this field will always read  |
|       |      | as zero. (see :ref:`icache-scramble-key`)                        |
+-------+------+------------------------------------------------------------------+
| 7     | RW   | **double_fault_seen:** A synchronous exception was observed when |
|       |      | the ``sync_exc_seen`` field was set. This field must be manually |
|       |      | cleared, hardware only sets it (see :ref:`double-fault-detect`). |
+-------+------+------------------------------------------------------------------+
| 6     | RW   | **sync_exc_seen:** A synchronous exception has been observed.    |
|       |      | This flag is cleared when ``mret`` is executed.                  |
|       |      | (see :ref:`double-fault-detect`).                                |
+-------+------+------------------------------------------------------------------+
| 5:3   | WARL | **dummy_instr_mask:** Mask to control frequency of dummy         |
|       |      | instruction insertion. If the core has not been configured with  |
|       |      | security features (SecureIbex parameter == 0), this field will   |
|       |      | always read as zero (see :ref:`security`).                       |
+-------+------+------------------------------------------------------------------+
| 2     | WARL | **dummy_instr_en:** Enable (1) or disable (0) dummy instruction  |
|       |      | insertion features. If the core has not been configured with     |
|       |      | security features (SecureIbex parameter == 0), this field will   |
|       |      | always read as zero (see :ref:`security`).                       |
+-------+------+------------------------------------------------------------------+
| 1     | WARL | **data_ind_timing:** Enable (1) or disable (0) data-independent  |
|       |      | timing features. If the core has not been configured with        |
|       |      | security features (SecureIbex parameter == 0), this field will   |
|       |      | always read as zero.                                             |
+-------+------+------------------------------------------------------------------+
| 0     | WARL | **icache_enable:** Enable (1) or disable (0) the instruction     |
|       |      | cache. If the instruction cache has not been configured (ICache  |
|       |      | parameter == 0), this field will always read as zero.            |
+-------+------+------------------------------------------------------------------+

Security Feature Seed Register (secureseed)
-------------------------------------------

CSR Address: ``0x7C1``

Reset Value: ``0x0000_0000``

Accessible in Machine Mode only.

Custom CSR to allow re-seeding of security-related pseudo-random number generators.
A write to this register will update the seeding of pseudo-random number generators inside the design.
This allows software to improve the randomness, and therefore security, of certain features by periodically reading from a true random number generator peripheral.
Seed values are not actually stored in a register and so reads to this register will always return zero.

Time Registers (time(h))
------------------------

CSR Address: ``0xC01 / 0xC81``

The User Mode ``time(h)`` registers are not implemented in Ibex.
Any access to these registers will trap.
It is recommended that trap handler software provides a means of accessing platform-defined ``mtime(h)`` timers where available.

Machine Vendor ID (mvendorid)
-----------------------------

CSR Address: ``0xF11``

Reset Value: ``0x0000_0000``

Use the top-level parameter ``CsrMvendorId`` in :file:`rtl/ibex_top.sv` to change the fixed value.
Details of what the ID represents can be found in the RISC-V Privileged Specification.

Machine Architecture ID (marchid)
---------------------------------

CSR Address: ``0xF12``

Reset Value: ``0x0000_0016`` (RV32I mode) / ``0x0000_0CE1`` (CHERIoT mode)

The value of ``marchid`` depends on the active ISA mode.
In standard RV32I mode it reads as 0x16, the architecture ID allocated to Ibex.
When CHERIoT mode is enabled (``cheriot_enable_i == IbexMuBiOn``), it reads as 0xCE1 to indicate the CHERIoT architecture.
The constants ``CSR_MARCHID_VALUE`` and ``CSR_MARCHID_CHERIOT_VALUE`` in :file:`rtl/ibex_pkg.sv` define these values.
Details of what the ID represents can be found in the RISC-V Privileged Specification.

Machine Implementation ID (mimpid)
----------------------------------

CSR Address: ``0xF13``

Reset Value: ``0x0000_0000``

Use the top-level parameter ``CsrMimpId`` in :file:`rtl/ibex_top.sv` to change the fixed value.
Details of what the ID represents can be found in the RISC-V Privileged Specification.

.. _csr-mhartid:

Hardware Thread ID (mhartid)
----------------------------

CSR Address: ``0xF14``

Reads directly return the value of the ``hart_id_i`` input signal.
See also :ref:`core-integration`.

Machine Stack High Watermark (mshwm)
-------------------------------------

CSR Address: ``0xBC1``

Reset Value: ``0x0000_0000``

**CHERIoT only.** Accessible only when ``BaseIsa == BaseIsaRV32IorCHERIoT`` and ``cheriot_enable_i == IbexMuBiOn``.
Any access in RV32I mode will trigger an illegal instruction exception.
Accessing this register also requires ``PCC.PERMIT_ACCESS_SYSTEM_REGISTERS``, without it a CHERIoT exception is raised.

Tracks the lowest address written by a store instruction within the stack region since last reset.
Hardware automatically updates this register whenever a store is issued to an address within ``[mshwmb, mshwm)``.
This effectively tracks the maximum stack depth.
The lower 4 bits are always zero (16-byte aligned).

Because the reset value is ``0x0`` the hardware update condition ``addr < mshwm`` can never be satisfied at reset.
Software must write an initial value (typically the top of the stack region) to ``mshwm`` before hardware tracking takes effect.

Software can also write to this register to reset the watermark.
Writes are rounded down to the nearest 16-byte boundary.

Machine Stack High Watermark Base (mshwmb)
------------------------------------------

CSR Address: ``0xBC2``

Reset Value: ``0x0000_0000``

**CHERIoT only.** Accessible only when ``BaseIsa == BaseIsaRV32IorCHERIoT`` and ``cheriot_enable_i == IbexMuBiOn``.
Any access in RV32I mode will trigger an illegal instruction exception.
Accessing this register also requires ``PCC.PERMIT_ACCESS_SYSTEM_REGISTERS``, without it a CHERIoT exception is raised.

Configures the lower bound (bottom) of the tracked stack region.
Stores to addresses below ``mshwmb`` are outside the tracked region and do not update ``mshwm``.
The lower 4 bits are always zero (16-byte aligned).

.. _cheriot-scrs:

CHERIoT Special Capability Registers (SCRs)
--------------------------------------------

**CHERIoT only.** These registers are accessible via the ``CSpecialRW`` instruction rather than the standard CSR access instructions.
They hold capability values (address plus metadata) and are not visible through the standard ``csrr``/``csrw`` RISC-V interface.

Accessing an SCR via ``CSpecialRW`` requires the **SR** (AccessSysReg) permission in the PCC.
Without it, a CHERIoT fault (``mcause`` = 0x1C, violation code 0x18) is raised (see :ref:`cheriot`).
The same SR requirement applies to all regular ``csrr``/``csrw`` accesses in CHERIoT mode (the sole exception being the unprivileged read-only counters 0xC00–0xC9F).

In CHERIoT mode, the standard ``mtvec`` (0x305) and ``mepc`` (0x341) CSR addresses are inaccessible via ``csrr``/``csrw`` — they raise an illegal instruction exception.
``mtcc`` and ``mepcc`` replace them entirely and are only accessible via ``CSpecialRW``.

+----+-----------------------+-------+--------------------------------------------------------------------+
| ID |   Name                | Mode  | Description                                                        |
+====+=======================+=======+====================================================================+
| 28 | ``mtcc``              | RW    | Machine Trap Code Capability (holds mtvec as a capability)         |
+----+-----------------------+-------+--------------------------------------------------------------------+
| 29 | ``mtdc``              | RW    | Machine Trap Data Capability (scratch capability for trap handler) |
+----+-----------------------+-------+--------------------------------------------------------------------+
| 30 | ``mscratchc``         | RW    | Machine Scratch Capability (independent of the integer mscratch)   |
+----+-----------------------+-------+--------------------------------------------------------------------+
| 31 | ``mepcc``             | RW    | Machine Exception Program Counter Capability (holds mepc as cap)   |
+----+-----------------------+-------+--------------------------------------------------------------------+

The following debug-mode SCRs are accessible only in Debug Mode:

+----+-----------------------+-------+------------------------------------------------------------------+
| ID |   Name                | Mode  | Description                                                      |
+====+=======================+=======+==================================================================+
| 24 | ``depcc``             | RW    | Debug Exception Program Counter Capability (holds dpc as cap)    |
+----+-----------------------+-------+------------------------------------------------------------------+
| 25 | ``dscratchc0``        | RW    | Debug Scratch Capability 0                                       |
+----+-----------------------+-------+------------------------------------------------------------------+
| 26 | ``dscratchc1``        | RW    | Debug Scratch Capability 1                                       |
+----+-----------------------+-------+------------------------------------------------------------------+

See :ref:`cheriot` for a full description of CHERIoT registers and their semantics.
