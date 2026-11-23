.. _cheriot:

CHERIoT Extension
=================

CHERIoT (Capability Hardware Extension to RISC-V for Internet of Things) is a capability-based ISA extension that provides hardware-enforced memory safety.
Ibex implements CHERIoT v1.0 as a runtime-switchable extension controlled by the ``BaseIsa`` parameter and the ``cheriot_enable_i`` signal.

CHERIoT Overview
----------------

CHERIoT extends the RISC-V ISA with *capabilities*: Every pointer becomes a capability that contains:

* A 32-bit address.
* Bounds (base and top), describing the valid address range.
* Permissions (load, store, execute, seal/unseal, etc.).
* An object type (for sealing/compartmentalisation).
* A validity tag bit, indicating whether the capability is valid.

Capabilities are 65 bits wide in memory (32-bit address + 32 bits of metadata + 1 tag bit) and are stored as two consecutive words in memory with the tag held out-of-band.
Capabilities are always 8-byte aligned.
Inside the Ibex register file, the capability metadata occupies a 35-bit slot (including a 2-bit correction value that is not stored in memory) alongside the 32-bit integer value.

The CHERIoT ISA is fully described in the `CHERIoT Architecture specification - Version 1.0 <https://github.com/microsoft/cheriot-sail/releases/>`_.

Enabling CHERIoT
----------------

CHERIoT support requires two conditions to be met:

1. **Elaboration-time**: set the ``BaseIsa`` parameter (see :ref:`parameters`) to ``ibex_pkg::BaseIsaRV32IorCHERIoT``.
   The core then implements the base RV32 ISA (e.g., with ePMP for memory protection) and the CHERIoT ISA and allows choosing the mode at runtime.
   With ``BaseIsaRV32I`` (the default for non-CHERIoT designs) all CHERIoT logic is omitted during synthesis.

2. **Runtime**: set ``cheriot_enable_i`` to ``ibex_pkg::IbexMuBiOn``.
   When de-asserted (``ibex_pkg::IbexMuBiOff``) the core runs as a standard RV32I processor.

.. important::
   **Security Constraint:** The ``cheriot_enable_i`` signal acts as a one-way switch. To ensure security and prevent arbitrary switching between memory protection modes, the mode must either be configured at reset and kept constant, or switched exactly once from off to on during runtime.
   Once CHERIoT mode is enabled, it **must not** be switched off again until reset.
   This constraint is **not enforced by hardware** but is checked by the ``CheriotEnableOneWaySwitch`` assertion in ``ibex_core``.
   The integrator is responsible for ensuring the signal is driven by a one-way latch or equivalent logic outside the core.
   Switching at runtime additionally needs a specific software sequence, see :ref:`cheriot-mode-switch`.

**Parameter requirements and unsupported combinations:**

* ``WritebackStage`` must be ``1``.
  The no-writeback path is not implemented for CHERIoT capability accesses.

* Zcmp instructions (``RV32Zcmp``) are not supported in CHERIoT mode.
  They may be included at elaboration time when Ibex runs in Rv32I mode (``cheriot_enable_i == 0``), but once ``cheriot_enable_i`` is asserted Zcmp instructions decode as illegal.

When CHERIoT is enabled, ``misa`` reflects the CHERIoT base ISA (bits X=1, I=0, E=1), and ``marchid`` reads as 0xCE1 instead of the standard Ibex value of 0x16 (22).
CHERIoT mode implies RV32E and uses only 16 registers (x0–x15).

.. _cheriot-mode-switch:

Switching to CHERIoT Mode at Runtime
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

.. important::
   Switching from RV32I to CHERIoT mode at runtime needs the software sequence and system conditions described here.
   They do not apply when ``cheriot_enable_i`` is ``ibex_pkg::IbexMuBiOn`` from reset.

The hardware neither clears the register file nor flushes the pipeline when ``cheriot_enable_i`` changes.
Instructions in flight are therefore partly handled in RV32I mode and partly in CHERIoT mode.

**Triggering the switch:**
The core must trigger the switch itself, as the last step of the sequence below, for example with a store to a register that sets ``cheriot_enable_i``.
Nothing else (for example another bus host, or a debugger through system bus access) may change ``cheriot_enable_i`` while the core runs other code.
An external agent may only switch while the core waits in a known state: it has completed the sequence up to the switch, and it sleeps in or polls from a ``wfi`` loop with interrupts disabled (see the second example below and ``core_sleep_o``).

**Software requirements:**

* Run the sequence in M-mode with interrupts disabled (``mstatus.MIE`` = 0), and keep them disabled until ``mtcc`` is set up in CHERIoT mode.
* Disable dummy instructions (``cpuctrlsts.dummy_instr_en``) before the switch, and restore the previous setting afterwards.
* Write zero to ``x16``–``x31`` and do not write them again before the switch.
  With ``RV32E`` = 1, skip this step: ``x16``–``x31`` do not exist, and the capability metadata storage still holds valid reset values.
* From the instruction that triggers the switch (or, with an external agent, from the first ``wfi``) until the core runs in CHERIoT mode, only use instructions that behave the same in both modes.
  The sequence only needs ``csrr`` of ``marchid``, a conditional branch and ``wfi``.
  In particular, this rules out:

  * Compressed instructions, as several encodings decode differently in CHERIoT mode.
  * Loads and stores, as they need a valid capability in the base register in CHERIoT mode.
  * ``auipc``, ``jal`` and ``jalr``, as they become ``AUIPCC``, ``CJAL`` and ``CJALR``.
  * ``x16``–``x31`` and the ``mtvec``, ``mepc``, ``mseccfg``, ``mseccfgh`` and PMP CSRs, as they are illegal in CHERIoT mode.
  * ``ecall``, ``ebreak``, ``mret`` and any other instruction that can trap or return from a trap.

* Wait for the switch by polling ``marchid`` until it reads the CHERIoT value (0xCE1).
* Set up ``mtcc`` right after the switch, before any instruction that can trap and before interrupts are enabled again.

**System requirements:**

* Debugging is not supported during the switch.
  The core must not halt or be in debug mode from the start of the sequence until ``mtcc`` is set up.
* From the instruction that triggers the switch (or, with an external agent, from the first ``wfi``) until ``mtcc`` is set up, either no non-maskable interrupt (NMI) may be taken, or the NMI handler must work in both modes, including a mode change while it runs.
  Ibex cannot mask NMIs, so without such a handler the integration must make sure that ``irq_nm_i`` is not raised in this window.
  An NMI taken earlier in the sequence must leave ``x16``–``x31`` zero.

The reasons are:

* The RV32I registers ``x16``–``x31`` and the capability metadata of ``x0``–``x15`` share the same storage (see :ref:`register-file-allocation`).
  With ``SecureIbex``, the shadow core stores ECC check bits for the register file: a 39/32 code for integer values and a 64/57 code for capabilities.
  A non-zero value left in ``x16``–``x31`` therefore becomes capability metadata with invalid ECC, and reading it in CHERIoT mode raises a major alert.
  This includes ``x16``: with dummy instructions enabled, it holds the ``x0`` capability that dummy instructions read (see :ref:`dummy-instruction-insertion`).
  Zero is safe because the zero values of both codes have the same check bits.
* A dummy instruction created in RV32I mode can read ``x16``–``x31``.
  If it is still in the pipeline when the mode changes, it decodes as an illegal instruction and raises an exception.
  A write to ``cpuctrlsts`` flushes the pipeline, so no such dummy instruction is left once the write that disables them has executed.
* Until ``mtcc`` is set up, a trap in CHERIoT mode jumps to the base address of the ``mtvec`` value set in RV32I mode, without vectoring, because CHERIoT mode only uses direct mode.
  The RV32I handler code there then runs in CHERIoT mode.
  An NMI taken in RV32I mode shortly before the switch runs its handler partly in CHERIoT mode instead.
  In both cases, the handler fails and the interrupted context is lost.
* ``depcc`` resets to null and is only written in CHERIoT mode.
  If the core halts in RV32I mode and resumes after the switch, ``dret`` installs an untagged PCC and the next instruction fetch faults.
* The polling loop works in both modes: ``csrr``, ``bne`` and ``wfi`` behave the same, and PCC still holds the root executable capability, which has the **SR** permission needed for CSR accesses.
  While the core sleeps in ``wfi``, no instruction is in flight.
  A pending interrupt that is enabled in ``mie`` wakes the core even with ``mstatus.MIE`` = 0, and the core then continues after ``wfi`` without taking the interrupt.

**State after the switch:**
The special capability registers only change in CHERIoT mode, so they still hold their reset values.
PCC, ``mtcc`` and ``mepcc`` hold the root executable capability, ``mtdc`` the root memory capability and ``mscratchc`` the root sealing capability, while ``depcc``, ``dscratchc0`` and ``dscratchc1`` are null.
``mtcc`` and ``mepcc`` keep the values of ``mtvec`` and ``mepc``, so ``mtcc`` still has the vectored mode bit (bit 0) set, which traps ignore.
``x1``–``x15`` keep their RV32I integer values and their capabilities are null.
Software should treat them as uninitialized, as after a reset.
PMP checks are not performed in CHERIoT mode (see :ref:`pmp`), so PMP regions and locks configured in RV32I mode no longer restrict accesses after the switch.

**Examples:**
The first example assumes that ``cheriot_enable_i`` is set by a store of ``t0`` to the address in ``a0``, which depends on the integration.
``.option arch, rv32i_zicsr`` is needed with a CHERIoT toolchain, which rejects ``x16``–``x31``.

.. code-block:: text

   # M-mode, interrupts are disabled. a0 and t0 are set up for the switch.
   .option push
   .option norvc
   .option arch, rv32i_zicsr
   csrrci a1, 0x7C0, 4               # cpuctrlsts.dummy_instr_en = 0, save the old value
   andi   a1, a1, 4
   .irp reg, 16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31
   li     x\reg, 0
   .endr
   li     t1, 0xCE1                  # marchid in CHERIoT mode
   sw     t0, 0(a0)                  # sets cheriot_enable_i
   1:
   csrr   t2, marchid
   bne    t2, t1, 1b                 # wait until the core runs in CHERIoT mode
   csrs   0x7C0, a1                  # restore cpuctrlsts.dummy_instr_en
   .option pop
   # Set up mtcc next, then derive capabilities before enabling interrupts.

In the second example, an external agent switches while the core sleeps and then wakes it with an interrupt that is enabled in ``mie``.
If the core wakes up before the switch, it keeps polling, which is equally safe.

.. code-block:: text

   # Same as above up to and including li t1, 0xCE1, without the store.
   # The wake-up interrupt is enabled in mie, mstatus.MIE = 0.
   1:
   wfi                               # the agent switches while the core sleeps
   csrr   t2, marchid
   bne    t2, t1, 1b                 # wait until the core runs in CHERIoT mode
   csrs   0x7C0, a1                  # restore cpuctrlsts.dummy_instr_en
   .option pop

Register File
-------------

In CHERIoT mode, the :ref:`register-file` is extended: each of the 16 accessible registers (x0–x15) holds both a 32-bit integer value and a 35-bit compressed capability.
Ibex stores 35 bits of metadata (rather than the 33 bits defined by the specification) because it additionally stores 2 bits of correction values to save recomputation time on each capability read from the register file.
The capability portion of a register is only accessible through capability instructions and untagged by integer writes.

Additional Interfaces
---------------------

Two top-level interfaces change with CHERIoT.

Data Memory Tag Interface
~~~~~~~~~~~~~~~~~~~~~~~~~

The data memory interface gains two tag signals:

``data_tag_o``
  1-bit output. When high, the current write transaction carries a valid capability tag or the current load transaction is a capability load.

``data_tag_i``
  1-bit input. The tag bit returned from memory for a load transaction.
  Must be driven high if and only if the loaded word has a stored/valid capability tag and the request was a capability load.

Since Ibex only has a 32-bit interface, it reads and writes capabilities in two consecutive transactions.
The tag bits must be set for both transactions for the capability to be considered a valid one.

.. _cheriot-trvk:

TRVK Revocation Bitmap Interface (``trvk_revbm_*``)
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

The TRVK (Temporal Revocation) filter is positioned just outside the LSU.
It intercepts capability loads and checks whether the loaded capability has been revoked by checking the revocation bitmap.

The revocation bitmap interface is an OBI compliant memory-mapped port.
Because this port is strictly used for bitmap lookups, it only implements the read channels of the OBI standard, sharing identical handshaking semantics with the instruction and data interfaces:

+----------------------------+-----+----------------------------------------------------+
| Signal                     | Dir | Description                                        |
+============================+=====+====================================================+
| ``trvk_revbm_req_o``       | out | Request valid                                      |
+----------------------------+-----+----------------------------------------------------+
| ``trvk_revbm_gnt_i``       | in  | Grant (request accepted this cycle)                |
+----------------------------+-----+----------------------------------------------------+
| ``trvk_revbm_rvalid_i``    | in  | Read data valid                                    |
+----------------------------+-----+----------------------------------------------------+
| ``trvk_revbm_addr_o``      | out | Byte address of the revocation bitmap word to read |
+----------------------------+-----+----------------------------------------------------+
| ``trvk_revbm_rdata_i``     | in  | 32-bit read data (32 revocation bits per word)     |
+----------------------------+-----+----------------------------------------------------+
| ``trvk_revbm_rdata_intg_i``| in  | 7-bit SECDED ECC check bits (if ``MemECC == 1``)   |
+----------------------------+-----+----------------------------------------------------+
| ``trvk_revbm_err_i``       | in  | Bus error on the revocation bitmap read            |
+----------------------------+-----+----------------------------------------------------+

The address space of the revocation bitmap is configured by two top-level parameters:

``CheriotRevBitmapBaseAddr``
  Base byte address of the memory holding the revocation bitmap (must be 4-byte aligned).
  Defaults to ``0x0``.

``CheriotRevBitmapAddrWidth``
  Log\ :sub:`2` of the bitmap size in bytes.
  Defaults to 11 (2 KiB), covering a 128 KiB heap.

``trvk_heap_base_addr_i``
  Base address of the heap region (must be 8-byte aligned).
  Only capabilities whose base address falls within the heap range require revocation checking.
  Capabilities with a base address outside this range bypass the revocation lookup entirely.

If ``BaseIsa == BaseIsaRV32I``, the ``trvk_revbm_*`` and ``trvk_heap_base_addr_i`` ports are unused and can be tied off in wrappers that configure ``BaseIsa`` before elaboration.

Instruction Set
---------------

New CHERIoT Instructions
~~~~~~~~~~~~~~~~~~~~~~~~

**Capability Inspection Instructions**

``CGetPerm``, ``CGetType``, ``CGetBase``, ``CGetLen``, ``CGetTag``, ``CGetAddr``, ``CGetHigh``, ``CGetTop``
  Return individual fields of a capability.

**Capability Modification Instructions**

``CSeal``, ``CUnseal``
  Seal or unseal a capability using a sealing capability.

``CAndPerm``
  Narrow the permissions of a capability (permissions can only be removed, not added).

``CSetAddr``, ``CIncAddr``, ``CIncAddrImm``
  Modify the address of a capability without changing bounds or permissions.

``CSetBounds``, ``CSetBoundsExact``, ``CSetBoundsRoundDown``, ``CSetBoundsImm``
  Narrow the bounds of a capability (bounds can only shrink, never grow).

``CSetHigh``
  Set the upper 32 bits of a capability (for constructing capabilities in debug/firmware contexts).

``CClearTag``
  Return the capability with its tag cleared (useful for converting a capability to an untagged integer pointer).

**Pointer-Arithmetic Instructions**

``CSub``
  Subtract the addresses of two capabilities and return the result as an integer.

``CMove``
  Copy a capability register.

**Pointer-Comparison Instructions**

``CTestSubset``
  Return 1 if one capability's bounds and permissions are a subset of another's.

``CSetEqualExact``
  Return 1 if two capabilities are identical (address, bounds, permissions, tag, and type).

**Special Capability Register Access**

``CSpecialRW``
  Read and/or write a CHERIoT Special Capability Register (SCR).
  Requires the **SR** (AccessSysReg) permission in the PCC; a missing permission raises a CHERI fault with violation code 0x18 (see the exception table below).
  The same SR requirement also applies to regular ``csrr``/``csrw`` instructions in CHERIoT mode, with the sole exception of the unprivileged read-only counters (0xC00–0xC9F).
  See :ref:`cheriot-scrs` for the list of SCRs.

**Adjusting to Compressed Capability Precision Instructions**

``CRoundRepresentableLength (CRRL)``
  Return the smallest representable length greater than or equal to the requested length.

``CRepresentableAlignmentMask (CRAM)``
  Return the alignment mask for a given length: bits that must be zero for the bounds to be exactly representable at that granularity.

Modified Existing Instructions
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

**Control Flow**

``CJAL``
  Capability-version of ``JAL``: unconditional PC-relative jump that saves the return address as a capability in the destination register.

``CJALR``
  Capability-version of ``JALR``: jumps to the address in a capability register while also installing that capability as the new PCC (Program Counter Capability).

**Memory Operations**

The standard RV32 ``LOAD`` and ``STORE`` instructions are modified to take a capability as the base address.

``CLC`` / ``CSC``
  Load or store a full capability (64 bits of data + tag).
  Encoding taken from RV64's ``LD`` and ``SD``.

**Address Construction Instructions**

``AUIPCC``
  Add upper immediate to the PCC address and place the result in a capability register.

``AUICGP``
  Add upper immediate to the capability global pointer (``cgp`` / ``c3``) and place the result in a capability register.

Exceptions
----------

CHERIoT violations produce RISC-V exceptions with ``mcause`` set to 0x1C (CHERIoT fault).
``mtval`` encodes the violation using an 11-bit field in bits [10:0]:

* **bit [10]** — ``S`` flag: 1 if the violating capability is a Special Capability Register (e.g. PCC), 0 for a general-purpose register.
* **bits [9:5]** — register index of the violating capability.
* **bits [4:0]** — violation cause code (see table below).

+------+------------------------------------------------------------------+
| Code | Violation                                                        |
+======+==================================================================+
| 0x00 | None                                                             |
+------+------------------------------------------------------------------+
| 0x01 | Bounds violation                                                 |
+------+------------------------------------------------------------------+
| 0x02 | Tag violation                                                    |
+------+------------------------------------------------------------------+
| 0x03 | Seal violation                                                   |
+------+------------------------------------------------------------------+
| 0x11 | PERMIT_EXECUTE violation                                         |
+------+------------------------------------------------------------------+
| 0x12 | PERMIT_LOAD violation                                            |
+------+------------------------------------------------------------------+
| 0x13 | PERMIT_STORE violation                                           |
+------+------------------------------------------------------------------+
| 0x15 | PERMIT_STORE_CAPABILITY violation                                |
+------+------------------------------------------------------------------+
| 0x18 | PERMIT_ACCESS_SYSTEM_REGISTERS violation                         |
+------+------------------------------------------------------------------+

CSRs Added by CHERIoT
----------------------

The following machine-mode CSRs are added when CHERIoT is enabled.
They are accessible only in CHERIoT mode.

``mshwm`` (0xBC1)
  Machine Stack High Watermark.
  Tracks the lowest address written by any store instruction within the stack region since last reset (16-byte aligned).
  Updated automatically by hardware but can also be written by software.

``mshwmb`` (0xBC2)
  Machine Stack High Watermark Base.
  Lower bound (base/bottom) of the tracked stack region.
  Stores to addresses below ``mshwmb`` do not update ``mshwm``.

The CHERIoT SCRs (Special Capability Registers) are described in :ref:`cheriot-scrs`.

Debug Mode
----------

Ibex does not enforce the CHERIoT protections in Debug Mode, so code running in Debug Mode can access all memory.
See :ref:`debug-cheriot` for details.
