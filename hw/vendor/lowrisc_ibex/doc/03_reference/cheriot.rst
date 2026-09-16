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

When CHERIoT is enabled, ``misa`` reflects the CHERIoT base ISA (bits X=1, I=0, E=1), and ``marchid`` reads as 0xCE1 instead of the standard Ibex value of 0x16 (22).
CHERIoT mode implies RV32E and uses only 16 registers (x0–x15).

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
