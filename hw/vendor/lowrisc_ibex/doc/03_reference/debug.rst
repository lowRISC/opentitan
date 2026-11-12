.. _debug-support:

Debug Support
=============

Ibex offers support for execution-based debug according to the `RISC-V Debug Specification <https://github.com/riscv/riscv-debug-spec/blob/0.13-test-release/riscv-debug-spec.pdf>`_, version 0.13.


.. note::

   Debug support in Ibex is only one of the components needed to build a System on Chip design with run-control debug support (think "the ability to attach GDB to a core over JTAG").
   Additionally, a Debug Module and a Debug Transport Module, compliant with the RISC-V Debug Specification, are needed.

   A supported open source implementation of these building blocks can be found in the `RISC-V Debug Support for PULP Cores IP block <https://github.com/pulp-platform/riscv-dbg/>`_.

   The `OpenTitan project <https://github.com/lowRISC/opentitan>`_ can serve as an example of how to integrate the two components in a toplevel design.

Interface
---------

+-----------------+-----------+-----------------------------+
| Signal          | Direction | Description                 |
+=================+===========+=============================+
| ``debug_req_i`` | input     | Request to enter Debug Mode |
+-----------------+-----------+-----------------------------+

``debug_req_i`` is the "debug interrupt", issued by the debug module when the core should enter Debug Mode.

Parameters
----------

+---------------------+-----------------------------------------------------------------+
| Parameter           | Description                                                     |
+=====================+=================================================================+
| ``DmBaseAddr``      | Base address of the Debug Module                                |
+---------------------+-----------------------------------------------------------------+
| ``DmAddrMask``      | Address mask of the Debug Module                                |
+---------------------+-----------------------------------------------------------------+
| ``DmHaltAddr``      | Address to jump to when entering Debug Mode                     |
+---------------------+-----------------------------------------------------------------+
| ``DmExceptionAddr`` | Address to jump to when an exception occurs while in Debug Mode |
+---------------------+-----------------------------------------------------------------+
| ``DbgTriggerEn``    | Enable support for debug triggers                               |
+---------------------+-----------------------------------------------------------------+
| ``DbgHwBreakNum``   | Number of debug triggers                                        |
+---------------------+-----------------------------------------------------------------+

Core Debug Registers
--------------------

Ibex implements four core debug registers, namely :ref:`csr-dcsr`, :ref:`csr-dpc`, and two debug scratch registers.
If the ``DbgTriggerEn`` parameter is set, debug trigger registers are available.
See :ref:`csr-tselect`, :ref:`csr-tdata1` and :ref:`csr-tdata2` for details.
All those registers are accessible from Debug Mode only.
If software tries to access them without the core being in Debug Mode, an illegal instruction exception is triggered.

.. _debug-cheriot:

Debug Mode in CHERIoT
---------------------

The CHERIoT specification does not define Debug Mode, so the behaviour described in this section is specific to Ibex.

In CHERIoT mode (see :ref:`cheriot`), Ibex does not enforce the CHERIoT protections in Debug Mode:

* Instruction fetch is not checked against the bounds, tag, seal and permissions of PCC.
* Loads and stores, including ``CLC`` and ``CSC``, are not checked against the bounds, tag, seal and permissions of the authorizing capability.
* ``CLC`` does not clear the tag or reduce the permissions of the loaded capability based on the permissions of the authorizing capability.
* Capability instructions do not raise CHERIoT exceptions.
  ``CSpecialRW`` with an unimplemented SCR index still raises an illegal instruction exception.

Code executed in Debug Mode, such as the debug ROM, the program buffer and the abstract commands of the Debug Module, can therefore read and write all memory and read every capability stored in it.

.. important::
   Debug Mode bypasses the memory protection of CHERIoT.
   A system that relies on CHERIoT to protect production assets must not give untrusted parties access to the Debug Module.

Ibex adds the debug SCRs ``depcc``, ``dscratchc0`` and ``dscratchc1``, which are not part of the CHERIoT specification (see :ref:`cheriot-scrs`).
On entry into Debug Mode, PCC is saved in ``depcc`` and replaced by ``mtcc``, as when taking a trap, and ``dret`` restores PCC from ``depcc``.
CSR and SCR accesses in Debug Mode therefore still require the SR permission in ``mtcc``.
