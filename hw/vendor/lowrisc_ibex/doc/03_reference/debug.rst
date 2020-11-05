.. _debug-support:

Debug Support
=============

Ibex offers support for execution-based debug according to the `RISC-V Debug Specification <https://riscv.org/specifications/debug-specification/>`_, version 0.13.


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
