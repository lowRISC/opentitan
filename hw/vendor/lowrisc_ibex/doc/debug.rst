.. _debug-support:

Debug Support
=============

Ibex offers support for execution-based debug according to the RISC-V Debug Specification, version 0.13.

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

Core Debug Registers
--------------------

Ibex implements four core debug registers, namely :ref:`csr-dcsr`, :ref:`csr-dpc`, and two debug scratch registers.
If the ``DbgTriggerEn`` parameter is set, debug trigger registers are available.
See :ref:`csr-tselect`, :ref:`csr-tdata1` and :ref:`csr-tdata2` for details.
All those registers are accessible from Debug Mode only.
If software tries to access them without the core being in Debug Mode, an illegal instruction exception is triggered.
