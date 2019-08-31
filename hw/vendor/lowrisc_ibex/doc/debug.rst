.. _debug-support:

Debug Support
=============

Ibex offers support for execution-based debug according to the RISC-V Debug Specification, version 0.13.

Interface
---------

+-----------------+-----------+-----------------------------+
| Signal          | Direction | Description                 |
+=================+===========+=============================+
| ``debug_req_i`` | input     | Request to enter debug mode |
+-----------------+-----------+-----------------------------+

``debug_req_i`` is the "debug interrupt", issued by the debug module when the core should enter debug mode.

Parameters
----------

+---------------------+-----------------------------------------------------------------+
| Parameter           | Description                                                     |
+=====================+=================================================================+
| ``DmHaltAddr``      | Address to jump to when entering debug mode                     |
+---------------------+-----------------------------------------------------------------+
| ``DmExceptionAddr`` | Address to jump to when an exception occurs while in debug mode |
+---------------------+-----------------------------------------------------------------+
