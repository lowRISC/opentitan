.. _pmp:

Physical Memory Protection (PMP)
================================

The Physical Memory Protection (PMP) unit implements region-based memory access checking in-accordance with the RISC-V Privileged Specification, version 1.11.
The following configuration parameters are available to control PMP checking:

+----------------+---------------+----------------------------------------------------------+
| Parameter      | Default value | Description                                              |
+================+===============+==========================================================+
| PMPEnable      | 0             | PMP support enabled                                      |
+----------------+---------------+----------------------------------------------------------+
| PMPNumRegions  | 4             | Number of implemented regions (1 - 16)                   |
+----------------+---------------+----------------------------------------------------------+
| PMPGranularity | 0             | Minimum match granularity :math:`2^{G+2}` bytes (0 - 31) |
+----------------+---------------+----------------------------------------------------------+

When PMPEnable is zero, the PMP module is not instantiated and all PMP registers read as zero (regardless of the value of PMPNumRegions)

PMP Integration
---------------

Addresses from the instruction fetch unit and load-store unit are passed to the PMP module for checking, and the output of the PMP check is used to gate the external request.
To maintain consistency with external errors, the instruction fetch unit and load-store unit progress with their request as if it was granted externally.
The PMP error is registered and consumed by the core when the data would have been consumed.

PMP Granularity
---------------

The PMP granularity parameter is used to reduce the size of the address matching comparators by increasing the minimum region size.
When the granularity is greater than zero, NA4 mode is not available and will be treated as OFF mode.
