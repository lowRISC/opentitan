.. _core-integration:

Core Integration
================

The main module is named ``ibex_core`` and can be found in ``ibex_core.sv``.
Below, the instantiation template is given and the parameters and interfaces are described.

Instantiation Template
----------------------

.. code-block:: verilog

  ibex_core #(
      .PMPEnable                ( 0            ),
      .PMPGranularity           ( 0            ),
      .PMPNumRegions            ( 4            ),
      .MHPMCounterNum           ( 0            ),
      .MHPMCounterWidth         ( 40           ),
      .RV32E                    ( 0            ),
      .RV32M                    ( 1            ),
      .MultiplierImplementation ( "fast"       ),
      .DbgTriggerEn             ( 0            ),
      .DmHaltAddr               ( 32'h1A110800 ),
      .DmExceptionAddr          ( 32'h1A110808 )
  ) u_core (
      // Clock and reset
      .clk_i          (),
      .rst_ni         (),
      .test_en_i      (),

      // Configuration
      .hart_id_i      (),
      .boot_addr_i    (),

      // Instruction memory interface
      .instr_req_o    (),
      .instr_gnt_i    (),
      .instr_rvalid_i (),
      .instr_addr_o   (),
      .instr_rdata_i  (),
      .instr_err_i    (),

      // Data memory interface
      .data_req_o     (),
      .data_gnt_i     (),
      .data_rvalid_i  (),
      .data_we_o      (),
      .data_be_o      (),
      .data_addr_o    (),
      .data_wdata_o   (),
      .data_rdata_i   (),
      .data_err_i     (),

      // Interrupt inputs
      .irq_software_i (),
      .irq_timer_i    (),
      .irq_external_i (),
      .irq_fast_i     (),
      .irq_nm_i       (),

      // Debug interface
      .debug_req_i    (),

      // Special control signals
      .fetch_enable_i (),
      .core_sleep_o   ()
  );

Parameters
----------

+------------------------------+-------------+------------+-----------------------------------------------------------------+
| Name                         | Type/Range  | Default    | Description                                                     |
+==============================+=============+============+=================================================================+
| ``PMPEnable``                | bit         | 0          | Enable PMP support                                              |
+------------------------------+-------------+------------+-----------------------------------------------------------------+
| ``PMPGranularity``           | int (0..31) | 0          | Minimum granularity of PMP address matching                     |
+------------------------------+-------------+------------+-----------------------------------------------------------------+
| ``PMPNumRegions``            | int (1..16) | 4          | Number implemented PMP regions (ignored if PMPEnable == 0)      |
+------------------------------+-------------+------------+-----------------------------------------------------------------+
| ``MHPMCounterNum``           | int (0..8)  | 0          | Number of performance monitor event counters                    |
+------------------------------+-------------+------------+-----------------------------------------------------------------+
| ``MHPMCounterWidth``         | int (64..1) | 40         | Bit width of performance monitor event counters                 |
+------------------------------+-------------+------------+-----------------------------------------------------------------+
| ``RV32E``                    | bit         | 0          | RV32E mode enable (16 integer registers only)                   |
+------------------------------+-------------+------------+-----------------------------------------------------------------+
| ``RV32M``                    | bit         | 1          | M(ultiply) extension enable                                     |
+------------------------------+-------------+------------+-----------------------------------------------------------------+
| ``MultiplierImplementation`` | string      | "fast"     | Multiplicator type, "slow", or "fast"                           |
+------------------------------+-------------+------------+-----------------------------------------------------------------+
| ``DbgTriggerEn``             | bit         | 0          | Enable debug trigger support (one trigger only)                 |
+------------------------------+-------------+------------+-----------------------------------------------------------------+
| ``DmHaltAddr``               | int         | 0x1A110800 | Address to jump to when entering Debug Mode                     |
+------------------------------+-------------+------------+-----------------------------------------------------------------+
| ``DmExceptionAddr``          | int         | 0x1A110808 | Address to jump to when an exception occurs while in Debug Mode |
+------------------------------+-------------+------------+-----------------------------------------------------------------+

Interfaces
----------

+-------------------------+-------------------------+-----+----------------------------------------+
| Signal(s)               | Width                   | Dir | Description                            |
+=========================+=========================+=====+========================================+
| ``clk_i``               | 1                       | in  | Clock signal                           |
+-------------------------+-------------------------+-----+----------------------------------------+
| ``rst_ni``              | 1                       | in  | Active-low asynchronous reset          |
+-------------------------+-------------------------+-----+----------------------------------------+
| ``test_en_i``           | 1                       | in  | Test input, enables clock              |
+-------------------------+-------------------------+-----+----------------------------------------+
| ``hart_id_i``           | 32                      | in  | Hart ID, usually static, can be read   |
|                         |                         |     | from :ref:`csr-mhartid` CSR            |
+-------------------------+-------------------------+-----+----------------------------------------+
| ``boot_addr_i``         | 32                      | in  | First program counter after reset      |
|                         |                         |     | = ``boot_addr_i`` + 0x80,              |
|                         |                         |     | see :ref:`exceptions-interrupts`       |
+-------------------------+-------------------------+-----+----------------------------------------+
| ``instr_*``             | Instruction fetch interface, see :ref:`instruction-fetch`              |
+-------------------------+------------------------------------------------------------------------+
| ``data_*``              | Load-store unit interface, see :ref:`load-store-unit`                  |
+-------------------------+------------------------------------------------------------------------+
| ``irq_*``               | Interrupt inputs, see :ref:`exceptions-interrupts`                     |
+-------------------------+------------------------------------------------------------------------+
| ``debug_*``             | Debug interface, see :ref:`debug-support`                              |
+-------------------------+-------------------------+-----+----------------------------------------+
| ``fetch_enable_i``      | 1                       | in  | Enable the core, won't fetch when 0    |
+-------------------------+-------------------------+-----+----------------------------------------+
| ``core_sleep_o``        | 1                       | out | Core in WFI with no outstanding data   |
|                         |                         |     | or instruction accesses. Deasserts     |
|                         |                         |     | if an external event (interrupt or     |
|                         |                         |     | debug req) wakes the core up           |
+-------------------------+-------------------------+-----+----------------------------------------+
