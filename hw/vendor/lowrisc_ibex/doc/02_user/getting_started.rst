.. _getting-started:

Getting Started with Ibex
=========================

The Ibex repository contains all the RTL needed to simulate and synthesize an Ibex core.
`FuseSoC <https://github.com/olofk/fusesoc>`_ core files list the RTL files required to build Ibex (see :file:`ibex_core.core`).
The core itself is contained in the :file:`rtl/` directory, though it utilizes some primitives found in the :file:`vendor/lowrisc_ip/` directory.
These primitives come from the `OpenTitan <https://github.com/lowrisc/opentitan>`_ project but are copied into the Ibex repository so the RTL has no external dependencies.
You may wish to replace these primitives with your own and some are only required for specific configurations.
See :ref:`integration-prims` for more information.

There are several paths to follow depending on what you wish to accomplish:

 * See :ref:`examples` for a basic simulation setup running the core in isolation and a simple FPGA system.
 * See :ref:`verification` to begin working with the DV flow.
 * See :ref:`core-integration` to integrate the Ibex core into your own design.
 * See :ref:`integration-fusesoc-files` for information on how to get a complete RTL file listing to build Ibex for use outside of FuseSoC based flows.
