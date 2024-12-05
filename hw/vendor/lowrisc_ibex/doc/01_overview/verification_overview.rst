Verification Overview
=====================

Ibex is verified using a :ref:`UVM based testbench<verification>` that employs a :ref:`co-simulation methodology<cosim>` to cross-check Ibex execution against an ISS reference model (`Spike <https://github.com/lowRISC/riscv-isa-sim>`_).
The testbench runs binaries built from source produced by the `RISC-DV <https://github.com/chipsalliance/riscv-dv>`_ random instruction generator.
Additional stimulus is provided in the form of randomized memory timings, memory errors, interrupts and debug requests by the testbench.
A comprehensive :ref:`testplan<testplan>` and :ref:`coverage plan<coverage-plan>` are implemented.

Verification Status
-------------------

Ibex has a large number of parameters resulting in a large number of possible configurations.
The configuration space is too large to fully verify the design for all possible parameter sets.
To manage this complexity regressions runs and verification closure target a number of :ref:`supported configurations<ibex-config>`.

Current verification closure effort is focussed on the ``opentitan`` configuration and is the only configuration with nightly regression runs.
Verification maturity is tracked via :ref:`verification_stages` that are `defined by the OpenTitan project <https://opentitan.org/book/doc/project_governance/development_stages.html#hardware-verification-stages-v>`_.
Ibex has achieved **V2S** for the `opentitan` configuration, broadly this means verification is almost complete (over 90% code and functional coverage hit with over 90% regression pass rate with test plan and coverage plan fully implemented) but not yet closed.

Nightly regression results, including a coverage summary and details of test failures, for the ``opentitan`` Ibex configuration are published at https://ibex.reports.lowrisc.org/opentitan/latest/report.html. Below is a summary of these results:

.. image:: https://ibex.reports.lowrisc.org/opentitan/latest/summary.svg
