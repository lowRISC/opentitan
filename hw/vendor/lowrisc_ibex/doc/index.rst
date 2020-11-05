Ibex: An embedded 32 bit RISC-V CPU core
========================================

Ibex is a production-quality open source 32 bit RISC-V CPU core written in SystemVerilog.
The CPU core is heavily parametrizable and well suited for embedded control applications.
Ibex is being extensively verified and has seen multiple tape-outs.

You are now reading the Ibex documentation.
The documentation is split into four parts.

The :doc:`Overview documentation <01_overview/index>` looks at Ibex from high up.
It answers questions like what are the high-level properties of Ibex, which standards is Ibex following, and where is it typically used.

The :doc:`User Guide <02_user/index>` provides all necessary information to use Ibex.
It is aimed at hardware developers integrating Ibex into a design, and software developers writing software running on Ibex.

The :doc:`Reference Guide <03_reference/index>` provides background information.
It describes the design in detail, discusses the verification approach and the resulting testbench structures, and generally helps to understand Ibex in depth.

The :doc:`Developer Guide <04_developer/index>` is aimed at people making changes to Ibex itself.
Since Ibex is open source, every user of Ibex is encouraged to learn how to adapt Ibex to their use case, and be part of the open development process.

.. toctree::
   :maxdepth: 2
   :hidden:

   01_overview/index.rst
   02_user/index.rst
   03_reference/index.rst
   04_developer/index.rst
