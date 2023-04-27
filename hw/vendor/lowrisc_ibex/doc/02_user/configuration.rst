.. _ibex-config:

Ibex Configurations
===================

The ``ibex_top`` module has a large number of top-level parameters which configure the core (see :ref:`core-integration`).
This gives rise to a huge number of possible Ibex core configurations.
To manage this complexity a number of named configurations is provided in the :file:`ibex_configs.yml` file.
A subset of these are 'supported configurations' which are the focus of verification and development activities.

Configuration Tool
------------------

A tool :file:`util/ibex_config.py` is provided to work with the named configurations.
This tool provides command line options to set Ibex parameters for various EDA tools for a named configuration.
Various Ibex flows (e.g. the DV flow) use this tool internally and can be provided with a configuration name from :file:`util/ibex_config.py` to work with.

Here is an example of using the configuration tool to get the FuseSoC options required to build the ``opentitan`` configuration.

.. code-block:: bash

  # Request FuseSoC options required to build the 'opentitan' Ibex configuration.
  ./util/ibex_config.py opentitan fusesoc_opts

  # The output of the tool
  --RV32E=0 --RV32M=ibex_pkg::RV32MSingleCycle --RV32B=ibex_pkg::RV32BOTEarlGrey --RegFile=ibex_pkg::RegFileFF --BranchTargetALU=1 --WritebackStage=1 --ICache=1 --ICacheECC=1 --ICacheScramble=1 --BranchPredictor=0 --DbgTriggerEn=1 --SecureIbex=1 --PMPEnable=1 --PMPGranularity=0 --PMPNumRegions=16 --MHPMCounterNum=10 --MHPMCounterWidth=32

For further information about using the tool check the help provided on the command line.

.. code-block:: bash

  # Get help on using ibex_config.py
  ./util/ibex_config.py -h

Supported Configurations
------------------------

The current set of supported configurations are:

 * ``small`` - RV32IMC with two stage pipeline and 3 cycle multiplier
 * ``opentitan`` - The configuration used by the `OpenTitan <www.opentitan.org>`_ project
 * ``maxperf`` - RV32IMC with three stage pipeline and single cycle multiplier, maximum performance (using stable features) configuration.
 * ``maxperf-pmp-bmbalanced`` - ``maxperf`` configuration with PMP and the 'balanced' bit-manipulation configuration (:ref:`core-integration` for details).
