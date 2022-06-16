.. _cosim:

Co-simulation System
====================

Overview
--------

A co-simulation system is provided that can run in either the Ibex UVM DV environment or with Simple System.
This system runs a RISC-V ISS (currently only Spike is supported) in lockstep with an Ibex core.
All instructions executed by Ibex and memory transactions generated are checked against the behaviour of the ISS.
This system supports memory errors, interrupt and debug requests which are observed in the RTL simulation and forwarded to the ISS so the ISS and RTL remain in sync.
The system uses a generic interface to allow support of multiple ISSes.
Only VCS is supported as a simulator, though no VCS specific functionality is required so adding support for another simulator should be straight-forward.

To run the co-simulation system, a particular version of Spike is required (see the Setup and Usage section, below).

The RISC-V Formal Interface (RVFI) is used to provide information about retired instructions and instructions that produce synchronous traps for checking.
The RVFI has been extended to provide interrupt and debug information and the value of the ``mcycle`` CSR.
These extended signals have the prefix ``rvfi_ext``

The co-simulation system is EXPERIMENTAL.
It is disabled by default in the UVM DV environment currently, however it is intended to become the primary checking method for the UVM testbench.

Setup and Usage
---------------

Clone the `lowRISC fork of Spike <https://github.com/lowRISC/riscv-isa-sim>`_ and check out the ``ibex-cosim-v0.3`` tag.
Other, later, versions called ``ibex-cosim-v*`` may also work but there's no guarantee of backwards compatibility.
Follow the Spike build instructions to build and install Spike.
The ``--enable-commitlog`` and ``--enable-misaligned`` options must be passed to ``configure``.
We recommend using a custom install location (using ``--prefix=<path>`` with ``configure``) to avoid cluttering system directories.
Note that, if you do this, you will also need to add an entry to ``PKG_CONFIG_PATH`` so that ``pkg-config`` can tell us how to build against the installed Spike libraries.

To build/run the UVM DV environment with the co-simulator, add the ``COSIM=1`` argument to the make command.
To build Simple System with the co-simulator, build the ``lowrisc:ibex:ibex_simple_system_cosim`` core.

Quick Build and Run Instructions
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

Build and install the co-simulator

.. code-block:: bash

  # Get the Ibex co-simulation spike branch
  git clone -b ibex_cosim https://github.com/lowRISC/riscv-isa-sim.git riscv-isa-sim-cosim

  # Setup build directory
  cd riscv-isa-sim-cosim
  mkdir build
  cd build

  # Configure and build spike
  ../configure --enable-commitlog --enable-misaligned --prefix=/opt/spike-cosim
  sudo make -j8 install

Run the UVM DV regression with co-simulation enabled

.. code-block:: bash

  # Run regression with co-simulation enabled
  cd <ibex_area>/dv/uvm/core_ibex
  make COSIM=1

Build and run Simple System with the co-simulation enabled

.. code-block:: bash

  # Build simulator
  fusesoc --cores-root=. run --target=sim --setup --build lowrisc:ibex:ibex_simple_system_cosim --RV32E=0 --RV32M=ibex_pkg::RV32MFast

  # Build coremark test binary, with performance counter dump disabled. The
  # co-simulator system doesn't produce matching performance counters in spike so
  # any read of those CSRs results in a mismatch and a failure.
  make -C ./examples/sw/benchmarks/coremark SUPPRESS_PCOUNT_DUMP=1

  # Run coremark binary with co-simulation checking
  build/lowrisc_ibex_ibex_simple_system_cosim_0/sim-verilator/Vibex_simple_system --meminit=ram,examples/sw/benchmarks/coremark/coremark.elf

Co-simulation details
----------------------

The co-simulation system uses DPI calls to link the DV and ISS sides together.
A C++ interface is defined in ``dv/cosim/cosim.h`` with a DPI wrapper provided by ``dv/cosim/cosim_dpi.cc`` and ``dv/cosim/cosim_dpi.h``.
A ``chandle``, which points to some class instance that implements the interface, must be provided by the DV environment.
All the co-simulation DPI calls take this ``chandle`` as a first argument.

The details below discuss the C++ interface.
The DPI version of the interface is almost identical, with all functions prefaced with ``riscv_cosim`` and taking a ``chandle`` of the co-simulation instance to use.

The core function of the co-simulation interface is the ``step`` function:

.. code-block:: c++

  virtual bool step(uint32_t write_reg, uint32_t write_reg_data, uint32_t pc, bool sync_trap);

``step`` takes arguments giving the PC of the most recently retired or synchronously trapping instruction in the DUT along with details of any register write that occurred.

Where ``step`` is provided with a retired (successfully executed) instruction it steps the ISS by one instruction and checks it executed the same instruction, with the same register write result, as the DUT.

When ``step`` is provided with an instruction that produces a synchronous trap, it checks the ISS also traps on the same instruction but does not step to the next executed instruction.
That instruction will be the first instruction of the trap handler and will be checked/stepped by the next call to ``step`` when it retires from the DUT.

Any data memory accesses that the ISS produces during the ``step`` are checked against observed DUT memory accesses.

``step`` returns false if any checks have failed.
If any errors occur during the step they can be accessed via ``get_errors`` which returns a vector of error messages.
For the DPI interface errors are accessed using ``riscv_cosim_get_num_errors`` and ``riscv_cosim_get_error``.
When errors have been checked they can be cleared with ``clear_errors``.

Trap Handling
^^^^^^^^^^^^^

Traps are separated into two categories, synchronous and asynchronous.
Synchronous traps are caused by a particular instruction's execution (e.g. an illegal instruction).
Asynchronous traps are caused by external interrupts.
Note that in Ibex error responses to both loads and store produce a synchronous trap so the co-simulation system has the same behaviour.

A synchronous trap is associated with a particular instruction and prevents that instruction from completing its execution.
That instruction doesn't retire, but is still made visible on the RVFI.
The ``rvfi_trap`` signal is asserted for an instruction that causes a synchronous trap.
As described above ``step`` should be called for any instruction that causes a synchronous trap to check the trap is also seen by the ISS.

An asynchronous trap can be seen as occurring between instructions and as such doesn't have an associated instruction, nothing will be seen on RVFI with ``rvfi_trap`` set.
The co-simulation system will immediately take any pending asynchronous trap when ``step`` is called, expecting the instruction checked with ``step`` to be the first instruction of the trap handler.

While a debug request is not strictly an asynchronous trap (it doesn't use the same exception handling mechanism), they work identically to asynchronous traps for the co-simulation system.
When a debug request is pending when ``step`` is called the co-simulation will expect the instruction checked by ``step`` to be the first instruction of the debug handler.

Interrupts and Debug Requests
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

The DV environment must observe any incoming interrupts and debug requests generated by the testbench and notify the co-simulation system of them using ``set_mip``, ``set_debug_req`` and ``set_nmi``.
An interrupt or debug request will take immediate effect at the next ``step`` (if architecturally required to do so).
The DV environment is responsible for determining when to call ``set_mip``, ``set_debug_req`` and ``set_nmi`` to ensure a RTL and co-simulation match.

The state of the incoming interrupts and debug request is sampled when an instruction moves from IF to ID/EX.
The sampled state is tracked with the rest of the RVFI pipeline and used to call ``set_mip``, ``set_debug_req`` and ``set_nmi`` when the instruction is output by the RVFI.
See the comments in :file:`rtl/ibex_core.sv`, around the ``new_debug_req``, ``new_nmi`` and ``new_irq`` signals for further details.

Memory Access Checking and Bus Errors
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

The co-simulation system must be informed of all Dside accesses performed by the RTL using ``notify_dside_access``.
See :file:`dv/cosim/cosim.h` for further details.
As Ibex doesn't perform speculative Dside memory accesses, all notified accesses are expected to match with accesses performed by the ISS in the same order they are notified.

Accesses notified via ``notify_dside_access`` can specify they saw an error response, the co-simulation system will produce the appropriate trap when the ISS attempts to access the address that saw the error.

Accesses must be notified before they occur in the ISS for the access matching and trapping on errors to work.

Iside accesses from Ibex can be speculative, so there is no simple link between accesses produced by the RTL and the accesses performed by the ISS for the Iside.
This means no direct checking of Iside accesses is done, however errors on the Iside accesses that result in an instruction fault trap need to be notified to the co-simulation system.
``set_iside_error`` does this, it is provided with the address that saw the bus error and it should be called immediately before the ``step`` that will process the trap.
The co-simulation system will produce an instruction fault trap if it attempts to access the provided error address in the ``step`` call following the ``set_iside_error`` call.

Two methods are available for dealing with bus errors on the Iside, they differ in where they probe.
One probes on the external instr_X memory interface, the other probes internally within the IF stage.
The probe used is selected by the ``probe_imem_for_err`` field of the ``core_ibex_cosim_cfg`` structure.
When set external probing is used, otherwise internal probing is used.

Both probe points look for addresses that have seen bus errors.
If an instruction entering ID/EX fetches from an address that has seen a bus error (as recorded by one of the probing methods) its ``rvfi_order_id`` is recorded.
When a faulting instruction is reported on the RVFI and its ``rvfi_order_id`` matches a recorded faulting one ``set_iside_error`` is called with the faulting address before the next ``step``.

The external interface probe should be used when it is guaranteed that a bus error to address A on the external interface results in a fetch error the next time an instruction with address A is observed entering the ID/EX stage (providing no successful access to A has occurred in the mean time).
Otherwise the internal probe should be used.
When Ibex is used with the prefetch buffer this guarantee holds and the external probe can be used.
When Ibex is used with the instruction cache this guarantee does not hold and the internal probe must be used.

Care should be taken when using the internal probe as it will miss any bug that causes instruction faults to be ignored by the prefetch buffer or ICache (or whatever else has been used in place of these by a custom implementation).
In the case of the Ibex ICache a separate testbench ensures instruction faults are dealt with appropriately within the ICache.
