Overview
========

While the ``RISCV-DV`` Instruction Generator provides a ``debug_rom`` section as
well as various interrupt and exception handlers, from a verification
standpoint this is not enough to help ensure that a core's internal state is being
updated correctly upon receiving external stimulus such as interrupts or debug
requests, such as the values of any relevant CSRs.
To help with this issue, the instruction generator also provides a mechanism by
which to communicate information to a RTL simulation environment via a
handshaking protocol.

Usage
-----

Every handshake produced by the instruction generator is just a small segment of
RISC-V assembly code, that end in one or more ``sw`` instructions to a specified memory
address ``signature_addr``.
This ``signature_addr`` is completely customizable, and
can be specified through a ``plusarg`` runtime option to the generator.
There is also an enable bit ``require_signature_addr`` that must be set through
another ``plusarg`` argument to enable these handshake code segments to be
generated in the main random assembly program.

A ``RISCV-DV`` based CPU verification environment that utilizes that handshaking mechanism should
provide a basic set of tasks to monitor this ``signature_addr`` for any writes - this will indicate
that the DUT is executing a particular handshake assembly sequence and is transmitting some
information to the testbench for analysis.
As a result, this ``signature_addr``
acts as a memory-mapped address that the testbench will monitor, and as
such, case should be taken when setting this address to ensure that the generator's
program randomization will not somehow create a sequence of random load/store
instructions that access the same ``signature_addr``.
A suggested value for this ``signature_addr`` is the value ``0x8ffffffc``, but can be set
to any other address depending on the CPU memory map.
More details, and an example, as to how to interface the testbench with this
handshake mechanism will be provided below.

Handshake Sequence Architecture
-------------------------------

The function ``gen_signature_handshake(...)`` contained in
`src/riscv_asm_program_gen.sv <https://github.com/google/riscv-dv/blob/master/src/riscv_asm_program_gen.sv>`_.
is used to actually generate the handshaking code and push it into the specified
instruction queue. Its usage can be seen repeatedly throughout the program
generation in various places, such as trap handlers and the debug ROM, where it
is important to send information to a testbench for further verification.
The ``signature_type_t``, ``core_status_t``, and ``test_result_t`` enums specified as
input values to this function are defined in
`src/riscv_signature_pkg.sv <https://github.com/google/riscv-dv/blob/master/src/riscv_signature_pkg.sv>`_.
Note that all of these definitions are within a standalone package, this is so
that an RTL simulation environment can also import this package to gain access
to these enums.
The ``signature_type_t`` enum is by far the most important enum value, as
this specifies what kind of handshake will be generated.

There are currently 4 defined values of ``signature_type``, each corresponding
to a different handshake type that will be generated; each will be explained below.
Note that two GPRs must be used to temporarily hold the store address and the
actual data to store to this address; the generator randomizes these two GPRs
for every generated program, but for the purposes of this document, ``x1`` and
``x2`` will be used, and ``0x8ffffffc`` will be used as the example ``signature_addr``.

CORE_STATUS
^^^^^^^^^^^

When the ``signature_type`` argument is specified as ``CORE_STATUS``, a single word
of data will be written to the ``signature_addr``. As the actual ``signature_type``
value is 8 bits wide, as specified in the ``riscv_signature_pkg``, this generated
data word will contain the ``CORE_STATUS`` value in its bottom 8 bits, and will
contain the specified value of ``core_status_t`` in the upper 24 bits. This
signature handshake is intended to convey basic information about the core's
execution state to an RTL simulation environment; a handshake containing a
``core_status`` of ``IN_DEBUG_MODE`` is added to the debug ROM to indicate to a
testbench that the core has jumped into Debug Mode and is executing the debug
ROM, a handshake containing a ``core_status`` of ``ILLEGAL_INSTR_EXCEPTION`` is
added to the illegal instruction exception handler code created by the generator
to indicate to a testbench that the core has trapped to and is executing the
proper handler after encountering an illegal instruction, and so on for the rest
of the defined ``core_status_t`` enum values.

Note that when generating these specific handshakes, it is only necessary to
specify the parameters ``instr``, ``signature_type``, and ``core_status``. For
example, to generate this handshake to signal status ``IN_MACHINE_MODE`` to the
testbench, the call to the function looks like this:

.. code-block:: verilog

    gen_signature_handshake(.instr(instr_string_queue),
                            .signature_type(CORE_STATUS),
                            .core_status(IN_MACHINE_MODE));

The sequence of assembly code generated by this call looks like the following:

.. code-block:: verilog

    // First, load the signature address into a GPR
    li x2, 0x8ffffffc
    // Load the intended core_status_t enum value into
    // a second GPR
    li x1, 0x2
    // Left-shift the core_status value by 8 bits
    // to make room for the signature_type
    slli x1, x1, 8
    // Load the intended signature_type_t enum value into
    // the bottom 8 bits of the data word
    addi x1, x1, 0x0
    // Store the data word to memory at the location of the signature_addr
    sw x1, 0(x2)

TEST_RESULT
^^^^^^^^^^^

As before, when ``signature_type`` is set to ``TEST_RESULT`` a single word of data
will be written to the signature address, and the value ``TEST_RESULT`` will be
placed in the bottom 8 bits. The upper 24 bits will then contain a value of type
``test_result_t``, either ``TEST_PASS`` or ``TEST_FAIL``, to indicate to the testbench
the exit status of the test. As the ISS co-simulation flow provides a robust
end-of-test correctness check, the only time that this signature handshake is
used is in the ``riscv_csr_test``. Since this test is generated with a Python
script and is entirely self-checking, we must send an exit status of ``TEST_PASS``
or ``TEST_FAIL`` to the testbench to indicate to either throw an error or end the
test correctly.

Note that when generating these handshakes, the only arguments that need to be
specified are ``instr``, ``signature_type``, and ``test_result``. For example, to
generate a handshake to communicate ``TEST_PASS`` to a testbench, the function
call would look like this:

.. code-block:: verilog

    gen_signature_handshake(.instr(instr_string_queue),
                            .signature_type(TEST_RESULT),
                            .test_result(TEST_PASS));

The sequence of generated assembly code with this function call would look like
the following:

.. code-block:: verilog

    // Load the signature address into a GPR
    li x2 0x8ffffffc
    // Load the intended test_result_t enum value
    li x1, 0x0
    // Left-shift the test_result value by 8 bits
    slli x1, x1, 8
    // Load the intended signature_type_t enum value into
    // the bottom 8 bits of the data word
    addi x1, x1, 0x1
    // Store this formatted word to memory at the signature address
    sw x1, 0(x2)

WRITE_GPR
^^^^^^^^^

When a ``signature_type`` of ``WRITE_GPR`` is passed to the
``gen_signature_handshake(...)`` function, one data word will initially be written
to the signature address, containing the ``signature_type`` of ``WRITE_GPR`` in the
lower 8 bits. After this, the value held by each of the 32 RISC-V general
purpose registers from ``x0`` to ``x31`` will be written to the signature address
with ``sw`` instructions.

For this particular handshake, the only function arguments that need to be
specified are ``instr`` and ``signature_type``. A function call to generate this
particular handshake would look like the following:

.. code-block:: verilog

    gen_signature_handshake(.instr(instr_string_queue),
                            .signature_type(WRITE_GPR));

The generated assembly sequence would look like this:

.. code-block:: verilog

    // Load the signature address into a GPR
    li x2, 0x8ffffffc
    // Load the value of WRITE_GPR into a second GPR
    li x1, 0x2
    // Store this word to memory at the signature address
    sw x1, 0(x2)
    // Iterate through all 32 GPRs and write each one to
    // memory at the signature address
    sw x0, 0(x2)
    sw x1, 0(x2)
    sw x2, 0(x2)
    sw x3, 0(x2)
    ...
    sw x30, 0(x2)
    sw x31, 0(x2)

WRITE_CSR
^^^^^^^^^

When ``gen_signature_handshake(...)`` is called with ``WRITE_CSR`` as the
``signature_type`` argument, we will generate a first ``sw`` instruction that writes a
data word to the ``signature_addr`` that contains the value ``WRITE_CSR`` in the
bottom 8 bits, and the address of the desired CSR in the upper 24 bits, to
indicate to the testbench which CSR will be written.
This first generated ``sw`` instruction is then followed by a second one, which
writes the actual data contained in the specified CSR to the signature address.

Note the only function arguments that have to be specified to generate this
handshake are ``instr``, ``signature_type``, and ``csr``. As an example, to generate a
handshake that writes the value of the `mie` CSR to the RTL simulation
environment, the function call would look like this:

.. code-block:: verilog

    gen_signature_handshake(.instr(instr_string_queue),
                            .signature_type(WRITE_CSR),
                            .csr(MIE));

The sequence of assembly generated by this call would look like the following:

.. code-block:: verilog

    // Load the signature address into a GPR
    li x2, 0x8ffffffc
    // Load the address of MIE into the second GPR
    li x1, 0x304
    // Left-shift the CSR address by 8 bits
    slli x1, x1, 8
    // Load the WRITE_CSR signature_type value into
    // the bottom 8 bits of the data word.
    // At this point, the data word is 0x00030403
    addi x1, x1, 0x3
    // Store this formatted word to memory at the signature address
    sw x1, 0(x2)
    // Read the actual CSR value into the second GPR
    csrr x1, 0x304
    // Write the value held by the CSR into memory at the signature address
    sw x1, 0(x2)

Sample Testbench Integration
----------------------------

Everything previously outlined has been relating to how this handshake
generation is implemented from the perspective of the ``RISCV-DV`` instruction
generator, but some work must be done in the RTL simulation environment to
actually interface with and use these handshakes to improve verification.

This handshaking mechanism has been put to use for verification of the `Ibex
RISC-V core <https://github.com/lowRISC/ibex>`_, in collaboration with lowRISC. To
interface with the handshaking code produced in the generator, this testbench
makes heavy use of the task ``wait_for_mem_txn(...)`` found in
`tests/core_ibex_base_test.sv <https://github.com/lowRISC/ibex/blob/master/dv/uvm/core_ibex/tests/core_ibex_base_test.sv>`_.
This task polls the Ibex core's data memory interface for any writes to the
chosen signature address (``0x8ffffffc``), and then based on the value of
``signature_type`` encoded by the generated handshake code, this task takes
appropriate action and stores the relevant data into a queue instantiated in the
base test class.

For example upon detecting a transaction written to the
signature address that has a ``signature_type`` of ``WRITE_CSR``, it right-shifts
the collected data word by 8 to obtain the CSR address, which is then stored to
the local queue. However, since for ``WRITE_CSR`` signatures there is a second
data word that gets written to memory at the signature address, the task waits
for the second write containing the CSR data to arrive, and then stores that
into the queue as well. After this task completes, it is now possible to pop
the stored data off of the queue for analysis anywhere else in the test class,
in this case examining the values of various CSR fields.

Additionally, the Ibex testbench provides a fairly basic API of some tasks
wrapping ``wait_for_mem_txn(...)`` for frequently used functionalities in various
test classes. This API is also found in
`tests/core_ibex_base_test.sv <https://github.com/lowRISC/ibex/blob/master/dv/uvm/core_ibex/tests/core_ibex_base_test.sv>`_.
Examples of use-cases for these API functions can be found throughout the
library of tests written for the Ibex core, found at
`tests/core_ibex_test_lib.sv <https://github.com/lowRISC/ibex/blob/master/dv/uvm/core_ibex/tests/core_ibex_test_lib.sv>`_, as these are heavily used to verify the core's response to external debug and interrupt stimulus.
