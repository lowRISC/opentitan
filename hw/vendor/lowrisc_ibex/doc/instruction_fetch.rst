.. _instruction-fetch:

Instruction Fetch
=================

The Instruction-Fetch (IF) stage of the core is able to supply one instruction to the Instruction-Decode (ID) stage per cycle if the instruction cache or the instruction memory is able to serve one instruction per cycle.
For optimal performance and timing closure reasons, a prefetcher is used which fetches instructions from the instruction memory, or instruction cache.

The following table describes the signals that are used to fetch instructions.
This interface is a simplified version of the interface used on the data interface as described in :ref:`load-store-unit`.
The main difference is that the instruction interface does not allow for write transactions and thus needs less signals.

.. tabularcolumns:: |p{4cm}|l|p{9cm}|

+-------------------------+-----------+-----------------------------------------------+
| Signal                  | Direction | Description                                   |
+=========================+===========+===============================================+
| ``instr_req_o``         | output    | Request valid, must stay high until           |
|                         |           | ``instr_gnt_i`` is high for one cycle         |
+-------------------------+-----------+-----------------------------------------------+
| ``instr_addr_o[31:0]``  | output    | Address, word aligned                         |
+-------------------------+-----------+-----------------------------------------------+
| ``instr_gnt_i``         | input     | The other side accepted the request.          |
|                         |           | ``instr_req_o`` may be deasserted in the next |
|                         |           | cycle.                                        |
+-------------------------+-----------+-----------------------------------------------+
| ``instr_rvalid_i``      | input     | ``instr_rdata_i`` holds valid data when       |
|                         |           | ``instr_rvalid_i`` is high. This signal will  |
|                         |           | be high for exactly one cycle per request.    |
+-------------------------+-----------+-----------------------------------------------+
| ``instr_rdata_i[31:0]`` | input     | Data read from memory                         |
+-------------------------+-----------+-----------------------------------------------+


Misaligned Accesses
-------------------

Externally, the IF interface performs word-aligned instruction fetches only.
Misaligned instruction fetches are handled by performing two separate word-aligned instruction fetches.
Internally, the core can deal with both word- and half-word-aligned instruction addresses to support compressed instructions.
The LSB of the instruction address is ignored internally.


Protocol
--------

The protocol used to communicate with the instruction cache or the instruction memory is very similar to the protocol used by the LSU on the data interface of Ibex.
See the description of the LSU in :ref:`LSU Protocol<lsu-protocol>` for details about this protocol.

.. caution::

   The IF protocol differs from the LSU protocol in that the address can change while the request is valid (``instr_req_o`` is high).
   This allows the core to immediately update the instruction fetch address when a branch occurs.
   As depicted in :numref:`if_timing_difference`, care has to be taken when working with the address.
   The data returned must match the address during the grant cycle.

   .. wavedrom::
      :name: if_timing_difference
      :caption: Memory transaction with wait states

      {"signal":
        [
          {"name": "clk", "wave": "p......"},
          {"name": "instr_req_o", "wave": "01..0.."},
          {"name": "instr_addr_o", "wave": "x=.=xxx", "data": ["Addr1", "Addr2"]},
          {"name": "instr_gnt_i", "wave": "0..10.."},
          {"name": "instr_rvalid_i", "wave": "0....10"},
          {"name": "instr_rdata_i", "wave": "xxxxx=x", "data": ["RData2"]}
        ],
        "config": { "hscale": 2 }
      }
