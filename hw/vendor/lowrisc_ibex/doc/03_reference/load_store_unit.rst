.. _load-store-unit:

Load-Store Unit
===============
:file:`rtl/ibex_load_store_unit.sv`

The Load-Store Unit (LSU) of the core takes care of accessing the data memory.
Loads and stores of words (32 bit), half words (16 bit) and bytes (8 bit) are supported.

Any load or store will stall the ID/EX stage for at least a cycle to await the response (whether that is awaiting load data or a response indicating whether an error has been seen for a store).

Data-Side Memory Interface
--------------------------

Signals that are used by the LSU:

+----------------------------+-----------+-----------------------------------------------+
| Signal                     | Direction | Description                                   |
+============================+===========+===============================================+
| ``data_req_o``             | output    | Request valid, must stay high until           |
|                            |           | ``data_gnt_i`` is high for one cycle          |
+----------------------------+-----------+-----------------------------------------------+
| ``data_addr_o[31:0]``      | output    | Address, word aligned                         |
+----------------------------+-----------+-----------------------------------------------+
| ``data_we_o``              | output    | Write Enable, high for writes, low for        |
|                            |           | reads. Sent together with ``data_req_o``      |
+----------------------------+-----------+-----------------------------------------------+
| ``data_be_o[3:0]``         | output    | Byte Enable. Is set for the bytes to          |
|                            |           | write/read, sent together with ``data_req_o`` |
+----------------------------+-----------+-----------------------------------------------+
| ``data_wdata_o[31:0]``     | output    | Data to be written to memory, sent together   |
|                            |           | with ``data_req_o``                           |
+----------------------------+-----------+-----------------------------------------------+
| ``data_wdata_intg_o[6:0]`` | output    | Integrity bits to be written to memory, sent  |
|                            |           | together with ``data_req_o`` (not used unless |
|                            |           | the SecureIbex parameter is set)              |
+----------------------------+-----------+-----------------------------------------------+
| ``data_gnt_i``             | input     | The other side accepted the request.          |
|                            |           | Outputs may change in the next cycle.         |
+----------------------------+-----------+-----------------------------------------------+
| ``data_rvalid_i``          | input     | ``data_err_i`` and ``data_rdata_i`` hold      |
|                            |           | valid data when ``data_rvalid_i`` is high.    |
|                            |           | This signal will be high for exactly one      |
|                            |           | cycle per request.                            |
+----------------------------+-----------+-----------------------------------------------+
| ``data_err_i``             | input     | Error response from the bus or the memory:    |
|                            |           | request cannot be handled. High in case of an |
|                            |           | error.                                        |
+----------------------------+-----------+-----------------------------------------------+
| ``data_rdata_i[31:0]``     | input     | Data read from memory                         |
+----------------------------+-----------+-----------------------------------------------+
| ``data_rdata_intg_i[6:0]`` | input     | Integrity bits read from memory (ignored      |
|                            |           | unless the SecureIbex parameter is set)       |
+----------------------------+-----------+-----------------------------------------------+


Bus Integrity Checking
----------------------

The core can optionally generate and verify check bits sent alongside the data for memory accesses.
Checkbits are generated and checked using a 39/32 Hsaio code (see :file:`vendor/lowrisc_ip/ip/prim/rtl/prim_secded_39_32_enc.sv`).
When this feature is used, any mismatch in checkbits will generate a major alert.

This feature is only used if the core is configured with the SecureIbex parameter set.
For all other configurations, the integrity signals can be ignored.

Misaligned Accesses
-------------------

The LSU is able to handle misaligned memory accesses, meaning accesses that are not aligned on natural word boundaries.
However, it does so by performing two separate word-aligned accesses.
This means that at least two cycles are needed for misaligned loads and stores.

If an error response is received for the first transaction, the second transaction will still be issued.
The second transaction will then follow the normal bus protocol, but its response/data will be ignored.
If a new load/store request is received while waiting for an abandoned second part to complete, it will not be serviced until the state machine returns to IDLE.

.. _lsu-protocol:

Protocol
--------

The protocol that is used by the LSU to communicate with a memory works as follows:

1. The LSU provides a valid address in ``data_addr_o`` and sets ``data_req_o`` high. In the case of a store, the LSU also sets ``data_we_o`` high and configures ``data_be_o`` and ``data_wdata_o``. The memory then answers with a ``data_gnt_i`` set high as soon as it is ready to serve the request. This may happen in the same cycle as the request was sent or any number of cycles later.

2. After receiving a grant, the address may be changed in the next cycle by the LSU. In addition, the ``data_wdata_o``, ``data_we_o`` and ``data_be_o`` signals may be changed as it is assumed that the memory has already processed and stored that information.

3. The memory answers with a ``data_rvalid_i`` set high for exactly one cycle to signal the response from the bus or the memory using ``data_err_i`` and ``data_rdata_i`` (during the very same cycle). This may happen one or more cycles after the grant has been received. If ``data_err_i`` is low, the request could successfully be handled at the destination and in the case of a load, ``data_rdata_i`` contains valid data. If ``data_err_i`` is high, an error occurred in the memory system and the core will raise an exception.

4. When multiple granted requests are outstanding, it is assumed that the memory requests will be kept in-order and one ``data_rvalid_i`` will be signalled for each of them, in the order they were issued.

:numref:`timing1`, :numref:`timing2` and :numref:`timing3` show example-timing diagrams of the protocol.

.. wavedrom::
   :name: timing1
   :caption: Basic Memory Transaction

   {"signal":
     [
       {"name": "clk", "wave": "p......"},
       {"name": "data_req_o", "wave": "01.0..."},
       {"name": "data_addr_o", "wave": "x=.xxxx", "data": ["Address"]},
       {"name": "data_we_o", "wave": "x=.xxxx", "data": ["WE"]},
       {"name": "data_be_o", "wave": "x=.xxxx", "data": ["BE"]},
       {"name": "data_wdata_o", "wave": "x=.xxxx", "data": ["WData"]},
       {"name": "data_gnt_i", "wave": "0.10..."},
       {"name": "data_rvalid_i", "wave": "0..10.."},
       {"name": "data_err_i", "wave": "xxx=xxx", "data": ["Err"]},
       {"name": "data_rdata_i", "wave": "xxx=xxx", "data": ["RData"]}

     ],
     "config": { "hscale": 2 }
    }

.. wavedrom::
   :name: timing2
   :caption: Back-to-back Memory Transaction

   {"signal":
     [
       {"name": "clk", "wave": "p......"},
       {"name": "data_req_o", "wave": "01.0..."},
       {"name": "data_addr_o", "wave": "x==xxxx", "data": ["Addr1", "Addr2"]},
       {"name": "data_we_o", "wave": "x==xxxx", "data": ["WE1", "WE2"]},
       {"name": "data_be_o", "wave": "x==xxxx", "data": ["BE1", "BE2"]},
       {"name": "data_wdata_o", "wave": "x==xxxx", "data": ["WData1", "Wdata2"]},
       {"name": "data_gnt_i", "wave": "01.0..."},
       {"name": "data_rvalid_i", "wave": "0.1.0.."},
       {"name": "data_err_i", "wave": "xx==xxx", "data": ["Err1", "Err2"]},
       {"name": "data_rdata_i", "wave": "xx==xxx", "data": ["RData1", "RData2"]}
     ],
     "config": { "hscale": 2 }
   }

.. wavedrom::
   :name: timing3
   :caption: Slow Response Memory Transaction

   {"signal":
     [
       {"name": "clk", "wave": "p......"},
       {"name": "data_req_o", "wave": "01..0.."},
       {"name": "data_addr_o", "wave": "x=..xxx", "data": ["Address"]},
       {"name": "data_we_o", "wave": "x=..xxx", "data": ["WE"]},
       {"name": "data_be_o", "wave": "x=..xxx", "data": ["BE"]},
       {"name": "data_wdata_o", "wave": "x=..xxx", "data": ["WData"]},
       {"name": "data_gnt_i", "wave": "0..10.."},
       {"name": "data_rvalid_i", "wave": "0....10"},
       {"name": "data_err_i", "wave": "xxxxx=x", "data": ["Err"]},
       {"name": "data_rdata_i", "wave": "xxxxx=x", "data": ["RData"]}
     ],
     "config": { "hscale": 2 }
   }
