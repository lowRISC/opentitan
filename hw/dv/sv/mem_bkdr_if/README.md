## Mem_bkdr Interface
The `mem_bkdr_if` interface provides a way to manipulate the memory array directly.
It includes a set of functions to backdoor read or write any address location within the memory.
The interface is bound to the memory using the `bind` keyword.
A virtual handle to it is passed on to the UVM side via `uvm_config_db` for controllability within various components.

### Assumptions
The following assumptions are made to ensure the interface works:
* This interface will be bound to one of the following modules:
  `prim_ram_1p`, `prim_ram_2p`, `prim_rom`
* The sub hierarchy from within these instances to the memory element will be fixed to
  `gen_generic.u_impl_generic.mem`

### Useful methods
This interface supports basic backdoor methods to access memory. Useful methods are:
* `is_addr_valid`: Check if input address is valid
  The input address is assumed to be the byte addressable address into memory
  starting at 0. It is user's responsibility to mask the upper bits.
* `read8`, `read16`, `read32`, `read64`: Functions to read one byte, two bytes, four bytes, and eight bytes respectively
  at specified input address
* `write8`, `write16`, `write32`, `write64`: Functions to write one byte, two bytes, four bytes, and eight bytes respectively
  with input data at specified input address
* `load_mem_from_file`: Load memory from a file specified by input string
* `print_mem`: Print the content of the memory
* `clear_mem`: Clear the memory to all 0s
* `set_mem`: Set the memory to all 1s
* `randomize_mem`: Randomize contents of the memory
