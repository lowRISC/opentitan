## Memory Model
The memory model UVC models a memory device which any host interface can read
from or write to. It is implemented as a `uvm_object`, and instantiates an
associative array of bytes `system_memory`. This class is paramterized by both
the address width and the data width, and creates two `typedefs` to represent
both, `mem_addr_t` and `mem_data_t`.
The `mem_model` class has four main functions, which are detailed below.

### `read_byte(mem_addr_t addr)`
This function looks up the byte of data corresponding to the memory address
passed in, and returns it. If the address does not exist in `system_memory`, it
will randomize the returned data and throw a `UVM_ERROR`.

### `write_byte(mem_addr_t addr, bit [7:0] data)`
This function simply assigns the given data to the specified memory address
location in `system_memory`.

### `write(input mem_addr_t addr, mem_data_t data)`
This function writes a full memory word of width `mem_data_t` to the specified
address, breaking it down into a series of back-to-back calls to `write_byte()`
to correctly byte-address the memory.

### `read(mem_addr_t addr)`
This function reads a full memory word of width `mem_data_t` from the specified
address, breaking it down into a series of back-to-back calls to `read_byte()`
to correctly byte-address the memory.
