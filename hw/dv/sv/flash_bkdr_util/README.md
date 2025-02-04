# Flash Backdoor Utility Class

The `flash_bkdr_util` class extends the functionality of the `mem_bkdr_util` class with the
scrambling of flash memory contents.

Class instances are created in the testbench module and passed to the UVM environment via `uvm_config_db`.

### Methods
* `flash_write_scrambled`: Write scrambled data into the flash memory at the given address
