---
title: "Memory Backdoor Scoreboard"
---

The mem_model_pkg checks write value matches with previous write value, but
there are some limitations.
  - Can’t check memory ECC if encoding and decoding match each other.
  - Can’t check the read value if the address hasn't been written after init
     or after a key request.
  - Can’t check the write value if the address isn’t read after the write.
  - Not aware of any B2B hazard (such as RAW).
This scoreboard can cover all above limitations, as it checks read/write value
matches with backdoor value. B2B hazard will be handled when predicting expected
value. All kinds of hazard corner cases will be sampled in functional coverage.

### `get_bkdr_val(mem_addr_t addr);`
User must override this pure virtual function to return backdoor value from the
memory based on the given address.

### `read_start(mem_addr_t addr, mem_mask_t mask)`
This function should be called when a read request is latched by design.
Predicted read value is calculated in this function:
 - If there is a pending write with same address (RAW hazard), the expected value is
 from this write (also depends on which bytes is enabled)
 - If no RAW hazard, the expected value is from latching backdoor value at the
 time of calling this function.

### `read_finish(mem_data_t act_data, mem_addr_t addr, mem_mask_t mask, bit en_check_consistency)`
This function should be called when a read transaction is done. It compares the read
value with expected value calculated at `read_start`.

### `write_start(mem_addr_t addr, mem_mask_t mask)`
This function should be called when a write request is latched by design.
Write items will be stored in the queue for checking RAW hazard and future comparison.

### `write_finish(mem_addr_t addr, mem_mask_t mask, bit en_check_consistency)`
This function should be called once the write data is written into the memory.
This function will read back the data from backdoor and compare with write value stored
in write_item_q.
