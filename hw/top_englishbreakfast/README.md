# Top Englishbreakfast

This is an experimental top intended for SCA/FI activities.

## Memory Map

The base addresses of the memory and peripherals are defined in this [table](./doc/memory_map.md).

The choice of memory, or lack thereof at location 0x0 confers two exclusive benefits:
- If there are no memories at location 0x0, then null pointers will immediately error and be noticed by software (the xbar will fail to decode and route)
- If SRAM is placed at 0, accesses to data located within 2KB of 0x0 can be accomplished with a single instruction and thus reduce code size.

For the purpose of `top_englishbreakfast`, the first option has been chosen to benefit software development and testing.
