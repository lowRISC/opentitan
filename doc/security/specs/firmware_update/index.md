---
title: "Firmware Update"
---

<p style="color: red; text-align: right;">
  Status: Pre-RFC
</p>

# Overview

The purpose of this document is to capture the process by which Tock will
perform a complete in-place B-slot update of the running firmware and request
that the `ROM/ROM_EXT` code boot into it.

*Note*: For certification reasons this document does not discuss detailed
guidance for encrypted updates. Additional implementation details on both
regular and encrypted updates to follow when possible.

# Update Process

1. A firmware update is initiated by a process external to the device.
    1. The system negotiates the parameters of the update:
        1. The system's availability for an update.
        2. Which slot the update must be built for, if the update requires a
           specific memory location (such as non relocatable monoliths).
        3. Which signature the update must be signed with in order to boot.
        4. The size of the update blocks. These should ideally be the same size
          as native flash pages.
        5. The total size of the update payload, in order to set boundaries on
           which the update can be performed.
2. The system unlocks the flash protection for the bounds of the B-slot.
3. For each block of the pending firmware update:
    2. The system erases the flash page at the destination address for the
       block.
    3. The system receives the block and writes it immediately to its
       destination address in flash. Blocks will need to be buffered given the
       speed of a flash write.
    4. Once written, the block is hashed and compared against the hash of the
       buffered block. This ensures that every flash write is complete and
       successful.
        6. If the hash doesn't match the hash of the buffered block, repeat the
           flash erase and write cycle.
        7. If the erase/flash cycle fails three times declare complete failure.
4. Issue a warning to the running applications that the system will be
   resetting.
5. Write a Boot Services request block into persistent RAM:
    5. Indicate the new firmware version slot to be booted.
    6. Indicate the retry policy to use when booting it.
6. Restart the system with a Boot Services cause set.
7. System follows the normal Secure Boot path into the new firmware image.
